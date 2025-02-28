/*
 * This file Copyright (C) 2008-2014 Mnemosyne LLC
 *
 * It may be used under the GNU GPL versions 2 or 3
 * or any future license endorsed by Mnemosyne LLC.
 *
 */

#include <algorithm> // std::partial_sort(), std::min(), std::max()
#include <cerrno> /* ENOENT */
#include <climits> /* INT_MAX */
#include <csignal>
#include <cstdint>
#include <cstdlib>
#include <cstring> /* memcpy */
#include <iterator> // std::back_inserter
#include <list>
#include <numeric> // std::acumulate()
#include <vector>

#ifndef _WIN32
#include <sys/types.h> /* umask() */
#include <sys/stat.h> /* umask() */
#endif

#include <event2/dns.h> /* evdns_base_free() */
#include <event2/event.h>

#include <libutp/utp.h>

// #define TR_SHOW_DEPRECATED
#include "transmission.h"
#include "announcer.h"
#include "bandwidth.h"
#include "blocklist.h"
#include "cache.h"
#include "crypto-utils.h"
#include "error.h"
#include "error-types.h"
#include "fdlimit.h"
#include "file.h"
#include "log.h"
#include "net.h"
#include "peer-io.h"
#include "peer-mgr.h"
#include "platform.h" /* tr_lock, tr_getTorrentDir() */
#include "platform-quota.h" /* tr_device_info_free() */
#include "port-forwarding.h"
#include "rpc-server.h"
#include "session.h"
#include "session-id.h"
#include "stats.h"
#include "torrent.h"
#include "tr-assert.h"
#include "tr-dht.h" /* tr_dhtUpkeep() */
#include "tr-udp.h"
#include "tr-utp.h"
#include "tr-lpd.h"
#include "trevent.h"
#include "utils.h"
#include "variant.h"
#include "verify.h"
#include "version.h"
#include "web.h"

enum
{
#ifdef TR_LIGHTWEIGHT
    DEFAULT_CACHE_SIZE_MB = 2,
    DEFAULT_PREFETCH_ENABLED = false,
#else
    DEFAULT_CACHE_SIZE_MB = 4,
    DEFAULT_PREFETCH_ENABLED = true,
#endif
    SAVE_INTERVAL_SECS = 360
};

#define dbgmsg(...) tr_logAddDeepNamed(nullptr, __VA_ARGS__)

static tr_port getRandomPort(tr_session* s)
{
    return tr_rand_int_weak(s->randomPortHigh - s->randomPortLow + 1) + s->randomPortLow;
}

/* Generate a peer id : "-TRxyzb-" + 12 random alphanumeric
   characters, where x is the major version number, y is the
   minor version number, z is the maintenance number, and b
   designates beta (Azureus-style) */
void tr_peerIdInit(uint8_t* buf)
{
    int val;
    int total = 0;
    char const* pool = "0123456789abcdefghijklmnopqrstuvwxyz";
    int const base = 36;

    memcpy(buf, PEERID_PREFIX, 8);

    tr_rand_buffer(buf + 8, 11);

    for (int i = 8; i < 19; ++i)
    {
        val = buf[i] % base;
        total += val;
        buf[i] = pool[val];
    }

    val = total % base != 0 ? base - total % base : 0;
    buf[19] = pool[val];
    buf[20] = '\0';
}

/***
****
***/

tr_encryption_mode tr_sessionGetEncryption(tr_session* session)
{
    TR_ASSERT(session != nullptr);

    return session->encryptionMode;
}

void tr_sessionSetEncryption(tr_session* session, tr_encryption_mode mode)
{
    TR_ASSERT(session != nullptr);
    TR_ASSERT(mode == TR_ENCRYPTION_PREFERRED || mode == TR_ENCRYPTION_REQUIRED || mode == TR_CLEAR_PREFERRED);

    session->encryptionMode = mode;
}

/***
****
***/

struct tr_bindinfo
{
    tr_socket_t socket;
    tr_address addr;
    struct event* ev;
};

static void close_bindinfo(struct tr_bindinfo* b)
{
    if (b != nullptr && b->socket != TR_BAD_SOCKET)
    {
        event_free(b->ev);
        b->ev = nullptr;
        tr_netCloseSocket(b->socket);
    }
}

static void close_incoming_peer_port(tr_session* session)
{
    close_bindinfo(session->bind_ipv4);
    close_bindinfo(session->bind_ipv6);
}

static void free_incoming_peer_port(tr_session* session)
{
    close_bindinfo(session->bind_ipv4);
    tr_free(session->bind_ipv4);
    session->bind_ipv4 = nullptr;

    close_bindinfo(session->bind_ipv6);
    tr_free(session->bind_ipv6);
    session->bind_ipv6 = nullptr;
}

static void accept_incoming_peer(evutil_socket_t fd, short what, void* vsession)
{
    TR_UNUSED(what);

    tr_socket_t clientSocket;
    tr_port clientPort;
    tr_address clientAddr;
    auto* session = static_cast<tr_session*>(vsession);

    clientSocket = tr_netAccept(session, fd, &clientAddr, &clientPort);

    if (clientSocket != TR_BAD_SOCKET)
    {
        if (tr_logGetDeepEnabled())
        {
            char addrstr[TR_ADDRSTRLEN];
            tr_address_and_port_to_string(addrstr, sizeof(addrstr), &clientAddr, clientPort);
            tr_logAddDeep(
                __FILE__,
                __LINE__,
                nullptr,
                "new incoming connection %" PRIdMAX " (%s)",
                (intmax_t)clientSocket,
                addrstr);
        }

        tr_peerMgrAddIncoming(session->peerMgr, &clientAddr, clientPort, tr_peer_socket_tcp_create(clientSocket));
    }
}

static void open_incoming_peer_port(tr_session* session)
{
    struct tr_bindinfo* b;

    /* bind an ipv4 port to listen for incoming peers... */
    b = session->bind_ipv4;
    b->socket = tr_netBindTCP(&b->addr, session->private_peer_port, false);

    if (b->socket != TR_BAD_SOCKET)
    {
        b->ev = event_new(session->event_base, b->socket, EV_READ | EV_PERSIST, accept_incoming_peer, session);
        event_add(b->ev, nullptr);
    }

    /* and do the exact same thing for ipv6, if it's supported... */
    if (tr_net_hasIPv6(session->private_peer_port))
    {
        b = session->bind_ipv6;
        b->socket = tr_netBindTCP(&b->addr, session->private_peer_port, false);

        if (b->socket != TR_BAD_SOCKET)
        {
            b->ev = event_new(session->event_base, b->socket, EV_READ | EV_PERSIST, accept_incoming_peer, session);
            event_add(b->ev, nullptr);
        }
    }
}

tr_address const* tr_sessionGetPublicAddress(tr_session const* session, int tr_af_type, bool* is_default_value)
{
    char const* default_value;
    struct tr_bindinfo const* bindinfo;

    switch (tr_af_type)
    {
    case TR_AF_INET:
        bindinfo = session->bind_ipv4;
        default_value = TR_DEFAULT_BIND_ADDRESS_IPV4;
        break;

    case TR_AF_INET6:
        bindinfo = session->bind_ipv6;
        default_value = TR_DEFAULT_BIND_ADDRESS_IPV6;
        break;

    default:
        bindinfo = nullptr;
        default_value = "";
        break;
    }

    if (is_default_value != nullptr && bindinfo != nullptr)
    {
        *is_default_value = tr_strcmp0(default_value, tr_address_to_string(&bindinfo->addr)) == 0;
    }

    return bindinfo != nullptr ? &bindinfo->addr : nullptr;
}

/***
****
***/

#ifdef TR_LIGHTWEIGHT
#define TR_DEFAULT_ENCRYPTION TR_CLEAR_PREFERRED
#else
#define TR_DEFAULT_ENCRYPTION TR_ENCRYPTION_PREFERRED
#endif

static int parse_tos(char const* tos)
{
    char* p;
    int value;

    if (evutil_ascii_strcasecmp(tos, "") == 0)
    {
        return 0;
    }

    if (evutil_ascii_strcasecmp(tos, "default") == 0)
    {
        return 0;
    }

    if (evutil_ascii_strcasecmp(tos, "lowcost") == 0)
    {
        return TR_IPTOS_LOWCOST;
    }

    if (evutil_ascii_strcasecmp(tos, "mincost") == 0)
    {
        return TR_IPTOS_LOWCOST;
    }

    if (evutil_ascii_strcasecmp(tos, "throughput") == 0)
    {
        return TR_IPTOS_THRUPUT;
    }

    if (evutil_ascii_strcasecmp(tos, "reliability") == 0)
    {
        return TR_IPTOS_RELIABLE;
    }

    if (evutil_ascii_strcasecmp(tos, "lowdelay") == 0)
    {
        return TR_IPTOS_LOWDELAY;
    }

    value = strtol(tos, &p, 0);

    if (p == nullptr || p == tos)
    {
        return 0;
    }

    return value;
}

static char const* format_tos(int value)
{
    static char buf[8];

    switch (value)
    {
    case 0:
        return "default";

    case TR_IPTOS_LOWCOST:
        return "lowcost";

    case TR_IPTOS_THRUPUT:
        return "throughput";

    case TR_IPTOS_RELIABLE:
        return "reliability";

    case TR_IPTOS_LOWDELAY:
        return "lowdelay";

    default:
        tr_snprintf(buf, 8, "%d", value);
        return buf;
    }
}

void tr_sessionGetDefaultSettings(tr_variant* d)
{
    TR_ASSERT(tr_variantIsDict(d));

    tr_variantDictReserve(d, 63);
    tr_variantDictAddBool(d, TR_KEY_blocklist_enabled, false);
    tr_variantDictAddStr(d, TR_KEY_blocklist_url, "http://www.example.com/blocklist");
    tr_variantDictAddInt(d, TR_KEY_cache_size_mb, DEFAULT_CACHE_SIZE_MB);
    tr_variantDictAddBool(d, TR_KEY_dht_enabled, true);
    tr_variantDictAddBool(d, TR_KEY_utp_enabled, true);
    tr_variantDictAddBool(d, TR_KEY_lpd_enabled, false);
    tr_variantDictAddStr(d, TR_KEY_download_dir, tr_getDefaultDownloadDir());
    tr_variantDictAddInt(d, TR_KEY_speed_limit_down, 100);
    tr_variantDictAddBool(d, TR_KEY_speed_limit_down_enabled, false);
    tr_variantDictAddInt(d, TR_KEY_encryption, TR_DEFAULT_ENCRYPTION);
    tr_variantDictAddInt(d, TR_KEY_idle_seeding_limit, 30);
    tr_variantDictAddBool(d, TR_KEY_idle_seeding_limit_enabled, false);
    tr_variantDictAddStr(d, TR_KEY_incomplete_dir, tr_getDefaultDownloadDir());
    tr_variantDictAddBool(d, TR_KEY_incomplete_dir_enabled, false);
    tr_variantDictAddInt(d, TR_KEY_message_level, TR_LOG_INFO);
    tr_variantDictAddInt(d, TR_KEY_download_queue_size, 5);
    tr_variantDictAddBool(d, TR_KEY_download_queue_enabled, true);
    tr_variantDictAddInt(d, TR_KEY_peer_limit_global, atoi(TR_DEFAULT_PEER_LIMIT_GLOBAL_STR));
    tr_variantDictAddInt(d, TR_KEY_peer_limit_per_torrent, atoi(TR_DEFAULT_PEER_LIMIT_TORRENT_STR));
    tr_variantDictAddInt(d, TR_KEY_peer_port, atoi(TR_DEFAULT_PEER_PORT_STR));
    tr_variantDictAddBool(d, TR_KEY_peer_port_random_on_start, false);
    tr_variantDictAddInt(d, TR_KEY_peer_port_random_low, 49152);
    tr_variantDictAddInt(d, TR_KEY_peer_port_random_high, 65535);
    tr_variantDictAddStr(d, TR_KEY_peer_socket_tos, TR_DEFAULT_PEER_SOCKET_TOS_STR);
    tr_variantDictAddBool(d, TR_KEY_pex_enabled, true);
    tr_variantDictAddBool(d, TR_KEY_port_forwarding_enabled, true);
    tr_variantDictAddInt(d, TR_KEY_preallocation, TR_PREALLOCATE_SPARSE);
    tr_variantDictAddBool(d, TR_KEY_prefetch_enabled, DEFAULT_PREFETCH_ENABLED);
    tr_variantDictAddInt(d, TR_KEY_peer_id_ttl_hours, 6);
    tr_variantDictAddBool(d, TR_KEY_queue_stalled_enabled, true);
    tr_variantDictAddInt(d, TR_KEY_queue_stalled_minutes, 30);
    tr_variantDictAddReal(d, TR_KEY_ratio_limit, 2.0);
    tr_variantDictAddBool(d, TR_KEY_ratio_limit_enabled, false);
    tr_variantDictAddBool(d, TR_KEY_rename_partial_files, true);
    tr_variantDictAddBool(d, TR_KEY_rpc_authentication_required, false);
    tr_variantDictAddStr(d, TR_KEY_rpc_bind_address, "0.0.0.0");
    tr_variantDictAddBool(d, TR_KEY_rpc_enabled, false);
    tr_variantDictAddStr(d, TR_KEY_rpc_password, "");
    tr_variantDictAddStr(d, TR_KEY_rpc_username, "");
    tr_variantDictAddStr(d, TR_KEY_rpc_whitelist, TR_DEFAULT_RPC_WHITELIST);
    tr_variantDictAddBool(d, TR_KEY_rpc_whitelist_enabled, true);
    tr_variantDictAddStr(d, TR_KEY_rpc_host_whitelist, TR_DEFAULT_RPC_HOST_WHITELIST);
    tr_variantDictAddBool(d, TR_KEY_rpc_host_whitelist_enabled, true);
    tr_variantDictAddInt(d, TR_KEY_rpc_port, TR_DEFAULT_RPC_PORT);
    tr_variantDictAddStr(d, TR_KEY_rpc_url, TR_DEFAULT_RPC_URL_STR);
    tr_variantDictAddBool(d, TR_KEY_scrape_paused_torrents_enabled, true);
    tr_variantDictAddStr(d, TR_KEY_script_torrent_done_filename, "");
    tr_variantDictAddBool(d, TR_KEY_script_torrent_done_enabled, false);
    tr_variantDictAddInt(d, TR_KEY_seed_queue_size, 10);
    tr_variantDictAddBool(d, TR_KEY_seed_queue_enabled, false);
    tr_variantDictAddBool(d, TR_KEY_alt_speed_enabled, false);
    tr_variantDictAddInt(d, TR_KEY_alt_speed_up, 50); /* half the regular */
    tr_variantDictAddInt(d, TR_KEY_alt_speed_down, 50); /* half the regular */
    tr_variantDictAddInt(d, TR_KEY_alt_speed_time_begin, 540); /* 9am */
    tr_variantDictAddBool(d, TR_KEY_alt_speed_time_enabled, false);
    tr_variantDictAddInt(d, TR_KEY_alt_speed_time_end, 1020); /* 5pm */
    tr_variantDictAddInt(d, TR_KEY_alt_speed_time_day, TR_SCHED_ALL);
    tr_variantDictAddInt(d, TR_KEY_speed_limit_up, 100);
    tr_variantDictAddBool(d, TR_KEY_speed_limit_up_enabled, false);
    tr_variantDictAddInt(d, TR_KEY_umask, 022);
    tr_variantDictAddInt(d, TR_KEY_upload_slots_per_torrent, 14);
    tr_variantDictAddStr(d, TR_KEY_bind_address_ipv4, TR_DEFAULT_BIND_ADDRESS_IPV4);
    tr_variantDictAddStr(d, TR_KEY_bind_address_ipv6, TR_DEFAULT_BIND_ADDRESS_IPV6);
    tr_variantDictAddBool(d, TR_KEY_start_added_torrents, true);
    tr_variantDictAddBool(d, TR_KEY_trash_original_torrent_files, false);
    tr_variantDictAddInt(d, TR_KEY_anti_brute_force_threshold, 100);
    tr_variantDictAddBool(d, TR_KEY_anti_brute_force_enabled, true);
    tr_variantDictAddInt(d, TR_KEY_verify_threads, 1);
}

void tr_sessionGetSettings(tr_session* s, tr_variant* d)
{
    TR_ASSERT(tr_variantIsDict(d));

    tr_variantDictReserve(d, 63);
    tr_variantDictAddBool(d, TR_KEY_blocklist_enabled, tr_blocklistIsEnabled(s));
    tr_variantDictAddStr(d, TR_KEY_blocklist_url, tr_blocklistGetURL(s));
    tr_variantDictAddInt(d, TR_KEY_cache_size_mb, tr_sessionGetCacheLimit_MB(s));
    tr_variantDictAddBool(d, TR_KEY_dht_enabled, s->isDHTEnabled);
    tr_variantDictAddBool(d, TR_KEY_utp_enabled, s->isUTPEnabled);
    tr_variantDictAddBool(d, TR_KEY_lpd_enabled, s->isLPDEnabled);
    tr_variantDictAddStr(d, TR_KEY_download_dir, tr_sessionGetDownloadDir(s));
    tr_variantDictAddInt(d, TR_KEY_download_queue_size, tr_sessionGetQueueSize(s, TR_DOWN));
    tr_variantDictAddBool(d, TR_KEY_download_queue_enabled, tr_sessionGetQueueEnabled(s, TR_DOWN));
    tr_variantDictAddInt(d, TR_KEY_speed_limit_down, tr_sessionGetSpeedLimit_KBps(s, TR_DOWN));
    tr_variantDictAddBool(d, TR_KEY_speed_limit_down_enabled, tr_sessionIsSpeedLimited(s, TR_DOWN));
    tr_variantDictAddInt(d, TR_KEY_encryption, s->encryptionMode);
    tr_variantDictAddInt(d, TR_KEY_idle_seeding_limit, tr_sessionGetIdleLimit(s));
    tr_variantDictAddBool(d, TR_KEY_idle_seeding_limit_enabled, tr_sessionIsIdleLimited(s));
    tr_variantDictAddStr(d, TR_KEY_incomplete_dir, tr_sessionGetIncompleteDir(s));
    tr_variantDictAddBool(d, TR_KEY_incomplete_dir_enabled, tr_sessionIsIncompleteDirEnabled(s));
    tr_variantDictAddInt(d, TR_KEY_message_level, tr_logGetLevel());
    tr_variantDictAddInt(d, TR_KEY_peer_limit_global, s->peerLimit);
    tr_variantDictAddInt(d, TR_KEY_peer_limit_per_torrent, s->peerLimitPerTorrent);
    tr_variantDictAddInt(d, TR_KEY_peer_port, tr_sessionGetPeerPort(s));
    tr_variantDictAddBool(d, TR_KEY_peer_port_random_on_start, s->isPortRandom);
    tr_variantDictAddInt(d, TR_KEY_peer_port_random_low, s->randomPortLow);
    tr_variantDictAddInt(d, TR_KEY_peer_port_random_high, s->randomPortHigh);
    tr_variantDictAddStr(d, TR_KEY_peer_socket_tos, format_tos(s->peerSocketTOS));
    tr_variantDictAddStr(d, TR_KEY_peer_congestion_algorithm, s->peer_congestion_algorithm);
    tr_variantDictAddBool(d, TR_KEY_pex_enabled, s->isPexEnabled);
    tr_variantDictAddBool(d, TR_KEY_port_forwarding_enabled, tr_sessionIsPortForwardingEnabled(s));
    tr_variantDictAddInt(d, TR_KEY_preallocation, s->preallocationMode);
    tr_variantDictAddBool(d, TR_KEY_prefetch_enabled, s->isPrefetchEnabled);
    tr_variantDictAddInt(d, TR_KEY_peer_id_ttl_hours, s->peer_id_ttl_hours);
    tr_variantDictAddBool(d, TR_KEY_queue_stalled_enabled, tr_sessionGetQueueStalledEnabled(s));
    tr_variantDictAddInt(d, TR_KEY_queue_stalled_minutes, tr_sessionGetQueueStalledMinutes(s));
    tr_variantDictAddReal(d, TR_KEY_ratio_limit, s->desiredRatio);
    tr_variantDictAddBool(d, TR_KEY_ratio_limit_enabled, s->isRatioLimited);
    tr_variantDictAddBool(d, TR_KEY_rename_partial_files, tr_sessionIsIncompleteFileNamingEnabled(s));
    tr_variantDictAddBool(d, TR_KEY_rpc_authentication_required, tr_sessionIsRPCPasswordEnabled(s));
    tr_variantDictAddStr(d, TR_KEY_rpc_bind_address, tr_sessionGetRPCBindAddress(s));
    tr_variantDictAddBool(d, TR_KEY_rpc_enabled, tr_sessionIsRPCEnabled(s));
    tr_variantDictAddStr(d, TR_KEY_rpc_password, tr_sessionGetRPCPassword(s));
    tr_variantDictAddInt(d, TR_KEY_rpc_port, tr_sessionGetRPCPort(s));
    tr_variantDictAddStr(d, TR_KEY_rpc_url, tr_sessionGetRPCUrl(s));
    tr_variantDictAddStr(d, TR_KEY_rpc_username, tr_sessionGetRPCUsername(s));
    tr_variantDictAddStr(d, TR_KEY_rpc_whitelist, tr_sessionGetRPCWhitelist(s));
    tr_variantDictAddBool(d, TR_KEY_rpc_whitelist_enabled, tr_sessionGetRPCWhitelistEnabled(s));
    tr_variantDictAddBool(d, TR_KEY_scrape_paused_torrents_enabled, s->scrapePausedTorrents);
    tr_variantDictAddBool(d, TR_KEY_script_torrent_done_enabled, tr_sessionIsTorrentDoneScriptEnabled(s));
    tr_variantDictAddStr(d, TR_KEY_script_torrent_done_filename, tr_sessionGetTorrentDoneScript(s));
    tr_variantDictAddInt(d, TR_KEY_seed_queue_size, tr_sessionGetQueueSize(s, TR_UP));
    tr_variantDictAddBool(d, TR_KEY_seed_queue_enabled, tr_sessionGetQueueEnabled(s, TR_UP));
    tr_variantDictAddBool(d, TR_KEY_alt_speed_enabled, tr_sessionUsesAltSpeed(s));
    tr_variantDictAddInt(d, TR_KEY_alt_speed_up, tr_sessionGetAltSpeed_KBps(s, TR_UP));
    tr_variantDictAddInt(d, TR_KEY_alt_speed_down, tr_sessionGetAltSpeed_KBps(s, TR_DOWN));
    tr_variantDictAddInt(d, TR_KEY_alt_speed_time_begin, tr_sessionGetAltSpeedBegin(s));
    tr_variantDictAddBool(d, TR_KEY_alt_speed_time_enabled, tr_sessionUsesAltSpeedTime(s));
    tr_variantDictAddInt(d, TR_KEY_alt_speed_time_end, tr_sessionGetAltSpeedEnd(s));
    tr_variantDictAddInt(d, TR_KEY_alt_speed_time_day, tr_sessionGetAltSpeedDay(s));
    tr_variantDictAddInt(d, TR_KEY_speed_limit_up, tr_sessionGetSpeedLimit_KBps(s, TR_UP));
    tr_variantDictAddBool(d, TR_KEY_speed_limit_up_enabled, tr_sessionIsSpeedLimited(s, TR_UP));
    tr_variantDictAddInt(d, TR_KEY_umask, s->umask);
    tr_variantDictAddInt(d, TR_KEY_upload_slots_per_torrent, s->uploadSlotsPerTorrent);
    tr_variantDictAddStr(d, TR_KEY_bind_address_ipv4, tr_address_to_string(&s->bind_ipv4->addr));
    tr_variantDictAddStr(d, TR_KEY_bind_address_ipv6, tr_address_to_string(&s->bind_ipv6->addr));
    tr_variantDictAddBool(d, TR_KEY_start_added_torrents, !tr_sessionGetPaused(s));
    tr_variantDictAddBool(d, TR_KEY_trash_original_torrent_files, tr_sessionGetDeleteSource(s));
    tr_variantDictAddInt(d, TR_KEY_anti_brute_force_threshold, tr_sessionGetAntiBruteForceThreshold(s));
    tr_variantDictAddBool(d, TR_KEY_anti_brute_force_enabled, tr_sessionGetAntiBruteForceEnabled(s));
    tr_variantDictAddInt(d, TR_KEY_verify_threads, tr_verifyGetParallelism(s->verifier));
}

bool tr_sessionLoadSettings(tr_variant* dict, char const* configDir, char const* appName)
{
    TR_ASSERT(tr_variantIsDict(dict));

    char* filename;
    tr_variant oldDict;
    tr_variant fileSettings;
    bool success;
    tr_error* error = nullptr;

    /* initializing the defaults: caller may have passed in some app-level defaults.
     * preserve those and use the session defaults to fill in any missing gaps. */
    oldDict = *dict;
    tr_variantInitDict(dict, 0);
    tr_sessionGetDefaultSettings(dict);
    tr_variantMergeDicts(dict, &oldDict);
    tr_variantFree(&oldDict);

    /* if caller didn't specify a config dir, use the default */
    if (tr_str_is_empty(configDir))
    {
        configDir = tr_getDefaultConfigDir(appName);
    }

    /* file settings override the defaults */
    filename = tr_buildPath(configDir, "settings.json", nullptr);

    if (tr_variantFromFile(&fileSettings, TR_VARIANT_FMT_JSON, filename, &error))
    {
        tr_variantMergeDicts(dict, &fileSettings);
        tr_variantFree(&fileSettings);
        success = true;
    }
    else
    {
        success = TR_ERROR_IS_ENOENT(error->code);
        tr_error_free(error);
    }

    /* cleanup */
    tr_free(filename);
    return success;
}

void tr_sessionSaveSettings(tr_session* session, char const* configDir, tr_variant const* clientSettings)
{
    TR_ASSERT(tr_variantIsDict(clientSettings));

    tr_variant settings;
    char* filename = tr_buildPath(configDir, "settings.json", nullptr);

    tr_variantInitDict(&settings, 0);

    /* the existing file settings are the fallback values */
    {
        tr_variant fileSettings;

        if (tr_variantFromFile(&fileSettings, TR_VARIANT_FMT_JSON, filename, nullptr))
        {
            tr_variantMergeDicts(&settings, &fileSettings);
            tr_variantFree(&fileSettings);
        }
    }

    /* the client's settings override the file settings */
    tr_variantMergeDicts(&settings, clientSettings);

    /* the session's true values override the file & client settings */
    {
        tr_variant sessionSettings;
        tr_variantInitDict(&sessionSettings, 0);
        tr_sessionGetSettings(session, &sessionSettings);
        tr_variantMergeDicts(&settings, &sessionSettings);
        tr_variantFree(&sessionSettings);
    }

    /* save the result */
    tr_variantToFile(&settings, TR_VARIANT_FMT_JSON, filename);

    /* cleanup */
    tr_free(filename);
    tr_variantFree(&settings);
}

/***
****
***/

/**
 * Periodically save the .resume files of any torrents whose
 * status has recently changed. This prevents loss of metadata
 * in the case of a crash, unclean shutdown, clumsy user, etc.
 */
static void onSaveTimer(evutil_socket_t fd, short what, void* vsession)
{
    TR_UNUSED(fd);
    TR_UNUSED(what);

    auto* session = static_cast<tr_session*>(vsession);

    if (tr_cacheFlushDone(session->cache) != 0)
    {
        tr_logAddError("Error while flushing completed pieces from cache");
    }

    for (auto* tor : session->torrents)
    {
        tr_torrentSave(tor);
    }

    tr_statsSaveDirty(session);

    tr_timerAdd(session->saveTimer, SAVE_INTERVAL_SECS, 0);
}

/***
****
***/

static void tr_sessionInitImpl(void*);

struct init_data
{
    bool done;
    bool messageQueuingEnabled;
    tr_session* session;
    char const* configDir;
    tr_variant* clientSettings;
};

tr_session* tr_sessionInit(char const* configDir, bool messageQueuingEnabled, tr_variant* clientSettings)
{
    TR_ASSERT(tr_variantIsDict(clientSettings));

    int64_t i;
    struct init_data data;

    tr_timeUpdate(time(nullptr));

    /* initialize the bare skeleton of the session object */
    auto* session = new tr_session{};
    session->udp_socket = TR_BAD_SOCKET;
    session->udp6_socket = TR_BAD_SOCKET;
    session->lock = tr_lockNew();
    session->cache = tr_cacheNew(1024 * 1024 * 2);
    session->magicNumber = SESSION_MAGIC_NUMBER;
    session->session_id = tr_session_id_new();
    tr_bandwidthConstruct(&session->bandwidth, nullptr);
    tr_variantInitList(&session->removedTorrents, 0);

    /* nice to start logging at the very beginning */
    if (tr_variantDictFindInt(clientSettings, TR_KEY_message_level, &i))
    {
        tr_logSetLevel(tr_log_level(i));
    }

    /* start the libtransmission thread */
    tr_net_init(); /* must go before tr_eventInit */
    tr_eventInit(session);
    TR_ASSERT(session->events != nullptr);

    /* run the rest in the libtransmission thread */
    data.done = false;
    data.session = session;
    data.configDir = configDir;
    data.messageQueuingEnabled = messageQueuingEnabled;
    data.clientSettings = clientSettings;
    tr_runInEventThread(session, tr_sessionInitImpl, &data);

    while (!data.done)
    {
        tr_wait_msec(50);
    }

    return session;
}

static void turtleCheckClock(tr_session* s, struct tr_turtle_info* t);

static void onNowTimer(evutil_socket_t fd, short what, void* vsession)
{
    TR_UNUSED(fd);
    TR_UNUSED(what);

    auto* session = static_cast<tr_session*>(vsession);

    TR_ASSERT(tr_isSession(session));
    TR_ASSERT(session->nowTimer != nullptr);

    int usec;
    int const min = 100;
    int const max = 999999;
    struct timeval tv;
    time_t const now = time(nullptr);

    /**
    ***  tr_session things to do once per second
    **/

    tr_timeUpdate(now);

    tr_dhtUpkeep(session);

    if (session->turtle.isClockEnabled)
    {
        turtleCheckClock(session, &session->turtle);
    }

    // TODO: this seems a little silly. Why do we increment this
    // every second instead of computing the value as needed by
    // subtracting the current time from a start time?
    for (auto* tor : session->torrents)
    {
        if (tor->isRunning)
        {
            if (tr_torrentIsSeed(tor))
            {
                ++tor->secondsSeeding;
            }
            else
            {
                ++tor->secondsDownloading;
            }
        }
    }

    /**
    ***  Set the timer
    **/

    /* schedule the next timer for right after the next second begins */
    tr_gettimeofday(&tv);
    usec = 1000000 - tv.tv_usec;

    if (usec > max)
    {
        usec = max;
    }

    if (usec < min)
    {
        usec = min;
    }

    tr_timerAdd(session->nowTimer, 0, usec);
}

static void loadBlocklists(tr_session* session);

static void tr_sessionInitImpl(void* vdata)
{
    auto* data = static_cast<struct init_data*>(vdata);
    tr_variant const* const clientSettings = data->clientSettings;
    tr_session* session = data->session;

    TR_ASSERT(tr_amInEventThread(session));
    TR_ASSERT(tr_variantIsDict(clientSettings));

    dbgmsg("tr_sessionInit: the session's top-level bandwidth object is %p", (void*)&session->bandwidth);

    tr_variant settings;

    tr_variantInitDict(&settings, 0);
    tr_sessionGetDefaultSettings(&settings);
    tr_variantMergeDicts(&settings, clientSettings);

    TR_ASSERT(session->event_base != nullptr);
    session->nowTimer = evtimer_new(session->event_base, onNowTimer, session);
    onNowTimer(0, 0, session);

#ifndef _WIN32
    /* Don't exit when writing on a broken socket */
    signal(SIGPIPE, SIG_IGN);
#endif

    tr_logSetQueueEnabled(data->messageQueuingEnabled);

    tr_setConfigDir(session, data->configDir);

    session->peerMgr = tr_peerMgrNew(session);

    session->shared = tr_sharedInit(session);

    session->verifier = tr_verifyInit();

    /**
    ***  Blocklist
    **/

    {
        char* filename = tr_buildPath(session->configDir, "blocklists", nullptr);
        tr_sys_dir_create(filename, TR_SYS_DIR_CREATE_PARENTS, 0777, nullptr);
        tr_free(filename);
        loadBlocklists(session);
    }

    TR_ASSERT(tr_isSession(session));

    session->saveTimer = evtimer_new(session->event_base, onSaveTimer, session);
    tr_timerAdd(session->saveTimer, SAVE_INTERVAL_SECS, 0);

    tr_announcerInit(session);

    /* first %s is the application name
       second %s is the version number */
    tr_logAddInfo(_("%s %s started"), TR_NAME, LONG_VERSION_STRING);

    tr_statsInit(session);

    tr_sessionSet(session, &settings);

    tr_udpInit(session);

    if (session->isLPDEnabled)
    {
        tr_lpdInit(session, &session->bind_ipv4->addr);
    }

    /* cleanup */
    tr_variantFree(&settings);
    data->done = true;
}

static void turtleBootstrap(tr_session*, struct tr_turtle_info*);
static void setPeerPort(tr_session* session, tr_port port);

static void sessionSetImpl(void* vdata)
{
    auto* data = static_cast<struct init_data*>(vdata);
    tr_session* session = data->session;
    tr_variant* settings = data->clientSettings;

    TR_ASSERT(tr_isSession(session));
    TR_ASSERT(tr_variantIsDict(settings));
    TR_ASSERT(tr_amInEventThread(session));

    int64_t i;
    double d;
    bool boolVal;
    char const* strVal;
    struct tr_bindinfo b;
    struct tr_turtle_info* turtle = &session->turtle;

    if (tr_variantDictFindInt(settings, TR_KEY_message_level, &i))
    {
        tr_logSetLevel(tr_log_level(i));
    }

#ifndef _WIN32

    if (tr_variantDictFindInt(settings, TR_KEY_umask, &i))
    {
        session->umask = (mode_t)i;
        umask(session->umask);
    }

#endif

    /* misc features */
    if (tr_variantDictFindInt(settings, TR_KEY_cache_size_mb, &i))
    {
        tr_sessionSetCacheLimit_MB(session, i);
    }

    if (tr_variantDictFindInt(settings, TR_KEY_peer_limit_per_torrent, &i))
    {
        tr_sessionSetPeerLimitPerTorrent(session, i);
    }

    if (tr_variantDictFindBool(settings, TR_KEY_pex_enabled, &boolVal))
    {
        tr_sessionSetPexEnabled(session, boolVal);
    }

    if (tr_variantDictFindBool(settings, TR_KEY_dht_enabled, &boolVal))
    {
        tr_sessionSetDHTEnabled(session, boolVal);
    }

    if (tr_variantDictFindBool(settings, TR_KEY_utp_enabled, &boolVal))
    {
        tr_sessionSetUTPEnabled(session, boolVal);
    }

    if (tr_variantDictFindBool(settings, TR_KEY_lpd_enabled, &boolVal))
    {
        tr_sessionSetLPDEnabled(session, boolVal);
    }

    if (tr_variantDictFindInt(settings, TR_KEY_encryption, &i))
    {
        tr_sessionSetEncryption(session, tr_encryption_mode(i));
    }

    if (tr_variantDictFindStr(settings, TR_KEY_peer_socket_tos, &strVal, nullptr))
    {
        session->peerSocketTOS = parse_tos(strVal);
    }

    if (tr_variantDictFindStr(settings, TR_KEY_peer_congestion_algorithm, &strVal, nullptr))
    {
        session->peer_congestion_algorithm = tr_strdup(strVal);
    }
    else
    {
        session->peer_congestion_algorithm = tr_strdup("");
    }

    if (tr_variantDictFindBool(settings, TR_KEY_blocklist_enabled, &boolVal))
    {
        tr_blocklistSetEnabled(session, boolVal);
    }

    if (tr_variantDictFindStr(settings, TR_KEY_blocklist_url, &strVal, nullptr))
    {
        tr_blocklistSetURL(session, strVal);
    }

    if (tr_variantDictFindBool(settings, TR_KEY_start_added_torrents, &boolVal))
    {
        tr_sessionSetPaused(session, !boolVal);
    }

    if (tr_variantDictFindBool(settings, TR_KEY_trash_original_torrent_files, &boolVal))
    {
        tr_sessionSetDeleteSource(session, boolVal);
    }

    if (tr_variantDictFindInt(settings, TR_KEY_peer_id_ttl_hours, &i))
    {
        session->peer_id_ttl_hours = i;
    }

    /* torrent queues */
    if (tr_variantDictFindInt(settings, TR_KEY_queue_stalled_minutes, &i))
    {
        tr_sessionSetQueueStalledMinutes(session, i);
    }

    if (tr_variantDictFindBool(settings, TR_KEY_queue_stalled_enabled, &boolVal))
    {
        tr_sessionSetQueueStalledEnabled(session, boolVal);
    }

    if (tr_variantDictFindInt(settings, TR_KEY_download_queue_size, &i))
    {
        tr_sessionSetQueueSize(session, TR_DOWN, i);
    }

    if (tr_variantDictFindBool(settings, TR_KEY_download_queue_enabled, &boolVal))
    {
        tr_sessionSetQueueEnabled(session, TR_DOWN, boolVal);
    }

    if (tr_variantDictFindInt(settings, TR_KEY_seed_queue_size, &i))
    {
        tr_sessionSetQueueSize(session, TR_UP, i);
    }

    if (tr_variantDictFindBool(settings, TR_KEY_seed_queue_enabled, &boolVal))
    {
        tr_sessionSetQueueEnabled(session, TR_UP, boolVal);
    }

    /* files and directories */
    if (tr_variantDictFindBool(settings, TR_KEY_prefetch_enabled, &boolVal))
    {
        session->isPrefetchEnabled = boolVal;
    }

    if (tr_variantDictFindInt(settings, TR_KEY_preallocation, &i))
    {
        session->preallocationMode = tr_preallocation_mode(i);
    }

    if (tr_variantDictFindStr(settings, TR_KEY_download_dir, &strVal, nullptr))
    {
        tr_sessionSetDownloadDir(session, strVal);
    }

    if (tr_variantDictFindStr(settings, TR_KEY_incomplete_dir, &strVal, nullptr))
    {
        tr_sessionSetIncompleteDir(session, strVal);
    }

    if (tr_variantDictFindBool(settings, TR_KEY_incomplete_dir_enabled, &boolVal))
    {
        tr_sessionSetIncompleteDirEnabled(session, boolVal);
    }

    if (tr_variantDictFindBool(settings, TR_KEY_rename_partial_files, &boolVal))
    {
        tr_sessionSetIncompleteFileNamingEnabled(session, boolVal);
    }

    /* rpc server */
    if (session->rpcServer != nullptr) /* close the old one */
    {
        tr_rpcClose(&session->rpcServer);
    }

    session->rpcServer = tr_rpcInit(session, settings);

    /* public addresses */

    free_incoming_peer_port(session);

    if (!tr_variantDictFindStr(settings, TR_KEY_bind_address_ipv4, &strVal, nullptr) ||
        !tr_address_from_string(&b.addr, strVal) || b.addr.type != TR_AF_INET)
    {
        b.addr = tr_inaddr_any;
    }

    b.socket = TR_BAD_SOCKET;
    session->bind_ipv4 = static_cast<struct tr_bindinfo*>(tr_memdup(&b, sizeof(struct tr_bindinfo)));

    if (!tr_variantDictFindStr(settings, TR_KEY_bind_address_ipv6, &strVal, nullptr) ||
        !tr_address_from_string(&b.addr, strVal) || b.addr.type != TR_AF_INET6)
    {
        b.addr = tr_in6addr_any;
    }

    b.socket = TR_BAD_SOCKET;
    session->bind_ipv6 = static_cast<tr_bindinfo*>(tr_memdup(&b, sizeof(struct tr_bindinfo)));

    /* incoming peer port */
    if (tr_variantDictFindInt(settings, TR_KEY_peer_port_random_low, &i))
    {
        session->randomPortLow = i;
    }

    if (tr_variantDictFindInt(settings, TR_KEY_peer_port_random_high, &i))
    {
        session->randomPortHigh = i;
    }

    if (tr_variantDictFindBool(settings, TR_KEY_peer_port_random_on_start, &boolVal))
    {
        tr_sessionSetPeerPortRandomOnStart(session, boolVal);
    }

    if (!tr_variantDictFindInt(settings, TR_KEY_peer_port, &i))
    {
        i = session->private_peer_port;
    }

    setPeerPort(session, boolVal ? getRandomPort(session) : i);

    if (tr_variantDictFindBool(settings, TR_KEY_port_forwarding_enabled, &boolVal))
    {
        tr_sessionSetPortForwardingEnabled(session, boolVal);
    }

    if (tr_variantDictFindInt(settings, TR_KEY_peer_limit_global, &i))
    {
        session->peerLimit = i;
    }

    /**
    **/

    if (tr_variantDictFindInt(settings, TR_KEY_upload_slots_per_torrent, &i))
    {
        session->uploadSlotsPerTorrent = i;
    }

    if (tr_variantDictFindInt(settings, TR_KEY_speed_limit_up, &i))
    {
        tr_sessionSetSpeedLimit_KBps(session, TR_UP, i);
    }

    if (tr_variantDictFindBool(settings, TR_KEY_speed_limit_up_enabled, &boolVal))
    {
        tr_sessionLimitSpeed(session, TR_UP, boolVal);
    }

    if (tr_variantDictFindInt(settings, TR_KEY_speed_limit_down, &i))
    {
        tr_sessionSetSpeedLimit_KBps(session, TR_DOWN, i);
    }

    if (tr_variantDictFindBool(settings, TR_KEY_speed_limit_down_enabled, &boolVal))
    {
        tr_sessionLimitSpeed(session, TR_DOWN, boolVal);
    }

    if (tr_variantDictFindReal(settings, TR_KEY_ratio_limit, &d))
    {
        tr_sessionSetRatioLimit(session, d);
    }

    if (tr_variantDictFindBool(settings, TR_KEY_ratio_limit_enabled, &boolVal))
    {
        tr_sessionSetRatioLimited(session, boolVal);
    }

    if (tr_variantDictFindInt(settings, TR_KEY_idle_seeding_limit, &i))
    {
        tr_sessionSetIdleLimit(session, i);
    }

    if (tr_variantDictFindBool(settings, TR_KEY_idle_seeding_limit_enabled, &boolVal))
    {
        tr_sessionSetIdleLimited(session, boolVal);
    }

    /**
    ***  Turtle Mode
    **/

    /* update the turtle mode's fields */
    if (tr_variantDictFindInt(settings, TR_KEY_alt_speed_up, &i))
    {
        turtle->speedLimit_Bps[TR_UP] = toSpeedBytes(i);
    }

    if (tr_variantDictFindInt(settings, TR_KEY_alt_speed_down, &i))
    {
        turtle->speedLimit_Bps[TR_DOWN] = toSpeedBytes(i);
    }

    if (tr_variantDictFindInt(settings, TR_KEY_alt_speed_time_begin, &i))
    {
        turtle->beginMinute = i;
    }

    if (tr_variantDictFindInt(settings, TR_KEY_alt_speed_time_end, &i))
    {
        turtle->endMinute = i;
    }

    if (tr_variantDictFindInt(settings, TR_KEY_alt_speed_time_day, &i))
    {
        turtle->days = tr_sched_day(i);
    }

    if (tr_variantDictFindBool(settings, TR_KEY_alt_speed_time_enabled, &boolVal))
    {
        turtle->isClockEnabled = boolVal;
    }

    if (tr_variantDictFindBool(settings, TR_KEY_alt_speed_enabled, &boolVal))
    {
        turtle->isEnabled = boolVal;
    }

    turtleBootstrap(session, turtle);

    /**
    ***  Scripts
    **/

    if (tr_variantDictFindBool(settings, TR_KEY_script_torrent_done_enabled, &boolVal))
    {
        tr_sessionSetTorrentDoneScriptEnabled(session, boolVal);
    }

    if (tr_variantDictFindStr(settings, TR_KEY_script_torrent_done_filename, &strVal, nullptr))
    {
        tr_sessionSetTorrentDoneScript(session, strVal);
    }

    if (tr_variantDictFindBool(settings, TR_KEY_scrape_paused_torrents_enabled, &boolVal))
    {
        session->scrapePausedTorrents = boolVal;
    }

    /**
    ***  BruteForce
    **/

    if (tr_variantDictFindInt(settings, TR_KEY_anti_brute_force_threshold, &i))
    {
        tr_sessionSetAntiBruteForceThreshold(session, i);
    }

    if (tr_variantDictFindBool(settings, TR_KEY_anti_brute_force_enabled, &boolVal))
    {
        tr_sessionSetAntiBruteForceEnabled(session, boolVal);
    }

    /**
    ***  Verifier
    **/

    if (tr_variantDictFindInt(settings, TR_KEY_verify_threads, &i))
    {
        tr_verifySetParallelism(session->verifier, i);
    }

    data->done = true;
}

void tr_sessionSet(tr_session* session, tr_variant* settings)
{
    struct init_data data;
    data.done = false;
    data.session = session;
    data.clientSettings = settings;

    /* run the rest in the libtransmission thread */
    tr_runInEventThread(session, sessionSetImpl, &data);

    while (!data.done)
    {
        tr_wait_msec(100);
    }
}

/***
****
***/

void tr_sessionSetDownloadDir(tr_session* session, char const* dir)
{
    TR_ASSERT(tr_isSession(session));

    struct tr_device_info* info = nullptr;

    if (dir != nullptr)
    {
        info = tr_device_info_create(dir);
    }

    tr_device_info_free(session->downloadDir);
    session->downloadDir = info;
}

char const* tr_sessionGetDownloadDir(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    char const* dir = nullptr;

    if (session != nullptr && session->downloadDir != nullptr)
    {
        dir = session->downloadDir->path;
    }

    return dir;
}

int64_t tr_sessionGetDirFreeSpace(tr_session* session, char const* dir)
{
    int64_t free_space;

    if (tr_strcmp0(dir, tr_sessionGetDownloadDir(session)) == 0)
    {
        free_space = tr_device_info_get_free_space(session->downloadDir);
    }
    else
    {
        free_space = tr_getDirFreeSpace(dir);
    }

    return free_space;
}

/***
****
***/

void tr_sessionSetIncompleteFileNamingEnabled(tr_session* session, bool b)
{
    TR_ASSERT(tr_isSession(session));

    session->isIncompleteFileNamingEnabled = b;
}

bool tr_sessionIsIncompleteFileNamingEnabled(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return session->isIncompleteFileNamingEnabled;
}

/***
****
***/

void tr_sessionSetIncompleteDir(tr_session* session, char const* dir)
{
    TR_ASSERT(tr_isSession(session));

    if (session->incompleteDir != dir)
    {
        tr_free(session->incompleteDir);

        session->incompleteDir = tr_strdup(dir);
    }
}

char const* tr_sessionGetIncompleteDir(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return session->incompleteDir;
}

void tr_sessionSetIncompleteDirEnabled(tr_session* session, bool b)
{
    TR_ASSERT(tr_isSession(session));

    session->isIncompleteDirEnabled = b;
}

bool tr_sessionIsIncompleteDirEnabled(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return session->isIncompleteDirEnabled;
}

/***
****
***/

void tr_sessionLock(tr_session* session)
{
    TR_ASSERT(tr_isSession(session));

    tr_lockLock(session->lock);
}

void tr_sessionUnlock(tr_session* session)
{
    TR_ASSERT(tr_isSession(session));

    tr_lockUnlock(session->lock);
}

bool tr_sessionIsLocked(tr_session const* session)
{
    return tr_isSession(session) && tr_lockHave(session->lock);
}

/***
****  Peer Port
***/

static void peerPortChanged(void* vsession)
{
    auto* session = static_cast<tr_session*>(vsession);
    TR_ASSERT(tr_isSession(session));

    close_incoming_peer_port(session);
    open_incoming_peer_port(session);
    tr_sharedPortChanged(session);

    for (auto* tor : session->torrents)
    {
        tr_torrentChangeMyPort(tor);
    }
}

static void setPeerPort(tr_session* session, tr_port port)
{
    session->private_peer_port = port;
    session->public_peer_port = port;

    tr_runInEventThread(session, peerPortChanged, session);
}

void tr_sessionSetPeerPort(tr_session* session, tr_port port)
{
    if (tr_isSession(session) && session->private_peer_port != port)
    {
        setPeerPort(session, port);
    }
}

tr_port tr_sessionGetPeerPort(tr_session const* session)
{
    return tr_isSession(session) ? session->private_peer_port : 0;
}

tr_port tr_sessionSetPeerPortRandom(tr_session* session)
{
    TR_ASSERT(tr_isSession(session));

    tr_sessionSetPeerPort(session, getRandomPort(session));
    return session->private_peer_port;
}

void tr_sessionSetPeerPortRandomOnStart(tr_session* session, bool random)
{
    TR_ASSERT(tr_isSession(session));

    session->isPortRandom = random;
}

bool tr_sessionGetPeerPortRandomOnStart(tr_session* session)
{
    TR_ASSERT(tr_isSession(session));

    return session->isPortRandom;
}

tr_port_forwarding tr_sessionGetPortForwarding(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return tr_port_forwarding(tr_sharedTraversalStatus(session->shared));
}

/***
****
***/

void tr_sessionSetRatioLimited(tr_session* session, bool isLimited)
{
    TR_ASSERT(tr_isSession(session));

    session->isRatioLimited = isLimited;
}

void tr_sessionSetRatioLimit(tr_session* session, double desiredRatio)
{
    TR_ASSERT(tr_isSession(session));

    session->desiredRatio = desiredRatio;
}

bool tr_sessionIsRatioLimited(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return session->isRatioLimited;
}

double tr_sessionGetRatioLimit(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return session->desiredRatio;
}

/***
****
***/

void tr_sessionSetIdleLimited(tr_session* session, bool isLimited)
{
    TR_ASSERT(tr_isSession(session));

    session->isIdleLimited = isLimited;
}

void tr_sessionSetIdleLimit(tr_session* session, uint16_t idleMinutes)
{
    TR_ASSERT(tr_isSession(session));

    session->idleLimitMinutes = idleMinutes;
}

bool tr_sessionIsIdleLimited(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return session->isIdleLimited;
}

uint16_t tr_sessionGetIdleLimit(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return session->idleLimitMinutes;
}

/***
****
****  SPEED LIMITS
****
***/

static unsigned int tr_sessionGetAltSpeed_Bps(tr_session const* s, tr_direction d);

bool tr_sessionGetActiveSpeedLimit_Bps(tr_session const* session, tr_direction dir, unsigned int* setme_Bps)
{
    bool isLimited = true;

    if (!tr_isSession(session))
    {
        return false;
    }

    if (tr_sessionUsesAltSpeed(session))
    {
        *setme_Bps = tr_sessionGetAltSpeed_Bps(session, dir);
    }
    else if (tr_sessionIsSpeedLimited(session, dir))
    {
        *setme_Bps = tr_sessionGetSpeedLimit_Bps(session, dir);
    }
    else
    {
        isLimited = false;
    }

    return isLimited;
}

bool tr_sessionGetActiveSpeedLimit_KBps(tr_session const* session, tr_direction dir, double* setme_KBps)
{
    unsigned int Bps = 0;
    bool const is_active = tr_sessionGetActiveSpeedLimit_Bps(session, dir, &Bps);
    *setme_KBps = toSpeedKBps(Bps);
    return is_active;
}

static void updateBandwidth(tr_session* session, tr_direction dir)
{
    unsigned int limit_Bps = 0;
    bool const isLimited = tr_sessionGetActiveSpeedLimit_Bps(session, dir, &limit_Bps);
    bool const zeroCase = isLimited && limit_Bps == 0;

    tr_bandwidthSetLimited(&session->bandwidth, dir, isLimited && !zeroCase);

    tr_bandwidthSetDesiredSpeed_Bps(&session->bandwidth, dir, limit_Bps);
}

enum
{
    MINUTES_PER_HOUR = 60,
    MINUTES_PER_DAY = MINUTES_PER_HOUR * 24,
    MINUTES_PER_WEEK = MINUTES_PER_DAY * 7
};

static void turtleUpdateTable(struct tr_turtle_info* t)
{
    tr_bitfield* b = &t->minutes;

    tr_bitfieldSetHasNone(b);

    for (int day = 0; day < 7; ++day)
    {
        if ((t->days & (1 << day)) != 0)
        {
            time_t const begin = t->beginMinute;
            time_t end = t->endMinute;

            if (end <= begin)
            {
                end += MINUTES_PER_DAY;
            }

            for (time_t i = begin; i < end; ++i)
            {
                tr_bitfieldAdd(b, (i + day * MINUTES_PER_DAY) % MINUTES_PER_WEEK);
            }
        }
    }
}

static void altSpeedToggled(void* vsession)
{
    auto* session = static_cast<tr_session*>(vsession);

    TR_ASSERT(tr_isSession(session));

    updateBandwidth(session, TR_UP);
    updateBandwidth(session, TR_DOWN);

    struct tr_turtle_info* t = &session->turtle;

    if (t->callback != nullptr)
    {
        (*t->callback)(session, t->isEnabled, t->changedByUser, t->callbackUserData);
    }
}

static void useAltSpeed(tr_session* s, struct tr_turtle_info* t, bool enabled, bool byUser)
{
    TR_ASSERT(tr_isSession(s));
    TR_ASSERT(t != nullptr);

    if (t->isEnabled != enabled)
    {
        t->isEnabled = enabled;
        t->changedByUser = byUser;
        tr_runInEventThread(s, altSpeedToggled, s);
    }
}

/**
 * @return whether turtle should be on/off according to the scheduler
 */
static bool getInTurtleTime(struct tr_turtle_info const* t)
{
    struct tm tm;
    size_t minute_of_the_week;
    time_t const now = tr_time();

    tr_localtime_r(&now, &tm);

    minute_of_the_week = tm.tm_wday * MINUTES_PER_DAY + tm.tm_hour * MINUTES_PER_HOUR + tm.tm_min;

    if (minute_of_the_week >= MINUTES_PER_WEEK) /* leap minutes? */
    {
        minute_of_the_week = MINUTES_PER_WEEK - 1;
    }

    return tr_bitfieldHas(&t->minutes, minute_of_the_week);
}

static constexpr tr_auto_switch_state_t autoSwitchState(bool enabled)
{
    return enabled ? TR_AUTO_SWITCH_ON : TR_AUTO_SWITCH_OFF;
}

static void turtleCheckClock(tr_session* s, struct tr_turtle_info* t)
{
    TR_ASSERT(t->isClockEnabled);

    bool enabled = getInTurtleTime(t);
    tr_auto_switch_state_t newAutoTurtleState = autoSwitchState(enabled);
    bool alreadySwitched = t->autoTurtleState == newAutoTurtleState;

    if (!alreadySwitched)
    {
        tr_logAddInfo("Time to turn %s turtle mode!", enabled ? "on" : "off");
        t->autoTurtleState = newAutoTurtleState;
        useAltSpeed(s, t, enabled, false);
    }
}

/* Called after the turtle's fields are loaded from an outside source.
 * It initializes the implementation fields
 * and turns on turtle mode if the clock settings say to. */
static void turtleBootstrap(tr_session* session, struct tr_turtle_info* turtle)
{
    turtle->changedByUser = false;
    turtle->autoTurtleState = TR_AUTO_SWITCH_UNUSED;

    tr_bitfieldConstruct(&turtle->minutes, MINUTES_PER_WEEK);

    turtleUpdateTable(turtle);

    if (turtle->isClockEnabled)
    {
        turtle->isEnabled = getInTurtleTime(turtle);
        turtle->autoTurtleState = autoSwitchState(turtle->isEnabled);
    }

    altSpeedToggled(session);
}

/***
****  Primary session speed limits
***/

static void tr_sessionSetSpeedLimit_Bps(tr_session* s, tr_direction d, unsigned int Bps)
{
    TR_ASSERT(tr_isSession(s));
    TR_ASSERT(tr_isDirection(d));

    s->speedLimit_Bps[d] = Bps;

    updateBandwidth(s, d);
}

void tr_sessionSetSpeedLimit_KBps(tr_session* s, tr_direction d, unsigned int KBps)
{
    tr_sessionSetSpeedLimit_Bps(s, d, toSpeedBytes(KBps));
}

unsigned int tr_sessionGetSpeedLimit_Bps(tr_session const* s, tr_direction d)
{
    TR_ASSERT(tr_isSession(s));
    TR_ASSERT(tr_isDirection(d));

    return s->speedLimit_Bps[d];
}

unsigned int tr_sessionGetSpeedLimit_KBps(tr_session const* s, tr_direction d)
{
    return toSpeedKBps(tr_sessionGetSpeedLimit_Bps(s, d));
}

void tr_sessionLimitSpeed(tr_session* s, tr_direction d, bool b)
{
    TR_ASSERT(tr_isSession(s));
    TR_ASSERT(tr_isDirection(d));

    s->speedLimitEnabled[d] = b;

    updateBandwidth(s, d);
}

bool tr_sessionIsSpeedLimited(tr_session const* s, tr_direction d)
{
    TR_ASSERT(tr_isSession(s));
    TR_ASSERT(tr_isDirection(d));

    return s->speedLimitEnabled[d];
}

/***
****  Alternative speed limits that are used during scheduled times
***/

static void tr_sessionSetAltSpeed_Bps(tr_session* s, tr_direction d, unsigned int Bps)
{
    TR_ASSERT(tr_isSession(s));
    TR_ASSERT(tr_isDirection(d));

    s->turtle.speedLimit_Bps[d] = Bps;

    updateBandwidth(s, d);
}

void tr_sessionSetAltSpeed_KBps(tr_session* s, tr_direction d, unsigned int KBps)
{
    tr_sessionSetAltSpeed_Bps(s, d, toSpeedBytes(KBps));
}

static unsigned int tr_sessionGetAltSpeed_Bps(tr_session const* s, tr_direction d)
{
    TR_ASSERT(tr_isSession(s));
    TR_ASSERT(tr_isDirection(d));

    return s->turtle.speedLimit_Bps[d];
}

unsigned int tr_sessionGetAltSpeed_KBps(tr_session const* s, tr_direction d)
{
    return toSpeedKBps(tr_sessionGetAltSpeed_Bps(s, d));
}

static void userPokedTheClock(tr_session* s, struct tr_turtle_info* t)
{
    tr_logAddDebug("Refreshing the turtle mode clock due to user changes");

    t->autoTurtleState = TR_AUTO_SWITCH_UNUSED;

    turtleUpdateTable(t);

    if (t->isClockEnabled)
    {
        bool const enabled = getInTurtleTime(t);
        useAltSpeed(s, t, enabled, true);
        t->autoTurtleState = autoSwitchState(enabled);
    }
}

void tr_sessionUseAltSpeedTime(tr_session* s, bool b)
{
    TR_ASSERT(tr_isSession(s));

    struct tr_turtle_info* t = &s->turtle;

    if (t->isClockEnabled != b)
    {
        t->isClockEnabled = b;
        userPokedTheClock(s, t);
    }
}

bool tr_sessionUsesAltSpeedTime(tr_session const* s)
{
    TR_ASSERT(tr_isSession(s));

    return s->turtle.isClockEnabled;
}

void tr_sessionSetAltSpeedBegin(tr_session* s, int minute)
{
    TR_ASSERT(tr_isSession(s));
    TR_ASSERT(minute >= 0);
    TR_ASSERT(minute < 60 * 24);

    if (s->turtle.beginMinute != minute)
    {
        s->turtle.beginMinute = minute;
        userPokedTheClock(s, &s->turtle);
    }
}

int tr_sessionGetAltSpeedBegin(tr_session const* s)
{
    TR_ASSERT(tr_isSession(s));

    return s->turtle.beginMinute;
}

void tr_sessionSetAltSpeedEnd(tr_session* s, int minute)
{
    TR_ASSERT(tr_isSession(s));
    TR_ASSERT(minute >= 0);
    TR_ASSERT(minute < 60 * 24);

    if (s->turtle.endMinute != minute)
    {
        s->turtle.endMinute = minute;
        userPokedTheClock(s, &s->turtle);
    }
}

int tr_sessionGetAltSpeedEnd(tr_session const* s)
{
    TR_ASSERT(tr_isSession(s));

    return s->turtle.endMinute;
}

void tr_sessionSetAltSpeedDay(tr_session* s, tr_sched_day days)
{
    TR_ASSERT(tr_isSession(s));

    if (s->turtle.days != days)
    {
        s->turtle.days = days;
        userPokedTheClock(s, &s->turtle);
    }
}

tr_sched_day tr_sessionGetAltSpeedDay(tr_session const* s)
{
    TR_ASSERT(tr_isSession(s));

    return s->turtle.days;
}

void tr_sessionUseAltSpeed(tr_session* session, bool enabled)
{
    useAltSpeed(session, &session->turtle, enabled, true);
}

bool tr_sessionUsesAltSpeed(tr_session const* s)
{
    TR_ASSERT(tr_isSession(s));

    return s->turtle.isEnabled;
}

void tr_sessionSetAltSpeedFunc(tr_session* session, tr_altSpeedFunc func, void* userData)
{
    TR_ASSERT(tr_isSession(session));

    session->turtle.callback = func;
    session->turtle.callbackUserData = userData;
}

/***
****
***/

void tr_sessionSetPeerLimit(tr_session* session, uint16_t n)
{
    TR_ASSERT(tr_isSession(session));

    session->peerLimit = n;
}

uint16_t tr_sessionGetPeerLimit(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return session->peerLimit;
}

void tr_sessionSetPeerLimitPerTorrent(tr_session* session, uint16_t n)
{
    TR_ASSERT(tr_isSession(session));

    session->peerLimitPerTorrent = n;
}

uint16_t tr_sessionGetPeerLimitPerTorrent(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return session->peerLimitPerTorrent;
}

/***
****
***/

void tr_sessionSetPaused(tr_session* session, bool isPaused)
{
    TR_ASSERT(tr_isSession(session));

    session->pauseAddedTorrent = isPaused;
}

bool tr_sessionGetPaused(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return session->pauseAddedTorrent;
}

void tr_sessionSetDeleteSource(tr_session* session, bool deleteSource)
{
    TR_ASSERT(tr_isSession(session));

    session->deleteSourceTorrent = deleteSource;
}

bool tr_sessionGetDeleteSource(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return session->deleteSourceTorrent;
}

/***
****
***/

unsigned int tr_sessionGetPieceSpeed_Bps(tr_session const* session, tr_direction dir)
{
    return tr_isSession(session) ? tr_bandwidthGetPieceSpeed_Bps(&session->bandwidth, 0, dir) : 0;
}

static unsigned int tr_sessionGetRawSpeed_Bps(tr_session const* session, tr_direction dir)
{
    return tr_isSession(session) ? tr_bandwidthGetRawSpeed_Bps(&session->bandwidth, 0, dir) : 0;
}

double tr_sessionGetRawSpeed_KBps(tr_session const* session, tr_direction dir)
{
    return toSpeedKBps(tr_sessionGetRawSpeed_Bps(session, dir));
}

int tr_sessionCountTorrents(tr_session const* session)
{
    return tr_isSession(session) ? std::size(session->torrents) : 0;
}

std::vector<tr_torrent*> tr_sessionGetTorrents(tr_session* session)
{
    TR_ASSERT(tr_isSession(session));

    auto const& src = session->torrents;
    auto const n = std::size(src);
    auto torrents = std::vector<tr_torrent*>{ n };
    std::copy(std::begin(src), std::end(src), std::begin(torrents));
    return torrents;
}

static void closeBlocklists(tr_session*);

static void sessionCloseImplWaitForIdleUdp(evutil_socket_t fd, short what, void* vsession);

static void sessionCloseImplStart(tr_session* session)
{
    session->isClosing = true;

    free_incoming_peer_port(session);

    if (session->isLPDEnabled)
    {
        tr_lpdUninit(session);
    }

    tr_utpClose(session);
    tr_dhtUninit(session);

    event_free(session->saveTimer);
    session->saveTimer = nullptr;

    event_free(session->nowTimer);
    session->nowTimer = nullptr;

    tr_sharedClose(session);
    tr_rpcClose(&session->rpcServer);

    /* Close the torrents. Get the most active ones first so that
     * if we can't get them all closed in a reasonable amount of time,
     * at least we get the most important ones first. */
    auto torrents = tr_sessionGetTorrents(session);
    std::sort(
        std::begin(torrents),
        std::end(torrents),
        [](auto const* a, auto const* b)
        {
            auto const aCur = a->downloadedCur + a->uploadedCur;
            auto const bCur = b->downloadedCur + b->uploadedCur;
            return aCur > bCur; // larger xfers go first
        });

    for (auto* tor : torrents)
    {
        tr_torrentFree(tor);
    }

    torrents.clear();

    /* Close the announcer *after* closing the torrents
       so that all the &event=stopped messages will be
       queued to be sent by tr_announcerClose() */
    tr_announcerClose(session);

    /* and this goes *after* announcer close so that
       it won't be idle until the announce events are sent... */
    tr_webClose(session, TR_WEB_CLOSE_WHEN_IDLE);

    tr_cacheFree(session->cache);
    session->cache = nullptr;

    tr_verifyClose(session->verifier);
    session->verifier = nullptr;

    /* saveTimer is not used at this point, reusing for UDP shutdown wait */
    TR_ASSERT(session->saveTimer == nullptr);
    session->saveTimer = evtimer_new(session->event_base, sessionCloseImplWaitForIdleUdp, session);
    tr_timerAdd(session->saveTimer, 0, 0);
}

static void sessionCloseImplFinish(tr_session* session);

static void sessionCloseImplWaitForIdleUdp(evutil_socket_t fd, short what, void* vsession)
{
    TR_UNUSED(fd);
    TR_UNUSED(what);

    auto* session = static_cast<tr_session*>(vsession);

    TR_ASSERT(tr_isSession(session));

    /* gotta keep udp running long enough to send out all
       the &event=stopped UDP tracker messages */
    if (!tr_tracker_udp_is_idle(session))
    {
        tr_tracker_udp_upkeep(session);
        tr_timerAdd(session->saveTimer, 0, 100000);
        return;
    }

    sessionCloseImplFinish(session);
}

static void sessionCloseImplFinish(tr_session* session)
{
    event_free(session->saveTimer);
    session->saveTimer = nullptr;

    /* we had to wait until UDP trackers were closed before closing these: */
    evdns_base_free(session->evdns_base, 0);
    session->evdns_base = nullptr;
    tr_tracker_udp_close(session);
    tr_udpUninit(session);

    tr_statsClose(session);
    tr_peerMgrFree(session->peerMgr);

    closeBlocklists(session);

    tr_fdClose(session);

    session->isClosed = true;
}

static void sessionCloseImpl(void* vsession)
{
    auto* session = static_cast<tr_session*>(vsession);

    TR_ASSERT(tr_isSession(session));

    sessionCloseImplStart(session);
}

static bool deadlineReached(time_t const deadline)
{
    return time(nullptr) >= deadline;
}

#define SHUTDOWN_MAX_SECONDS 20

void tr_sessionClose(tr_session* session)
{
    TR_ASSERT(tr_isSession(session));

    time_t const deadline = time(nullptr) + SHUTDOWN_MAX_SECONDS;

    dbgmsg(
        "shutting down transmission session %p... now is %zu, deadline is %zu",
        (void*)session,
        (size_t)time(nullptr),
        (size_t)deadline);

    /* close the session */
    tr_runInEventThread(session, sessionCloseImpl, session);

    while (!session->isClosed && !deadlineReached(deadline))
    {
        dbgmsg("waiting for the libtransmission thread to finish");
        tr_wait_msec(100);
    }

    /* "shared" and "tracker" have live sockets,
     * so we need to keep the transmission thread alive
     * for a bit while they tell the router & tracker
     * that we're closing now */
    while ((session->shared != nullptr || session->web != nullptr || session->announcer != nullptr ||
            session->announcer_udp != nullptr) &&
           !deadlineReached(deadline))
    {
        dbgmsg(
            "waiting on port unmap (%p) or announcer (%p)... now %zu deadline %zu",
            (void*)session->shared,
            (void*)session->announcer,
            (size_t)time(nullptr),
            (size_t)deadline);
        tr_wait_msec(50);
    }

    tr_webClose(session, TR_WEB_CLOSE_NOW);

    /* close the libtransmission thread */
    tr_eventClose(session);

    while (session->events != nullptr)
    {
        static bool forced = false;
        dbgmsg("waiting for libtransmission thread to finish... now %zu deadline %zu", (size_t)time(nullptr), (size_t)deadline);
        tr_wait_msec(100);

        if (deadlineReached(deadline) && !forced)
        {
            dbgmsg("calling event_loopbreak()");
            forced = true;
            event_base_loopbreak(session->event_base);
        }

        if (deadlineReached(deadline + 3))
        {
            dbgmsg("deadline+3 reached... calling break...\n");
            break;
        }
    }

    /* free the session memory */
    tr_variantFree(&session->removedTorrents);
    tr_bandwidthDestruct(&session->bandwidth);
    tr_bitfieldDestruct(&session->turtle.minutes);
    tr_session_id_free(session->session_id);
    tr_lockFree(session->lock);

    if (session->metainfoLookup != nullptr)
    {
        tr_variantFree(session->metainfoLookup);
        tr_free(session->metainfoLookup);
    }

    tr_device_info_free(session->downloadDir);
    tr_free(session->torrentDoneScript);
    tr_free(session->configDir);
    tr_free(session->resumeDir);
    tr_free(session->torrentDir);
    tr_free(session->incompleteDir);
    tr_free(session->blocklist_url);
    tr_free(session->peer_congestion_algorithm);
    delete session;
}

struct sessionLoadTorrentsData
{
    tr_session* session;
    tr_ctor* ctor;
    int* setmeCount;
    tr_torrent** torrents;
    bool done;
};

static void sessionLoadTorrents(void* vdata)
{
    auto* data = static_cast<struct sessionLoadTorrentsData*>(vdata);
    TR_ASSERT(tr_isSession(data->session));

    tr_ctorSetSave(data->ctor, false); /* since we already have them */

    tr_sys_path_info info;
    char const* dirname = tr_getTorrentDir(data->session);
    tr_sys_dir_t odir = (tr_sys_path_get_info(dirname, 0, &info, nullptr) && info.type == TR_SYS_PATH_IS_DIRECTORY) ?
        tr_sys_dir_open(dirname, nullptr) :
        TR_BAD_SYS_DIR;

    auto torrents = std::list<tr_torrent*>{};
    if (odir != TR_BAD_SYS_DIR)
    {
        char const* name;

        while ((name = tr_sys_dir_read_name(odir, nullptr)) != nullptr)
        {
            if (tr_str_has_suffix(name, ".torrent"))
            {
                tr_torrent* tor;
                char* path = tr_buildPath(dirname, name, nullptr);
                tr_ctorSetMetainfoFromFile(data->ctor, path);

                if ((tor = tr_torrentNew(data->ctor, nullptr, nullptr)) != nullptr)
                {
                    torrents.push_back(tor);
                }

                tr_free(path);
            }
        }

        tr_sys_dir_close(odir, nullptr);
    }

    int const n = std::size(torrents);
    data->torrents = tr_new(tr_torrent*, n);
    std::copy(std::begin(torrents), std::end(torrents), data->torrents);

    if (n != 0)
    {
        tr_logAddInfo(_("Loaded %d torrents"), n);
    }

    if (data->setmeCount != nullptr)
    {
        *data->setmeCount = n;
    }

    data->done = true;
}

tr_torrent** tr_sessionLoadTorrents(tr_session* session, tr_ctor* ctor, int* setmeCount)
{
    struct sessionLoadTorrentsData data;

    data.session = session;
    data.ctor = ctor;
    data.setmeCount = setmeCount;
    data.torrents = nullptr;
    data.done = false;

    tr_runInEventThread(session, sessionLoadTorrents, &data);

    while (!data.done)
    {
        tr_wait_msec(100);
    }

    return data.torrents;
}

/***
****
***/

void tr_sessionSetPexEnabled(tr_session* session, bool enabled)
{
    TR_ASSERT(tr_isSession(session));

    session->isPexEnabled = enabled;
}

bool tr_sessionIsPexEnabled(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return session->isPexEnabled;
}

bool tr_sessionAllowsDHT(tr_session const* session)
{
    return tr_sessionIsDHTEnabled(session);
}

bool tr_sessionIsDHTEnabled(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return session->isDHTEnabled;
}

static void toggleDHTImpl(void* vsession)
{
    auto* session = static_cast<tr_session*>(vsession);

    TR_ASSERT(tr_isSession(session));

    tr_udpUninit(session);
    session->isDHTEnabled = !session->isDHTEnabled;
    tr_udpInit(session);
}

void tr_sessionSetDHTEnabled(tr_session* session, bool enabled)
{
    TR_ASSERT(tr_isSession(session));

    if (enabled != session->isDHTEnabled)
    {
        tr_runInEventThread(session, toggleDHTImpl, session);
    }
}

/***
****
***/

bool tr_sessionIsUTPEnabled(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

#ifdef WITH_UTP
    return session->isUTPEnabled;
#else
    return false;
#endif
}

static void toggle_utp(void* vsession)
{
    auto* session = static_cast<tr_session*>(vsession);

    TR_ASSERT(tr_isSession(session));

    session->isUTPEnabled = !session->isUTPEnabled;

    tr_udpSetSocketBuffers(session);

    /* But don't call tr_utpClose -- see reset_timer in tr-utp.c for an
       explanation. */
}

void tr_sessionSetUTPEnabled(tr_session* session, bool enabled)
{
    TR_ASSERT(tr_isSession(session));

    if (enabled != session->isUTPEnabled)
    {
        tr_runInEventThread(session, toggle_utp, session);
    }
}

/***
****
***/

static void toggleLPDImpl(void* vsession)
{
    auto* session = static_cast<tr_session*>(vsession);

    TR_ASSERT(tr_isSession(session));

    if (session->isLPDEnabled)
    {
        tr_lpdUninit(session);
    }

    session->isLPDEnabled = !session->isLPDEnabled;

    if (session->isLPDEnabled)
    {
        tr_lpdInit(session, &session->bind_ipv4->addr);
    }
}

void tr_sessionSetLPDEnabled(tr_session* session, bool enabled)
{
    TR_ASSERT(tr_isSession(session));

    if (enabled != session->isLPDEnabled)
    {
        tr_runInEventThread(session, toggleLPDImpl, session);
    }
}

bool tr_sessionIsLPDEnabled(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return session->isLPDEnabled;
}

bool tr_sessionAllowsLPD(tr_session const* session)
{
    return tr_sessionIsLPDEnabled(session);
}

/***
****
***/

void tr_sessionSetCacheLimit_MB(tr_session* session, int max_bytes)
{
    TR_ASSERT(tr_isSession(session));

    tr_cacheSetLimit(session->cache, toMemBytes(max_bytes));
}

int tr_sessionGetCacheLimit_MB(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return toMemMB(tr_cacheGetLimit(session->cache));
}

/***
****
***/

struct port_forwarding_data
{
    bool enabled;
    struct tr_shared* shared;
};

static void setPortForwardingEnabled(void* vdata)
{
    auto* data = static_cast<struct port_forwarding_data*>(vdata);
    tr_sharedTraversalEnable(data->shared, data->enabled);
    tr_free(data);
}

void tr_sessionSetPortForwardingEnabled(tr_session* session, bool enabled)
{
    struct port_forwarding_data* d;
    d = tr_new0(struct port_forwarding_data, 1);
    d->shared = session->shared;
    d->enabled = enabled;
    tr_runInEventThread(session, setPortForwardingEnabled, d);
}

bool tr_sessionIsPortForwardingEnabled(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return tr_sharedTraversalIsEnabled(session->shared);
}

/***
****
***/

static bool tr_stringEndsWith(char const* strval, char const* end)
{
    size_t const slen = strlen(strval);
    size_t const elen = strlen(end);

    return slen >= elen && memcmp(&strval[slen - elen], end, elen) == 0;
}

static void loadBlocklists(tr_session* session)
{
    tr_sys_dir_t odir;
    char* dirname;
    char const* name;
    auto loadme = std::unordered_set<std::string>{};
    bool const isEnabled = session->isBlocklistEnabled;

    /* walk the blocklist directory... */
    dirname = tr_buildPath(session->configDir, "blocklists", nullptr);
    odir = tr_sys_dir_open(dirname, nullptr);

    if (odir == TR_BAD_SYS_DIR)
    {
        tr_free(dirname);
        return;
    }

    while ((name = tr_sys_dir_read_name(odir, nullptr)) != nullptr)
    {
        char* path;
        char* load = nullptr;

        if (name[0] == '.') /* ignore dotfiles */
        {
            continue;
        }

        path = tr_buildPath(dirname, name, nullptr);

        if (tr_stringEndsWith(path, ".bin"))
        {
            load = tr_strdup(path);
        }
        else
        {
            char* binname;
            tr_sys_path_info path_info;
            tr_sys_path_info binname_info;

            binname = tr_strdup_printf("%s" TR_PATH_DELIMITER_STR "%s.bin", dirname, name);

            if (!tr_sys_path_get_info(binname, 0, &binname_info, nullptr)) /* create it */
            {
                tr_blocklistFile* b = tr_blocklistFileNew(binname, isEnabled);
                int const n = tr_blocklistFileSetContent(b, path);

                if (n > 0)
                {
                    load = tr_strdup(binname);
                }

                tr_blocklistFileFree(b);
            }
            else if (
                tr_sys_path_get_info(path, 0, &path_info, nullptr) &&
                path_info.last_modified_at >= binname_info.last_modified_at) /* update it */
            {
                char* old;
                tr_blocklistFile* b;

                old = tr_strdup_printf("%s.old", binname);
                tr_sys_path_remove(old, nullptr);
                tr_sys_path_rename(binname, old, nullptr);
                b = tr_blocklistFileNew(binname, isEnabled);

                if (tr_blocklistFileSetContent(b, path) > 0)
                {
                    tr_sys_path_remove(old, nullptr);
                }
                else
                {
                    tr_sys_path_remove(binname, nullptr);
                    tr_sys_path_rename(old, binname, nullptr);
                }

                tr_blocklistFileFree(b);
                tr_free(old);
            }

            tr_free(binname);
        }

        if (load != nullptr)
        {
            loadme.emplace(load);
            tr_free(load);
        }

        tr_free(path);
    }

    session->blocklists.clear();
    std::transform(
        std::begin(loadme),
        std::end(loadme),
        std::back_inserter(session->blocklists),
        [&isEnabled](auto const& path) { return tr_blocklistFileNew(path.c_str(), isEnabled); });

    /* cleanup */
    tr_sys_dir_close(odir, nullptr);
    tr_free(dirname);
}

static void closeBlocklists(tr_session* session)
{
    auto& src = session->blocklists;
    std::for_each(std::begin(src), std::end(src), [](auto* b) { tr_blocklistFileFree(b); });
    src.clear();
}

void tr_sessionReloadBlocklists(tr_session* session)
{
    closeBlocklists(session);
    loadBlocklists(session);

    tr_peerMgrOnBlocklistChanged(session->peerMgr);
}

int tr_blocklistGetRuleCount(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    auto const& src = session->blocklists;
    return std::accumulate(
        std::begin(src),
        std::end(src),
        0,
        [](int sum, auto const* cur) { return sum + tr_blocklistFileGetRuleCount(cur); });
}

bool tr_blocklistIsEnabled(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return session->isBlocklistEnabled;
}

void tr_blocklistSetEnabled(tr_session* session, bool enabled)
{
    TR_ASSERT(tr_isSession(session));

    session->isBlocklistEnabled = enabled;

    auto& src = session->blocklists;
    std::for_each(
        std::begin(src),
        std::end(src),
        [enabled](auto* blocklist) { tr_blocklistFileSetEnabled(blocklist, enabled); });
}

bool tr_blocklistExists(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return !std::empty(session->blocklists);
}

int tr_blocklistSetContent(tr_session* session, char const* contentFilename)
{
    tr_sessionLock(session);

    // find (or add) the default blocklist
    tr_blocklistFile* b = nullptr;
    auto& src = session->blocklists;
    char const* const name = DEFAULT_BLOCKLIST_FILENAME;
    auto const it = std::find_if(
        std::begin(src),
        std::end(src),
        [&name](auto const* blocklist) { return tr_stringEndsWith(tr_blocklistFileGetFilename(blocklist), name); });
    if (it == std::end(src))
    {
        char* path = tr_buildPath(session->configDir, "blocklists", name, nullptr);
        b = tr_blocklistFileNew(path, session->isBlocklistEnabled);
        src.push_back(b);
        tr_free(path);
    }
    else
    {
        b = *it;
    }

    // set the default blocklist's content
    int const ruleCount = tr_blocklistFileSetContent(b, contentFilename);
    tr_sessionUnlock(session);
    return ruleCount;
}

bool tr_sessionIsAddressBlocked(tr_session const* session, tr_address const* addr)
{
    auto& src = session->blocklists;
    return std::any_of(
        std::begin(src),
        std::end(src),
        [&addr](auto* blocklist) { return tr_blocklistFileHasAddress(blocklist, addr); });
}

void tr_blocklistSetURL(tr_session* session, char const* url)
{
    if (session->blocklist_url != url)
    {
        tr_free(session->blocklist_url);
        session->blocklist_url = tr_strdup(url);
    }
}

char const* tr_blocklistGetURL(tr_session const* session)
{
    return session->blocklist_url;
}

/***
****
***/

static void metainfoLookupInit(tr_session* session)
{
    TR_ASSERT(tr_isSession(session));

    tr_variant* lookup = tr_new0(tr_variant, 1);
    tr_variantInitDict(lookup, 0);

    int n = 0;

    tr_sys_path_info info;
    char const* dirname = tr_getTorrentDir(session);
    tr_sys_dir_t odir = (tr_sys_path_get_info(dirname, 0, &info, nullptr) && info.type == TR_SYS_PATH_IS_DIRECTORY) ?
        tr_sys_dir_open(dirname, nullptr) :
        TR_BAD_SYS_DIR;

    if (odir != TR_BAD_SYS_DIR)
    {
        tr_ctor* ctor = tr_ctorNew(session);
        tr_ctorSetSave(ctor, false); /* since we already have them */

        char const* name;

        /* walk through the directory and find the mappings */
        while ((name = tr_sys_dir_read_name(odir, nullptr)) != nullptr)
        {
            if (tr_str_has_suffix(name, ".torrent"))
            {
                tr_info inf;
                char* path = tr_buildPath(dirname, name, nullptr);
                tr_ctorSetMetainfoFromFile(ctor, path);

                if (tr_torrentParse(ctor, &inf) == TR_PARSE_OK)
                {
                    ++n;
                    tr_variantDictAddStr(lookup, tr_quark_new(inf.hashString, TR_BAD_SIZE), path);
                }

                tr_free(path);
            }
        }

        tr_sys_dir_close(odir, nullptr);
        tr_ctorFree(ctor);
    }

    session->metainfoLookup = lookup;
    tr_logAddDebug("Found %d torrents in \"%s\"", n, dirname);
}

char const* tr_sessionFindTorrentFile(tr_session const* session, char const* hashString)
{
    if (session->metainfoLookup == nullptr)
    {
        metainfoLookupInit((tr_session*)session);
    }

    char const* filename = nullptr;
    (void)tr_variantDictFindStr(session->metainfoLookup, tr_quark_new(hashString, TR_BAD_SIZE), &filename, nullptr);
    return filename;
}

void tr_sessionSetTorrentFile(tr_session* session, char const* hashString, char const* filename)
{
    /* since we walk session->configDir/torrents/ to build the lookup table,
     * and tr_sessionSetTorrentFile() is just to tell us there's a new file
     * in that same directory, we don't need to do anything here if the
     * lookup table hasn't been built yet */
    if (session->metainfoLookup != nullptr)
    {
        tr_variantDictAddStr(session->metainfoLookup, tr_quark_new(hashString, TR_BAD_SIZE), filename);
    }
}

/***
****
***/

void tr_sessionSetRPCEnabled(tr_session* session, bool isEnabled)
{
    TR_ASSERT(tr_isSession(session));

    tr_rpcSetEnabled(session->rpcServer, isEnabled);
}

bool tr_sessionIsRPCEnabled(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return tr_rpcIsEnabled(session->rpcServer);
}

void tr_sessionSetRPCPort(tr_session* session, tr_port port)
{
    TR_ASSERT(tr_isSession(session));

    tr_rpcSetPort(session->rpcServer, port);
}

tr_port tr_sessionGetRPCPort(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return tr_rpcGetPort(session->rpcServer);
}

void tr_sessionSetRPCUrl(tr_session* session, char const* url)
{
    TR_ASSERT(tr_isSession(session));

    tr_rpcSetUrl(session->rpcServer, url);
}

char const* tr_sessionGetRPCUrl(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return tr_rpcGetUrl(session->rpcServer);
}

void tr_sessionSetRPCCallback(tr_session* session, tr_rpc_func func, void* user_data)
{
    TR_ASSERT(tr_isSession(session));

    session->rpc_func = func;
    session->rpc_func_user_data = user_data;
}

void tr_sessionSetRPCWhitelist(tr_session* session, char const* whitelist)
{
    TR_ASSERT(tr_isSession(session));

    tr_rpcSetWhitelist(session->rpcServer, whitelist);
}

char const* tr_sessionGetRPCWhitelist(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return tr_rpcGetWhitelist(session->rpcServer);
}

void tr_sessionSetRPCWhitelistEnabled(tr_session* session, bool isEnabled)
{
    TR_ASSERT(tr_isSession(session));

    tr_rpcSetWhitelistEnabled(session->rpcServer, isEnabled);
}

bool tr_sessionGetRPCWhitelistEnabled(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return tr_rpcGetWhitelistEnabled(session->rpcServer);
}

void tr_sessionSetRPCPassword(tr_session* session, char const* password)
{
    TR_ASSERT(tr_isSession(session));

    tr_rpcSetPassword(session->rpcServer, password);
}

char const* tr_sessionGetRPCPassword(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return tr_rpcGetPassword(session->rpcServer);
}

void tr_sessionSetRPCUsername(tr_session* session, char const* username)
{
    TR_ASSERT(tr_isSession(session));

    tr_rpcSetUsername(session->rpcServer, username);
}

char const* tr_sessionGetRPCUsername(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return tr_rpcGetUsername(session->rpcServer);
}

void tr_sessionSetRPCPasswordEnabled(tr_session* session, bool isEnabled)
{
    TR_ASSERT(tr_isSession(session));

    tr_rpcSetPasswordEnabled(session->rpcServer, isEnabled);
}

bool tr_sessionIsRPCPasswordEnabled(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return tr_rpcIsPasswordEnabled(session->rpcServer);
}

char const* tr_sessionGetRPCBindAddress(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return tr_rpcGetBindAddress(session->rpcServer);
}

/****
*****
****/

bool tr_sessionIsTorrentDoneScriptEnabled(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return session->isTorrentDoneScriptEnabled;
}

void tr_sessionSetTorrentDoneScriptEnabled(tr_session* session, bool isEnabled)
{
    TR_ASSERT(tr_isSession(session));

    session->isTorrentDoneScriptEnabled = isEnabled;
}

char const* tr_sessionGetTorrentDoneScript(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return session->torrentDoneScript;
}

void tr_sessionSetTorrentDoneScript(tr_session* session, char const* scriptFilename)
{
    TR_ASSERT(tr_isSession(session));

    if (session->torrentDoneScript != scriptFilename)
    {
        tr_free(session->torrentDoneScript);
        session->torrentDoneScript = tr_strdup(scriptFilename);
    }
}

/***
****
***/

void tr_sessionSetQueueSize(tr_session* session, tr_direction dir, int n)
{
    TR_ASSERT(tr_isSession(session));
    TR_ASSERT(tr_isDirection(dir));

    session->queueSize[dir] = n;
}

int tr_sessionGetQueueSize(tr_session const* session, tr_direction dir)
{
    TR_ASSERT(tr_isSession(session));
    TR_ASSERT(tr_isDirection(dir));

    return session->queueSize[dir];
}

void tr_sessionSetQueueEnabled(tr_session* session, tr_direction dir, bool is_enabled)
{
    TR_ASSERT(tr_isSession(session));
    TR_ASSERT(tr_isDirection(dir));

    session->queueEnabled[dir] = is_enabled;
}

bool tr_sessionGetQueueEnabled(tr_session const* session, tr_direction dir)
{
    TR_ASSERT(tr_isSession(session));
    TR_ASSERT(tr_isDirection(dir));

    return session->queueEnabled[dir];
}

void tr_sessionSetQueueStalledMinutes(tr_session* session, int minutes)
{
    TR_ASSERT(tr_isSession(session));
    TR_ASSERT(minutes > 0);

    session->queueStalledMinutes = minutes;
}

void tr_sessionSetQueueStalledEnabled(tr_session* session, bool is_enabled)
{
    TR_ASSERT(tr_isSession(session));

    session->stalledEnabled = is_enabled;
}

bool tr_sessionGetQueueStalledEnabled(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return session->stalledEnabled;
}

int tr_sessionGetQueueStalledMinutes(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return session->queueStalledMinutes;
}

void tr_sessionSetAntiBruteForceThreshold(tr_session* session, int bad_requests)
{
    TR_ASSERT(tr_isSession(session));
    TR_ASSERT(bad_requests > 0);
    tr_rpcSetAntiBruteForceThreshold(session->rpcServer, bad_requests);
}

void tr_sessionSetAntiBruteForceEnabled(tr_session* session, bool is_enabled)
{
    TR_ASSERT(tr_isSession(session));

    tr_rpcSetAntiBruteForceEnabled(session->rpcServer, is_enabled);
}

bool tr_sessionGetAntiBruteForceEnabled(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return tr_rpcGetAntiBruteForceEnabled(session->rpcServer);
}

int tr_sessionGetAntiBruteForceThreshold(tr_session const* session)
{
    TR_ASSERT(tr_isSession(session));

    return tr_rpcGetAntiBruteForceThreshold(session->rpcServer);
}

std::vector<tr_torrent*> tr_sessionGetNextQueuedTorrents(tr_session* session, tr_direction direction, size_t num_wanted)
{
    TR_ASSERT(tr_isSession(session));
    TR_ASSERT(tr_isDirection(direction));

    // build an array of the candidates
    auto candidates = std::vector<tr_torrent*>{};
    candidates.reserve(tr_sessionCountTorrents(session));
    for (auto* tor : session->torrents)
    {
        if (tr_torrentIsQueued(tor) && (direction == tr_torrentGetQueueDirection(tor)))
        {
            candidates.push_back(tor);
        }
    }

    // find the best n candidates
    num_wanted = std::min(num_wanted, candidates.size());
    if (num_wanted < candidates.size())
    {
        std::partial_sort(
            std::begin(candidates),
            std::begin(candidates) + num_wanted,
            std::end(candidates),
            [](auto const* a, auto const* b) { return tr_torrentGetQueuePosition(a) < tr_torrentGetQueuePosition(b); });
        candidates.resize(num_wanted);
    }

    return candidates;
}

int tr_sessionCountQueueFreeSlots(tr_session* session, tr_direction dir)
{
    int const max = tr_sessionGetQueueSize(session, dir);
    tr_torrent_activity const activity = dir == TR_UP ? TR_STATUS_SEED : TR_STATUS_DOWNLOAD;

    if (!tr_sessionGetQueueEnabled(session, dir))
    {
        return INT_MAX;
    }

    /* count how many torrents are active */
    int active_count = 0;
    bool const stalled_enabled = tr_sessionGetQueueStalledEnabled(session);
    int const stalled_if_idle_for_n_seconds = tr_sessionGetQueueStalledMinutes(session) * 60;
    time_t const now = tr_time();
    for (auto const* tor : session->torrents)
    {
        /* is it the right activity? */
        if (activity != tr_torrentGetActivity(tor))
        {
            continue;
        }

        /* is it stalled? */
        if (stalled_enabled)
        {
            int const idle_secs = (int)difftime(now, std::max(tor->startDate, tor->activityDate));
            if (idle_secs >= stalled_if_idle_for_n_seconds)
                continue;
        }

        ++active_count;

        /* if we've reached the limit, no need to keep counting */
        if (active_count >= max)
        {
            return 0;
        }
    }

    return max - active_count;
}

void tr_sessionAddTorrent(tr_session* session, tr_torrent* tor)
{
    session->torrents.insert(tor);
    session->torrentsById.insert_or_assign(tor->uniqueId, tor);
    session->torrentsByHash.insert_or_assign(tor->info.hash, tor);
    session->torrentsByHashString.insert_or_assign(tor->info.hashString, tor);
}

void tr_sessionRemoveTorrent(tr_session* session, tr_torrent* tor)
{
    session->torrents.erase(tor);
    session->torrentsById.erase(tor->uniqueId);
    session->torrentsByHash.erase(tor->info.hash);
    session->torrentsByHashString.erase(tor->info.hashString);
}
