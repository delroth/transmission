/*
 * This file Copyright (C) 2012-2014 Mnemosyne LLC
 *
 * It may be used under the GNU GPL versions 2 or 3
 * or any future license endorsed by Mnemosyne LLC.
 *
 */

#include <stdio.h> /* fprintf() */
#include <string.h> /* strcmp(), strchr(), memcmp() */
#include <stdlib.h> /* qsort() */
#include <time.h>

#include <curl/curl.h>

#include <event2/buffer.h>

#include <libtransmission/transmission.h>
#include <libtransmission/tr-getopt.h>
#include <libtransmission/utils.h>
#include <libtransmission/web.h> /* tr_webGetResponseStr() */
#include <libtransmission/variant.h>
#include <libtransmission/version.h>

#include "units.h"

#define MY_NAME "transmission-show"
#define TIMEOUT_SECS 30

static tr_option options[] = {
    { 'm', "magnet", "Give a magnet link for the specified torrent", "m", false, nullptr },
    { 's', "scrape", "Ask the torrent's trackers how many peers are in the torrent's swarm", "s", false, nullptr },
    { 'u', "unsorted", "Do not sort files by name", "u", false, nullptr },
    { 'V', "version", "Show version number and exit", "V", false, nullptr },
    { 0, nullptr, nullptr, nullptr, false, nullptr }
};

static char const* getUsage(void)
{
    return "Usage: " MY_NAME " [options] <.torrent file>";
}

static bool magnetFlag = false;
static bool scrapeFlag = false;
static bool unsorted = false;
static bool showVersion = false;
char const* filename = nullptr;

static int parseCommandLine(int argc, char const* const* argv)
{
    int c;
    char const* optarg;

    while ((c = tr_getopt(getUsage(), argc, argv, options, &optarg)) != TR_OPT_DONE)
    {
        switch (c)
        {
        case 'm':
            magnetFlag = true;
            break;

        case 's':
            scrapeFlag = true;
            break;

        case 'u':
            unsorted = true;
            break;

        case 'V':
            showVersion = true;
            break;

        case TR_OPT_UNK:
            filename = optarg;
            break;

        default:
            return 1;
        }
    }

    return 0;
}

static void doShowMagnet(tr_info const* inf)
{
    char* str = tr_torrentInfoGetMagnetLink(inf);
    printf("%s", str);
    tr_free(str);
}

static int compare_files_by_name(void const* va, void const* vb)
{
    tr_file const* a = *(tr_file const* const*)va;
    tr_file const* b = *(tr_file const* const*)vb;
    return strcmp(a->name, b->name);
}

static char const* time_t_to_str(time_t timestamp)
{
    if (timestamp == 0)
    {
        return "Unknown";
    }

    struct tm tm;
    tr_localtime_r(&timestamp, &tm);
    static char buf[32];
    strftime(buf, sizeof(buf), "%a %b %2e %T %Y%n", &tm); /* ctime equiv */
    return buf;
}

static void showInfo(tr_info const* inf)
{
    char buf[128];
    tr_file** files;
    int prevTier = -1;

    /**
    ***  General Info
    **/

    printf("GENERAL\n\n");
    printf("  Name: %s\n", inf->name);
    printf("  Hash: %s\n", inf->hashString);
    printf("  Created by: %s\n", inf->creator ? inf->creator : "Unknown");
    printf("  Created on: %s\n", time_t_to_str(inf->dateCreated));

    if (!tr_str_is_empty(inf->comment))
    {
        printf("  Comment: %s\n", inf->comment);
    }

    printf("  Piece Count: %d\n", inf->pieceCount);
    printf("  Piece Size: %s\n", tr_formatter_mem_B(buf, inf->pieceSize, sizeof(buf)));
    printf("  Total Size: %s\n", tr_formatter_size_B(buf, inf->totalSize, sizeof(buf)));
    printf("  Privacy: %s\n", inf->isPrivate ? "Private torrent" : "Public torrent");

    /**
    ***  Trackers
    **/

    printf("\nTRACKERS\n");

    for (unsigned int i = 0; i < inf->trackerCount; ++i)
    {
        if (prevTier != inf->trackers[i].tier)
        {
            prevTier = inf->trackers[i].tier;
            printf("\n  Tier #%d\n", prevTier + 1);
        }

        printf("  %s\n", inf->trackers[i].announce);
    }

    /**
    ***
    **/

    if (inf->webseedCount > 0)
    {
        printf("\nWEBSEEDS\n\n");

        for (unsigned int i = 0; i < inf->webseedCount; ++i)
        {
            printf("  %s\n", inf->webseeds[i]);
        }
    }

    /**
    ***  Files
    **/

    printf("\nFILES\n\n");
    files = tr_new(tr_file*, inf->fileCount);

    for (unsigned int i = 0; i < inf->fileCount; ++i)
    {
        files[i] = &inf->files[i];
    }

    if (!unsorted)
    {
        qsort(files, inf->fileCount, sizeof(tr_file*), compare_files_by_name);
    }

    for (unsigned int i = 0; i < inf->fileCount; ++i)
    {
        printf("  %s (%s)\n", files[i]->name, tr_formatter_size_B(buf, files[i]->length, sizeof(buf)));
    }

    tr_free(files);
}

static size_t writeFunc(void* ptr, size_t size, size_t nmemb, void* vbuf)
{
    auto* buf = static_cast<evbuffer*>(vbuf);
    size_t const byteCount = size * nmemb;
    evbuffer_add(buf, ptr, byteCount);
    return byteCount;
}

static CURL* tr_curl_easy_init(struct evbuffer* writebuf)
{
    CURL* curl = curl_easy_init();
    curl_easy_setopt(curl, CURLOPT_USERAGENT, MY_NAME "/" LONG_VERSION_STRING);
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, writeFunc);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, writebuf);
    curl_easy_setopt(curl, CURLOPT_HTTPAUTH, CURLAUTH_ANY);
    curl_easy_setopt(curl, CURLOPT_VERBOSE, tr_env_key_exists("TR_CURL_VERBOSE"));
    curl_easy_setopt(curl, CURLOPT_ENCODING, "");
    return curl;
}

static void doScrape(tr_info const* inf)
{
    for (unsigned int i = 0; i < inf->trackerCount; ++i)
    {
        CURL* curl;
        CURLcode res;
        struct evbuffer* buf;
        char const* scrape = inf->trackers[i].scrape;
        char* url;
        char escaped[SHA_DIGEST_LENGTH * 3 + 1];

        if (scrape == nullptr)
        {
            continue;
        }

        tr_http_escape_sha1(escaped, inf->hash);

        url = tr_strdup_printf("%s%cinfo_hash=%s", scrape, strchr(scrape, '?') != nullptr ? '&' : '?', escaped);

        printf("%s ... ", url);
        fflush(stdout);

        buf = evbuffer_new();
        curl = tr_curl_easy_init(buf);
        curl_easy_setopt(curl, CURLOPT_URL, url);
        curl_easy_setopt(curl, CURLOPT_TIMEOUT, TIMEOUT_SECS);

        if ((res = curl_easy_perform(curl)) != CURLE_OK)
        {
            printf("error: %s\n", curl_easy_strerror(res));
        }
        else
        {
            long response;
            curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, &response);

            if (response != 200)
            {
                printf("error: unexpected response %ld \"%s\"\n", response, tr_webGetResponseStr(response));
            }
            else /* HTTP OK */
            {
                tr_variant top;
                tr_variant* files;
                bool matched = false;
                char const* begin = (char const*)evbuffer_pullup(buf, -1);

                if (tr_variantFromBenc(&top, begin, evbuffer_get_length(buf)) == 0)
                {
                    if (tr_variantDictFindDict(&top, TR_KEY_files, &files))
                    {
                        size_t child_pos = 0;
                        tr_quark key;
                        tr_variant* val;

                        while (tr_variantDictChild(files, child_pos, &key, &val))
                        {
                            if (memcmp(inf->hash, tr_quark_get_string(key, nullptr), SHA_DIGEST_LENGTH) == 0)
                            {
                                int64_t seeders;
                                if (!tr_variantDictFindInt(val, TR_KEY_complete, &seeders))
                                {
                                    seeders = -1;
                                }

                                int64_t leechers;
                                if (!tr_variantDictFindInt(val, TR_KEY_incomplete, &leechers))
                                {
                                    leechers = -1;
                                }

                                printf("%d seeders, %d leechers\n", (int)seeders, (int)leechers);
                                matched = true;
                            }

                            ++child_pos;
                        }
                    }

                    tr_variantFree(&top);
                }

                if (!matched)
                {
                    printf("no match\n");
                }
            }
        }

        curl_easy_cleanup(curl);
        evbuffer_free(buf);
        tr_free(url);
    }
}

int tr_main(int argc, char* argv[])
{
    int err;
    tr_info inf;
    tr_ctor* ctor;

    tr_logSetLevel(TR_LOG_ERROR);
    tr_formatter_mem_init(MEM_K, MEM_K_STR, MEM_M_STR, MEM_G_STR, MEM_T_STR);
    tr_formatter_size_init(DISK_K, DISK_K_STR, DISK_M_STR, DISK_G_STR, DISK_T_STR);
    tr_formatter_speed_init(SPEED_K, SPEED_K_STR, SPEED_M_STR, SPEED_G_STR, SPEED_T_STR);

    if (parseCommandLine(argc, (char const* const*)argv) != 0)
    {
        return EXIT_FAILURE;
    }

    if (showVersion)
    {
        fprintf(stderr, MY_NAME " " LONG_VERSION_STRING "\n");
        return EXIT_SUCCESS;
    }

    /* make sure the user specified a filename */
    if (filename == nullptr)
    {
        fprintf(stderr, "ERROR: No .torrent file specified.\n");
        tr_getopt_usage(MY_NAME, getUsage(), options);
        fprintf(stderr, "\n");
        return EXIT_FAILURE;
    }

    /* try to parse the .torrent file */
    ctor = tr_ctorNew(nullptr);
    tr_ctorSetMetainfoFromFile(ctor, filename);
    err = tr_torrentParse(ctor, &inf);
    tr_ctorFree(ctor);

    if (err != TR_PARSE_OK)
    {
        fprintf(stderr, "Error parsing .torrent file \"%s\"\n", filename);
        return EXIT_FAILURE;
    }

    if (magnetFlag)
    {
        doShowMagnet(&inf);
    }
    else
    {
        printf("Name: %s\n", inf.name);
        printf("File: %s\n", filename);
        printf("\n");
        fflush(stdout);

        if (scrapeFlag)
        {
            doScrape(&inf);
        }
        else
        {
            showInfo(&inf);
        }
    }

    /* cleanup */
    putc('\n', stdout);
    tr_metainfoFree(&inf);
    return EXIT_SUCCESS;
}
