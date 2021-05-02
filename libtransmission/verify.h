/*
 * This file Copyright (C) 2007-2014 Mnemosyne LLC
 *
 * It may be used under the GNU GPL versions 2 or 3
 * or any future license endorsed by Mnemosyne LLC.
 *
 */

#pragma once

#ifndef __TRANSMISSION__
#error only libtransmission should #include this header.
#endif

/**
 * @addtogroup file_io File IO
 * @{
 */

typedef struct tr_verifier tr_verifier;

tr_verifier* tr_verifyInit(void);

void tr_verifyAdd(tr_verifier* v, tr_torrent* tor, tr_verify_done_func callback_func, void* callback_user_data);

void tr_verifyRemove(tr_verifier* v, tr_torrent* tor);

void tr_verifyClose(tr_verifier* v);

/* @} */
