/* Shim (wasi-sdk build of the Lean runtime): declarations only, for uv.h. */
#pragma once
typedef unsigned int tcflag_t; typedef unsigned char cc_t; typedef unsigned int speed_t;
struct termios { tcflag_t c_iflag, c_oflag, c_cflag, c_lflag; cc_t c_cc[32]; };
