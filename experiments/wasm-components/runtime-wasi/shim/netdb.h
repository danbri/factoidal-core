/* Shim (wasi-sdk build of the Lean runtime): declarations only, for uv.h.
   No name resolution exists under WASI Preview 1; nothing here is defined. */
#pragma once
#include <sys/socket.h>
struct addrinfo { int ai_flags, ai_family, ai_socktype, ai_protocol; socklen_t ai_addrlen;
  struct sockaddr *ai_addr; char *ai_canonname; struct addrinfo *ai_next; };
#define NI_MAXHOST 1025
#define NI_MAXSERV 32
