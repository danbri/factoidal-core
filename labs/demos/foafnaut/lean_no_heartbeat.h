/* The native engine's compiled Lean code counts no heartbeats.
 *
 * lean.h's lean_alloc_small_object calls lean_inc_heartbeat() before every small allocation.
 * The count is a thread-local variable of Lean's runtime, read only by Lean's elaborator
 * (maxHeartbeats); nothing in the engine reads it. On macOS a thread-local variable of a
 * dynamic library is reached through a call (_tlv_get_addr), so each allocation paid a call
 * into the runtime and that call: about 14% of an allocation and its free.
 *
 * build-web-render.sh compiles the engine's C with
 *   -include lean_no_heartbeat.h -Dlean_inc_heartbeat=foafnaut_no_heartbeat
 * so lean.h's declaration and its one call name this empty function. Lean's runtime library
 * is not compiled this way and keeps its own counter. */
#ifndef FOAFNAUT_LEAN_NO_HEARTBEAT_H
#define FOAFNAUT_LEAN_NO_HEARTBEAT_H
static inline void foafnaut_no_heartbeat(void) {}
#endif
