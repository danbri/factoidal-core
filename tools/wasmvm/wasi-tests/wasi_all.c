/* wasi_all.c: calls each wasi_snapshot_preview1 function that wasi/api.h of
 * Emscripten 6.0.8 declares (45 of the 46 in the witx; sock_accept is missing there),
 * with zero arguments. Built by tools/wasmvm/wasi-tests/build.sh; the imports the
 * compiler emits give an outside check of WasmVM/Wasi.lean Fn.type. */
#include <wasi/api.h>
#include <stdint.h>
__attribute__((export_name("call"))) int32_t call(int32_t k) {
  switch (k) {
  case 0: return __wasi_args_get(0, 0);
  case 1: return __wasi_args_sizes_get(0, 0);
  case 2: return __wasi_environ_get(0, 0);
  case 3: return __wasi_environ_sizes_get(0, 0);
  case 4: return __wasi_clock_res_get(0, 0);
  case 5: return __wasi_clock_time_get(0, 0, 0);
  case 6: return __wasi_fd_advise(0, 0, 0, 0);
  case 7: return __wasi_fd_allocate(0, 0, 0);
  case 8: return __wasi_fd_close(0);
  case 9: return __wasi_fd_datasync(0);
  case 10: return __wasi_fd_fdstat_get(0, 0);
  case 11: return __wasi_fd_fdstat_set_flags(0, 0);
  case 12: return __wasi_fd_fdstat_set_rights(0, 0, 0);
  case 13: return __wasi_fd_filestat_get(0, 0);
  case 14: return __wasi_fd_filestat_set_size(0, 0);
  case 15: return __wasi_fd_filestat_set_times(0, 0, 0, 0);
  case 16: return __wasi_fd_pread(0, 0, 0, 0, 0);
  case 17: return __wasi_fd_prestat_get(0, 0);
  case 18: return __wasi_fd_prestat_dir_name(0, 0, 0);
  case 19: return __wasi_fd_pwrite(0, 0, 0, 0, 0);
  case 20: return __wasi_fd_read(0, 0, 0, 0);
  case 21: return __wasi_fd_readdir(0, 0, 0, 0, 0);
  case 22: return __wasi_fd_renumber(0, 0);
  case 23: return __wasi_fd_seek(0, 0, 0, 0);
  case 24: return __wasi_fd_sync(0);
  case 25: return __wasi_fd_tell(0, 0);
  case 26: return __wasi_fd_write(0, 0, 0, 0);
  case 27: return __wasi_path_create_directory(0, 0, 0);
  case 28: return __wasi_path_filestat_get(0, 0, 0, 0, 0);
  case 29: return __wasi_path_filestat_set_times(0, 0, 0, 0, 0, 0, 0);
  case 30: return __wasi_path_link(0, 0, 0, 0, 0, 0, 0);
  case 31: return __wasi_path_open(0, 0, 0, 0, 0, 0, 0, 0, 0);
  case 32: return __wasi_path_readlink(0, 0, 0, 0, 0, 0);
  case 33: return __wasi_path_remove_directory(0, 0, 0);
  case 34: return __wasi_path_rename(0, 0, 0, 0, 0, 0);
  case 35: return __wasi_path_symlink(0, 0, 0, 0, 0);
  case 36: return __wasi_path_unlink_file(0, 0, 0);
  case 37: return __wasi_poll_oneoff(0, 0, 0, 0);
  case 38: __wasi_proc_exit(0); return -1;
  case 39: return __wasi_proc_raise(0);
  case 40: return __wasi_sched_yield();
  case 41: return __wasi_random_get(0, 0);
  case 42: return __wasi_sock_recv(0, 0, 0, 0, 0, 0);
  case 43: return __wasi_sock_send(0, 0, 0, 0, 0);
  case 44: return __wasi_sock_shutdown(0, 0);
  }
  return -2;
}
