/* Darwin/Lean 4.33.1 diagnostic probe. Includes generated Lean C unchanged.
 * See docs/20261030-webdav-compact-base64.md for build and scope.
 */
#include <lean/lean.h>
#include <openssl/sha.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/resource.h>
#include "Snapshot.c"
extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);
extern lean_object *initialize_Init(uint8_t);
extern lean_object *lp_l4factoidal_L4Factoidal_LWS_Base64_encodeFast___boxed(lean_object *);
extern lean_object *lp_l4factoidal_L4Factoidal_LWS_Base64_decodeFast_x3f(lean_object *);
extern lean_object *lp_l4factoidal_L4Factoidal_LWS_Base64_encode(lean_object *);
extern lean_object *lp_l4factoidal_L4Factoidal_LWS_Base64_decode_x3f(lean_object *);
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+t.tv_nsec/1e9; }
static void sha(const unsigned char *p,size_t n,char out[65]) {
  unsigned char digest[SHA256_DIGEST_LENGTH];
  SHA256(p,n,digest);
  for(size_t i=0;i<32;i++)sprintf(out+2*i,"%02x",digest[i]);
  out[64]=0;
}
int main(int argc,char **argv) {
  if(argc!=3 || (strcmp(argv[1],"fast") && strcmp(argv[1],"reference"))) return 2;
  size_t size=strtoull(argv[2],NULL,10);
  if(size>60*1024*1024 || (!strcmp(argv[1],"reference") && size>1048576)) return 2;
  lean_initialize_runtime_module();
  lean_object *init=initialize_Init(1);
  if(lean_io_result_is_error(init)) return 3;
  lean_dec(init);
  /* Exactly the codec constant initialization in Snapshot initializer; no Store/Binding startup. */
  lp_l4factoidal_L4Factoidal_LWS_Base64_group2___closed__0___boxed__const__1 =
    _init_lp_l4factoidal_L4Factoidal_LWS_Base64_group2___closed__0___boxed__const__1();
  lean_mark_persistent(lp_l4factoidal_L4Factoidal_LWS_Base64_group2___closed__0___boxed__const__1);
  lean_io_mark_end_initialization();
  lean_object *input=lean_alloc_sarray(1,size,size);
  unsigned char *data=lean_sarray_cptr(input);
  for(size_t i=0;i<size;i++)data[i]=(unsigned char)(i*73+19);
  char inputHash[65],outputHash[65];sha(data,size,inputHash);
  double start=now();
  lean_inc_ref(input);
  lean_object *encoded = !strcmp(argv[1],"fast") ?
    lp_l4factoidal_L4Factoidal_LWS_Base64_encodeFast___boxed(input) :
    lp_l4factoidal_L4Factoidal_LWS_Base64_encode(input);
  double encodedAt=now();
  size_t encodedSize=lean_string_size(encoded)-1;
  lean_inc_ref(encoded);
  lean_object *result = !strcmp(argv[1],"fast") ?
    lp_l4factoidal_L4Factoidal_LWS_Base64_decodeFast_x3f(encoded) :
    lp_l4factoidal_L4Factoidal_LWS_Base64_decode_x3f(encoded);
  double decodedAt=now();
  if(lean_is_scalar(result)) return 4;
  lean_object *output=lean_ctor_get(result,0);
  if(lean_sarray_size(output)!=size || memcmp(data,lean_sarray_cptr(output),size)) return 5;
  sha(lean_sarray_cptr(output),size,outputHash);
  if(strcmp(inputHash,outputHash)) return 6;
  struct rusage usage; getrusage(RUSAGE_SELF,&usage);
  printf("{\"mode\":\"%s\",\"inputBytes\":%zu,\"encodedBytes\":%zu,\"encodeMs\":%.3f,\"decodeMs\":%.3f,\"peakRSSBytes\":%ld,\"equal\":true,\"inputSHA256\":\"%s\",\"outputSHA256\":\"%s\"}\n",
    argv[1],size,encodedSize,(encodedAt-start)*1000,(decodedAt-encodedAt)*1000,usage.ru_maxrss,inputHash,outputHash);
  lean_dec(result);lean_dec(encoded);lean_dec(input);
  return 0;
}
