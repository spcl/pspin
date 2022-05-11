#ifndef __SLP_L1_H__
#define __SLP_L1_H__

#ifndef VECTOR_LEN
#define VECTOR_LEN 8
#endif

#ifndef DTYPE
#define DTYPE int32_t
#endif

#define TY_FIT_DATA 0
#define TY_PREDICT 1
typedef struct {
  // 0: fit data
  //    data: input vectors + correct predictions
  // 1: end of data (synchronization)
  //    data: final sequence number (not including current) for fit data
  // 2: predict
  //    data: input vectors
  uint8_t type;
  // number of data samples included
  // must be 0 for type == 1
  uint32_t count;
} slp_frame_hdr_t;

#endif // define __SLP_L1_H__
