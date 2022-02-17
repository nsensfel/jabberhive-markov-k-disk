#ifndef _JH_CORE_INDEX_H_
#define _JH_CORE_INDEX_H_

#include "index_types.h"

#if JH_INDEX_MAX >= SIZE_MAX
#define JH_index_cannot_allocate_more(type_size, counter) \
      (\
         (((size_t) (counter)) == SIZE_MAX) \
         || ((counter) == JH_INDEX_MAX) \
         || ((((size_t) (counter)) + 1) > (SIZE_MAX / (type_size))) \
      )
#else
#define JH_index_cannot_allocate_more(type_size, counter) \
      (\
         ((counter) == JH_INDEX_MAX) \
         || ((((size_t) (counter)) + 1) > (SIZE_MAX / (type_size))) \
      )
#endif

/*
 * Returns a random JH_index.
 */
/*@
   ensures (\result <= JH_INDEX_MAX);
   assigns \result;
@*/
JH_index JH_index_random (void);

/*
 * Returns a random JH_index, included in [0, limit]
 */
/*@
   ensures (\result <= limit);
   assigns \result;
@*/
JH_index JH_index_random_up_to (const JH_index limit);

int JH_index_cmp (const JH_index a, const JH_index b);

#endif
