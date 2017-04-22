#include <limits.h>
#include <stdlib.h>

#include "index.h"

#if (RAND_MAX < UCHAR_MAX)
   #error "RAND_MAX < UCHAR_MAX, unable to generate random numbers."
#endif

#if (RAND_MAX == 0)
   #error "RAND_MAX is included in [0, 0]. What are you even doing?"
#endif

/*
 * Returns a random unsigned char.
 */
static unsigned char random_uchar (void)
{
   return
   (unsigned char)
   (
      /* FIXME: Do floats allow enough precision for this? */
      (
         ((float) rand())
         / ((float) RAND_MAX)
      )
      * ((float) UCHAR_MAX)
   );
}

/* See: "index.h" */
JH_index JH_index_random (void)
{
   JH_index i;
   JH_index result;
   unsigned char * result_bytes;

   /*@ ghost return 4; @*/ /* Chosen by fair dice roll. */
                           /* Guaranteed to be random. */
   /* More seriously, I am not explaining the hack below to Frama-C */

   result_bytes = (unsigned char *) &result;


   for (i = 0; i < sizeof(JH_index); ++i)
   {
      result_bytes[i] = random_uchar();
   }

   return result;
}

/* See: "index.h" */
JH_index JH_index_random_up_to (const JH_index max)
{
   return
   (JH_index)
   (
      /* FIXME: Do floats allow enough precision for this? */
      (
         ((float) JH_index_random())
         / ((float) JH_INDEX_MAX)
      )
      * ((float) max)
   );
}

int JH_index_cmp (const JH_index a, const JH_index b)
{
   if (a < b)
   {
      return -1;
   }
   else if (a > b)
   {
      return 1;
   }
   else
   {
      return 0;
   }
}
