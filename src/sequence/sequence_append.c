#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../core/index.h"

#include "../error/error.h"

#include "sequence.h"

/******************************************************************************/
/** MEMORY (RE)ALLOCATION *****************************************************/
/******************************************************************************/

/*@
   requires \valid(required_capacity);
   requires \valid(io);
   requires
      \separated
      (
         (required_capacity+ (0 .. \block_length(required_capacity))),
         (io+ (0 .. \block_length(io)))
      );

   assigns \result;
   assigns (*required_capacity);

   ensures ((\result == 0) || (\result == -1));

   ensures \valid(required_capacity);
   ensures \valid(io);

   ensures
      \separated
      (
         (required_capacity+ (0 .. \block_length(required_capacity))),
         (io+ (0 .. \block_length(io)))
      );

   ensures
      (
         (\result == 0) <==>
               ((*required_capacity) == (\old(*required_capacity) + 1))
      );

   ensures
      (
         (\result == 0) ==>
            ((*required_capacity) * sizeof(JH_index)) <= SIZE_MAX
      );

   ensures
      (
         (\result == -1) <==>
            ((*required_capacity) == \old(*required_capacity))
      );

@*/
static int increment_required_capacity
(
   size_t required_capacity [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   if
   (
      (*required_capacity == SIZE_MAX)
      || ((SIZE_MAX / sizeof(JH_index)) <= (*required_capacity + 1))
   )
   {
      /*@ assert \valid(io); @*/

      #ifndef JH_RUNNING_FRAMA_C
      JH_S_ERROR
      (
         io,
         "Sequence capacity increment aborted, as the new size would not fit "
         "in a size_t variable."
      );
      #endif

      return -1;
   }

   /*@ assert ((*required_capacity) < SIZE_MAX); @*/
   /*@ assert \valid(required_capacity); @*/
   *required_capacity = (*required_capacity + 1);

   /* assert (((*required_capacity) * sizeof(JH_index)) <= SIZE_MAX); @*/

   return 0;
}

/******************************************************************************/
/** EXPORTED ******************************************************************/
/******************************************************************************/

int JH_sequence_ensure_capacity
(
   JH_index * sequence [const restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   const size_t sequence_required_capacity,
   FILE io [const restrict static 1]
)
{
   JH_index * new_sequence;

   /*@ assert \valid(sequence_capacity); @*/
   if (sequence_required_capacity <= *sequence_capacity)
   {
      return 0;
   }

   /*@
      assert
      (
         sequence_required_capacity
         <= (SIZE_MAX / sizeof(JH_index))
      );
   @*/
   /*@ assert \valid(sequence); @*/
   /*@ assert \valid(*sequence); @*/
   new_sequence =
      (JH_index *) realloc
      (
         (void *) *sequence,
         (sequence_required_capacity * sizeof(JH_index))
      );

   if (new_sequence == (JH_index *) NULL)
   {
      /*@ assert \valid(io); @*/

      #ifndef JH_RUNNING_FRAMA_C
      JH_S_ERROR
      (
         io,
         "Unable to reallocate memory to match sequence's required size."
      );
      #endif

      return -1;
   }

   *sequence_capacity = sequence_required_capacity;
   *sequence = new_sequence;

   return 1;
}

int JH_sequence_append_left
(
   const JH_index word_id,
   JH_index * sequence [const restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   if (increment_required_capacity(sequence_length, io) < 0)
   {
      return -1;
   }

   /*@ assert (((*sequence_length) * sizeof(JH_index)) <= SIZE_MAX); @*/
   if
   (
      JH_sequence_ensure_capacity
      (
         sequence,
         sequence_capacity,
         *sequence_length,
         io
      ) < 0
   )
   {
      *sequence_length -= 1;

      return -1;
   }

   /*@ assert (*sequence_length) >= 0; @*/

   if ((*sequence_length) > 1)
   {
      /*@ assert(((*sequence_length) * sizeof(JH_index)) <= SIZE_MAX); @*/

      #ifndef JH_RUNNING_FRAMA_C
      memmove
      (
         (void *) ((*sequence) + 1),
         (const void *) (*sequence),
         (((*sequence_length) - 1) * sizeof(JH_index))
      );
      #endif
   }

   (*sequence)[0] = word_id;

   return 0;
}

int JH_sequence_append_right
(
   JH_index * sequence [const restrict static 1],
   const JH_index word_id,
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   if (increment_required_capacity(sequence_length, io) < 0)
   {
      return -1;
   }

   /*@ assert (((*sequence_length) * sizeof(JH_index)) <= SIZE_MAX); @*/

   if
   (
      JH_sequence_ensure_capacity
      (
         sequence,
         sequence_capacity,
         *sequence_length,
         io
      ) < 0
   )
   {
      *sequence_length -= 1;

      return -1;
   }

   /*@ assert ((*sequence_length) >= 1); @*/
   (*sequence)[(*sequence_length) - 1] = word_id;
   /*@ assert ((*sequence_length) >= 1); @*/

   return 0;
}
