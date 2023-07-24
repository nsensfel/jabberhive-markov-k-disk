#include <stdlib.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../core/index.h"

#include "../sequence/sequence.h"

#include "../error/error.h"

#include "../io/io.h"

#include "../parameters/parameters.h"

#include "knowledge.h"

/******************************************************************************/
/** INITIALIZE ****************************************************************/
/******************************************************************************/
/**
 * Updates the sorted sequence list, both in RAM and on disk, to insert the
 * new element.
 **/
static void set_nth_sequence
(
   const struct JH_knowledge k [const restrict static 1],
   const JH_index sorted_sequence_ix,
   const JH_index sequence_id,
   FILE io [const restrict static 1]
)
{
   // WARNING: sequences_length has already been increased.
   const JH_index previous_sequence_length = (k->sequences_length - 1);

   if (sorted_sequence_ix < previous_sequence_length)
   {
      memmove
      (
         (void *) (k->sequences_sorted + (sorted_sequence_ix + 1)),
         (const void *) (k->sequences_sorted + sorted_sequence_ix),
         (
            ((size_t) (previous_sequence_length - sorted_sequence_ix))
            * sizeof(JH_index)
         )
      );
   }

   k->sequences_sorted[sorted_sequence_ix] = sequence_id;

   JH_io_write_sorted_sequences
   (
      k->sequences_sorted_filename,
      k->sequences_length,
      k->sequences_sorted,
      io
   );
}

/******************************************************************************/
/** ALLOCATING MEMORY *********************************************************/
/******************************************************************************/
static int reallocate_sequences_sorted_list
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_index * new_sequences_sorted;

   if
   (
      JH_index_cannot_allocate_more
      (
         sizeof(JH_index),
         k->sequences_length
      )
   )
   {
      JH_S_ERROR
      (
         io,
         "Unable to store the size of the sorted sequences list, as it would "
         "overflow size_t variables."
      );

      return -1;
   }

   new_sequences_sorted =
      (JH_index *) realloc
      (
         (void *) k->sequences_sorted,
         (((size_t) k->sequences_length) * sizeof(JH_index))
      );

   if (new_sequences_sorted == (JH_index *) NULL)
   {
      JH_S_ERROR
      (
         io,
         "Unable to allocate the memory required for the new sorted sequences "
         "list."
      );

      return -1;
   }

   k->sequences_sorted = new_sequences_sorted;

   return 0;
}

/******************************************************************************/
/** ADD A NEW SEQUENCE ********************************************************/
/******************************************************************************/
static int add_sequence
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const JH_index sequence [const restrict static 1],
   const JH_index sequence_id,
   const JH_index sorted_sequence_ix,
   FILE io [const restrict static 1]
)
{
   if (k->sequences_length == JH_INDEX_MAX)
   {
      JH_S_ERROR
      (
         io,
         "Unable to add sequence: the variable that stores the number of known "
         "sequences would overflow."
      );

      return -1;
   }

   if
   (
      JH_io_write_sequence_from_id
      (
         params,
         k->sequences_length,
         sequence,
         io
      )
      < 0
   )
   {
      return -1;
   }

   if (JH_DEBUG_KNOWLEDGE_LEARN_SEQUENCE)
   {
      JH_index i;

      JH_S_DEBUG
      (
         io,
         JH_DEBUG_KNOWLEDGE_LEARN_SEQUENCE,
         "Learning new sequence."
      );

      for (i = 0; i < (JH_parameters_get_markov_order(params) - 1); ++i)
      {
         JH_DEBUG
         (
            io,
            JH_DEBUG_KNOWLEDGE_LEARN_SEQUENCE,
            "markov_sequence[%u]: %u",
            i,
            sequence[i]
         );
      }
   }

   k->sequences_length += 1;

   if (reallocate_sequences_sorted_list(k, io) < 0)
   {
      k->sequences_length -= 1;

      return -1;
   }

   set_nth_sequence(k, sorted_sequence_ix, sequence_id, io);

   return 0;
}

/******************************************************************************/
/** EXPORTED ******************************************************************/
/******************************************************************************/
int JH_knowledge_learn_markov_sequence
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const JH_index sequence [const restrict static 1],
   JH_index sequence_id [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   int i;
   JH_index sorted_ix;

   if (JH_DEBUG_KNOWLEDGE_LEARN_SEQUENCE)
   {
      JH_index j;

      JH_S_DEBUG
      (
         io,
         JH_DEBUG_KNOWLEDGE_LEARN_SEQUENCE,
         "Studying markov sequence..."
      );

      for (j = 0; j < (JH_parameters_get_markov_order(params) - 1); ++j)
      {
         JH_DEBUG
         (
            io,
            JH_DEBUG_KNOWLEDGE_LEARN_SEQUENCE,
            "markov_sequence[%u]: %u",
            j,
            sequence[j]
         );
      }
   }

   JH_knowledge_readlock_sequences(k, io);

   i =
      JH_knowledge_find_sequence
      (
         params,
         k,
         sequence,
         sequence_id,
         &sorted_ix,
         io
      );

   /*
    * We might need to write, but we have reading access.
    * We can't get the writing access while someone (even us) has the reading
    * access, so we release the reading access in any case.
    */
   JH_knowledge_readunlock_sequences(k, io);

   if (i < 0)
   {
      return -1;
   }

   if (i == 1)
   {
      JH_DEBUG
      (
         io,
         JH_DEBUG_KNOWLEDGE_LEARN_SEQUENCE,
         "Markov sequence is known. ID: %u",
         *sequence_id
      );

      return 0;
   }


   JH_knowledge_writelock_sequences(k, io);
   /*
    * Now we have writer access, but someone else might have modified 'k' before
    * we did, so we need to find the sequence's location again.
    */
   i =
      JH_knowledge_lazy_find_sequence
      (
         params,
         k,
         sequence,
         sequence_id,
         &sorted_ix,
         io
      );

   if (i < 0)
   {
      JH_knowledge_writeunlock_sequences(k, io);

      return -1;
   }

   if (i == 1)
   {
      JH_knowledge_writeunlock_sequences(k, io);

      JH_DEBUG
      (
         io,
         JH_DEBUG_KNOWLEDGE_LEARN_SEQUENCE,
         "Markov sequence is known. ID: %u",
         *sequence_id
      );

      return 0;
   }

   if
   (
      add_sequence
      (
         params,
         k,
         sequence,
         *sequence_id,
         sorted_ix,
         io
      )
      < 0
   )
   {
      JH_knowledge_writeunlock_sequences(k, io);

      return -1;
   }
   else
   {
      JH_knowledge_writeunlock_sequences(k, io);

      return 0;
   }
}
