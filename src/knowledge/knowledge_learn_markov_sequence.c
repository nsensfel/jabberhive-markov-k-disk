#include <stdlib.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../sequence/sequence.h"

#include "../error/error.h"

#include "knowledge.h"

/******************************************************************************/
/** INITIALIZE ****************************************************************/
/******************************************************************************/
static void set_nth_sequence
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index sorted_sequence_id,
   const JH_index sequence_id
)
{
   if (sorted_sequence_id < (k->sequences_length - 1))
   {
      memmove
      (
         (void *) (k->sequences_sorted + (sorted_sequence_id + 1)),
         (const void *) (k->sequences_sorted + sorted_sequence_id),
         (
            ((size_t) ((k->sequences_length - 1) - sorted_sequence_id))
            * sizeof(JH_index)
         )
      );
   }

   k->sequences_sorted[sorted_sequence_id] = sequence_id;
}

/******************************************************************************/
/** ALLOCATING MEMORY *********************************************************/
/******************************************************************************/
static int reallocate_sequences_list
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_index ** new_sequences;

   if ((SIZE_MAX / sizeof(JH_index *)) < (size_t) k->sequences_length)
   {
      JH_S_ERROR
      (
         io,
         "Unable to store the size of the sequences list, as it would overflow "
         "size_t variables."
      );

      return -1;
   }

   new_sequences =
      (JH_index **) realloc
      (
         (void *) k->sequences,
         (((size_t) k->sequences_length) * sizeof(JH_index *))
      );

   if (new_sequences == (JH_index **) NULL)
   {
      JH_S_ERROR
      (
         io,
         "Unable to allocate the memory required for the new sequence list."
      );

      return -1;
   }

   k->sequences = new_sequences;

   return 0;
}

static int reallocate_sequences_sorted_list
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_index * new_sequences_sorted;

   if ((SIZE_MAX / sizeof(JH_index)) < (size_t) k->sequences_length)
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

/* Pre: (=< JH_INDEX_MAX SIZE_MAX) */
/*@
   requires
   (
      (base_length == destination_length)
      ||
      (
         (base_length < destination_length)
         &&
         (
           (base[0] == JH_START_OF_SEQUENCE)
           (base[base_length - 1] == JH_END_OF_SEQUENCE)
         )
      )
   );
@*/
static JH_index * copy_sequence
(
   const JH_index base [const restrict static 1],
   const JH_index destination_length,
   FILE io [const restrict static 1]
)
{
   JH_index * result;

   result =
      (JH_index *) calloc
      (
         (size_t) (destination_length),
         sizeof(JH_index)
      );

   if (result == (JH_index *) NULL)
   {
      JH_S_ERROR
      (
         io,
         "Unable to allocate the memory required to store a new sequence."
      );

      return (JH_index *) NULL;
   }

   memcpy
   (
      (void *) result,
      (const void *) base,
      (((size_t) destination_length) * sizeof(JH_index))
   );

   return result;
}

/******************************************************************************/
/** ADD A NEW SEQUENCE ********************************************************/
/******************************************************************************/

static int add_sequence
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index sequence [const restrict static 1],
   const JH_index markov_order, /* Pre (> markov_order 1) */
   const JH_index sequence_id,
   const JH_index sorted_sequence_id,
   FILE io [const restrict static 1]
)
{
   JH_index * stored_sequence;

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

   stored_sequence = copy_sequence(sequence, (markov_order - 1), io);

   if (stored_sequence == (JH_index *) NULL)
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

      for (i = 0; i < (markov_order - 1); ++i)
      {
         JH_DEBUG
         (
            io,
            JH_DEBUG_KNOWLEDGE_LEARN_SEQUENCE,
            "markov_sequence[%u]: %u",
            i,
            stored_sequence[i]
         );
      }
   }

   k->sequences_length += 1;

   if (reallocate_sequences_list(k, io) < 0)
   {
      k->sequences_length -= 1;

      free((void *) stored_sequence);

      return -1;
   }

   k->sequences[sequence_id] = stored_sequence;

   if (reallocate_sequences_sorted_list(k, io) < 0)
   {
      k->sequences_length -= 1;

      free((void *) stored_sequence);

      return -1;
   }

   set_nth_sequence(k, sorted_sequence_id, sequence_id);

   return 0;
}

/******************************************************************************/
/** SEARCH EXISTING SEQUENCES *************************************************/
/******************************************************************************/

int JH_knowledge_find_sequence
(
   const struct JH_knowledge k [const static 1],
   const JH_index sequence [const restrict static 1],
   const JH_index markov_order, /* Pre: (> 1) */
   JH_index sequence_id [const restrict static 1]
)
{
   /* This is a binary search */
   int cmp;
   JH_index i, current_min, current_max;
   const JH_index markov_sequence_length = (markov_order - 1);

   /* Handles the case where the list is empty ********************************/
   current_max = k->sequences_length;

   if (current_max == 0)
   {
      *sequence_id = 0;

      return -1;
   }
   /***************************************************************************/

   current_min = 0;
   current_max -= 1;

   while (current_min <= current_max)
   {
      i = (current_min + ((current_max - current_min) / 2));

      cmp =
         JH_sequence_cmp
         (
            sequence,
            k->sequences[k->sequences_sorted[i]],
            markov_sequence_length
         );

      if (cmp > 0)
      {
         current_min = (i + 1);

         if (current_min > current_max)
         {
            *sequence_id = current_min;

            return -1;
         }
      }
      else if (cmp < 0)
      {
         if ((current_min >= current_max) || (i == 0))
         {
            *sequence_id = current_min;

            return -1;
         }

         current_max = (i - 1);
      }
      else
      {
         *sequence_id = k->sequences_sorted[i];

         return 0;
      }
   }

   *sequence_id = current_min;

   return -1;
}

/******************************************************************************/
/** EXPORTED ******************************************************************/
/******************************************************************************/

int JH_knowledge_learn_markov_sequence
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index sequence [const restrict static 1],
   const JH_index markov_order, /* Pre (> markov_order 1) */
   JH_index sequence_id [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_index sorted_id;

   if (JH_DEBUG_KNOWLEDGE_LEARN_SEQUENCE)
   {
      JH_index i;

      JH_S_DEBUG
      (
         io,
         JH_DEBUG_KNOWLEDGE_LEARN_SEQUENCE,
         "Studying markov sequence..."
      );

      for (i = 0; i < (markov_order - 1); ++i)
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

   if
   (
      JH_knowledge_find_sequence
      (
         k,
         sequence,
         markov_order,
         sequence_id
      ) == 0
   )
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

   sorted_id = *sequence_id;
   *sequence_id = k->sequences_length;

   return
      add_sequence
      (
         k,
         sequence,
         markov_order,
         *sequence_id,
         sorted_id,
         io
      );
}
