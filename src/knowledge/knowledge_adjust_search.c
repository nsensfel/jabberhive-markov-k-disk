#include <stdlib.h>
#include <string.h>
#include <errno.h>

#include "../core/char.h"
#include "../core/index.h"
#include "../sequence/sequence.h"

#include "../io/io.h"

#include "../parameters/parameters.h"

#include "../error/error.h"

#include "knowledge.h"

int JH_knowledge_lazy_find_sequence
(
   const struct JH_parameters params [const restrict static 1],
   const struct JH_knowledge k [const restrict static 1],
   const JH_index sequence [const restrict static 1],
   JH_index found_sequence_id [const restrict static 1],
   JH_index expected_sequence_sorted_ix [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   int cmp, mod;
   JH_index * candidate_sequence;

   const JH_index markov_sequence_length =
      (
         JH_parameters_get_markov_order(params)
         - 1
      );

   /* Handles the case where the list is empty ********************************/

   if (k->sequences_length == 0)
   {
      *expected_sequence_sorted_ix = 0;
      *found_sequence_id = 0;

      return 0;
   }

   /***************************************************************************/

   if ((*expected_sequence_sorted_ix) >= k->sequences_length)
   {
      // No new sequences were inserted, and this sequence belongs to the end
      // of the sorted list.
      return 0;
   }

   mod = 0;

   for (;;)
   {
      if
      (
         JH_io_read_sequence_from_id
         (
            params,
            k->sequences_sorted[*expected_sequence_sorted_ix],
            &candidate_sequence,
            io
         )
         < 0
      )
      {
         return -2;
      }

      cmp =
         JH_sequence_cmp
         (
            markov_sequence_length,
            sequence,
            candidate_sequence
         );

      JH_knowledge_finalize_sequence(&candidate_sequence);

      if (cmp > 0)
      {
         // Need to go at a higher index.

         if (mod < 0)
         {
            // We were going to lower the index
            // so we should be returning index we had just before.
            *expected_sequence_sorted_ix += 1;

            return 0;
         }

         mod = 1;

         *expected_sequence_sorted_ix += 1;

         if ((*expected_sequence_sorted_ix) >= k->sequences_length)
         {
            // Last element of the list is lower than target.

            return 0;
         }
      }
      else if (cmp == 0)
      {
         *found_sequence_id = k->sequences_sorted[*expected_sequence_sorted_ix];

         return 1;
      }
      else if (cmp < 0)
      {
         // Need to go at a lower index.

         if (mod > 0)
         {
            // We were going up.
            // So our current index is what we want.

            return 0;
         }

         mod = -1;

         if (*expected_sequence_sorted_ix > 0)
         {
            *expected_sequence_sorted_ix -= 1;
         }
         else
         {
            // first element of sorted list is greater than target.

            return 0;
         }
      }
   }
}

/* See "knowledge.h". */
int JH_knowledge_lazy_find_word
(
   const struct JH_parameters params [const restrict static 1],
   const struct JH_knowledge k [const restrict static 1],
   const size_t word_size,
   const JH_char word [const restrict static word_size],
   JH_index found_word_id [const restrict static 1],
   JH_index expected_word_sorted_ix [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   /* This is a binary search */
   int cmp, mod;
   struct JH_knowledge_word candidate;

   /* Handles the case where the list is empty ********************************/
   if (k->words_length == 0)
   {
      *found_word_id = 0;
      *expected_word_sorted_ix = 0;

      return 0;
   }

   /***************************************************************************/

   if ((*expected_word_sorted_ix) >= k->words_length)
   {
      // No new words were inserted, and this word belongs to the end of the
      // sorted list.

      return 0;
   }

   for (;;)
   {
      if
      (
         JH_io_read_word_from_id
         (
            params,
            k->words_sorted[*expected_word_sorted_ix],
            &candidate,
            io
         )
         < 0
      )
      {
         return -1;
      }

      cmp =
         JH_word_cmp
         (
            word_size,
            word,
            candidate.word_length,
            candidate.word
         );

      JH_knowledge_finalize_word(&candidate);

      if (cmp > 0)
      {
         // word is higher.
         if (mod < 0)
         {
            // We were going down, so
            // should be the index we had just before.
            *expected_word_sorted_ix += 1;

            return 0;
         }

         mod = 1;

         *expected_word_sorted_ix += 1;

         if ((*expected_word_sorted_ix) >= k->words_length)
         {
            // end of list.
            return 0;
         }
      }
      else if (cmp == 0)
      {
         *found_word_id = k->words_sorted[*expected_word_sorted_ix];

         return 1;
      }
      else if (cmp < 0)
      {
         // word is lower.

         if (mod > 0)
         {
            // We were going up, so it
            // should be at this index.
            return 0;
         }

         mod = -1;

         if (*expected_word_sorted_ix > 0)
         {
            *expected_word_sorted_ix -= 1;
         }
         else
         {
            // first element of sorted list is greater than target.

            return 0;
         }
      }
   }
}
