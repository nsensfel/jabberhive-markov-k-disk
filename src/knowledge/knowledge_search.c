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

int JH_knowledge_find_sequence
(
   const struct JH_parameters params [const restrict static 1],
   const struct JH_knowledge k [const restrict static 1],
   const JH_index sequence [const restrict static 1],
   JH_index found_sequence_id [const restrict static 1],
   JH_index expected_sequence_sorted_ix [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   /* This is a binary search */
   int cmp;
   JH_index i, current_min, current_max;
   JH_index * candidate_sequence;

   const JH_index markov_sequence_length =
      (
         JH_parameters_get_markov_order(params)
         - 1
      );

   /* Handles the case where the list is empty ********************************/
   current_max = k->sequences_length;

   if (current_max == 0)
   {
      *expected_sequence_sorted_ix = 0;
      *found_sequence_id = 0;

      return 0;
   }

   /***************************************************************************/

   current_min = 0;
   current_max -= 1;

   while (current_min <= current_max)
   {

      i = (current_min + ((current_max - current_min) / 2));

      if
      (
         JH_io_read_sequence_from_id
         (
            params,
            k->sequences_sorted[i],
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
            sequence,
            candidate_sequence,
            markov_sequence_length
         );

      JH_knowledge_finalize_sequence(&candidate_sequence);

      if (cmp > 0)
      {
         current_min = (i + 1);

         if (current_min > current_max)
         {
            *found_sequence_id = k->sequences_length;
            *expected_sequence_sorted_ix = current_min;

            return 0;
         }
      }
      else if (cmp < 0)
      {
         if ((current_min >= current_max) || (i == 0))
         {
            *found_sequence_id = k->sequences_length;
            *expected_sequence_sorted_ix = current_min;

            return 0;
         }

         current_max = (i - 1);
      }
      else
      {
         *found_sequence_id = k->sequences_sorted[i];
         *expected_sequence_sorted_ix = i;

         return 1;
      }
   }

   *found_sequence_id = k->sequences_length;
   *expected_sequence_sorted_ix = current_min;

   return 0;
}

/* See "knowledge.h". */
int JH_knowledge_find_word
(
   const struct JH_parameters params [const restrict static 1],
   const struct JH_knowledge k [const restrict static 1],
   const JH_char word [const restrict static 1],
   const size_t word_size,
   JH_index found_word_id [const restrict static 1],
   JH_index expected_word_sorted_ix [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   /* This is a binary search */
   int cmp;
   JH_index current_min, current_max;

   /* Handles the case where the list is empty ********************************/
   current_max = k->words_length;

   if (current_max == 0)
   {
      *found_word_id = 0;
      *expected_word_sorted_ix = 0;

      return 0;
   }
   /***************************************************************************/

   current_min = 0;
   current_max -= 1;

   while (current_min <= current_max)
   {
      struct JH_knowledge_word candidate;

      *expected_word_sorted_ix =
         (
            current_min
            + ((current_max - current_min) / 2)
         );

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
            word,
            word_size,
            candidate.word,
            candidate.word_length
         );

      JH_knowledge_finalize_word(&candidate);

      if (cmp > 0)
      {
         current_min = ((*expected_word_sorted_ix) + 1);

         if (current_min > current_max)
         {
            *found_word_id = k->words_length;
            *expected_word_sorted_ix = current_min;

            return 0;
         }
      }
      else if (cmp < 0)
      {
         if ((current_min >= current_max) || (*expected_word_sorted_ix == 0))
         {
            *found_word_id = k->words_length;
            *expected_word_sorted_ix = current_min;

            return 0;
         }

         current_max = ((*expected_word_sorted_ix) - 1);
      }
      else
      {
         *found_word_id = k->words_sorted[*expected_word_sorted_ix];

         return 1;
      }
   }

   *found_word_id = k->words_length;
   *expected_word_sorted_ix = current_min;

   return 0;
}

int JH_knowledge_find_adjacent_sequence
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index sequence_id,
   const JH_index word_id,
   const bool is_swt,
   JH_index expected_index [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   struct JH_knowledge_word word;
   JH_index * collection_length;

   /* This is a binary search */
   int cmp;
   JH_index i, current_min, current_max;

   if (JH_io_read_word_from_id(params, word_id, &word, io) < 0)
   {
      return -1;
   }

   collection_length =
      (
         is_swt ?
         &(word.swt_sequences_ref_length)
         :
         &(word.tws_sequences_ref_length)
      );

   JH_knowledge_finalize_word(&word);

   if ((*collection_length) == 0)
   {
      *expected_index = 0;

      return 0;
   }

   current_min = 0;
   current_max = ((*collection_length) - 1);

   while (current_min <= current_max)
   {
      struct JH_knowledge_adjacent_sequence as;

      i = (current_min + ((current_max - current_min) / 2));

      if
      (
         JH_io_read_adjacent_sequence_from_id
         (
            params,
            word_id,
            i,
            is_swt,
            &as,
            io
         )
         < 0
      )
      {
         return -1;
      }

      cmp = JH_index_cmp(sequence_id, as.id);

      JH_knowledge_finalize_adjacent_sequence(&as);

      if (cmp > 0)
      {
         current_min = (i + 1);

         if (current_min > current_max)
         {
            *expected_index = current_min;

            return 0;
         }
      }
      else if (cmp < 0)
      {
         if ((current_min >= current_max) || (i == 0))
         {
            *expected_index = current_min;

            return 0;
         }

         current_max = (i - 1);
      }
      else
      {
         *expected_index = i;

         return 1;
      }
   }

   *expected_index = current_min;

   return 0;
}

int JH_knowledge_find_sequence_target
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
   const JH_index target_id,
   JH_index result_ix [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   /* This is a binary search */
   struct JH_knowledge_adjacent_sequence as;
   int cmp;
   JH_index i, current_min, current_max;

   if
   (
      JH_io_read_adjacent_sequence_from_id
      (
         params,
         word_id,
         adjacent_sequence_ix,
         is_swt,
         &as,
         io
      )
      < 0
   )
   {
      return -1;
   }

   if (as.targets_length == 0)
   {
      *result_ix = 0;

      JH_knowledge_finalize_adjacent_sequence(&as);

      return 0;
   }

   current_min = 0;
   current_max = (as.targets_length - 1);

   while (current_min <= current_max)
   {
      struct JH_knowledge_target st;

      i = (current_min + ((current_max - current_min) / 2));

      if
      (
         JH_io_read_sequence_target_from_id
         (
            params,
            word_id,
            adjacent_sequence_ix,
            is_swt,
            i,
            &st,
            io
         )
         < 0
      )
      {
         JH_knowledge_finalize_adjacent_sequence(&as);

         return -1;
      }

      cmp = JH_index_cmp(target_id, st.id);

      JH_knowledge_finalize_sequence_target(&st);

      if (cmp > 0)
      {
         current_min = (i + 1);

         if (current_min > current_max)
         {
            *result_ix = current_min;

            JH_knowledge_finalize_adjacent_sequence(&as);

            return 0;
         }
      }
      else if (cmp < 0)
      {
         if ((current_min >= current_max) || (i == 0))
         {
            *result_ix = current_min;

            JH_knowledge_finalize_adjacent_sequence(&as);

            return 0;
         }

         current_max = (i - 1);
      }
      else
      {
         *result_ix = i;

         JH_knowledge_finalize_adjacent_sequence(&as);

         return 1;
      }
   }

   *result_ix = current_min;

   JH_knowledge_finalize_adjacent_sequence(&as);

   return 0;
}
