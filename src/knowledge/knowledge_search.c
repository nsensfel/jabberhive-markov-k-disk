#include <stdlib.h>

#include "../core/char.h"
#include "../core/index.h"
#include "../sequence/sequence.h"

#include "../error/error.h"

#include "knowledge.h"

/* See "knowledge.h". */
int JH_knowledge_find_word_id
(
   const struct JH_knowledge k [const restrict static 1],
   const JH_char word [const restrict static 1],
   const size_t word_length,
   JH_index result [const restrict static 1]
)
{
   /* This is a binary search */
   int cmp;
   JH_index i, current_min, current_max;

   /* Handles the case where the list is empty ********************************/
   current_max = k->words_length;

   if (current_max == 0)
   {
      *result = 0;

      return -1;
   }
   /***************************************************************************/

   current_min = 0;
   current_max -= 1;

   while (current_min <= current_max)
   {
      i = (current_min + ((current_max - current_min) / 2));

      cmp =
         JH_word_cmp
         (
            word,
            word_length,
            k->words[k->words_sorted[i]].word,
            k->words[k->words_sorted[i]].word_length
         );

      if (cmp > 0)
      {
         current_min = (i + 1);

         if (current_min > current_max)
         {
            *result = current_min;

            return -1;
         }
      }
      else if (cmp < 0)
      {
         if ((current_min >= current_max) || (i == 0))
         {
            *result = current_min;

            return -1;
         }

         current_max = (i - 1);
      }
      else
      {
         *result = k->words_sorted[i];

         return 0;
      }
   }

   *result = current_min;

   return -1;
}

int JH_knowledge_find_markov_sequence
(
   const JH_index sequence_id,
   const struct JH_knowledge_sequence_collection sc [const restrict static 1],
   JH_index result [const restrict static 1]
)
{
   /* This is a binary search */
   int cmp;
   JH_index i, current_min, current_max;

   if (sc->sequences_ref_length == 0)
   {
      *result = 0;

      return -1;
   }

   current_min = 0;
   current_max = (sc->sequences_ref_length - 1);

   while (current_min <= current_max)
   {
      i = (current_min + ((current_max - current_min) / 2));

      cmp =
         JH_index_cmp
         (
            sequence_id,
            sc->sequences_ref[sc->sequences_ref_sorted[i]].id
         );

      if (cmp > 0)
      {
         current_min = (i + 1);

         if (current_min > current_max)
         {
            *result = current_min;

            return -1;
         }
      }
      else if (cmp < 0)
      {
         if ((current_min >= current_max) || (i == 0))
         {
            *result = current_min;

            return -1;
         }

         current_max = (i - 1);
      }
      else
      {
         *result = sc->sequences_ref_sorted[i];

         return 0;
      }
   }

   *result = current_min;

   return -1;
}

int JH_knowledge_find_sequence_target
(
   const JH_index target_id,
   const struct JH_knowledge_sequence_data sd [const restrict static 1],
   JH_index result [const restrict static 1]
)
{
   /* This is a binary search */
   int cmp;
   JH_index i, current_min, current_max;

   if (sd->targets_length == 0)
   {
      *result = 0;

      return -1;
   }

   current_min = 0;
   current_max = (sd->targets_length - 1);

   while (current_min <= current_max)
   {
      i = (current_min + ((current_max - current_min) / 2));

      cmp = JH_index_cmp(target_id, sd->targets[i].id);

      if (cmp > 0)
      {
         current_min = (i + 1);

         if (current_min > current_max)
         {
            *result = current_min;

            return -1;
         }
      }
      else if (cmp < 0)
      {
         if ((current_min >= current_max) || (i == 0))
         {
            *result = current_min;

            return -1;
         }

         current_max = (i - 1);
      }
      else
      {
         *result = i;

         return 0;
      }
   }

   *result = current_min;

   return -1;
}
