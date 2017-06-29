#include <stdlib.h>

#include "../core/char.h"
#include "../core/index.h"

#include "../error/error.h"

#include "../sequence/sequence.h"

#include "knowledge.h"

static int weighted_random_pick
(
   const struct JH_knowledge_sequence_data sd [const restrict static 1],
   JH_index result [const restrict static 1]
)
{
   JH_index accumulator, random_number;

   accumulator = 0;

   if (sd->occurrences == 0)
   {
      return -1;
   }

   random_number = JH_index_random_up_to(sd->occurrences);
   /*@ ensures (0 <= random_number <= weights_sum); @*/

   *result = 0;

   for (;;)
   {
      accumulator += sd->targets[*result].occurrences;

      if (accumulator < random_number)
      {
         *result += 1;
      }
      else
      {
         *result = sd->targets[*result].id;

         return 0;
      }
   }
}

int JH_knowledge_random_tws_target
(
   struct JH_knowledge k [const static 1],
   JH_index target [const restrict static 1],
   const JH_index word_id,
   const JH_index sequence_id,
   FILE io [const restrict static 1]
)
{
   JH_index s_index;

   JH_knowledge_readlock_word(k, word_id, io);

   if
   (
      JH_knowledge_find_markov_sequence
      (
         sequence_id,
         &(k->words[word_id].tws),
         &s_index
      ) < 0
   )
   {
      JH_knowledge_readunlock_word(k, word_id, io);

      return -1;
   }

   if
   (
      weighted_random_pick
      (
         &(k->words[word_id].tws.sequences_ref[s_index]),
         target
      )
      < 0
   )
   {
      JH_knowledge_readunlock_word(k, word_id, io);

      return -1;
   }
   else
   {
      JH_knowledge_readunlock_word(k, word_id, io);

      return 0;
   }
}

int JH_knowledge_random_swt_target
(
   struct JH_knowledge k [const static 1],
   const JH_index sequence_id,
   const JH_index word_id,
   JH_index target [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_index s_index;

   JH_knowledge_readlock_word(k, word_id, io);

   if
   (
      JH_knowledge_find_markov_sequence
      (
         sequence_id,
         &(k->words[word_id].swt),
         &s_index
      ) < 0
   )
   {
      JH_knowledge_readunlock_word(k, word_id, io);

      return -1;
   }

   if
   (
      weighted_random_pick
      (
         &(k->words[word_id].swt.sequences_ref[s_index]),
         target
      )
      < 0
   )
   {
      JH_knowledge_readunlock_word(k, word_id, io);

      return -1;
   }
   else
   {
      JH_knowledge_readunlock_word(k, word_id, io);

      return 0;
   }
}
