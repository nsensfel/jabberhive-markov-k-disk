#include <stdlib.h>

#include "../core/char.h"
#include "../core/index.h"

#include "../error/error.h"

#include "../sequence/sequence.h"

#include "../parameters/parameters.h"

#include "../io/io.h"

#include "knowledge.h"

static int weighted_random_target_id_pick
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool sequence_is_prefix,
   JH_index resulting_id [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   struct JH_knowledge_adjacent_sequence as;
   JH_index resulting_ix;
   JH_index accumulator, random_number;

   accumulator = 0;

   if
   (
      JH_io_read_adjacent_sequence_from_id
      (
         params,
         word_id,
         adjacent_sequence_ix,
         sequence_is_prefix,
         &as,
         io
      )
      < 0
   )
   {
      return -2;
   }

   if (as.occurrences == 0)
   {
      JH_knowledge_finalize_adjacent_sequence(&as);

      return -1;
   }

   random_number = JH_index_random_up_to(as.occurrences);
   /*@ ensures (0 <= random_number <= weights_sum); @*/

   JH_knowledge_finalize_adjacent_sequence(&as);

   *resulting_id = 0;
   resulting_ix = 0;

   for (;;)
   {
      struct JH_knowledge_target target;

      if
      (
         JH_io_read_sequence_target_from_id
         (
            params,
            word_id,
            adjacent_sequence_ix,
            sequence_is_prefix,
            resulting_ix,
            &target,
            io
         )
         < 0
      )
      {
         return -3;
      }

      accumulator += target.occurrences;

      if (accumulator < random_number)
      {
         resulting_ix += 1;

         JH_knowledge_finalize_sequence_target(&target);
      }
      else
      {
         *resulting_id = target.id;

         JH_knowledge_finalize_sequence_target(&target);

         return 0;
      }
   }
}

int JH_knowledge_random_target
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const JH_index word_id,
   const JH_index sequence_id,
   const bool is_swt,
   JH_index target [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_index adjacent_sequence_index;

   JH_knowledge_readlock_word(k, word_id, io);

   if
   (
      JH_knowledge_find_adjacent_sequence
      (
         params,
         sequence_id,
         word_id,
         is_swt,
         &adjacent_sequence_index,
         io
      )
      < 0
   )
   {
      JH_knowledge_readunlock_word(k, word_id, io);

      return -1;
   }

   if
   (
      weighted_random_target_id_pick
      (
         params,
         word_id,
         adjacent_sequence_index,
         is_swt,
         target,
         io
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
