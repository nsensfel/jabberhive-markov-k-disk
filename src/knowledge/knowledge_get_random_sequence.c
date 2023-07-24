#include <stdlib.h>

#include "../core/char.h"
#include "../core/index.h"

#include "../sequence/sequence.h"

#include "../parameters/parameters.h"

#include "../error/error.h"

#include "../io/io.h"

#include "knowledge.h"

/**
 * Picks a random prefix sequence for word, with the occurrence of each prefix
 * sequence being used as their weight.
 *
 * Returns: 0 on success, -1 on error.
 *
 * Pre:
 *    - Read lock on `word_id`.
 *    - `sum == (\sum (\e -> e.occurrences) word[word_id].swt)`.
 *
 * Post:
 *    - `*resulting_id` is the ID of a randomly selected prefix sequence for
 *       word[word_id].
 *
 * Notes:
 *    - Does not acquire locks.
 *    - frees up anything it may have allocated before returning.
 **/
static int weighted_random_pick
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index sum,
   JH_index resulting_id [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_index resulting_ix;
   JH_index accumulator, random_number;

   accumulator = 0;

   if (sum == 0)
   {
      return -1;
   }

   random_number = JH_index_random_up_to(sum);
   /*@ ensures (0 <= random_number <= weights_sum); @*/

   resulting_ix = 0;
   *resulting_id = 0;

   for (;;)
   {
      struct JH_knowledge_adjacent_sequence as;

      if
      (
         JH_io_read_adjacent_sequence_from_id
         (
            params,
            word_id,
            resulting_ix,
            /* is_prefix = */ true,
            &as,
            io
         )
         < 0
      )
      {
         JH_ERROR
         (
            io,
            "Could not read sequence data file {word: %u, swt sequence: %u}.",
            word_id,
            resulting_ix
         );

         return -1;
      }

      accumulator += as.occurrences;

      if (accumulator < random_number)
      {
         resulting_ix += 1;

         JH_knowledge_finalize_adjacent_sequence(&as);
      }
      else
      {
         *resulting_id = as.id;

         JH_knowledge_finalize_adjacent_sequence(&as);

         return 0;
      }
   }
}

/* See: "knowledge.h" */
int JH_knowledge_copy_random_prefix
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const JH_index word_id,
   JH_index copied_prefix [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   struct JH_knowledge_word word;
   JH_index * prefix_sequence;
   JH_index prefix_sequence_id;

   JH_knowledge_readlock_word(k, word_id, io);

   if (JH_io_read_word_from_id(params, word_id, &word, io) < 0)
   {
      JH_knowledge_readunlock_word(k, word_id, io);

      JH_ERROR(io, "Could not get word %u", word_id);

      return -1;
   }

   if
   (
      weighted_random_pick
      (
         params,
         word_id,
         word.occurrences,
         &prefix_sequence_id,
         io
      )
      < 0
   )
   {
      JH_knowledge_readunlock_word(k, word_id, io);

      JH_S_PROG_ERROR
      (
         io,
         "Knowledge inconsistency; there are no acceptable markov sequences "
         "linked to a word that has been picked as being an acceptable pillar."
      );

      JH_knowledge_finalize_word(&word);

      return -1;
   }

   JH_knowledge_readunlock_word(k, word_id, io);
   JH_knowledge_finalize_word(&word);

   if
   (
      JH_io_read_sequence_from_id
      (
         params,
         prefix_sequence_id,
         &prefix_sequence,
         io
      )
      < 0
   )
   {
      return -1;
   }

   memcpy
   (
      (void *) copied_prefix,
      (const void *) prefix_sequence,
      (
         ((size_t) (JH_parameters_get_markov_order(params) - 1))
         * sizeof(JH_index)
      )
   );

   JH_knowledge_finalize_sequence(&prefix_sequence);

   return 0;
}
