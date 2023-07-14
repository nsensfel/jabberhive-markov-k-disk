#include <stdlib.h>

#include "../core/index.h"

#include "../error/error.h"

#include "../io/io.h"

#include "../parameters/parameters.h"

#include "knowledge.h"

static int add_target
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
   const JH_index target_id,
   const JH_index t_index,
   FILE io [const restrict static 1]
)
{
   struct JH_knowledge_target target;
   struct JH_knowledge_adjacent_sequence as;
   JH_index length;

   // FIXME: can optimize filename generation.
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

   /* (as->targets_length == JH_INDEX_MAX) => target_id \in as->targets. */

   as.targets_length += 1;

   length = as.targets_length;

   if
   (
      JH_io_write_adjacent_sequence_from_id
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
      JH_knowledge_finalize_adjacent_sequence(&as);

      return -1;
   }

   JH_knowledge_finalize_adjacent_sequence(&as);

   if (t_index != (length - 1))
   {
      if
      (
         JH_io_shift_sequence_target_from_id
         (
            params,
            word_id,
            adjacent_sequence_ix,
            is_swt,
            t_index,
            (length - 1),
            io
         )
         < 0
      )
      {
         return -1;
      }
   }

   target.id = target_id;
   target.occurrences = 0;

   if
   (
      JH_io_write_sequence_target_from_id
      (
         params,
         word_id,
         adjacent_sequence_ix,
         is_swt,
         t_index,
         &target,
         io
      )
      < 0
   )
   {
      return -1;
   }

   return 0;
}

static int add_adjacent_sequence
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
   const JH_index sequence_id,
   FILE io [const restrict static 1]
)
{
   JH_index new_length;
   struct JH_knowledge_word word;
   struct JH_knowledge_adjacent_sequence as;

   if (JH_io_read_word_from_id(params, word_id, &word, io) < 0)
   {
      return -1;
   }

   if (is_swt)
   {
      word.swt_sequences_ref_length += 1;
      new_length = word.swt_sequences_ref_length;
   }
   else
   {
      word.tws_sequences_ref_length += 1;
      new_length = word.tws_sequences_ref_length;
   }

   if (JH_io_write_word_from_id(params, word_id, &word, io) < 0)
   {
      JH_knowledge_finalize_word(&word);

      return -2;
   }

   JH_knowledge_finalize_word(&word);

   if
   (
      JH_io_shift_adjacent_sequence_from_id
      (
         params,
         word_id,
         adjacent_sequence_ix,
         is_swt,
         (new_length - 1),
         io
      )
      < 0
   )
   {
      return -3;
   }

   as.id = sequence_id;
   as.occurrences = 0;
   as.targets_length = 0;

   if
   (
      JH_io_generate_adjacent_sequence_directory_from_id
      (
         params,
         word_id,
         adjacent_sequence_ix,
         is_swt,
         io
      )
      < 0
   )
   {
      return -4;
   }

   if
   (
      JH_io_write_adjacent_sequence_from_id
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
      return -5;
   }

   return 0;
}

int JH_knowledge_strengthen_adjacent_sequence
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const JH_index sequence_id,
   const JH_index word_id,
   const JH_index target_id,
   const bool is_swt,
   FILE io [const restrict static 1]
)
{
   int i;
   JH_index t_index;
   struct JH_knowledge_target target;
   struct JH_knowledge_adjacent_sequence as;
   JH_index adjacent_sequence_ix;

   JH_knowledge_writelock_word(k, word_id, io);

   i =
      JH_knowledge_find_adjacent_sequence
      (
         params,
         sequence_id,
         word_id,
         is_swt,
         &adjacent_sequence_ix,
         io
      );

   if (i < 0)
   {
      JH_knowledge_writeunlock_word(k, word_id, io);

      return -1;
   }

   if (i == 0)
   {
      if
      (
         add_adjacent_sequence
         (
            params,
            word_id,
            adjacent_sequence_ix,
            is_swt,
            sequence_id,
            io
         )
         < 0
      )
      {
         JH_knowledge_writeunlock_word(k, word_id, io);

         return -1;
      }
   }

   i =
      JH_knowledge_find_sequence_target
      (
         params,
         word_id,
         adjacent_sequence_ix,
         is_swt,
         target_id,
         &t_index,
         io
      );

   if (i < 0)
   {
      JH_knowledge_writeunlock_word(k, word_id, io);

      return -1;
   }

   if (i == 0)
   {
      if
      (
         add_target
         (
            params,
            word_id,
            adjacent_sequence_ix,
            is_swt,
            target_id,
            t_index,
            io
         )
         < 0
      )
      {
         JH_knowledge_writeunlock_word(k, word_id, io);

         return -1;
      }
   }

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
      JH_knowledge_writeunlock_word(k, word_id, io);

      return -1;
   }

   if (as.occurrences == JH_INDEX_MAX)
   {
      JH_knowledge_writeunlock_word(k, word_id, io);
      JH_knowledge_finalize_adjacent_sequence(&as);

      JH_S_ERROR
      (
         io,
         "[E] Unable to strengthen link: link is already at max strength."
      );

      return -1;

   }

   as.occurrences += 1;

   if
   (
      JH_io_write_adjacent_sequence_from_id
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
      JH_knowledge_writeunlock_word(k, word_id, io);
      JH_knowledge_finalize_adjacent_sequence(&as);

      return -1;
   }

   JH_knowledge_finalize_adjacent_sequence(&as);

   if
   (
      JH_io_read_sequence_target_from_id
      (
         params,
         word_id,
         adjacent_sequence_ix,
         is_swt,
         t_index,
         &target,
         io
      )
      < 0
   )
   {
      JH_knowledge_writeunlock_word(k, word_id, io);

      return -1;
   }

   if (target.occurrences == JH_INDEX_MAX)
   {
      JH_S_ERROR
      (
         io,
         "[E] Unable to strengthen link: link is already at max strength."
      );

      JH_knowledge_writeunlock_word(k, word_id, io);
      JH_knowledge_finalize_sequence_target(&target);

      return -1;
   }

   target.occurrences += 1;

   if
   (
      JH_io_write_sequence_target_from_id
      (
         params,
         word_id,
         adjacent_sequence_ix,
         is_swt,
         t_index,
         &target,
         io
      )
      < 0
   )
   {
      JH_knowledge_writeunlock_word(k, word_id, io);
      JH_knowledge_finalize_sequence_target(&target);

      return -1;
   }

   JH_knowledge_finalize_sequence_target(&target);
   JH_knowledge_writeunlock_word(k, word_id, io);

   return 0;
}
