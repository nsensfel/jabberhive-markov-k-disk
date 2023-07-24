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
   const bool update_adjacent,
   FILE io [const restrict static 1]
)
{
   char * adjacent_sequence_filename;
   struct JH_knowledge_target target;
   struct JH_knowledge_adjacent_sequence as;
   JH_index previous_length;

   if (update_adjacent)
   {
      if
      (
         JH_io_generate_adjacent_sequence_filename
         (
            params,
            word_id,
            adjacent_sequence_ix,
            is_swt,
            &adjacent_sequence_filename,
            io
         )
         < 0
      )
      {
         return -1;
      }

      if (JH_io_read_adjacent_sequence(adjacent_sequence_filename, &as, io) < 0)
      {
         free((void *) adjacent_sequence_filename);

         return -2;
      }

      /* (as->targets_length == JH_INDEX_MAX) => target_id \in as->targets. */

      previous_length = as.targets_length;

      as.targets_length += 1;


      if (JH_io_write_adjacent_sequence(adjacent_sequence_filename, &as, io) < 0)
      {
         free((void *) adjacent_sequence_filename);
         JH_knowledge_finalize_adjacent_sequence(&as);

         return -3;
      }

      free((void *) adjacent_sequence_filename);
      JH_knowledge_finalize_adjacent_sequence(&as);

      if
      (
         (t_index < previous_length)
         &&
         (
            JH_io_shift_sequence_target_from_id
            (
               params,
               word_id,
               adjacent_sequence_ix,
               is_swt,
               t_index,
               previous_length,
               io
            )
            < 0
         )
      )
      {
         return -1;
      }
   }

   target.id = target_id;
   target.occurrences = 1;

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
   char * word_filename;
   JH_index previous_length;
   struct JH_knowledge_word word;
   struct JH_knowledge_adjacent_sequence as;

   if (JH_io_generate_word_filename(params, word_id, &word_filename, io) < 0)
   {
      return -1;
   }

   if (JH_io_read_word(word_filename, &word, io) < 0)
   {
      free((void *) word_filename);

      return -2;
   }

   if (is_swt)
   {
      previous_length = word.swt_sequences_ref_length;
      word.swt_sequences_ref_length += 1;
   }
   else
   {
      previous_length = word.tws_sequences_ref_length;
      word.tws_sequences_ref_length += 1;
   }

   if (JH_io_write_word(word_filename, &word, io) < 0)
   {
      free((void *) word_filename);

      JH_knowledge_finalize_word(&word);

      return -3;
   }

   free((void *) word_filename);
   JH_knowledge_finalize_word(&word);

   if
   (
      (adjacent_sequence_ix < previous_length)
      &&
      (
         JH_io_shift_adjacent_sequence_from_id
         (
            params,
            word_id,
            adjacent_sequence_ix,
            is_swt,
            previous_length,
            io
         )
         < 0
      )
   )
   {
      return -4;
   }

   as.id = sequence_id;
   as.occurrences = 1;
   as.targets_length = 1;

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
      return -5;
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
      return -6;
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
   bool new_sequence, new_target;
   JH_index t_index;
   struct JH_knowledge_target target;
   struct JH_knowledge_adjacent_sequence as;
   JH_index adjacent_sequence_ix;

   new_sequence = false;
   new_target = false;

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
   /*
      JH_DEBUG
      (
         io,
         1,
         "New sequence of {%u, %u, %d}: %u",
         word_id,
         adjacent_sequence_ix,
         is_swt,
         sequence_id
      );
*/
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

      new_sequence = true;
   }

   if (!new_sequence)
   {
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
         new_target = true;
      }
   }
   else
   {
      new_target = true;
      t_index = 0;
   }

   if (new_target)
   {
   /*
      JH_DEBUG
      (
         io,
         1,
         "New target of {%u, %u, %d}: %u (ix: %u).",
         word_id,
         adjacent_sequence_ix,
         is_swt,
         target_id,
         t_index
      );
*/
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
            !new_sequence,
            io
         )
         < 0
      )
      {
         JH_knowledge_writeunlock_word(k, word_id, io);

         return -1;
      }
   }

   if (!new_sequence)
   {
      char * filename;

      if
      (
         JH_io_generate_adjacent_sequence_filename
         (
            params,
            word_id,
            adjacent_sequence_ix,
            is_swt,
            &filename,
            io
         )
         < 0
      )
      {
         JH_knowledge_writeunlock_word(k, word_id, io);

         return -1;
      }

      if (JH_io_read_adjacent_sequence(filename, &as, io) < 0)
      {
         free((void *) filename);
         JH_knowledge_writeunlock_word(k, word_id, io);

         return -2;
      }

      if (as.occurrences == JH_INDEX_MAX)
      {
         free((void *) filename);
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

      if (JH_io_write_adjacent_sequence(filename, &as, io) < 0)
      {
         free((void *) filename);
         JH_knowledge_writeunlock_word(k, word_id, io);
         JH_knowledge_finalize_adjacent_sequence(&as);

         return -1;
      }

      free((void *) filename);
      JH_knowledge_finalize_adjacent_sequence(&as);
   }

   if (!new_target)
   {
      char * filename;

      if
      (
         JH_io_generate_sequence_target_filename
         (
            params,
            word_id,
            adjacent_sequence_ix,
            is_swt,
            t_index,
            &filename,
            io
         )
         < 0
      )
      {
         JH_knowledge_writeunlock_word(k, word_id, io);

         return -1;
      }

      if (JH_io_read_sequence_target(filename, &target, io) < 0)
      {
         free((void *) filename);
         JH_knowledge_writeunlock_word(k, word_id, io);

         return -1;
      }

      if (target.occurrences == JH_INDEX_MAX)
      {
         JH_ERROR
         (
            io,
            "[E] Unable to strengthen %s link: link is already at max strength.",
            filename
         );

         free((void *) filename);

         JH_knowledge_writeunlock_word(k, word_id, io);
         JH_knowledge_finalize_sequence_target(&target);

         return -1;
      }

      target.occurrences += 1;

      if (JH_io_write_sequence_target(filename, &target, io) < 0)
      {
         free((void *) filename);

         JH_knowledge_writeunlock_word(k, word_id, io);
         JH_knowledge_finalize_sequence_target(&target);

         return -1;
      }

      free((void *) filename);
      JH_knowledge_finalize_sequence_target(&target);
   }

   JH_knowledge_writeunlock_word(k, word_id, io);

   return 0;
}
