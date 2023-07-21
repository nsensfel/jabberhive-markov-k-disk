#include <stdlib.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../sequence/sequence.h"

#include "../error/error.h"

#include "../io/io.h"

#include "../parameters/parameters.h"

#include "knowledge.h"

/******************************************************************************/
/** LEARN FOLLOWING SEQUENCE **************************************************/
/******************************************************************************/
static void parse_swt_sequence
(
   const JH_index sequence [const restrict static 1],
   const size_t index,
   const JH_index buffer_length,
   JH_index buffer [const restrict static buffer_length]
)
{
   size_t j;
   size_t index_offset;

   index_offset = buffer_length;

   for (j = 0; j < buffer_length; ++j)
   {
      if (index >= index_offset)
      {
         buffer[j] = sequence[index - index_offset];
      }
      else
      {
         buffer[j] = JH_START_OF_SEQUENCE_ID;
      }

      --index_offset;
   }
}

static int add_swt_sequence
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const size_t sequence_length,
   const JH_index sequence [const restrict static sequence_length],
   const size_t index,
   const JH_index buffer_length,
   JH_index buffer [const restrict static buffer_length],
   FILE io [const restrict static 1]
)
{
   JH_index sequence_id;

   parse_swt_sequence(sequence, index, buffer_length, buffer);

   if
   (
      JH_knowledge_learn_markov_sequence
      (
         params,
         k,
         buffer,
         &sequence_id,
         io
      ) < 0
   )
   {
      return -1;
   }

   if (index == (sequence_length - 1))
   {
      return
         JH_knowledge_strengthen_adjacent_sequence
         (
            params,
            k,
            sequence_id,
            sequence[index],
            JH_END_OF_SEQUENCE_ID,
            /* is_swt = */ true,
            io
         );
   }
   else
   {
      return
         JH_knowledge_strengthen_adjacent_sequence
         (
            params,
            k,
            sequence_id,
            sequence[index],
            sequence[index + 1],
            /* is_swt = */ true,
            io
         );
   }
}

/******************************************************************************/
/** LEARN PRECEDING SEQUENCE **************************************************/
/******************************************************************************/
static void parse_tws_sequence
(
   const size_t sequence_length,
   const JH_index sequence [const restrict static sequence_length],
   const size_t index,
   const JH_index buffer_length,
   JH_index buffer [const restrict static buffer_length]
)
{
   size_t j;
   size_t index_offset;

   for (j = 0; j < buffer_length; ++j)
   {
      index_offset = (j + 1) + index;

      if (sequence_length > index_offset)
      {
         buffer[j] = sequence[index_offset];
      }
      else
      {
         buffer[j] = JH_END_OF_SEQUENCE_ID;
      }
   }
}

static int add_tws_sequence
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const size_t sequence_length,
   const JH_index sequence [const restrict static sequence_length],
   const size_t index,
   const JH_index buffer_length,
   JH_index buffer [const restrict static buffer_length],
   FILE io [const restrict static 1]
)
{
   JH_index sequence_id;

   parse_tws_sequence(sequence_length, sequence, index, buffer_length, buffer);

   if
   (
      JH_knowledge_learn_markov_sequence
      (
         params,
         k,
         buffer,
         &sequence_id,
         io
      ) < 0
   )
   {
      return -1;
   }

   if (index == 0)
   {
      return
         JH_knowledge_strengthen_adjacent_sequence
         (
            params,
            k,
            sequence_id,
            sequence[index],
            JH_START_OF_SEQUENCE_ID,
            /* is_swt = */ false,
            io
         );
   }
   else
   {
      return
         JH_knowledge_strengthen_adjacent_sequence
         (
            params,
            k,
            sequence_id,
            sequence[index],
            sequence[index - 1],
            /* is_swt = */ false,
            io
         );
   }
}

/******************************************************************************/
/** EXPORTED ******************************************************************/
/******************************************************************************/
int JH_knowledge_learn_sequence
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const size_t sequence_length,
   const JH_index sequence [const restrict static sequence_length],
   FILE io [const restrict static 1]
)
{
   JH_index * buffer;
   size_t i;
   const JH_index buffer_length = (JH_parameters_get_markov_order(params) - 1);

   buffer =
      (JH_index *) calloc
      (
         (size_t) buffer_length,
         sizeof(JH_index)
      );

   if (buffer == (JH_index *) NULL)
   {
      JH_S_ERROR
      (
         io,
         "Unable to allocate memory required to create markov sequences."
      );

      return -1;
   }

   for (i = 0; i < sequence_length; ++i)
   {
      char * word_filename;
      struct JH_knowledge_word word;

      if
      (
         add_swt_sequence
         (
            params,
            k,
            sequence_length,
            sequence,
            i,
            buffer_length,
            buffer,
            io
         ) < 0
      )
      {
         free((void *) buffer);

         return -1;
      }

      /* TODO: handle failure. */
      if
      (
         add_tws_sequence
         (
            params,
            k,
            sequence_length,
            sequence,
            i,
            buffer_length,
            buffer,
            io
         ) < 0
      )
      {
         free((void *) buffer);

         return -1;
      }

      JH_knowledge_writelock_word(k, sequence[i], io);

      if
      (
         JH_io_generate_word_filename
         (
            params,
            sequence[i],
            &word_filename,
            io
         )
         < 0
      )
      {
         JH_knowledge_writeunlock_word(k, sequence[i], io);
         free((void *) buffer);

         return -1;
      }

      if (JH_io_read_word(word_filename, &word, io) < 0)
      {
         free((void *) buffer);
         free((void *) word_filename);
         JH_knowledge_writeunlock_word(k, sequence[i], io);

         return -1;
      }

      word.occurrences += 1;

      if (JH_io_write_word(word_filename, &word, io) < 0)
      {
         JH_knowledge_finalize_word(&word);
         free((void *) buffer);
         free((void *) word_filename);
         JH_knowledge_writeunlock_word(k, sequence[i], io);

         return -1;
      }

      JH_knowledge_finalize_word(&word);
      free((void *) word_filename);
      JH_knowledge_writeunlock_word(k, sequence[i], io);
   }

   free((void *) buffer);

   return 0;
}
