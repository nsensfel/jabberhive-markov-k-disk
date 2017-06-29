#include <stdlib.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../sequence/sequence.h"

#include "../error/error.h"

#include "knowledge.h"

/******************************************************************************/
/** LEARN FOLLOWING SEQUENCE **************************************************/
/******************************************************************************/
static void parse_swt_sequence
(
   const JH_index sequence [const restrict static 1],
   const size_t index,
   JH_index buffer [const restrict static 1],
   const JH_index buffer_length
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
   struct JH_knowledge k [const restrict static 1],
   const JH_index sequence [const restrict static 1],
   const size_t index,
   const size_t sequence_length,
   const JH_index markov_order,
   JH_index buffer [const restrict static 1],
   const JH_index buffer_length,
   FILE io [const restrict static 1]
)
{
   JH_index sequence_id;

   parse_swt_sequence(sequence, index, buffer, buffer_length);

   if
   (
      JH_knowledge_learn_markov_sequence
      (
         k,
         buffer,
         (buffer_length + 1),
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
         JH_knowledge_strengthen_swt
         (
            k,
            sequence_id,
            sequence[index],
            JH_END_OF_SEQUENCE_ID,
            io
         );
   }
   else
   {
      return
         JH_knowledge_strengthen_swt
         (
            k,
            sequence_id,
            sequence[index],
            sequence[index + 1],
            io
         );
   }
}

/******************************************************************************/
/** LEARN PRECEDING SEQUENCE **************************************************/
/******************************************************************************/
static void parse_tws_sequence
(
   const JH_index sequence [const restrict static 1],
   const size_t index,
   const size_t sequence_length,
   JH_index buffer [const restrict static 1],
   const JH_index buffer_length
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
   struct JH_knowledge k [const restrict static 1],
   const JH_index sequence [const restrict static 1],
   const size_t index,
   const size_t sequence_length,
   const JH_index markov_order,
   JH_index buffer [const restrict static 1],
   const JH_index buffer_length,
   FILE io [const restrict static 1]
)
{
   JH_index sequence_id;

   parse_tws_sequence(sequence, index, sequence_length, buffer, buffer_length);

   if
   (
      JH_knowledge_learn_markov_sequence
      (
         k,
         buffer,
         (buffer_length + 1),
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
         JH_knowledge_strengthen_tws
         (
            k,
            JH_START_OF_SEQUENCE_ID,
            sequence[index],
            sequence_id,
            io
         );
   }
   else
   {
      return
         JH_knowledge_strengthen_tws
         (
            k,
            sequence[index - 1],
            sequence[index],
            sequence_id,
            io
         );
   }
}

/******************************************************************************/
/** EXPORTED ******************************************************************/
/******************************************************************************/
int JH_knowledge_learn_sequence
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index sequence [const restrict static 1],
   const size_t sequence_length,
   const JH_index markov_order,
   FILE io [const restrict static 1]
)
{
   JH_index * buffer;
   size_t i;
   const JH_index buffer_length = (markov_order - 1);

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
      if
      (
         add_swt_sequence
         (
            k,
            sequence,
            i,
            sequence_length,
            markov_order,
            buffer,
            buffer_length,
            io
         ) < 0
      )
      {
         return -1;
      }

      /* TODO: handle failure. */
      if
      (
         add_tws_sequence
         (
            k,
            sequence,
            i,
            sequence_length,
            markov_order,
            buffer,
            buffer_length,
            io
         ) < 0
      )
      {
         return -1;
      }

      JH_knowledge_writelock_word(k, sequence[i], io);

      k->words[sequence[i]].occurrences += 1;

      JH_knowledge_writeunlock_word(k, sequence[i], io);
   }

   return 0;
}
