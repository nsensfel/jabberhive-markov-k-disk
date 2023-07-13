#define _POSIX_C_SOURCE 200809L
#include <stdlib.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../core/char.h"
#include "../core/index.h"

#include "../error/error.h"

#include "../knowledge/knowledge.h"

#include "sequence.h"

/******************************************************************************/
/** HANDLING WORDS ************************************************************/
/******************************************************************************/

static int add_word_to_sequence
(
   const struct JH_parameters params [const restrict static 1],
   const JH_char string [const restrict static 1],
   const size_t word_start,
   const size_t word_length,
   JH_index * sequence [const restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_index word_id;

   if
   (
      JH_knowledge_learn_word
      (
         params,
         k,
         (string + word_start),
         word_length,
         &word_id,
         io
      ) < 0
   )
   {
      return -1;
   }

   if
   (
      JH_sequence_append_right
      (
         sequence,
         word_id,
         sequence_capacity,
         sequence_length,
         io
      ) < 0
   )
   {
      return -1;
   }

   return 0;
}

static int find_word
(
   const JH_char string [const restrict static 1],
   const size_t string_length,
   const size_t offset,
   size_t word_start [const restrict static 1],
   size_t word_length [const restrict static 1]
)
{
   size_t i;

   i = offset;

   while ((string[i] == ' ') && (i < string_length))
   {
      i += 1;
   }

   if (i >= string_length)
   {
      return -1;
   }

   *word_start = i;

   while ((string[i] != ' ') && (i < string_length))
   {
      i += 1;
   }

   *word_length = (i - *word_start);

   return 0;
}

/******************************************************************************/
/** EXPORTED ******************************************************************/
/******************************************************************************/

/* See: "sequence.h" */
int JH_sequence_from_undercase_string
(
   const struct JH_parameters params [const restrict static 1],
   const JH_char string [const restrict],
   const size_t string_length,
   struct JH_knowledge k [const restrict static 1],
   JH_index * sequence [const restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   size_t word_start, word_length;
   size_t i;

   i = 0;

   *sequence_length = 0;

   JH_DEBUG
   (
      io,
      JH_DEBUG_SEQUENCE_FROM_STRING,
      "Converting string of size %lu to sequence.",
      string_length
   );

   if
   (
      JH_sequence_append_right
      (
         sequence,
         JH_START_OF_SEQUENCE_ID,
         sequence_capacity,
         sequence_length,
         io
      ) < 0
   )
   {
      *sequence_length = 0;

      return -1;
   }

   JH_S_DEBUG
   (
      io,
      JH_DEBUG_SEQUENCE_FROM_STRING,
      "[SOS] added to sequence."
   );

   while (i < string_length)
   {
      if (find_word(string, string_length, i, &word_start, &word_length) < 0)
      {
         break;
      }

      JH_DEBUG
      (
         io,
         JH_DEBUG_SEQUENCE_FROM_STRING,
         "Word of size %lu found in string at index %lu.",
         word_length,
         word_start
      );

      if
      (
         add_word_to_sequence
         (
            params,
            string,
            word_start,
            word_length,
            sequence,
            sequence_capacity,
            sequence_length,
            k,
            io
         ) < 0
      )
      {
         *sequence_length = 0;

         return -1;
      }

      i = (word_start + word_length);
   }

   if
   (
      JH_sequence_append_right
      (
         sequence,
         JH_END_OF_SEQUENCE_ID,
         sequence_capacity,
         sequence_length,
         io
      ) < 0
   )
   {
      *sequence_length = 0;

      return -1;
   }

   return 0;
}
