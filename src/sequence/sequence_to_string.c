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
/** MEMORY ALLOCATION *********************************************************/
/******************************************************************************/
static int ensure_string_capacity
(
   JH_char * string [const restrict static 1],
   size_t string_capacity [const restrict static 1],
   const size_t string_required_capacity,
   FILE io [const restrict static 1]
)
{
   JH_char * new_string;

   if (string_required_capacity <= *string_capacity)
   {
      return 0;
   }

   new_string =
      (JH_char *) realloc
      (
         (void *) *string,
         ((size_t) string_required_capacity) * sizeof(JH_char)
      );

   if (new_string== (JH_char *) NULL)
   {
      JH_S_ERROR
      (
         io,
         "Unable to reallocate memory to match string's required size."
      );

      return -1;
   }

   *string_capacity = string_required_capacity;
   *string = new_string;

   return 1;
}

/******************************************************************************/
/** ADD WORD ******************************************************************/
/******************************************************************************/
static int increment_required_capacity
(
   size_t current_capacity [const restrict static 1],
   const size_t increase_factor,
   FILE io [const restrict static 1]
)
{
   if ((JH_INDEX_MAX - increase_factor) < *current_capacity)
   {
      JH_S_ERROR
      (
         io,
         "String capacity increment aborted, as the new capacity would not "
         "fit in a JH_index variable."
      );

      return -1;
   }

   *current_capacity += increase_factor;

   if ((SIZE_MAX / sizeof(JH_char)) < *current_capacity)
   {
      *current_capacity -= increase_factor;

      JH_S_ERROR
      (
         io,
         "String capacity increment aborted, as the new size would not fit "
         "in a size_t variable."
      );

      return -2;
   }

   return 0;
}

static int add_word
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   struct JH_knowledge k [const restrict static 1],
   JH_char * destination [const restrict static 1],
   size_t destination_capacity [const restrict static 1],
   size_t destination_length [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_char * word;
   JH_index word_size;
   size_t insertion_point;

   if (word_id < JH_RESERVED_IDS_COUNT)
   {
      return 0;
   }

   if (JH_knowledge_get_word(params, k, word_id, &word, &word_size, io) < 0)
   {
      return -1;
   }

   insertion_point = *destination_length;

   /* word_size includes '\n', which will be replaced by a space. */
   /* (word_size == JH_INDEX_MAX) ==> could not have learned word. */
   if (increment_required_capacity(destination_length, (word_size + 1), io) < 0)
   {
      free((void *) word);

      return -1;
   }

   if
   (
      ensure_string_capacity
      (
         destination,
         destination_capacity,
         *destination_length,
         io
      ) < 0
   )
   {
      free((void *) word);

      return -2;
   }

   memcpy
   (
      (*destination + insertion_point),
      (const void *) word,
      word_size
   );

   free((void *) word);

   (*destination)[*destination_length - 1] = ' ';

   return 0;
}

/******************************************************************************/
/** EXPORTED ******************************************************************/
/******************************************************************************/
int JH_sequence_to_undercase_string
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index sequence [const restrict static 1],
   const size_t sequence_length,
   struct JH_knowledge k [const restrict static 1],
   JH_char * destination [const restrict static 1],
   size_t destination_capacity [const restrict static 1],
   size_t destination_length [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   size_t i;

   *destination_length = 0;

   for (i = 0; i < sequence_length; ++i)
   {
      if
      (
         add_word
         (
            params,
            sequence[i],
            k,
            destination,
            destination_capacity,
            destination_length,
            io
         ) < 0
      )
      {
         *destination_length = 0;

         return -1;
      }
   }

   return 0;
}
