#include <stdlib.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../error/error.h"

#include "knowledge.h"

/******************************************************************************/
/** INITIALIZING STRUCTURES ***************************************************/
/******************************************************************************/

static void initialize_sequence_collection
(
   struct JH_knowledge_sequence_collection c [const restrict static 1]
)
{
   c->sequences_ref = (struct JH_knowledge_sequence_data *) NULL;
   c->sequences_ref_length = 0;
   c->sequences_ref_sorted = (JH_index *) NULL;
}

static void initialize_word
(
   struct JH_knowledge_word w [const restrict static 1]
)
{
   w->word = (const JH_char *) NULL;
   w->word_length = 0;
   w->occurrences = 0;

   initialize_sequence_collection(&(w->swt));
   initialize_sequence_collection(&(w->tws));
}

/******************************************************************************/
/** ALLOCATING MEMORY *********************************************************/
/******************************************************************************/
static JH_char * copy_word
(
   const JH_char original [const restrict static 1],
   const JH_index original_length,
   FILE io [const restrict static 1]
)
{
   JH_char * result;

   result =
      (JH_char *)
      calloc
      (
         original_length,
         sizeof(JH_char)
      );

   if (result == (JH_char *) NULL)
   {
      JH_S_ERROR(io, "Unable to allocate memory to store new word.");

      return (JH_char *) NULL;
   }

   memcpy
   (
      (void *) result,
      (const void *) original,
      (((size_t) original_length) * sizeof(JH_char))
   );

   return result;
}

static int reallocate_words_list
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   struct JH_knowledge_word * new_words;

   if
   (
      (SIZE_MAX / sizeof(struct JH_knowledge_word))
      < (size_t) k->words_length
   )
   {
      JH_S_ERROR
      (
         io,
         "Unable to store the size of the words list, as it would overflow "
         "size_t variables."
      );

      return -1;
   }

   new_words =
      (struct JH_knowledge_word *) realloc
      (
         (void *) k->words,
         (((size_t) k->words_length) * sizeof(struct JH_knowledge_word))
      );

   if (new_words == (struct JH_knowledge_word *) NULL)
   {
      JH_S_ERROR
      (
         io,
         "Unable to allocate the memory required for the new words list."
      );

      return -1;
   }

   k->words = new_words;

   return 0;
}

static int reallocate_words_sorted_list
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_index * new_words_sorted;

   /*
    * This has already been tested previously for a struct JH_knowledge_word,
    * whose size is bigger than a JH_index.
    * */
   /*
   if ((SIZE_MAX / sizeof(JH_index)) < k->words_length)
   {
      JH_S_ERROR
      (
         "Unable to store the size of the sorted words list, as it would "
         "overflow size_t variables."
      );

      return -1;
   }
   */

   new_words_sorted =
      (JH_index *) realloc
      (
         (void *) k->words_sorted,
         (((size_t) k->words_length) * sizeof(JH_index))
      );

   if (new_words_sorted == (JH_index *) NULL)
   {
      JH_S_ERROR
      (
         io,
         "Unable to allocate the memory required for the new sorted words list."
      );

      return -1;
   }

   k->words_sorted = new_words_sorted;

   return 0;
}

static void set_nth_word
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index sorted_word_id,
   const JH_index word_id
)
{
   /* Safe: (> k->words_length 1) */
   if (sorted_word_id < (k->words_length - 1))
   {
      memmove
      (
         /* Safe: (=< (+ sorted_word_id 1) k->words_length) */
         (void *) (k->words_sorted + (sorted_word_id + 1)),
         (const void *) (k->words_sorted + sorted_word_id),
         (
            ((size_t) ((k->words_length - 1) - sorted_word_id))
            * sizeof(JH_index)
         )
      );
   }

   k->words_sorted[sorted_word_id] = word_id;
}

static int add_word
(
   struct JH_knowledge k [const restrict static 1],
   const JH_char word [const restrict static 1],
   const JH_index word_length,
   const JH_index word_id,
   const JH_index sorted_word_id,
   FILE io [const restrict static 1]
)
{
   JH_char * stored_word;

   if (k->words_length == JH_INDEX_MAX)
   {
      JH_S_ERROR
      (
         io,
         "Unable to add word: the variable that stores the number of known "
         "words would overflow."
      );

      return -1;
   }

   stored_word = copy_word(word, word_length, io);

   if (stored_word == (JH_char *) NULL)
   {
      return -1;
   }

   k->words_length += 1;

   if (reallocate_words_list(k, io) < 0)
   {
      k->words_length -= 1;

      return -1;
   }

   initialize_word(k->words + word_id);

   k->words[word_id].word = stored_word;
   k->words[word_id].word_length = word_length;

   if (reallocate_words_sorted_list(k, io) < 0)
   {
      k->words_length -= 1;

      return -1;
   }

   set_nth_word(k, sorted_word_id, word_id);

   return 0;
}

/******************************************************************************/
/** EXPORTED ******************************************************************/
/******************************************************************************/

int JH_knowledge_learn_word
(
   struct JH_knowledge k [const restrict static 1],
   const JH_char word [const restrict static 1],
   const size_t word_length,
   JH_index word_id [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_index sorted_id;

   if (word_length >= (size_t) JH_INDEX_MAX)
   {
      JH_S_ERROR(io, "Word is too long to be learned.");

      return -1;
   }

   if
   (
      JH_knowledge_find_word_id
      (
         k,
         word,
         (((size_t) word_length) * sizeof(JH_char)),
         word_id
      ) == 0
   )
   {
      JH_DEBUG
      (
         io,
         JH_DEBUG_KNOWLEDGE_LEARN_WORD,
         "Word of size %u is already known (id: %u).",
         (JH_index) word_length,
         *word_id
      );

      return 0;
   }

   sorted_id = *word_id;
   *word_id = k->words_length;

   JH_DEBUG
   (
      io,
      JH_DEBUG_KNOWLEDGE_LEARN_WORD,
      "Learning new word of size %u (id: %u, sorted_id: %u).",
      (JH_index) word_length,
      *word_id,
      sorted_id
   );

   return add_word(k, word, (JH_index) word_length, *word_id, sorted_id, io);
}
