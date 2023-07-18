#include <stdlib.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../core/index.h"

#include "../error/error.h"

#include "../io/io.h"

#include "../parameters/parameters.h"

#include "knowledge.h"

/******************************************************************************/
/** INITIALIZING STRUCTURES ***************************************************/
/******************************************************************************/
static int initialize_word
(
   struct JH_knowledge_word w [const restrict static 1]
)
{
   w->word = (JH_char *) NULL;
   w->word_length = 0;
   w->occurrences = 0;
   w->swt_sequences_ref_length = 0;
   w->tws_sequences_ref_length = 0;

   return 0;
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

static int reallocate_word_locks_list
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   pthread_rwlock_t * new_word_locks;

   if
   (
      JH_index_cannot_allocate_more
      (
         sizeof(pthread_rwlock_t),
         k->words_length
      )
   )
   {
      JH_S_ERROR
      (
         io,
         "Unable to store the size of the word locks list, as it would "
         "overflow size_t variables."
      );

      return -1;
   }

   new_word_locks =
      (pthread_rwlock_t *) realloc
      (
         (void *) k->word_locks,
         (((size_t) k->words_length) * sizeof(pthread_rwlock_t))
      );

   if (new_word_locks == (pthread_rwlock_t *) NULL)
   {
      JH_S_ERROR
      (
         io,
         "Unable to allocate the memory required for the new word locks list."
      );

      return -1;
   }

   k->word_locks = new_word_locks;

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
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const JH_char word [const restrict static 1],
   const JH_index word_length,
   const JH_index word_id,
   const JH_index sorted_word_id,
   FILE io [const restrict static 1]
)
{
   int error;
   struct JH_knowledge_word new_word;
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
      JH_S_DEBUG
      (
         io,
         JH_DEBUG_KNOWLEDGE_LEARN_WORD,
         "New word failed to be copied."
      );

      return -1;
   }

   k->words_length += 1;

   if (reallocate_word_locks_list(k, io) < 0)
   {
      k->words_length -= 1;

      free((void *) stored_word);

      return -1;
   }

   initialize_word(&new_word);

   new_word.word = stored_word;
   new_word.word_length = word_length;

   if (JH_io_generate_word_directory_from_id(params, word_id, io) < 0)
   {
      JH_knowledge_finalize_word(&new_word);
      k->words_length -= 1;

      return -1;
   }

   JH_DEBUG
   (
      io,
      JH_DEBUG_KNOWLEDGE_LEARN_WORD,
      "New word (%u) directory created.",
      word_id
   );

   if (JH_io_write_word_from_id(params, word_id, &new_word, io) < 0)
   {
      JH_knowledge_finalize_word(&new_word);
      k->words_length -= 1;

      return -1;
   }

   JH_DEBUG
   (
      io,
      JH_DEBUG_KNOWLEDGE_LEARN_WORD,
      "New word (%u) file written.",
      word_id
   );

   JH_knowledge_finalize_word(&new_word);

   if (reallocate_words_sorted_list(k, io) < 0)
   {
      k->words_length -= 1;

      return -1;
   }

   set_nth_word(k, sorted_word_id, word_id);

   JH_io_write_sorted_words
   (
      k->words_sorted_filename,
      k->words_length,
      k->words_sorted,
      io
   );

   error =
      pthread_rwlock_init
      (
         (k->word_locks + word_id),
         (const pthread_rwlockattr_t *) NULL
      );

   if (error != 0)
   {
      JH_ERROR
      (
         io,
         "Unable to initialize knowledge's word %u lock: %s.",
         word_id,
         strerror(error)
      );

      return -1;
   }

   return 0;
}

/******************************************************************************/
/** EXPORTED ******************************************************************/
/******************************************************************************/

int JH_knowledge_learn_word
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const JH_char word [const restrict static 1],
   const size_t word_length,
   JH_index word_id [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   int i;
   JH_index sorted_ix;

   if (word_length >= (size_t) JH_INDEX_MAX)
   {
      JH_S_ERROR(io, "Word is too long to be learned.");

      return -1;
   }
   else if (word_length == 0)
   {
      JH_S_ERROR(io, "Word is empty.");

      return -2;
   }

   JH_knowledge_readlock_words(k, io);

   i =
      JH_knowledge_find_word
      (
         params,
         k,
         word,
         (((size_t) word_length) * sizeof(JH_char)),
         word_id,
         &sorted_ix,
         io
      );

   /*
    * We may need to write, but we currently have reading access.
    * We can't get the writing access while someone (even us) has the reading
    * access, so we release the reading access in any case.
    */
   JH_knowledge_readunlock_words(k, io);

   if (i < 0)
   {
      return -1;
   }

   if (i == 1)
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

   JH_knowledge_writelock_words(k, io);
   /*
    * Now we have writer access, but someone else might have modified 'k' before
    * we did, so we need to find the word's location again.
    */
   i =
      JH_knowledge_lazy_find_word
      (
         params,
         k,
         word,
         (((size_t) word_length) * sizeof(JH_char)),
         word_id,
         &sorted_ix,
         io
      );

   if (i < 0)
   {
      JH_knowledge_writeunlock_words(k, io);

      return -1;
   }

   if (i == 1)
   {
      JH_knowledge_writeunlock_words(k, io);

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

   *word_id = k->words_length;

   JH_DEBUG
   (
      io,
      JH_DEBUG_KNOWLEDGE_LEARN_WORD,
      "Learning new word of size %u (id: %u, sorted_ix: %u).",
      (JH_index) word_length,
      *word_id,
      sorted_ix
   );

   if
   (
      add_word
      (
         params,
         k,
         word,
         (JH_index) word_length,
         *word_id,
         sorted_ix,
         io
      )
      < 0
   )
   {
      JH_knowledge_writeunlock_words(k, io);

      return -1;
   }
   else
   {
      JH_knowledge_writeunlock_words(k, io);

      return 0;
   }
}
