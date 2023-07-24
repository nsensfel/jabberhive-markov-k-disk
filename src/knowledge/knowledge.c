#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../error/error.h"

#include "../io/io.h"

#include "knowledge.h"

/** Basic functions of the JH_knowledge structure ****************************/

/**
 * Creates the minimal database needed to run.
 * This includes the sorted words and sequences files, as well as the reserved
 * start-of-sentence and end-of-sentence words.
 *
 * Returns 0 on success, negative values on error.
 **/
static int initialize_without_database
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   // Needed argument for `JH_knowledge_learn_word`. Not actually used.
   JH_index reserved_word_id;

   if (JH_io_initialize_database(params, io) < 0)
   {
      return -1;
   }

   if
   (
      (
         JH_knowledge_learn_word
         (
            params,
            k,
            /* word_length = */ 5,
            "[SoS]",
            &reserved_word_id,
            io
         ) < 0
      )
      ||
      (
         JH_knowledge_learn_word
         (
            params,
            k,
            /* word_length = */ 5,
            "[EoS]",
            &reserved_word_id,
            io
         ) < 0
      )
   )
   {
      // This is a less than ideal situation: the database folder is incomplete,
      // yet likely to pass the initialization test.
      // TODO: should we delete the database folder here and output a warning
      //       if we fail to do so?
      JH_S_FATAL(io, "Unable to learn reserved words.");

      return -2;
   }

   return 0;
}

/**
 * Reads data from an existing database, so that the `k` structure retrieves the
 * sorted words and sequences files' data, which is all that's needed to re-use
 * the database.
 * The locks for each word are also re-created. Their state is not stored in the
 * database, but any thread that may have acquired them is no longer running, so
 * it's fine (the database cannot be used by multiple servers at once).
 *
 * Returns 0 on success, negative values on error.
 **/
static int initialize_with_database
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_index i;

   if
   (
      JH_io_read_sorted_words
      (
         k->words_sorted_filename,
         &(k->words_length),
         &(k->words_sorted),
         io
      )
      < 0
   )
   {
      return -1;
   }

   if
   (
      JH_io_read_sorted_sequences
      (
         k->sequences_sorted_filename,
         &(k->sequences_length),
         &(k->sequences_sorted),
         io
      )
      < 0
   )
   {
      free((void *) k->sequences_sorted);

      return -1;
   }

   k->word_locks =
      (pthread_rwlock_t *) calloc
      (
         (size_t) k->words_length,
         sizeof(pthread_rwlock_t)
      );

   if (k->word_locks == (pthread_rwlock_t *) NULL)
   {
      JH_S_ERROR
      (
         io,
         "Unable to allocate the memory required for the word locks list."
      );

      free((void *) k->sequences_sorted);
      free((void *) k->words_sorted);

      return -2;
   }

   for (i = 0; i < k->words_length; ++i)
   {
      int error;

      error =
         pthread_rwlock_init
         (
            (k->word_locks + i),
            (const pthread_rwlockattr_t *) NULL
         );

      if (error != 0)
      {
         JH_FATAL
         (
            io,
            "Unable to initialize word lock: %s.",
            strerror(error)
         );

         while (i > 0)
         {
            i--;

            pthread_rwlock_destroy(k->word_locks + i);
         }

         free((void *) k->sequences_sorted);
         free((void *) k->words_sorted);
         free((void *) k->word_locks);

         return -3;
      }
   }

   return 0;
}

/* See: "knowledge.h" */
int JH_knowledge_initialize
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   int error;

   k->words_length = 0;
   k->words_sorted = (JH_index *) NULL;
   k->word_locks = (pthread_rwlock_t *) NULL;

   if
   (
      JH_io_generate_sorted_words_filename
      (
         params,
         &(k->words_sorted_filename),
         io
      )
      < 0
   )
   {
      return -1;
   }

   k->sequences_length = 0;
   k->sequences_sorted = (JH_index *) NULL;

   if
   (
      JH_io_generate_sorted_sequences_filename
      (
         params,
         &(k->sequences_sorted_filename),
         io
      )
      < 0
   )
   {
      free((void *) k->words_sorted_filename);

      return -1;
   }

#ifndef JH_RUNNING_FRAMA_C
   error =
      pthread_rwlock_init
      (
         &(k->words_lock),
         (const pthread_rwlockattr_t *) NULL
      );
#else
   error = 0;
#endif

   if (error != 0)
   {
      JH_FATAL
      (
         io,
         "Unable to initialize knowledge's words lock: %s.",
         strerror(error)
      );

      return -1;
   }

#ifndef JH_RUNNING_FRAMA_C
   error =
      pthread_rwlock_init
      (
         &(k->sequences_lock),
         (const pthread_rwlockattr_t *) NULL
      );
#else
   error = 0;
#endif

   if (error != 0)
   {
      JH_FATAL
      (
         io,
         "Unable to initialize knowledge's sequences lock: %s.",
         strerror(error)
      );

      return -1;
   }

   if (JH_io_database_exists(k))
   {
      error = initialize_with_database(k, io);
   }
   else
   {
      error = initialize_without_database(params, k, io);
   }

   if (error < 0)
   {
      free((void *) k->words_sorted_filename);
      free((void *) k->sequences_sorted_filename);

      return -1;
   }

   return 0;
}

/* See: "knowledge.h" */
int JH_knowledge_get_word
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const JH_index word_id,
   JH_char * word [const restrict static 1],
   JH_index word_length [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   struct JH_knowledge_word target;

   JH_knowledge_readlock_word(k, word_id, io);

   if (JH_io_read_word_from_id(params, word_id, &target, io) < 0)
   {
      JH_knowledge_readunlock_word(k, word_id, io);

      JH_ERROR(io, "Could not get word %u.", word_id);

      return -1;
   }

   JH_knowledge_readunlock_word(k, word_id, io);

   // +1 to account for '\0'
   *word = calloc((target.word_length + 1), sizeof(char));

   if (*word == (char *) NULL)
   {
      JH_ERROR(io, "Could allocate memory to copy word %u.", word_id);
      JH_knowledge_finalize_word(&target);

      *word_length = 0;

      return -2;
   }

   memcpy(*word, target.word, sizeof(char) * (target.word_length + 1));

   (*word)[target.word_length] = '\0';

   *word_length = target.word_length;

   JH_knowledge_finalize_word(&target);

   return 0;
}

/* See: "knowledge.h" */
int JH_knowledge_rarest_word
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const size_t sequence_length,
   const JH_index sequence [const restrict static sequence_length],
   JH_index rarest_word_id [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_index current_max_score;
   size_t i;
   int success;

   current_max_score = JH_INDEX_MAX;

   success = -1;

   for (i = 0; i < sequence_length; ++i)
   {
      struct JH_knowledge_word candidate;

      JH_knowledge_readlock_word(k, sequence[i], io);

      if (JH_io_read_word_from_id(params, sequence[i], &candidate, io) < 0)
      {
         JH_knowledge_readunlock_word(k, sequence[i], io);

         JH_ERROR(io, "Could not get word %u", sequence[i]);

         return -2;
      }

      JH_knowledge_readunlock_word(k, sequence[i], io);

      if
      (
         (candidate.occurrences <= current_max_score)
         /* Otherwise we might just have learned it, or it must not be used. */
         && (candidate.occurrences > 1)
      )
      {
         current_max_score = candidate.occurrences;
         *rarest_word_id = sequence[i];
         success = 0;
      }

      JH_knowledge_finalize_word(&candidate);
   }

   return success;
}

char * JH_knowledge_get_sorted_sequences_filename
(
   const struct JH_knowledge k [const restrict static 1]
)
{
   return k->sequences_sorted_filename;
}

char * JH_knowledge_get_sorted_words_filename
(
   const struct JH_knowledge k [const restrict static 1]
)
{
   return k->words_sorted_filename;
}
