#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../error/error.h"

#include "knowledge.h"

/** Basic functions of the JH_knowledge structure ****************************/

/* See: "knowledge.h" */
int JH_knowledge_initialize (struct JH_knowledge k [const restrict static 1])
{
   int error;
   JH_index reserved_word_id;

   k->words = (struct JH_knowledge_word *) NULL;
   k->words_length = 0;
   k->words_sorted = (JH_index *) NULL;

   k->sequences = (JH_index **) NULL;
   k->sequences_length = 0;
   k->sequences_sorted = (JH_index *) NULL;

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
         stderr,
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
         stderr,
         "Unable to initialize knowledge's sequences lock: %s.",
         strerror(error)
      );

      return -1;
   }

   if
   (
      (
         JH_knowledge_learn_word
         (
            k,
            "[SoS]",
            5,
            &reserved_word_id,
            stderr
         ) < 0
      )
      ||
      (
         JH_knowledge_learn_word
         (
            k,
            "[EoS]",
            5,
            &reserved_word_id,
            stderr
         ) < 0
      )
   )
   {
      JH_S_FATAL(stderr, "Unable to learn reserved words.");

      return -1;
   }

   return 0;
}

void JH_knowledge_get_word
(
   struct JH_knowledge k [const static 1],
   const JH_index word_ref,
   const JH_char * word [const restrict static 1],
   JH_index word_length [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_knowledge_readlock_words(k, io);

   *word = k->words[word_ref].word;
   *word_length = k->words[word_ref].word_length;

   JH_knowledge_readunlock_words(k, io);
}

int JH_knowledge_rarest_word
(
   struct JH_knowledge k [const static 1],
   const JH_index sequence [const restrict static 1],
   const size_t sequence_length,
   JH_index word_id [const restrict static 1],
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
      JH_knowledge_readlock_word(k, sequence[i], io);
      if
      (
         (k->words[sequence[i]].occurrences <= current_max_score)
         /* Otherwise we might just have learned it, or it must not be used. */
         && (k->words[sequence[i]].occurrences > 1)
      )
      {
         current_max_score = k->words[sequence[i]].occurrences;
         *word_id = sequence[i];
         success = 0;
      }

      JH_knowledge_readunlock_word(k, sequence[i], io);
   }

   return success;
}
