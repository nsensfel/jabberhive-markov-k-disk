#include <stdlib.h>

#include "knowledge.h"

void JH_knowledge_finalize_sequence_target
(
   const struct JH_knowledge_target target [const restrict static 1]
)
{
   (void) target;
}

void JH_knowledge_finalize_adjacent_sequence
(
   const struct JH_knowledge_adjacent_sequence as [const restrict static 1]
)
{
   (void) as;
}

/*
void JH_knowledge_finalize_sequence_collection
(
   const struct JH_knowledge_sequence_collection sc [const restrict static 1]
)
{
   if (sc->sequences_ref_sorted != (JH_index *) NULL)
   {
      free((void *) sc->sequences_ref_sorted);

      sc->sequences_ref_sorted = (JH_index *) NULL;
   }
}
*/

void JH_knowledge_finalize_sequence
(
   JH_index * sequence [const restrict static 1]
)
{
   if (*sequence != (JH_index *) NULL)
   {
      free((void *) *sequence);

      *sequence = (JH_index *) NULL;
   }
}

void JH_knowledge_finalize_word
(
   struct JH_knowledge_word word [const restrict static 1]
)
{
   if (word->word != (char *) NULL)
   {
      free((void *) word->word);

      word->word = (char *) NULL;
   }
}

/* See: "knowledge.h" */
void JH_knowledge_finalize (struct JH_knowledge k [const restrict static 1])
{
   JH_index i;

   if (k->word_locks != (pthread_rwlock_t *) NULL)
   {
      for (i = 0; i < k->words_length; ++i)
      {
         pthread_rwlock_destroy(k->word_locks + i);
      }

      free((void *) k->word_locks);
   }

   k->words_length = 0;

   if (k->words_sorted != (JH_index *) NULL)
   {
      free((void *) k->words_sorted);

      k->words_sorted = (JH_index *) NULL;
   }

   k->sequences_length = 0;

   if (k->sequences_sorted != (JH_index *) NULL)
   {
      free((void *) k->sequences_sorted);

      k->sequences_sorted = (JH_index *) NULL;
   }

   pthread_rwlock_destroy(&(k->words_lock));
   pthread_rwlock_destroy(&(k->sequences_lock));
}
