#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../error/error.h"

#include "knowledge.h"

/** WORDS *********************************************************************/
/**** LOCK ********************************************************************/
int JH_knowledge_readlock_words
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   int err;

   err = pthread_rwlock_rdlock(&(k->words_lock));

   if (err != 0)
   {
      JH_ERROR
      (
         io,
         "Unable to gain read access to knowledge's words: %s",
         strerror(err)
      );

      return -1;
   }

   return 0;
}

int JH_knowledge_writelock_words
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   int err;

   err = pthread_rwlock_wrlock(&(k->words_lock));

   if (err != 0)
   {
      JH_ERROR
      (
         io,
         "Unable to gain write access to knowledge's words: %s",
         strerror(err)
      );

      return -1;
   }

   return 0;
}

/**** UNLOCK ******************************************************************/
int JH_knowledge_readunlock_words
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   int err;

   err = pthread_rwlock_unlock(&(k->words_lock));

   if (err != 0)
   {
      JH_ERROR
      (
         io,
         "Unable to release read access to knowledge's words: %s",
         strerror(err)
      );

      return -1;
   }

   return 0;
}

int JH_knowledge_writeunlock_words
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   int err;

   err = pthread_rwlock_unlock(&(k->words_lock));

   if (err != 0)
   {
      JH_ERROR
      (
         io,
         "Unable to release write access to knowledge's words: %s",
         strerror(err)
      );

      return -1;
   }

   return 0;
}

/** SEQUENCES *****************************************************************/
/**** LOCK ********************************************************************/
int JH_knowledge_readlock_sequences
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   int err;

   err = pthread_rwlock_rdlock(&(k->sequences_lock));

   if (err != 0)
   {
      JH_ERROR
      (
         io,
         "Unable to gain read access to knowledge's sequences: %s",
         strerror(err)
      );

      return -1;
   }

   return 0;
}

int JH_knowledge_writelock_sequences
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   int err;

   err = pthread_rwlock_wrlock(&(k->sequences_lock));

   if (err != 0)
   {
      JH_ERROR
      (
         io,
         "Unable to gain write access to knowledge's sequences: %s",
         strerror(err)
      );

      return -1;
   }

   return 0;
}

/**** UNLOCK ******************************************************************/
int JH_knowledge_readunlock_sequences
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   int err;

   err = pthread_rwlock_unlock(&(k->sequences_lock));

   if (err != 0)
   {
      JH_ERROR
      (
         io,
         "Unable to release read access to knowledge's sequences: %s",
         strerror(err)
      );

      return -1;
   }

   return 0;
}

int JH_knowledge_writeunlock_sequences
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   int err;

   err = pthread_rwlock_unlock(&(k->sequences_lock));

   if (err != 0)
   {
      JH_ERROR
      (
         io,
         "Unable to release write access to knowledge's sequences: %s",
         strerror(err)
      );

      return -1;
   }

   return 0;
}

/** WORD **********************************************************************/
/**** LOCK ********************************************************************/
int JH_knowledge_readlock_word
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index i,
   FILE io [const restrict static 1]
)
{
   int err;

   if (JH_knowledge_readlock_words(k, io) < 0)
   {
      return -1;
   }

   err = pthread_rwlock_rdlock(&(k->words[i].lock));

   if (err != 0)
   {
      JH_ERROR
      (
         io,
         "Unable to gain read access to a knowledge's word: %s",
         strerror(err)
      );

      return -1;
   }

   return 0;
}

int JH_knowledge_writelock_word
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index i,
   FILE io [const restrict static 1]
)
{
   int err;

   if (JH_knowledge_readlock_words(k, io) < 0)
   {
      return -1;
   }


   err = pthread_rwlock_wrlock(&(k->words[i].lock));

   if (err != 0)
   {
      JH_ERROR
      (
         io,
         "Unable to gain write access to a knowledge's word: %s",
         strerror(err)
      );

      return -1;
   }

   return 0;
}

/**** UNLOCK ******************************************************************/
int JH_knowledge_readunlock_word
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index i,
   FILE io [const restrict static 1]
)
{
   int err;

   if (JH_knowledge_readunlock_words(k, io) < 0)
   {
      return -1;
   }

   err = pthread_rwlock_unlock(&(k->words[i].lock));

   if (err != 0)
   {
      JH_ERROR
      (
         io,
         "Unable to release read access to a knowledge's word: %s",
         strerror(err)
      );

      return -1;
   }

   return 0;
}

int JH_knowledge_writeunlock_word
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index i,
   FILE io [const restrict static 1]
)
{
   int err;

   if (JH_knowledge_readunlock_words(k, io) < 0)
   {
      return -1;
   }

   err = pthread_rwlock_unlock(&(k->words[i].lock));

   if (err != 0)
   {
      JH_ERROR
      (
         io,
         "Unable to release write access to a knowledge's word: %s",
         strerror(err)
      );

      return -1;
   }

   return 0;
}
