#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h> /* defines SIZE_MAX */

#include "../core/index.h"

#include "../error/error.h"

#include "../knowledge/knowledge.h"

#include "sequence.h"


/******************************************************************************/
/** ADDING ELEMENTS TO THE LEFT ***********************************************/
/******************************************************************************/

/*
 * Adds an id to the left of the sequence, according to what is known as likely
 * to fit there.
 * This requires the reallocation of {sequence}. The freeing of the previous
 * memory space is handled. If an error happened, {*sequence} remains untouched.
 * Semaphore:
 *    Takes then releases access for {k}.
 * Returns:
 *    0 on success.
 *    -1 iff nothing fitting was found.
 *    -2 iff the addition of that id failed.
 * Pre:
 *    (initialized {sequence})
 *    (initialized {k})
 *    (> {markov_order} 1)
 *    (initialized {*sequence[0..({markov_order} - 1)]})
 */
static int extend_left
(
   JH_index * sequence [const restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   const JH_index markov_order,
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_index sequence_id, word_id;

   /* preceding_words_weights_sum > 0 */

   JH_knowledge_readlock_sequences(k, io);

   if
   (
      JH_knowledge_find_sequence
      (
         k,
         ((*sequence) + 1),
         markov_order,
         &sequence_id
      ) < 0
   )
   {
      JH_knowledge_readunlock_sequences(k, io);

      JH_S_ERROR(io, "Could not find matching TWS sequence.");

      return -1;
   }

   JH_knowledge_readunlock_sequences(k, io);

   if
   (
      JH_knowledge_random_tws_target
      (
         k,
         &word_id,
         (*sequence)[0],
         sequence_id,
         io
      ) < 0
   )
   {
      JH_S_ERROR(io, "Could not find matching TWS target.");

      return -1;
   }

   if
   (
      JH_sequence_append_left
      (
         word_id,
         sequence,
         sequence_capacity,
         sequence_length,
         io
      ) < 0
   )
   {
      return -3;
   }

   return 0;
}

/*
 * Continuously adds ids to the left of the sequence, according to what is known
 * as likely to fit there. If {credits} is NULL, it will stop upon reaching
 * the id indicating the start of a sequence, otherwise it will also limit to
 * {*credits} words added (including the one indicating the start of a
 * sequence).
 * This requires the reallocation of {sequence}. The freeing of the previous
 * memory space is handled. If an error happened, {sequence} remains unfreed.
 * Returns:
 *    0 on success.
 *    -1 iff we did not manage to have JH_START_OF_SEQUENCE_ID as a starting
 *       point. This cannot be caused by lack of {*credits}, but rather by a
 *       memory allocation problem or a more important issue in {k}. Indeed, it
 *       could mean we do not know any word preceding {*sequence[0]}, not even
 *       JH_START_OF_SEQUENCE_ID.
 * Pre:
 *    (initialized {sequence})
 *    (initialized {sequence_size})
 *    (initialized {k})
 *    (> {markov_order} 1)
 *    (initialized {*sequence[0..(MARKOV_ORDER - 1)]})
 */
static int complete_left_part_of_sequence
(
   JH_index * sequence [restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   const JH_index markov_order,
   size_t credits [const restrict],
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   for (;;)
   {
      if ((credits == (size_t *) NULL) || (*credits > 0))
      {
         if
         (
            extend_left
            (
               sequence,
               sequence_capacity,
               sequence_length,
               markov_order,
               k,
               io
            ) < 0
         )
         {
            /* We are sure *sequence[0] is defined. */
            if ((*sequence)[0] == JH_START_OF_SEQUENCE_ID)
            {
               /*
                * We failed to add a word, but it was because none should have
                * been added.
                */
               return 0;
            }
            else
            {
               return -1;
            }
         }
      }
      else
      {
         /* No more credits available, the sequence will have to start here. */
         (*sequence)[0] = JH_START_OF_SEQUENCE_ID;

         return 0;
      }

      if (credits != (size_t *) NULL)
      {
         *credits -= 1;
      }

      /* We are sure *sequence[0] is defined. */
      switch ((*sequence)[0])
      {
         case JH_END_OF_SEQUENCE_ID:
            JH_S_WARNING
            (
               io,
               "END OF LINE was added at the left part of an sequence."
            );

            (*sequence)[0] = JH_START_OF_SEQUENCE_ID;
            return 0;

         case JH_START_OF_SEQUENCE_ID:
            return 0;

         default:
            break;
      }
   }
}

/******************************************************************************/
/** ADDING ELEMENTS TO THE RIGHT **********************************************/
/******************************************************************************/


/*
 * Adds an id to the right of the sequence, according to what is known as likely
 * to fit there.
 * This requires the reallocation of {sequence}. The freeing of the previous
 * memory space is handled. If an error happened, {*sequence} remains untouched.
 * Semaphore:
 *    Takes then releases access for {k}.
 * Returns:
 *    0 on success.
 *    -1 iff nothing fitting was found.
 *    -2 iff the addition of that id failed.
 * Pre:
 *    (initialized {sequence})
 *    (initialized {k})
 *    (> {markov_order} 1)
 *    (initialized {*sequence[0..(MARKOV_ORDER - 1)]})
 */
static int extend_right
(
   JH_index * sequence [const restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   const JH_index markov_order,
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_index sequence_id, word_id;

   /* preceding_words_weights_sum > 0 */

   JH_knowledge_readlock_sequences(k, io);

   if
   (
      JH_knowledge_find_sequence
      (
         k,
         ((*sequence) + (*sequence_length - markov_order)),
         markov_order,
         &sequence_id
      ) < 0
   )
   {
      JH_knowledge_readunlock_sequences(k, io);

      JH_S_PROG_ERROR
      (
         io,
         "Knowledge consistency error: generated markov sequence could not be "
         "found."
      );

      return -1;
   }

   JH_knowledge_readunlock_sequences(k, io);

   if
   (
      JH_knowledge_random_swt_target
      (
         k,
         sequence_id,
         (*sequence)[*sequence_length - 1],
         &word_id,
         io
      ) < 0
   )
   {
      JH_S_PROG_ERROR
      (
         io,
         "Knowledge consistency error: generated markov sequence had no known "
         "targets."
      );

      return -1;
   }

   /* following_words_weights_sum > 0 */

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
      return -3;
   }

   return 0;
}

/*
 * Continuously adds ids to the right of the sequence, according to what is
 * known as likely to fit there. If {credits} is NULL, it will stop upon
 * reaching the id indicating the end of a sequence, otherwise it will also
 * limit to {*credits} words added (including the one indicating the end of a
 * sequence).
 * This requires the reallocation of {sequence}. The freeing of the previous
 * memory space is handled. If an error happened, {sequence} remain untouched.
 * Returns:
 *    0 on success.
 *    -1 iff we did not manage to have JH_END_OF_SEQUENCE_ID as a stopping
 *       point. This cannot be caused by lack of {*credits}, but rather by a
 *       memory allocation problem or a more important issue in {k}. Indeed, it
 *       could mean we do not know any word following {*sequence[0]}, not even
 *       JH_END_OF_SEQUENCE_ID.
 * Pre:
 *    (initialized {sequence})
 *    (initialized {*sequence_size})
 *    (initialized {k})
 *    (> {markov_order} 1)
 *    (initialized {*sequence[0..(MARKOV_ORDER - 1)]})
 */
static int complete_right_part_of_sequence
(
   JH_index * sequence [const restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   const JH_index markov_order,
   size_t credits [const restrict],
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   for (;;)
   {
      if ((credits == (size_t *) NULL) || (*credits > 0))
      {
         if
         (
            extend_right
            (
               sequence,
               sequence_capacity,
               sequence_length,
               markov_order,
               k,
               io
            ) < 0
         )
         {
            /* Safe: (> sequence_length 1) */
            if ((*sequence)[(*sequence_length - 1)] == JH_END_OF_SEQUENCE_ID)
            {
               /*
                * We failed to add a word, but it was because none should have
                * been added.
                */
               return 0;
            }
            else
            {
               return -1;
            }
         }
      }
      else
      {
         /* No more credits available, we end the sequence. */
         (*sequence)[((*sequence_length) - 1)] = JH_END_OF_SEQUENCE_ID;

         return 0;
      }

      if (credits != (size_t *) NULL)
      {
         *credits -= 1;
      }

      /* Safe: (> sequence_length 1) */
      switch ((*sequence)[((*sequence_length) - 1)])
      {
         case JH_START_OF_SEQUENCE_ID:
            JH_S_WARNING
            (
               io,
               "END OF LINE was added at the right part of an sequence."
            );

            (*sequence)[((*sequence_length) - 1)] = JH_END_OF_SEQUENCE_ID;
            return 0;

         case JH_END_OF_SEQUENCE_ID:
            return 0;

         default:
            break;
      }
   }
}

/******************************************************************************/
/** INITIALIZING SEQUENCE *****************************************************/
/******************************************************************************/

/*
 * Initializes an pre-allocated sequence by filling it with {initial_word}
 * followed by a sequence of ({markov_order} - 1) words that is known to have
 * followed {initial_word} at least once. This sequence is chosen depending on
 * how often {k} indicates it has followed {initial_word}.
 * Returns:
 *    0 on success.
 *    -1 if no such sequence was found.
 * Pre:
 *    (size (= {sequence} {markov_order}))
 *    (initialized {k})
 *    (> markov_order 1)
 * Post:
 *    (initialized {sequence[0..(markov_order - 1)]})
 */
static int initialize_sequence
(
   JH_index sequence [const restrict static 1],
   const JH_index initial_word,
   const JH_index markov_order,
   struct JH_knowledge k [const static 1],
   FILE io [const restrict static 1]
)
{
   sequence[(markov_order - 1)] = initial_word;

   if
   (
      JH_knowledge_copy_random_swt_sequence
      (
         k,
         sequence,
         initial_word,
         markov_order,
         io
      ) < 0
   )
   {
      return -1;
   }

   if (JH_DEBUG_SEQUENCE_CREATION_INIT)
   {
      JH_index i;

      for (i = 0; i < markov_order; ++i)
      {
         JH_DEBUG
         (
            io,
            JH_DEBUG_SEQUENCE_CREATION_INIT,
            "sequence[%u]: %u",
            i,
            sequence[i]
         );
      }
   }

   return 0;
}

/******************************************************************************/
/** EXPORTED ******************************************************************/
/******************************************************************************/

/* See "sequence.h" */
int JH_sequence_create_from
(
   const JH_index initial_word,
   size_t credits [const restrict],
   struct JH_knowledge k [const restrict static 1],
   const JH_index markov_order,
   JH_index * sequence [const restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   if
   (
      JH_sequence_ensure_capacity
      (
         sequence,
         sequence_capacity,
         markov_order,
         io
      ) < 0
   )
   {
      *sequence_length = 0;

      return -1;
   }

   if
   (
      initialize_sequence
      (
         *sequence,
         initial_word,
         markov_order,
         k,
         io
      ) < 0
   )
   {
      JH_S_ERROR(io, "Failed to create start of new sequence.");

      *sequence_length = 0;

      return -2;
   }

   *sequence_length = markov_order;

   if
   (
      complete_right_part_of_sequence
      (
         sequence,
         sequence_capacity,
         sequence_length,
         markov_order,
         credits,
         k,
         io
      ) < 0
   )
   {
      JH_S_ERROR(io, "Failed to create right part of sequence.");

      *sequence_length = 0;

      return -3;
   }

   if
   (
      complete_left_part_of_sequence
      (
         sequence,
         sequence_capacity,
         sequence_length,
         markov_order,
         credits,
         k,
         io
      ) < 0
   )
   {
      JH_S_ERROR(io, "Failed to create left part of sequence.");

      *sequence_length = 0;

      return -4;
   }

   if (*sequence_length < 3)
   {
      /* 2 elements, for start and stop. */
      JH_S_ERROR(io, "Created sequence was empty.");

      *sequence_length = 0;

      return -5;
   }

   return 0;
}
