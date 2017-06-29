#ifndef _JH_KNOWLEDGE_KNOWLEDGE_H_
#define _JH_KNOWLEDGE_KNOWLEDGE_H_

#include "../core/char_types.h"
#include "../core/index_types.h"

#include "../error/error.h"

#include "knowledge_types.h"

int JH_knowledge_readlock_words
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_knowledge_writelock_words
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_knowledge_readunlock_words
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_knowledge_writeunlock_words
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_knowledge_readlock_word
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index i,
   FILE io [const restrict static 1]
);

int JH_knowledge_writelock_word
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index i,
   FILE io [const restrict static 1]
);

int JH_knowledge_readunlock_word
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index i,
   FILE io [const restrict static 1]
);

int JH_knowledge_writeunlock_word
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index i,
   FILE io [const restrict static 1]
);

int JH_knowledge_readlock_sequences
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_knowledge_writelock_sequences
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_knowledge_readunlock_sequences
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_knowledge_writeunlock_sequences
(
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
);

/*@
   requires (\block_length(k) >= 1);

// Returns zero on success, -1 on failure.
   assigns \result;
   ensures ((\result == 0) || (\result == -1));

// On success, all fields of {*k} are set.
   ensures ((\result == 0) ==> \valid(k));

// On success, the two reserved words are learnt.
   ensures ((\result == 0) ==> (k->words_length == 2));

// On success, the mutex is initialized and unlocked.
   ensures ((\result == 0) ==> (k->mutex == 1));

// At least some fields of k are set in any case.
   assigns (*k);
@*/
int JH_knowledge_initialize (struct JH_knowledge k [const restrict static 1]);

void JH_knowledge_finalize (struct JH_knowledge k [const restrict static 1]);

/*
 * When returning 0:
 *    {word} was added to {k}, or was already there.
 *    {*result} indicates where {word} is in {k->words}.
 *
 * When returning -1:
 *    Something went wrong when adding the occurrence of {word} to {k}.
 *    {k} remains semantically unchanged.
 *    {*result} may or may not have been altered.
 */
int JH_knowledge_learn_word
(
   struct JH_knowledge k [const static 1],
   const JH_char word [const restrict static 1],
   const size_t word_length,
   JH_index result [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_knowledge_learn_sequence
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index sequence [const restrict static 1],
   const size_t sequence_length,
   const JH_index markov_order,
   FILE io [const restrict static 1]
);

int JH_knowledge_learn_markov_sequence
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index sequence [const restrict static 1],
   const JH_index markov_order, /* Pre (> markov_order 1) */
   JH_index sequence_id [const restrict static 1],
   FILE io [const restrict static 1]
);

void JH_knowledge_get_word
(
   struct JH_knowledge k [const static 1],
   const JH_index word_ref,
   const JH_char * word [const restrict static 1],
   JH_index word_length [const restrict static 1],
   FILE io [const restrict static 1]
);

/*
 * When returning 0:
 *    {word} is in {k}.
 *    {word} is located at {k->words[*result]}.
 *
 * When returning -1:
 *    {word} is not in {k}.
 *    {*result} is where {word} was expected to be found in
 *    {k->sorted_indices}.
 *
 * Does not acquire locks
 */
int JH_knowledge_find_word_id
(
   const struct JH_knowledge k [const restrict static 1],
   const JH_char word [const restrict static 1],
   const size_t word_size,
   JH_index result [const restrict static 1]
);

 /*
 * Does not acquire locks
 */
int JH_knowledge_find_sequence
(
   const struct JH_knowledge k [const static 1],
   const JH_index sequence [const restrict static 1],
   const JH_index markov_order, /* Pre: (> 1) */
   JH_index sequence_id [const restrict static 1]
);

int JH_knowledge_rarest_word
(
   struct JH_knowledge k [const static 1],
   const JH_index sequence [const restrict static 1],
   const size_t sequence_length,
   JH_index word_id [const restrict static 1],
   FILE io [const restrict static 1]
);

/*
* Does not acquire locks
*/
int JH_knowledge_find_markov_sequence
(
   const JH_index sequence_id,
   const struct JH_knowledge_sequence_collection sc [const restrict static 1],
   JH_index result [const restrict static 1]
);

/*
* Does not acquire locks
*/
int JH_knowledge_find_sequence_target
(
   const JH_index target_id,
   const struct JH_knowledge_sequence_data sd [const restrict static 1],
   JH_index result [const restrict static 1]
);

int JH_knowledge_random_tws_target
(
   struct JH_knowledge k [const static 1],
   JH_index target [const restrict static 1],
   const JH_index word_id,
   const JH_index sequence_id,
   FILE io [const restrict static 1]
);

int JH_knowledge_random_swt_target
(
   struct JH_knowledge k [const static 1],
   const JH_index sequence_id,
   const JH_index word_id,
   JH_index target [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_knowledge_copy_random_swt_sequence
(
   struct JH_knowledge k [const static 1],
   JH_index sequence [const restrict static 1],
   const JH_index word_id,
   const JH_index markov_order,
   FILE io [const restrict static 1]
);

int JH_knowledge_strengthen_swt
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index sequence_id,
   const JH_index word_id,
   const JH_index target_id,
   FILE io [const restrict static 1]
);

int JH_knowledge_strengthen_tws
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index target_id,
   const JH_index word_id,
   const JH_index sequence_id,
   FILE io [const restrict static 1]
);

/*
 * TODO
 */
/*
int JH_knowledge_weaken_swt
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index sequence_id,
   const JH_index word_id,
   const JH_index target_id,
   FILE io [const restrict static 1]
);

int JH_knowledge_weaken_tws
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index target_id,
   const JH_index word_id,
   const JH_index sequence_id,
   FILE io [const restrict static 1]
);
*/
#endif
