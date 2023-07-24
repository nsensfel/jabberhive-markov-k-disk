#ifndef _JH_KNOWLEDGE_KNOWLEDGE_H_
#define _JH_KNOWLEDGE_KNOWLEDGE_H_

#include <stdio.h>
#include <stdbool.h>

#include "../core/char_types.h"
#include "../core/index_types.h"

#include "../error/error.h"

#include "../parameters/parameters_types.h"

#include "knowledge_types.h"

char * JH_knowledge_get_sorted_sequences_filename
(
   const struct JH_knowledge k [const restrict static 1]
);

char * JH_knowledge_get_sorted_words_filename
(
   const struct JH_knowledge k [const restrict static 1]
);

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

/**
 * Populates the members of `k` and recovers an existing database or creates a
 * new one, depending on the state of the folder it is assigned to.
 *
 * Returns 0 on success, negative values on error.
 *
 * Pre:
 *    - `k` should not have any member in need of freeing.
 *
 * Post:
 *    - If succeeded, allocated `k` members should be finalized using
 *      JH_knowledge_finalize.
 *    - If failed, all allocations have already been freed.
 *
 * Notes:
 **/
int JH_knowledge_initialize
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   FILE io [const restrict static 1]
);

/**
 * Frees up any data allocated during the initialization of a knowledge
 * structure, and destroys its locks.
 **/
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
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const size_t word_length,
   const JH_char word [const restrict static word_length],
   JH_index result [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_knowledge_learn_sequence
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const size_t sequence_length,
   const JH_index sequence [const restrict static sequence_length],
   FILE io [const restrict static 1]
);

int JH_knowledge_learn_markov_sequence
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const JH_index sequence [const restrict static 1],
   JH_index sequence_id [const restrict static 1],
   FILE io [const restrict static 1]
);


/**
 * Populates the members of `k` and recovers an existing database or creates a
 * new one, depending on the state of the folder it is assigned to.
 *
 * Returns 0 on success, negative values on error.
 *
 * Pre:
 *    - `k` initialized.
 *    - `word_id` < `len(k->word_locks)`.
 *
 * Post:
 *    - If succeeded, `*word` is a dynamically allocated memory space.
 *    - If failed, all new allocations have already been freed.
 *    - `*word` contains `word_length + 1` characters, as the string is `\0`
 *       terminated.
 *
 * Notes:
 *    - Acquires and releases read-lock on `word_id`.
 **/
int JH_knowledge_get_word
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const JH_index word_id,
   JH_char * word [const restrict static 1],
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
int JH_knowledge_find_word
(
   const struct JH_parameters params [const restrict static 1],
   const struct JH_knowledge k [const restrict static 1],
   const size_t word_size,
   const JH_char word [const restrict static word_size],
   JH_index found_word_id [const restrict static 1],
   JH_index expected_word_sorted_ix [const restrict static 1],
   FILE io [const restrict static 1]
);

/**
 * Finds the ID and sorted index of the given word. If the word is not known,
 * the ID and sorted index are the ones that should be given to the word upon
 * learning it.
 *
 * The sorted index is that of the lowest element that's greater than the target
 * word.
 *
 * Returns 1 if found, 0 if not found, and negative values on error.
 *
 * Pre:
 *    - `k` initialized.
 *    - Lock acquired on words.
 *
 * Post (non-negative returned value):
 *    - `*found_word_id` is the word's ID.
 *    - `*expected_word_sorted_ix` is the word's sorted index.
 *
 * Notes:
 *    - Acquires and releases read-lock on each word candidate.
 *    - Results are only garanteed as long as the lock on words is kept.
 *    - All memory allocated by the function is freed within it.
 **/
int JH_knowledge_lazy_find_word
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const size_t word_size,
   const JH_char word [const restrict static word_size],
   JH_index found_word_id [const restrict static 1],
   JH_index expected_word_sorted_ix [const restrict static 1],
   FILE io [const restrict static 1]
);

/*
 * Does not acquire locks
 */
int JH_knowledge_find_sequence
(
   const struct JH_parameters params [const restrict static 1],
   const struct JH_knowledge k [const restrict static 1],
   const JH_index sequence [const restrict static 1],
   JH_index found_sequence_id [const restrict static 1],
   JH_index expected_sequence_sorted_ix [const restrict static 1],
   FILE io [const restrict static 1]
);

/**
 * Finds the ID and sorted index of the given sequence. If the sequence is not
 * known, the ID and sorted index are the ones that should be given to the
 * sequence upon learning it.
 *
 * The sorted index is that of the lowest element that's greater than the target
 * sequence.
 *
 * Returns 1 if found, 0 if not found, and negative values on error.
 *
 * Pre:
 *    - `k` initialized.
 *    - `(\forall (w \in sequence) (w < k->word_locks))`
 *    - `len(sequence) == (MARKOV_ORDER - 1)`
 *    - Lock acquired on sequences.
 *
 * Post (non-negative returned value):
 *    - `*found_sequence_id` is the sequence's ID.
 *    - `*expected_sequence_sorted_ix` is the sequence's sorted index.
 *
 * Notes:
 *    - Results are only garanteed as long as the lock on sequences is kept.
 *    - All memory allocated by the function is freed within it.
 **/
int JH_knowledge_lazy_find_sequence
(
   const struct JH_parameters params [const restrict static 1],
   const struct JH_knowledge k [const restrict static 1],
   const JH_index sequence [const restrict static 1],
   JH_index found_sequence_id [const restrict static 1],
   JH_index expected_sequence_sorted_ix [const restrict static 1],
   FILE io [const restrict static 1]
);

/**
 * Finds the ID of the rarest word in a sequence. The rarest word is defined as
 * the one that has the fewest registered occurrences in the database. Words
 * that have only been seen once are not considered, because they are unlikely
 * to produce original sentences.
 *
 * Returns 0 on success, negative values on error.
 *
 * Pre:
 *    - `k` initialized.
 *    - `(\forall (w \in sequence) (w < k->word_locks))`
 *
 * Post:
 *
 * Notes:
 *    - Acquires and releases read-lock on each word of the sequence.
 *    - All allocations made by the function are freed before it returns.
 **/
int JH_knowledge_rarest_word
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const size_t sequence_length,
   const JH_index sequence [const restrict static sequence_length],
   JH_index word_id [const restrict static 1],
   FILE io [const restrict static 1]
);

/*
* Does not acquire locks
*/
int JH_knowledge_find_adjacent_sequence
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index sequence_id,
   const JH_index word_id,
   const bool sequence_is_prefix,
   JH_index found_or_expected_ix [const restrict static 1],
   FILE io [const restrict static 1]
);

/*
* Does not acquire locks
*/
int JH_knowledge_find_sequence_target
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
   const JH_index target_id,
   JH_index result_ix [const restrict static 1],
   FILE io [const restrict static 1]
);

/**
 * Provides the ID of a random target word, given a word ID and the ID of one
 * of the sequence that is adjacent to it.
 *
 * Returns 0 on success, negative values on error.
 *
 * Pre:
 *    - `params` initialized.
 *    - `k` initialized.
 *    - `word_id < k->words_length`.
 *    - `sequence_id < k->sequences_length`.
 *    - `is_swt == 1` if sequence is a prefix, `0` if it's a suffix.
 *
 * Post:
 *    - `target` contains the ID of random target word for the sequence.
 *
 * Notes:
 *    - Acquires and releases read-lock on `word_id`.
 *    - All allocations made by the function are freed before it returns.
 **/
int JH_knowledge_random_target
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const JH_index word_id,
   const JH_index sequence_id,
   const bool is_swt,
   JH_index target [const restrict static 1],
   FILE io [const restrict static 1]
);


/**
 * Copies a random prefix (SWT) sequence of the word into the given buffer.
 *
 * Returns 0 on success, negative values on error.
 *
 * Pre:
 *    - `params` initialized.
 *    - `k` initialized.
 *    - `word_id < k->words_length`.
 *    - `len(copied_prefix) >= (MARKOV_ORDER - 1)`
 *
 * Post:
 *    - `copied_prefix` contains a random prefix of `word[word_id]`.
 *
 * Notes:
 *    - Acquires and releases read-lock on `word_id`.
 *    - All allocations made by the function are freed before it returns.
 **/
int JH_knowledge_copy_random_prefix
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const JH_index word_id,
   JH_index copied_prefix [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_knowledge_strengthen_adjacent_sequence
(
   const struct JH_parameters params [const restrict static 1],
   struct JH_knowledge k [const restrict static 1],
   const JH_index sequence_id,
   const JH_index word_id,
   const JH_index target_id,
   const bool is_swt,
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

/**
 * Frees up any data allocated during the initialization of a sequence target.
 **/
void JH_knowledge_finalize_sequence_target
(
   const struct JH_knowledge_target target [const restrict static 1]
);

/**
 * Frees up any data allocated during the initialization of an adjacent
 * sequence.
 **/
void JH_knowledge_finalize_adjacent_sequence
(
   const struct JH_knowledge_adjacent_sequence as [const restrict static 1]
);

/*
void JH_knowledge_finalize_sequence_collection
(
   const struct JH_knowledge_sequence_collection sc [const restrict static 1]
);
*/

/**
 * Frees up any data allocated during the initialization of a sequence.
 **/
void JH_knowledge_finalize_sequence
(
   JH_index * sequence [const restrict static 1]
);

/**
 * Frees up any data allocated during the initialization of a word.
 **/
void JH_knowledge_finalize_word
(
   struct JH_knowledge_word word [const restrict static 1]
);
#endif
