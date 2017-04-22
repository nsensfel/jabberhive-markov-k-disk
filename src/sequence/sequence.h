#ifndef _JH_CORE_SEQUENCE_H_
#define _JH_CORE_SEQUENCE_H_

/* Defines SIZE_MAX */
#include <stdint.h>

#include "../core/char_types.h"
#include "../core/index_types.h"

#include "../error/error.h"

#include "../knowledge/knowledge_types.h"

#include "sequence_types.h"

/*@
   requires \valid(sequence);
   requires (\block_length(sequence) >= 1);
   requires \valid(sequence_capacity);
   requires (\block_length(sequence) >= 1);
   requires \valid(io);

   requires (((*sequence_capacity) * sizeof(JH_index)) <= SIZE_MAX);
   requires ((sequence_required_capacity * sizeof(JH_index)) <= SIZE_MAX);

   requires
      \separated
      (
         (sequence+ (0 .. \block_length(sequence))),
         ((*sequence)+ (0 .. \block_length(*sequence))),
         (sequence_capacity+ (0 ..\block_length(sequence_capacity))),
         (io+ (0 ..\block_length(io)))
      );

   ensures
      \separated
      (
         (sequence+ (0 .. \block_length(sequence))),
         ((*sequence)+ (0 .. \block_length(*sequence))),
         (sequence_capacity+ (0 ..\block_length(sequence_capacity))),
         (io+ (0 ..\block_length(io)))
      );

   ensures (((*sequence_capacity) * sizeof(JH_index)) <= SIZE_MAX);
   ensures ((sequence_required_capacity * sizeof(JH_index)) <= SIZE_MAX);
   ensures \valid(sequence);
   ensures \valid(*sequence);
   ensures \valid(sequence_capacity);
   ensures \valid(io);

   assigns (*sequence);
   assigns (*sequence_capacity);

   ensures ((\result == 1) || (\result == 0) || (\result == -1));

   ensures
      (
         (\result == 1) ==>
            ((*sequence_capacity) == sequence_required_capacity)
      );

   ensures
      (
         (\result == 1) ==>
            ((*sequence_capacity) > \old(*sequence_capacity))
      );

   ensures ((\result == -1) ==> ((*sequence) == \old(*sequence)));

   ensures
      (
         (\result == -1) ==>
            ((*sequence_capacity) == \old(*sequence_capacity))
      );

   ensures ((\result == 0) ==> ((*sequence) == \old(*sequence)));

   ensures
      (
         (\result == 0) ==>
            ((*sequence_capacity) == \old(*sequence_capacity))
      );
@*/
int JH_sequence_ensure_capacity
(
   JH_index * sequence [const restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   const size_t sequence_required_capacity,
   FILE io [const restrict static 1]
);

int JH_sequence_from_undercase_string
(
   const JH_char string [const restrict],
   const size_t string_length,
   struct JH_knowledge k [const restrict static 1],
   JH_index * sequence [const restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   FILE io [const restrict static 1]
);

/*
 * Creates a sequence containing {initial_word}. The remaining elements of
 * sequence are added according to what is known to {k} as being possible.
 * The resulting sequence starts by JH_START_OF_SEQUENCE_ID, and ends by
 * JH_END_OF_SEQUENCE_ID. The sequence is allocated by the function. If an
 * error occur, it is unallocated and set to NULL ({sequence_size} is set
 * accordingly).
 * Return:
 *    0 on success.
 *    -1 iff the allocating failed.
 *    -2 iff the sequence initialization failed.
 *    -3 iff an error occured when trying to add elements to the right of the
 *       sequence.
 *    -4 iff an error occured when trying to add elements to the left of the
 *       sequence.
 *    -5 iff the resulting sequence would have been empty.
 * Pre:
 *    (> {markov_order} 1)
 *    (knows {k} {initial_word})
 *    (initialized {k})
 */
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
);

/*@
   requires \valid(sequence);
   requires \valid(*sequence);
   requires \valid(sequence_capacity);
   requires \valid(sequence_length);
   requires \valid(io);
   requires (((*sequence_length) * sizeof(JH_index)) <= SIZE_MAX);
   requires (((*sequence_capacity) * sizeof(JH_index)) <= SIZE_MAX);
   requires
      \separated
      (
         (sequence+ (0 .. \block_length(sequence))),
         ((*sequence)+ (0 .. \block_length(*sequence))),
         (sequence_capacity+ (0 ..\block_length(sequence_capacity))),
         (sequence_length+ (0 ..\block_length(sequence_length))),
         (io+ (0 ..\block_length(io)))
      );

   assigns (*sequence_length);
   assigns (*sequence[0]);
   assigns (*sequence_capacity);

   ensures \valid(sequence);
   ensures \valid(*sequence);
   ensures \valid(sequence_capacity);
   ensures \valid(sequence_length);
   ensures \valid(io);
   ensures (((*sequence_length) * sizeof(JH_index)) <= SIZE_MAX);
   ensures (((*sequence_capacity) * sizeof(JH_index)) <= SIZE_MAX);
   ensures
      \separated
      (
         (sequence+ (0 .. \block_length(sequence))),
         ((*sequence)+ (0 .. \block_length(*sequence))),
         (sequence_capacity+ (0 ..\block_length(sequence_capacity))),
         (sequence_length+ (0 ..\block_length(sequence_length))),
         (io+ (0 ..\block_length(io)))
      );

   ensures ((\result == 0) || (\result == -1));

   ensures
   (
      (\result == 0) ==>
         (*sequence_length == (\old(*sequence_length) + 1))
   );

   ensures
      (
         (\result == 0) ==>
            ((*sequence_capacity) >= \old(*sequence_capacity))
      );

   ensures ((\result == 0) ==> (*sequence_length > \old(*sequence_length)));

   ensures ((\result == -1) ==> ((*sequence_length) == \old(*sequence_length)));
   ensures ((\result == -1) ==> (((*sequence)[0]) == \old((*sequence)[0])));
   ensures
      (
         (\result == -1) ==>
            ((*sequence_capacity) == \old(*sequence_capacity))
      );

   ensures ((\result == -1) ==> ((*sequence_length) == \old(*sequence_length)));
   ensures
      (
         (\result == -1) ==>
            ((*sequence_capacity) == \old(*sequence_capacity))
      );

@*/
int JH_sequence_append_left
(
   const JH_index word_id,
   JH_index * sequence [const restrict static 1],
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   FILE io [const restrict static 1]
);

/*@
   requires \valid(sequence);
   requires \valid(*sequence);
   requires \valid(sequence_capacity);
   requires \valid(sequence_length);
   requires \valid(io);
   requires (((*sequence_length) * sizeof(JH_index)) <= SIZE_MAX);
   requires (((*sequence_capacity) * sizeof(JH_index)) <= SIZE_MAX);
   requires
      \separated
      (
         (sequence+ (0 .. \block_length(sequence))),
         ((*sequence)+ (0 .. \block_length(*sequence))),
         (sequence_capacity+ (0 ..\block_length(sequence_capacity))),
         (sequence_length+ (0 ..\block_length(sequence_length))),
         (io+ (0 ..\block_length(io)))
      );

   assigns (*sequence_length);
   assigns ((*sequence)[0]);
   assigns (*sequence_capacity);

   ensures \valid(sequence);
   ensures \valid(*sequence);
   ensures \valid(sequence_capacity);
   ensures \valid(sequence_length);
   ensures \valid(io);
   ensures (((*sequence_length) * sizeof(JH_index)) <= SIZE_MAX);
   ensures (((*sequence_capacity) * sizeof(JH_index)) <= SIZE_MAX);
   ensures
      \separated
      (
         (sequence+ (0 .. \block_length(sequence))),
         ((*sequence)+ (0 .. \block_length(*sequence))),
         (sequence_capacity+ (0 ..\block_length(sequence_capacity))),
         (sequence_length+ (0 ..\block_length(sequence_length))),
         (io+ (0 ..\block_length(io)))
      );

   ensures ((\result == 0) || (\result == -1));

   ensures
   (
      (\result == 0) ==>
         (*sequence_length == (\old(*sequence_length) + 1))
   );

   ensures
      (
         (\result == 0) ==>
            ((*sequence_capacity) >= \old(*sequence_capacity))
      );

   ensures ((\result == 0) ==> (*sequence_length > \old(*sequence_length)));

   ensures ((\result == -1) ==> ((*sequence_length) == \old(*sequence_length)));
   ensures ((\result == -1) ==> (((*sequence)[0]) == \old((*sequence)[0])));
   ensures
      (
         (\result == -1) ==>
            ((*sequence_capacity) == \old(*sequence_capacity))
      );

   ensures ((\result == -1) ==> ((*sequence_length) == \old(*sequence_length)));
   ensures
      (
         (\result == -1) ==>
            ((*sequence_capacity) == \old(*sequence_capacity))
      );

@*/
int JH_sequence_append_right
(
   JH_index * sequence [const restrict static 1],
   const JH_index word_id,
   size_t sequence_capacity [const restrict static 1],
   size_t sequence_length [const restrict static 1],
   FILE io [const restrict static 1]
);

/*
 * Compares two sequences.
 * JH_END_OF_SEQUENCE marks the ending of a sequence, regardless of indicated
 * sequence length, meaning that [10][JH_END_OF_SEQUENCE][9] and
 * [10][JH_END_OF_SEQUENCE][8] are considered equal. Sequences do not have to
 * contain JH_END_OF_SEQUENCE. [10][JH_END_OF_SEQUENCE] and [10] are
 * considered different, [10][JH_END_OF_SEQUENCE]
 * and [10][JH_END_OF_SEQUENCE][JH_END_OF_SEQUENCE] are considered equal.
 * Same logic is applyied for JH_START_OF_SEQUENCE:
 * [START_OF_SEQUENCE][10] is not [10], but
 * [START_OF_SEQUENCE][START_OF_SEQUENCE][10] and [START_OF_SEQUENCE][10] are
 * the same.
 * Return:
 *    1 iff {sequence_a} should be considered being more than {sequence_b}
 *    0 iff {sequence_a} should be considered being equal to {sequence_b}
 *    -1 iff {sequence_a} should be considered being less than {sequence_b}
 */
int JH_sequence_cmp
(
   const JH_index sequence_a [const],
   const JH_index sequence_b [const],
   const JH_index length
);

int JH_sequence_to_undercase_string
(
   const JH_index sequence [const restrict static 1],
   const size_t sequence_length,
   struct JH_knowledge k [const restrict static 1],
   JH_char * destination [const restrict static 1],
   size_t destination_capacity [const restrict static 1],
   size_t destination_length [const restrict static 1],
   FILE io [const restrict static 1]
);

#endif
