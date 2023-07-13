#pragma once

#include <stdbool.h>
#include <stdio.h>

#include "../knowledge/knowledge_types.h"
#include "../parameters/parameters_types.h"

/******************************************************************************/
/**** ADJACENT SEQUENCE *******************************************************/
/******************************************************************************/
int JH_io_generate_adjacent_sequence_directory_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
   FILE io [const restrict static 1]
);

int JH_io_generate_adjacent_sequence_filename
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
   char * result [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_write_adjacent_sequence_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
   const struct JH_knowledge_adjacent_sequence as [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_write_adjacent_sequence
(
   const char filename [const restrict static 1],
   const struct JH_knowledge_adjacent_sequence as [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_read_adjacent_sequence_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
   struct JH_knowledge_adjacent_sequence as [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_read_adjacent_sequence
(
   const char filename [const restrict static 1],
   struct JH_knowledge_adjacent_sequence out [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_shift_adjacent_sequence_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index shift_starts_at,
   const bool is_swt,
   const JH_index collection_length,
   FILE io [const restrict static 1]
);

/******************************************************************************/
/**** DATABASE ****************************************************************/
/******************************************************************************/
int JH_io_database_exists
(
   const struct JH_knowledge k [const restrict static 1]
);

/******************************************************************************/
/**** JH_INDEX ****************************************************************/
/******************************************************************************/
int JH_io_read_jh_index
(
   FILE file [const restrict static 1],
   char * buffer [const restrict static 1],
   size_t buffer_size [const restrict static 1],
   JH_index out [const restrict static 1],
   const char file_type [const restrict static 1],
   const char field_name [const restrict static 1],
   const char filename [const restrict static 1],
   FILE io [const restrict static 1]
);

/******************************************************************************/
/**** SEQUENCE ****************************************************************/
/******************************************************************************/
int JH_io_generate_sequence_filename
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index id,
   char * result [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_write_sequence_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index sequence_id,
   const JH_index sequence [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_write_sequence
(
   const char filename [const restrict static 1],
   const JH_index length,
   const JH_index in [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_read_sequence_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index sequence_id,
   JH_index * restrict out [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_read_sequence
(
   const char filename [const restrict static 1],
   const JH_index sequence_length,
   JH_index * restrict out [const restrict static 1],
   FILE io [const restrict static 1]
);

/******************************************************************************/
/**** SEQUENCE TARGET *********************************************************/
/******************************************************************************/
int JH_io_generate_sequence_target_filename
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
   const JH_index sequence_target_ix,
   char * result [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_write_sequence_target_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
   const JH_index sequence_target_ix,
   const struct JH_knowledge_target st [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_write_sequence_target
(
   const char filename [const restrict static 1],
   const struct JH_knowledge_target st [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_read_sequence_target_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
   const JH_index sequence_target_ix,
   struct JH_knowledge_target st [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_read_sequence_target
(
   const char filename [const restrict static 1],
   struct JH_knowledge_target out [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_shift_sequence_target_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
   const JH_index shift_starts_at,
   const JH_index collection_length,
   FILE io [const restrict static 1]
);

/******************************************************************************/
/**** SORTED SEQUENCES ********************************************************/
/******************************************************************************/
int JH_io_generate_sorted_sequences_filename
(
   const struct JH_parameters params [const restrict static 1],
   char * result [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_write_sorted_sequences
(
   const char filename [const restrict static 1],
   const JH_index length,
   const JH_index in [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_read_sorted_sequences
(
   const char filename [const restrict static 1],
   JH_index length [const restrict static 1],
   JH_index * restrict out [const restrict static 1],
   FILE io [const restrict static 1]
);

/******************************************************************************/
/**** SORTED WORDS ************************************************************/
/******************************************************************************/
int JH_io_generate_sorted_words_filename
(
   const struct JH_parameters params [const restrict static 1],
   char * result [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_write_sorted_words
(
   const char filename [const restrict static 1],
   const JH_index length,
   const JH_index in [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_read_sorted_words
(
   const char filename [const restrict static 1],
   JH_index length [const restrict static 1],
   JH_index * restrict out [const restrict static 1],
   FILE io [const restrict static 1]
);

/******************************************************************************/
/**** WORD ********************************************************************/
/******************************************************************************/
int JH_io_generate_word_directory_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index id,
   FILE io [const restrict static 1]
);

int JH_io_generate_word_filename
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index id,
   char * result [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_write_word_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const struct JH_knowledge_word word [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_write_word
(
   const char filename [const restrict static 1],
   const struct JH_knowledge_word in [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_read_word_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   struct JH_knowledge_word word [const restrict static 1],
   FILE io [const restrict static 1]
);

int JH_io_read_word
(
   const char filename [const restrict static 1],
   struct JH_knowledge_word out [const restrict static 1],
   FILE io [const restrict static 1]
);
