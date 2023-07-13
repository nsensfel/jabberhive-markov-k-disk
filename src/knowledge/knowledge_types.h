#ifndef _JH_KNOWLEDGE_KNOWLEDGE_TYPES_H_
#define _JH_KNOWLEDGE_KNOWLEDGE_TYPES_H_

#ifndef JH_RUNNING_FRAMA_C
   #include <pthread.h>
#endif

#include "../core/index_types.h"
#include "../core/char_types.h"

struct JH_knowledge_target
{
   JH_index id;
   JH_index occurrences;
};

struct JH_knowledge_adjacent_sequence
{
   JH_index id;
   JH_index occurrences;
   //struct JH_knowledge_target * targets;
   JH_index targets_length;
};

//struct JH_knowledge_sequence_collection
//{
//   struct JH_knowledge_adjacent_sequence * sequences_ref;
//   JH_index * sequences_ref_sorted;
//   JH_index sequences_ref_length;
//};

struct JH_knowledge_word
{
   JH_char * word;
   JH_index word_length;
   JH_index occurrences;

   /* [Sequence] [Word] [Target] */
   JH_index swt_sequences_ref_length;
   //struct JH_knowledge_sequence_collection swt;

   /* [Target] [Word] [Sequence] */
   JH_index tws_sequences_ref_length;
   //struct JH_knowledge_sequence_collection tws;

   //pthread_rwlock_t lock;
};

struct JH_knowledge
{
#ifndef JH_RUNNING_FRAMA_C
   pthread_rwlock_t words_lock;
   pthread_rwlock_t * word_locks;
   pthread_rwlock_t sequences_lock;
#else
   int words_lock;
   int sequences_lock;
   int * word_lock;
#endif

   //struct JH_knowledge_word * words;
   JH_index words_length;
   JH_index * words_sorted;
   char * words_sorted_filename;

   //JH_index ** sequences;
   JH_index sequences_length;
   JH_index * sequences_sorted;
   char * sequences_sorted_filename;
};

#endif
