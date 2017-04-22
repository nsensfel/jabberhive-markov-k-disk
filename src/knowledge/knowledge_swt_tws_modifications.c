#include <stdlib.h>

#include "../core/index.h"

#include "../error/error.h"

#include "knowledge.h"

static int add_target
(
   struct JH_knowledge_sequence_data sd [const restrict static 1],
   const JH_index target_id,
   const JH_index s_index,
   const JH_index t_index,
   FILE io [const restrict static 1]
)
{
   struct JH_knowledge_target * new_p;

   /* (sd->targets_length == JH_INDEX_MAX) => target_id \in sd->targets. */

   sd->targets_length += 1;

   new_p =
      (struct JH_knowledge_target *) realloc
      (
         (void *) sd->targets,
         (sd->targets_length * sizeof(struct JH_knowledge_target))
      );

   if (new_p == (struct JH_knowledge_target *) NULL)
   {
      JH_S_ERROR
      (
         io,
         "[E] Unable to allocate memory required to store more targets."
      );

      sd->targets_length -= 1;

      return -1;
   }

   sd->targets = new_p;

   if (t_index != (sd->targets_length - 1))
   {
      memmove
      (
         (void *) (sd->targets + t_index + 1),
         (const void *) (sd->targets + t_index),
         (size_t)
         (
            ((sd->targets_length - t_index) - 1)
            * sizeof(struct JH_knowledge_target)
         )
      );
   }

   sd->targets[t_index].id = target_id;
   sd->targets[t_index].occurrences = 0;

   return 0;
}

static int add_sequence
(
   struct JH_knowledge_sequence_collection sc [const restrict static 1],
   const JH_index sequence_id,
   JH_index s_index [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   struct JH_knowledge_sequence_data * new_p;
   JH_index * new_ps;

   /*
    * (sc->sequences_ref_length == JH_INDEX_MAX) =>
    *    sequence_id \in sc->sequences_ref.
    */

   sc->sequences_ref_length += 1;

   new_p =
      (struct JH_knowledge_sequence_data *) realloc
      (
         (void *) sc->sequences_ref,
         (sc->sequences_ref_length * sizeof(struct JH_knowledge_sequence_data))
      );

   if (new_p == (struct JH_knowledge_sequence_data *) NULL)
   {
      JH_S_ERROR
      (
         io,
         "[E] Unable to allocate memory required to store new preceding or "
         " following sequence."
      );

      sc->sequences_ref_length -= 1;

      return -1;
   }

   sc->sequences_ref = new_p;

   new_ps =
      (JH_index *) realloc
      (
         (void *) sc->sequences_ref_sorted,
         (sc->sequences_ref_length * sizeof(JH_index))
      );

   if (new_p == (struct JH_knowledge_sequence_data *) NULL)
   {
      JH_S_ERROR
      (
         io,
         "[E] Unable to allocate memory required to store new preceding or "
         " following sequence."
      );

      sc->sequences_ref_length -= 1;

      return -1;
   }

   sc->sequences_ref_sorted = new_ps;

   if (*s_index != (sc->sequences_ref_length - 1))
   {
      memmove
      (
         (void *) (sc->sequences_ref_sorted + (*s_index) + 1),
         (const void *) (sc->sequences_ref_sorted + (*s_index)),
         (size_t)
         (
            ((sc->sequences_ref_length - (*s_index)) - 1)
            * sizeof(JH_index)
         )
      );
   }

   sc->sequences_ref_sorted[*s_index] = (sc->sequences_ref_length - 1);
   *s_index = (sc->sequences_ref_length - 1);

   sc->sequences_ref[*s_index].id = sequence_id;
   sc->sequences_ref[*s_index].occurrences = 0;
   sc->sequences_ref[*s_index].targets = (struct JH_knowledge_target *) NULL;
   sc->sequences_ref[*s_index].targets_length = 0;

   return 0;
}

int JH_knowledge_strengthen_swt
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index sequence_id,
   const JH_index word_id,
   const JH_index target_id,
   FILE io [const restrict static 1]
)
{
   JH_index s_index, t_index;

   if
   (
      JH_knowledge_find_markov_sequence
      (
         sequence_id,
         &(k->words[word_id].swt),
         &s_index
      ) < 0
   )
   {
      if
      (
         add_sequence
         (
            &(k->words[word_id].swt),
            sequence_id,
            &s_index,
            io
         ) < 0
      )
      {
         return -1;
      }
   }

   if
   (
      JH_knowledge_find_sequence_target
      (
         target_id,
         (k->words[word_id].swt.sequences_ref + s_index),
         &t_index
      ) < 0
   )
   {
      if
      (
         add_target
         (
            &(k->words[word_id].swt.sequences_ref[s_index]),
            target_id,
            s_index,
            t_index,
            io
         ) < 0
      )
      {
         return -1;
      }
   }

   if
   (
      (
         k->words[word_id].swt.sequences_ref[s_index].occurrences
         == JH_INDEX_MAX
      )
      ||
      (
         k->words[word_id].swt.sequences_ref[s_index].targets[t_index].occurrences
         == JH_INDEX_MAX
      )
   )
   {
      JH_S_WARNING
      (
         io,
         "[W] Unable to strengthen SWT link: link is already at max strength."
      );

      return 1;
   }

   k->words[word_id].swt.sequences_ref[s_index].occurrences += 1;
   k->words[word_id].swt.sequences_ref[s_index].targets[t_index].occurrences += 1;

   return 0;
}

int JH_knowledge_strengthen_tws
(
   struct JH_knowledge k [const restrict static 1],
   const JH_index target_id,
   const JH_index word_id,
   const JH_index sequence_id,
   FILE io [const restrict static 1]
)
{
   JH_index s_index, t_index;

   if
   (
      JH_knowledge_find_markov_sequence
      (
         sequence_id,
         &(k->words[word_id].tws),
         &s_index
      ) < 0
   )
   {
      if
      (
         add_sequence
         (
            &(k->words[word_id].tws),
            sequence_id,
            &s_index,
            io
         ) < 0
      )
      {
         return -1;
      }
   }

   if
   (
      JH_knowledge_find_sequence_target
      (
         target_id,
         (k->words[word_id].tws.sequences_ref + s_index),
         &t_index
      ) < 0
   )
   {
      if
      (
         add_target
         (
            &(k->words[word_id].tws.sequences_ref[s_index]),
            target_id,
            s_index,
            t_index,
            io
         ) < 0
      )
      {
         return -1;
      }
   }

   if
   (
      (
         k->words[word_id].tws.sequences_ref[s_index].occurrences
         == JH_INDEX_MAX
      )
      ||
      (
         k->words[word_id].tws.sequences_ref[s_index].targets[t_index].occurrences
         == JH_INDEX_MAX
      )
   )
   {
      JH_S_ERROR
      (
         io,
         "[E] Unable to strengthen TWS link: link is already at max strength."
      );

      return -1;
   }

   k->words[word_id].tws.sequences_ref[s_index].occurrences += 1;
   k->words[word_id].tws.sequences_ref[s_index].targets[t_index].occurrences += 1;

   return 0;
}
