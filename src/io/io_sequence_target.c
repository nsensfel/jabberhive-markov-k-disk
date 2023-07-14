#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

#include "../error/error.h"

#include "../knowledge/knowledge.h"
#include "../parameters/parameters.h"

#include "io.h"

int JH_io_generate_sequence_target_filename
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
   const JH_index sequence_target_ix,
   char * result [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   size_t length;

   length =
      snprintf
      (
         NULL,
         0,
         (is_swt ?
            "%s/word/%u/swt/%u/target_%u.txt"
            :
            "%s/word/%u/tws/%u/target_%u.txt"
         ),
         JH_parameters_get_database_path(params),
         word_id,
         adjacent_sequence_ix,
         sequence_target_ix
      );

   length += 1;

   *result = calloc(length, sizeof(char));

   if (*result == (char *) NULL)
   {
      JH_ERROR
      (
         io,
         "Could not allocate memory for path: %s.\n",
         strerror(errno)
      );

      return -1;
   }

   snprintf
   (
      *result,
      length,
      (is_swt ?
         "%s/word/%u/swt/%u/target_%u.txt"
         :
         "%s/word/%u/tws/%u/target_%u.txt"
      ),
      JH_parameters_get_database_path(params),
      word_id,
      adjacent_sequence_ix,
      sequence_target_ix
   );

   return 0;
}

int JH_io_write_sequence_target_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
   const JH_index sequence_target_ix,
   const struct JH_knowledge_target st [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   char * filename;

   if
   (
      JH_io_generate_sequence_target_filename
      (
         params,
         word_id,
         adjacent_sequence_ix,
         is_swt,
         sequence_target_ix,
         &filename,
         io
      )
      < 0
   )
   {
      return -1;
   }

   if (JH_io_write_sequence_target(filename, st, io) < 0)
   {
      free((void *) filename);

      return -2;
   }

   free((void *) filename);

   return 0;
}

int JH_io_write_sequence_target
(
   const char filename [const restrict static 1],
   const struct JH_knowledge_target st [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   FILE *file;

   JH_DEBUG
   (
      io,
      JH_DEBUG_IO,
      "Writing sequence target to %s.",
      filename
   );

   file = fopen(filename, "w");

   if (file == (FILE *) NULL)
   {
      JH_ERROR
      (
         io,
         "Could not open sequence target file \"%s\": %s.",
         filename,
         strerror(errno)
      );

      return -1;
   }

   fprintf
   (
      file,
      "%u\n%u\n",
      st->id,
      st->occurrences
   );

   fclose(file);

   return 0;
}

int JH_io_read_sequence_target_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
   const JH_index sequence_target_ix,
   struct JH_knowledge_target st [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   char * filename;

   if
   (
      JH_io_generate_sequence_target_filename
      (
         params,
         word_id,
         adjacent_sequence_ix,
         is_swt,
         sequence_target_ix,
         &filename,
         io
      )
      < 0
   )
   {
      return -1;
   }

   if (JH_io_read_sequence_target(filename, st, io) < 0)
   {
      free((void *) filename);

      return -2;
   }

   free((void *) filename);

   return 0;
}

int JH_io_read_sequence_target
(
   const char filename [const restrict static 1],
   struct JH_knowledge_target out [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   size_t buffer_size;
   char * buffer;
   FILE * file;

   JH_DEBUG
   (
      io,
      JH_DEBUG_IO,
      "Reading sequence target from %s.",
      filename
   );

   file = fopen(filename, "r");

   if (file == (FILE *) NULL)
   {
      JH_ERROR
      (
         io,
         "Could not open sequence target file \"%s\": %s.",
         filename,
         strerror(errno)
      );

      return -1;
   }

   buffer_size = 0;
   buffer = NULL;

   if
   (
      (
         JH_io_read_jh_index
         (
            file,
            &buffer,
            &buffer_size,
            &(out->id),
            "sequence target",
            "id",
            filename,
            io
         )
         < 0
      )
      ||
      (
         JH_io_read_jh_index
         (
            file,
            &buffer,
            &buffer_size,
            &(out->occurrences),
            "sequence target",
            "occurrences count",
            filename,
            io
         )
         < 0
      )
   )
   {
      fclose(file);
      free((void *) buffer);

      return -3;
   }

   fclose(file);

   free((void *) buffer);

   return 0;
}

int JH_io_shift_sequence_target_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
   const JH_index shift_starts_at,
   const JH_index collection_length,
   FILE io [const restrict static 1]
)
{
   char * source;
   char * dest;
   JH_index i;

   i = collection_length;

   while (i > shift_starts_at)
   {
      if
      (
         JH_io_generate_sequence_target_filename
         (
            params,
            word_id,
            adjacent_sequence_ix,
            is_swt,
            i,
            &dest,
            io
         )
         < 0
      )
      {
         return -1;
      }

      i -= 1;

      if
      (
         JH_io_generate_sequence_target_filename
         (
            params,
            word_id,
            adjacent_sequence_ix,
            is_swt,
            i,
            &source,
            io
         )
         < 0
      )
      {
         free((void *) dest);

         return -1;
      }

      if (rename(source, dest) < 0)
      {

         JH_ERROR
         (
            io,
               "Unable to move file \"%s\" to \"%s\": %s.\n"
               "Database may have been made incoherent as a result."
            ,
            source,
            dest,
            strerror(errno)
         );

         free((void *) dest);
         free((void *) source);

         return -2;
      }

      free((void *) dest);
      free((void *) source);
   }

   return 0;
}
