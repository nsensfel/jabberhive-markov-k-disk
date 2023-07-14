#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include <sys/stat.h>

#include "../error/error.h"

#include "../knowledge/knowledge.h"
#include "../parameters/parameters.h"

#include "io.h"

int JH_io_generate_adjacent_sequence_directory_path
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
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
         (is_swt ? "%s/word/%u/swt/%u" : "%s/word/%u/tws/%u"),
         JH_parameters_get_database_path(params),
         word_id,
         adjacent_sequence_ix
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
      (is_swt ? "%s/word/%u/swt/%u" : "%s/word/%u/tws/%u"),
      JH_parameters_get_database_path(params),
      word_id,
      adjacent_sequence_ix
   );

   return 0;
}

int JH_io_generate_adjacent_sequence_directory_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
   FILE io [const restrict static 1]
)
{
   char * path;

   if
   (
      JH_io_generate_adjacent_sequence_directory_path
      (
         params,
         word_id,
         adjacent_sequence_ix,
         is_swt,
         &path,
         io
      )
      < 0
   )
   {
      return -1;
   }

   if (mkdir(path, 0755) < 0)
   {
      JH_ERROR
      (
         io,
         "Could not create \"%s\" directory: %s.\n",
         path,
         strerror(errno)
      );

      free((void *) path);

      return -2;
   }

   free((void *) path);

   return 0;
}

int JH_io_generate_adjacent_sequence_filename
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
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
         (is_swt ? "%s/word/%u/swt/%u/data.txt" : "%s/word/%u/tws/%u/data.txt"),
         JH_parameters_get_database_path(params),
         word_id,
         adjacent_sequence_ix
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
      (is_swt ? "%s/word/%u/swt/%u/data.txt" : "%s/word/%u/tws/%u/data.txt"),
      JH_parameters_get_database_path(params),
      word_id,
      adjacent_sequence_ix
   );

   return 0;
}

int JH_io_write_adjacent_sequence_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
   const struct JH_knowledge_adjacent_sequence as [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   char * filename;

   if
   (
      JH_io_generate_adjacent_sequence_filename
      (
         params,
         word_id,
         adjacent_sequence_ix,
         is_swt,
         &filename,
         io
      )
      < 0
   )
   {
      return -1;
   }

   if (JH_io_write_adjacent_sequence(filename, as, io) < 0)
   {
      free((void *) filename);

      return -2;
   }

   free((void *) filename);

   return 0;
}

int JH_io_write_adjacent_sequence
(
   const char filename [const restrict static 1],
   const struct JH_knowledge_adjacent_sequence as [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   FILE *file;

   JH_DEBUG
   (
      io,
      JH_DEBUG_IO,
      "Writing adjacent sequence to %s.",
      filename
   );

   file = fopen(filename, "w");

   if (file == (FILE *) NULL)
   {
      JH_ERROR
      (
         io,
         "Could not open adjacent sequence file \"%s\": %s.",
         filename,
         strerror(errno)
      );

      return -1;
   }

   fprintf
   (
      file,
      "%u\n%u\n%u\n",
      as->id,
      as->occurrences,
      as->targets_length
   );

   fclose(file);

   return 0;
}

int JH_io_read_adjacent_sequence_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index adjacent_sequence_ix,
   const bool is_swt,
   struct JH_knowledge_adjacent_sequence as [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   char * filename;

   if
   (
      JH_io_generate_adjacent_sequence_filename
      (
         params,
         word_id,
         adjacent_sequence_ix,
         is_swt,
         &filename,
         io
      )
      < 0
   )
   {
      return -1;
   }

   if (JH_io_read_adjacent_sequence(filename, as, io) < 0)
   {
      free((void *) filename);

      return -2;
   }

   free((void *) filename);

   return 0;
}

int JH_io_read_adjacent_sequence
(
   const char filename [const restrict static 1],
   struct JH_knowledge_adjacent_sequence out [const restrict static 1],
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
      "Reading adjacent sequence from %s.",
      filename
   );

   file = fopen(filename, "r");

   if (file == (FILE *) NULL)
   {
      JH_ERROR
      (
         io,
         "Could not open adjacent sequence file \"%s\": %s.",
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
            "adjacent sequence",
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
            "adjacent sequence",
            "occurrences count",
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
            &(out->targets_length),
            "adjacent sequence",
            "targets list length",
            filename,
            io
         )
         < 0
      )
   )
   {
      free((void *) buffer);
      fclose(file);

      return -3;
   }

   free((void *) buffer);
   fclose(file);

   return 0;
}

int JH_io_shift_adjacent_sequence_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const JH_index shift_starts_at,
   const bool is_swt,
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
         JH_io_generate_adjacent_sequence_directory_path
         (
            params,
            word_id,
            i,
            is_swt,
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
         JH_io_generate_adjacent_sequence_directory_path
         (
            params,
            word_id,
            i,
            is_swt,
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
            "Unable to rename directory \"%s\" to \"%s\": %s.\n"
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
