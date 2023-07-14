#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

#include "../error/error.h"

#include "../knowledge/knowledge.h"
#include "../parameters/parameters.h"

#include "io.h"

int JH_io_generate_sequence_filename
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index id,
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
         "%s/sequence/%u.txt",
         JH_parameters_get_database_path(params),
         id
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
      "%s/sequence/%u.txt",
      JH_parameters_get_database_path(params),
      id
   );

   return 0;
}


int JH_io_write_sequence_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index sequence_id,
   const JH_index sequence [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   char * filename;

   if
   (
      JH_io_generate_sequence_filename
      (
         params,
         sequence_id,
         &filename,
         io
      )
      < 0
   )
   {
      return -1;
   }

   if
   (
      JH_io_write_sequence
      (
         filename,
         (JH_parameters_get_markov_order(params) - 1),
         sequence,
         io
      )
      < 0
   )
   {
      free((void *) filename);

      return -2;
   }

   free((void *) filename);

   return 0;
}

int JH_io_write_sequence
(
   const char filename [const restrict static 1],
   const JH_index length,
   const JH_index in [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_index i;
   FILE *file;

   JH_DEBUG
   (
      io,
      JH_DEBUG_IO,
      "Writing sequence to %s.",
      filename
   );

   file = fopen(filename, "w");

   if (file == (FILE *) NULL)
   {
      JH_ERROR
      (
         io,
         "Could not open sequence file \"%s\": %s.",
         filename,
         strerror(errno)
      );

      return -1;
   }

   for (i = 0; i < length; ++i)
   {
      fprintf(file, "%u\n", in[i]);
   }

   fclose(file);

   return 0;
}

int JH_io_read_sequence_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index sequence_id,
   JH_index * restrict out [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   char * filename;

   if
   (
      JH_io_generate_sequence_filename
      (
         params,
         sequence_id,
         &filename,
         io
      )
      < 0
   )
   {
      return -1;
   }

   if
   (
      JH_io_read_sequence
      (
         filename,
         (JH_parameters_get_markov_order(params) - 1),
         out,
         io
      )
      < 0
   )
   {
      free((void *) filename);

      return -2;
   }

   free((void *) filename);

   return 0;
}

int JH_io_read_sequence
(
   const char filename [const restrict static 1],
   const JH_index sequence_length,
   JH_index * restrict out [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_index i;
   size_t buffer_size;
   char * buffer;
   FILE * file;

   JH_DEBUG
   (
      io,
      JH_DEBUG_IO,
      "Reading sequence from %s.",
      filename
   );


   file = fopen(filename, "r");

   if (file == (FILE *) NULL)
   {
      JH_ERROR
      (
         io,
         "Could not open sequence file \"%s\": %s.",
         filename,
         strerror(errno)
      );

      return -1;
   }

   *out = (JH_index *) calloc(sequence_length, sizeof(JH_index));

   if (*out == (JH_index *) NULL)
   {
      JH_ERROR
      (
         io,
         "Could not allocate memory to read sequence of length %u: %s.",
         sequence_length,
         strerror(errno)
      );

      return -2;
   }

   buffer_size = 0;
   buffer = NULL;

   for (i = 0; i < sequence_length; ++i)
   {
      if
      (
         JH_io_read_jh_index
         (
            file,
            &buffer,
            &buffer_size,
            ((*out) + i),
            "sequence",
            "word id",
            filename,
            io
         )
         < 0
      )
      {
         fclose(file);
         free((void *) buffer);

         return -3;
      }
   }

   fclose(file);
   free((void *) buffer);

   return 0;
}
