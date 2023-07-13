#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

#include "../error/error.h"

#include "../parameters/parameters.h"

#include "io.h"

int JH_io_generate_sorted_words_filename
(
   const struct JH_parameters params [const restrict static 1],
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
         "%s/sorted_words.txt",
         JH_parameters_get_database_path(params)
      );

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
      "%s/sorted_words.txt",
      JH_parameters_get_database_path(params)
   );

   return 0;
}

int JH_io_write_sorted_words
(
   const char filename [const restrict static 1],
   const JH_index length,
   const JH_index in [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_index i;
   FILE *file;

   file = fopen(filename, "w");

   if (file == (FILE *) NULL)
   {
      JH_ERROR
      (
         io,
         "Could not open word file \"%s\": %s.",
         filename,
         strerror(errno)
      );

      return -1;
   }

   fprintf(file, "%u\n", length);

   for (i = 0; i < length; ++i)
   {
      fprintf(file, "%u\n", in[i]);
   }

   fclose(file);

   return 0;
}

int JH_io_read_sorted_words
(
   const char filename [const restrict static 1],
   JH_index length [const restrict static 1],
   JH_index * restrict out [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_index i;
   size_t buffer_size;
   char * buffer;
   FILE * file;

   file = fopen(filename, "r");

   if (file == (FILE *) NULL)
   {
      JH_ERROR
      (
         io,
         "Could not open sorted words file \"%s\": %s.",
         filename,
         strerror(errno)
      );

      return -1;
   }

   buffer_size = 0;
   buffer = NULL;

   if
   (
      JH_io_read_jh_index
      (
         file,
         &buffer,
         &buffer_size,
         length,
         "sorted words",
         "length",
         filename,
         io
      )
      < 0
   )
   {
      fclose(file);
      free((void *) buffer);

      *length = 0;

      return -2;
   }

   *out = (JH_index *) calloc((size_t) (*length), sizeof(JH_index));

   if ((*out) == (JH_index *) NULL)
   {
      JH_ERROR
      (
         io,
         "Could not allocate memory for %u sorted words: %s.",
         (*length),
         strerror(errno)
      );

      *length = 0;

      fclose(file);
      free((void *) buffer);

      return -3;
   }

   for (i = 0; i < (*length); ++i)
   {
      if
      (
         JH_io_read_jh_index
         (
            file,
            &buffer,
            &buffer_size,
            ((*out) + i),
            "sorted words",
            "word id",
            filename,
            io
         )
         < 0
      )
      {
         fclose(file);
         free((void *) (*out));
         free((void *) buffer);

         *length = 0;

         return -4;
      }
   }

   fclose(file);
   free((void *) buffer);

   return 0;
}
