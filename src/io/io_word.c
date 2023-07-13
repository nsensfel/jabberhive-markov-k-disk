#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

#include <sys/stat.h>

#include "../error/error.h"

#include "../knowledge/knowledge.h"
#include "../parameters/parameters.h"

#include "io.h"

int JH_io_generate_word_directory_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index id,
   FILE io [const restrict static 1]
)
{
   char * path;
   size_t length;

   length =
      snprintf
      (
         NULL,
         0,
         "%s/word/%u",
         JH_parameters_get_database_path(params),
         id
      );

   path = (char *) calloc(length, sizeof(char));

   if (path == (char *) NULL)
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
      path,
      length,
      "%s/word/%u",
      JH_parameters_get_database_path(params),
      id
   );

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

int JH_io_generate_word_filename
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
         "%s/word/%u/data.txt",
         JH_parameters_get_database_path(params),
         id
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
      "%s/word/%u/data.txt",
      JH_parameters_get_database_path(params),
      id
   );

   return 0;
}

int JH_io_write_word_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   const struct JH_knowledge_word word [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   char * filename;

   if
   (
      JH_io_generate_word_filename
      (
         params,
         word_id,
         &filename,
         io
      )
      < 0
   )
   {
      return -1;
   }

   if (JH_io_write_word(filename, word, io) < 0)
   {
      free((void *) filename);

      return -2;
   }

   free((void *) filename);

   return 0;
}

int JH_io_write_word
(
   const char filename [const restrict static 1],
   const struct JH_knowledge_word in [const restrict static 1],
   FILE io [const restrict static 1]
)
{
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

   fprintf
   (
      file,
      "%s\n%u\n%u\n%u\n%u\n",
      in->word,
      in->word_length,
      in->occurrences,
      in->swt_sequences_ref_length,
      in->tws_sequences_ref_length
   );

   fclose(file);

   return 0;
}

int JH_io_read_word_from_id
(
   const struct JH_parameters params [const restrict static 1],
   const JH_index word_id,
   struct JH_knowledge_word word [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   char * filename;

   if
   (
      JH_io_generate_word_filename
      (
         params,
         word_id,
         &filename,
         io
      )
      < 0
   )
   {
      return -1;
   }

   if (JH_io_read_word(filename, word, io) < 0)
   {
      free((void *) filename);

      return -2;
   }

   free((void *) filename);

   return 0;
}

int JH_io_read_word
(
   const char filename [const restrict static 1],
   struct JH_knowledge_word out [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   ssize_t ret;
   size_t buffer_size;
   char * buffer;
   FILE * file;

   file = fopen(filename, "r");

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

   buffer_size = 0;
   out->word = (char *) NULL;

   ret = getline(&(out->word), &buffer_size, file);

   if (ret < 0)
   {
      JH_ERROR
      (
         io,
         "Could not read first line of word file \"%s\": %s.",
         filename,
         strerror(errno)
      );

      fclose(file);
      free((void *) out->word);

      return -2;
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
            &(out->word_length),
            "word",
            "word length",
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
            "word",
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
            &(out->swt_sequences_ref_length),
            "word",
            "SWT adjacent sequences count",
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
            &(out->tws_sequences_ref_length),
            "word",
            "TWS adjacent sequences count",
            filename,
            io
         )
         < 0
      )
   )
   {
      fclose(file);
      free((void *) buffer);
      free((void *) out->word);

      return -3;
   }

   fclose(file);

   free((void *) buffer);

   return 0;
}
