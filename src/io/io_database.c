#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include <sys/stat.h>

#include "../error/error.h"

#include "../knowledge/knowledge.h"

#include "../parameters/parameters.h"

#include "io.h"

int JH_io_database_exists
(
   const struct JH_knowledge k [const restrict static 1]
)
{
   int ret;
 //  struct stat s;

   JH_DEBUG
   (
      stdout,
      JH_DEBUG_IO,
      "Checking if file %s exists, to see if folder is a database.",
      JH_knowledge_get_sorted_words_filename(k)
   );


   //ret = stat(JH_knowledge_get_sorted_sequences_filename(k), &s);
   ret = access(JH_knowledge_get_sorted_words_filename(k), W_OK);

   JH_DEBUG
   (
      stdout,
      JH_DEBUG_IO,
      "DB test yielded %d: %s.",
      ret,
      strerror(errno)
   );

   if (ret >= 0)
   {
      JH_DEBUG
      (
         stdout,
         JH_DEBUG_IO,
         "Checking if file %s exists, to see if database is fully initialized.",
         JH_knowledge_get_sorted_sequences_filename(k)
      );


      //ret = stat(JH_knowledge_get_sorted_sequences_filename(k), &s);
      ret = access(JH_knowledge_get_sorted_sequences_filename(k), W_OK);

      JH_DEBUG
      (
         stdout,
         JH_DEBUG_IO,
         "DB test yielded %d: %s.",
         ret,
         strerror(errno)
      );

      return (ret >= 0);
   }

   return 0;
}

static int generate_inner_db_folder
(
   const struct JH_parameters params [const restrict static 1],
   const char suffix [const restrict static 1],
   FILE io [const restrict]
)
{
   char * path;
   size_t length;

   length =
      snprintf
      (
         NULL,
         0,
         "%s%s",
         JH_parameters_get_database_path(params),
         suffix
      );

   length += 1;

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
      "%s%s",
      JH_parameters_get_database_path(params),
      suffix
   );

   JH_DEBUG
   (
      io,
      JH_DEBUG_IO,
      "Creating dir: %s",
      path
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

int JH_io_initialize_database
(
   const struct JH_parameters params [const restrict static 1],
   FILE io [const restrict static 1]
)
{
   JH_DEBUG
   (
      stdout,
      JH_DEBUG_IO,
      "Initializing new database in %s",
      JH_parameters_get_database_path(params)
   );

   (void) generate_inner_db_folder(params, "", io);

   if
   (
      (generate_inner_db_folder(params, "/word", io) < 0)
      || (generate_inner_db_folder(params, "/sequence", io) < 0)
   )
   {
      return -1;
   }

   return 0;
}
