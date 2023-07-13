#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

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
   struct stat s;

   if (stat(JH_knowledge_get_sorted_sequences_filename(k), &s) < 0)
   {
      return 0;
   }

   return 1;
}
