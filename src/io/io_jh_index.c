#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

#include "../error/error.h"

#include "io.h"

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
)
{
   if (getline(buffer, buffer_size, file) < 0)
   {
      JH_ERROR
      (
         io,
         "Could not read %s of %s file \"%s\": %s.",
         field_name,
         file_type,
         filename,
         strerror(errno)
      );

      return -1;
   }

   *out = (JH_index) atol(*buffer);

   return 0;
}
