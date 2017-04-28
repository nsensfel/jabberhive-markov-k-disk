#include <stdio.h>
#include <string.h>

#include "../error/error.h"

#include "server.h"

int JH_server_worker_send_confirm_pipelining_support
(
   struct JH_server_worker worker [const restrict static 1]
)
{
   int err;

   err = fprintf(worker->socket_as_file, "!CPS 0\n");

   if (err == 0)
   {
      JH_S_ERROR
      (
         stderr,
         "Thread could not write anything to socket."
      );

      return -1;
   }
   else if (err < 0)
   {
      JH_ERROR
      (
         stderr,
         "Thread could not write to socket: %s.",
         strerror(err)
      );

      return -1;
   }

   return 0;
}

int JH_server_worker_send_confirm_protocol_version
(
   struct JH_server_worker worker [const restrict static 1]
)
{
   int err;

   err = fprintf(worker->socket_as_file, "!CPV 1\n");

   if (err == 0)
   {
      JH_S_ERROR
      (
         stderr,
         "Thread could not write anything to socket."
      );

      return -1;
   }
   else if (err < 0)
   {
      JH_ERROR
      (
         stderr,
         "Thread could not write to socket: %s.",
         strerror(err)
      );

      return -1;
   }

   return 0;
}

int JH_server_worker_send_positive
(
   struct JH_server_worker worker [const restrict static 1]
)
{
   int err;

   err = fprintf(worker->socket_as_file, "!P \n");

   if (err == 0)
   {
      JH_S_ERROR
      (
         stderr,
         "Thread could not write anything to socket."
      );

      return -1;
   }
   else if (err < 0)
   {
      JH_ERROR
      (
         stderr,
         "Thread could not write to socket: %s.",
         strerror(err)
      );

      return -1;
   }

   return 0;
}

int JH_server_worker_send_negative
(
   struct JH_server_worker worker [const restrict static 1]
)
{
   int err;

   err = fprintf(worker->socket_as_file, "!N \n");

   if (err == 0)
   {
      JH_S_ERROR
      (
         stderr,
         "Thread could not write anything to socket."
      );

      return -1;
   }
   else if (err < 0)
   {
      JH_ERROR
      (
         stderr,
         "Thread could not write to socket: %s.",
         strerror(err)
      );

      return -1;
   }

   return 0;
}

int JH_server_worker_send_generated_reply
(
   struct JH_server_worker worker [const restrict static 1]
)
{
   int err;
   size_t written;

   err = fputs
   (
      "!GR ",
      worker->socket_as_file
   );

   if (err == 0)
   {
      JH_S_ERROR
      (
         stderr,
         "Thread could not write anything to socket."
      );

      return -1;
   }
   else if (err < 0)
   {
      JH_ERROR
      (
         stderr,
         "Thread could not write to socket: %s.",
         strerror(err)
      );

      return -1;
   }

   written =
      fwrite
      (
         worker->buffer,
         sizeof(JH_char),
         worker->buffer_length,
         worker->socket_as_file
      );

   if (written != (worker->buffer_length * sizeof(JH_char)))
   {
      // TODO: Error handling.
      JH_S_ERROR
      (
         stderr,
         "Error while writing to socket."
      );

      return -1;
   }

   err = fputs
   (
      "\n",
      worker->socket_as_file
   );

   if (err == 0)
   {
      JH_S_ERROR
      (
         stderr,
         "Thread could not write anything to socket."
      );

      return -1;
   }

   return 0;
}
