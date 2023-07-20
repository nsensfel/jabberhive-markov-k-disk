#include "../pervasive.h"

#include "../error/error.h"

#include "../sequence/sequence.h"

#include "../knowledge/knowledge.h"

#include "../parameters/parameters.h"

#include "server.h"

static int load_reply
(
   struct JH_server_worker worker [const restrict static 1]
)
{
   JH_index rarest_word_id;

   if
   (
      JH_knowledge_rarest_word
      (
         worker->params.server_params,
         worker->params.knowledge,
         worker->sequence_buffer,
         worker->sequence_buffer_length,
         &rarest_word_id,
         worker->socket_as_file
      ) < 0
   )
   {

      JH_S_ERROR(worker->socket_as_file, "Could not find rarest word.");

      return -1;
   }

   JH_DEBUG
   (
      worker->socket_as_file,
      1,
      "Word selected as pillar: %u",
      rarest_word_id
   );

   if
   (
      JH_sequence_create_from
      (
         worker->params.server_params,
         rarest_word_id,
         (size_t *) NULL,
         worker->params.knowledge,
         JH_parameters_get_markov_order(worker->params.server_params),
         &(worker->sequence_buffer),
         &(worker->sequence_buffer_capacity),
         &(worker->sequence_buffer_length),
         worker->socket_as_file
      ) < 0
   )
   {
      JH_S_ERROR
      (
         worker->socket_as_file,
         "Could not create reply from selected word."
      );

      return -1;
   }

   if
   (
      JH_sequence_to_undercase_string
      (
         worker->params.server_params,
         worker->sequence_buffer,
         worker->sequence_buffer_length,
         worker->params.knowledge,
         &(worker->buffer),
         &(worker->buffer_capacity),
         &(worker->buffer_length),
         worker->socket_as_file
      ) < 0
   )
   {
      JH_S_ERROR
      (
         worker->socket_as_file,
         "Could not convert reply sequence to string."
      );

      return -1;
   }

   return 0;
}

static int handle_rpv
(
   struct JH_server_worker worker [const restrict static 1]
)
{
   if
   (
      (worker->buffer[5] == '1')
      &&
      (
         (worker->buffer[6] == ',')
         || (worker->buffer[6] == '\n')
      )
   )
   {
      if (JH_server_worker_send_confirm_protocol_version(worker) < 0)
      {
         return -1;
      }

      return JH_server_worker_send_positive(worker);
   }
   else
   {
      return JH_server_worker_send_negative(worker);
   }
}

static int handle_rps
(
   struct JH_server_worker worker [const restrict static 1]
)
{
   if (JH_server_worker_send_confirm_pipelining_support(worker) < 0)
   {
      return -1;
   }

   return JH_server_worker_send_positive(worker);
}

static int handle_rl
(
   struct JH_server_worker worker [const restrict static 1]
)
{
   if
   (
      JH_sequence_from_undercase_string
      (
         worker->params.server_params,
         (const JH_char *) (worker->buffer + 4),
         (worker->buffer_length - 5),
         worker->params.knowledge,
         &(worker->sequence_buffer),
         &(worker->sequence_buffer_capacity),
         &(worker->sequence_buffer_length),
         worker->socket_as_file
      ) < 0
   )
   {
      return JH_server_worker_send_negative(worker);
   }

   if
   (
      JH_knowledge_learn_sequence
      (
         worker->params.server_params,
         worker->params.knowledge,
         worker->sequence_buffer_length,
         worker->sequence_buffer,
         worker->socket_as_file
      ) < 0
   )
   {
      return JH_server_worker_send_negative(worker);
   }

   return JH_server_worker_send_positive(worker);
}

static int handle_rlr
(
   struct JH_server_worker worker [const restrict static 1]
)
{
   if
   (
      JH_sequence_from_undercase_string
      (
         worker->params.server_params,
         (const JH_char *) (worker->buffer + 5),
         (worker->buffer_length - 6),
         worker->params.knowledge,
         &(worker->sequence_buffer),
         &(worker->sequence_buffer_capacity),
         &(worker->sequence_buffer_length),
         worker->socket_as_file
      ) < 0
   )
   {
      return JH_server_worker_send_negative(worker);
   }

   if
   (
      JH_knowledge_learn_sequence
      (
         worker->params.server_params,
         worker->params.knowledge,
         worker->sequence_buffer_length,
         worker->sequence_buffer,
         worker->socket_as_file
      ) < 0
   )
   {
      return JH_server_worker_send_negative(worker);
   }

   if (load_reply(worker) < 0)
   {
      return JH_server_worker_send_negative(worker);
   }

   if (JH_server_worker_send_generated_reply(worker) < 0)
   {
      return -1;
   }

   return JH_server_worker_send_positive(worker);
}

static int handle_rr
(
   struct JH_server_worker worker [const restrict static 1]
)
{
   if
   (
      JH_sequence_from_undercase_string
      (
         worker->params.server_params,
         (const JH_char *) (worker->buffer + 4),
         (worker->buffer_length - 5),
         worker->params.knowledge,
         &(worker->sequence_buffer),
         &(worker->sequence_buffer_capacity),
         &(worker->sequence_buffer_length),
         worker->socket_as_file
      ) < 0
   )
   {
      JH_S_DEBUG(worker->socket_as_file, 1, "?RR failed at string to sequence.");

      return JH_server_worker_send_negative(worker);
   }

   if (load_reply(worker) < 0)
   {
      JH_S_DEBUG(worker->socket_as_file, 1, "?RR failed at load reply.");
      return JH_server_worker_send_negative(worker);
   }

   if (JH_server_worker_send_generated_reply(worker) < 0)
   {
      return -1;
   }

   return JH_server_worker_send_positive(worker);
}

int JH_server_worker_handle_request
(
   struct JH_server_worker worker [const restrict static 1]
)
{
   if (JH_IS_PREFIX("?RPV ", worker->buffer))
   {
      return handle_rpv(worker);
   }
   else if (JH_IS_PREFIX("?RPS ", worker->buffer))
   {
      return handle_rps(worker);
   }
   else if (JH_IS_PREFIX("?RL ", worker->buffer))
   {
      return handle_rl(worker);
   }
   else if (JH_IS_PREFIX("?RR ", worker->buffer))
   {
      return handle_rr(worker);
   }
   else if (JH_IS_PREFIX("?RLR ", worker->buffer))
   {
      return handle_rlr(worker);
   }
   else
   {
      JH_S_ERROR(worker->socket_as_file, "Unsupported request received.");

      return JH_server_worker_send_negative(worker);
   }

   return 0;
}
