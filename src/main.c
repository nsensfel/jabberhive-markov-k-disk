#include <stdio.h>

#include "parameters/parameters.h"

#include "server/server.h"

#include "pervasive.h"

static void print_help (const char runnable [const restrict static 1])
{
   printf
   (
      "JabberHive - K-order Markov Chain Server\n"
      "Software Version %d\n"
      "Protocol Version %d\n"
      "\nUsages:\n"
      "   SERVER:\t%s SESSION_NAME MARKOV_ORDER\n"
      "   CLEAN UP:\t%s -c SESSION_NAME\n"
      "   SHOW HELP:\tAnything else.\n"
      "\nParameters:\n"
      "   SESSION_NAME:\tValid UNIX socket.\n"
      "   MARKOV_ORDER:\tPositive integer, greater than 1.\n",
      JH_SERVER_VERSION,
      JH_PROTOCOL_VERSION,
      runnable,
      runnable
   );
}

int main (int const argc, const char * argv [const static argc])
{
   struct JH_parameters params;

   switch (JH_parameters_initialize(&params, argc, argv))
   {
      case JH_RUNS:
         return JH_server_main(&params);

      default:
      case JH_PRINTS_HELP:
         print_help(argv[0]);
         return 0;
   }
}
