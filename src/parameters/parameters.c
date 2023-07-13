#include <stdio.h>
#include <stdlib.h>
#include <errno.h>

#include "../core/index.h"

#include "../error/error.h"

#include "parameters.h"

static int parse_markov_order
(
   struct JH_parameters param [const restrict static 1],
   const char argv [const restrict]
)
{
   long long int input;
   const int old_errno = errno;

   errno = 0;

   input = strtoll(argv, (char **) NULL, 10);

   if
   (
      (errno != 0)
      || (input > (long long int) JH_INDEX_MAX)
      || (input < 1)
   )
   {
      JH_FATAL
      (
         stderr,
         "Invalid or value for parameter 'MARKOV_ORDER', accepted "
         "range is "
         "[2, %lli] (integer).",
         (long long int) JH_INDEX_MAX
      );

      errno = old_errno;

      return -1;
   }

   param->markov_order = (JH_index) input;

   errno = old_errno;

   return 0;
}

enum JH_invocation_objective JH_parameters_initialize
(
   struct JH_parameters param [const restrict static 1],
   int const argc,
   // FIXME: GCC bug with const below. Fixed in 11.3
   const char * argv [const static /*argc*/ 4]
)
{
   param->session = (const char *) NULL;
   param->markov_order = 2;

   switch (argc)
   {
      case 4:
         param->session = argv[1];
         param->database_path = argv[3];

         if (parse_markov_order(param, argv[2]) < 0)
         {
            return JH_PRINTS_HELP;
         }
         else
         {
            return JH_RUNS;
         }

      case 2:
         param->session = argv[1];

         return JH_CLEANS_UP;

      default:
         return JH_PRINTS_HELP;
   }
}

const char * JH_parameters_get_session_name
(
   const struct JH_parameters param [const restrict static 1]
)
{
   return param->session;
}

const char * JH_parameters_get_database_path
(
   const struct JH_parameters param [const restrict static 1]
)
{
   return param->database_path;
}

JH_index JH_parameters_get_markov_order
(
   const struct JH_parameters param [const restrict static 1]
)
{
   return param->markov_order;
}
