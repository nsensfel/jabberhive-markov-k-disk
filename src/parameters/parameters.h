#ifndef _JH_CLI_PARAMETERS_H_
#define _JH_CLI_PARAMETERS_H_

#include "parameters_types.h"

const char * JH_parameters_get_session_name
(
   const struct JH_parameters param [const restrict static 1]
);

JH_index JH_parameters_get_markov_order
(
   const struct JH_parameters param [const restrict static 1]
);

enum JH_invocation_objective JH_parameters_initialize
(
   struct JH_parameters param [const restrict static 1],
   int const argc,
   const char * argv [const static argc]
);

#endif
