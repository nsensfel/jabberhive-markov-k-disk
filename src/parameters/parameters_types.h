#ifndef _JH_CLI_PARAMETERS_TYPES_H_
#define _JH_CLI_PARAMETERS_TYPES_H_

#include "../core/index_types.h"

enum JH_invocation_objective
{
   JH_PRINTS_HELP,
   JH_CLEANS_UP,
   JH_RUNS
};

struct JH_parameters
{
   const char * restrict session;
   JH_index markov_order;
};

#endif
