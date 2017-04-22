#ifndef _JH_CORE_CHAR_H_
#define _JH_CORE_CHAR_H_

#include "char_types.h"

/* Compares two words. {word_a} does not have to be null terminated. */
/*@
 @ requires null_terminated_string(word_b);
 @ requires ((length(word_a) * sizeof(JH_char)) == word_a_size);
 @ ensures ((\result == 1) || (\result == 0) || (\result == -1));
 @*/
int JH_word_cmp
(
   const JH_char word_a [const static 1],
   const size_t word_a_size,
   const JH_char word_b [const static 1],
   const size_t word_b_size
);

/*
 * Returns the lowercase equivalent of JH_char that are included in ['A','Z'].
 * Other JH_char are returned untouched.
 */
JH_char JH_char_to_lowercase (const JH_char c);

#endif

