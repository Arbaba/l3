#ifndef FAIL_H
#define FAIL_H

/* A method to indicate vm failure */
extern void fail(char* msg, ...) __attribute__ ((noreturn));

#endif // FAIL_H
