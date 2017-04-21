#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
	/* Team name */
	"copy to understand",
	/* first members name */
	"brian",
	"asdf@asdf.com",
	"",
	""
	
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to nearest multiple of ALIGNMENT */

#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* additional macros */

#define WSIZE 8
#define DSIZE 16
#define INITCHUNKSIZE (1<<6)
