# my-malloc
Malloc Lab - my completed implementation of the malloc lab from Computer Systems - A Programmer's Perspective by David O'Halloran and Randall Bryant of CMU.

This is one of the first C labs I completed - thus, lots of ugly code.  

My implementation creates a dynamic memory allocation API that uses doubly linked lists to store memory blocks.  These blocks are segregated by size - each linked list holds blocks of sizes up to a certain power of 2.  When the user asks for a block of memory of size N, the first free block in the list is grabbed where size is at least N.  If that block's total space minus N has enough space for header/footer tags and at least some amount of bytes of data, that block is split in 2 with the remainder added to the appropriate list.  The other split's address is returned to the user.
