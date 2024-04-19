# FLOATING POINT SQUARE ROOT FUNCTIONS

In this repository, you can find all code examples used in an article published in Numerical Algorithms (Springer):

*"Fast and accurate approximation algorithms for computing floating point square root"*

**By:**

 - Paweł Gepner
 - Zbigniew Kokosiński
 - Leonid Moroz
 - Volodymyr Samotyy
 - Mariusz Węgrzyn
 - Nataliia Gavkalova

## BUILD INSTRUCTION

1. Download:  
https://sourceforge.net/projects/half/  
and put header file `half.hpp` in main directory.

2. Make sure default system compiler is set to `clang`.  
Alternatively set `CMAKE_CXX_COMPILER=clang++` environmental variable.

2. Execute:
```bash
$ cmake .
$ make
```

3. Binary can be found in main directory.
