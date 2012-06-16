% KeYmaeraD Tutorial

# Introduction

This tutorial is about the KeYmaeraD theorem prover.

# Getting Started

## Installation

KeYmaeraD is currently supported on Mac OSX and Linux.
To compile KeYmaeraD, you will need:
   - Scala 2.9.0 or higher
   - Mathematica

To set up, define the following environment variables: (in parentheses
are appropriate values on my Mac OSX system.)

JLINK (=/Applications/Mathematica.app/SystemFiles/Links/JLink)
MATHKERNEL (=/Applications/Mathematica.app/Contents/MacOS/MathKernel)

To compile, navigate to the KeYmaeraD root directory and type "make".

To run, use the "runprover" script:

~~~~
./runprover [-workers (# workers)]  [-nogui]
~~~~

The default number of workers is the number of available processors on
your machine, determined by a call to Runtime.getRuntime().availableProcessors().
This command will launch these workers as subprocesses.

You may also start workers manually with the "runworker" command:

~~~~
./runworker [-c jobmaster address] [-cp jobmaster port]
~~~~

The jobmaster port can be read from the output of the prover.

## A First Example

~~~~
dl('load, "examples/simple.dl")
~~~~

# Proving Theorems

## Proof Rules

## Tactics

## Contributing

If you find any bugs, please let the developers know.

If you are doing development on KeYmaeraD, you may want to use the
test suite. You will need to download scalatest (www.scalatest.org) to
do so. To compile the tests, make sure that tests/scalatest.jar is a
symbolic link to your copy of scalatest, and type "make tests".