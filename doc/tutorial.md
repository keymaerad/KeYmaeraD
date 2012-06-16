% KeYmaeraD Tutorial

# Introduction

## Overview

KeYmaeraD is a theorem prover for distributed hybrid systems.
KeYmaeraD implements quantified differential dynamic logic (QdL).

KeYmaeraD has two broad design goals. First, it aims to automate and
streamline the difficult parts of theorem proving, making it quick and
easy to find and share proofs in differential dynamic logic and its
variants. Second, with an eye to more advanced users who will be
interested in designing new verification approaches, KeYmaeraD aims to
be a laboratory for experimentation new logics and proof search
techniques. Let us discuss how our design strategy achieves these
goals.

Since the primary activity of a KeYmaeraD user is the construction of
a proof tree, we have put much thought into our representation of that
object. A proof tree in KeYmaeraD has as its root the "goal" node,
i.e. what the user is ultimately trying to prove. From there, the tree
can branch in two ways. And-branching gives rise to "conjunctive
subgoal" nodes, all of which must be proved in order to prove their
parent. Or-branches gives rise "disjunctive subgoal" nodes, only one
of which need be proved in order to prove their parent. All of the
nodes are stored as objects in heap memory and are displayed through a
graphical user interface. Arbitrarily many or-branches can coexist at
any time, at any level of the tree. In this way, multiple approaches
to proving a single formula can be attempted at the same time. When
any of them succeeds, the now-irrelevant others are automatically
cancelled. In this way, we sidestep entirely the difficult issue of
backtracking, a pain point in many other theorem provers.

The only way the user can modify the proof tree is through a
predefined set of proof rules. Application of these rules can be
scripted and combined in sophisticated ways with "tactics," a notion
we have adopted from the LCF style of theorem proving. The rules and
tactics are modular and separated from the core implementation of
KeYmaeraD, allowing us to easily experiment with new logics and search
techniques.

Since efficiency is one of our priorities, we have developed a
distributed backend for KeYmearaD. We have found that the most
expensive part of theorem proving for hybrid systems is closing the
arithmetic subgoals at the leaves of the proof tree. A typical proof
search at our current scale will spawn tens or hundreds of these
tasks, none of which are dependent on any other. We have therefore
designed KeYmareaD to exploit this potential parallelism.

For several reasons, including our desire to ensure that we will
continue to be able to scale KeYmaeraD to ever larger and more
difficult problems, we have given KeYmaeraD a somewhat unconventional
concurrency model. There is no shared state between threads; instead,
we take a purely message-passing approach. This makes the
implementation easier to understand. It also allows us to easily
experiment with different kinds of frontends. A command-line interface
and graphical interface already exist. In the future, if we want a web
interface---which might be very useful if we want to prove a single
theorem over the course of many days---such a thing should be
straightforward to implement.

## Refereneces

KeYmaeraD is described in

  David W. Renshaw, Sarah M. Loos, and André Platzer.
  Distributed theorem proving for distributed hybrid systems.
  In Shengchao Qin and Zongyan Qiu, editors, International Conference
  on Formal Engineering Methods, ICFEM'11, Durham, United Kingdom,
  Proceedings, volume 6991 of LNCS. Springer, 2011.

KeYmaeraD implements the logic and proof calculus introduced in 

  André Platzer.
  Quantified differential dynamic logic for distributed hybrid systems.
  In Anuj Dawar and Helmut Veith, editors, Computer Science Logic,
  19th EACSL Annual Conference, CSL 2010, Brno, Czech Republic, August 23-27, 2010.
  Proceedings, volume 6247 of LNCS, pages 469-483. Springer, 2010.

For more information, also see

  http://symbolaris.com/logic/disthysys.html


# Getting Started

## Installation

KeYmaeraD is currently supported on Mac OSX and Linux.
To compile KeYmaeraD, you will need:

* Scala 2.9.0 or higher
* Mathematica

To set up, define the following environment variables: (in parentheses
are appropriate values on my Mac OSX system.)

JLINK (=/Applications/Mathematica.app/SystemFiles/Links/JLink)

MATHKERNEL (=/Applications/Mathematica.app/Contents/MacOS/MathKernel)

To compile, navigate to the KeYmaeraD root directory and type `make`.
To run, use the `runprover` script:

```
./runprover [-workers (# workers)]  [-nogui]
```

The default number of workers is the number of available processors on
your machine, determined by a call to
`Runtime.getRuntime().availableProcessors()`.  This command will
launch these workers as subprocesses.  It is important that you do not
start more workers than the number of instances of Mathematica you are
authorized to run simultaneously. Otherwise, KeYmaeraD will deadlock
as it waits for Mathematica to load.

You may also start workers manually with the "runworker" command:

```
./runworker [-c jobmaster address] [-cp jobmaster port]
```

The jobmaster port is determined upon startup
of the prover and can be read from its output.

## A Simple Example

Start up KeYmaeraD by typing `./runprover`.  On startup, KeYmaeraD
automatically loads the file "examples.simple.dl". Once the GUI loads,
press Cmd-d. You should see a proof tree grow and eventually get
closed, as indicated by green checkmarks.  To quit KeYmaeraD, close
the GUI window.

## A More Involved Example

When learning how KeYmaeraD works, it helps
to start with just the commandline interface. 

```
./runprover -nogui
```

After a few moments, you will be presented with a `scala>` prompt. The
way to communicate with the main KeYmaeraD actor is through the `dl`
function, as in the following command, which loads the file
"examples/simple.dl".

```
scala> dl('load, "examples/simple.dl")
```

At any time, you can look at the current proof node by typing
`dl('here)`.  In the current case, you should see something like:


```
{  }  |- [x() := 0; (x() := x() + 1) ++ (x() := 40)] x() > 0
OrNode
rule = loaded from examples/simple.dl
nodeID = 2
status = Open
parent = None
children = List()
```

The top line is the theorem we are trying to prove.

```
scala> dl('rule, seq, RightP(0))
success
```

```
scala> dl('here)
{  }  |- [x() := 0; (x() := x() + 1) ++ (x() := 40)] x() > 0
OrNode
rule = loaded from examples/simple.dl
nodeID = 2
status = Open
parent = None
children = List(3)
```

Now our node has a child of ID 3.  We may navigate to that node like
with the command `dl('goto, 3)`.  Once there, we may try to apply
other proof rules; in this case `assign` is what would make progress.
We may also apply a tactic, which finished up the proof in this case.

```
scala> dl('tactic, easiestT)
```

If we try `dl('here)` again, we see that the status is `Proved`.
Remember when we pressed Cmd-d in the GUI in the previous example?
What that actually did was exactly what we just did here: apply the
`easiestT` tactic. We are done and we may exit with `dl('quit)`.



# Proving Theorems

## Proof Rules

rules.scala

## Tactics

tactics.scala

## Writing Tactic Scripts

Tactic scripts are a way to save your work on in-progress and
completed proofs. If you are trying to prove "problem.dl" you may
create a file "problem.dl.scala" which will contain scala code. Your
script should consist of an object named `Script` with a value named
`main` that has type `Tactic`. Then, whenever you load
"problem.dl.scala", in addition to "problem.dl" loading, like normal,
the script will be compiled and loaded so that you have access to it
on the command line. This may take several moments; a success message
will appear on the command line when compilation is complete. At this
point, if you press Cmd-u in the GUI, the `main` tactic will be 
executed.



# Contributing

If you find any bugs, please let the developers know, either by
submitting an "issue" to the github repository or by direct email.

If you are doing development on KeYmaeraD, you may want to use the
test suite. You will need to download scalatest (www.scalatest.org) to
do so. To compile the tests, make sure that tests/scalatest.jar is a
symbolic link to your copy of scalatest, and type "make tests".