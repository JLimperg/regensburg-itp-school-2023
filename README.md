# A Taste of Lean 4

Lecture series at the 2023 International Summer School on Interactions of Proof
Assistants and Mathematics in Regensburg

## Installing Lean 4

To install Lean 4, follow the instructions
[here](https://leanprover-community.github.io/get_started.html). After you've
done so, you should have the following software available:

- `git` (the version control system)
- `elan` (the version manager for Lean 4, providing the `lake` executable, among
   others)
- Visual Studio Code (VSCode, an editor) with the Lean 4 extension
  - Alternatively, Emacs and Neovim also have some degree of Lean support.

## Following Along with the Lectures

This repository contains a Lean project with the code that I'll be discussing
during the lectures. If you want to follow along, execute these steps (which
also work for any other Lean package):

- Clone this repository. In a terminal (on Windows, use Git Bash) type
  ```text
  git clone https://github.com/JLimperg/regensburg-itp-school-2023.git
  ```
  and hit enter. This will create a directory `regensburg-itp-school-2023`.
- Switch to this directory:
  ```text
  cd regensburg-itp-school-2023
  ```
- Download dependencies, including cached binary files:
  ```text
  lake exe cache get
  ```
  This will download the appropriate version of Lean, the appropriate version
  of this project's dependencies, and compiled files for the dependencies.
  You can also skip this step, but then the next step will take a very long
  time.
- Build the project:
  ```text
  lake build
  ```
  This will compile the project (and its dependencies, but if you've executed
  the previous step, you already have compiled files for the dependencies).
  Some warnings are expected.
- Start VSCode and open the *folder* `regensburg-itp-school-2023` (*not* a
  specific file in that folder).
- Select the file `Talk/01Logic.lean`. This is some of the code I'll be
  discussing during the lecture. Lean should automatically start and blue or
  green squiggly lines should appear at various places in the file.

See also [these
instructions](https://leanprover-community.github.io/install/project.html#working-on-an-existing-project).

## Exercises

The Lean community has developed several learning resources, differing in target
audience and pace. During the exercise class, I suggest you work on whichever of
these resources best matches your learning objectives. Yet more resources are
available [here](https://leanprover-community.github.io/learn.html).

### Mathematically Oriented

#### Natural Number Game

https://adam.math.hhu.de/#/g/hhu-adam/NNG4

A very gentle introduction focusing on basic tactics and induction over
natural numbers. Runs in a browser, no installation required.

#### A Glimpse of Lean

https://github.com/PatrickMassot/GlimpseOfLean

A mathematically oriented tutorial of 2-3h. Can be run locally or in a browser.
To run it locally, clone the above Git repository and follow [the same steps as
for my lecture project](#following-along-with-the-lectures).

#### Mathematics in Lean

https://leanprover-community.github.io/mathematics_in_lean/

The de facto standard interactive textbook about doing mathematics in Lean. Can
be run locally or in a browser. To run it locally, clone [this Git
repository](https://github.com/leanprover-community/mathematics_in_lean) and
follow [the same steps as for my lecture
project](#following-along-with-the-lectures). Many warnings are expected at the
`lake build` step.

#### The Mechanics of Proof

https://hrmacbeth.github.io/math2001/

Lecture notes for an early undergraduate mathematics course. Shorter and gentler
than Mathematics in Lean. Can be run locally or in a browser. To run it locally,
clone [this Git repository](https://github.com/hrmacbeth/math2001) and follow
[the same steps as for my lecture project](#following-along-with-the-lectures).

### Computer Science Oriented

#### Functional Programming in Lean

https://leanprover.github.io/functional_programming_in_lean/

A textbook about functional programming in Lean. The code examples can be found
[here](https://github.com/leanprover/fp-lean).

#### Logical Verification (2023 edition)

https://github.com/blanchette/logical_verification_2023

Lecture notes and code for an MSc-level computer science course using Lean, with
a focus on proofs about programming languages. To run the code, clone the above
Git repository and follow [the same steps as for my lecture
project](#following-along-with-the-lectures). Many warnings (and even errors in
some exercise sheets) are expected at the `lake build` step.

#### Theorem Proving in Lean 4

https://leanprover.github.io/theorem_proving_in_lean4/

The official Lean 4 textbook. Discusses the Lean system in a systematic fashion
without focusing on any particular application.

## Resources

- [Lean Zulip](https://leanprover.zulipchat.com): very active chat server. Basic
  questions are very welcome; post them in a new topic in the `#new members`
  stream.
- [leanprover-community](https://leanprover-community.github.io): lots of
  documentation, though some of it is outdated.
- [mathlib
  overview](https://leanprover-community.github.io/mathlib-overview.html):
  high-level description of the mathematics that's currently in mathlib.
- [mathlib 4 docs](https://leanprover-community.github.io/mathlib4_docs/): API
  documentation for mathlib as well as Lean 4 and the standard library.
- [Loogle](https://loogle.lean-fro.org/): search engine for Lean theorems.
- [Lean 4 manual](https://leanprover.github.io/lean4/doc/): official Lean 4
  reference manual.
- [Metaprogramming
  book](https://github.com/leanprover-community/lean4-metaprogramming-book):
  work-in-progress textbook about Lean 4 metaprogramming.
