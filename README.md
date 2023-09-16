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
- Download the dependencies of this project:
  ```text
  lake update
  ```
  This will download the dependencies of my code, notably a specific version of
  Lean 4 and a specific version of mathlib, the Lean mathematical library.
- Download cached mathlib files:
  ```text
  lake exe cache get
  ```
  This will download compiled files for this mathlib version from the mathlib
  cache server. You can also skip this step, but then the next step will take
  a very long time.
- Build the project:
  ```text
  lake build
  ```
  This will compile the project's dependencies and the project itself. Some
  warnings are expected.
- Start VSCode and open the *folder* `regensburg-itp-school-2023` (*not* a
  specific file in that folder).
- Select the file `Talk/Lecture.lean`. This is the code I'll be discussing
  during the lecture. Lean should automatically start and blue or green squiggly
  lines should appear at various places in the file.

## Exercises

To be announced (hopefully by the start of the school).
