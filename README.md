# Lean 4 Autograder

This project provides a Lean 4 autograder that works with [Gradescope](https://gradescope-autograders.readthedocs.io/en/latest/). 
It checks that students have provided proof terms with the correct type or have created equal `Expr`s up to definitional equality. 
The autograder can check theorems, functions, propositions, and instances. It *cannot* grade inductive types or structures.

## Setup 

More detailed instructions can be found in the [Lean autograder shell](https://github.com/robertylewis/lean4_autograder), but here is a brief overview.

First, set up a course repository on GitHub. Add this project, autograder-main, as a lake dependency. 
Then, use [autograder shell](https://github.com/robertylewis/lean4_autograder) to create the zip file that actually gets uploaded to Gradescope.
This project is meant to work with MathLib assignments, so for a good Gradescope performance, their container must have at least 2.0 CPU and 3.0GB RAM. 
Otherwise, you'll get inscrutable errors when it runs out of memory. 
After this is all set up, students will only need to submit a file to Gradescope.

For an example, see the repository [fpv2023](https://github.com/BrownCS1951x/fpv2023). 
The lakefile of this project imports this autograder project.
To create a Gradescope assignment for HW1, edit the configuration file in the autograder shell 
to point at `Homeworks/Homework1.lean` in that repository, run the `make_autograder.sh` script, 
and upload the resulting zip file to Gradescope.
Students would then submit *only* their `Homework1.lean` file to Gradescope.

## Autograding 

The two main attributes are `@[autogradedProof pts]` and `@[autogradedDef pts]`.

`@[autogradedProof pts]` is used for theorems. 
It checks that the student has provided a `sorry`-free proof of the theorem that does not use any nonstandard axioms.
Extra axioms can be allowed with the `@[legalAxiom]` attribute.
Note that the solution file needs the theorem statement, but does not need a proof of the theorem.

For example, the autograder would award 1 point for a proof of `th1`.

```lean
@[autogradedProof 1]
theorem th3 (h : ¬q → ¬p) : (p → q) := sorry
```

`@[autogradedDef pts]` is used for functions, propositions, and instances.
The correct definition of the theorem is needed in the solution file.
The autograder will try to prove that the student's definition is equal to the solution definition using `Eq.refl`, `HEq.refl`, and various tactics.
A default list of tactics for the assignment can be set using `@[defaultTactics #[]]` over the `setDefaultTactics` function.
Individual problems can override the default list of tactics using the `@[validTactics #[]]` attribute. 

For example, the autograder would award 2 points for a definition of `reverse` that is equal to the solution definition below.
It will only use `rfl` to prove the equality.

```lean
@[defaultTactics #[rfl, simp]] 
def setDefaultTactics := () 

@[autogradedDef 2, validTactics #[rfl]]
def reverse {α : Type} : List α → List α
  | List.nil        => List.nil
  | List.cons x xs  => List.append (reverse xs) [x]
```

## Testing the Autograder

To test the autograder locally, build the project and run the autograder with the `--local` flag.
This will print the results of the autograder to the console instead of producing a JSON file.

```lean
lake exe autograder --local path/to/submission.lean path/to/solutions.lean
```

To test the autograder, build the project and run the autograder with the `--test` flag.
This will check the submission sheet for the `[@autograderTest status name]` attribute.

The `autograderTest` attribute is used to test multiple possible submissions to a problem
without editing the master solutions file. The `status` paramenter is the expected status 
of the test and should either be `passes` or `fails`. The `name` parameter is the name of 
the problem in the solutions files. 

Here is an example of a solution and test file for the `reverse` function.

```lean
-- Solutions file
@[autogradedDef 1, validTactics #[custom_simp]]
def reverse {α : Type} : List α → List α
  | List.nil        => List.nil
  | List.cons x xs  => List.append (reverse xs) [x]
```

```lean
-- Test file
-- Exactly the same
@[autograderTest passes `reverse]
def reverse {α : Type} : List α → List α
  | List.nil        => List.nil
  | List.cons x xs  => List.append (reverse xs) [x]

-- Different but correct implementation
@[autograderTest passes `reverse]
def reverse2 {α : Type} (lst: List α) : List α := 
  lst.foldr (fun x acc => acc ++ [x]) []

-- Wrong implementation
@[autograderTest fails `reverse]
def reverse3 {α : Type} : List α → List α
  | List.nil        => List.nil
  | List.cons x xs  => List.append [x] (reverse3 xs)
```
