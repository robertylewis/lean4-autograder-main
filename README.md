# Lean 4 Autograder

This project provides a Lean 4 autograder that works with [Gradescope](https://gradescope-autograders.readthedocs.io/en/latest/). 
It checks that students have provided correct proof terms or have created the correct `Expr` up to definitional equality. 
This includes theorems, funcitons, propositions, and instances. 

The autograder does *not* use test cases. Additionally, it cannot grade inductive types or structures.

## Setup 

First, set up a solutions repository on GitHub.
Add this project, autograder-main, as a lake dependency to the project. 
Then, set up the [autograder shell](https://github.com/robertylewis/lean4_autograder) for a specific assignment in repository.
The autograder shell creates the zip file that actually gets uploaded to Gradescope.
This project is meant to work with MathLib assignments, so for a good Gradescope performance, their container must have at least 2.0 CPU and 3.0GB RAM. 
Otherwise, you'll get inscrutable errors when it runs out of memory. 
Students will only need to submit a file to Gradescope.

Note that it is **NOT** necessary to edit `autograder_config.json` unless you want to use the helper scripts.

For an example, see the submissions repository [fpv2023](https://github.com/BrownCS1951x/fpv2023). 
The lakefile of this project imports this autograder project.
To create a Gradescope assignment for HW1, I would edit the configuration file in the autograder shell 
to point at `Homeworks/Homework1.lean` in that repository, run the `make_autograder.sh` script, 
and upload the resulting zip file to Gradescope.
Students would then submit *only* their `Homework1.lean` file to Gradescope.

## Autograding 

The two main attributes are `@[autogradedProof pts]` and `@[autogradedDef pts]`.

`@[autogradedProof pts]` is used for theorems. 
It checks that the student has provided a `sorry`-free proof of the theorem that does not use any nonstandard axioms.
Extra axioms can be allowed with the `@[legalAxiom]` attribute.

Note that you only need to write the theorem statement in the solution file. 
You do not need to write the proof.

For example, the autograder would award 1 point for a proof of `th1`.

```lean
@[autogradedProof 1]
theorem th3 (h : ¬q → ¬p) : (p → q) := sorry
```

`@[autogradedDef pts]` is used for functions, propositions, and instances.
You need to provide the correct definition in the solution file.
The autograder will try to prove that the student's definition is equal to the solution definition using `Eq.refl`, `HEq.refl`, and various tactics.
You can set a default list of tactics for the assignment by setting `@[defaultTactics #[]]` over the `setDefaultTactics` function.
You can also explicitly set `@[validTactics #[]]` over individual problems.

For example, the autograder would award 2 points for a definition of `reverse` that is equal to the solution definition below.
It will try to use `rfl` and `simp` to prove the equality.

```lean
@[defaultTactics #[rfl, simp]] 
def setDefaultTactics := () 

@[autogradedDef 2]
def reverse {α : Type} : List α → List α
  | List.nil        => List.nil
  | List.cons x xs  => List.append (reverse xs) [x]
```

## Testing the Autograder

While the autograder is designed to be used with Gradescope, you can test it locally.

The `[@autograderTest status name]` attribue can be used to test multiple possible solutions to a problem at once.
The `status` paramenter is the expected status of the test and should be either `passes` or `fails`.
The `name` parameter is the name of the problem in the solutions files. 

After setting up the solution and test files, you can run the autograder with the following command: `lake exe autograder --test`.

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

For an alternate way to test, run:
```lake exe autograder --local path/to/submission.lean path/to/solutions.lean```

Right now this will save the results in `../results/results.json`,
or error if this directory doesn't exist. Fixing this is a todo!
