# Lean 4 Autograder

This project provides a Lean 4 autograder that works with [Gradescope](https://gradescope-autograders.readthedocs.io/en/latest/).

To generate the files Gradescope needs, this project uses a repository on GitHub that must contain a template of the assignment the students will receive. This project retrieves from the template how many points each exercise is worth. Thus, the template must follow the following pattern:

```lean
@[autograded 2]
theorem th3 (h : ¬q → ¬p) : (p → q) := sorry
```

It is **NOT** necessary to edit `autograder_config.json` unless you want to use the helper scripts.

### Gradescope Container Minimum Specifications

This project is meant to work with MathLib assignments, so for a good Gradescope performance, their container must have at least 2.0 CPU and 3.0GB RAM.

## Usage

Add this project as a lake dependency to your course project. Then, set up the [autograder shell](https://github.com/robertylewis/lean4_autograder) for use with an assignment in that course project.

For an example, see [fpv2023](https://github.com/BrownCS1951x/fpv2023). 
The lakefile of this project imports this autograder project.
To create a Gradescope assignment for HW1, I would edit the configuration file in the autograder shell 
to point at `Homeworks/Homework1.lean` in that repository,
run the `make_autograder.sh` script, 
and upload the resulting zip file to Gradescope.
Students would then submit *only* their `Homework1.lean` file to Gradescope.
