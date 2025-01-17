# Formalising Mathematics

Repository for the Jan-Mar 2021 TCC course on formalising mathematics.

# What is this?

In this course, we're going to be turning maths theorems into levels of a computer game called Lean. We'll start off with proving basic stuff like composite of injective functions is injective. We'll move on to harder mathematics as the course goes on. The course comprises 8 workshops. You don't have to do all the questions in each workshop.

# Prerequisites?

You should know some mathematics. For example if you're a second year undergraduate you should easily be able to be able to solve the levels from first few weeks.

You should also get Lean 3 and the community tools installed on your computer. This is harder than it sounds, unfortunately. [Here are the instructions](https://leanprover-community.github.io/get_started.html) .

# How to play?

Assuming you have Lean and the user tools installed, first install the repository by firing up a command line, navigating (using `pwd` and `cd`) to the directory you want to install this project in, and then typing

```
leanproject get ImperialCollegeLondon/formalising-mathematics

code formalising-mathematics
```

and then open up some of the files in `src/week1` and you're up and running. Look at the `README.md` file in `src/week1` for more instructions. Fill in the `sorry`s. Try a couple of levels of the [natural number game](http://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game/) if you're not sure what's going on.

# I failed to install Lean

Well, you can always play along using the community web editor. Here are the four worlds for week 1. You might have to wait for a minute or so until "Lean is busy..." becomes "Lean is ready!".

[logic](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2Fformalising-mathematics%2Fmaster%2Fsrc%2Fweek_1%2FPart_A_logic.lean)

[sets](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2Fformalising-mathematics%2Fmaster%2Fsrc%2Fweek_1%2FPart_B_sets.lean)

[functions](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2Fformalising-mathematics%2Fmaster%2Fsrc%2Fweek_1%2FPart_C_functions.lean)

[relations](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2Fformalising-mathematics%2Fmaster%2Fsrc%2Fweek_1%2FPart_D_relations.lean)