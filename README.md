# Branch Number Formalization

This project formalizes Theorem 1 from [*A New Algorithm for Computing Branch Number of Non-Singular Matrices over Finite Fields*](https://arxiv.org/pdf/2405.07007) in Lean 4.

## Viewing the Blueprint

The blueprint is a web-based documentation of the formalization, showing the mathematical content alongside links to the Lean code.

### Step 1: Install leanblueprint

Install the leanblueprint CLI tool using pip:

```bash
pip install leanblueprint
```

For more information, see the [leanblueprint documentation](https://github.com/PatrickMassot/leanblueprint).

### Step 2: Build the web version

```bash
leanblueprint web
```

### Step 3: Serve the blueprint locally

```bash
leanblueprint serve
```

Then visit `http://0.0.0.0:8000/` in your browser.

## Building the Lean Code

To build and verify the Lean formalization:

```bash
lake exe cache get  # Download Mathlib cache (recommended)
lake build          # Build the project
```
