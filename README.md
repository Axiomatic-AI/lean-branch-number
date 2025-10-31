# Branch Number Formalization

This project formalizes Theorem 1 from [*A New Algorithm for Computing Branch Number of Non-Singular Matrices over Finite Fields*](https://arxiv.org/pdf/2405.07007) in Lean 4.

## Viewing the Blueprint

The blueprint is a web-based documentation of the formalization, showing the mathematical content alongside links to the Lean code.

### Option 1: View Pre-built HTML (No installation required)

The blueprint is already built in the `blueprint/web/` folder. To view it:

**Open directly in browser:**
```bash
open blueprint/web/index.html
```

**Or serve with Python:**
```bash
cd blueprint/web
python3 -m http.server 8080
# Then visit http://localhost:8080 in your browser
```

### Option 2: Rebuild the Blueprint

If you want to rebuild the blueprint from source (requires `leanblueprint` installed):

```bash
leanblueprint web    # Rebuild web version
leanblueprint pdf    # Rebuild PDF version
leanblueprint serve  # Build and serve at http://localhost:8000
```

## Building the Lean Code

To build and verify the Lean formalization:

```bash
lake exe cache get  # Download Mathlib cache (recommended)
lake build          # Build the project
```

## Project Structure

- `LeanCryptography/lean_certificate.lean` - Main formalization
- `blueprint/src/` - Blueprint LaTeX source files
- `blueprint/web/` - Pre-built web version of blueprint
- `blueprint/print/` - Pre-built PDF version of blueprint

## Requirements

- **To view the blueprint:** Any modern web browser (no dependencies)
- **To rebuild the blueprint:** [leanblueprint](https://github.com/PatrickMassot/leanblueprint) and LaTeX
- **To build the Lean code:** [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (version specified in `lean-toolchain`)
