# Branch Number Formalization

This project formalizes Theorem 1 from [*A New Algorithm for Computing Branch Number of Non-Singular Matrices over Finite Fields*](https://arxiv.org/pdf/2405.07007) in Lean 4.

## Setup

### Prerequisites

Leanblueprint requires graphviz. Install it based on your operating system:

**macOS:**
```bash
brew install graphviz
```
(Requires [Homebrew](https://brew.sh))

**Ubuntu/Debian:**
```bash
sudo apt install graphviz libgraphviz-dev
```

**Other systems:** See the [pygraphviz installation guide](https://pygraphviz.github.io/documentation/stable/install.html).

### Install leanblueprint

```bash
pip install leanblueprint
```

For more information, see the [leanblueprint documentation](https://github.com/PatrickMassot/leanblueprint).

## Useful Commands

Build and serve the blueprint locally:
```bash
leanblueprint web
leanblueprint serve
```
Then visit `http://0.0.0.0:8000/` in your browser.

Build the PDF version:
```bash
leanblueprint pdf
```

Build the Lean code:
```bash
lake exe cache get  # Download Mathlib cache (recommended)
lake build          # Build the project
```
