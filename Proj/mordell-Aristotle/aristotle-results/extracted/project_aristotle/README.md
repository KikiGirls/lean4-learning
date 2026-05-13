This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# mordell-Aristotle

Lean 4 project for Mordell formalization experiments with Aristotle.

## Build

```bash
lake build
```

## Aristotle

Set your Aristotle API key before submitting jobs:

```bash
export ARISTOTLE_API_KEY="your-api-key-here"
```

Then submit this project:

```bash
aristotle submit "Fill in all sorries in this project" --project-dir /Users/kikigirl/Desktop/lean4-learning/Proj/mordell-Aristotle --wait
```
