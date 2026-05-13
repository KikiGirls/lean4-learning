# Mistral Vibe CLI for Leanstral

Installed CLI: `vibe 2.9.5`

The executable is linked at:

```bash
~/.local/bin/vibe
```

## Setup

Run:

```bash
vibe --setup
```

Then start Vibe:

```bash
vibe --workdir /Users/kikigirl/Desktop/lean4-learning/Proj/mordell-Aristotle --trust
```

Inside the Vibe interactive session, run:

```text
/leanstall
```

This installs the Lean mode and configures Leanstral as a Vibe agent/model.

## Quick Programmatic Check

```bash
vibe -p "Explain the Lean theorem in MordellAristotle.Basic" \
  --workdir /Users/kikigirl/Desktop/lean4-learning/Proj/mordell-Aristotle \
  --trust
```
