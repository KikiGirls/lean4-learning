# Aristotle CLI

Installed SDK: `aristotlelib`

## Activate

```bash
source /Users/kikigirl/Desktop/lean4-learning/tools/Aristotle/.venv/bin/activate
```

The command is also linked at:

```bash
~/.local/bin/aristotle
```

## Authentication

Create an API key at <https://aristotle.harmonic.fun>, then set:

```bash
export ARISTOTLE_API_KEY="your-api-key-here"
```

To persist it for new zsh terminals:

```bash
echo 'export ARISTOTLE_API_KEY="your-api-key-here"' >> ~/.zshrc
source ~/.zshrc
```

## Common Commands

Fill sorries in a Lean project:

```bash
aristotle submit "Fill in all sorries in this project" --project-dir /Users/kikigirl/Desktop/lean4-learning/Proj/mordell-Archon --wait
```

Formalize a document:

```bash
aristotle formalize paper.tex --wait --destination output.tar.gz
```

List recent Aristotle projects:

```bash
aristotle list --limit 10
```
