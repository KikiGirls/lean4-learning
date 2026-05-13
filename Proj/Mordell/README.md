# Mordell

## Blueprints

This project now has two blueprint views under `docs/blueprint/`:

* `mordell_blueprint_simplified.svg` and `.png`: a paper-ready simplified dependency graph of the principal proof chain.
* `mordell_blueprint_full.html`: a complete interactive declaration graph extracted from the Lean source files.

Regenerate them with:

```bash
python3 docs/generate_blueprints.py
```

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
