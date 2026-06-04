{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  # The Nix packages provided in the environment
  packages = [
    pkgs.python3
    pkgs.python3Packages.pip
    # Needed to build pygraphviz (a leanblueprint dependency) from source
    pkgs.graphviz
    pkgs.pkg-config
    # Whatever other packages are required
  ];
  shellHook = ''
    if [ ! -d .venv ]; then
      python -m venv .venv
    fi
    source .venv/bin/activate
    # Install/refresh MCP server used by Claude Code (.mcp.json points at .venv/bin/lean-lsp-mcp)
    python -m pip install --quiet --upgrade lean-lsp-mcp

    # NixOS has no /bin/bash. Rewrite hardcoded shebangs in the lean4-skills
    # plugin so Claude Code hooks can exec them. Idempotent; re-runs on every
    # shell entry so the patch self-heals after a plugin update.
    for f in $HOME/.claude/plugins/cache/lean4-skills/lean4/*/hooks/*.sh \
             $HOME/.claude/plugins/cache/lean4-skills/lean4/*/lib/scripts/*.sh; do
      [ -f "$f" ] && sed -i '1s|^#!/bin/bash$|#!/usr/bin/env bash|' "$f"
    done
  '';
}
