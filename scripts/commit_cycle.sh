#!/usr/bin/env bash
set -e
git add state/ RrLean/ agents/
git commit -m "cycle: $1"
git push
