#!/bin/bash
katsura_solver_path="/home/opam/repos/hflmc2-ls/_build/default/bin/main.exe"
dune exec ./bin/muapprox_main.exe -- "$@"
