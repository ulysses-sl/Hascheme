#!/bin/bash
ghc -package parsec -XExistentialQuantification -o lisp replparser.hs
ghc -package parsec -XExistentialQuantification -o parser varfunc.hs


