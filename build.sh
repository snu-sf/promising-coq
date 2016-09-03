#!/usr/bin/env bash

mkdir -p .build
rsync -avl --delete --exclude '*.vo' --exclude '*.vio' --exclude '*.v.d' --exclude '*.glob' --exclude '.*.aux' lib src Makefile _CoqProject .build
cd .build
if [ -z $* ]
then
  make -j -f Makefile build
else
  make -j -f Makefile $*
fi
