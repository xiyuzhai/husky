#!/bin/bash
git pull
# cloc crates --exclude-dir=node_modules,out,target,dist,forks,package-lock.json,package.json,target-rs --exclude-ext=html,css,json,toml,md
scc ./ --exclude-dir=data,expect-files,tests,target-rs,node_modules,out,target,dist,package-lock.json,package.json,target-rs
