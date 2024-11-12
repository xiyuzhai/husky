update-lean-toolchain:
	curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
update: update-lean-toolchain
	lake update

build: update
	lake build

clean:
	lake clean