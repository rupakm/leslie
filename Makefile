.PHONY: all LTS TLA clean

all:
	lake build

LTS:
	lake build Leslie_LTS

TLA:
	lake build Leslie

clean:
	lake clean
