# PDDL to HTN
This project enables translation of a PDDL domain to HTN (JSHOP format for now). The input of translation is a PDDL domain along with a representative instance and mutex invariants computed by FastDownward for example.

## Dependencies
* g++
* python3

## How to run the translator
Change the path to PDDL domains in `htn/domains/` spec file for each domain.
Running `htn/translate_domains.sh` will translate default domains provided `JSHOP2/htndesc/` paths for each domain are created.

## References

Lotinac, Damir, and Anders Jonsson. "Constructing hierarchical task models using invariance analysis." Proceedings of the Twenty-second European Conference on Artificial Intelligence. IOS Press, 2016. [pdf](https://pdfs.semanticscholar.org/93e8/f422f8ce4ab102b2a4d2e4cd57af19e605b8.pdf)

Lotinac, Damir. Novel approaches for generalized planning. Diss. Universitat Pompeu Fabra, 2017. [pdf](https://www.tdx.cat/handle/10803/458525#page=1)