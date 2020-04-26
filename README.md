# PDDL to HTN
This project enables translation of a PDDL domain to HTN (JSHOP format for now). The input of translation is a PDDL domain along with a representative instance and mutex invariants computed by FastDownward for example.

## Dependencies
* g++
* python3

## How to run the translator
Change the path to PDDL domains in `htn/domains/` spec file for each domain.
Running `htn/translate_domains.sh` will translate default domains provided `JSHOP2/htndesc/` paths for each domain are created.
