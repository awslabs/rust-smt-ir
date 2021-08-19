# Solvers

The online features used by some of the predictive models are a function of the theory and conflict lemmas that are outputted while CVC4 is running. However it is not possible to output these with the standard CVC4 binaries available online. Hence it must be built from source.

The build instructions for CVC4 are [here](https://github.com/CVC4/CVC4-archived/blob/master/INSTALL.md). They can be followed exactly except that the option ``--tracing`` must be passed to the script ``configure.sh``. (I also passed the options ``--gpl --cln`` as I ran into issues with GMP. This is not necessary but may be helpful if you run into similar issues.)

Finally, as I was using the results from SMT Comp 2020 to train my models, I used the version of CVC4 which was submitted to the competition (a pre-release of version 1.8) which is available [here](https://github.com/cvc5/cvc5/tree/smtcomp2020).
