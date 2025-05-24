# lean-cpc-checker

To call cvc5 on an unsat SMT-LIB v2 query and check its proof, run the following command:
```
lake exe checker <native> file.smt2
```
where `<native>` is either `true` or `false`, depending on whether you want to use native compoenents for proof replay or not.
