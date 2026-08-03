# Lean verification that computing Kemeny score is NP-hard for 3 input rankings

This is a companion repository for the paper "Kemeny Rank Aggregation is NP-Hard for Three Voters" by Dominik Peters, [arXiv:2607.25540](https://arxiv.org/abs/2607.25540). It formalizes the NP-hardness reduction presented there in Lean, which shows that the following problem is NP-hard:

**KEMENY SCORE** for three voters

Input: Three linear orders, a budget b

Question: Does there exist a linear order whose total Kendall-tau distance to the input linear orders is at most b?

The reduction is built on top of the more general project [HardnessReductionLean](https://github.com/DominikPeters/HardnessReductionsLean/). That project does *not* anchor its theory in any machine model, so it doesn't prove NP-hardness _end to end_. It does prove that the reduction presented (from MAX COVER) is correct, and gives a certificate that the reduction is polynomial-time computable (the certificate is an algorithm written in a custom heavily restricted programming language that can only express polynomial time programs).