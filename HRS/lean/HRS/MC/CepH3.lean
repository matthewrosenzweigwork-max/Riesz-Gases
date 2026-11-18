import HRS.MC.CepaDefs

/-
Packet CEPH3 (`cep_H3_limit_semicontinuity`): proved for the repaired statement (hypotheses `hΦlim`, `hZlc` added to the spec).
Files, in dependency order: CepH3A1, A2, B1, B2, B3 (Moreau-Yosida layer), C1, C2, C3 (relative entropy library, Donsker-Varadhan lsc),
D1, D2 (covering map `mk ∘ unrank` and change of variables), E1-E4 (Gaussian domination, narrow convergence of the reference measures),
F1 (convergence in probability), G1 (Gibbs side), H1, H2 (parts (a) and (c)), I1, J1-J3, K1, K2, L1, M1 (part (b)), CepH3Pf (assembly,
`HRS.MC.CepH3.cep_H3_limit_semicontinuity_proof`), CepH3Tie (type check against the spec statement).
-/
