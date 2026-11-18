import HRS.MC.CepH5FinProof
import HRS.Appendix.CepaFlow
import HRS.MC.CepaSpec

/-!
# Tie for packet CEPH5FIN: the relocated proof has exactly the statements of the spec theorem and of the frozen theorem.
-/

example := (@HRS.MC.CepH5Fin.cep_H5_entropy_confined_proof : type_of% @HRS.MC.Cepa.cep_H5_entropy_confined)
/-- The frozen `HRS.cepa_entropy_confined` has the same statement, except that its implicit binder `N` comes before
`Ω, mΩ, P` (it is a section variable of `CepaFlow`), so the literal `type_of%` comparison fails and the tie
permutes these four implicit binders. -/
example : type_of% @HRS.cepa_entropy_confined := by
  intro N Ω mΩ P inst
  exact @HRS.MC.CepH5Fin.cep_H5_entropy_confined_proof Ω mΩ P N inst
