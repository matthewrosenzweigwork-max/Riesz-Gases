import HRS.MC.CepE2Aux5

/-!
# Packet CEPE2: Moreau–Yosida kit for the chamber potential (`cep_E2_moreau_yosida`)

`HRS.MC.CepE2.cep_E2_moreau_yosida_proof` has the statement of `HRS.MC.Cepa.cep_E2_moreau_yosida`
(the duplicated vocabulary `Ch`, `cep_Alcove`, `cep_chamberPot`, `cep_Yosida` unfolds to the same bodies).
The resolvent `J_n z` is the solution in the open alcove of `n (z - x) = ∇Φ(x)`, which exists by minimising
`Φ + (n/2)|· - z|²` on a compact sublevel set of the barrier `Φ`; `Φ_n` is the Moreau envelope.
-/

open Set Filter Topology
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE2

open HRS.MC.CepE1

/-- Copy of `HRS.MC.Cepa.cep_Yosida`. -/
structure cep_Yosida (a : ℝ) (N : ℕ) (J : ℝ → Ch N → Ch N) : Prop where
  mem : ∀ n z, 0 < n → J n z ∈ cep_Alcove N
  force : ∀ n z, 0 < n → n • (z - J n z) = gradient (cep_chamberPot a N) (J n z)
  lip : ∀ n, 0 < n → LipschitzWith (Real.toNNReal n) (fun z => n • (z - J n z))
  yosida : ∀ m n x y, 0 < m → 0 < n →
    -((1 / m + 1 / n) * inner ℝ (m • (x - J m x)) (n • (y - J n y)))
      ≤ inner ℝ (m • (x - J m x) - n • (y - J n y)) (x - y)

theorem cep_E2_moreau_yosida_proof (a : ℝ) (ha : 0 < a) (N : ℕ) :
    ∃ (J : ℝ → Ch N → Ch N) (Φn : ℝ → Ch N → ℝ), cep_Yosida a N J ∧
      (∀ n z, 0 < n → HasGradientAt (Φn n) (n • (z - J n z)) z) ∧
      (∀ n z, 0 < n → z ∈ cep_Alcove N → Φn n z ≤ cep_chamberPot a N z) ∧
      (∀ z, z ∈ cep_Alcove N → Filter.Tendsto (fun n : ℕ => Φn n z) Filter.atTop (𝓝 (cep_chamberPot a N z))) := by
  refine ⟨fun n z => cepe2_J ha n z, fun n z => cepe2_env ha n z, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro n z hn
    exact (cepe2_J_spec ha hn z).1
  · intro n z hn
    obtain ⟨hA, hF⟩ := cepe2_J_spec ha hn z
    rw [hF, cepe2_gradient_eq hA]
  · intro n hn
    refine LipschitzWith.of_dist_le_mul fun z z' => ?_
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hn,
      Real.coe_toNNReal _ hn.le]
    exact mul_le_mul_of_nonneg_left (cepe2_lip ha hn z z') hn.le
  · intro m n x y hm hn
    exact cepe2_yosida ha hm hn x y
  · intro n z hn
    exact cepe2_env_hasGradient ha hn z
  · intro n z hn hz
    exact cepe2_env_le ha hn hz
  · intro z hz
    exact cepe2_env_tendsto ha hz

end HRS.MC.CepE2
