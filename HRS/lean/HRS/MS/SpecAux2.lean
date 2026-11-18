import HRS.MS.SpecAux1

/-!
# S8P: geometric decay of quasi-compact operators (generic, for S8.3)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  Continues `SpecAux1`: if `S = K + R` (`K` compact, `‖R‖ ≤ θ`) has no
eigenvalue of modulus `> θ`, then `spectrum ⊆ closedBall 0 θ` and `‖S^n‖ ≤ C θ'^n` for every `θ' > θ`.
-/

noncomputable section

open Filter Topology Module
open scoped ENNReal NNReal

namespace HRS.MS.Spec

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The spectrum of `K + R` lies in the closed ball of radius `θ`. -/
theorem s8p_spectrum_in_ball (K R : X →L[ℂ] X) (hK : IsCompactOperator K) {θ : ℝ}
    (hRθ : ‖R‖ ≤ θ)
    (heig : ∀ z : ℂ, Module.End.HasEigenvalue ((K + R : X →L[ℂ] X) : Module.End ℂ X) z → ‖z‖ ≤ θ) :
    ∀ z ∈ spectrum ℂ (K + R), ‖z‖ ≤ θ := by
  intro z hz
  by_contra hlt
  push Not at hlt
  rcases s8p_quasi_compact_resolvent K R hK (lam := z) (lt_of_le_of_lt hRθ hlt) with h | h
  · exact absurd (heig z h) (not_le.2 hlt)
  · exact hz h

/-- Geometric decay of the powers. -/
theorem s8p_geometric_decay (K R : X →L[ℂ] X) (hK : IsCompactOperator K) {θ θ' : ℝ}
    (hθ0 : 0 ≤ θ) (hθθ' : θ < θ') (hRθ : ‖R‖ ≤ θ)
    (heig : ∀ z : ℂ, Module.End.HasEigenvalue ((K + R : X →L[ℂ] X) : Module.End ℂ X) z → ‖z‖ ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖(K + R) ^ n‖ ≤ C * θ' ^ n := by
  set S : X →L[ℂ] X := K + R with hS
  have hsp := s8p_spectrum_in_ball K R hK hRθ heig
  have hrad : spectralRadius ℂ S ≤ ENNReal.ofReal θ := by
    refine iSup₂_le fun z hz => ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    have hz' : z ∈ spectrum ℂ S ∪ {0} := by rwa [← quasispectrum_eq_spectrum_union_zero ℂ S]
    rcases hz' with h | h
    · simpa using hsp z h
    · rw [Set.mem_singleton_iff] at h; subst h; simpa using hθ0
  have hθ'pos : 0 < θ' := lt_of_le_of_lt hθ0 hθθ'
  have hlt : spectralRadius ℂ S < ENNReal.ofReal θ' :=
    lt_of_le_of_lt hrad ((ENNReal.ofReal_lt_ofReal_iff hθ'pos).2 hθθ')
  have hG := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius S
  have hev := hG.eventually (eventually_lt_nhds hlt)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have key : ∀ n : ℕ, max N 1 ≤ n → ‖S ^ n‖ ≤ θ' ^ n := by
    intro n hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    have h := hN n hnN
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have h2 := ENNReal.rpow_lt_rpow h hnpos
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hnpos.ne', ENNReal.rpow_one,
      ENNReal.rpow_natCast, ← ENNReal.ofReal_pow hθ'pos.le, ← ENNReal.ofReal_coe_nnreal] at h2
    have h3 := (ENNReal.ofReal_lt_ofReal_iff (pow_pos hθ'pos n)).1 h2
    simpa using h3.le
  refine ⟨1 + ∑ n ∈ Finset.range (max N 1), ‖S ^ n‖ / θ' ^ n, by positivity, fun n => ?_⟩
  have hsum : 0 ≤ ∑ n ∈ Finset.range (max N 1), ‖S ^ n‖ / θ' ^ n :=
    Finset.sum_nonneg fun n _ => by positivity
  by_cases hn : max N 1 ≤ n
  · calc ‖S ^ n‖ ≤ θ' ^ n := key n hn
      _ = 1 * θ' ^ n := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hθ'pos.le _)
  · push Not at hn
    have hle : ‖S ^ n‖ / θ' ^ n ≤ ∑ m ∈ Finset.range (max N 1), ‖S ^ m‖ / θ' ^ m :=
      Finset.single_le_sum (f := fun m => ‖S ^ m‖ / θ' ^ m) (fun m _ => by positivity)
        (Finset.mem_range.2 hn)
    have hp : 0 < θ' ^ n := pow_pos hθ'pos n
    calc ‖S ^ n‖ = (‖S ^ n‖ / θ' ^ n) * θ' ^ n := by field_simp
      _ ≤ (1 + ∑ m ∈ Finset.range (max N 1), ‖S ^ m‖ / θ' ^ m) * θ' ^ n :=
          mul_le_mul_of_nonneg_right (by linarith) hp.le

end HRS.MS.Spec
