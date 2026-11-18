import HRS.MS.WhoAux10
import HRS.MS.WhoAux11
import HRS.MS.WhoAux12
import HRS.MS.UlOrbitAux2
import HRS.Whole.Orbits

/-!
# S54 tie: `HRS.Whole.weighted_higher_order`

`weighted_higher_order_proof` has exactly the type of the frozen statement (the frozen declaration is unproved; a warning is expected).
`k₀ = ⌊4 + d/2⌋ + 1`.  (a): the evolution `u` of level `k` is the evolution `u₀` of the large level `K` (existence at level `K`,
`ul6_mono_level`, uniqueness at level `k`), and `u₀` obeys the a priori weighted bound `who_core`; (b): `who_B`; (c): `who_embed`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Who

open HRS HRS.Whole HRS.MS.Ul

theorem who_E_mul (X : ℝ) (hX : 0 ≤ X) (Y : ℝ≥0∞) :
    (ENNReal.ofReal X * Y) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt X) * Y ^ (1 / 2 : ℝ) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg hX (by norm_num),
    Real.sqrt_eq_rpow]

/-- from the `Nsq` bound to the frozen norm -/
theorem who_to_E {d : ℕ} (hd : 1 ≤ d) {r r' : ℕ} {P Cn : ℝ} (hCn : 0 ≤ Cn) {u f : Euc d → ℝ}
    (hf : ContDiff ℝ r' f) (h : Nsq r P u ≤ ENNReal.ofReal Cn * Nsq r' P f) :
    weightedSobolevE r P u ≤ ENNReal.ofReal (Real.sqrt (Cn * (d : ℝ) ^ (r + r'))) * weightedSobolevE r' P f := by
  rw [who_E_eq, who_E_eq, ← who_E_mul _ (by positivity)]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  calc Esq r P u ≤ ((d : ℝ≥0∞) ^ r) * Nsq r P u := who_Esq_le hd
    _ ≤ ((d : ℝ≥0∞) ^ r) * (ENNReal.ofReal Cn * (((d : ℝ≥0∞) ^ r') * Esq r' P f)) :=
        mul_le_mul' le_rfl (h.trans (mul_le_mul' le_rfl (who_Nsq_le hd hf)))
    _ = ENNReal.ofReal (Cn * (d : ℝ) ^ (r + r')) * Esq r' P f := by
        rw [ENNReal.ofReal_mul hCn, ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast, pow_add]
        ring

theorem weighted_higher_order_proof : type_of% @HRS.Whole.weighted_higher_order := by
  intro d hd s hs0 hsd θ hθ
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : s + 1 < d := by linarith
  have hsd' : s < (d : ℝ) := by linarith
  refine ⟨⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ + 1, ?_⟩
  intro r P hP T ν Q M ρ c hT hν hρ hc
  obtain ⟨ψ, rfl⟩ := hρ.2
  have hP0 : 0 ≤ P := by linarith [show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity]
  intro Cf
  refine ⟨?_, ?_, ?_⟩
  · -- (a)
    obtain ⟨Cc, hCc0, hcore⟩ := who_core hd1 hs0 hs1 M ψ hc hP Q hν T r
    refine ⟨Real.sqrt (Cc * (d : ℝ) ^ (2 * r)), ?_⟩
    intro k hk t ht f hf hfc u hu r' hr'
    have hk4 : (4 : ℝ) + (d : ℝ) / 2 < k :=
      (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast hk)
    set K : ℕ := max k (⌊(r : ℝ) + 4 + (d : ℝ) / 2⌋₊ + 1) with hKdef
    have hKk : k ≤ K := le_max_left _ _
    have hK1 : (r : ℝ) + 4 + (d : ℝ) / 2 < K := by
      have h1 : (r : ℝ) + 4 + (d : ℝ) / 2 < ((⌊(r : ℝ) + 4 + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast; exact Nat.lt_floor_add_one _
      exact h1.trans_le (Nat.cast_le.2 (le_max_right _ _))
    have hK4 : (4 : ℝ) + (d : ℝ) / 2 < K := by
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      linarith
    have hKr : ((r + 3 : ℕ) : ℝ) + (d : ℝ) / 2 < K := by
      have : ((r + 3 : ℕ) : ℝ) = (r : ℝ) + 3 := by push_cast; ring
      linarith
    obtain ⟨C₁, hC₁⟩ := ul_evolution_exists hs0 hsd' θ hθ K hK4 T ν hT hν Q M ψ ⟨ψ, rfl⟩ c hc
    have hclos : UlClosure K θ f :=
      ul4b_closure_of_ccc K θ ⟨f, 0, hf, hfc, by funext x; simp⟩
    obtain ⟨u₀, hu₀, hb₀⟩ := hC₁ t ht f hclos
    have hu₀k := ul6_mono_level hKk hu₀
    have heq := ul_evolution_unique hs0 hsd' θ hθ k hk4 ν hν Q M ψ ⟨ψ, rfl⟩ c hc ht.1 hu hu₀k
    have hfin := ul0_ulNormE_lt_top_of_closure K θ hθ hclos
    have hBu : ∀ σ ∈ Set.Icc (0 : ℝ) t, ulNormE K θ (u₀ σ) ≤ ENNReal.ofReal (C₁ * (ulNormE K θ f).toReal) := by
      intro σ hσ
      refine (hb₀ σ hσ).trans ?_
      rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin.ne]
    obtain ⟨hcd, hN⟩ := hcore hθ hK4 hKr ht.1 ht.2 hf hfc hu₀ hBu r' hr'
    rw [heq r' hr']
    refine ⟨hcd, ?_⟩
    have := who_to_E hd1 hCc0 (contDiff_infty.1 hf r) hN
    rwa [show r + r = 2 * r by ring] at this
  · -- (b)
    obtain ⟨CB, hCB0, hB⟩ := who_B hd1 hs0 hs1 M ψ hc hP Q ν T r
    refine ⟨Real.sqrt (CB * (d : ℝ) ^ (r + (r + 2))), ?_⟩
    intro Φ hΦ t ht g hg hgc
    obtain ⟨hcd, hN⟩ := hB hΦ t ht hg hgc
    exact who_to_E hd1 hCB0 (contDiff_infty.1 hg (r + 2)) hN
  · -- (c)
    intro α hα
    obtain ⟨C, -, hC⟩ := who_embed hd1 hP0 r α hα
    exact ⟨C, fun i x f hf => hC i x f hf⟩

end HRS.MS.Who
