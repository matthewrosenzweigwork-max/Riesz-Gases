import HRS.Equilibrium.HeatSplitD1
import HRS.Energy.Coercivity

/-!
# HRS.Energy.PressureSplit — the weak split `g = g_L + q - c` with a uniform envelope (Proposition 5.5)

Proof of `N:prop:pressure`, `N:eq:finite-split` (source lines 6355-6362): the heat split of
`HRS/Equilibrium/HeatSplitD1.lean` (the `d ≥ 1` copy of `HeatSplit.lean`) gives, for every `ε`,
`g = g_L + q - c` with `q ≥ 0` even, `∫ q = c ≤ ε`, `g_L = ∑_{k∈Λ} a_k cos(2πk·x)`, `a_k ≥ 0`.
The point of this file is the envelope `q ≤ E₀ (g + c_*)` with `E₀` independent of `ε ≤ 1`, which holds
since `g_τ ≥ -A c_ψ Γ((d-s)/2)` uniformly in the heat time (the heat-kernel lower bound `psi_ge`), so
`q = g - g_L + c ≤ g + E₁ + 2c`.  The kernel `q` is redefined to be `0` at the origin (the value of the
Riesz kernel at `0` is junk), which keeps `q ≤ E₀ (g + c_*)` everywhere.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HRS

open ExternalD1 ExternalD1.HeatSplit

variable {d : ℕ} {s : ℝ}

/-- Uniform lower bound `g_τ ≥ -E₁` for the smooth part of the heat split. -/
theorem hSmooth_ge (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ E₁ : ℝ, 0 ≤ E₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ x : Torus d, -E₁ ≤ hSmooth d s τ x := by
  set a : ℝ := ((d : ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set c : ℝ := Real.exp 1 * (1 + ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2)) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    have : 0 ≤ ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2) :=
      tsum_nonneg fun _ => (Real.exp_pos _).le
    positivity
  have hA0 : 0 ≤ KernelAux.subA d s := KernelD1Aux.subA_nonneg_d1 hd hs0 hsd
  have hΓ : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  refine ⟨KernelAux.subA d s * (c * Real.Gamma a), by positivity, fun τ hτ x => ?_⟩
  rw [hSmooth_eq_integral hd hs0 hsd hτ x]
  have hG : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (a - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent ha
  have hG' : IntegrableOn (fun t : ℝ => c * (Real.exp (-t) * t ^ (a - 1))) (Ioi τ) :=
    (hG.mono_set (Ioi_subset_Ioi hτ.le)).const_mul c
  have hK : -(c * Real.Gamma a) ≤ ∫ t in Ioi τ, hW d s t * psiFn x t := by
    by_cases hf : IntegrableOn (fun t => hW d s t * psiFn x t) (Ioi τ)
    · have h1 : ∫ t in Ioi τ, -(c * (Real.exp (-t) * t ^ (a - 1))) ≤
          ∫ t in Ioi τ, hW d s t * psiFn x t := by
        refine setIntegral_mono_on hG'.neg hf measurableSet_Ioi fun t ht => ?_
        have ht' : 0 < t := lt_trans hτ ht
        have h2 := psi_ge x ht'
        rw [neg_mul] at h2
        have h2' : -(c * Real.exp (-t)) ≤ psiFn x t := by rw [hc]; exact h2
        have h3 := hW_nonneg (d := d) (s := s) ht'
        have h4 : hW d s t = t ^ (a - 1) := rfl
        rw [h4] at h3 ⊢
        calc -(c * (Real.exp (-t) * t ^ (a - 1))) = t ^ (a - 1) * (-(c * Real.exp (-t))) := by ring
          _ ≤ t ^ (a - 1) * psiFn x t := mul_le_mul_of_nonneg_left h2' h3
      refine le_trans ?_ h1
      rw [integral_neg, neg_le_neg_iff, integral_const_mul]
      have h5 : ∫ t in Ioi τ, Real.exp (-t) * t ^ (a - 1) ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ (a - 1) :=
        setIntegral_mono_set hG (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
          mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt ht) _))
          (Filter.Eventually.of_forall (Ioi_subset_Ioi hτ.le))
      rw [Real.Gamma_eq_integral ha] at *
      exact mul_le_mul_of_nonneg_left (by simpa [Real.Gamma_eq_integral ha] using h5) hc0
    · rw [integral_undef hf]
      have : 0 ≤ c * Real.Gamma a := by positivity
      linarith
  have := mul_le_mul_of_nonneg_left hK hA0
  linarith [show KernelAux.subA d s * -(c * Real.Gamma a) = -(KernelAux.subA d s * (c * Real.Gamma a)) by ring]

/-- The uniform split `g = g_L + q - c` (see the module docstring). -/
def UniformSplit (d : ℕ) (s cs : ℝ) : Prop :=
  ∃ E₀ : ℝ, 0 ≤ E₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∃ (Λ : Finset (Lattice d)) (a : Lattice d → ℝ) (q : Torus d → ℝ) (c : ℝ),
      (∀ k ∈ Λ, 0 ≤ a k) ∧ Measurable q ∧ (∀ x, 0 ≤ q x) ∧ (∀ x, q (-x) = q x) ∧ Integrable q ∧
      ∫ x, q x ≤ ε ∧ 0 ≤ c ∧
      (∀ x : Torus d, x ≠ 0 → periodicRiesz d s x = ∑ k ∈ Λ, a k * Torus.cosMode k x + q x - c) ∧
      (∀ x, q x ≤ E₀ * (periodicRiesz d s x + cs))

theorem uniformSplit (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (cs : ℝ)
    (hcs : ∀ z : Torus d, 1 ≤ periodicRiesz d s z + cs) : UniformSplit d s cs := by
  obtain ⟨E₁, hE₁, hE₁'⟩ := hSmooth_ge hd hs0 hsd
  refine ⟨1 + |E₁ + 2 - cs|, by positivity, fun ε hε hε1 => ?_⟩
  obtain ⟨τ, hτ, hτ1, L, hL⟩ := exists_small_hC hd hs0 hsd hε
  have hCle := hL L le_rfl
  set q : Torus d → ℝ := fun x => if x = 0 then 0 else hQ d s τ L x with hq
  have hsplit : ∀ x : Torus d, x ≠ 0 → periodicRiesz d s x = hGL d s τ L x + q x - hC d s τ L := by
    intro x hx
    simp only [hq, hx, if_false]
    exact periodicRiesz_eq_gL_add hd hs0 hsd hτ L x hx
  have hC0 := hC_nonneg hd hs0 hsd hτ L
  have hgeven : ∀ x : Torus d, hGL d s τ L (-x) = hGL d s τ L x := by
    intro x
    unfold hGL
    exact Finset.sum_congr rfl fun k _ => by rw [StaticLimitAux.cosMode_neg_arg]
  refine ⟨hModes d L, hCoeff d s τ, q, hC d s τ L, ?_, ?_, ?_, ?_, ?_, ?_, hC0, ?_, ?_⟩
  · intro k hk
    exact hCoeff_nonneg hd hs0 hsd hτ.le k
  · exact Measurable.ite (measurableSet_singleton (0 : Torus d)) measurable_const
      (measurable_hQ hd hs0 hsd hτ L)
  · intro x
    simp only [hq]
    split_ifs
    · exact le_rfl
    · exact hQ_nonneg hd hs0 hsd hτ L x
  · intro x
    by_cases hx : x = 0
    · simp [hq, hx]
    · have hx' : -x ≠ 0 := neg_ne_zero.2 hx
      have h1 := hsplit x hx
      have h2 := hsplit (-x) hx'
      rw [periodicRiesz_neg, hgeven] at h2
      linarith
  · have hae : q =ᵐ[volume] hQ d s τ L := by
      have : ∀ᵐ x : Torus d ∂volume, x ≠ 0 := by
        rw [ae_iff]
        simpa using volume_singleton_torus hd
      filter_upwards [this] with x hx
      simp [hq, hx]
    exact (integrable_hQ hd hs0 hsd hτ L).congr hae.symm
  · have hae : q =ᵐ[volume] hQ d s τ L := by
      have : ∀ᵐ x : Torus d ∂volume, x ≠ 0 := by
        rw [ae_iff]
        simpa using volume_singleton_torus hd
      filter_upwards [this] with x hx
      simp [hq, hx]
    rw [integral_congr_ae hae, integral_hQ hd hs0 hsd hτ L]
    exact hCle
  · intro x hx
    rw [hsplit x hx]
    unfold hGL
    ring
  · intro x
    have hE : 0 ≤ 1 + |E₁ + 2 - cs| := by positivity
    by_cases hx : x = 0
    · simp only [hq, hx, if_true]
      exact mul_nonneg hE (by linarith [hcs 0])
    · have hw := hcs x
      have h1 := hsplit x hx
      have h2 : hGL d s τ L x = hSmooth d s τ x - hRest d s τ L x := by
        rw [hSmooth_eq_add hd hs0 hsd hτ L x]; ring
      have h3 := hE₁' τ hτ x
      have h4 := abs_hRest_le hd hs0 hsd hτ L x
      have h5 : hRest0 d s τ L ≤ hC d s τ L := by
        unfold hC
        have : 0 ≤ hMass d s τ := by
          unfold hMass
          have := hexp_pos hsd
          have := KernelD1Aux.subA_nonneg_d1 hd hs0 hsd
          positivity
        linarith
      have h6 := neg_abs_le (hRest d s τ L x)
      have hqx : q x ≤ periodicRiesz d s x + cs + (E₁ + 2 - cs) := by
        have : q x = periodicRiesz d s x - hGL d s τ L x + hC d s τ L := by linarith
        rw [this, h2]
        linarith [le_abs_self (hRest d s τ L x)]
      calc q x ≤ periodicRiesz d s x + cs + |E₁ + 2 - cs| := by
            linarith [le_abs_self (E₁ + 2 - cs)]
        _ ≤ (periodicRiesz d s x + cs) + |E₁ + 2 - cs| * (periodicRiesz d s x + cs) := by
            have := mul_le_mul_of_nonneg_left hw (abs_nonneg (E₁ + 2 - cs))
            linarith
        _ = (1 + |E₁ + 2 - cs|) * (periodicRiesz d s x + cs) := by ring

end HRS

end
