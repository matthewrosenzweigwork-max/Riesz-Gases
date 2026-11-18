import HRS.PDE.MovSXAux2
import HRS.Appendix.B15Aux2

/-!
# MOVSX Aux3: `pressure_two_sided` for `C²` backgrounds (packet `movT_pressure_two_sided_C2`)

From `movsx_pressure_param` with `G = g = periodicRiesz`, `q = q₀` the uniform split of `g`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS

variable {d : ℕ}

/-- `ρ ≤ ‖ρ‖_{C²}` pointwise for a `C²` function on the torus. -/
theorem movsx_le_cbNorm_two {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ) (x : Torus d) :
    ρ x ≤ Torus.cbNorm 2 ρ := by
  have hc : Continuous ρ := b15_continuous_of_isCk hρ
  have hbdd : BddAbove (Set.range fun y : Euc d => ‖iteratedFDeriv ℝ 0 (Torus.lift ρ) y‖) := by
    obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
    refine ⟨R, ?_⟩
    rintro _ ⟨y, rfl⟩
    show ‖iteratedFDeriv ℝ 0 (Torus.lift ρ) y‖ ≤ R
    rw [norm_iteratedFDeriv_zero]
    exact hR (Torus.mk y) trivial
  have h := le_ciSup hbdd (Torus.rep x)
  have e : ‖iteratedFDeriv ℝ 0 (Torus.lift ρ) (Torus.rep x)‖ = |ρ x| := by
    rw [norm_iteratedFDeriv_zero]
    simp [Torus.lift, Torus.mk_rep]
  rw [e] at h
  have h0 : ρ x ≤ ⨆ y : Euc d, ‖iteratedFDeriv ℝ 0 (Torus.lift ρ) y‖ := (le_abs_self _).trans h
  have h1 : 0 ≤ ⨆ y : Euc d, ‖iteratedFDeriv ℝ 1 (Torus.lift ρ) y‖ :=
    Real.iSup_nonneg fun _ => norm_nonneg _
  have h2 : 0 ≤ ⨆ y : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift ρ) y‖ :=
    Real.iSup_nonneg fun _ => norm_nonneg _
  have : Torus.cbNorm 2 ρ = (⨆ y : Euc d, ‖iteratedFDeriv ℝ 0 (Torus.lift ρ) y‖) +
      (⨆ y : Euc d, ‖iteratedFDeriv ℝ 1 (Torus.lift ρ) y‖) +
      (⨆ y : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift ρ) y‖) := by
    simp [Torus.cbNorm, Finset.sum_range_succ]
  linarith

set_option maxHeartbeats 1600000 in
theorem movsx_pressure_two_sided_C2 (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cstar : ℝ) (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar)
    (βm βp : ℝ) (hβm : 0 < βm) (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ₂ : ℝ) (B : ℝ) :
    ∃ θ₀ C : ℝ, 0 < θ₀ ∧ 0 ≤ C ∧
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsCk 2 ρ → (∀ x, c₀ ≤ ρ x) →
        Torus.cbNorm 2 ρ ≤ Λ₂ →
      ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
        (∀ x y, |h x y| ≤ B * (periodicRiesz d s (x - y) + cstar)) →
      ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc βm βp, ∀ θ : ℝ, |θ| ≤ θ₀ →
          ENNReal.ofReal (Real.exp (-(C * N * deltaN d s N))) ≤
              ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
                modulatedEnergy (fun x y => periodicRiesz d s (x - y) - θ * h x y) X
                  (withDensityReal ρ))) ∂(Measure.pi fun _ => withDensityReal ρ) ∧
          ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
                modulatedEnergy (fun x y => periodicRiesz d s (x - y) - θ * h x y) X
                  (withDensityReal ρ))) ∂(Measure.pi fun _ => withDensityReal ρ) ≤
            ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) := by
  obtain ⟨g, hg⟩ : ∃ g : Torus d → ℝ, g = periodicRiesz d s := ⟨_, rfl⟩
  rw [← hg] at hw ⊢
  obtain ⟨g0, hg0⟩ : ∃ g0 : ℝ, g0 = g 0 := ⟨_, rfl⟩
  obtain ⟨cs, hcsdef⟩ : ∃ cs : ℝ, cs = max cstar (1 - g0) := ⟨_, rfl⟩
  have hcs : ∀ z : Torus d, 1 ≤ g z + cs := by
    intro z
    by_cases hz : z = 0
    · subst hz
      have : 1 - g0 ≤ cs := by rw [hcsdef]; exact le_max_right _ _
      linarith
    · have := hw z hz; have : cstar ≤ cs := by rw [hcsdef]; exact le_max_left _ _
      linarith
  have hcstar : cstar ≤ cs := by rw [hcsdef]; exact le_max_left _ _
  obtain ⟨B', hB'def⟩ : ∃ B' : ℝ, B' = max B 0 := ⟨_, rfl⟩
  have hB' : 0 ≤ B' := by rw [hB'def]; exact le_max_right _ _
  have hgm : Measurable g := by rw [hg]; exact CoercAux.measurable_periodicRiesz_one hd hs0 hsd
  have hcs' : ∀ z : Torus d, 1 ≤ periodicRiesz d s z + cs := fun z => by have := hcs z; rw [hg] at this; exact this
  obtain ⟨E₀, hE₀, hspl⟩ := uniformSplit hd hs0 hsd cs hcs'
  rw [← hg] at hspl
  obtain ⟨Λ0, hΛ0def⟩ : ∃ Λ0 : ℝ, Λ0 = max Λ₂ 0 := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ0 := by rw [hΛ0def]; exact le_max_right _ _
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = 1 + |cs| := ⟨_, rfl⟩
  have hκ : 0 ≤ κ := by rw [hκdef]; positivity
  obtain ⟨ε₀, hε₀, hε₀1, hP⟩ := movsx_pressure_param hd s hs0 hsd cs hcs' βm βp hβm Λ0 hΛ0 E₀ B' κ hE₀ hB' hκ
  rw [← hg] at hP
  obtain ⟨Λf, af, q, c, haf, hqm, hq0, hqev, hqint, hqε, hc0, hsplit, hqenv⟩ := hspl ε₀ hε₀ hε₀1
  obtain ⟨Sa, hSa⟩ : ∃ Sa : ℝ, Sa = ∑ k ∈ Λf, af k := ⟨_, rfl⟩
  have hSa0 : 0 ≤ Sa := by rw [hSa]; exact Finset.sum_nonneg haf
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = B' * (Sa + |g0| + |cs|) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  obtain ⟨θ₀, C, hθ₀, hC, hP2⟩ := hP Λf af q c D haf hqm hq0 hqint hqε hc0 hD0 hqenv
  refine ⟨θ₀, C, hθ₀, hC, ?_⟩
  intro ρ hρ hck hlow hcb h hhm hsym hdom N hN β hβ θ hθ
  have hρΛ : ∀ x, ρ x ≤ Λ0 := fun x =>
    ((movsx_le_cbNorm_two hck x).trans hcb).trans (hΛ0def ▸ le_max_left _ _)
  have hhdom : ∀ x y, |h x y| ≤ B' * (g (x - y) + cs) := by
    rw [hB'def]; exact dom_max hd hcstar hw hdom
  have hsplit' : ∀ x : Torus d, x ≠ 0 → g x = ∑ k ∈ Λf, af k * Torus.cosMode k x + q x - c := hsplit
  have hcosle : ∀ z : Torus d, |∑ k ∈ Λf, af k * Torus.cosMode k z| ≤ Sa := by
    intro z
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hSa]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [abs_mul, abs_of_nonneg (haf k hk)]
    exact mul_le_of_le_one_right (haf k hk) (abs_cosMode_le k z)
  have henv : ∀ x y, |h x y| ≤ B' * q (x - y) + D := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      have h1 := hhdom x x
      rw [sub_self] at h1
      have h2 : g 0 + cs ≤ |g0| + |cs| := by
        rw [← hg0]; exact add_le_add (le_abs_self _) (le_abs_self _)
      have h3 : B' * (g 0 + cs) ≤ B' * (|g0| + |cs|) := mul_le_mul_of_nonneg_left h2 hB'
      have h4 : 0 ≤ B' * q 0 := mul_nonneg hB' (hq0 _)
      have h5 : B' * (|g0| + |cs|) ≤ D := by
        rw [hD]; exact mul_le_mul_of_nonneg_left (by linarith [abs_nonneg g0, abs_nonneg cs]) hB'
      rw [sub_self]; linarith
    · have h1 := hhdom x y
      have h2 := hsplit' (x - y) (sub_ne_zero.2 hxy)
      have h3 := le_abs_self (∑ k ∈ Λf, af k * Torus.cosMode k (x - y))
      have h4 := hcosle (x - y)
      have h5 : g (x - y) + cs ≤ q (x - y) + (Sa + |cs|) := by
        have := le_abs_self cs
        have := (le_abs_self _ : (∑ k ∈ Λf, af k * Torus.cosMode k (x - y)) ≤ _)
        linarith
      have h6 : B' * (g (x - y) + cs) ≤ B' * (q (x - y) + (Sa + |cs|)) :=
        mul_le_mul_of_nonneg_left h5 hB'
      have h7 : B' * (Sa + |cs|) ≤ D := by
        rw [hD]; exact mul_le_mul_of_nonneg_left (by linarith [abs_nonneg g0]) hB'
      nlinarith
  have hGdom : ∀ z, |g z| ≤ κ * (g z + cs) := by
    intro z
    have h1 := hcs z
    have h2 : |g z| ≤ (g z + cs) + |cs| := by
      have := le_abs_self cs
      have := neg_abs_le cs
      rw [abs_le]; constructor <;> linarith [neg_abs_le (g z), le_abs_self (g z)]
    rw [hκdef]
    nlinarith [abs_nonneg cs]
  exact hP2 g q hgm hqm hq0 (fun x => le_rfl) hqev (fun z _ => hGdom z) hsplit' ρ hρ hρΛ h hhm hsym hhdom henv N hN β hβ θ hθ
 
end HRS

end
