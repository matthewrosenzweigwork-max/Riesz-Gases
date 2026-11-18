import HRS.MC.E213R1
import HRS.MC.E213R2
import HRS.MC.E213N3
import HRS.MC.S7PIS2Obs

/-!
# Packet e213r, part 3: the covariance identification for the shifted noise

For the covariation density `1_{(u,T]} noiseDens` of the shifted martingale `G^u` and the dual evolution `Vev` of a smooth
positive trajectory:
`∫_{[0,ta∧tb]} 1_{(u,T]}(σ) noiseDens_σ(pullback φa, pullback φb) dσ = 2 β⁻¹ ∫_{[u,ta∧tb]} ∫ ∇U^{v,ta}φa · ∇U^{v,tb}φb ρ^v dv`
(`t25p_cov_eq` and `e213k_covDensT_eq`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213R

open HRS HRS.Sec7 HRS.Uniform HRS.Uniform.Q54c HRS.GF HRS.T25P HRS.AdjK

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-- The covariation density of the shifted noise `G^u` on `[0,T]`. -/
def e213rCd (m q : ℝ) (ρ : ℝ → Torus d → ℝ) (u T : ℝ) :
    ℝ → NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ :=
  fun r => (Set.Ioc u T).indicator (HRS.MC.E213N.noiseDens m q ρ) r

theorem e213r_cov_integral (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    (hm : (d : ℝ) / 2 + 2 < m) {T u : ℝ} (hu : 0 ≤ u)
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual : IsDualEvolution htr.dyn ρ m Vev)
    {Cr : ℝ} (hCr : 0 ≤ Cr) (hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → ‖Vev t r‖ ≤ Cr)
    {ta tb : ℝ} (hta : ta ∈ Set.Icc (0 : ℝ) T) (htb : tb ∈ Set.Icc (0 : ℝ) T)
    {φa φb : Torus d → ℝ} (hφa : Torus.IsSmooth φa) (hφb : Torus.IsSmooth φb) :
    ∫ σ in Set.Icc 0 (min ta tb), e213rCd m β⁻¹ ρ u T σ
        (pullbackVec (HRS.Uniform.Comp28.plainData Vev) ta σ (gfb4_ell m φa))
        (pullbackVec (HRS.Uniform.Comp28.plainData Vev) tb σ (gfb4_ell m φb)) =
      2 * β⁻¹ * ∫ v in Set.Icc u (min ta tb), ∫ x,
        inner ℝ (Torus.grad (propagator htr.dyn ρ v ta φa) x) (Torus.grad (propagator htr.dyn ρ v tb φb) x) *
          ρ v x := by
  set n : ℕ := ⌈T⌉₊ + 1 with hn
  have hnpos : (0 : ℝ) < n := by rw [hn]; push_cast; positivity
  have hTn : T ≤ (n : ℝ) := by
    rw [hn]; push_cast; exact (Nat.le_ceil T).trans (le_add_of_nonneg_right zero_le_one)
  have hq : (0 : ℝ) ≤ β⁻¹ := inv_nonneg.2 htr.hβ.le
  have hta' : ta ∈ Set.Icc (0 : ℝ) n := ⟨hta.1, hta.2.trans hTn⟩
  have htb' : tb ∈ Set.Icc (0 : ℝ) n := ⟨htb.1, htb.2.trans hTn⟩
  have hmin : min ta tb ≤ T := (min_le_left _ _).trans hta.2
  set H : ℝ → ℝ := fun σ => 2 * β⁻¹ * ∫ x, inner ℝ (Torus.grad (propagator htr.dyn ρ σ ta φa) x)
    (Torus.grad (propagator htr.dyn ρ σ tb φb) x) * ρ σ x with hH
  have h1 : ∫ σ in Set.Icc 0 (min ta tb), e213rCd m β⁻¹ ρ u T σ
        (pullbackVec (HRS.Uniform.Comp28.plainData Vev) ta σ (gfb4_ell m φa))
        (pullbackVec (HRS.Uniform.Comp28.plainData Vev) tb σ (gfb4_ell m φb)) =
      ∫ σ in Set.Icc 0 (min ta tb), (Set.Ioc u T).indicator H σ := by
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    have hσn : σ ∈ Set.Icc (0 : ℝ) n := ⟨hσ.1, hσ.2.trans (hmin.trans hTn)⟩
    have hκ : HRS.MC.E213N.noiseDens m β⁻¹ ρ σ = covDensT m β⁻¹ n ρ σ :=
      (HRS.MC.E213K.e213k_covDensT_eq m β⁻¹ n ρ hσn).symm
    have hcov := t25p_cov_eq hd htr hm hnpos hdual hCr (fun r t hr hrt _ => hKb r t hr hrt) hq
      hta' htb' hσ hφa hφb
    simp only [e213rCd, Set.indicator_apply]
    split_ifs with h
    · rw [hκ]; exact hcov
    · simp
  rw [h1, setIntegral_indicator measurableSet_Ioc]
  have hset : Set.Icc 0 (min ta tb) ∩ Set.Ioc u T = Set.Icc u (min ta tb) \ {u} := by
    ext σ
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioc, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h3.le, h2⟩, h3.ne'⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have : u < σ := lt_of_le_of_ne h1 (Ne.symm h3)
      exact ⟨⟨hu.trans h1, h2⟩, this, h2.trans hmin⟩
  rw [hset]
  have hnull : ∫ σ in Set.Icc u (min ta tb) \ {u}, H σ = ∫ σ in Set.Icc u (min ta tb), H σ := by
    refine setIntegral_congr_set ?_
    have : (Set.Icc u (min ta tb) \ {u} : Set ℝ) =ᵐ[volume] Set.Icc u (min ta tb) :=
      sdiff_null_ae_eq_self (by simp)
    exact this
  rw [hnull]
  simp only [hH]
  rw [integral_const_mul]

end HRS.MC.E213R
