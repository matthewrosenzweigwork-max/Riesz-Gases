import HRS.Equilibrium.Parametrix.PX3aAuxV
import HRS.Equilibrium.LocalDivSub

/-!
# Packet PX3a auxiliaries W: integrability of conormal kernels of order `< d`
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

lemma abs_le_envW_of_conormal {σ : ℝ} {b : ℕ} {B : ℝ} (hB : 0 ≤ B) {H : Torus d → Torus d → ℝ}
    (hH : Conormal σ b 0 B H) (hdiag : ∀ x, H x x = 0) (x y : Torus d) :
    |H x y| ≤ B * (1 + Torus.eucDist x y ^ (-σ) * (1 + |Real.log (Torus.eucDist x y)|) ^ b) := by
  by_cases hxy : x = y
  · subst hxy
    rw [hdiag, abs_zero]
    have : 0 ≤ Torus.eucDist x x ^ (-σ) * (1 + |Real.log (Torus.eucDist x x)|) ^ b :=
      mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (pow_nonneg (by positivity) _)
    exact mul_nonneg hB (by linarith)
  · set w : Euc d := Torus.centeredRep (x - y) with hw
    have hmk : Torus.mk w = x - y := px3a_mk_cR _
    have hwb : ∀ i, |w i| ≤ 1 / 2 := px3a_abs_cR_le _
    have hwne : Torus.mk w ≠ 0 := by rw [hmk]; exact sub_ne_zero.mpr hxy
    have hdist : Torus.eucDist x y = ‖w‖ := eucDist_mk_sub_eq hmk hwb
    have h := norm_slice_le hB hH hwne hwb (Torus.rep x) (i := 0) le_rfl
    rw [norm_iteratedFDeriv_zero] at h
    have e : lift2 H (Torus.rep x, Torus.rep x - w) = H x y := by
      simp only [lift2]
      rw [mk_sub_eq, hmk, Torus.mk_rep]
      congr 1; abel
    rw [e, Real.norm_eq_abs] at h
    rw [hdist]
    simpa [envW] using h

theorem conormal_row_int (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {σ : ℝ}
    (hσ : σ < d) (b : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (B : ℝ) (H : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b 0 B H →
      (∀ x, H x x = 0) → ∀ x, Integrable (fun y => H x y) (withDensityReal ρ) ∧
        ∫ y, |H x y| ∂(withDensityReal ρ) ≤ K * B := by
  obtain ⟨Rm, hRm⟩ := exists_density_bound hρ
  have hI0 : 0 ≤ ∫ w in LocalDivAux.cube d, envW d σ b w :=
    setIntegral_nonneg LocalDivAux.measurableSet_cube fun w _ => by
      linarith [one_le_envW (d := d) σ b w]
  have hRm0 : 0 ≤ Rm := (hρ.density.nonneg (0 : Torus d)).trans (hRm 0)
  refine ⟨Rm * ∫ w in LocalDivAux.cube d, envW d σ b w, mul_nonneg hRm0 hI0, fun B H hB hH hdiag x => ?_⟩
  have hmeas : Measurable fun p : Torus d × Torus d => H p.1 p.2 := by
    have := measurable_offZero_of_contDiffOn (F := H) (m := 0) hH.smooth
    have e : Function.uncurry (offZero H) = fun p : Torus d × Torus d => H p.1 p.2 := by
      funext p
      by_cases h : p.1 = p.2
      · simp [Function.uncurry, offZero, h, hdiag]
      · simp [Function.uncurry, offZero, h]
    rw [← e]; exact this
  set g : ℝ → ℝ := fun t => B * (1 + t ^ (-σ) * (1 + |Real.log t|) ^ b) with hg
  have hgi : IntegrableOn (fun w : Euc d => g ‖w‖) (LocalDivAux.cube d) :=
    (integrableOn_cube_envW hd hσ b).const_mul B
  have hbd : ∀ x y, |H x y| ≤ g (Torus.eucDist x y) :=
    fun x y => abs_le_envW_of_conormal hB hH hdiag x y
  obtain ⟨hint, _⟩ := LocalDivAux.kernel_int hρ hRm hmeas hbd hgi x
  refine ⟨hint, ?_⟩
  have hmeas' : Measurable fun p : Torus d × Torus d => |H p.1 p.2| := hmeas.abs
  have hbd' : ∀ x y, |(fun x y => |H x y|) x y| ≤ g (Torus.eucDist x y) := by
    intro x y; simpa using hbd x y
  obtain ⟨_, hb'⟩ := LocalDivAux.kernel_int hρ hRm hmeas' hbd' hgi x
  refine (le_abs_self _).trans (hb'.trans (le_of_eq ?_))
  have : ∫ w in LocalDivAux.cube d, g ‖w‖ = B * ∫ w in LocalDivAux.cube d, envW d σ b w := by
    rw [← integral_const_mul]; rfl
  rw [this]
  ring

lemma measurable_of_conormal {σ : ℝ} {b : ℕ} {B : ℝ} {H : Torus d → Torus d → ℝ}
    (hH : Conormal σ b 0 B H) (hdiag : ∀ x, H x x = 0) :
    Measurable fun p : Torus d × Torus d => H p.1 p.2 := by
  have := measurable_offZero_of_contDiffOn (F := H) (m := 0) hH.smooth
  have e : Function.uncurry (offZero H) = fun p : Torus d × Torus d => H p.1 p.2 := by
    funext p
    by_cases h : p.1 = p.2
    · simp [Function.uncurry, offZero, h, hdiag]
    · simp [Function.uncurry, offZero, h]
  rw [← e]; exact this

theorem conormal_prod_int (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {σ : ℝ}
    (hσ : σ < d) (b : ℕ) {B : ℝ} (hB : 0 ≤ B) {H : Torus d → Torus d → ℝ} (hH : Conormal σ b 0 B H)
    (hdiag : ∀ x, H x x = 0) :
    Integrable (fun p : Torus d × Torus d => H p.1 p.2) ((withDensityReal ρ).prod (withDensityReal ρ)) := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨K, hK0, hK⟩ := conormal_row_int hd hρ hσ b
  have hmeas := measurable_of_conormal hH hdiag
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun x => (hK B H hB hH hdiag x).1, ?_⟩
  have hm2 : AEStronglyMeasurable (fun x => ∫ y, ‖H x y‖ ∂(withDensityReal ρ)) (withDensityReal ρ) :=
    (hmeas.norm.aestronglyMeasurable (μ := (withDensityReal ρ).prod (withDensityReal ρ))).integral_prod_right'
  refine Integrable.of_bound hm2 (K * B) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
  simpa [Real.norm_eq_abs] using (hK B H hB hH hdiag x).2

end HRS.Parx

end
