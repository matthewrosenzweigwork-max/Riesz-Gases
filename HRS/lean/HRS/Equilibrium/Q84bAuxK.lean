/-
# HRS.Equilibrium.Q84bAuxK — packet Q84b: the canonical row is differentiable under the integral
-/
import HRS.Equilibrium.Q84bAuxJ

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84b

variable {d : ℕ} {s : ℝ}

theorem q84b_psi_integrable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {K : ℝ}
    {ψ : Torus d → Torus d → ℝ} (hPs : PsiSize s K ψ) (hmeas : Measurable (Function.uncurry ψ))
    (p : Torus d) : Integrable (fun z => ψ p z) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  have hd0 : 0 < d := by omega
  refine Integrable.mono' ((q84b_w_integrable hd hcrit p).const_mul (2 * |K|))
    (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
  filter_upwards [q84b_ae_ne hd0 p] with z hz
  have hzp : p ≠ z := fun h => hz h.symm
  have h1 := q84b_size_le hs1 hPs hzp
  have hr := PairCorrAux.rTrunc_pos hzp
  have hr1 := PairCorrAux.rTrunc_le_one p z
  have hu : rTrunc p z ^ (1 - s) ≤ rTrunc p z ^ (-s) := by
    rw [Q84a.q84a_rpow_split hr]
    have : 0 ≤ rTrunc p z ^ (-s) := Real.rpow_nonneg hr.le _
    nlinarith
  rw [Real.norm_eq_abs]
  have hK : K ≤ |K| := le_abs_self K
  have hK0 : 0 ≤ |K| := abs_nonneg K
  have hA : 0 ≤ 1 + rTrunc p z ^ (1 - s) := by
    have := Real.rpow_nonneg hr.le (1 - s); linarith
  calc |ψ p z| ≤ 2 * K * (1 + rTrunc p z ^ (1 - s)) := h1
    _ ≤ 2 * |K| * (1 + rTrunc p z ^ (1 - s)) := by nlinarith
    _ ≤ 2 * |K| * wEnv s p z := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        unfold wEnv; linarith


theorem q84b_setint_psi (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {K : ℝ} {ψ : Torus d → Torus d → ℝ}
    (hPs : PsiSize s K ψ) (hmeas : Measurable (Function.uncurry ψ)) (p : Torus d)
    {N : Set (Torus d)} (hN : MeasurableSet N) {R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1)
    (hsub : ∀ z ∈ N, Torus.eucDist p z < R) :
    ∫ z in N, |ψ p z| ≤ 4 * |K| * R * (PairCorrAux.cdR d * ((1 / d + 1 / s) * R ^ s)) := by
  have hint := (q84b_psi_integrable hd hcrit hPs hmeas p).abs
  have hBm : MeasurableSet {z : Torus d | Torus.eucDist p z < R} :=
    measurableSet_lt (PairCorrAux.measurable_eucDist' p) measurable_const
  rw [← integral_indicator hN]
  refine le_trans ?_ (q84b_near_psi hd hcrit hPs p hR0 hR1)
  refine integral_mono (hint.indicator hN) (hint.indicator hBm) fun z => ?_
  refine Set.indicator_le_indicator_of_subset (fun z hz => hsub z hz) (fun z => abs_nonneg _) z

theorem q84b_near_part (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {ρ : Torus d → ℝ} {Bρ : ℝ}
    (hBρ0 : 0 ≤ Bρ) (hBρ : ∀ x, |ρ x| ≤ Bρ) (hρm : Measurable ρ) {K : ℝ}
    {ψ : Torus d → Torus d → ℝ} (hPs : PsiSize s K ψ) (hmeas : Measurable (Function.uncurry ψ))
    (x y : Torus d) {ε : ℝ} (hε0 : 0 < ε) (h3 : 3 * ε ≤ 1) (hy : Torus.eucDist x y ≤ ε) {t : ℝ}
    (ht : t ≠ 0) :
    ‖∫ z in {z : Torus d | Torus.eucDist x z < 2 * ε}, ρ z * (t⁻¹ * (ψ y z - ψ x z))‖ ≤
      Bρ * |t|⁻¹ * (2 * (4 * |K| * (3 * ε) *
        (PairCorrAux.cdR d * ((1 / d + 1 / s) * (3 * ε) ^ s)))) := by
  set N : Set (Torus d) := {z : Torus d | Torus.eucDist x z < 2 * ε} with hNdef
  have hNm : MeasurableSet N :=
    measurableSet_lt (PairCorrAux.measurable_eucDist' x) measurable_const
  have hR0 : 0 < 3 * ε := by linarith
  have hiy := q84b_psi_integrable hd hcrit hPs hmeas y
  have hix := q84b_psi_integrable hd hcrit hPs hmeas x
  have hf : Integrable (fun z => ρ z * (t⁻¹ * (ψ y z - ψ x z))) := by
    have := ((hiy.sub hix).const_mul t⁻¹).bdd_mul (c := Bρ) hρm.aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa using hBρ z)
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp
  have hbd : Integrable (fun z => Bρ * |t|⁻¹ * (|ψ y z| + |ψ x z|)) :=
    (hiy.abs.add hix.abs).const_mul _
  have h1 : ‖∫ z in N, ρ z * (t⁻¹ * (ψ y z - ψ x z))‖ ≤
      ∫ z in N, Bρ * |t|⁻¹ * (|ψ y z| + |ψ x z|) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine setIntegral_mono_on hf.norm.integrableOn hbd.integrableOn hNm fun z _ => ?_
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv]
    calc |ρ z| * (|t|⁻¹ * |ψ y z - ψ x z|) ≤ Bρ * (|t|⁻¹ * (|ψ y z| + |ψ x z|)) := by
          refine mul_le_mul (hBρ z) (mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity))
            (by positivity) hBρ0
      _ = _ := by ring
  have h2 : ∫ z in N, Bρ * |t|⁻¹ * (|ψ y z| + |ψ x z|) =
      Bρ * |t|⁻¹ * ((∫ z in N, |ψ y z|) + ∫ z in N, |ψ x z|) := by
    rw [integral_const_mul, integral_add hiy.abs.integrableOn hix.abs.integrableOn]
  refine h1.trans (h2.le.trans ?_)
  have e1 : ∀ z ∈ N, Torus.eucDist y z < 3 * ε := by
    intro z hz
    have hz' : Torus.eucDist x z < 2 * ε := hz
    have := PairCorrAux.eucDist_triangle y x z
    rw [PairCorrAux.eucDist_symm' y x] at this
    linarith
  have e2 : ∀ z ∈ N, Torus.eucDist x z < 3 * ε := by
    intro z hz
    have hz' : Torus.eucDist x z < 2 * ε := hz
    linarith
  have hy' := q84b_setint_psi hd hcrit hPs hmeas y hNm hR0 h3 e1
  have hx' := q84b_setint_psi hd hcrit hPs hmeas x hNm hR0 h3 e2
  have hpos : 0 ≤ Bρ * |t|⁻¹ := by positivity
  refine (mul_le_mul_of_nonneg_left (add_le_add hy' hx') hpos).trans (le_of_eq ?_)
  ring

end HRS.Q84b
