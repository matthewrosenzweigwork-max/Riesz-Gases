import HRS.MS.S104eC1I
import HRS.MS.S104eC1F

/-!
# S104E route C, packet C1 (part J): the top-order jet of `P_h g` for `g ∈ C^j_b` (Stein formula) and `VanB` gain

`s104c1_top`: for `h > 0`, `g ∈ Bd j B`, `m : Fin (j+1) → ℝ^d`:
`D^{j+1}(P_h g)(x) m = (c^{j+1}/σ) ∫ D^j g (c x + σ z) (tail m) ⟪z, m 0⟫ dγ(z)` (`c = e^{-ah}`, `σ = σ_h`).
`s104c1_vgain`: `g ∈ Bd j` with vanishing `j`-jets gives vanishing `(j+1)`-jets of `P_h g`, `h > 0`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ContDiff RealInnerProductSpace

namespace HRS.MS.S104e.C
open HRS HRS.Whole HRS.MS.R2WinOrbNL HRS.MS.Ul HRS.MS.Wad
variable {d : ℕ}

theorem s104c1_top {a ν τ : ℝ} (ha : 0 < a) (hν : 0 < ν) (hτ : 0 < τ) {j : ℕ} {B : ℝ} {g : Euc d → ℝ}
    (hg : Bd j B g) (x : Euc d) (m : Fin (j + 1) → Euc d) :
    iteratedFDeriv ℝ (j + 1) (ouSg (ouQ d a) ν τ g) x m =
      (Real.exp (-a * τ) ^ (j + 1) / s83_ms a ν τ) *
        ∫ z, iteratedFDeriv ℝ j g (Real.exp (-a * τ) • x + s83_ms a ν τ • z) (Fin.tail m) *
          ⟪z, m 0⟫ ∂(stdGaussian (Euc d)) := by
  have hgc : Continuous g := hg.1.continuous
  have hOP := s104c1_ouSg ha hν.le hτ.le hgc
  obtain ⟨K, s0, hK, hs0, hcore⟩ := s104c1_gain_core (d := d) a ν τ ha hν
  have hC := (hcore j hg hτ le_rfl).1
  have hCu : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (ouSg (ouQ d a) ν τ g) := by rw [hOP]; exact hC
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ j (ouSg (ouQ d a) ν τ g)) :=
    hCu.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self j)
  rw [iteratedFDeriv_succ_apply_left]
  set V : Fin j → Euc d := Fin.tail m with hV
  set w : Euc d := m 0 with hw
  set c : ℝ := Real.exp (-a * τ) with hc
  set σ : ℝ := s83_ms a ν τ with hσ
  have hσ0 : 0 < σ := s83_ms_pos ha hν hτ
  have hcabs : |c| ≤ 1 := s83_abs_mc_le_one ha.le hτ.le
  have hσabs : |σ| ≤ Real.sqrt (ν / a) := s83_abs_ms_le ha hν.le hτ.le
  set φ : Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ := iteratedFDeriv ℝ j g with hφ
  have hφc : Continuous φ := hg.1.continuous_iteratedFDeriv (by exact_mod_cast le_rfl)
  have hφb : ∀ y, ‖φ y‖ ≤ B := fun y => hg.2 j le_rfl y
  set gV : Euc d → ℝ := fun y => φ y V with hgV
  have hAV : Continuous (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ V) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ V).continuous
  have hgVc : Continuous gV := hAV.comp hφc
  have hgVb : Wt 0 (B * ∏ i, ‖V i‖) gV := fun y => by
    simp only [Real.rpow_zero, mul_one]
    calc ‖gV y‖ ≤ ‖φ y‖ * ∏ i, ‖V i‖ := (φ y).le_opNorm V
      _ ≤ B * ∏ i, ‖V i‖ := mul_le_mul_of_nonneg_right (hφb y) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have hform : ∀ y, iteratedFDeriv ℝ j (ouSg (ouQ d a) ν τ g) y V = c ^ j * s83_G c σ gV y := by
    intro y
    rw [s104c1_Drep ha hν.le hg hτ.le le_rfl y]
    have hint : Integrable (fun z : Euc d => φ (c • y + σ • z)) (stdGaussian (Euc d)) :=
      Integrable.of_bound (C := B) (hφc.comp (by fun_prop)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => hφb _)
    rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul, ContinuousMultilinearMap.integral_apply hint]
    rfl
  have hderiv : HasFDerivAt (fun y => iteratedFDeriv ℝ j (ouSg (ouQ d a) ν τ g) y V)
      (c ^ j • ((c / σ) • innerSL ℝ (s84_S c σ gV x))) x := by
    have h1 := (s84_G_hasFDerivAt hgVc (le_refl (0 : ℝ)) hgVb hcabs hσabs hσ0.ne' x).const_mul (c ^ j)
    have e : (fun y => iteratedFDeriv ℝ j (ouSg (ouQ d a) ν τ g) y V) = fun y => c ^ j * s83_G c σ gV y :=
      funext hform
    rw [e]; exact h1
  have hL := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ V).hasFDerivAt.comp x (hdiff x).hasFDerivAt
  have huniq := hL.unique hderiv
  have hw' : (fderiv ℝ (iteratedFDeriv ℝ j (ouSg (ouQ d a) ν τ g)) x w) V =
      c ^ j * ((c / σ) * ⟪s84_S c σ gV x, w⟫) := by
    have := congrArg (fun L : Euc d →L[ℝ] ℝ => L w) huniq
    simpa [innerSL_apply_apply] using this
  rw [hw']
  have hInt := s84_Fu_integrable hgVc (le_refl (0 : ℝ)) hgVb hcabs hσabs x
  have hin : ⟪s84_S c σ gV x, w⟫ = ∫ z, gV (c • x + σ • z) * ⟪z, w⟫ ∂(stdGaussian (Euc d)) := by
    unfold s84_S
    rw [real_inner_comm, ← integral_inner hInt w]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp [real_inner_smul_right, real_inner_comm]
  rw [hin]
  rw [pow_succ]
  field_simp
  try rfl

theorem s104c1_top_norm {a ν τ : ℝ} (ha : 0 < a) (hν : 0 < ν) (hτ : 0 < τ) {j : ℕ} {B : ℝ} {g : Euc d → ℝ}
    (hg : Bd j B g) (x : Euc d) :
    ‖iteratedFDeriv ℝ (j + 1) (ouSg (ouQ d a) ν τ g) x‖ ≤
      (Real.exp (-a * τ) ^ (j + 1) / s83_ms a ν τ) *
        ∫ z, ‖iteratedFDeriv ℝ j g (Real.exp (-a * τ) • x + s83_ms a ν τ • z)‖ * ‖z‖
          ∂(stdGaussian (Euc d)) := by
  have hσ0 : 0 < s83_ms a ν τ := s83_ms_pos ha hν hτ
  set c : ℝ := Real.exp (-a * τ) with hc
  set σ : ℝ := s83_ms a ν τ with hσ
  have hcpos : 0 < c := Real.exp_pos _
  set φ : Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ := iteratedFDeriv ℝ j g with hφ
  have hφc : Continuous φ := hg.1.continuous_iteratedFDeriv (by exact_mod_cast le_rfl)
  have hφb : ∀ y, ‖φ y‖ ≤ B := fun y => hg.2 j le_rfl y
  set J : ℝ := ∫ z, ‖φ (c • x + σ • z)‖ * ‖z‖ ∂(stdGaussian (Euc d)) with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hK0 : 0 ≤ c ^ (j + 1) / σ := by positivity
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  rw [s104c1_top ha hν hτ hg x m, norm_mul, Real.norm_eq_abs, abs_of_nonneg hK0]
  have hint : Integrable (fun z : Euc d => ‖φ (c • x + σ • z)‖ * ‖z‖) (stdGaussian (Euc d)) :=
    (s104c1_int_norm.const_mul B).mono'
      (((hφc.comp (by fun_prop)).norm.aestronglyMeasurable).mul s104c1_int_norm.1)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
        exact mul_le_mul_of_nonneg_right (hφb _) (norm_nonneg _))
  have hP : ∏ i : Fin (j + 1), ‖m i‖ = ‖m 0‖ * ∏ i : Fin j, ‖Fin.tail m i‖ := by
    rw [Fin.prod_univ_succ]; rfl
  have hP0 : 0 ≤ ∏ i : Fin (j + 1), ‖m i‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hI : ‖∫ z, φ (c • x + σ • z) (Fin.tail m) * ⟪z, m 0⟫ ∂(stdGaussian (Euc d))‖ ≤
      J * ∏ i : Fin (j + 1), ‖m i‖ := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hbd : ∀ z : Euc d, ‖φ (c • x + σ • z) (Fin.tail m) * ⟪z, m 0⟫‖ ≤
        (‖φ (c • x + σ • z)‖ * ‖z‖) * ∏ i : Fin (j + 1), ‖m i‖ := by
      intro z
      rw [norm_mul, hP]
      have h1 : ‖φ (c • x + σ • z) (Fin.tail m)‖ ≤ ‖φ (c • x + σ • z)‖ * ∏ i : Fin j, ‖Fin.tail m i‖ :=
        (φ (c • x + σ • z)).le_opNorm _
      have h2 : ‖⟪z, m 0⟫‖ ≤ ‖z‖ * ‖m 0‖ := norm_inner_le_norm _ _
      calc _ ≤ (‖φ (c • x + σ • z)‖ * ∏ i : Fin j, ‖Fin.tail m i‖) * (‖z‖ * ‖m 0‖) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hint2 : Integrable (fun z : Euc d => φ (c • x + σ • z) (Fin.tail m) * ⟪z, m 0⟫)
        (stdGaussian (Euc d)) := by
      refine (hint.mul_const (∏ i : Fin (j + 1), ‖m i‖)).mono' ?_ (Filter.Eventually.of_forall hbd)
      refine (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ (Fin.tail m)).continuous.comp
        (hφc.comp (by fun_prop))).aestronglyMeasurable).mul ?_
      exact (continuous_id.inner continuous_const).aestronglyMeasurable
    calc ∫ z, ‖φ (c • x + σ • z) (Fin.tail m) * ⟪z, m 0⟫‖ ∂(stdGaussian (Euc d))
        ≤ ∫ z, (‖φ (c • x + σ • z)‖ * ‖z‖) * ∏ i : Fin (j + 1), ‖m i‖ ∂(stdGaussian (Euc d)) :=
          integral_mono hint2.norm (hint.mul_const _) hbd
      _ = J * ∏ i : Fin (j + 1), ‖m i‖ := by rw [integral_mul_const]
  calc c ^ (j + 1) / σ * ‖∫ z, φ (c • x + σ • z) (Fin.tail m) * ⟪z, m 0⟫ ∂(stdGaussian (Euc d))‖
      ≤ c ^ (j + 1) / σ * (J * ∏ i : Fin (j + 1), ‖m i‖) := mul_le_mul_of_nonneg_left hI hK0
    _ = _ := by ring

theorem s104c1_vgain {a ν : ℝ} (ha : 0 < a) (hν : 0 < ν) {h : ℝ} (hh : 0 < h) {j : ℕ} {B : ℝ}
    {g : Euc d → ℝ} (hg : Bd j B g) (hv : VanB j g) : VanB (j + 1) (ouSg (ouQ d a) ν h g) := by
  intro i hi
  rcases Nat.lt_or_ge i (j + 1) with hi' | hi'
  · exact s104c1_vanB ha hν.le hg hv hh.le i (by omega)
  · have hij : i = j + 1 := le_antisymm hi hi'
    subst hij
    have hφc : Continuous (iteratedFDeriv ℝ j g) := hg.1.continuous_iteratedFDeriv (by exact_mod_cast le_rfl)
    have key := s104c1_van_w (s := s83_ms a ν h) hφc (fun y => hg.2 j le_rfl y) (hv j le_rfl)
      (Real.exp_pos (-a * h)).ne' (w := fun z : Euc d => ‖z‖) s104c1_int_norm (fun _ => norm_nonneg _)
    have key2 := key.const_mul (Real.exp (-a * h) ^ (j + 1) / s83_ms a ν h)
    rw [mul_zero] at key2
    exact squeeze_zero (fun x => norm_nonneg _) (fun x => s104c1_top_norm ha hν hh hg x) key2

end HRS.MS.S104e.C
