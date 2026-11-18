import HRS.MS.SA16RVol3

/-!
# S.A.16 (SA16R) Vol4: existence and uniqueness of the Volterra solution

`sa16r_volt_exists_unique`: for `VoltKer T C P`, `T > 0` and `f0` continuous on `[0,T]` there is `u`, continuous on
`[0,T]`, with `u τ = f0 τ + voltOp P u τ` on `[0,T]`, and every continuous solution agrees with `u` on `[0,T]`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16R

section Volt4
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- clamped extension of a continuous function on `[0,T]` -/
def sa16r_ext {T : ℝ} (hT : 0 ≤ T) (w : C(Icc (0 : ℝ) T, X)) : ℝ → X :=
  fun r => w (Set.projIcc 0 T hT r)

lemma sa16r_ext_cont {T : ℝ} (hT : 0 ≤ T) (w : C(Icc (0 : ℝ) T, X)) :
    Continuous (sa16r_ext hT w) := w.continuous.comp continuous_projIcc

lemma sa16r_ext_apply {T : ℝ} (hT : 0 ≤ T) (w : C(Icc (0 : ℝ) T, X)) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) :
    sa16r_ext hT w r = w ⟨r, hr⟩ := by
  simp [sa16r_ext, Set.projIcc_of_mem hT hr]

/-- the weighted Duhamel map on `C([0,T];X)` -/
def sa16r_Psi {T C : ℝ} (P : ℝ → ℝ → X →L[ℝ] X) (hP : VoltKer T C P) (hT : 0 < T) (f0 : ℝ → X)
    (hf0 : ContinuousOn f0 (Icc 0 T)) {lam : ℝ} (hl : 0 ≤ lam) (w : C(Icc (0 : ℝ) T, X)) :
    C(Icc (0 : ℝ) T, X) :=
  ⟨fun τ => Real.exp (-lam * (τ : ℝ)) • f0 τ + voltOp (voltW P lam) (sa16r_ext hT.le w) τ, by
    have h1 : ContinuousOn (fun τ : ℝ => Real.exp (-lam * τ) • f0 τ + voltOp (voltW P lam)
        (sa16r_ext hT.le w) τ) (Icc 0 T) := by
      have h2 : ContinuousOn (fun τ : ℝ => Real.exp (-lam * τ)) (Icc 0 T) := by fun_prop
      exact (h2.smul hf0).add (sa16r_volt_contOn (hP.weight hl) hT (sa16r_ext_cont hT.le w).continuousOn)
    exact continuousOn_iff_continuous_domRestrict.1 h1⟩

lemma sa16r_Psi_apply {T C : ℝ} (P : ℝ → ℝ → X →L[ℝ] X) (hP : VoltKer T C P) (hT : 0 < T) (f0 : ℝ → X)
    (hf0 : ContinuousOn f0 (Icc 0 T)) {lam : ℝ} (hl : 0 ≤ lam) (w : C(Icc (0 : ℝ) T, X))
    (τ : Icc (0 : ℝ) T) :
    sa16r_Psi P hP hT f0 hf0 hl w τ = Real.exp (-lam * (τ : ℝ)) • f0 τ +
      voltOp (voltW P lam) (sa16r_ext hT.le w) τ := rfl

theorem sa16r_volt_exists_unique {T C : ℝ} {P : ℝ → ℝ → X →L[ℝ] X} (hP : VoltKer T C P) (hT : 0 < T)
    {f0 : ℝ → X} (hf0 : ContinuousOn f0 (Icc 0 T)) :
    ∃ u : ℝ → X, ContinuousOn u (Icc 0 T) ∧ (∀ τ ∈ Icc (0 : ℝ) T, u τ = f0 τ + voltOp P u τ) ∧
      ∀ v : ℝ → X, ContinuousOn v (Icc 0 T) → (∀ τ ∈ Icc (0 : ℝ) T, v τ = f0 τ + voltOp P v τ) →
        ∀ τ ∈ Icc (0 : ℝ) T, v τ = u τ := by
  have hC := hP.C_nonneg hT
  obtain ⟨lam, hl, hk⟩ := sa16r_kappa_small T (ε := 1 / (2 * (C + 1))) (by positivity)
  have hK : C * sa16r_kappa T lam ≤ 1 / 2 := by
    have h1 : C * sa16r_kappa T lam ≤ C * (1 / (2 * (C + 1))) :=
      mul_le_mul_of_nonneg_left hk hC
    have h2 : C * (1 / (2 * (C + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    exact h1.trans h2
  set Ψ := sa16r_Psi P hP hT f0 hf0 hl with hΨdef
  have hcontr : ContractingWith (1 / 2 : ℝ≥0) Ψ := by
    refine ⟨by
      rw [← NNReal.coe_lt_coe]; norm_num, LipschitzWith.of_dist_le_mul fun w w' => ?_⟩
    rw [dist_eq_norm]
    have hd : dist w w' = ‖w - w'‖ := dist_eq_norm _ _
    rw [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    have hB : ∀ r ∈ Icc (0 : ℝ) T, ‖sa16r_ext hT.le w r - sa16r_ext hT.le w' r‖ ≤ dist w w' := by
      intro r hr
      rw [sa16r_ext_apply hT.le w hr, sa16r_ext_apply hT.le w' hr, ← dist_eq_norm]
      exact ContinuousMap.dist_apply_le_dist _
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun τ => ?_
    rw [ContinuousMap.sub_apply, hΨdef, sa16r_Psi_apply, sa16r_Psi_apply, add_sub_add_left_eq_sub]
    refine (sa16r_volt_diff_le hP hT hl (sa16r_ext_cont hT.le w).continuousOn
      (sa16r_ext_cont hT.le w').continuousOn hB τ.2).trans ?_
    calc C * sa16r_kappa T lam * dist w w' ≤ (1 / 2) * dist w w' :=
          mul_le_mul_of_nonneg_right hK dist_nonneg
      _ = 1 / 2 * dist w w' := rfl
  -- the fixed point
  set w₀ := ContractingWith.fixedPoint Ψ hcontr with hw₀
  have hfix : Ψ w₀ = w₀ := ContractingWith.fixedPoint_isFixedPt hcontr
  let u : ℝ → X := fun τ => Real.exp (lam * τ) • sa16r_ext hT.le w₀ τ
  have hucont : ContinuousOn u (Icc 0 T) := by
    have : Continuous u := by
      have := sa16r_ext_cont hT.le w₀
      fun_prop
    exact this.continuousOn
  have e1 : ∀ τ : ℝ, Real.exp (lam * τ) * Real.exp (-lam * τ) = 1 := fun τ => by
    rw [← Real.exp_add]; simp
  -- solutions give fixed points
  have hsolfix : ∀ v : ℝ → X, ContinuousOn v (Icc 0 T) →
      (∀ τ ∈ Icc (0 : ℝ) T, v τ = f0 τ + voltOp P v τ) →
      ∃ w : C(Icc (0 : ℝ) T, X), (∀ τ : Icc (0 : ℝ) T, w τ = Real.exp (-lam * (τ : ℝ)) • v τ) ∧ Ψ w = w := by
    intro v hv hsol
    let w : C(Icc (0 : ℝ) T, X) := ⟨fun τ => Real.exp (-lam * (τ : ℝ)) • v τ, by
      have h1 : ContinuousOn (fun τ : ℝ => Real.exp (-lam * τ) • v τ) (Icc 0 T) := by
        have h2 : ContinuousOn (fun τ : ℝ => Real.exp (-lam * τ)) (Icc 0 T) := by fun_prop
        exact h2.smul hv
      exact continuousOn_iff_continuous_domRestrict.1 h1⟩
    refine ⟨w, fun τ => rfl, ?_⟩
    ext τ
    rw [hΨdef, sa16r_Psi_apply]
    have hcongr : voltOp (voltW P lam) (sa16r_ext hT.le w) τ =
        voltOp (voltW P lam) (fun r => Real.exp (-lam * r) • v r) τ := by
      refine sa16r_voltOp_congr _ τ.2.1 fun r hr => ?_
      have hr' : r ∈ Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans τ.2.2⟩
      rw [sa16r_ext_apply hT.le w hr']
      rfl
    rw [hcongr, sa16r_voltOp_weight P lam v τ.2.1 (hP.integrable_integrand hT hv τ.2.1 τ.2.2)]
    have hv' := hsol τ τ.2
    show Real.exp (-lam * (τ : ℝ)) • f0 τ + Real.exp (-lam * (τ : ℝ)) • voltOp P v τ =
      Real.exp (-lam * (τ : ℝ)) • v τ
    rw [← smul_add, ← hv']
  -- the fixed point solves the equation
  have hfixsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = f0 τ + voltOp P u τ := by
    intro τ hτ
    have h1 : w₀ ⟨τ, hτ⟩ = Real.exp (-lam * τ) • f0 τ +
        voltOp (voltW P lam) (sa16r_ext hT.le w₀) τ := by
      have := congrArg (fun w : C(Icc (0 : ℝ) T, X) => w ⟨τ, hτ⟩) hfix
      rw [hΨdef, sa16r_Psi_apply] at this
      exact this.symm
    have hcongr : voltOp (voltW P lam) (sa16r_ext hT.le w₀) τ =
        voltOp (voltW P lam) (fun r => Real.exp (-lam * r) • u r) τ := by
      refine sa16r_voltOp_congr _ hτ.1 fun r hr => ?_
      have hr' : r ∈ Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans hτ.2⟩
      simp only [u, smul_smul, ← Real.exp_add]
      simp
    rw [hcongr, sa16r_voltOp_weight P lam u hτ.1 (hP.integrable_integrand hT hucont hτ.1 hτ.2)] at h1
    have h2 : u τ = Real.exp (lam * τ) • w₀ ⟨τ, hτ⟩ := by
      simp [u, sa16r_ext_apply hT.le w₀ hτ]
    rw [h2, h1, smul_add, smul_smul, smul_smul, e1, one_smul, one_smul]
  refine ⟨u, hucont, hfixsol, fun v hv hsol τ hτ => ?_⟩
  obtain ⟨w, hw, hwfix⟩ := hsolfix v hv hsol
  have hweq : w = w₀ := by
    exact ContractingWith.fixedPoint_unique' hcontr hwfix hfix
  have h1 : w ⟨τ, hτ⟩ = Real.exp (-lam * τ) • v τ := hw ⟨τ, hτ⟩
  rw [hweq] at h1
  have h2 : u τ = Real.exp (lam * τ) • w₀ ⟨τ, hτ⟩ := by
    simp [u, sa16r_ext_apply hT.le w₀ hτ]
  rw [h2, h1, smul_smul, e1, one_smul]

end Volt4

end HRS.Whole.AppendixA.Phase2SA16R
