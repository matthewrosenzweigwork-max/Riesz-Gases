/-
# HRS.Equilibrium.Q84bAuxH — packet Q84b: the integration-by-parts identity for `Jop`
-/
import HRS.Equilibrium.Q84bAuxG

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84b

variable {d : ℕ} {s : ℝ}

/-- The integrand of the double integral on the force side. -/
def q84b_Phi (ρ : Torus d → ℝ) (s : ℝ) (ψ : Torus d → Torus d → ℝ) (b : Torus d)
    (p : Torus d × Torus d) : ℝ :=
  inner ℝ (HRS.KernelGrad.kern (periodicRieszGrad d s) ρ p.1 p.2) (gradFst ψ p.1 b) * ρ p.1

theorem q84b_measurable_kern_prod (hsd : s < d) {ρ : Torus d → ℝ} (hρc : Continuous ρ) :
    Measurable (fun p : Torus d × Torus d => HRS.KernelGrad.kern (periodicRieszGrad d s) ρ p.1 p.2) := by
  have hG : Measurable (periodicRieszGrad d s : Torus d → Euc d) :=
    HRS.KernelGrad.measurable_periodicRieszGrad hsd
  unfold HRS.KernelGrad.kern
  refine Measurable.ite (measurableSet_le (measurable_norm.comp measurable_snd) measurable_const) ?_ ?_
  · exact ((hρc.measurable.comp (measurable_fst.sub measurable_snd)).sub
      (hρc.measurable.comp measurable_fst)).smul (hG.comp measurable_snd)
  · exact (hρc.measurable.comp (measurable_fst.sub measurable_snd)).smul (hG.comp measurable_snd)

theorem q84b_Phi_integrable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {ρ : Torus d → ℝ}
    (hρ1 : Torus.IsCk 1 ρ) {K : ℝ} {ψ : Torus d → Torus d → ℝ} (hPs : PsiSize s K ψ) (b : Torus d) :
    Integrable (q84b_Phi ρ s ψ b) ((volume : Measure (Torus d)).prod volume) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  have hs0 : 0 ≤ s := by linarith
  have hsd : s < d := by rw [hcrit]; linarith
  have hd0 : 0 < d := by omega
  obtain ⟨Cg, hGood⟩ := HRS.KernelGrad.goodKernel_periodicRieszGrad hd hs0 hsd
  obtain ⟨Bρ, hBρ0, hBρ⟩ := HRS.KernelGrad.isCk_bounded hρ1
  obtain ⟨L, hL0, hL⟩ := HRS.KernelGrad.isLipschitz_of_isCk hρ1
  have hρc : Continuous ρ := HRS.PDE.MFAux.continuous_of_isCk hρ1
  have hwi := q84b_w_integrable hd hcrit b
  have hwi' : Integrable (fun x : Torus d => wEnv s x b) := by
    simpa [PairCorrAux.wEnv_symm s _ b] using hwi
  have hdi := HRS.KernelGrad.integrable_dom hGood L Bρ
  set BB : Torus d × Torus d → ℝ := fun p =>
    Bρ * K * (wEnv s p.1 b * HRS.KernelGrad.dom s Cg L Bρ d p.2) with hBB
  have hBBi : Integrable BB ((volume : Measure (Torus d)).prod volume) :=
    (hwi'.mul_prod hdi).const_mul (Bρ * K)
  have hΦm : Measurable (q84b_Phi ρ s ψ b) := by
    unfold q84b_Phi
    exact (Measurable.inner (q84b_measurable_kern_prod hsd hρc)
      ((q84b_measurable_gradFst ψ b).comp measurable_fst)).mul (hρc.measurable.comp measurable_fst)
  have hBBm : Measurable BB := by
    have hdm : Measurable (HRS.KernelGrad.dom s Cg L Bρ d : Torus d → ℝ) := by
      unfold HRS.KernelGrad.dom
      exact measurable_const.mul ((measurable_norm.pow_const _).add measurable_const) |>.add measurable_const
    exact measurable_const.mul (((q84b_measurable_w_left b).comp measurable_fst).mul
      (hdm.comp measurable_snd))
  refine Integrable.mono' hBBi hΦm.aestronglyMeasurable ?_
  have hset : MeasurableSet {p : Torus d × Torus d | ‖q84b_Phi ρ s ψ b p‖ ≤ BB p} :=
    measurableSet_le hΦm.norm hBBm
  refine (Measure.ae_prod_iff_ae_ae hset).2 ?_
  filter_upwards [q84b_ae_ne hd0 b] with x hx
  filter_upwards [HRS.KernelGrad.kern_bound_ae hGood hBρ hL hL0 hBρ0 x] with u hu
  show ‖q84b_Phi ρ s ψ b (x, u)‖ ≤ BB (x, u)
  have hD := Q84a.q84a_grad_le_w hs1 hPs hx
  simp only [q84b_Phi, hBB, norm_mul, Real.norm_eq_abs]
  have h1 := abs_real_inner_le_norm (HRS.KernelGrad.kern (periodicRieszGrad d s) ρ x u) (gradFst ψ x b)
  have h2 : ‖HRS.KernelGrad.kern (periodicRieszGrad d s) ρ x u‖ * ‖gradFst ψ x b‖ ≤
      HRS.KernelGrad.dom s Cg L Bρ d u * (K * wEnv s x b) :=
    mul_le_mul hu hD (norm_nonneg _) ((norm_nonneg _).trans hu)
  have h3 := hBρ x
  calc |inner ℝ (HRS.KernelGrad.kern (periodicRieszGrad d s) ρ x u) (gradFst ψ x b)| * |ρ x|
      ≤ (HRS.KernelGrad.dom s Cg L Bρ d u * (K * wEnv s x b)) * Bρ :=
        mul_le_mul (h1.trans h2) h3 (abs_nonneg _) ((abs_nonneg _).trans (h1.trans h2))
    _ = _ := by ring


/-- Vector-valued `x`-integral appearing after the interchange of integrations. -/
def q84b_Ev (ρ : Torus d → ℝ) (ψ : Torus d → Torus d → ℝ) (b u : Torus d) : Euc d :=
  ∫ x, ((ρ (x - u) - (if ‖u‖ ≤ 1 / 4 then ρ x else 0)) * ρ x) • gradFst ψ x b

/-- `∇_xψ(·,b)` is integrable. -/
theorem q84b_gradFst_integrable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {K : ℝ}
    {ψ : Torus d → Torus d → ℝ} (hPs : PsiSize s K ψ) (b : Torus d) :
    Integrable (fun x => gradFst ψ x b) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  have hd0 : 0 < d := by omega
  have hwi := q84b_w_integrable hd hcrit b
  have hwi' : Integrable (fun x : Torus d => wEnv s x b) := by
    simpa [PairCorrAux.wEnv_symm s _ b] using hwi
  refine Integrable.mono' (hwi'.const_mul K) (q84b_measurable_gradFst ψ b).aestronglyMeasurable ?_
  filter_upwards [q84b_ae_ne hd0 b] with x hx
  exact Q84a.q84a_grad_le_w hs1 hPs hx

theorem q84b_Ev_integrand (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {ρ : Torus d → ℝ}
    (hρ1 : Torus.IsCk 1 ρ) {K : ℝ} {ψ : Torus d → Torus d → ℝ} (hPs : PsiSize s K ψ) (b u : Torus d) :
    Integrable (fun x => ((ρ (x - u) - (if ‖u‖ ≤ 1 / 4 then ρ x else 0)) * ρ x) • gradFst ψ x b) := by
  obtain ⟨Bρ, hBρ0, hBρ⟩ := HRS.KernelGrad.isCk_bounded hρ1
  have hρc : Continuous ρ := HRS.PDE.MFAux.continuous_of_isCk hρ1
  have hD := q84b_gradFst_integrable hd hcrit hPs b
  refine Integrable.bdd_smul (φ := fun x => (ρ (x - u) - (if ‖u‖ ≤ 1 / 4 then ρ x else 0)) * ρ x)
    hD (Bρ * Bρ + Bρ * Bρ) ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    refine Measurable.mul (Measurable.sub (hρc.measurable.comp (measurable_id.sub measurable_const)) ?_)
      hρc.measurable
    split_ifs
    · exact hρc.measurable
    · exact measurable_const
  · refine Eventually.of_forall fun x => ?_
    simp only [Real.norm_eq_abs, abs_mul]
    have h1 := hBρ x
    have h2 := hBρ (x - u)
    have h3 : |ρ (x - u) - (if ‖u‖ ≤ 1 / 4 then ρ x else 0)| ≤ Bρ + Bρ := by
      refine (abs_sub _ _).trans (add_le_add h2 ?_)
      split_ifs
      · exact h1
      · simpa using hBρ0
    calc |ρ (x - u) - (if ‖u‖ ≤ 1 / 4 then ρ x else 0)| * |ρ x| ≤ (Bρ + Bρ) * Bρ :=
          mul_le_mul h3 h1 (abs_nonneg _) (by linarith)
      _ ≤ Bρ * Bρ + Bρ * Bρ := by nlinarith


theorem q84b_int_mul_inner {D : Torus d → Euc d} (hD : Integrable D) {φ : Torus d → ℝ}
    (hφ : Measurable φ) {C : ℝ} (hC : ∀ x, |φ x| ≤ C) (v : Euc d) :
    Integrable (fun y => φ y * inner ℝ v (D y)) := by
  have := (Integrable.bdd_smul (φ := φ) hD C hφ.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa using hC x)).const_inner (𝕜 := ℝ) v
  refine this.congr (Eventually.of_forall fun y => ?_)
  simp [real_inner_smul_right]

theorem q84b_inner_x_Psi (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {ρ : Torus d → ℝ}
    (hρ1 : Torus.IsCk 1 ρ) {K : ℝ} {ψ : Torus d → Torus d → ℝ} (hPs : PsiSize s K ψ)
    (b u : Torus d) :
    ∫ x, q84b_Psi ρ s ψ b (x, u) =
      inner ℝ (periodicRieszGrad d s u) (q84b_Ev ρ ψ b (-u)) -
        inner ℝ (periodicRieszGrad d s u) (q84b_Ev ρ ψ b u) := by
  obtain ⟨Bρ, hBρ0, hBρ⟩ := HRS.KernelGrad.isCk_bounded hρ1
  have hρc : Continuous ρ := HRS.PDE.MFAux.continuous_of_isCk hρ1
  have hD := q84b_gradFst_integrable hd hcrit hPs b
  set Gu := periodicRieszGrad d s u with hGu
  have hBB : ∀ φ : Torus d → ℝ, (∀ x, |φ x| ≤ Bρ * Bρ) → Measurable φ →
      Integrable (fun y => φ y * inner ℝ Gu (gradFst ψ y b)) := fun φ h hm =>
    q84b_int_mul_inner hD hm h Gu
  have hQi : Integrable (fun y => ρ (y + u) * ρ y * inner ℝ Gu (gradFst ψ y b)) := by
    refine hBB (fun y => ρ (y + u) * ρ y) (fun y => ?_) ?_
    · rw [abs_mul]; exact mul_le_mul (hBρ _) (hBρ _) (abs_nonneg _) hBρ0
    · exact (hρc.measurable.comp (measurable_id.add measurable_const)).mul hρc.measurable
  have hS2i : Integrable (fun x => ρ x * ρ (x - u) * inner ℝ Gu (gradFst ψ x b)) := by
    refine hBB (fun x => ρ x * ρ (x - u)) (fun x => ?_) ?_
    · rw [abs_mul]; exact mul_le_mul (hBρ _) (hBρ _) (abs_nonneg _) hBρ0
    · exact hρc.measurable.mul (hρc.measurable.comp (measurable_id.sub measurable_const))
  have e1 : ∀ x, q84b_Psi ρ s ψ b (x, u) =
      (fun y => ρ (y + u) * ρ y * inner ℝ Gu (gradFst ψ y b)) (x - u) -
        ρ x * ρ (x - u) * inner ℝ Gu (gradFst ψ x b) := by
    intro x
    simp only [q84b_Psi, inner_sub_right, sub_add_cancel]
    ring
  simp_rw [e1]
  rw [integral_sub (hQi.comp_sub_right u) hS2i, integral_sub_right_eq_self
    (fun y => ρ (y + u) * ρ y * inner ℝ Gu (gradFst ψ y b)) u, ← integral_sub hQi hS2i]
  have e2 : ∀ y, ρ (y + u) * ρ y * inner ℝ Gu (gradFst ψ y b) -
      ρ y * ρ (y - u) * inner ℝ Gu (gradFst ψ y b) =
      inner ℝ Gu (((ρ (y - -u) - (if ‖-u‖ ≤ 1 / 4 then ρ y else 0)) * ρ y) • gradFst ψ y b) -
        inner ℝ Gu (((ρ (y - u) - (if ‖u‖ ≤ 1 / 4 then ρ y else 0)) * ρ y) • gradFst ψ y b) := by
    intro y
    simp only [real_inner_smul_right, sub_neg_eq_add, norm_neg]
    split_ifs <;> ring
  simp_rw [e2]
  rw [integral_sub ((q84b_Ev_integrand hd hcrit hρ1 hPs b (-u)).const_inner Gu)
    ((q84b_Ev_integrand hd hcrit hρ1 hPs b u).const_inner Gu),
    integral_inner (q84b_Ev_integrand hd hcrit hρ1 hPs b (-u)),
    integral_inner (q84b_Ev_integrand hd hcrit hρ1 hPs b u)]
  rfl


theorem q84b_Phi_u (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ1 : Torus.IsCk 1 ρ) {ψ : Torus d → Torus d → ℝ} (b x : Torus d)
    (hforce : forceField d s ρ x = convGradConv (periodicRieszGrad d s) ρ x) :
    ∫ u, q84b_Phi ρ s ψ b (x, u) = ρ x * inner ℝ (forceField d s ρ x) (gradFst ψ x b) := by
  obtain ⟨Cg, hGood⟩ := HRS.KernelGrad.goodKernel_periodicRieszGrad hd hs0 hsd
  obtain ⟨B, hB0, hB⟩ := HRS.KernelGrad.isCk_bounded hρ1
  obtain ⟨L, hL0, hL⟩ := HRS.KernelGrad.isLipschitz_of_isCk hρ1
  have hK : Integrable (HRS.KernelGrad.kern (periodicRieszGrad d s) ρ x) :=
    HRS.KernelGrad.integrable_kern hGood (HRS.PDE.MFAux.continuous_of_isCk hρ1).measurable hB hL hL0 hB0 x
  unfold q84b_Phi
  simp only
  rw [integral_mul_const]
  have : ∫ u, inner ℝ (HRS.KernelGrad.kern (periodicRieszGrad d s) ρ x u) (gradFst ψ x b) =
      inner ℝ (forceField d s ρ x) (gradFst ψ x b) := by
    calc ∫ u, inner ℝ (HRS.KernelGrad.kern (periodicRieszGrad d s) ρ x u) (gradFst ψ x b)
        = ∫ u, inner ℝ (gradFst ψ x b) (HRS.KernelGrad.kern (periodicRieszGrad d s) ρ x u) :=
          integral_congr_ae (Eventually.of_forall fun u => real_inner_comm _ _)
      _ = inner ℝ (gradFst ψ x b) (∫ u, HRS.KernelGrad.kern (periodicRieszGrad d s) ρ x u) :=
          integral_inner hK _
      _ = inner ℝ (forceField d s ρ x) (gradFst ψ x b) := by
          rw [← HRS.KernelGrad.convGradConv_eq_integral_kern, ← hforce, real_inner_comm]
  rw [this, mul_comm]

theorem q84b_Phi_x (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {ρ : Torus d → ℝ}
    (hρ1 : Torus.IsCk 1 ρ) {K : ℝ} {ψ : Torus d → Torus d → ℝ} (hPs : PsiSize s K ψ)
    (b u : Torus d) :
    ∫ x, q84b_Phi ρ s ψ b (x, u) = inner ℝ (periodicRieszGrad d s u) (q84b_Ev ρ ψ b u) := by
  unfold q84b_Ev
  rw [← integral_inner (q84b_Ev_integrand hd hcrit hρ1 hPs b u)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [q84b_Phi, HRS.KernelGrad.kern, real_inner_smul_right]
  split_ifs with h
  · simp only [real_inner_smul_left, h, if_true]
    rw [real_inner_comm (gradFst ψ x b)]
    ring
  · simp only [real_inner_smul_left, h, if_false]
    rw [real_inner_comm (gradFst ψ x b)]
    ring


/-- The antisymmetry identity: `∫ ρ(a) R(a) da = -2 ∫ ρ F·∇f`. -/
theorem q84b_Rk_mean (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {ρ : Torus d → ℝ}
    (hρ1 : Torus.IsCk 1 ρ) {K : ℝ} {ψ : Torus d → Torus d → ℝ} (hPs : PsiSize s K ψ) (b : Torus d)
    (hforce : ∀ x, forceField d s ρ x = convGradConv (periodicRieszGrad d s) ρ x) :
    Integrable (fun x => ρ x * ∫ u, q84b_Rk ρ s (fun w => ψ w b) x u) ∧
    Integrable (fun x => ρ x * inner ℝ (forceField d s ρ x) (gradFst ψ x b)) ∧
    ∫ x, ρ x * ∫ u, q84b_Rk ρ s (fun w => ψ w b) x u =
      -2 * ∫ x, ρ x * inner ℝ (forceField d s ρ x) (gradFst ψ x b) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  have hΨ := q84b_Psi_integrable hd hcrit hρ1 hPs b
  have hΦ := q84b_Phi_integrable hd hcrit hρ1 hPs b
  have hΨx : ∀ x, ∫ u, q84b_Psi ρ s ψ b (x, u) =
      ρ x * ∫ u, q84b_Rk ρ s (fun w => ψ w b) x u := by
    intro x
    rw [← integral_const_mul]
    rfl
  have hI1 : Integrable (fun x => ρ x * ∫ u, q84b_Rk ρ s (fun w => ψ w b) x u) := by
    have := hΨ.integral_prod_left
    simp only [hΨx] at this
    exact this
  have hΦx : ∀ x, ∫ u, q84b_Phi ρ s ψ b (x, u) =
      ρ x * inner ℝ (forceField d s ρ x) (gradFst ψ x b) := fun x =>
    q84b_Phi_u hd hs0 hsd hρ1 b x (hforce x)
  have hI2 : Integrable (fun x => ρ x * inner ℝ (forceField d s ρ x) (gradFst ψ x b)) := by
    have := hΦ.integral_prod_left
    simp only [hΦx] at this
    exact this
  refine ⟨hI1, hI2, ?_⟩
  -- the interchange of integrations
  have hθ : Integrable (fun u => inner ℝ (periodicRieszGrad d s u) (q84b_Ev ρ ψ b u)) := by
    have := hΦ.integral_prod_right
    simp only [q84b_Phi_x hd hcrit hρ1 hPs b] at this
    exact this
  have hθmean : ∫ u, inner ℝ (periodicRieszGrad d s u) (q84b_Ev ρ ψ b u) =
      ∫ x, ρ x * inner ℝ (forceField d s ρ x) (gradFst ψ x b) := by
    have := integral_integral_swap (f := fun x u => q84b_Phi ρ s ψ b (x, u)) hΦ
    simp only [hΦx, q84b_Phi_x hd hcrit hρ1 hPs b] at this
    exact this.symm
  have hswap := integral_integral_swap (f := fun x u => q84b_Psi ρ s ψ b (x, u)) hΨ
  simp only [hΨx, q84b_inner_x_Psi hd hcrit hρ1 hPs b] at hswap
  rw [hswap, ← hθmean]
  -- `∫ ⟨G u, Ev (-u)⟩ = - ∫ ⟨G u, Ev u⟩`
  have hodd : ∀ u, periodicRieszGrad d s (-u) = -periodicRieszGrad d s u := fun u =>
    HRS.KernelGrad.periodicRieszGrad_neg_of_lt hsd u
  have hneg : ∀ u, inner ℝ (periodicRieszGrad d s u) (q84b_Ev ρ ψ b (-u)) =
      -(fun v => inner ℝ (periodicRieszGrad d s v) (q84b_Ev ρ ψ b v)) (-u) := by
    intro u
    simp only [hodd, inner_neg_left, neg_neg]
  have hnegi : Integrable (fun u => inner ℝ (periodicRieszGrad d s u) (q84b_Ev ρ ψ b (-u))) := by
    simp_rw [hneg]
    exact (hθ.comp_neg).neg
  rw [integral_sub hnegi hθ]
  simp_rw [hneg]
  rw [integral_neg, integral_neg_eq_self (fun v => inner ℝ (periodicRieszGrad d s v) (q84b_Ev ρ ψ b v))]
  ring

end HRS.Q84b
