import HRS.Commutator.Torus.TUNITAux1
import HRS.Commutator.Torus.TENAux4
import HRS.Commutator.Torus.TKRAux13
import HRS.Commutator.Torus.TSAMPAux10
import HRS.Energy.Commutator.AbsConv

/-!
# T-UNIT-a helpers, part 2: `∇g_≤` facts, the integrability package, the pairing formula

Prefix `tunit_`.  Torus analogue of `Whole/DECAux2.lean`: `TDecGood ρ K` (measurable, symmetric,
`K(a,·)ρ ∈ L¹`, `K ρ ⊗ ρ ∈ L¹`), the potential `Φ_K`, and
`ν.pair2 K = N⁻¹ ∑_i Φ_K(X_i) - ∫ ρ Φ_K`, `pairT K X ρ = N⁻¹ ∑_i Φ_K(X_i) - ∫ ρ Φ_K` for a kernel vanishing on the
diagonal.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad

variable {d : ℕ} {s η : ℝ}

/-! ### Facts on `∇g_≤` -/

theorem tunit_glo_continuous (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) :
    Continuous (gloForceT s η : Torus d → Euc d) := by
  have hd2 : 2 ≤ d := by omega
  have hsd1 : s + 1 < (d : ℝ) := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  exact tsamp_continuous_euc fun i => tkr_glo_continuous hd2 hs0 hsd1 hη i

theorem tunit_glo_measurable (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) :
    Measurable (gloForceT s η : Torus d → Euc d) :=
  (tunit_glo_continuous hd hs0 hsd hη).measurable

theorem tunit_glo_bound (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : Torus d, ‖gloForceT s η z‖ ≤ B := by
  obtain ⟨B, hB⟩ := ten_bound_of_continuous (G := fun z => ‖gloForceT s η z‖)
    (tunit_glo_continuous hd hs0 hsd hη).norm
  refine ⟨B, (norm_nonneg _).trans (hB 0), fun z => ?_⟩
  have := hB z
  rwa [norm_norm] at this

theorem tunit_glo_odd (hd : 3 ≤ d) (hsd : s < (d : ℝ) - 2) (x : Torus d) :
    gloForceT s η (-x) = -gloForceT s η x := by
  have hsd' : s < (d : ℝ) := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hP : ∀ z : Torus d, perio (Whole.psiL η⁻¹ : Euc d → ℝ) (-z) = perio (Whole.psiL η⁻¹ : Euc d → ℝ) z :=
    fun z => ten_perio_neg (fun w => Whole.cmxFB_psiL_neg _ w) z
  unfold gloForceT PleqT
  have e : ∀ y : Torus d, perio (Whole.psiL η⁻¹ : Euc d → ℝ) (-x - -y) • periodicRieszGrad d s (-y) =
      -(perio (Whole.psiL η⁻¹ : Euc d → ℝ) (x - y) • periodicRieszGrad d s y) := by
    intro y
    rw [show -x - -y = -(x - y) by abel, hP, periodicRieszGrad_neg_of_lt hsd', smul_neg]
  calc ∫ y, perio (Whole.psiL η⁻¹ : Euc d → ℝ) (-x - y) • periodicRieszGrad d s y
      = ∫ y, perio (Whole.psiL η⁻¹ : Euc d → ℝ) (-x - -y) • periodicRieszGrad d s (-y) :=
        (integral_neg_eq_self (fun y => perio (Whole.psiL η⁻¹ : Euc d → ℝ) (-x - y) •
          periodicRieszGrad d s y) volume).symm
    _ = ∫ y, -(perio (Whole.psiL η⁻¹ : Euc d → ℝ) (x - y) • periodicRieszGrad d s y) :=
        integral_congr_ae (ae_of_all _ e)
    _ = -∫ y, perio (Whole.psiL η⁻¹ : Euc d → ℝ) (x - y) • periodicRieszGrad d s y := integral_neg _

/-- Sup bound on the convolution `(F*σ)(x) = σ.intV (y ↦ F(x-y))`. -/
theorem tunit_convForce_bound (σ : SMT d) [IsFiniteMeasure σ.pos] [IsFiniteMeasure σ.neg]
    {F : Torus d → Euc d} {B : ℝ} (hB : ∀ z, ‖F z‖ ≤ B) (x : Torus d) :
    ‖σ.convForce F x‖ ≤ B * (σ.pos.real Set.univ + σ.neg.real Set.univ) := by
  unfold SMT.convForce SMT.intV
  calc ‖(∫ y, F (x - y) ∂σ.pos) - ∫ y, F (x - y) ∂σ.neg‖
      ≤ ‖∫ y, F (x - y) ∂σ.pos‖ + ‖∫ y, F (x - y) ∂σ.neg‖ := norm_sub_le _ _
    _ ≤ B * σ.pos.real Set.univ + B * σ.neg.real Set.univ :=
        add_le_add (norm_integral_le_of_norm_le_const (ae_of_all _ fun y => hB _))
          (norm_integral_le_of_norm_le_const (ae_of_all _ fun y => hB _))
    _ = B * (σ.pos.real Set.univ + σ.neg.real Set.univ) := by ring

/-! ### The integrability package -/

/-- Integrability package for a kernel against the signed density `ρ`. -/
structure TDecGood (ρ : Torus d → ℝ) (K : Torus d → Torus d → ℝ) : Prop where
  meas : Measurable (fun q : Torus d × Torus d => K q.1 q.2)
  symm : ∀ x y, K x y = K y x
  F1 : ∀ a, Integrable (fun y => K a y * ρ y)
  F2 : Integrable (fun q : Torus d × Torus d => K q.1 q.2 * ρ q.1 * ρ q.2)

theorem TDecGood.congr' {ρ : Torus d → ℝ} {K K' : Torus d → Torus d → ℝ} (h : TDecGood ρ K)
    (hK : ∀ x y, K x y = K' x y) : TDecGood ρ K' := by
  have e : K = K' := funext fun x => funext fun y => hK x y
  subst e
  exact h

theorem TDecGood.add {ρ : Torus d → ℝ} {K₁ K₂ : Torus d → Torus d → ℝ} (h₁ : TDecGood ρ K₁)
    (h₂ : TDecGood ρ K₂) : TDecGood ρ (fun x y => K₁ x y + K₂ x y) where
  meas := h₁.meas.add h₂.meas
  symm := fun x y => by simp only [h₁.symm x y, h₂.symm x y]
  F1 := fun a => ((h₁.F1 a).add (h₂.F1 a)).congr (ae_of_all _ fun y => by
    simp only [Pi.add_apply, add_mul])
  F2 := (h₁.F2.add h₂.F2).congr (ae_of_all _ fun q => by simp only [Pi.add_apply, add_mul])

theorem TDecGood.sub {ρ : Torus d → ℝ} {K₁ K₂ : Torus d → Torus d → ℝ} (h₁ : TDecGood ρ K₁)
    (h₂ : TDecGood ρ K₂) : TDecGood ρ (fun x y => K₁ x y - K₂ x y) where
  meas := h₁.meas.sub h₂.meas
  symm := fun x y => by simp only [h₁.symm x y, h₂.symm x y]
  F1 := fun a => ((h₁.F1 a).sub (h₂.F1 a)).congr (ae_of_all _ fun y => by
    simp only [Pi.sub_apply, sub_mul])
  F2 := (h₁.F2.sub h₂.F2).congr (ae_of_all _ fun q => by simp only [Pi.sub_apply, sub_mul])

/-- The potential `Φ_K(x) = N⁻¹ ∑_j K(x, X_j) - ∫ K(x,y) ρ(y) dy`. -/
def tunitPhi (ρ : Torus d → ℝ) {N : ℕ} (X : Config d N) (K : Torus d → Torus d → ℝ) (x : Torus d) : ℝ :=
  (1 / (N : ℝ)) * ∑ j, K x (X j) - ∫ y, K x y * ρ y

theorem tunitPhi_meas {ρ : Torus d → ℝ} (hρm : Measurable ρ) {N : ℕ} (X : Config d N)
    {K : Torus d → Torus d → ℝ} (hG : TDecGood ρ K) : Measurable (tunitPhi ρ X K) := by
  unfold tunitPhi
  have h1 : Measurable (fun x => ∑ j, K x (X j)) :=
    Finset.measurable_sum _ fun j _ => hG.meas.comp (measurable_id.prodMk measurable_const)
  have h2 : Measurable (fun x => ∫ y, K x y * ρ y) :=
    tunit_param_measurable (μ := volume) (J := fun x y => K x y * ρ y)
      (hG.meas.mul (hρm.comp measurable_snd))
  exact (h1.const_mul _).sub h2

theorem tunitPhi_pt {ρ : Torus d → ℝ} {N : ℕ} (X : Config d N) (K : Torus d → Torus d → ℝ)
    (hG : TDecGood ρ K) (x : Torus d) :
    ρ x * tunitPhi ρ X K x =
      (1 / (N : ℝ)) * ∑ j, K (X j) x * ρ x - ∫ y, K x y * ρ x * ρ y := by
  have hint : ∫ y, K x y * ρ x * ρ y = ρ x * ∫ y, K x y * ρ y := by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  unfold tunitPhi
  have hsum : ∑ j, K x (X j) = ∑ j, K (X j) x := Finset.sum_congr rfl fun j _ => hG.symm x (X j)
  rw [hint, hsum, ← Finset.sum_mul]
  ring

theorem tunitPhi_integrable {ρ : Torus d → ℝ} {N : ℕ} (X : Config d N)
    {K : Torus d → Torus d → ℝ} (hG : TDecGood ρ K) :
    Integrable (fun x => ρ x * tunitPhi ρ X K x) := by
  have hpt : ∀ x, ρ x * tunitPhi ρ X K x =
      (1 / (N : ℝ)) * ∑ j, K (X j) x * ρ x - ∫ y, K x y * ρ x * ρ y :=
    fun x => tunitPhi_pt X K hG x
  have hi1 : Integrable (fun x => (1 / (N : ℝ)) * ∑ j, K (X j) x * ρ x) := by
    refine Integrable.const_mul ?_ _
    exact integrable_finsetSum _ fun j _ => hG.F1 (X j)
  have hi2 : Integrable (fun x => ∫ y, K x y * ρ x * ρ y) := hG.F2.integral_prod_left
  have heq : (fun x => ρ x * tunitPhi ρ X K x) =
      fun x => (1 / (N : ℝ)) * ∑ j, K (X j) x * ρ x - ∫ y, K x y * ρ x * ρ y :=
    funext hpt
  rw [heq]
  exact hi1.sub hi2

/-- The pairing formula on `ν = μ_N - μ`: `𝒞_K(ν) = N⁻¹ ∑_i Φ_K(X_i) - ∫ ρ Φ_K`. -/
theorem tunit_pair2_formula {ρ : Torus d → ℝ} (hρ : BddDensityT ρ) {N : ℕ} (hN : 1 ≤ N)
    (X : Config d N) {K : Torus d → Torus d → ℝ} (hG : TDecGood ρ K) :
    (chargeT X ρ).pair2 K =
      (1 / (N : ℝ)) * ∑ i, tunitPhi ρ X K (X i) - ∫ x, ρ x * tunitPhi ρ X K x := by
  have hinner : ∀ x, (chargeT X ρ).int (fun y => K x y) = tunitPhi ρ X K x := by
    intro x
    have hm : Measurable (fun y => K x y) := hG.meas.comp (measurable_const.prodMk measurable_id)
    have hint : Integrable (fun y => ρ y * K x y) :=
      (hG.F1 x).congr (ae_of_all _ fun y => mul_comm _ _)
    have e : ∫ y, ρ y * K x y = ∫ y, K x y * ρ y :=
      integral_congr_ae (ae_of_all _ fun y => mul_comm _ _)
    rw [tunit_charge_int ρ hρ hN X (fun y => K x y) hm hint]
    simp only [tunitPhi, e]
  have hPhi : (chargeT X ρ).pair2 K = (chargeT X ρ).int (tunitPhi ρ X K) := by
    unfold SMT.pair2
    simp only [hinner]
  rw [hPhi, tunit_charge_int ρ hρ hN X (tunitPhi ρ X K)
    (tunitPhi_meas hρ.measurable X hG) (tunitPhi_integrable X hG)]

theorem tunitPhi_add {ρ : Torus d → ℝ} {N : ℕ} (X : Config d N) {K₁ K₂ : Torus d → Torus d → ℝ}
    (h₁ : TDecGood ρ K₁) (h₂ : TDecGood ρ K₂) (x : Torus d) :
    tunitPhi ρ X (fun x y => K₁ x y + K₂ x y) x = tunitPhi ρ X K₁ x + tunitPhi ρ X K₂ x := by
  have e : ∫ y, (K₁ x y + K₂ x y) * ρ y = (∫ y, K₁ x y * ρ y) + ∫ y, K₂ x y * ρ y := by
    refine Eq.trans ?_ (integral_add (h₁.F1 x) (h₂.F1 x))
    congr 1
    funext y
    ring
  simp only [tunitPhi]
  rw [e, Finset.sum_add_distrib]
  ring

/-- Additivity of the pairing in the kernel (both kernels good). -/
theorem tunit_pair2_add {ρ : Torus d → ℝ} (hρ : BddDensityT ρ) {N : ℕ} (hN : 1 ≤ N)
    (X : Config d N) {K₁ K₂ : Torus d → Torus d → ℝ} (h₁ : TDecGood ρ K₁) (h₂ : TDecGood ρ K₂) :
    (chargeT X ρ).pair2 (fun x y => K₁ x y + K₂ x y) =
      (chargeT X ρ).pair2 K₁ + (chargeT X ρ).pair2 K₂ := by
  have hfun : tunitPhi ρ X (fun x y => K₁ x y + K₂ x y) =
      fun x => tunitPhi ρ X K₁ x + tunitPhi ρ X K₂ x := funext (tunitPhi_add X h₁ h₂)
  have hI : ∫ x, ρ x * (tunitPhi ρ X K₁ x + tunitPhi ρ X K₂ x) =
      (∫ x, ρ x * tunitPhi ρ X K₁ x) + ∫ x, ρ x * tunitPhi ρ X K₂ x := by
    refine Eq.trans ?_ (integral_add (tunitPhi_integrable X h₁) (tunitPhi_integrable X h₂))
    congr 1
    funext x
    ring
  rw [tunit_pair2_formula hρ hN X (h₁.add h₂), tunit_pair2_formula hρ hN X h₁,
    tunit_pair2_formula hρ hN X h₂, hfun, hI]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

/-- The `pairT` identity for a good kernel with zero diagonal. -/
theorem tunit_pairT_formula {ρ : Torus d → ℝ} {N : ℕ} (X : Config d N) {K : Torus d → Torus d → ℝ}
    (hG : TDecGood ρ K) (hdiag : ∀ x, K x x = 0) :
    pairT K X ρ = (1 / (N : ℝ)) * ∑ i, tunitPhi ρ X K (X i) - ∫ x, ρ x * tunitPhi ρ X K x := by
  have hi1 : Integrable (fun x => (1 / (N : ℝ)) * ∑ j, K (X j) x * ρ x) := by
    refine Integrable.const_mul ?_ _
    exact integrable_finsetSum _ fun j _ => hG.F1 (X j)
  have hi2 : Integrable (fun x => ∫ y, K x y * ρ x * ρ y) := hG.F2.integral_prod_left
  have hI : ∫ x, ρ x * tunitPhi ρ X K x =
      (1 / (N : ℝ)) * ∑ j, (∫ y, K (X j) y * ρ y) - ∫ x, ∫ y, K x y * ρ x * ρ y := by
    have e1 : (fun x => ρ x * tunitPhi ρ X K x) =
        fun x => (1 / (N : ℝ)) * ∑ j, K (X j) x * ρ x - ∫ y, K x y * ρ x * ρ y :=
      funext (tunitPhi_pt X K hG)
    rw [e1, integral_sub hi1 hi2, integral_const_mul,
      integral_finsetSum _ (fun j _ => hG.F1 (X j))]
  have hE : ∀ i, ∑ j ∈ Finset.univ.erase i, K (X i) (X j) = ∑ j, K (X i) (X j) :=
    fun i => Finset.sum_erase _ (hdiag (X i))
  unfold pairT
  simp only [hE]
  rw [hI]
  simp only [tunitPhi, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-! ### Commutator kernels -/

theorem tunit_commKer_meas {F : Torus d → Euc d} {v : Torus d → Euc d} (hF : Measurable F)
    (hv : Measurable v) : Measurable (fun q : Torus d × Torus d => commKernel F v q.1 q.2) := by
  unfold commKernel
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
  exact ((hv.comp measurable_fst).sub (hv.comp measurable_snd)).inner
    (hF.comp (measurable_fst.sub measurable_snd))

theorem tunit_commKer_symm {F : Torus d → Euc d} (hF : ∀ z, F (-z) = -F z) (v : Torus d → Euc d)
    (x y : Torus d) : commKernel F v x y = commKernel F v y x := by
  unfold commKernel
  by_cases h : x = y
  · subst h; rfl
  · have h' : y ≠ x := fun e => h e.symm
    rw [if_neg h, if_neg h', show y - x = -(x - y) by abel, hF, show v y - v x = -(v x - v y) by abel,
      inner_neg_left, inner_neg_right, neg_neg]

theorem tunit_commKer_diag (F : Torus d → Euc d) (v : Torus d → Euc d) (x : Torus d) :
    commKernel F v x x = 0 := by
  unfold commKernel
  simp

/-- A bounded measurable symmetric kernel is good. -/
theorem tunit_good_bdd {ρ : Torus d → ℝ} (hρ : BddDensityT ρ) {K : Torus d → Torus d → ℝ}
    (hm : Measurable (fun q : Torus d × Torus d => K q.1 q.2)) (hs : ∀ x y, K x y = K y x) {C : ℝ}
    (hC : ∀ x y, ‖K x y‖ ≤ C) : TDecGood ρ K := by
  obtain ⟨B, hB⟩ := hρ.bdd
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 0)
  have hρm := hρ.measurable
  refine ⟨hm, hs, fun a => ?_, ?_⟩
  · refine tunit_bdd_integrable ((hm.comp (measurable_const.prodMk measurable_id)).mul hρm) (C * B)
      (fun y => ?_)
    rw [norm_mul]
    exact mul_le_mul (hC _ _) (by rw [Real.norm_eq_abs]; exact hB y) (norm_nonneg _) hC0
  · refine tunit_bdd_integrable ((hm.mul (hρm.comp measurable_fst)).mul (hρm.comp measurable_snd))
      (C * B * B) (fun q => ?_)
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (hC _ _) (by rw [Real.norm_eq_abs]; exact hB q.1) (norm_nonneg _) hC0)
      (by rw [Real.norm_eq_abs]; exact hB q.2) (norm_nonneg _) (mul_nonneg hC0 hB0)

/-- The full commutator kernel `commKernel ∇g v` is good (Lipschitz `v`). -/
theorem tunit_full_good (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {ρ : Torus d → ℝ}
    (hρ : BddDensityT ρ) {v : Torus d → Euc d} {L : ℝ} (hL : 0 ≤ L) (hv : IsLipschitzVF L v) :
    TDecGood ρ (commKernel (periodicRieszGrad d s) v) := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd' : s < (d : ℝ) := by linarith
  obtain ⟨C, hC0, hC⟩ := HRS.Commutator.commKernel_bound (by omega : 1 ≤ d) hs0 hsd'
  have hK : 0 ≤ C * L := mul_nonneg hC0 hL
  have hvc : Continuous v := HRS.Commutator.IsLipschitzVF.continuous hL hv
  have hmeas : Measurable (fun p : Torus d × Torus d => commKernel (periodicRieszGrad d s) v p.1 p.2) :=
    tunit_commKer_meas (measurable_periodicRieszGrad hsd') hvc.measurable
  have hbound : ∀ x y : Torus d,
      |commKernel (periodicRieszGrad d s) v x y| ≤ (C * L) * (‖x - y‖ ^ (-s) + 1) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      unfold commKernel
      rw [if_pos rfl, abs_zero]
      exact mul_nonneg hK (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) zero_le_one)
    · have h1 := hC L v hL hv x y hxy
      have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
      have h2 : KernelGrad.tdist x y ^ (-s) ≤ ‖x - y‖ ^ (-s) := by
        rw [KernelGrad.tdist_eq_sub_zero]
        exact Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hz) (KernelGrad.norm_le_tdist _)
          (by linarith)
      calc |commKernel (periodicRieszGrad d s) v x y|
          ≤ C * L * (KernelGrad.tdist x y ^ (-s) + 1) := h1
        _ ≤ (C * L) * (‖x - y‖ ^ (-s) + 1) := mul_le_mul_of_nonneg_left (by linarith) hK
  have hgi : Integrable (fun z : Torus d => (C * L) * (‖z‖ ^ (-s) + 1)) volume :=
    ((KernelGrad.integrable_norm_rpow_neg (by omega) hsd').add (integrable_const _)).const_mul _
  have hg0 : ∀ z : Torus d, 0 ≤ (C * L) * (‖z‖ ^ (-s) + 1) := fun z =>
    mul_nonneg hK (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) zero_le_one)
  refine ⟨hmeas, fun x y => tunit_commKer_symm (periodicRieszGrad_neg_of_lt hsd') v x y, fun a => ?_, ?_⟩
  · refine (ten_sec_integrable hgi hρ a).norm.mono' ?_ (ae_of_all _ fun y => ?_)
    · exact ((hmeas.comp (measurable_const.prodMk measurable_id)).mul hρ.measurable).aestronglyMeasurable
    · rw [norm_mul, norm_mul, Real.norm_of_nonneg (hg0 _), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hbound a y) (norm_nonneg _)
  · refine (ten_joint_integrable hgi hρ).norm.mono' ?_ (ae_of_all _ fun q => ?_)
    · exact ((hmeas.mul (hρ.measurable.comp measurable_fst)).mul
        (hρ.measurable.comp measurable_snd)).aestronglyMeasurable
    · rw [norm_mul, norm_mul, norm_mul, norm_mul, Real.norm_of_nonneg (hg0 _), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hbound q.1 q.2) (norm_nonneg _))
        (norm_nonneg _)

/-- The kernel `commKernel ∇g_≤ v` is good (bounded). -/
theorem tunit_glo_good (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η)
    {ρ : Torus d → ℝ} (hρ : BddDensityT ρ) {v : Torus d → Euc d} {L : ℝ} (hL : 0 ≤ L)
    (hv : IsLipschitzVF L v) : TDecGood ρ (commKernel (gloForceT s η) v) := by
  obtain ⟨Bg, hBg0, hBg⟩ := tunit_glo_bound hd hs0 hsd hη
  have hvc : Continuous v := HRS.Commutator.IsLipschitzVF.continuous hL hv
  have hbound : ∀ x y, ‖commKernel (gloForceT s η) v x y‖ ≤ (L * d) * Bg := by
    intro x y
    unfold commKernel
    by_cases hxy : x = y
    · rw [if_pos hxy, norm_zero]
      exact mul_nonneg (mul_nonneg hL (Nat.cast_nonneg d)) hBg0
    · rw [if_neg hxy]
      have h1 : ‖inner ℝ (v x - v y) (gloForceT s η (x - y))‖ ≤
          ‖v x - v y‖ * ‖gloForceT s η (x - y)‖ := norm_inner_le_norm _ _
      have h2 : ‖v x - v y‖ ≤ L * d := by
        calc ‖v x - v y‖ ≤ L * KernelGrad.tdist x y := hv x y
          _ ≤ L * d := by
            rw [KernelGrad.tdist_eq_sub_zero]
            exact mul_le_mul_of_nonneg_left (KernelGrad.tdist_le_card _) hL
      exact h1.trans (mul_le_mul h2 (hBg _) (norm_nonneg _) (mul_nonneg hL (Nat.cast_nonneg d)))
  exact tunit_good_bdd hρ (tunit_commKer_meas (tunit_glo_measurable hd hs0 hsd hη) hvc.measurable)
    (tunit_commKer_symm (fun z => by rw [tunit_glo_odd hd hsd]) v) hbound

end HRS.Commutator.TorusNote
