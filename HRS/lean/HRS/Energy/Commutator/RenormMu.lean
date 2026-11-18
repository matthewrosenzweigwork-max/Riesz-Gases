import HRS.Energy.Commutator.RenormSelf

/-!
# Route S, packet S4: the `μ`-term inside the ball (`B2`)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.RoughLimit

namespace HRS.Commutator.Renorm

variable {d : ℕ}

/-- `∫_{|z| ≤ ρ} |z| |w_l(z)|` -/
def Wt (d : ℕ) (l ρ : ℝ) : ℝ :=
  ∫ z : Torus d, if KernelGrad.tdist z 0 ≤ ρ then KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖ else 0

/-- `∫_{|z| ≤ ρ} |w_l(z)|` -/
def Wb (d : ℕ) (l ρ : ℝ) : ℝ :=
  ∫ z : Torus d, if KernelGrad.tdist z 0 ≤ ρ then ‖SliceAux.sgv l z‖ else 0

theorem integrable_Wt (hd : 1 ≤ d) {l : ℝ} (hl : 0 ≤ l) (ρ : ℝ) :
    Integrable (fun z : Torus d => if KernelGrad.tdist z 0 ≤ ρ then KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖ else 0)
      volume := by
  refine Integrable.mono' (integrable_tdist_sgv hd hl) ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (Measurable.ite (measurableSet_le EnergyAux.measurable_tdist_zero measurable_const)
      ((EnergyAux.measurable_tdist_zero).mul (measurable_sgv_l l).norm) measurable_const).aestronglyMeasurable
  · split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (KernelGrad.tdist_nonneg z 0) (norm_nonneg _))]
    · simp only [norm_zero]; exact mul_nonneg (KernelGrad.tdist_nonneg z 0) (norm_nonneg _)

theorem integrable_Wb (hd : 1 ≤ d) {l : ℝ} (hl : 0 ≤ l) (ρ : ℝ) :
    Integrable (fun z : Torus d => if KernelGrad.tdist z 0 ≤ ρ then ‖SliceAux.sgv l z‖ else 0) volume := by
  refine Integrable.mono' (sgv_integrable (d := d) hl).norm ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (Measurable.ite (measurableSet_le EnergyAux.measurable_tdist_zero measurable_const)
      (measurable_sgv_l l).norm measurable_const).aestronglyMeasurable
  · split_ifs
    · simp
    · simp

theorem Wt_nonneg (l ρ : ℝ) : 0 ≤ Wt d l ρ := by
  unfold Wt
  refine integral_nonneg fun z => ?_
  split_ifs
  · exact mul_nonneg (KernelGrad.tdist_nonneg z 0) (norm_nonneg _)
  · exact le_rfl

theorem Wb_nonneg (l ρ : ℝ) : 0 ≤ Wb d l ρ := by
  unfold Wb
  refine integral_nonneg fun z => ?_
  split_ifs
  · exact norm_nonneg _
  · exact le_rfl

theorem Wt_mono (hd : 1 ≤ d) {l : ℝ} (hl : 0 ≤ l) {ρ ρ' : ℝ} (h : ρ ≤ ρ') : Wt d l ρ ≤ Wt d l ρ' := by
  unfold Wt
  refine integral_mono (integrable_Wt hd hl ρ) (integrable_Wt hd hl ρ') fun z => ?_
  by_cases h1 : KernelGrad.tdist z 0 ≤ ρ
  · rw [if_pos h1, if_pos (h1.trans h)]
  · rw [if_neg h1]; split_ifs
    · exact mul_nonneg (KernelGrad.tdist_nonneg z 0) (norm_nonneg _)
    · exact le_rfl

theorem Wb_mono (hd : 1 ≤ d) {l : ℝ} (hl : 0 ≤ l) {ρ ρ' : ℝ} (h : ρ ≤ ρ') : Wb d l ρ ≤ Wb d l ρ' := by
  unfold Wb
  refine integral_mono (integrable_Wb hd hl ρ) (integrable_Wb hd hl ρ') fun z => ?_
  by_cases h1 : KernelGrad.tdist z 0 ≤ ρ
  · rw [if_pos h1, if_pos (h1.trans h)]
  · rw [if_neg h1]; split_ifs
    · exact norm_nonneg _
    · exact le_rfl

theorem muB_bound (hd : 1 ≤ d) {l : ℝ} (hl : 0 ≤ l) {L : ℝ} (hL : 0 ≤ L) {v : Torus d → Euc d}
    (hv : IsLipschitzVF L v) {a : Torus d} {η : ℝ} (hη : 0 ≤ η) {σ : Measure (Torus d)} [IsFiniteMeasure σ]
    (hsupp : ∀ᵐ x ∂σ, KernelGrad.tdist x a ≤ η)
    (hrep : ∀ y, η < KernelGrad.tdist y a → ∫ x, SliceAux.sgv l (y - x) ∂σ = SliceAux.sgv l (y - a))
    {μ : Measure (Torus d)} [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ⊤) (hμ : μ ≤ c • (volume : Measure (Torus d))) :
    |muB l v σ μ a| ≤ c.toReal * L * (Wt d l η + σ.real Set.univ * (Wt d l (2 * η) + η * Wb d l (2 * η))) := by
  obtain ⟨w, hw⟩ : ∃ w : Torus d → Euc d, w = SliceAux.sgv l := ⟨_, rfl⟩
  subst hw
  have hwm : Measurable (SliceAux.sgv l : Torus d → Euc d) := measurable_sgv_l l
  have hwint : Integrable (SliceAux.sgv l : Torus d → Euc d) volume := sgv_integrable hl
  have hvc := lipschitzVF_continuous hL hv
  have hvm : Measurable v := hvc.measurable
  -- the kernel `H`
  obtain ⟨H, hH⟩ : ∃ H : Torus d → ℝ, H = fun z => if KernelGrad.tdist z 0 ≤ 2 * η then
    KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖ + η * ‖SliceAux.sgv l z‖ else 0 := ⟨_, rfl⟩
  have hHm : Measurable H := by
    rw [hH]
    refine Measurable.ite (measurableSet_le EnergyAux.measurable_tdist_zero measurable_const) ?_ measurable_const
    exact ((EnergyAux.measurable_tdist_zero).mul (hwm.norm)).add (measurable_const.mul hwm.norm)
  have hHe : H = fun z => (if KernelGrad.tdist z 0 ≤ 2 * η then KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖ else 0) +
      η * (if KernelGrad.tdist z 0 ≤ 2 * η then ‖SliceAux.sgv l z‖ else 0) := by
    funext z; rw [hH]; by_cases h : KernelGrad.tdist z 0 ≤ 2 * η <;> simp [h]
  have hHi : Integrable H volume := by
    rw [hHe]
    exact (integrable_Wt hd hl _).add ((integrable_Wb hd hl _).const_mul η)
  have hH0 : ∀ z, 0 ≤ H z := fun z => by
    rw [hH]; dsimp only; split_ifs
    · exact add_nonneg (mul_nonneg (KernelGrad.tdist_nonneg z 0) (norm_nonneg _)) (mul_nonneg hη (norm_nonneg _))
    · exact le_rfl
  have hHint : ∫ z, H z = Wt d l (2 * η) + η * Wb d l (2 * η) := by
    rw [hHe, integral_add (integrable_Wt hd hl _) ((integrable_Wb hd hl _).const_mul η), integral_const_mul]
    rfl
  -- the first piece
  obtain ⟨f1, hf1⟩ : ∃ f1 : Torus d → ℝ, f1 = fun z => if KernelGrad.tdist z 0 ≤ η then KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖ else 0 := ⟨_, rfl⟩
  have hf1i : Integrable f1 volume := by rw [hf1]; exact integrable_Wt hd hl η
  have hf1m : Measurable f1 := by
    rw [hf1]
    refine Measurable.ite (measurableSet_le EnergyAux.measurable_tdist_zero measurable_const) ?_ measurable_const
    exact (EnergyAux.measurable_tdist_zero).mul (hwm.norm)
  obtain ⟨K, hK⟩ : ∃ K : Torus d → ℝ, K = fun y => L * f1 (a - y) + L * ∫ x, H (x - y) ∂σ := ⟨_, rfl⟩
  have hHσ : Integrable (fun p : Torus d × Torus d => H (p.1 - p.2)) (σ.prod volume) :=
    integrable_conv_vol hHm hHi σ
  have hHσ' : Integrable (fun p : Torus d × Torus d => H (p.2 - p.1)) ((volume : Measure (Torus d)).prod σ) := by
    have := hHσ.swap
    exact this
  have hKi : Integrable K volume := by
    rw [hK]
    refine Integrable.add ?_ ?_
    · exact (hf1i.comp_sub_left a).const_mul L
    · exact hHσ'.integral_prod_left.const_mul L
  have hK0 : ∀ y, 0 ≤ K y := fun y => by
    rw [hK]; dsimp only
    have h1 : 0 ≤ f1 (a - y) := by
      rw [hf1]; dsimp only; split_ifs
      · exact mul_nonneg (KernelGrad.tdist_nonneg _ 0) (norm_nonneg _)
      · exact le_rfl
    have h2 : 0 ≤ ∫ x, H (x - y) ∂σ := integral_nonneg fun x => hH0 _
    positivity
  -- integral of `K`
  have hKint : ∫ y, K y = L * Wt d l η + L * (σ.real Set.univ * (Wt d l (2 * η) + η * Wb d l (2 * η))) := by
    rw [hK]
    dsimp only
    rw [integral_add ((hf1i.comp_sub_left a).const_mul L) (hHσ'.integral_prod_left.const_mul L),
      integral_const_mul, integral_const_mul, integral_sub_left_eq_self f1 volume a]
    have hf1W : ∫ x, f1 x = Wt d l η := by rw [hf1]; rfl
    have hswap : ∫ y, ∫ x, H (x - y) ∂σ = σ.real Set.univ * (Wt d l (2 * η) + η * Wb d l (2 * η)) := by
      rw [integral_integral_swap (f := fun y x => H (x - y)) hHσ']
      simp_rw [integral_sub_left_eq_self H volume]
      rw [integral_const, hHint]
      simp [Measure.real]
    rw [hf1W, hswap]
  have hae : ∀ᵐ y ∂(volume : Measure (Torus d)),
      ‖inner ℝ (v a - v y) (SliceAux.sgv l (a - y) - ∫ x, SliceAux.sgv l (x - y) ∂σ)‖ ≤ K y := by
    filter_upwards [hHσ'.prod_right_ae] with y hy
    by_cases hya : η < KernelGrad.tdist y a
    · have e : ∫ x, SliceAux.sgv l (x - y) ∂σ = SliceAux.sgv l (a - y) := by
        have e1 : ∀ x : Torus d, SliceAux.sgv l (x - y) = -SliceAux.sgv l (y - x) := fun x => by
          rw [← sgv_odd]; congr 1; abel
        simp_rw [e1]
        rw [integral_neg, hrep y hya, ← sgv_odd]
      rw [e, sub_self, inner_zero_right, norm_zero]
      exact hK0 y
    · push Not at hya
      have hya' : KernelGrad.tdist (a - y) 0 ≤ η := by
        rw [← EnergyAux.tdist_def, tdist_symm']; exact hya
      have hay : KernelGrad.tdist a y = KernelGrad.tdist (a - y) 0 := EnergyAux.tdist_def a y
      have h3 : KernelGrad.tdist a y * ∫ x, ‖SliceAux.sgv l (x - y)‖ ∂σ ≤ ∫ x, H (x - y) ∂σ := by
        rw [← integral_const_mul]
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by
          have := KernelGrad.tdist_nonneg a y
          positivity) hy ?_
        filter_upwards [hsupp] with x hx
        have t0 : KernelGrad.tdist a y ≤ η := by rw [tdist_symm']; exact hya
        have t1 : KernelGrad.tdist (x - y) 0 ≤ 2 * η := by
          rw [← EnergyAux.tdist_def]
          have := tdist_tri x a y
          linarith
        have t2 : KernelGrad.tdist a y ≤ KernelGrad.tdist (x - y) 0 + η := by
          rw [← EnergyAux.tdist_def]
          have := tdist_tri a x y
          rw [tdist_symm' a x] at this
          linarith
        rw [hH]; dsimp only; rw [if_pos t1]
        nlinarith [norm_nonneg (SliceAux.sgv l (x - y))]
      have h4 : ‖∫ x, SliceAux.sgv l (x - y) ∂σ‖ ≤ ∫ x, ‖SliceAux.sgv l (x - y)‖ ∂σ := norm_integral_le_integral_norm _
      have h5 := hv a y
      calc ‖inner ℝ (v a - v y) (SliceAux.sgv l (a - y) - ∫ x, SliceAux.sgv l (x - y) ∂σ)‖
          ≤ ‖v a - v y‖ * ‖SliceAux.sgv l (a - y) - ∫ x, SliceAux.sgv l (x - y) ∂σ‖ := norm_inner_le_norm _ _
        _ ≤ (L * KernelGrad.tdist a y) * (‖SliceAux.sgv l (a - y)‖ + ∫ x, ‖SliceAux.sgv l (x - y)‖ ∂σ) := by
            refine mul_le_mul h5 ((norm_sub_le _ _).trans (add_le_add le_rfl h4)) (norm_nonneg _)
              (mul_nonneg hL (KernelGrad.tdist_nonneg a y))
        _ = L * (KernelGrad.tdist a y * ‖SliceAux.sgv l (a - y)‖) + L * (KernelGrad.tdist a y * ∫ x, ‖SliceAux.sgv l (x - y)‖ ∂σ) := by ring
        _ ≤ K y := by
            rw [hK]; dsimp only
            have : f1 (a - y) = KernelGrad.tdist a y * ‖SliceAux.sgv l (a - y)‖ := by
              rw [hf1]; dsimp only; rw [if_pos hya', hay]
            rw [this]
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h3 hL)
  have hac : μ ≪ (volume : Measure (Torus d)) := Measure.absolutelyContinuous_of_le_smul hμ
  have hKc : Integrable K (c • (volume : Measure (Torus d))) := hKi.smul_measure hc
  have hKμ : Integrable K μ := hKc.mono_measure hμ
  unfold muB
  calc |∫ y, inner ℝ (v a - v y) (SliceAux.sgv l (a - y) - ∫ x, SliceAux.sgv l (x - y) ∂σ) ∂μ|
      ≤ ∫ y, ‖inner ℝ (v a - v y) (SliceAux.sgv l (a - y) - ∫ x, SliceAux.sgv l (x - y) ∂σ)‖ ∂μ := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ)
          (fun y => inner ℝ (v a - v y) (SliceAux.sgv l (a - y) - ∫ x, SliceAux.sgv l (x - y) ∂σ))
    _ ≤ ∫ y, K y ∂μ := integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _) hKμ (hac.ae_le hae)
    _ ≤ ∫ y, K y ∂(c • (volume : Measure (Torus d))) :=
        integral_mono_measure hμ (Filter.Eventually.of_forall hK0) hKc
    _ = c.toReal * ∫ y, K y := by rw [integral_smul_measure]; rfl
    _ = c.toReal * L * (Wt d l η + σ.real Set.univ * (Wt d l (2 * η) + η * Wb d l (2 * η))) := by
        rw [hKint]; ring

end HRS.Commutator.Renorm
