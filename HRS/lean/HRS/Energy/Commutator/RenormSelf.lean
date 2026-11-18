import HRS.Energy.Commutator.RenormMaster

/-!
# Route S, packet S4: the self-interaction of a smeared charge (neutralised stress inequality)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.RoughLimit

namespace HRS.Commutator.Renorm

variable {d : ℕ}

/-- `J_l = ∫ |z| |w_l(z)| dz`. -/
def Jl (d : ℕ) (l : ℝ) : ℝ := ∫ z : Torus d, KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖

theorem integrable_tdist_sgv (hd : 1 ≤ d) {l : ℝ} (hl : 0 ≤ l) :
    Integrable (fun z : Torus d => KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖) volume := by
  obtain ⟨A, B, hA, hB, h⟩ := HeatAux.tdist_grad_le (d := d) hd hl
  have h1 : Integrable (fun z : Torus d => A * sliceG d l z + B) volume :=
    ((RoughKernel.integrable_sliceG hl).const_mul A).add (integrable_const B)
  have hm : Measurable fun z : Torus d => KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖ :=
    (EnergyAux.measurable_tdist_zero).mul (measurable_sgv_l l).norm
  refine Integrable.mono' h1 hm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (KernelGrad.tdist_nonneg z 0) (norm_nonneg _))]
  by_cases hz : z = 0
  · subst hz
    have h0 : KernelGrad.tdist (0 : Torus d) 0 = 0 := CoercAux.tdist_self 0
    rw [h0, zero_mul]
    have := sliceG_zero_arg_nonneg (d := d) l
    positivity
  · have := h z hz
    rw [show ‖SliceAux.sgv l z‖ = ‖sliceGrad d l z‖ by rw [sliceGrad_eq hl hz]; rfl]
    exact this


theorem integral_sgv_vol (l : ℝ) : ∫ z : Torus d, SliceAux.sgv l z = 0 := by
  have h : ∫ z : Torus d, SliceAux.sgv l (-z) = ∫ z : Torus d, SliceAux.sgv l z :=
    integral_neg_eq_self (fun z : Torus d => SliceAux.sgv l z) volume
  simp_rw [sgv_odd, integral_neg] at h
  have : (2 : ℝ) • ∫ z : Torus d, SliceAux.sgv l z = 0 := by
    rw [two_smul]; nth_rewrite 1 [← h]; simp
  rcases smul_eq_zero.mp this with h2 | h2
  · norm_num at h2
  · exact h2

theorem kern_vol_vol {l : ℝ} (hl : 0 ≤ l) {v : Torus d → Euc d} (hvm : Measurable v) {Cv : ℝ}
    (hvb : ∀ x, ‖v x‖ ≤ Cv) :
    ∫ p : Torus d × Torus d, kern (SliceAux.sgv l) v p.1 p.2 ∂((volume : Measure (Torus d)).prod volume) = 0 := by
  have hwm := measurable_sgv_l (d := d) l
  have hwint := sgv_integrable (d := d) hl
  have hI : Integrable (fun p : Torus d × Torus d => ‖SliceAux.sgv l (p.1 - p.2)‖)
      ((volume : Measure (Torus d)).prod volume) := integrable_norm_conv hwm hwint volume
  have hint : ∀ u : Torus d → Euc d, Measurable u → (∀ x, ‖u x‖ ≤ Cv) →
      Integrable (fun p : Torus d × Torus d => inner ℝ (u p.1) (SliceAux.sgv l (p.1 - p.2)))
        ((volume : Measure (Torus d)).prod volume) := by
    intro u hu hub
    refine Integrable.mono' (hI.const_mul Cv)
      (Measurable.aestronglyMeasurable (Measurable.inner (hu.comp measurable_fst)
        (hwm.comp (measurable_fst.sub measurable_snd)))) (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hub _) (norm_nonneg _))
  have hint2 : Integrable (fun p : Torus d × Torus d => inner ℝ (v p.2) (SliceAux.sgv l (p.1 - p.2)))
      ((volume : Measure (Torus d)).prod volume) := by
    refine Integrable.mono' (hI.const_mul Cv)
      (Measurable.aestronglyMeasurable (Measurable.inner (hvm.comp measurable_snd)
        (hwm.comp (measurable_fst.sub measurable_snd)))) (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hvb _) (norm_nonneg _))
  have hint1 := hint v hvm hvb
  have e : ∀ p : Torus d × Torus d, kern (SliceAux.sgv l) v p.1 p.2 =
      inner ℝ (v p.1) (SliceAux.sgv l (p.1 - p.2)) - inner ℝ (v p.2) (SliceAux.sgv l (p.1 - p.2)) := by
    intro p; unfold kern; rw [inner_sub_left]
  simp_rw [e]
  rw [integral_sub hint1 hint2]
  have t1 : ∫ p : Torus d × Torus d, inner ℝ (v p.1) (SliceAux.sgv l (p.1 - p.2))
      ∂((volume : Measure (Torus d)).prod volume) = 0 := by
    rw [integral_prod _ hint1]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only []
    have hw1 : Integrable (fun y => SliceAux.sgv l (x - y)) (volume : Measure (Torus d)) := hwint.comp_sub_left x
    rw [integral_inner hw1, integral_sub_left_eq_self (fun z => SliceAux.sgv l z) volume x, integral_sgv_vol]
    simp
  have t2 : ∫ p : Torus d × Torus d, inner ℝ (v p.2) (SliceAux.sgv l (p.1 - p.2))
      ∂((volume : Measure (Torus d)).prod volume) = 0 := by
    rw [integral_prod_symm _ hint2]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only []
    have hw1 : Integrable (fun x => SliceAux.sgv l (x - y)) (volume : Measure (Torus d)) := hwint.comp_sub_right y
    rw [integral_inner hw1, integral_sub_right_eq_self (fun z => SliceAux.sgv l z) y, integral_sgv_vol]
    simp
  rw [t1, t2]; simp

theorem tdist_eq_zero_arg (x y : Torus d) : KernelGrad.tdist x y = KernelGrad.tdist (x - y) 0 := by
  unfold KernelGrad.tdist; simp

/-- the inner integral `∫ k(x,y) dvol(y)` is bounded by `L J_l`. -/
theorem abs_int_kern_vol_le (hd : 1 ≤ d) {l : ℝ} (hl : 0 ≤ l) {L : ℝ} (hL : 0 ≤ L) {v : Torus d → Euc d}
    (hv : IsLipschitzVF L v) (x : Torus d) :
    |∫ y, kern (SliceAux.sgv l) v x y ∂(volume : Measure (Torus d))| ≤ L * Jl d l := by
  have hI : Integrable (fun z : Torus d => KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖) volume :=
    integrable_tdist_sgv hd hl
  have hI' : Integrable (fun y : Torus d => KernelGrad.tdist (x - y) 0 * ‖SliceAux.sgv l (x - y)‖) volume :=
    hI.comp_sub_left x
  have hle : ∀ y, |kern (SliceAux.sgv l) v x y| ≤ L * (KernelGrad.tdist (x - y) 0 * ‖SliceAux.sgv l (x - y)‖) := by
    intro y
    unfold kern
    refine (abs_real_inner_le_norm _ _).trans ?_
    have := hv x y
    rw [tdist_eq_zero_arg] at this
    calc ‖v x - v y‖ * ‖SliceAux.sgv l (x - y)‖ ≤ (L * KernelGrad.tdist (x - y) 0) * ‖SliceAux.sgv l (x - y)‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = _ := by ring
  have hmeas : Measurable fun y : Torus d => kern (SliceAux.sgv l) v x y := by
    have hvc := lipschitzVF_continuous hL hv
    unfold kern
    exact Measurable.inner (measurable_const.sub hvc.measurable) ((measurable_sgv_l l).comp (measurable_const.sub measurable_id))
  calc |∫ y, kern (SliceAux.sgv l) v x y ∂(volume : Measure (Torus d))|
      ≤ ∫ y, |kern (SliceAux.sgv l) v x y| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := (volume : Measure (Torus d)))
          (fun y => kern (SliceAux.sgv l) v x y)
    _ ≤ ∫ y, L * (KernelGrad.tdist (x - y) 0 * ‖SliceAux.sgv l (x - y)‖) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _)
          (hI'.const_mul L) (Filter.Eventually.of_forall hle)
    _ = L * Jl d l := by
        rw [integral_const_mul]
        congr 1
        exact integral_sub_left_eq_self (fun z : Torus d => KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖) volume x

theorem selfB_bound (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 < C ∧ ∀ {l : ℝ} (hl : 0 ≤ l) {L : ℝ} (hL : 0 ≤ L)
    {v : Torus d → Euc d} (hv : IsLipschitzVF L v) {σ : Measure (Torus d)} [IsFiniteMeasure σ]
    (hat : 2 ≤ d → ∀ x, σ {x} = 0)
    (hG : Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) (σ.prod σ)),
    |selfB l v σ| ≤ C * L * quadForm (fun x y => sliceGfull d l (x - y)) σ
        (ENNReal.ofReal (σ.real Set.univ) • (volume : Measure (Torus d))) +
      2 * L * (σ.real Set.univ) ^ 2 * Jl d l := by
  obtain ⟨C, hC, hs⟩ := stress_rough d
  refine ⟨C, hC, fun {l} hl {L} hL {v} hv {σ} _ hat hG => ?_⟩
  set m : ℝ := σ.real Set.univ with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  set α : Measure (Torus d) := ENNReal.ofReal m • (volume : Measure (Torus d)) with hα
  have hc : ENNReal.ofReal m ≠ ⊤ := ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure α := Measure.smul_finite _ hc
  have hle : α ≤ ENNReal.ofReal m • (volume : Measure (Torus d)) := le_rfl
  have hint : Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) ((σ + α).prod (σ + α)) := by
    rw [Measure.add_prod, Measure.prod_add, Measure.prod_add]
    exact integrable_add_measure.mpr ⟨integrable_add_measure.mpr ⟨hG, integrable_G_mu hl σ hc hle⟩,
      integrable_add_measure.mpr ⟨integrable_G_mu_swap hl σ hc hle, integrable_G_mu hl α hc hle⟩⟩
  have hst := hs l hl L v hL hv σ α inferInstance inferInstance
    (fun _ => by
      have hv1 : (volume : Measure (Torus d)) Set.univ = 1 := measure_univ
      rw [hα, Measure.smul_apply, hv1, smul_eq_mul, mul_one, hm, Measure.real,
        ENNReal.ofReal_toReal (measure_ne_top σ _)])
    (fun h2 => ⟨hat h2, atomless_of_le_vol (by omega) hc hle⟩) hint
  rw [commKernel_sliceGrad hl v] at hst
  have hvc := lipschitzVF_continuous hL hv
  obtain ⟨Cv, hCv⟩ := exists_bound_of_cont hvc
  set I : Torus d → ℝ := fun x => ∫ y, kern (SliceAux.sgv l) v x y ∂(volume : Measure (Torus d)) with hI
  have hkσσ : Integrable (fun p : Torus d × Torus d => kern (SliceAux.sgv l) v p.1 p.2) (σ.prod σ) :=
    integrable_kern_of_G hd hl hL hv hG
  have hvv : Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2))
      ((volume : Measure (Torus d)).prod volume) :=
    integrable_conv_vol (EnergyAux.measurable_sliceGfull l) (integrable_sliceGfull_vol hl) volume
  have hkvv : Integrable (fun p : Torus d × Torus d => kern (SliceAux.sgv l) v p.1 p.2)
      ((volume : Measure (Torus d)).prod volume) := integrable_kern_of_G hd hl hL hv hvv
  have hin : ∀ x, ∫ y, kern (SliceAux.sgv l) v x y ∂α = m * I x := by
    intro x
    rw [hα, integral_smul_measure, ENNReal.toReal_ofReal hm0, smul_eq_mul]
  have hT1 : ∫ x, ∫ y, kern (SliceAux.sgv l) v x y ∂σ ∂σ = selfB l v σ := by
    unfold selfB
    exact (integral_prod _ hkσσ).symm
  have hIσ : ∫ x, ∫ y, kern (SliceAux.sgv l) v x y ∂α ∂σ = m * ∫ x, I x ∂σ := by
    simp_rw [hin]; rw [integral_const_mul]
  have hI0 : ∫ x, I x ∂(volume : Measure (Torus d)) = 0 := by
    have := integral_prod _ hkvv
    rw [← this]
    exact kern_vol_vol hl hvc.measurable hCv
  have hT3 : ∫ x, ∫ y, kern (SliceAux.sgv l) v x y ∂α ∂α = 0 := by
    simp_rw [hin]
    rw [integral_const_mul, hα, integral_smul_measure, hI0]; simp
  have hexp : quadForm (fun x y => kern (SliceAux.sgv l) v x y) σ α = selfB l v σ - 2 * (m * ∫ x, I x ∂σ) := by
    unfold quadForm
    rw [hT1, hIσ, hT3]; ring
  have hIb : |∫ x, I x ∂σ| ≤ L * Jl d l * m := by
    have := norm_integral_le_of_norm_le_const (μ := σ) (f := I) (C := L * Jl d l)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact abs_int_kern_vol_le hd hl hL hv x)
    simpa [Real.norm_eq_abs, hm, mul_comm] using this
  have hfin : selfB l v σ = quadForm (fun x y => kern (SliceAux.sgv l) v x y) σ α + 2 * (m * ∫ x, I x ∂σ) := by
    rw [hexp]; ring
  have hst' : |quadForm (fun x y => kern (SliceAux.sgv l) v x y) σ α| ≤ C * L * quadForm (fun x y => sliceGfull d l (x - y)) σ α := by
    simpa [commKernel_eq_kern] using hst
  rw [hfin]
  calc |quadForm (fun x y => kern (SliceAux.sgv l) v x y) σ α + 2 * (m * ∫ x, I x ∂σ)|
      ≤ |quadForm (fun x y => kern (SliceAux.sgv l) v x y) σ α| + |2 * (m * ∫ x, I x ∂σ)| := abs_add_le _ _
    _ ≤ C * L * quadForm (fun x y => sliceGfull d l (x - y)) σ α + 2 * L * m ^ 2 * Jl d l := by
        refine add_le_add hst' ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hm0, abs_two]
        nlinarith [hIb, hm0]

theorem tdist_tri (x y z : Torus d) : KernelGrad.tdist x z ≤ KernelGrad.tdist x y + KernelGrad.tdist y z := by
  rw [EnergyAux.tdist_def x z, EnergyAux.tdist_def x y, EnergyAux.tdist_def y z]
  have := EnergyAux.tdist_add_le (x - y) (y - z)
  rwa [show x - y + (y - z) = x - z by abel] at this

theorem selfB_pointwise {l : ℝ} (hl : 0 ≤ l) {L : ℝ} (hL : 0 ≤ L) {v : Torus d → Euc d}
    (hv : IsLipschitzVF L v) {σ : Measure (Torus d)} [IsFiniteMeasure σ] {a : Torus d} {η : ℝ}
    (hsupp : ∀ᵐ x ∂σ, KernelGrad.tdist x a ≤ η) {K2 : ℝ}
    (hK2 : ∀ z : Torus d, KernelGrad.tdist z 0 ≤ 2 * η → KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖ ≤ K2) :
    |selfB l v σ| ≤ L * K2 * (σ.real Set.univ) ^ 2 := by
  have h1 : ∀ᵐ p ∂(σ.prod σ), KernelGrad.tdist p.1 a ≤ η :=
    Measure.quasiMeasurePreserving_fst.ae hsupp
  have h2 : ∀ᵐ p ∂(σ.prod σ), KernelGrad.tdist p.2 a ≤ η :=
    Measure.quasiMeasurePreserving_snd.ae hsupp
  have hb : ∀ᵐ p ∂(σ.prod σ), ‖kern (SliceAux.sgv l) v p.1 p.2‖ ≤ L * K2 := by
    filter_upwards [h1, h2] with p hp1 hp2
    have ht : KernelGrad.tdist (p.1 - p.2) 0 ≤ 2 * η := by
      rw [← EnergyAux.tdist_def]
      have := tdist_tri p.1 a p.2
      rw [tdist_symm' a p.2] at this
      linarith
    have hz := hK2 _ ht
    rw [Real.norm_eq_abs]
    unfold kern
    refine (abs_real_inner_le_norm _ _).trans ?_
    have h5 := hv p.1 p.2
    rw [EnergyAux.tdist_def] at h5
    calc ‖v p.1 - v p.2‖ * ‖SliceAux.sgv l (p.1 - p.2)‖
        ≤ (L * KernelGrad.tdist (p.1 - p.2) 0) * ‖SliceAux.sgv l (p.1 - p.2)‖ :=
          mul_le_mul_of_nonneg_right h5 (norm_nonneg _)
      _ = L * (KernelGrad.tdist (p.1 - p.2) 0 * ‖SliceAux.sgv l (p.1 - p.2)‖) := by ring
      _ ≤ L * K2 := mul_le_mul_of_nonneg_left hz hL
  have := norm_integral_le_of_norm_le_const hb
  unfold selfB
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  have hu : (σ.prod σ) Set.univ = σ Set.univ * σ Set.univ := by
    rw [← Set.univ_prod_univ, Measure.prod_prod]
  have : (σ.prod σ).real Set.univ = (σ.real Set.univ) ^ 2 := by
    rw [Measure.real, hu, ENNReal.toReal_mul]; simp [Measure.real, sq]
  rw [this]

end HRS.Commutator.Renorm
