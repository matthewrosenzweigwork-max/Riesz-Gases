import HRS.Equilibrium.Parametrix.PX4bAuxG

/-!
# Packet PX4b auxiliaries H: the explicit (no-flux) formula for `Jop` of a conormal slice
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

open HRS.PDE HRS.PDE.MFAux

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- `∂_{x_i} F` as a kernel. -/
def px4b_K1 (i : Fin d) (F : Torus d → Torus d → ℝ) : Torus d → Torus d → ℝ :=
  fun x y => Torus.partialDeriv i (fun z => F z y) x

/-- `∂_{x_i}² F` as a kernel. -/
def px4b_K2 (i : Fin d) (F : Torus d → Torus d → ℝ) : Torus d → Torus d → ℝ :=
  px4b_K1 i (px4b_K1 i F)

/-- `∑_i ∂_i(ρ ∂_i F) = ∑_i (∂_iρ ∂_iF + ρ ∂_i²F)`. -/
def px4b_Eexp (ρ : Torus d → ℝ) (F : Torus d → Torus d → ℝ) : Torus d → Torus d → ℝ :=
  fun w y => ∑ i : Fin d, (Torus.partialDeriv i ρ w * px4b_K1 i F w y + ρ w * px4b_K2 i F w y)

lemma px4b_vol_int_of_mu (hρ : SmoothPosDensity ρ) {k : Torus d → ℝ}
    (hk : Integrable k (withDensityReal ρ)) : Integrable k := by
  have h1 := px4b_withDensity_int hρ hk
  have hρc : Continuous ρ := continuous_of_isSmooth hρ.smooth
  have hinv : Continuous (fun u => (ρ u)⁻¹) := hρc.inv₀ (fun u => (hρ.pos u).ne')
  obtain ⟨C, hC⟩ := PDE.MFSchauder.exists_bound_of_cont hinv
  refine (h1.bdd_mul (c := C) (f := fun u => (ρ u)⁻¹) hinv.aestronglyMeasurable
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hC u)).congr ?_
  refine Eventually.of_forall fun u => ?_
  simp only
  rw [← mul_assoc, inv_mul_cancel₀ (hρ.pos u).ne', one_mul]


lemma px4b_hdiv_eq (hρ : ContDiff ℝ ∞' (Torus.lift ρ)) {y : Torus d} {f : Torus d → ℝ}
    (hf : Nice ρ y f) (i : Fin d) {w : Torus d} (hw : w ≠ y) :
    Torus.partialDeriv i (fun u => ρ u * Torus.partialDeriv i f u) w =
      Torus.partialDeriv i ρ w * Torus.partialDeriv i f w +
        ρ w * Torus.partialDeriv i (fun u => Torus.partialDeriv i f u) w := by
  have hc2 : ContDiffAt ℝ 2 (Torus.lift f) (Torus.rep w) := hf.c2 _ (by rwa [Torus.mk_rep])
  have hdρ : DifferentiableAt ℝ (Torus.lift ρ) (Torus.rep w) :=
    (hρ.differentiable (by simp)) _
  have hdf : DifferentiableAt ℝ (Torus.lift (fun u => Torus.partialDeriv i f u)) (Torus.rep w) := by
    have e : Torus.lift (fun u => Torus.partialDeriv i f u) =
        fun v => fderiv ℝ (Torus.lift f) v (px4b_e i) := funext fun v => px4b_lift_partialDeriv f i v
    rw [e]
    exact ((hc2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const _)
  have := px4b_partialDeriv_mul i hdρ hdf
  rw [Torus.mk_rep] at this
  rw [this]; ring


/-- Class facts for the derivative kernels. -/
lemma px4b_K1_conormal {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ}
    (hm : 1 ≤ m) (hF : ConormalL σ b m B F) (i : Fin d) :
    ConormalL (σ + 1) (fun c => max (b c) (b (c + 1))) (m - 1) (2 * B) (px4b_K1 i F) :=
  conormal_partial_fst_aux hF hm i

lemma px4b_K2_conormal {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ}
    (hm : 2 ≤ m) (hF : ConormalL σ b m B F) (i : Fin d) :
    ConormalL (σ + 1 + 1) (fun c => max (max (b c) (b (c + 1))) (max (b (c + 1)) (b (c + 1 + 1))))
      (m - 1 - 1) (2 * (2 * B)) (px4b_K2 i F) :=
  conormal_partial_fst_aux (px4b_K1_conormal (by omega) hF i) (by omega) i

/-- Integrability of `∂_i(ρ ∂_i f)` for a conormal slice. -/
lemma px4b_hdiv_int (hd : 2 ≤ d) (hρ : SmoothPosDensity ρ) {σ : ℝ} (hσ : σ + 2 < d)
    {b : ℕ → ℕ} {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ} (hm : 2 ≤ m)
    (hF : ConormalL σ b m B F) (y : Torus d) (i : Fin d) :
    Integrable (Torus.partialDeriv i (fun u => ρ u * Torus.partialDeriv i (fun z => F z y) u)) := by
  have hnice := px4b_slice_nice hd hρ hσ hm hF y
  have I1 : Integrable (fun u => px4b_K1 i F u y) := px4b_vol_int_of_mu hρ
    (px4b_slice_int hd hρ (σ := σ + 1) (by linarith) (px4b_K1_conormal (by omega) hF i) y)
  have I2 : Integrable (fun u => px4b_K2 i F u y) := px4b_vol_int_of_mu hρ
    (px4b_slice_int hd hρ (σ := σ + 1 + 1) (by linarith) (px4b_K2_conormal hm hF i) y)
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1
  have hρc : Continuous ρ := continuous_of_isSmooth hρ.smooth
  have hρ'c : Continuous (Torus.partialDeriv i ρ) := PDE.continuous_partialDeriv i ρ hρ1
  obtain ⟨C1, hC1⟩ := PDE.MFSchauder.exists_bound_of_cont hρc
  obtain ⟨C2, hC2⟩ := PDE.MFSchauder.exists_bound_of_cont hρ'c
  have J1 := I1.bdd_mul (c := C2) hρ'c.aestronglyMeasurable
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hC2 u)
  have J2 := I2.bdd_mul (c := C1) hρc.aestronglyMeasurable
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hC1 u)
  refine (J1.add J2).congr ?_
  have hae : ∀ᵐ w ∂(volume : Measure (Torus d)), w ≠ y := by
    rw [ae_iff]; simpa using volume_singleton_torus (by omega : 1 ≤ d) y
  filter_upwards [hae] with w hw
  have := px4b_hdiv_eq hρ.smooth hnice i hw
  simp only [Pi.add_apply]
  rw [this]
  rfl


/-- The no-flux formula: for a conormal slice singular at `y`, `x ≠ y`,
`Jop f (x) = g ⋆ ∑_i ∂_i(ρ ∂_i f) (x)`, the divergence being the pointwise one. -/
theorem px4b_J_explicit (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ + 2 < d) {b : ℕ → ℕ} {m : ℕ}
    {B : ℝ} {F : Torus d → Torus d → ℝ} (hm : 2 ≤ m) (hF : ConormalL σ b m B F) {y x : Torus d}
    (hxy : x ≠ y) :
    Jop d s ρ (fun z => F z y) x = ∫ w, periodicRiesz d s (x - w) * px4b_Eexp ρ F w y := by
  obtain ⟨hg, hgs, hρ⟩ := px4b_kernel_facts H
  have hd := H.two_le
  have hnice := px4b_slice_nice hd H.rho_smooth hσ hm hF y
  obtain ⟨δ, hδ, hD⟩ := px4b_Jop_facts hg hgs hρ hxy hnice
  have hx0 : px4b_D (Torus.rep x - Torus.rep x) < δ := by
    rw [sub_self, px4b_D_mk_zero (mk_isLat isLat_zero)]; exact hδ
  have hdiff : ∀ i : Fin d, DifferentiableAt ℝ (Torus.lift (convFun (periodicRiesz d s)
      (fun u => ρ u * Torus.partialDeriv i (fun z => F z y) u))) (Torus.rep x) :=
    fun i => (hD _ hx0 i).2
  rw [px4b_Jop_eq_sum hdiff]
  have hE : ∀ i : Fin d, Integrable (fun w => periodicRiesz d s (x - w) *
        Torus.partialDeriv i (fun u => ρ u * Torus.partialDeriv i (fun z => F z y) u) w) ∧
      Torus.partialDeriv i (convFun (periodicRiesz d s)
        (fun u => ρ u * Torus.partialDeriv i (fun z => F z y) u)) x =
        convFun (periodicRiesz d s)
          (Torus.partialDeriv i (fun u => ρ u * Torus.partialDeriv i (fun z => F z y) u)) x := fun i =>
    px4b_partialDeriv_convFun hd i hg hgs hxy
      (fun v hv => px4b_Nice_hloc hρ hnice i hv) (hnice.hint i)
      (px4b_hdiv_int hd H.rho_smooth hσ hm hF y i)
  have hsum : ∀ i : Fin d, fderiv ℝ (Torus.lift (convFun (periodicRiesz d s)
      (fun u => ρ u * Torus.partialDeriv i (fun z => F z y) u))) (Torus.rep x) (EuclideanSpace.single i 1) =
      ∫ w, periodicRiesz d s (x - w) *
        Torus.partialDeriv i (fun u => ρ u * Torus.partialDeriv i (fun z => F z y) u) w := fun i =>
    (hE i).2
  simp_rw [hsum]
  rw [← integral_finset_sum _ (fun i _ => (hE i).1)]
  have hae : ∀ᵐ w ∂(volume : Measure (Torus d)), w ≠ y := by
    rw [ae_iff]; simpa using volume_singleton_torus (by omega : 1 ≤ d) y
  refine integral_congr_ae ?_
  filter_upwards [hae] with w hw
  rw [px4b_Eexp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [px4b_hdiv_eq hρ hnice i hw]
  rfl


/-- The rows of `∂_{x_i}F` and `∂_{x_i}²F` have mean zero when the rows of `F` do. -/
lemma px4b_rows_zero (hd : 2 ≤ d) (hρ : SmoothPosDensity ρ) {σ : ℝ} (hσ : σ + 2 < d)
    {b : ℕ → ℕ} {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ} (hm : 2 ≤ m)
    (hF : ConormalL σ b m B F) (hrow : ∀ x, ∫ y, F x y ∂(withDensityReal ρ) = 0) (i : Fin d)
    (x : Torus d) :
    ∫ y, px4b_K1 i F x y ∂(withDensityReal ρ) = 0 ∧
      ∫ y, px4b_K2 i F x y ∂(withDensityReal ρ) = 0 := by
  have h1 : ∀ x, ∫ y, px4b_K1 i F x y ∂(withDensityReal ρ) = 0 := fun x =>
    px4b_row_deriv_zero hd hρ (σ := σ) (by linarith) (by omega) hF i hrow x
  exact ⟨h1 x, px4b_row_deriv_zero hd hρ (σ := σ + 1) (by linarith) (m := m - 1) (by omega)
    (px4b_K1_conormal (by omega) hF i) i h1 x⟩

/-- The row integral of `Bop` over the second variable. -/
lemma px4b_B_row (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ + 2 < d) {b : ℕ → ℕ} {m : ℕ} {B : ℝ}
    {F : Torus d → Torus d → ℝ} (hm : 2 ≤ m) (hF : ConormalL σ b m B F)
    (hrow : ∀ x, ∫ y, F x y ∂(withDensityReal ρ) = 0) (x : Torus d) :
    Integrable (fun y => Bop d s V β ρ (fun z => F z y) x) (withDensityReal ρ) ∧
      ∫ y, Bop d s V β ρ (fun z => F z y) x ∂(withDensityReal ρ) = 0 := by
  have hd := H.two_le
  have hρ := H.rho_smooth
  have I1 : ∀ j, Integrable (fun y => px4b_K1 j F x y) (withDensityReal ρ) := fun j =>
    ((px4b_row_bound hd hρ (σ := σ + 1) (by linarith) (px4b_K1_conormal (by omega) hF j)).choose_spec x).1
  have I2 : ∀ j, Integrable (fun y => px4b_K2 j F x y) (withDensityReal ρ) := fun j =>
    ((px4b_row_bound hd hρ (σ := σ + 1 + 1) (by linarith) (px4b_K2_conormal hm hF j)).choose_spec x).1
  have hR : Integrable (fun y => β⁻¹ * ∑ i : Fin d, px4b_K2 i F x y +
      β⁻¹ * ∑ j : Fin d, (Torus.partialDeriv j ρ x / ρ x) * px4b_K1 j F x y) (withDensityReal ρ) :=
    ((integrable_finsetSum Finset.univ fun i _ => I2 i).const_mul β⁻¹).add
      ((integrable_finsetSum Finset.univ fun j _ => (I1 j).const_mul _).const_mul β⁻¹)
  have hae : (fun y => Bop d s V β ρ (fun z => F z y) x) =ᵐ[withDensityReal ρ]
      fun y => β⁻¹ * ∑ i : Fin d, px4b_K2 i F x y +
        β⁻¹ * ∑ j : Fin d, (Torus.partialDeriv j ρ x / ρ x) * px4b_K1 j F x y := by
    filter_upwards [px4b_ae_ne_mu (by omega : 1 ≤ d) ρ x] with y hy
    have hc2 : ContDiffAt ℝ 2 (Torus.lift (fun z => F z y)) (Torus.rep x) :=
      px4b_slice_c2 hm hF y _ (by rw [Torus.mk_rep]; exact Ne.symm hy)
    rw [px4b_Bop_eq H hc2]
    rfl
  refine ⟨hR.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_add ((integrable_finsetSum Finset.univ fun i _ => I2 i).const_mul β⁻¹)
    ((integrable_finsetSum Finset.univ fun j _ => (I1 j).const_mul _).const_mul β⁻¹),
    integral_const_mul, integral_const_mul, integral_finset_sum _ (fun i _ => I2 i),
    integral_finset_sum _ (fun j _ => (I1 j).const_mul _)]
  have z2 : ∀ i, ∫ y, px4b_K2 i F x y ∂(withDensityReal ρ) = 0 := fun i =>
    (px4b_rows_zero hd hρ hσ hm hF hrow i x).2
  have z1 : ∀ j, ∫ y, (Torus.partialDeriv j ρ x / ρ x) * px4b_K1 j F x y ∂(withDensityReal ρ) = 0 :=
    fun j => by
      rw [integral_const_mul, (px4b_rows_zero hd hρ hσ hm hF hrow j x).1, mul_zero]
  simp [z1, z2]


/-- The row integral of `Jop` over the second variable. -/
lemma px4b_J_row (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ + 2 < d) {b : ℕ → ℕ} {m : ℕ} {B : ℝ}
    {F : Torus d → Torus d → ℝ} (hm : 2 ≤ m) (hF : ConormalL σ b m B F)
    (hrow : ∀ x, ∫ y, F x y ∂(withDensityReal ρ) = 0) (x : Torus d) :
    Integrable (fun y => Jop d s ρ (fun z => F z y) x) (withDensityReal ρ) ∧
      ∫ y, Jop d s ρ (fun z => F z y) x ∂(withDensityReal ρ) = 0 := by
  obtain ⟨hg, hgs, hρs⟩ := px4b_kernel_facts H
  have hd := H.two_le
  have hρ := H.rho_smooth
  set μ := withDensityReal ρ with hμ
  haveI : IsProbabilityMeasure μ := isProb_withDensityReal hρ.density
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1
  have hρc : Continuous ρ := continuous_of_isSmooth hρ.smooth
  have hρ'c : ∀ i, Continuous (Torus.partialDeriv i ρ) := fun i => PDE.continuous_partialDeriv i ρ hρ1
  -- bounds and classes
  have hK1 := fun i => px4b_K1_conormal (σ := σ) (b := b) (m := m) (B := B) (F := F) (by omega) hF i
  have hK2 := fun i => px4b_K2_conormal (σ := σ) (b := b) (m := m) (B := B) (F := F) hm hF i
  have bd1 : ∀ i, ∃ K : ℝ, ∀ x, Integrable (fun y => px4b_K1 i F x y) μ ∧ ∫ y, |px4b_K1 i F x y| ∂μ ≤ K :=
    fun i => px4b_row_bound hd hρ (σ := σ + 1) (by linarith) (hK1 i)
  have bd2 : ∀ i, ∃ K : ℝ, ∀ x, Integrable (fun y => px4b_K2 i F x y) μ ∧ ∫ y, |px4b_K2 i F x y| ∂μ ≤ K :=
    fun i => px4b_row_bound hd hρ (σ := σ + 1 + 1) (by linarith) (hK2 i)
  choose KK1 hKK1 using bd1
  choose KK2 hKK2 using bd2
  have bq : ∀ i, ∃ Q : ℝ, ∀ w, |Torus.partialDeriv i ρ w| ≤ Q := fun i =>
    PDE.MFSchauder.exists_bound_of_cont (hρ'c i)
  choose Q hQ using bq
  obtain ⟨R, hR⟩ := PDE.MFSchauder.exists_bound_of_cont hρc
  -- the offZero kernels
  have hG1m : ∀ i, Measurable (Function.uncurry (offZero (px4b_K1 i F))) := fun i =>
    measurable_offZero_of_contDiffOn (hK1 i).smooth
  have hG2m : ∀ i, Measurable (Function.uncurry (offZero (px4b_K2 i F))) := fun i =>
    measurable_offZero_of_contDiffOn (hK2 i).smooth
  have hne : ∀ w : Torus d, ∀ᵐ y ∂μ, y ≠ w := fun w => px4b_ae_ne_mu (by omega) ρ w
  have hG1e : ∀ i w, (fun y => offZero (px4b_K1 i F) w y) =ᵐ[μ] fun y => px4b_K1 i F w y := fun i w => by
    filter_upwards [hne w] with y hy
    simp [offZero, Ne.symm hy]
  have hG2e : ∀ i w, (fun y => offZero (px4b_K2 i F) w y) =ᵐ[μ] fun y => px4b_K2 i F w y := fun i w => by
    filter_upwards [hne w] with y hy
    simp [offZero, Ne.symm hy]
  set Et : Torus d → Torus d → ℝ := fun w y => ∑ i : Fin d,
    (Torus.partialDeriv i ρ w * offZero (px4b_K1 i F) w y + ρ w * offZero (px4b_K2 i F) w y) with hEt
  have hEtm : Measurable (Function.uncurry Et) := by
    refine Finset.measurable_sum _ fun i _ => ?_
    refine Measurable.add ?_ ?_
    · exact ((hρ'c i).measurable.comp measurable_fst).mul (hG1m i)
    · exact (hρc.measurable.comp measurable_fst).mul (hG2m i)
  have hEtrow : ∀ w, Integrable (fun y => Et w y) μ := fun w => by
    refine integrable_finsetSum _ fun i _ => ?_
    refine Integrable.add ?_ ?_
    · exact ((hKK1 i w).1.congr (hG1e i w).symm).const_mul _
    · exact ((hKK2 i w).1.congr (hG2e i w).symm).const_mul _
  have hEtzero : ∀ w, ∫ y, Et w y ∂μ = 0 := fun w => by
    simp only [hEt]
    rw [integral_finset_sum _ fun i _ => ?_]
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [integral_add, integral_const_mul, integral_const_mul,
        integral_congr_ae (hG1e i w), integral_congr_ae (hG2e i w),
        (px4b_rows_zero hd hρ hσ hm hF hrow i w).1, (px4b_rows_zero hd hρ hσ hm hF hrow i w).2]
      · simp
      · exact ((hKK1 i w).1.congr (hG1e i w).symm).const_mul _
      · exact ((hKK2 i w).1.congr (hG2e i w).symm).const_mul _
    · refine Integrable.add ?_ ?_
      · exact ((hKK1 i w).1.congr (hG1e i w).symm).const_mul _
      · exact ((hKK2 i w).1.congr (hG2e i w).symm).const_mul _
  -- uniform row bound of `Et`
  have hEtbd : ∀ w, ∫ y, ‖Et w y‖ ∂μ ≤ ∑ i : Fin d, (Q i * KK1 i + R * KK2 i) := by
    intro w
    have hQ0 : ∀ i, 0 ≤ Q i := fun i => (abs_nonneg _).trans (hQ i w)
    have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR w)
    have i1 : ∀ i, Integrable (fun y => |offZero (px4b_K1 i F) w y|) μ := fun i =>
      ((hKK1 i w).1.congr (hG1e i w).symm).abs
    have i2 : ∀ i, Integrable (fun y => |offZero (px4b_K2 i F) w y|) μ := fun i =>
      ((hKK2 i w).1.congr (hG2e i w).symm).abs
    have hpt : ∀ y, ‖Et w y‖ ≤ ∑ i : Fin d, (Q i * |offZero (px4b_K1 i F) w y| +
        R * |offZero (px4b_K2 i F) w y|) := by
      intro y
      rw [Real.norm_eq_abs]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hQ i w) (abs_nonneg _)
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hR w) (abs_nonneg _)
    calc ∫ y, ‖Et w y‖ ∂μ ≤ ∫ y, ∑ i : Fin d, (Q i * |offZero (px4b_K1 i F) w y| +
          R * |offZero (px4b_K2 i F) w y|) ∂μ :=
        integral_mono (hEtrow w).norm
          (integrable_finsetSum _ fun i _ => ((i1 i).const_mul _).add ((i2 i).const_mul _))
          hpt
      _ = ∑ i : Fin d, (Q i * ∫ y, |offZero (px4b_K1 i F) w y| ∂μ +
          R * ∫ y, |offZero (px4b_K2 i F) w y| ∂μ) := by
        rw [integral_finset_sum (Finset.univ : Finset (Fin d)) (f := fun i y => Q i * |offZero (px4b_K1 i F) w y| +
          R * |offZero (px4b_K2 i F) w y|) fun i _ => ((i1 i).const_mul (Q i)).add ((i2 i).const_mul R)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_add ((i1 i).const_mul _) ((i2 i).const_mul _), integral_const_mul,
          integral_const_mul]
      _ ≤ ∑ i : Fin d, (Q i * KK1 i + R * KK2 i) := by
        refine Finset.sum_le_sum fun i _ => add_le_add ?_ ?_
        · refine mul_le_mul_of_nonneg_left ?_ (hQ0 i)
          have := (hKK1 i w).2
          rwa [integral_congr_ae ((hG1e i w).mono fun y (hy : offZero (px4b_K1 i F) w y = px4b_K1 i F w y) => by
            show |offZero (px4b_K1 i F) w y| = |px4b_K1 i F w y|; rw [hy])]
        · refine mul_le_mul_of_nonneg_left ?_ hR0
          have := (hKK2 i w).2
          rwa [integral_congr_ae ((hG2e i w).mono fun y (hy : offZero (px4b_K2 i F) w y = px4b_K2 i F w y) => by
            show |offZero (px4b_K2 i F) w y| = |px4b_K2 i F w y|; rw [hy])]
  -- the joint function
  obtain ⟨A, hA⟩ : ∃ A : Torus d × Torus d → ℝ,
      ∀ p, A p = periodicRiesz d s (x - p.1) * Et p.1 p.2 := ⟨_, fun _ => rfl⟩
  have hgm : Measurable (periodicRiesz d s : Torus d → ℝ) := PDE.LocInt.measurable_of_smoothOffZero hgs
  have hAe : A = fun p => periodicRiesz d s (x - p.1) * Et p.1 p.2 := funext hA
  have hAm : Measurable A := by
    rw [hAe]
    exact (hgm.comp (measurable_const.sub measurable_fst)).mul hEtm
  have hgx : Integrable (fun w => periodicRiesz d s (x - w)) := hg.comp_sub_left x
  have hint : Integrable A (volume.prod μ) := by
    rw [integrable_prod_iff hAm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun w => ?_, ?_⟩
    · have := (hEtrow w).const_mul (periodicRiesz d s (x - w))
      simpa only [hA] using this
    · refine Integrable.mono' (hgx.norm.mul_const (∑ i : Fin d, (Q i * KK1 i + R * KK2 i)))
        (hAm.norm.aestronglyMeasurable.integral_prod_right') (Eventually.of_forall fun w => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      calc ∫ y, ‖A (w, y)‖ ∂μ = ‖periodicRiesz d s (x - w)‖ * ∫ y, ‖Et w y‖ ∂μ := by
            rw [← integral_const_mul]
            refine integral_congr_ae (Eventually.of_forall fun y => ?_)
            show ‖A (w, y)‖ = _
            rw [hA, norm_mul]
        _ ≤ ‖periodicRiesz d s (x - w)‖ * ∑ i : Fin d, (Q i * KK1 i + R * KK2 i) :=
            mul_le_mul_of_nonneg_left (hEtbd w) (norm_nonneg _)
  -- Fubini
  have hFub := integral_integral_swap (f := fun (w : Torus d) (y : Torus d) => A (w, y)) hint
  have hzero : ∫ w, ∫ y, A (w, y) ∂μ = 0 := by
    have : ∀ w, ∫ y, A (w, y) ∂μ = 0 := fun w => by
      simp only [hA]
      rw [integral_const_mul, hEtzero, mul_zero]
    simp [this]
  -- identification with `Jop`
  have hJ : (fun y => Jop d s ρ (fun z => F z y) x) =ᵐ[μ] fun y => ∫ w, A (w, y) := by
    filter_upwards [px4b_ae_ne_mu (by omega : 1 ≤ d) ρ x] with y hy
    rw [px4b_J_explicit H hσ hm hF (Ne.symm hy)]
    refine integral_congr_ae ?_
    have hae : ∀ᵐ w ∂(volume : Measure (Torus d)), w ≠ y := by
      rw [ae_iff]; simpa using volume_singleton_torus (by omega : 1 ≤ d) y
    filter_upwards [hae] with w hw
    rw [hA]
    simp only [hEt, px4b_Eexp]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [offZero, hw]
  refine ⟨hint.integral_prod_right.congr hJ.symm, ?_⟩
  rw [integral_congr_ae hJ, ← hFub, hzero]

end HRS.Parx
end
