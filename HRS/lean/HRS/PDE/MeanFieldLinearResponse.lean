import HRS.PDE.MeanFieldAdjointFrozen
import HRS.PDE.MeanFieldAdjointSmoothing

/-!
# Response existence for `1 ≤ d` (package MF-01, packet P13a, part 1)

`exists_unique_response_of_one_le`: Lax–Milgram on `L²(μ)` for `A = I + β K P`, where `P` is the
centering projection.  The kernel operator `K` is shown to be bounded on `L²(μ)` by a Schur test
against the finite measure `μ = ρ dx` (`ρ` bounded), and `⟨K P f, f⟩ ≥ 0` is extended from
continuous functions by density.  See `HRS/PDE/MeanFieldAdjointPlan.md`, packet P13a.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.PDE.MFLinear

section Schur

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Cauchy–Schwarz for weighted `lintegral`s: `(∫ w u)² ≤ (∫ w)(∫ w u²)`. -/
theorem lintegral_cs (w u : α → ℝ≥0∞) (hw : AEMeasurable w μ) (hu : AEMeasurable u μ) :
    (∫⁻ y, w y * u y ∂μ) ^ 2 ≤ (∫⁻ y, w y ∂μ) * ∫⁻ y, w y * u y ^ 2 ∂μ := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (f := fun y => w y ^ (1 / 2 : ℝ))
    (g := fun y => w y ^ (1 / 2 : ℝ) * u y) (hw.pow_const _) ((hw.pow_const _).mul hu)
  have e1 : ∀ y, (w y ^ (1 / 2 : ℝ)) * (w y ^ (1 / 2 : ℝ) * u y) = w y * u y := fun y => by
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ y, (w y ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = w y := fun y => by
    rw [← ENNReal.rpow_mul]; norm_num
  have e3 : ∀ y, (w y ^ (1 / 2 : ℝ) * u y) ^ (2 : ℝ) = w y * u y ^ 2 := fun y => by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e2]
    norm_cast
  simp only [Pi.mul_apply, e1, e2, e3] at h1
  calc (∫⁻ y, w y * u y ∂μ) ^ 2
      ≤ ((∫⁻ y, w y ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ y, w y * u y ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left' h1 2
    _ = (∫⁻ y, w y ∂μ) * ∫⁻ y, w y * u y ^ 2 ∂μ := by
        rw [mul_pow]
        congr 1 <;>
        · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

/-- Schur test in `L²`. -/
theorem schur_sq [SFinite μ] (w : α → α → ℝ≥0∞) (W : ℝ≥0∞) (hWt : W ≠ ∞)
    (hW1 : ∀ x, ∫⁻ y, w x y ∂μ ≤ W) (hW2 : ∀ y, ∫⁻ x, w x y ∂μ ≤ W)
    (hwx : ∀ x, AEMeasurable (fun y => w x y) μ) (hwy : ∀ y, AEMeasurable (fun x => w x y) μ)
    (hw : AEMeasurable (fun p : α × α => w p.1 p.2) (μ.prod μ)) (u : α → ℝ≥0∞)
    (hu : AEMeasurable u μ) :
    ∫⁻ x, (∫⁻ y, w x y * u y ∂μ) ^ 2 ∂μ ≤ W ^ 2 * ∫⁻ y, u y ^ 2 ∂μ := by
  have hint : AEMeasurable (fun p : α × α => w p.1 p.2 * u p.2 ^ 2) (μ.prod μ) :=
    hw.mul ((hu.pow_const 2).comp_snd)
  calc ∫⁻ x, (∫⁻ y, w x y * u y ∂μ) ^ 2 ∂μ
      ≤ ∫⁻ x, W * ∫⁻ y, w x y * u y ^ 2 ∂μ ∂μ := by
        refine lintegral_mono fun x => ?_
        exact (lintegral_cs _ _ (hwx x) hu).trans (mul_le_mul_left (hW1 x) _)
    _ = W * ∫⁻ x, ∫⁻ y, w x y * u y ^ 2 ∂μ ∂μ := lintegral_const_mul' _ _ hWt
    _ = W * ∫⁻ y, ∫⁻ x, w x y * u y ^ 2 ∂μ ∂μ := by
        rw [lintegral_lintegral_swap hint]
    _ ≤ W * ∫⁻ y, W * u y ^ 2 ∂μ := by
        refine mul_le_mul_right (lintegral_mono fun y => ?_) _
        rw [lintegral_mul_const'' _ (hwy y)]
        exact mul_le_mul_left (hW2 y) _
    _ = W ^ 2 * ∫⁻ y, u y ^ 2 ∂μ := by
        rw [lintegral_const_mul' _ _ hWt, ← mul_assoc, sq]

/-- `L¹` Schur test. -/
theorem schur_one [SFinite μ] (w : α → α → ℝ≥0∞) (W : ℝ≥0∞)
    (hW2 : ∀ y, ∫⁻ x, w x y ∂μ ≤ W) (hwy : ∀ y, AEMeasurable (fun x => w x y) μ)
    (hw : AEMeasurable (fun p : α × α => w p.1 p.2) (μ.prod μ)) (u : α → ℝ≥0∞)
    (hu : AEMeasurable u μ) :
    ∫⁻ x, ∫⁻ y, w x y * u y ∂μ ∂μ ≤ W * ∫⁻ y, u y ∂μ := by
  have hint : AEMeasurable (fun p : α × α => w p.1 p.2 * u p.2) (μ.prod μ) :=
    hw.mul hu.comp_snd
  rw [lintegral_lintegral_swap hint, ← lintegral_const_mul'' _ hu]
  refine lintegral_mono fun y => ?_
  rw [lintegral_mul_const'' _ (hwy y), mul_comm W]
  exact (mul_le_mul_left (hW2 y) _).trans_eq (mul_comm _ _)

end Schur

section TorusKernel

variable {d : ℕ} {g ρ : Torus d → ℝ}

instance instSigmaFiniteWD (ρ : Torus d → ℝ) : SigmaFinite (withDensityReal ρ) :=
  sigmaFinite_withDensityReal ρ

theorem negInv : (volume : Measure (Torus d)).IsNegInvariant :=
  MeasureTheory.Measure.pi.isNegInvariant (fun _ : Fin d => (volume : Measure UnitAddCircle))

/-- Slice-wise bounds on the kernel against `μ = ρ dx`. -/
theorem kernel_W_bounds (hge : ∀ x, g (-x) = g x) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ) :
    (∀ x, ∫⁻ y, ‖g (x - y)‖ₑ ∂(withDensityReal ρ) ≤
        ENNReal.ofReal Λ * ∫⁻ y, ‖g y‖ₑ) ∧
    (∀ y, ∫⁻ x, ‖g (x - y)‖ₑ ∂(withDensityReal ρ) ≤
        ENNReal.ofReal Λ * ∫⁻ y, ‖g y‖ₑ) := by
  have key := fun x => KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ENNReal.ofReal ‖g z‖) x
  simp only [ofReal_norm] at key
  refine ⟨key, fun y => ?_⟩
  have : ∀ x, ‖g (x - y)‖ₑ = ‖g (y - x)‖ₑ := fun x => by
    rw [← neg_sub, hge]
  simp_rw [this]
  exact key y

theorem aestronglyMeasurable_kernel_prod (hg : AEStronglyMeasurable g volume) (ρ : Torus d → ℝ) :
    AEStronglyMeasurable (fun p : Torus d × Torus d => g (p.1 - p.2))
      ((withDensityReal ρ).prod (withDensityReal ρ)) := by
  have hac : withDensityReal ρ ≪ (volume : Measure (Torus d)) :=
    withDensity_absolutelyContinuous _ _
  have := negInv (d := d)
  have := hg.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_sub_of_right_invariant (volume : Measure (Torus d)) volume)
  exact this.mono_ac (hac.prod hac)

theorem aemeasurable_kernel_slices (hg : AEStronglyMeasurable g volume) (ρ : Torus d → ℝ) :
    (∀ x, AEMeasurable (fun y => ‖g (x - y)‖ₑ) (withDensityReal ρ)) ∧
    (∀ y, AEMeasurable (fun x => ‖g (x - y)‖ₑ) (withDensityReal ρ)) ∧
    AEMeasurable (fun p : Torus d × Torus d => ‖g (p.1 - p.2)‖ₑ)
      ((withDensityReal ρ).prod (withDensityReal ρ)) := by
  have hac : withDensityReal ρ ≪ (volume : Measure (Torus d)) :=
    withDensity_absolutelyContinuous _ _
  have := negInv (d := d)
  refine ⟨fun x => ?_, fun y => ?_, (aestronglyMeasurable_kernel_prod hg ρ).enorm⟩
  · have := hg.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
    exact (this.mono_ac hac).enorm
  · have := hg.comp_measurePreserving (measurePreserving_sub_right volume y)
    exact (this.mono_ac hac).enorm

/-- Standing hypotheses on the kernel `g` and the density `ρ ≤ Λ`. -/
structure KS (g ρ : Torus d → ℝ) (Λ : ℝ) : Prop where
  int : Integrable g
  even : ∀ x, g (-x) = g x
  prob : IsProbDensity ρ
  bd : ∀ x, ρ x ≤ Λ

/-- The Schur constant. -/
def Wc (g : Torus d → ℝ) (Λ : ℝ) : ℝ≥0∞ := ENNReal.ofReal Λ * ∫⁻ y, ‖g y‖ₑ

theorem KS.W_ne_top {Λ : ℝ} (H : KS g ρ Λ) : Wc g Λ ≠ ∞ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top H.int.hasFiniteIntegral.ne

theorem KS.isProb {Λ : ℝ} (H : KS g ρ Λ) : IsProbabilityMeasure (withDensityReal ρ) :=
  MFSemigroup.isProb_withDensityReal H.prob

/-- `Φ f (x) = ∫ g(x-y) f(y) dμ(y)`. -/
def Phi (g ρ f : Torus d → ℝ) (x : Torus d) : ℝ := ∫ y, g (x - y) * f y ∂(withDensityReal ρ)

theorem kop_eq_Phi (g ρ f : Torus d → ℝ) :
    Kop g (withDensityReal ρ) f = fun x => Phi g ρ f x - pair (withDensityReal ρ) (Phi g ρ f) :=
  rfl

theorem integrable_kernel_prod {Λ : ℝ} (H : KS g ρ Λ) {f : Torus d → ℝ}
    (hf : Integrable f (withDensityReal ρ)) :
    Integrable (fun p : Torus d × Torus d => g (p.1 - p.2) * f p.2)
      ((withDensityReal ρ).prod (withDensityReal ρ)) := by
  obtain ⟨hx, hy, hp⟩ := aemeasurable_kernel_slices H.int.aestronglyMeasurable ρ
  obtain ⟨hW1, hW2⟩ := kernel_W_bounds H.even Λ H.bd
  have hm : AEStronglyMeasurable (fun p : Torus d × Torus d => g (p.1 - p.2) * f p.2)
      ((withDensityReal ρ).prod (withDensityReal ρ)) :=
    (aestronglyMeasurable_kernel_prod H.int.aestronglyMeasurable ρ).mul
      (hf.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  refine ⟨hm, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod _ hm.enorm]
  simp only [enorm_mul]
  refine lt_of_le_of_lt (schur_one (fun x y => ‖g (x - y)‖ₑ) (Wc g Λ) hW2 hy hp (fun y => ‖f y‖ₑ)
    hf.aestronglyMeasurable.enorm) ?_
  exact ENNReal.mul_lt_top H.W_ne_top.lt_top hf.hasFiniteIntegral

theorem ae_integrable_slice {Λ : ℝ} (H : KS g ρ Λ) {f : Torus d → ℝ}
    (hf : Integrable f (withDensityReal ρ)) :
    ∀ᵐ x ∂(withDensityReal ρ), Integrable (fun y => g (x - y) * f y) (withDensityReal ρ) :=
  (integrable_kernel_prod H hf).prod_right_ae

theorem integrable_Phi {Λ : ℝ} (H : KS g ρ Λ) {f : Torus d → ℝ}
    (hf : Integrable f (withDensityReal ρ)) : Integrable (Phi g ρ f) (withDensityReal ρ) :=
  (integrable_kernel_prod H hf).integral_prod_left

theorem lintegral_Phi_sq {Λ : ℝ} (H : KS g ρ Λ) {f : Torus d → ℝ}
    (hf : AEStronglyMeasurable f (withDensityReal ρ)) :
    ∫⁻ x, ‖Phi g ρ f x‖ₑ ^ 2 ∂(withDensityReal ρ) ≤
      Wc g Λ ^ 2 * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(withDensityReal ρ) := by
  obtain ⟨hx, hy, hp⟩ := aemeasurable_kernel_slices H.int.aestronglyMeasurable ρ
  obtain ⟨hW1, hW2⟩ := kernel_W_bounds H.even Λ H.bd
  refine le_trans (lintegral_mono fun x => ?_)
    (schur_sq (fun x y => ‖g (x - y)‖ₑ) (Wc g Λ) H.W_ne_top hW1 hW2 hx hy hp (fun y => ‖f y‖ₑ)
      hf.enorm)
  refine pow_le_pow_left' ?_ 2
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  simp only [enorm_mul]

theorem eLpNorm_two_pow {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem memLp_Phi {Λ : ℝ} (H : KS g ρ Λ) {f : Torus d → ℝ}
    (hf : MemLp f 2 (withDensityReal ρ)) :
    MemLp (Phi g ρ f) 2 (withDensityReal ρ) ∧
    eLpNorm (Phi g ρ f) 2 (withDensityReal ρ) ≤ Wc g Λ * eLpNorm f 2 (withDensityReal ρ) := by
  have := H.isProb
  have hfi : Integrable f (withDensityReal ρ) := hf.integrable one_le_two
  have hPm : AEStronglyMeasurable (Phi g ρ f) (withDensityReal ρ) :=
    (integrable_Phi H hfi).aestronglyMeasurable
  have h := lintegral_Phi_sq H hf.aestronglyMeasurable
  rw [← eLpNorm_two_pow hPm, ← eLpNorm_two_pow hf.aestronglyMeasurable, ← mul_pow] at h
  have hle := (ENNReal.pow_le_pow_left_iff (by norm_num)).1 h
  exact ⟨hle.trans_lt (ENNReal.mul_lt_top H.W_ne_top.lt_top hf), hle⟩

theorem memLp_Kop {Λ : ℝ} (H : KS g ρ Λ) {f : Torus d → ℝ}
    (hf : MemLp f 2 (withDensityReal ρ)) :
    MemLp (Kop g (withDensityReal ρ) f) 2 (withDensityReal ρ) ∧
    eLpNorm (Kop g (withDensityReal ρ) f) 2 (withDensityReal ρ) ≤
      2 * Wc g Λ * eLpNorm f 2 (withDensityReal ρ) := by
  have := H.isProb
  obtain ⟨hP, hPle⟩ := memLp_Phi H hf
  have hfi : Integrable f (withDensityReal ρ) := hf.integrable one_le_two
  have hPi := integrable_Phi H hfi
  set c := pair (withDensityReal ρ) (Phi g ρ f) with hc
  have hcle : ‖c‖ₑ ≤ eLpNorm (Phi g ρ f) 2 (withDensityReal ρ) := by
    calc ‖c‖ₑ ≤ ∫⁻ x, ‖Phi g ρ f x‖ₑ ∂(withDensityReal ρ) := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (Phi g ρ f) 1 (withDensityReal ρ) := (eLpNorm_one_eq_lintegral_enorm hPi.aestronglyMeasurable).symm
      _ ≤ eLpNorm (Phi g ρ f) 2 (withDensityReal ρ) :=
        eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have hconst : eLpNorm (fun _ : Torus d => c) 2 (withDensityReal ρ) = ‖c‖ₑ := by
    rw [eLpNorm_const _ (by norm_num) (NeZero.ne _)]
    simp
  have hK : Kop g (withDensityReal ρ) f = fun x => Phi g ρ f x - c := kop_eq_Phi g ρ f
  rw [hK]
  have hsub : eLpNorm (fun x => Phi g ρ f x - c) 2 (withDensityReal ρ) ≤
      eLpNorm (Phi g ρ f) 2 (withDensityReal ρ) + ‖c‖ₑ := by
    have := eLpNorm_sub_le (μ := withDensityReal ρ) (p := 2) (f := Phi g ρ f) (g := fun _ => c)
      (by norm_num)
    rw [hconst] at this
    exact this
  have hbd : eLpNorm (fun x => Phi g ρ f x - c) 2 (withDensityReal ρ) ≤
      2 * Wc g Λ * eLpNorm f 2 (withDensityReal ρ) := by
    calc _ ≤ eLpNorm (Phi g ρ f) 2 (withDensityReal ρ) + ‖c‖ₑ := hsub
      _ ≤ eLpNorm (Phi g ρ f) 2 (withDensityReal ρ) + eLpNorm (Phi g ρ f) 2 (withDensityReal ρ) :=
        add_le_add_right hcle _
      _ ≤ _ := by
        rw [← two_mul, mul_assoc]
        exact mul_le_mul_right hPle _
  exact ⟨hbd.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) H.W_ne_top.lt_top) hf), hbd⟩

theorem Phi_congr {f f' : Torus d → ℝ} (h : f =ᵐ[withDensityReal ρ] f') :
    Phi g ρ f = Phi g ρ f' := by
  funext x
  unfold Phi
  refine integral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy]

theorem Kop_congr {f f' : Torus d → ℝ} (h : f =ᵐ[withDensityReal ρ] f') :
    Kop g (withDensityReal ρ) f = Kop g (withDensityReal ρ) f' := by
  rw [kop_eq_Phi, kop_eq_Phi, Phi_congr h]

theorem Phi_add_ae {Λ : ℝ} (H : KS g ρ Λ) {a b : Torus d → ℝ}
    (ha : Integrable a (withDensityReal ρ)) (hb : Integrable b (withDensityReal ρ)) :
    Phi g ρ (fun y => a y + b y) =ᵐ[withDensityReal ρ] fun x => Phi g ρ a x + Phi g ρ b x := by
  filter_upwards [ae_integrable_slice H ha, ae_integrable_slice H hb] with x hxa hxb
  unfold Phi
  simp_rw [mul_add]
  exact integral_add hxa hxb

theorem Kop_add_ae {Λ : ℝ} (H : KS g ρ Λ) {a b : Torus d → ℝ}
    (ha : Integrable a (withDensityReal ρ)) (hb : Integrable b (withDensityReal ρ)) :
    Kop g (withDensityReal ρ) (fun y => a y + b y) =ᵐ[withDensityReal ρ]
      fun x => Kop g (withDensityReal ρ) a x + Kop g (withDensityReal ρ) b x := by
  have h1 := Phi_add_ae H ha hb
  have h2 : pair (withDensityReal ρ) (Phi g ρ (fun y => a y + b y)) =
      pair (withDensityReal ρ) (Phi g ρ a) + pair (withDensityReal ρ) (Phi g ρ b) := by
    unfold pair
    rw [← integral_add (integrable_Phi H ha) (integrable_Phi H hb)]
    exact integral_congr_ae h1
  filter_upwards [h1] with x hx
  rw [kop_eq_Phi, kop_eq_Phi, kop_eq_Phi]
  simp only
  rw [hx, h2]
  ring

theorem Kop_smul (c : ℝ) (f : Torus d → ℝ) :
    Kop g (withDensityReal ρ) (fun y => c * f y) = fun x => c * Kop g (withDensityReal ρ) f x := by
  have h1 : ∀ x, Phi g ρ (fun y => c * f y) x = c * Phi g ρ f x := fun x => by
    unfold Phi
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  have h2 : pair (withDensityReal ρ) (Phi g ρ (fun y => c * f y)) =
      c * pair (withDensityReal ρ) (Phi g ρ f) := by
    unfold pair
    simp_rw [h1]
    exact integral_const_mul _ _
  funext x
  rw [kop_eq_Phi, kop_eq_Phi]
  simp only
  rw [h1, h2]
  ring

end TorusKernel

section LpLevel

variable {d : ℕ} {g ρ : Torus d → ℝ} {Λ : ℝ}

/-- `K` as a bounded operator on `L²(μ)`. -/
def KopLp (H : KS g ρ Λ) : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ) :=
  LinearMap.mkContinuous
    { toFun := fun u => (memLp_Kop H (Lp.memLp u)).1.toLp (Kop g (withDensityReal ρ) u)
      map_add' := fun u v => by
        have := H.isProb
        have hu := (Lp.memLp u).integrable one_le_two
        have hv := (Lp.memLp v).integrable one_le_two
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp (memLp_Kop H (Lp.memLp (u + v))).1,
          Lp.coeFn_add (((memLp_Kop H (Lp.memLp u)).1).toLp (Kop g (withDensityReal ρ) u))
            (((memLp_Kop H (Lp.memLp v)).1).toLp (Kop g (withDensityReal ρ) v)),
          MemLp.coeFn_toLp (memLp_Kop H (Lp.memLp u)).1,
          MemLp.coeFn_toLp (memLp_Kop H (Lp.memLp v)).1,
          Kop_add_ae H hu hv, Lp.coeFn_add u v] with x h1 h2 h3 h4 h5 h6
        rw [h1, h2]
        simp only [Pi.add_apply]
        rw [h3, h4]
        rw [Kop_congr (g := g) (ρ := ρ) (f := ⇑(u + v)) (f' := fun y => u y + v y)
          (Lp.coeFn_add u v)]
        exact h5
      map_smul' := fun c u => by
        have := H.isProb
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp (memLp_Kop H (Lp.memLp (c • u))).1,
          Lp.coeFn_smul c (((memLp_Kop H (Lp.memLp u)).1).toLp (Kop g (withDensityReal ρ) u)),
          MemLp.coeFn_toLp (memLp_Kop H (Lp.memLp u)).1, Lp.coeFn_smul c u] with x h1 h2 h3 h4
        rw [RingHom.id_apply, h1, h2]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [h3]
        rw [Kop_congr (g := g) (ρ := ρ) (f := ⇑(c • u)) (f' := fun y => c * u y)
          (by filter_upwards [Lp.coeFn_smul c u] with y hy; rw [hy]; rfl)]
        rw [Kop_smul] }
    (2 * Wc g Λ).toReal (fun u => by
      have := H.isProb
      show ‖(memLp_Kop H (Lp.memLp u)).1.toLp (Kop g (withDensityReal ρ) u)‖ ≤ _
      rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
      refine ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) H.W_ne_top)
        (Lp.eLpNorm_ne_top u)) (memLp_Kop H (Lp.memLp u)).2)

theorem KopLp_coe (H : KS g ρ Λ) (u : Lp ℝ 2 (withDensityReal ρ)) :
    ⇑(KopLp H u) =ᵐ[withDensityReal ρ] Kop g (withDensityReal ρ) ⇑u :=
  MemLp.coeFn_toLp (memLp_Kop H (Lp.memLp u)).1

/-- The constant function `1` in `L²(μ)`. -/
def oneLp (H : KS g ρ Λ) : Lp ℝ 2 (withDensityReal ρ) :=
  have := H.isProb
  (memLp_const (1 : ℝ)).toLp (fun _ => 1)

/-- The centering projection on `L²(μ)`. -/
def PcLp (H : KS g ρ Λ) : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ) :=
  ContinuousLinearMap.id ℝ _ - (innerSL ℝ (oneLp H)).smulRight (oneLp H)

theorem inner_oneLp (H : KS g ρ Λ) (u : Lp ℝ 2 (withDensityReal ρ)) :
    inner ℝ (oneLp H) u = pair (withDensityReal ρ) ⇑u := by
  have := H.isProb
  rw [MeasureTheory.L2.inner_def]
  unfold pair
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_const (1 : ℝ))] with x hx
  have : (oneLp H : Torus d → ℝ) x = 1 := hx
  rw [this]
  simp

theorem PcLp_coe (H : KS g ρ Λ) (u : Lp ℝ 2 (withDensityReal ρ)) :
    ⇑(PcLp H u) =ᵐ[withDensityReal ρ] projMean (withDensityReal ρ) ⇑u := by
  have := H.isProb
  have h1 : PcLp H u = u - (pair (withDensityReal ρ) ⇑u) • oneLp H := by
    simp [PcLp, inner_oneLp]
  rw [h1]
  filter_upwards [Lp.coeFn_sub u ((pair (withDensityReal ρ) ⇑u) • oneLp H),
    Lp.coeFn_smul (pair (withDensityReal ρ) ⇑u) (oneLp H),
    MemLp.coeFn_toLp (memLp_const (1 : ℝ))] with x h2 h3 h4
  rw [h2]
  simp only [Pi.sub_apply, projMean]
  rw [h3]
  have : (oneLp H : Torus d → ℝ) x = 1 := h4
  simp [this]

/-- `T = K ∘ P` on `L²(μ)`. -/
def TLp (H : KS g ρ Λ) : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ) :=
  (KopLp H).comp (PcLp H)

theorem TLp_coe (H : KS g ρ Λ) (u : Lp ℝ 2 (withDensityReal ρ)) :
    ⇑(TLp H u) =ᵐ[withDensityReal ρ]
      Kop g (withDensityReal ρ) (projMean (withDensityReal ρ) ⇑u) := by
  have e := KopLp_coe H (PcLp H u)
  rw [Kop_congr (PcLp_coe H u)] at e
  exact e

theorem pair_projMean_zero (H : KS g ρ Λ) (f : Torus d → ℝ) :
    pair (withDensityReal ρ) (projMean (withDensityReal ρ) f) = 0 := by
  have := H.isProb
  exact MFSemigroup.pair_projMean _ f

/-- `⟨K P f, f⟩_{L²(μ)} ≥ 0` for continuous `f` (not necessarily centered). -/
theorem l2Inner_kop_projMean_nonneg (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (hprob : IsProbDensity ρ) (hρc : Continuous ρ) (f : Torus d → ℝ) (hf : Continuous f) :
    0 ≤ l2Inner (withDensityReal ρ)
      (Kop (periodicRiesz d s) (withDensityReal ρ) (projMean (withDensityReal ρ) f)) f := by
  have hP := MFSemigroup.isProb_withDensityReal hprob
  set c := pair (withDensityReal ρ) f with hc
  set f0 := projMean (withDensityReal ρ) f with hf0
  have hf0c : Continuous f0 := hf.sub continuous_const
  have h0 : pair (withDensityReal ρ) f0 = 0 := MFSemigroup.pair_projMean _ f
  have hnn := MFAdjoint.l2Inner_kop_nonneg' hd s hs0 hsd ρ hprob hρc f0 hf0c h0
  set F := Kop (periodicRiesz d s) (withDensityReal ρ) f0 with hF
  have hFc : Continuous F := by
    rw [hF, MFAdjoint.kop_eq s hprob]
    exact (MFAdjoint.continuous_conv_kernel hd s hs0 hsd (hρc.mul hf0c)).sub continuous_const
  have hFp : pair (withDensityReal ρ) F = 0 := MFSemigroup.pair_projMean _ _
  have hint : ∀ {a : Torus d → ℝ}, Continuous a → Integrable a (withDensityReal ρ) :=
    fun ha => ha.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have e : l2Inner (withDensityReal ρ) F f =
      l2Inner (withDensityReal ρ) F f0 + c * pair (withDensityReal ρ) F := by
    unfold l2Inner pair
    rw [← integral_const_mul, ← integral_add (f := fun x => F x * f0 x) (g := fun x => c * F x)
      (hint (hFc.mul hf0c)) ((hint hFc).const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hf0, projMean]
    ring
  rw [e, hFp, mul_zero, add_zero]
  exact hnn

theorem TLp_inner_nonneg (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (H : KS (periodicRiesz d s) ρ Λ) (hρc : Continuous ρ) (u : Lp ℝ 2 (withDensityReal ρ)) :
    0 ≤ inner ℝ (TLp H u) u := by
  have hP := H.isProb
  have hdense : DenseRange (ContinuousMap.toLp (E := ℝ) (α := Torus d) 2 (withDensityReal ρ) ℝ) :=
    ContinuousMap.toLp_denseRange ℝ (withDensityReal ρ) ℝ (by norm_num)
  refine hdense.induction_on u (isClosed_le continuous_const
    ((TLp H).continuous.inner continuous_id)) (fun f => ?_)
  set v := ContinuousMap.toLp (E := ℝ) (α := Torus d) 2 (withDensityReal ρ) ℝ f with hv
  have hvf : ⇑v =ᵐ[withDensityReal ρ] ⇑f := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (μ := withDensityReal ρ) f
  have hpair : pair (withDensityReal ρ) ⇑v = pair (withDensityReal ρ) ⇑f :=
    integral_congr_ae hvf
  have hproj : projMean (withDensityReal ρ) ⇑v =ᵐ[withDensityReal ρ]
      projMean (withDensityReal ρ) ⇑f := by
    filter_upwards [hvf] with y hy
    simp only [projMean, hy, hpair]
  have hnn := l2Inner_kop_projMean_nonneg hd s hs0 hsd H.prob hρc ⇑f f.continuous
  rw [MeasureTheory.L2.inner_def]
  refine le_of_le_of_eq hnn ?_
  unfold l2Inner
  refine integral_congr_ae ?_
  filter_upwards [TLp_coe H v, hvf] with x h1 h2
  rw [h1, h2, Kop_congr hproj]
  simp [mul_comm]

/-- Transfer of `l2Inner (Kop (projMean a)) b` under a.e. equality of the arguments. -/
theorem l2Inner_Kop_projMean_ae (k ρ : Torus d → ℝ) {a a' b b' : Torus d → ℝ}
    (ha : a =ᵐ[withDensityReal ρ] a') (hb : b =ᵐ[withDensityReal ρ] b') :
    l2Inner (withDensityReal ρ) (Kop k (withDensityReal ρ) (projMean (withDensityReal ρ) a)) b =
      l2Inner (withDensityReal ρ) (Kop k (withDensityReal ρ) (projMean (withDensityReal ρ) a')) b' := by
  have hp : pair (withDensityReal ρ) a = pair (withDensityReal ρ) a' := integral_congr_ae ha
  have hk : Kop k (withDensityReal ρ) (projMean (withDensityReal ρ) a) =
      Kop k (withDensityReal ρ) (projMean (withDensityReal ρ) a') := by
    refine Kop_congr (g := k) ?_
    filter_upwards [ha] with x hx
    simp only [projMean, hx, hp]
  rw [hk]
  unfold l2Inner
  refine integral_congr_ae ?_
  filter_upwards [hb] with x hx
  rw [hx]

/-- The `L²(μ)` inner product as the integral of the a.e. representatives. -/
theorem innerLp_eq_l2Inner (ρ : Torus d → ℝ) (a b : Lp ℝ 2 (withDensityReal ρ)) :
    inner ℝ a b = l2Inner (withDensityReal ρ) ⇑a ⇑b := by
  rw [MeasureTheory.L2.inner_def]
  unfold l2Inner
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_comm]

theorem inner_TLp_eq_l2Inner {k ρ : Torus d → ℝ} {Λ : ℝ} (H : KS k ρ Λ)
    (u v : Lp ℝ 2 (withDensityReal ρ)) :
    inner ℝ (TLp H u) v =
      l2Inner (withDensityReal ρ) (Kop k (withDensityReal ρ) (projMean (withDensityReal ρ) ⇑u)) ⇑v := by
  rw [innerLp_eq_l2Inner]
  unfold l2Inner
  refine integral_congr_ae ?_
  filter_upwards [TLp_coe H u] with x hx
  rw [hx]

/-- `⟨K P f, g⟩ = ⟨K P g, f⟩` in `L²(μ)` for continuous `f, g` (from the symmetry of `K` on centered
continuous functions, `l2Inner_kop_symm'`). -/
theorem l2Inner_kop_projMean_symm (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (ρ : Torus d → ℝ) (hprob : IsProbDensity ρ) (hρc : Continuous ρ) (f g : Torus d → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    l2Inner (withDensityReal ρ) (Kop (periodicRiesz d s) (withDensityReal ρ)
        (projMean (withDensityReal ρ) f)) g =
      l2Inner (withDensityReal ρ) (Kop (periodicRiesz d s) (withDensityReal ρ)
        (projMean (withDensityReal ρ) g)) f := by
  have hP := MFSemigroup.isProb_withDensityReal hprob
  have hKc : ∀ G : Torus d → ℝ, Continuous G →
      Continuous (Kop (periodicRiesz d s) (withDensityReal ρ) G) := by
    intro G hG
    rw [MFAdjoint.kop_eq s hprob]
    exact (MFAdjoint.continuous_conv_kernel hd s hs0 hsd (hρc.mul hG)).sub continuous_const
  have hPf : Continuous (projMean (withDensityReal ρ) f) := hf.sub continuous_const
  have hPg : Continuous (projMean (withDensityReal ρ) g) := hg.sub continuous_const
  have hcf : pair (withDensityReal ρ) (projMean (withDensityReal ρ) f) = 0 :=
    MFSemigroup.pair_projMean _ f
  have hcg : pair (withDensityReal ρ) (projMean (withDensityReal ρ) g) = 0 :=
    MFSemigroup.pair_projMean _ g
  have hKF : pair (withDensityReal ρ)
      (Kop (periodicRiesz d s) (withDensityReal ρ) (projMean (withDensityReal ρ) f)) = 0 :=
    MFSemigroup.pair_projMean _ _
  have hKG : pair (withDensityReal ρ)
      (Kop (periodicRiesz d s) (withDensityReal ρ) (projMean (withDensityReal ρ) g)) = 0 :=
    MFSemigroup.pair_projMean _ _
  calc l2Inner (withDensityReal ρ) (Kop (periodicRiesz d s) (withDensityReal ρ)
          (projMean (withDensityReal ρ) f)) g
      = l2Inner (withDensityReal ρ) (Kop (periodicRiesz d s) (withDensityReal ρ)
          (projMean (withDensityReal ρ) f)) (projMean (withDensityReal ρ) g) :=
        (MFAdjoint.l2Inner_projMean_right hprob hρc (hKc _ hPf) hg hKF).symm
    _ = l2Inner (withDensityReal ρ) (projMean (withDensityReal ρ) f)
          (Kop (periodicRiesz d s) (withDensityReal ρ) (projMean (withDensityReal ρ) g)) :=
        MFAdjoint.l2Inner_kop_symm' hd s hs0 hsd ρ hprob hρc _ _ hPf hPg hcf hcg
    _ = l2Inner (withDensityReal ρ) f
          (Kop (periodicRiesz d s) (withDensityReal ρ) (projMean (withDensityReal ρ) g)) := by
        rw [MFAdjoint.l2Inner_comm', MFAdjoint.l2Inner_projMean_right hprob hρc (hKc _ hPg) hf hKG,
          MFAdjoint.l2Inner_comm']
    _ = l2Inner (withDensityReal ρ) (Kop (periodicRiesz d s) (withDensityReal ρ)
          (projMean (withDensityReal ρ) g)) f := MFAdjoint.l2Inner_comm' _ _ _

/-- Symmetry of `T = K ∘ P` on `L²(μ)` for `1 ≤ d` (density of continuous functions). -/
theorem TLp_symm (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (H : KS (periodicRiesz d s) ρ Λ) (hρc : Continuous ρ) (u v : Lp ℝ 2 (withDensityReal ρ)) :
    inner ℝ (TLp H u) v = inner ℝ u (TLp H v) := by
  have hP := H.isProb
  have hdense : DenseRange (ContinuousMap.toLp (E := ℝ) (α := Torus d) 2 (withDensityReal ρ) ℝ) :=
    ContinuousMap.toLp_denseRange ℝ (withDensityReal ρ) ℝ (by norm_num)
  have c1 : ∀ f g : C(Torus d, ℝ),
      inner ℝ (TLp H (ContinuousMap.toLp (E := ℝ) (α := Torus d) 2 (withDensityReal ρ) ℝ f))
          (ContinuousMap.toLp (E := ℝ) (α := Torus d) 2 (withDensityReal ρ) ℝ g) =
        inner ℝ (ContinuousMap.toLp (E := ℝ) (α := Torus d) 2 (withDensityReal ρ) ℝ f)
          (TLp H (ContinuousMap.toLp (E := ℝ) (α := Torus d) 2 (withDensityReal ρ) ℝ g)) := by
    intro f g
    have hf' : ⇑(ContinuousMap.toLp (E := ℝ) (α := Torus d) 2 (withDensityReal ρ) ℝ f) =ᵐ[withDensityReal ρ]
        ⇑f := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (μ := withDensityReal ρ) f
    have hg' : ⇑(ContinuousMap.toLp (E := ℝ) (α := Torus d) 2 (withDensityReal ρ) ℝ g) =ᵐ[withDensityReal ρ]
        ⇑g := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (μ := withDensityReal ρ) g
    have e := (real_inner_comm (ContinuousMap.toLp (E := ℝ) (α := Torus d) 2 (withDensityReal ρ) ℝ f)
      (TLp H (ContinuousMap.toLp (E := ℝ) (α := Torus d) 2 (withDensityReal ρ) ℝ g))).symm
    rw [e, inner_TLp_eq_l2Inner H, inner_TLp_eq_l2Inner H]
    refine (l2Inner_Kop_projMean_ae (periodicRiesz d s) ρ hf' hg').trans ?_
    refine (l2Inner_kop_projMean_symm hd s hs0 hsd ρ H.prob hρc ⇑f ⇑g f.continuous g.continuous).trans ?_
    exact (l2Inner_Kop_projMean_ae (periodicRiesz d s) ρ hg' hf').symm
  have c2 : ∀ g : C(Torus d, ℝ), ∀ w : Lp ℝ 2 (withDensityReal ρ),
      inner ℝ (TLp H w) (ContinuousMap.toLp (E := ℝ) (α := Torus d) 2 (withDensityReal ρ) ℝ g) =
        inner ℝ w (TLp H (ContinuousMap.toLp (E := ℝ) (α := Torus d) 2 (withDensityReal ρ) ℝ g)) := by
    intro g w
    have cl : IsClosed {x : Lp ℝ 2 (withDensityReal ρ) |
        inner ℝ (TLp H x) (ContinuousMap.toLp (E := ℝ) (α := Torus d) 2 (withDensityReal ρ) ℝ g) =
          inner ℝ x (TLp H (ContinuousMap.toLp (E := ℝ) (α := Torus d) 2 (withDensityReal ρ) ℝ g))} :=
      isClosed_eq ((TLp H).continuous.inner continuous_const)
        (continuous_id.inner continuous_const)
    exact hdense.induction_on w cl (fun f => c1 f g)
  have cl : IsClosed {x : Lp ℝ 2 (withDensityReal ρ) | inner ℝ (TLp H u) x = inner ℝ u (TLp H x)} :=
    isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner (TLp H).continuous)
  exact hdense.induction_on v cl (fun g => c2 g u)

end LpLevel

section LaxMilgram

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem bijective_of_coercive (A : E →L[ℝ] E) (hA : ∀ u, ‖u‖ * ‖u‖ ≤ inner ℝ (A u) u) :
    Function.Bijective A := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).comp A
  have hB : IsCoercive B := ⟨1, one_pos, fun u => by simpa [B] using hA u⟩
  have hE : ∀ v, hB.continuousLinearEquivOfBilin v = A v := fun v => by
    refine ext_inner_right ℝ fun w => ?_
    rw [hB.continuousLinearEquivOfBilin_apply]
    simp [B]
  have : (A : E → E) = hB.continuousLinearEquivOfBilin := by
    funext v; rw [hE]
  rw [this]
  exact hB.continuousLinearEquivOfBilin.bijective

end LaxMilgram

section Main

variable {d : ℕ}

theorem projMean_of_pair_zero {μ : Measure (Torus d)} {f : Torus d → ℝ} (h : pair μ f = 0) :
    projMean μ f = f := by
  funext x
  simp [projMean, h]

/-- `A = I + β K P` on `L²(μ)`. -/
def ALp {g ρ : Torus d → ℝ} {Λ : ℝ} (H : KS g ρ Λ) (β : ℝ) :
    Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ) :=
  ContinuousLinearMap.id ℝ _ + β • TLp H

theorem A_coe {g ρ : Torus d → ℝ} {Λ : ℝ} (H : KS g ρ Λ) (β : ℝ)
    (u : Lp ℝ 2 (withDensityReal ρ)) :
    ⇑(ALp H β u) =ᵐ[withDensityReal ρ]
      fun x => u x + β * Kop g (withDensityReal ρ) (projMean (withDensityReal ρ) ⇑u) x := by
  have e : ALp H β u = u + β • TLp H u := rfl
  rw [e]
  filter_upwards [Lp.coeFn_add u (β • TLp H u), Lp.coeFn_smul β (TLp H u), TLp_coe H u]
    with x h1 h2 h3
  rw [h1]
  simp only [Pi.add_apply]
  rw [h2]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h3]

/-- P13a: the response equation is uniquely solvable for `1 ≤ d` (Lax–Milgram on `L²_0(μ)`,
`K_μ ≥ 0` bounded self-adjoint from the (I1) kernel facts).  This is `HRS.exists_unique_response`
without the restriction `2 ≤ d`, for continuous densities. -/
theorem exists_unique_response_of_one_le (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (hρc : Continuous ρ) (β : ℝ) (hβ : 0 ≤ β)
    (ψ : Torus d → ℝ) (hψ : MemLp ψ 2 (withDensityReal ρ)) :
    ∃ h, IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ h ∧
      ∀ h', IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ h' →
        h' =ᵐ[withDensityReal ρ] h := by
  obtain ⟨Λ, hΛ⟩ := isCompact_univ.exists_bound_of_continuousOn hρc.continuousOn
  have H : KS (periodicRiesz d s) ρ Λ :=
    ⟨MFOneLe.integrable_periodicRiesz hd s hs0 hsd, fun x => periodicRiesz_neg x, hρ,
      fun x => (le_abs_self _).trans (hΛ x (Set.mem_univ x))⟩
  have hP := H.isProb
  set μ := withDensityReal ρ with hμ
  set A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := ALp H β with hA
  have hAbij : Function.Bijective A := by
    refine bijective_of_coercive A fun u => ?_
    have e : A u = u + β • TLp H u := rfl
    rw [e, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_mul_norm]
    have := TLp_inner_nonneg hd s hs0 hsd H hρc u
    nlinarith [mul_nonneg hβ this]
  have hq : MemLp (projMean μ ψ) 2 μ := hψ.sub (memLp_const _)
  obtain ⟨uL, huL⟩ := hAbij.2 (hq.toLp (projMean μ ψ))
  -- the equation
  have hstar : ∀ᵐ x ∂μ, uL x + β * Kop (periodicRiesz d s) μ (projMean μ ⇑uL) x =
      projMean μ ψ x := by
    filter_upwards [A_coe H β uL, MemLp.coeFn_toLp hq] with x h1 h2
    rw [← h1, huL, h2]
  have hpair : pair μ ⇑uL = 0 := by
    have hu1 : Integrable (⇑uL) μ := (Lp.memLp uL).integrable one_le_two
    have hKi : Integrable (Kop (periodicRiesz d s) μ (projMean μ ⇑uL)) μ :=
      ((memLp_Kop H ((Lp.memLp uL).sub (memLp_const _))).1).integrable one_le_two
    have h1 : pair μ (fun x => uL x + β * Kop (periodicRiesz d s) μ (projMean μ ⇑uL) x) =
        pair μ (projMean μ ψ) := integral_congr_ae hstar
    rw [pair_projMean_zero H] at h1
    unfold pair at h1 ⊢
    rw [integral_add hu1 (hKi.const_mul β), integral_const_mul] at h1
    have h2 : ∫ x, Kop (periodicRiesz d s) μ (projMean μ ⇑uL) x ∂μ = 0 :=
      pair_projMean_zero H _
    rw [h2, mul_zero, add_zero] at h1
    exact h1
  refine ⟨⇑uL, ⟨Lp.memLp uL, hpair, ?_⟩, ?_⟩
  · rw [projMean_of_pair_zero hpair] at hstar
    exact hstar
  · rintro h' ⟨hm', hp', he'⟩
    set u' := hm'.toLp h' with hu'
    have hu'h : ⇑u' =ᵐ[μ] h' := MemLp.coeFn_toLp hm'
    have hpu' : pair μ ⇑u' = 0 := (integral_congr_ae hu'h).trans hp'
    have hAu : A u' = hq.toLp (projMean μ ψ) := by
      refine Lp.ext ?_
      filter_upwards [A_coe H β u', MemLp.coeFn_toLp hq, hu'h, he'] with x h1 h2 h3 h4
      rw [h1, h2, projMean_of_pair_zero hpu', Kop_congr hu'h, h3]
      exact h4
    have : u' = uL := hAbij.1 (hAu.trans huL.symm)
    exact hu'h.symm.trans (Filter.EventuallyEq.of_eq (by rw [this]))

end Main

variable {d : ℕ}

/-! ### P13a part 2: susceptibility as a time integral

Route.  For `ψ ∈ C ∩ H^{mStar+4}` the centered frozen semigroup `S(σ)ψ` equals, for `σ ∈ [0,T']`, the
centering of a classical adjoint solution `F(T' - σ)` (`exists_classical_frozen`), so `(σ,x) ↦ S(σ)ψ(x)`
and `(σ,x) ↦ equilibriumGen (S(σ)ψ)(x)` are jointly continuous with pointwise time derivative
`equilibriumGen (S(σ)ψ)` on `(0,T')` (`frozen_path_data`).  Differentiating uniformly in `x` gives a
differentiable path in `C(𝕋^d)` and hence in `L²(μ)` (`hasDerivAt_pL`; no Fourier coefficients needed).
With `R = A⁻¹` on `L²(μ)` (`A = I + βKP`, `exists_inverse`; `R` is self-adjoint and `A (-β⁻¹ … L)`
algebra `equilibriumGen f = -β⁻¹ A (L f)` in `inner_R_eqGen`), the product rule gives
`d/dv ⟨S(v)φ, R S(v)ψ⟩ = -2β⁻¹ ∫ ρβ ∇S(v)φ·∇S(v)ψ` (`hasDerivAt_F_abs`).  For `φ = ψ` the
derivative is `≤ 0` and `F(T) → 0` by the `L²` decay `exists_frozen_l2_decay`, which gives
integrability; the general case is dominated by `(e_φφ + e_ψψ)/2` (`abs_energy_le`), and the
improper FTC (`real_ftc`) yields the identity.  `F(0) = ⟨Pφ, R Pψ⟩ = susceptibilityCov`
(`susceptibilityCov_eq_inner`). -/

section P13aPart2

open MFAdjoint

/-- The classical solution behind the centered frozen semigroup, for continuous `H^{mStar+4}` data. -/
theorem exists_classical_frozen (hd : 1 ≤ d) {s νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ}
    (H : FrozenHyp d s (2 * mStar d + 4) νm νp c₀ Λ₀ β V ρβ) {ψ : Torus d → ℝ}
    (hψc : Continuous ψ) (hψm : MemSobolev (mStar d + 4) ψ) {T' : ℝ} (hT' : 0 < T') :
    ∃ F : ℝ → Torus d → ℝ,
      IsClassicalAdjointSolution (mfData d s H.hs0 H.hsd V β H.hβ) (fun _ => ρβ) T' ψ F ∧
      ∀ σ ∈ Set.Icc (0 : ℝ) T', equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ σ ψ =
        projMean (withDensityReal ρβ) (F (T' - σ)) := by
  have h3 := ClassicalPart.three_le_mStar d
  set m : ℕ := mStar d + 4 with hmdef
  have hH : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρβ := H.mono (by omega)
  set D := mfData d s H.hs0 H.hsd V β H.hβ with hD
  have hA := adjointData_frozen_level m hH 0 T' hT'
  obtain ⟨C, Cs, -, -, hmain⟩ := adjoint_torus_classical hd s H.hs0 H.hsd m (by omega)
    (frozenRegime d s c₀) 1 Λ₀ Λ₀
  have hψm' : MemSobolev (m : ℝ) ψ := by rw [hmdef]; push_cast; exact hψm
  obtain ⟨hF, -⟩ := hmain D 0 T' (fun _ => ρβ) hA T' ⟨hT', le_rfl⟩ ψ hψc hψm'
  refine ⟨_, hF, fun σ hσ => ?_⟩
  have hψ2 : Torus.IsCk 2 ψ := isCk_two_of_memSobolev hψc
    (memSobolev_mono_idx hψm' (by exact_mod_cast (by omega : mStar d + 2 ≤ m)))
  have hKf := ClassicalAux.convKernelFacts hd D
  have hV1 : Torus.IsCk 1 D.V := ET.isCk_mono' (a := 1) (b := m + 3) (by omega) hH.hV
  have hρ1 : Torus.IsCk 1 ρβ := ET.isCk_mono' (a := 1) (b := m + 3) (by omega) hH.hρC
  unfold equilibriumSemigroup
  congr 1
  rcases hσ.1.eq_or_lt with h0 | hpos
  · rw [← h0, MFSemigroup.propagator_zero D hKf hV1 _ hρ1 hψ2, sub_zero]
    exact (hF.terminal).symm
  · rw [MFOneLe.propagator_frozen_eq_of_one_le hd s H.hs0 H.hsd m (by omega) _ 1 Λ₀ Λ₀ D 0 T' ρβ hA
      ⟨hT', le_rfl⟩ hF ⟨hpos, hσ.2⟩]


/-- Path data of the frozen centered semigroup on `[0,T']`: continuity in `x` and jointly, and the
pointwise time derivative `equilibriumGen (S(σ)ψ)` on `(0,T')`. -/
theorem frozen_path_data (hd : 1 ≤ d) {s νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ}
    (H : FrozenHyp d s (2 * mStar d + 4) νm νp c₀ Λ₀ β V ρβ) {ψ : Torus d → ℝ}
    (hψc : Continuous ψ) (hψm : MemSobolev (mStar d + 4) ψ) {T' : ℝ} (hT' : 0 < T') :
    (∀ σ ∈ Set.Icc (0 : ℝ) T',
      Torus.IsCk 2 (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ σ ψ)) ∧
    (∀ σ ∈ Set.Icc (0 : ℝ) T',
      pair (withDensityReal ρβ) (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ σ ψ) = 0) ∧
    Continuous (fun p : Set.Icc (0 : ℝ) T' × Torus d =>
      equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ p.1 ψ p.2) ∧
    Continuous (fun p : Set.Icc (0 : ℝ) T' × Torus d =>
      equilibriumGen d s ρβ β⁻¹ (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ p.1 ψ) p.2) ∧
    ∀ x : Torus d, ∀ σ ∈ Set.Ioo (0 : ℝ) T',
      HasDerivAt (fun σ' => equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ σ' ψ x)
        (equilibriumGen d s ρβ β⁻¹ (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ σ ψ) x) σ := by
  have h3 := ClassicalPart.three_le_mStar d
  obtain ⟨F, hF, hS⟩ := exists_classical_frozen hd H hψc hψm hT'
  set D := mfData d s H.hs0 H.hsd V β H.hβ with hD
  set m : ℕ := mStar d + 4 with hmdef
  have hH : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρβ := H.mono (by omega)
  have hprob : IsProbDensity ρβ := H.thermal.1
  have := MFSemigroup.isProb_withDensityReal hprob
  have hρc : Continuous ρβ := H.cont (by omega)
  have hpos : ∀ x, 0 < ρβ x := fun x => lt_of_lt_of_le H.hc₀ (H.hlow x)
  have hV2 : Torus.IsCk 2 D.V := ET.isCk_mono' (a := 2) (b := m + 3) (by omega) hH.hV
  have hρ2 : Torus.IsCk 2 ρβ := ET.isCk_mono' (a := 2) (b := m + 3) (by omega) hH.hρC
  have hmem : ∀ σ ∈ Set.Icc (0 : ℝ) T', T' - σ ∈ Set.Icc (0 : ℝ) T' := fun σ hσ =>
    ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hsub : ContinuousOn (fun σ : ℝ => T' - σ) (Set.Icc 0 T') :=
    continuousOn_const.sub continuousOn_id
  -- pointwise formulas
  have hSx : ∀ σ ∈ Set.Icc (0 : ℝ) T', ∀ x,
      equilibriumSemigroup D ρβ σ ψ x = F (T' - σ) x - pair (withDensityReal ρβ) (F (T' - σ)) := by
    intro σ hσ x
    rw [hS σ hσ]
    rfl
  have hval : ∀ σ ∈ Set.Icc (0 : ℝ) T', ∀ x,
      equilibriumGen d s ρβ β⁻¹ (equilibriumSemigroup D ρβ σ ψ) x =
        backwardGenerator D ρβ (F (T' - σ)) x -
          pair (withDensityReal ρβ) (backwardGenerator D ρβ (F (T' - σ))) := by
    intro σ hσ x
    have hf2 : Torus.IsCk 2 (F (T' - σ)) := hF.c2 _ (hmem σ hσ)
    have hord := congrFun (MFOneLe.operator_order_core_of_one_le hd D rfl β H.hβ rfl hV2 ρβ H.thermal
      hρ2 hpos (F (T' - σ)) hf2) x
    rw [hS σ hσ]
    unfold equilibriumGen
    rw [MFSemigroup.lop_projMean]
    exact hord.symm
  have hsubT : Continuous fun p : Set.Icc (0 : ℝ) T' × Torus d =>
      ((⟨T' - p.1.1, hmem p.1.1 p.1.2⟩ : Set.Icc (0 : ℝ) T'), p.2) :=
    Continuous.prodMk (Continuous.subtype_mk (continuous_const.sub (continuous_subtype_val.comp
      continuous_fst)) _) continuous_snd
  have hsubI : Continuous fun σ : Set.Icc (0 : ℝ) T' => (⟨T' - σ.1, hmem σ.1 σ.2⟩ : Set.Icc (0 : ℝ) T') :=
    Continuous.subtype_mk (continuous_const.sub continuous_subtype_val) _
  have hpairF : Continuous fun p : Set.Icc (0 : ℝ) T' × Torus d =>
      pair (withDensityReal ρβ) (F (T' - p.1.1)) :=
    ((continuousOn_iff_continuous_domRestrict.1 (MFSemigroup.continuousOn_pair_F hprob hρc hF)).comp
      (hsubI.comp continuous_fst))
  have hpairB : Continuous fun p : Set.Icc (0 : ℝ) T' × Torus d =>
      pair (withDensityReal ρβ) (backwardGenerator D ρβ (F (T' - p.1.1))) := by
    have hB := MFSemigroup.continuousOn_pair_bg hprob hρc hF
    have hB' : Continuous fun r : Set.Icc (0 : ℝ) T' =>
        pair (withDensityReal ρβ) (backwardGenerator D ρβ (F r.1)) :=
      continuousOn_iff_continuous_domRestrict.1 hB
    have := hB'.comp (hsubI.comp continuous_fst : Continuous fun p : Set.Icc (0 : ℝ) T' × Torus d =>
      (⟨T' - p.1.1, hmem p.1.1 p.1.2⟩ : Set.Icc (0 : ℝ) T'))
    exact this
  have hcF : Continuous fun p : Set.Icc (0 : ℝ) T' × Torus d => F (T' - p.1.1) p.2 := by
    have := (MFSemigroup.continuous_F hF).comp hsubT
    exact this
  have hcB : Continuous fun p : Set.Icc (0 : ℝ) T' × Torus d =>
      backwardGenerator D ρβ (F (T' - p.1.1)) p.2 := by
    have h1 := hF.cont_time_deriv
    have := h1.comp hsubT
    exact this
  refine ⟨fun σ hσ => ?_, fun σ _ => MFSemigroup.pair_projMean _ _, ?_, ?_, ?_⟩
  · have hf2 : Torus.IsCk 2 (F (T' - σ)) := hF.c2 _ (hmem σ hσ)
    have : Torus.IsCk 2 (fun x => F (T' - σ) x - pair (withDensityReal ρβ) (F (T' - σ))) :=
      hf2.sub contDiff_const
    rw [hS σ hσ]
    exact this
  · refine (hcF.sub hpairF).congr fun p => ?_
    exact (hSx p.1.1 p.1.2 p.2).symm
  · refine (hcB.sub hpairB).congr fun p => ?_
    exact (hval p.1.1 p.1.2 p.2).symm
  · intro x σ hσ
    have hd := (MFSemigroup.hasDerivAt_F hF x hσ).sub (MFSemigroup.hasDerivAt_pair_F hprob hρc hF hσ)
    have hσ' : σ ∈ Set.Icc (0 : ℝ) T' := Set.Ioo_subset_Icc_self hσ
    have hev : (fun σ' => equilibriumSemigroup D ρβ σ' ψ x) =ᶠ[𝓝 σ]
        fun σ' => F (T' - σ') x - pair (withDensityReal ρβ) (F (T' - σ')) := by
      filter_upwards [Ioo_mem_nhds hσ.1 hσ.2] with σ' hσ''
      exact hSx σ' (Set.Ioo_subset_Icc_self hσ'') x
    exact (hd.congr_of_eventuallyEq hev).congr_deriv (hval σ hσ' x).symm


/-! ### Differentiable paths in `C(𝕋^d)` and `L²(μ)` -/

section Path

open Classical in
/-- The path `v ↦ G v` of functions, as a path in `C(𝕋^d)` (`0` where `G v` is not continuous). -/
def pc (G : ℝ → Torus d → ℝ) (v : ℝ) : C(Torus d, ℝ) :=
  if h : Continuous (G v) then ⟨G v, h⟩ else 0

theorem pc_apply {G : ℝ → Torus d → ℝ} {v : ℝ} (h : Continuous (G v)) (x : Torus d) :
    pc G v x = G v x := by
  simp [pc, h]

theorem continuousOn_pc {a b : ℝ} {G : ℝ → Torus d → ℝ} (hc : ∀ v ∈ Set.Icc a b, Continuous (G v))
    (hG : Continuous fun p : Set.Icc a b × Torus d => G p.1 p.2) :
    ContinuousOn (pc G) (Set.Icc a b) := by
  have h1 := (ContinuousMap.curry (⟨fun p : Set.Icc a b × Torus d => G p.1 p.2, hG⟩ :
    C(Set.Icc a b × Torus d, ℝ))).continuous
  refine continuousOn_iff_continuous_domRestrict.2 (h1.congr fun v => ?_)
  ext x
  simp [pc_apply (hc v.1 v.2)]



theorem hasDerivAt_pc {a b : ℝ} {G G' : ℝ → Torus d → ℝ}
    (hc : ∀ v ∈ Set.Icc a b, Continuous (G v)) (hc' : ∀ v ∈ Set.Icc a b, Continuous (G' v))
    (hG' : Continuous fun p : Set.Icc a b × Torus d => G' p.1 p.2)
    (hder : ∀ x, ∀ v ∈ Set.Ioo a b, HasDerivAt (fun v => G v x) (G' v x) v)
    {v0 : ℝ} (hv0 : v0 ∈ Set.Ioo a b) :
    HasDerivAt (pc G) (pc G' v0) v0 := by
  have hcont : ContinuousOn (pc G') (Set.Icc a b) := continuousOn_pc hc' hG'
  have hat : ContinuousAt (pc G') v0 :=
    hcont.continuousAt (Icc_mem_nhds hv0.1 hv0.2)
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hat ε hε
  set δ' := min δ (min (v0 - a) (b - v0)) with hδdef
  have hδ'pos : 0 < δ' := lt_min hδ (lt_min (by linarith [hv0.1]) (by linarith [hv0.2]))
  have hball : Metric.ball v0 δ' ⊆ Set.Ioo a b := by
    intro w hw
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hw
    have h1 : δ' ≤ v0 - a := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : δ' ≤ b - v0 := (min_le_right _ _).trans (min_le_right _ _)
    exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
  filter_upwards [Metric.ball_mem_nhds v0 hδ'pos] with v hv
  have hvI : ∀ w ∈ Metric.ball v0 δ', w ∈ Set.Icc a b := fun w hw => Set.Ioo_subset_Icc_self (hball hw)
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
  have hf : ∀ w ∈ Metric.ball v0 δ', HasDerivWithinAt (fun w => G w x - (w - v0) * G' v0 x)
      (G' w x - G' v0 x) (Metric.ball v0 δ') w := by
    intro w hw
    have h1 := (hder x w (hball hw)).sub (((hasDerivAt_id w).sub_const v0).mul_const (G' v0 x))
    exact (h1.congr_deriv (by simp)).hasDerivWithinAt
  have hb : ∀ w ∈ Metric.ball v0 δ', ‖G' w x - G' v0 x‖ ≤ ε := by
    intro w hw
    have hw1 : dist w v0 < δ := lt_of_lt_of_le (Metric.mem_ball.1 hw) (min_le_left _ _)
    have h2 := hδ' hw1
    have h3 : ‖pc G' w x - pc G' v0 x‖ ≤ ‖pc G' w - pc G' v0‖ := by
      have := ContinuousMap.norm_coe_le_norm (pc G' w - pc G' v0) x
      simpa using this
    rw [pc_apply (hc' w (hvI w hw)), pc_apply (hc' v0 (hvI v0 (Metric.mem_ball_self hδ'pos)))] at h3
    rw [dist_eq_norm] at h2
    exact (h3.trans h2.le)
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf hb (convex_ball v0 δ')
    (Metric.mem_ball_self hδ'pos) hv
  have e : (pc G v - pc G v0 - (v - v0) • pc G' v0) x =
      (G v x - (v - v0) * G' v0 x) - (G v0 x - (v0 - v0) * G' v0 x) := by
    rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      pc_apply (hc v (hvI v hv)), pc_apply (hc v0 (hvI v0 (Metric.mem_ball_self hδ'pos))),
      pc_apply (hc' v0 (hvI v0 (Metric.mem_ball_self hδ'pos)))]
    simp only [smul_eq_mul, sub_self, zero_mul, sub_zero]
    ring
  rw [e]
  exact key



/-- The path `v ↦ G v` of continuous functions as a path in `L²(μ)`. -/
def pL (μ : Measure (Torus d)) [IsFiniteMeasure μ] (G : ℝ → Torus d → ℝ) (v : ℝ) :
    Lp ℝ 2 μ :=
  ContinuousMap.toLp (E := ℝ) 2 μ ℝ (pc G v)

theorem pL_ae {μ : Measure (Torus d)} [IsFiniteMeasure μ] {G : ℝ → Torus d → ℝ} {v : ℝ}
    (h : Continuous (G v)) : ⇑(pL μ G v) =ᵐ[μ] G v := by
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℝ) (p := 2) (𝕜 := ℝ) μ (pc G v)] with x hx
  rw [pL, hx, pc_apply h]

theorem continuousOn_pL (μ : Measure (Torus d)) [IsFiniteMeasure μ] {a b : ℝ}
    {G : ℝ → Torus d → ℝ} (hc : ∀ v ∈ Set.Icc a b, Continuous (G v))
    (hG : Continuous fun p : Set.Icc a b × Torus d => G p.1 p.2) :
    ContinuousOn (pL μ G) (Set.Icc a b) :=
  (ContinuousMap.toLp (E := ℝ) 2 μ ℝ).continuous.comp_continuousOn (continuousOn_pc hc hG)

theorem hasDerivAt_pL (μ : Measure (Torus d)) [IsFiniteMeasure μ] {a b : ℝ}
    {G G' : ℝ → Torus d → ℝ}
    (hc : ∀ v ∈ Set.Icc a b, Continuous (G v)) (hc' : ∀ v ∈ Set.Icc a b, Continuous (G' v))
    (hG' : Continuous fun p : Set.Icc a b × Torus d => G' p.1 p.2)
    (hder : ∀ x, ∀ v ∈ Set.Ioo a b, HasDerivAt (fun v => G v x) (G' v x) v)
    {v0 : ℝ} (hv0 : v0 ∈ Set.Ioo a b) :
    HasDerivAt (pL μ G) (pL μ G' v0) v0 :=
  (ContinuousMap.toLp (E := ℝ) 2 μ ℝ).hasFDerivAt.comp_hasDerivAt v0 (hasDerivAt_pc hc hc' hG' hder hv0)

end Path


/-! ### The inverse of `A = I + βKP` on `L²(μ)` -/

section Alg

variable {ρ : Torus d → ℝ} {Λ : ℝ}

theorem ALp_coercive (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (H : KS (periodicRiesz d s) ρ Λ) (hρc : Continuous ρ) (β : ℝ) (hβ : 0 ≤ β)
    (u : Lp ℝ 2 (withDensityReal ρ)) : ‖u‖ * ‖u‖ ≤ inner ℝ (ALp H β u) u := by
  have e : ALp H β u = u + β • TLp H u := rfl
  rw [e, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_mul_norm]
  have := TLp_inner_nonneg hd s hs0 hsd H hρc u
  nlinarith [mul_nonneg hβ this]

theorem ALp_symm (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (H : KS (periodicRiesz d s) ρ Λ) (hρc : Continuous ρ) (β : ℝ)
    (x y : Lp ℝ 2 (withDensityReal ρ)) : inner ℝ (ALp H β x) y = inner ℝ x (ALp H β y) := by
  have e : ∀ u, ALp H β u = u + β • TLp H u := fun u => rfl
  rw [e, e, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    TLp_symm hd s hs0 hsd H hρc]

theorem exists_inverse (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (H : KS (periodicRiesz d s) ρ Λ) (hρc : Continuous ρ) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ R : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ),
      (∀ x, R (ALp H β x) = x) ∧ (∀ y, ALp H β (R y) = y) ∧
      (∀ x y, inner ℝ (R x) y = inner ℝ x (R y)) ∧ (∀ y, 0 ≤ inner ℝ (R y) y) := by
  have hco := ALp_coercive hd s hs0 hsd H hρc β hβ
  have hbij : Function.Bijective (ALp H β) := bijective_of_coercive _ hco
  let E := ContinuousLinearEquiv.ofBijective (ALp H β)
    (LinearMap.ker_eq_bot.2 hbij.1) (LinearMap.range_eq_top.2 hbij.2)
  have hE : ∀ x, E x = ALp H β x := fun x => rfl
  refine ⟨(E.symm : _ →L[ℝ] _), fun x => ?_, fun y => ?_, fun x y => ?_, fun y => ?_⟩
  · have := E.symm_apply_apply x
    rwa [hE] at this
  · have := E.apply_symm_apply y
    rwa [hE] at this
  · have h1 : ALp H β (E.symm y) = y := by
      have := E.apply_symm_apply y
      rwa [hE] at this
    have h2 : ALp H β (E.symm x) = x := by
      have := E.apply_symm_apply x
      rwa [hE] at this
    calc inner ℝ (E.symm x) y = inner ℝ (E.symm x) (ALp H β (E.symm y)) := by rw [h1]
      _ = inner ℝ (ALp H β (E.symm x)) (E.symm y) := (ALp_symm hd s hs0 hsd H hρc β _ _).symm
      _ = inner ℝ x (E.symm y) := by rw [h2]
  · have h1 : ALp H β (E.symm y) = y := by
      have := E.apply_symm_apply y
      rwa [hE] at this
    have := hco (E.symm y)
    rw [h1] at this
    have h3 : 0 ≤ ‖E.symm y‖ * ‖E.symm y‖ := mul_self_nonneg _
    have h4 : inner ℝ y (E.symm y) = inner ℝ (E.symm y) y := real_inner_comm _ _
    simp only [ContinuousLinearEquiv.coe_coe]
    linarith


theorem continuous_lop {ρ f : Torus d → ℝ} (hρ1 : Torus.IsCk 1 ρ) (hpos : ∀ x, 0 < ρ x)
    (hf : Torus.IsCk 2 f) : Continuous (Lop ρ f) := by
  have hρc : Continuous ρ := MFAux.continuous_of_isCk hρ1
  have hH : ∀ j, Torus.IsCk 1 (fun y => ρ y * Torus.partialDeriv j f y) :=
    fun j => MFAux.isCk_mul_partialDeriv ρ f hρ1 hf j
  have hDc : Continuous fun y => ∑ j, Torus.partialDeriv j
      (fun y' => ρ y' * Torus.partialDeriv j f y') y :=
    continuous_finsetSum _ fun j _ => continuous_partialDeriv j _ (hH j)
  have : Lop ρ f = fun x => -(ρ x)⁻¹ * ∑ j, Torus.partialDeriv j
      (fun y' => ρ y' * Torus.partialDeriv j f y') x := by
    funext x
    unfold Lop
    rw [MFAux.div_smul_grad ρ f hρ1 hf x]
  rw [this]
  exact ((hρc.inv₀ fun x => (hpos x).ne').neg).mul hDc

theorem l2Inner_congr_ae {μ : Measure (Torus d)} {a a' b b' : Torus d → ℝ} (ha : a =ᵐ[μ] a')
    (hb : b =ᵐ[μ] b') : l2Inner μ a b = l2Inner μ a' b' := by
  unfold l2Inner
  refine integral_congr_ae ?_
  filter_upwards [ha, hb] with x h1 h2
  rw [h1, h2]

theorem eqGen_ae (s : ℝ) (H : KS (periodicRiesz d s) ρ Λ) (β : ℝ) (hβ : 0 < β)
    (hρ1 : Torus.IsCk 1 ρ) {f : Torus d → ℝ} (hf : Torus.IsCk 2 f)
    (q : Lp ℝ 2 (withDensityReal ρ)) (hq : ⇑q =ᵐ[withDensityReal ρ] Lop ρ f) :
    ⇑(β⁻¹ • ALp H β q) =ᵐ[withDensityReal ρ]
      fun x => -(equilibriumGen d s ρ β⁻¹ f x) := by
  have hP := H.isProb
  have hp0 : pair (withDensityReal ρ) ⇑q = 0 :=
    (integral_congr_ae hq).trans (MFAdjoint.pair_lop H.prob hρ1 hf)
  have hproj : projMean (withDensityReal ρ) ⇑q =ᵐ[withDensityReal ρ] Lop ρ f := by
    filter_upwards [hq] with x hx
    simp only [projMean, hx, hp0, sub_zero]
  have hK : Kop (periodicRiesz d s) (withDensityReal ρ) (projMean (withDensityReal ρ) ⇑q) =
      Kop (periodicRiesz d s) (withDensityReal ρ) (Lop ρ f) := Kop_congr hproj
  filter_upwards [Lp.coeFn_smul β⁻¹ (ALp H β q), A_coe H β q, hq] with x h1 h2 h3
  rw [h1]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h2]
  simp only [equilibriumGen]
  rw [hK, h3]
  field_simp


theorem inner_R_eqGen (s : ℝ) (H : KS (periodicRiesz d s) ρ Λ) (β : ℝ) (hβ : 0 < β)
    (hρ1 : Torus.IsCk 1 ρ) (hpos : ∀ x, 0 < ρ x)
    (R : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ))
    (hRA : ∀ x, R (ALp H β x) = x) {f g : Torus d → ℝ} (hf : Torus.IsCk 2 f) (hg : Torus.IsCk 1 g)
    (u' y : Lp ℝ 2 (withDensityReal ρ))
    (hu' : ⇑u' =ᵐ[withDensityReal ρ] equilibriumGen d s ρ β⁻¹ f)
    (hy : ⇑y =ᵐ[withDensityReal ρ] g) :
    inner ℝ y (R u') = -β⁻¹ * ∫ x, ρ x * inner ℝ (Torus.grad f x) (Torus.grad g x) := by
  have hP := H.isProb
  have hLc := continuous_lop hρ1 hpos hf
  have hmem : MemLp (Lop ρ f) 2 (withDensityReal ρ) :=
    hLc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set q : Lp ℝ 2 (withDensityReal ρ) := hmem.toLp (Lop ρ f) with hqdef
  have hq : ⇑q =ᵐ[withDensityReal ρ] Lop ρ f := MemLp.coeFn_toLp hmem
  have h1 := eqGen_ae s H β hβ hρ1 hf q hq
  have hu : u' = -(β⁻¹ • ALp H β q) := by
    refine Lp.ext ?_
    filter_upwards [hu', h1, Lp.coeFn_neg (β⁻¹ • ALp H β q)] with x a b c
    rw [c, a]
    simp only [Pi.neg_apply, b, neg_neg]
  have hRu : R u' = -(β⁻¹ • q) := by
    rw [hu, map_neg, map_smul, hRA]
  rw [hRu, inner_neg_right, real_inner_smul_right, innerLp_eq_l2Inner]
  have e1 : l2Inner (withDensityReal ρ) ⇑y ⇑q = l2Inner (withDensityReal ρ) g (Lop ρ f) :=
    l2Inner_congr_ae hy hq
  rw [e1, MFAdjoint.l2Inner_comm', MFAdjoint.l2Inner_lop_eq ρ H.prob hρ1 f g hf hg]
  ring


end Alg

/-! ### The derivative of `v ↦ ⟨S(v)φ, R S(v)ψ⟩` -/

section Deriv

variable {s νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ} {ρ : Torus d → ℝ} {Λ : ℝ}

theorem KS_of_frozen (hd : 1 ≤ d) (H : FrozenHyp d s (2 * mStar d + 4) νm νp c₀ Λ₀ β V ρβ) :
    KS (periodicRiesz d s) ρβ Λ₀ :=
  ⟨MFOneLe.integrable_periodicRiesz hd s H.hs0 H.hsd, periodicRiesz_neg, H.thermal.1, H.le_Lam⟩

theorem hasDerivAt_F_abs (s : ℝ) (hKS : KS (periodicRiesz d s) ρ Λ) [IsFiniteMeasure (withDensityReal ρ)]
    (β : ℝ) (hβ : 0 < β)
    (hρ1 : Torus.IsCk 1 ρ) (hpos : ∀ x, 0 < ρ x)
    (R : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ))
    (hRA : ∀ x, R (ALp hKS β x) = x) (hRs : ∀ x y, inner ℝ (R x) y = inner ℝ x (R y))
    {a b : ℝ} (Sφ Sψ : ℝ → Torus d → ℝ)
    (c2φ : ∀ v ∈ Set.Icc a b, Torus.IsCk 2 (Sφ v))
    (jGφ : Continuous fun p : Set.Icc a b × Torus d => equilibriumGen d s ρ β⁻¹ (Sφ p.1) p.2)
    (dφ : ∀ x, ∀ v ∈ Set.Ioo a b, HasDerivAt (fun v => Sφ v x)
      (equilibriumGen d s ρ β⁻¹ (Sφ v) x) v)
    (c2ψ : ∀ v ∈ Set.Icc a b, Torus.IsCk 2 (Sψ v))
    (jGψ : Continuous fun p : Set.Icc a b × Torus d => equilibriumGen d s ρ β⁻¹ (Sψ p.1) p.2)
    (dψ : ∀ x, ∀ v ∈ Set.Ioo a b, HasDerivAt (fun v => Sψ v x)
      (equilibriumGen d s ρ β⁻¹ (Sψ v) x) v)
    {v0 : ℝ} (hv0 : v0 ∈ Set.Ioo a b) :
    HasDerivAt (fun v => inner ℝ (pL (withDensityReal ρ) Sφ v)
        (R (pL (withDensityReal ρ) Sψ v)))
      (-2 * β⁻¹ * ∫ x, inner ℝ (Torus.grad (Sφ v0) x) (Torus.grad (Sψ v0) x) * ρ x) v0 := by
  have hP := hKS.isProb
  have hv0' : v0 ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hv0
  have cont1 : ∀ {f : Torus d → ℝ}, Torus.IsCk 2 f → Continuous f := fun hf =>
    MFAux.continuous_of_isCk (hf.of_le (by norm_num))
  have cs : ∀ {G : ℝ → Torus d → ℝ}, (Continuous fun p : Set.Icc a b × Torus d => G p.1 p.2) →
      ∀ v ∈ Set.Icc a b, Continuous (G v) := fun h v hv =>
    h.comp (continuous_const.prodMk continuous_id (f := fun x : Torus d => (⟨v, hv⟩ : Set.Icc a b)))
  have h1 := hasDerivAt_pL (withDensityReal ρ) (G := Sφ) (G' := fun v => equilibriumGen d s ρ β⁻¹ (Sφ v))
    (fun v hv => cont1 (c2φ v hv)) (cs (G := fun v => equilibriumGen d s ρ β⁻¹ (Sφ v)) jGφ) jGφ dφ hv0
  have h2 := hasDerivAt_pL (withDensityReal ρ) (G := Sψ) (G' := fun v => equilibriumGen d s ρ β⁻¹ (Sψ v))
    (fun v hv => cont1 (c2ψ v hv)) (cs (G := fun v => equilibriumGen d s ρ β⁻¹ (Sψ v)) jGψ) jGψ dψ hv0
  have h2' := R.hasFDerivAt.comp_hasDerivAt v0 h2
  have h4 := h1.inner ℝ h2'
  have eφ : ⇑(pL (withDensityReal ρ) Sφ v0) =ᵐ[withDensityReal ρ] Sφ v0 := pL_ae (cont1 (c2φ v0 hv0'))
  have eψ : ⇑(pL (withDensityReal ρ) Sψ v0) =ᵐ[withDensityReal ρ] Sψ v0 := pL_ae (cont1 (c2ψ v0 hv0'))
  have eφ' : ⇑(pL (withDensityReal ρ) (fun v => equilibriumGen d s ρ β⁻¹ (Sφ v)) v0) =ᵐ[withDensityReal ρ]
      equilibriumGen d s ρ β⁻¹ (Sφ v0) := pL_ae (cs (G := fun v => equilibriumGen d s ρ β⁻¹ (Sφ v)) jGφ v0 hv0')
  have eψ' : ⇑(pL (withDensityReal ρ) (fun v => equilibriumGen d s ρ β⁻¹ (Sψ v)) v0) =ᵐ[withDensityReal ρ]
      equilibriumGen d s ρ β⁻¹ (Sψ v0) := pL_ae (cs (G := fun v => equilibriumGen d s ρ β⁻¹ (Sψ v)) jGψ v0 hv0')
  have hφ1 : Torus.IsCk 1 (Sφ v0) := (c2φ v0 hv0').of_le (by norm_num)
  have hψ1 : Torus.IsCk 1 (Sψ v0) := (c2ψ v0 hv0').of_le (by norm_num)
  have k1 := inner_R_eqGen s hKS β hβ hρ1 hpos R hRA (c2ψ v0 hv0') hφ1
    (pL (withDensityReal ρ) (fun v => equilibriumGen d s ρ β⁻¹ (Sψ v)) v0)
    (pL (withDensityReal ρ) Sφ v0) eψ' eφ
  have k2 := inner_R_eqGen s hKS β hβ hρ1 hpos R hRA (c2φ v0 hv0') hψ1
    (pL (withDensityReal ρ) (fun v => equilibriumGen d s ρ β⁻¹ (Sφ v)) v0)
    (pL (withDensityReal ρ) Sψ v0) eφ' eψ
  have e2 : inner ℝ (pL (withDensityReal ρ) (fun v => equilibriumGen d s ρ β⁻¹ (Sφ v)) v0)
      (R (pL (withDensityReal ρ) Sψ v0)) =
      -β⁻¹ * ∫ x, ρ x * inner ℝ (Torus.grad (Sφ v0) x) (Torus.grad (Sψ v0) x) := by
    rw [← hRs, real_inner_comm]
    exact k2
  have e1 : ∫ x, ρ x * inner ℝ (Torus.grad (Sψ v0) x) (Torus.grad (Sφ v0) x) =
      ∫ x, ρ x * inner ℝ (Torus.grad (Sφ v0) x) (Torus.grad (Sψ v0) x) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [real_inner_comm]
  have e3 : ∫ x, inner ℝ (Torus.grad (Sφ v0) x) (Torus.grad (Sψ v0) x) * ρ x =
      ∫ x, ρ x * inner ℝ (Torus.grad (Sφ v0) x) (Torus.grad (Sψ v0) x) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [mul_comm]
  rw [e1] at k1
  refine h4.congr_deriv ?_
  have hc : ((⇑R ∘ pL (withDensityReal ρ) Sψ) v0) = R (pL (withDensityReal ρ) Sψ v0) := rfl
  rw [hc, k1, e2, e3]
  ring


end Deriv

/-! ### Improper fundamental theorem of calculus -/

section RealFTC

theorem real_diag {F e : ℝ → ℝ} {c : ℝ} (hc : 0 < c) (hFc : ContinuousOn F (Set.Ici 0))
    (hFd : ∀ v, 0 < v → HasDerivAt F (-(c * e v)) v) (he : ∀ v, 0 < v → 0 ≤ e v)
    (hF : Tendsto F atTop (𝓝 0)) : IntegrableOn e (Set.Ioi 0) := by
  have h := integrableOn_Ioi_deriv_of_nonpos (a := 0) (g := F) (g' := fun v => -(c * e v)) (l := 0)
    (hFc 0 Set.self_mem_Ici) (fun v hv => hFd v hv) (fun v hv => by
      have := he v hv
      nlinarith) hF
  have h2 : IntegrableOn (fun v => -(1 / c) * -(c * e v)) (Set.Ioi 0) := h.const_mul (-(1 / c))
  refine IntegrableOn.congr_fun h2 (fun v _ => ?_) measurableSet_Ioi
  field_simp

theorem real_ftc {F e g : ℝ → ℝ} {c : ℝ} (hc : 0 < c) (hFc : ContinuousOn F (Set.Ici 0))
    (hFd : ∀ v, 0 < v → HasDerivAt F (-(c * e v)) v) (hF : Tendsto F atTop (𝓝 0))
    (hg : IntegrableOn g (Set.Ioi 0)) (hdom : ∀ v, 0 < v → |e v| ≤ g v) :
    IntegrableOn e (Set.Ici 0) ∧ F 0 = c * ∫ v in Set.Ici 0, e v := by
  have hmeas : AEStronglyMeasurable e (volume.restrict (Set.Ioi 0)) := by
    have : AEStronglyMeasurable (fun v => -(deriv F v) / c) (volume.restrict (Set.Ioi 0)) :=
      ((measurable_deriv F).neg.div_const c).aestronglyMeasurable
    refine this.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [(hFd v hv).deriv]
    field_simp
  have hint : IntegrableOn e (Set.Ioi 0) := by
    refine Integrable.mono' hg hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [Real.norm_eq_abs]
    exact hdom v hv
  have hint' : IntegrableOn (fun v => -(c * e v)) (Set.Ioi 0) := (hint.const_mul c).neg
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0) (f := F) (f' := fun v => -(c * e v))
    (m := 0) (hFc 0 Set.self_mem_Ici) (fun v hv => hFd v hv) hint' hF
  refine ⟨(integrableOn_Ici_iff_integrableOn_Ioi (hb := enorm_ne_top)).2 hint, ?_⟩
  rw [integral_Ici_eq_integral_Ioi]
  have : ∫ v in Set.Ioi (0 : ℝ), -(c * e v) = -(c * ∫ v in Set.Ioi (0 : ℝ), e v) := by
    rw [integral_neg, integral_const_mul]
  rw [this] at hI
  linarith

end RealFTC

/-! ### The energy integrand -/

section Energy

theorem continuous_inner_grad {a b : Torus d → ℝ} (ha : Torus.IsCk 1 a) (hb : Torus.IsCk 1 b) :
    Continuous fun x => inner ℝ (Torus.grad a x) (Torus.grad b x) := by
  simp_rw [MFApriori.inner_grad_grad]
  exact continuous_finsetSum _ fun j _ => (continuous_partialDeriv j a ha).mul
    (continuous_partialDeriv j b hb)

theorem integrable_energy {ρ a b : Torus d → ℝ} (hρc : Continuous ρ) (ha : Torus.IsCk 1 a)
    (hb : Torus.IsCk 1 b) :
    Integrable fun x => inner ℝ (Torus.grad a x) (Torus.grad b x) * ρ x :=
  ((continuous_inner_grad ha hb).mul hρc).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem energy_nonneg {ρ a : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) :
    0 ≤ ∫ x, inner ℝ (Torus.grad a x) (Torus.grad a x) * ρ x :=
  integral_nonneg fun x => mul_nonneg real_inner_self_nonneg (hρ0 x)

theorem abs_energy_le {ρ a b : Torus d → ℝ} (hρc : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (ha : Torus.IsCk 1 a) (hb : Torus.IsCk 1 b) :
    |∫ x, inner ℝ (Torus.grad a x) (Torus.grad b x) * ρ x| ≤
      ((∫ x, inner ℝ (Torus.grad a x) (Torus.grad a x) * ρ x) +
        ∫ x, inner ℝ (Torus.grad b x) (Torus.grad b x) * ρ x) / 2 := by
  have iab := integrable_energy hρc ha hb
  have iaa := integrable_energy hρc ha ha
  have ibb := integrable_energy hρc hb hb
  have hsum : ∫ x, (inner ℝ (Torus.grad a x) (Torus.grad a x) * ρ x +
      inner ℝ (Torus.grad b x) (Torus.grad b x) * ρ x) / 2 =
      ((∫ x, inner ℝ (Torus.grad a x) (Torus.grad a x) * ρ x) +
        ∫ x, inner ℝ (Torus.grad b x) (Torus.grad b x) * ρ x) / 2 := by
    rw [integral_div, integral_add iaa ibb]
  rw [abs_le]
  constructor
  · have h1 : ∫ x, -((inner ℝ (Torus.grad a x) (Torus.grad a x) * ρ x +
        inner ℝ (Torus.grad b x) (Torus.grad b x) * ρ x) / 2) ≤
        ∫ x, inner ℝ (Torus.grad a x) (Torus.grad b x) * ρ x := by
      refine integral_mono ((iaa.add ibb).div_const 2).neg iab fun x => ?_
      have h := real_inner_self_nonneg (x := Torus.grad a x + Torus.grad b x)
      rw [inner_add_left, inner_add_right, inner_add_right, real_inner_comm (Torus.grad a x)
        (Torus.grad b x)] at h
      have := mul_nonneg h (hρ0 x)
      nlinarith
    rw [integral_neg, hsum] at h1
    linarith
  · have h1 : ∫ x, inner ℝ (Torus.grad a x) (Torus.grad b x) * ρ x ≤
        ∫ x, (inner ℝ (Torus.grad a x) (Torus.grad a x) * ρ x +
        inner ℝ (Torus.grad b x) (Torus.grad b x) * ρ x) / 2 := by
      refine integral_mono iab ((iaa.add ibb).div_const 2) fun x => ?_
      have h := real_inner_self_nonneg (x := Torus.grad a x - Torus.grad b x)
      rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm (Torus.grad a x)
        (Torus.grad b x)] at h
      have := mul_nonneg h (hρ0 x)
      nlinarith
    rw [hsum] at h1
    exact h1

end Energy

theorem norm_pL_le {ρ : Torus d → ℝ} {Λ : ℝ} (hprob : IsProbDensity ρ) (hρc : Continuous ρ) (hΛ : ∀ x, ρ x ≤ Λ)
    [IsFiniteMeasure (withDensityReal ρ)] {G : ℝ → Torus d → ℝ} {v : ℝ} (hc : Continuous (G v)) :
    ‖pL (withDensityReal ρ) G v‖ ≤ Real.sqrt Λ * sobolevNorm 0 (G v) := by
  set u := pL (withDensityReal ρ) G v with hu
  have e1 : ‖u‖ * ‖u‖ = l2Inner (withDensityReal ρ) (G v) (G v) := by
    rw [← real_inner_self_eq_norm_mul_norm, innerLp_eq_l2Inner]
    exact l2Inner_congr_ae (pL_ae hc) (pL_ae hc)
  rw [MFAdjoint.l2Inner_mu hprob] at e1
  have hI : 0 ≤ ∫ x, G v x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have e2 : ∫ x, ρ x * (G v x * G v x) ≤ Λ * ∫ x, G v x ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono ?_ ?_ fun x => ?_
    · exact (hρc.mul (hc.mul hc)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · exact ((hc.pow 2).const_mul Λ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · have : 0 ≤ G v x * G v x := mul_self_nonneg _
      nlinarith [hΛ x]
  rw [MFAdjoint.sobolevNorm_zero_eq hc]
  have e3 : ‖u‖ ^ 2 ≤ Λ * ∫ x, G v x ^ 2 := by rw [sq]; linarith
  calc ‖u‖ = Real.sqrt (‖u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (Λ * ∫ x, G v x ^ 2) := Real.sqrt_le_sqrt e3
    _ = Real.sqrt Λ * Real.sqrt (∫ x, G v x ^ 2) := Real.sqrt_mul' _ hI

/-! ### Identification of the response and of `susceptibilityCov` -/

section Ident

variable {ρ : Torus d → ℝ} {Λ : ℝ}

theorem isResponse_of_A {g : Torus d → ℝ} (H : KS g ρ Λ) (β : ℝ) (ψ : Torus d → ℝ)
    (u : Lp ℝ 2 (withDensityReal ρ))
    (hu : ⇑(ALp H β u) =ᵐ[withDensityReal ρ] projMean (withDensityReal ρ) ψ) :
    IsResponse g (withDensityReal ρ) β ψ ⇑u := by
  have hP := H.isProb
  have hstar : ∀ᵐ x ∂(withDensityReal ρ), u x + β * Kop g (withDensityReal ρ) (projMean (withDensityReal ρ) ⇑u) x = projMean (withDensityReal ρ) ψ x := by
    filter_upwards [A_coe H β u, hu] with x h1 h2
    rw [← h1, h2]
  have hpair : pair (withDensityReal ρ) ⇑u = 0 := by
    have hu1 : Integrable (⇑u) (withDensityReal ρ) := (Lp.memLp u).integrable one_le_two
    have hKi : Integrable (Kop g (withDensityReal ρ) (projMean (withDensityReal ρ) ⇑u)) (withDensityReal ρ) :=
      ((memLp_Kop H ((Lp.memLp u).sub (memLp_const _))).1).integrable one_le_two
    have h1 : pair (withDensityReal ρ) (fun x => u x + β * Kop g (withDensityReal ρ) (projMean (withDensityReal ρ) ⇑u) x) = pair (withDensityReal ρ) (projMean (withDensityReal ρ) ψ) :=
      integral_congr_ae hstar
    rw [pair_projMean_zero H] at h1
    unfold pair at h1 ⊢
    rw [integral_add hu1 (hKi.const_mul β), integral_const_mul] at h1
    have h2 : ∫ x, Kop g (withDensityReal ρ) (projMean (withDensityReal ρ) ⇑u) x ∂(withDensityReal ρ) = 0 := pair_projMean_zero H _
    rw [h2, mul_zero, add_zero] at h1
    exact h1
  refine ⟨Lp.memLp u, hpair, ?_⟩
  rw [projMean_of_pair_zero hpair] at hstar
  exact hstar

theorem susceptibilityCov_eq_inner (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (H : KS (periodicRiesz d s) ρ Λ) (hρc : Continuous ρ) (β : ℝ) (hβ : 0 < β)
    (R : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ))
    (hAR : ∀ y, ALp H β (R y) = y) (φ ψ : Torus d → ℝ) (hψc : Continuous ψ)
    (y1 y2 : Lp ℝ 2 (withDensityReal ρ))
    (hy1 : ⇑y1 =ᵐ[withDensityReal ρ] projMean (withDensityReal ρ) φ)
    (hy2 : ⇑y2 =ᵐ[withDensityReal ρ] projMean (withDensityReal ρ) ψ) :
    susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β φ ψ = inner ℝ y1 (R y2) := by
  have hP := H.isProb
  have hresp : IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ ⇑(R y2) :=
    isResponse_of_A H β ψ (R y2) (by rw [hAR]; exact hy2)
  have hex : ∃ h, IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ h := ⟨_, hresp⟩
  obtain ⟨h0, -, huniq⟩ := exists_unique_response_of_one_le hd s hs0 hsd ρ H.prob hρc β hβ.le ψ
    (hψc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hch : responseInverse (periodicRiesz d s) (withDensityReal ρ) β ψ =ᵐ[withDensityReal ρ] ⇑(R y2) := by
    unfold responseInverse
    simp only [hex, dite_true]
    exact (huniq _ hex.choose_spec).trans (huniq _ hresp).symm
  unfold susceptibilityCov
  rw [innerLp_eq_l2Inner]
  exact (l2Inner_congr_ae (Filter.EventuallyEq.refl _ _) hch).trans
    (l2Inner_congr_ae hy1.symm (Filter.EventuallyEq.refl _ _))

end Ident

/-! ### The function `F(v) = ⟨S(v)φ, R S(v)ψ⟩` -/

section Main

variable {s νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ}

/-- The centered frozen equilibrium semigroup. -/
abbrev Sg (H : FrozenHyp d s (2 * mStar d + 4) νm νp c₀ Λ₀ β V ρβ) (v : ℝ) (ψ : Torus d → ℝ) :
    Torus d → ℝ :=
  equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ v ψ

theorem frozen_zero (hd : 1 ≤ d) (H : FrozenHyp d s (2 * mStar d + 4) νm νp c₀ Λ₀ β V ρβ)
    {ψ : Torus d → ℝ} (hψc : Continuous ψ) (hψm : MemSobolev (mStar d + 4) ψ) :
    Sg H 0 ψ = projMean (withDensityReal ρβ) ψ := by
  obtain ⟨F, hF, hS⟩ := exists_classical_frozen hd H hψc hψm one_pos
  have := hS 0 ⟨le_rfl, zero_le_one⟩
  refine this.trans ?_
  rw [sub_zero, hF.terminal]

theorem frozen_F_props (hd : 1 ≤ d) (H : FrozenHyp d s (2 * mStar d + 4) νm νp c₀ Λ₀ β V ρβ)
    [IsProbabilityMeasure (withDensityReal ρβ)]
    (R : Lp ℝ 2 (withDensityReal ρβ) →L[ℝ] Lp ℝ 2 (withDensityReal ρβ))
    (hRA : ∀ x, R (ALp (KS_of_frozen hd H) β x) = x)
    (hRs : ∀ x y, inner ℝ (R x) y = inner ℝ x (R y))
    {φ ψ : Torus d → ℝ} (hφ : Continuous φ) (hφm : MemSobolev (mStar d + 4) φ)
    (hψ : Continuous ψ) (hψm : MemSobolev (mStar d + 4) ψ) :
    ContinuousOn (fun v => inner ℝ (pL (withDensityReal ρβ) (fun v => Sg H v φ) v)
        (R (pL (withDensityReal ρβ) (fun v => Sg H v ψ) v))) (Set.Ici 0) ∧
    (∀ v, 0 < v → HasDerivAt (fun v => inner ℝ (pL (withDensityReal ρβ) (fun v => Sg H v φ) v)
        (R (pL (withDensityReal ρβ) (fun v => Sg H v ψ) v)))
      (-(2 * β⁻¹ * ∫ x, inner ℝ (Torus.grad (Sg H v φ) x) (Torus.grad (Sg H v ψ) x) * ρβ x)) v) ∧
    Tendsto (fun v => inner ℝ (pL (withDensityReal ρβ) (fun v => Sg H v φ) v)
        (R (pL (withDensityReal ρβ) (fun v => Sg H v ψ) v))) atTop (𝓝 0) := by
  have h3 := ClassicalPart.three_le_mStar d
  have hKS := KS_of_frozen hd H
  have hρc : Continuous ρβ := H.cont (by omega)
  have hρ1 : Torus.IsCk 1 ρβ := ET.isCk_mono' (a := 1) (b := 2 * mStar d + 4) (by omega) H.hρC
  have hpos : ∀ x, 0 < ρβ x := fun x => lt_of_lt_of_le H.hc₀ (H.hlow x)
  have cont1 : ∀ {f : Torus d → ℝ}, Torus.IsCk 2 f → Continuous f := fun hf =>
    MFAux.continuous_of_isCk (hf.of_le (by norm_num))
  have D1 := fun v (hv : 0 ≤ v) => frozen_path_data hd H hφ hφm (T' := v + 1) (by linarith)
  have D2 := fun v (hv : 0 ≤ v) => frozen_path_data hd H hψ hψm (T' := v + 1) (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    have hc1 := continuousOn_pL (withDensityReal ρβ) (a := 0) (b := v + 1) (G := fun w => Sg H w φ)
      (fun w hw => cont1 ((D1 v hv).1 w hw)) (D1 v hv).2.2.1
    have hc2 := continuousOn_pL (withDensityReal ρβ) (a := 0) (b := v + 1) (G := fun w => Sg H w ψ)
      (fun w hw => cont1 ((D2 v hv).1 w hw)) (D2 v hv).2.2.1
    have hc := ContinuousOn.inner (𝕜 := ℝ) hc1 (R.continuous.comp_continuousOn hc2)
    refine (hc v ⟨hv, by linarith⟩).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsWithin.2 ⟨Set.Iio (v + 1), isOpen_Iio, by simp, fun y hy => ⟨hy.2, hy.1.le⟩⟩
  · intro v hv
    have := hasDerivAt_F_abs s (KS_of_frozen hd H) β H.hβ hρ1 hpos R hRA hRs (a := 0) (b := v + 1)
      (fun w => Sg H w φ) (fun w => Sg H w ψ) (D1 v hv.le).1 (D1 v hv.le).2.2.2.1 (D1 v hv.le).2.2.2.2
      (D2 v hv.le).1 (D2 v hv.le).2.2.2.1 (D2 v hv.le).2.2.2.2 (v0 := v) ⟨hv, by linarith⟩
    exact this.congr_deriv (by ring)
  · obtain ⟨C, c, hC, hc, hdec⟩ := exists_frozen_l2_decay hd s νm νp c₀ Λ₀
    have hH5 : FrozenHyp d s (mStar d + 5) νm νp c₀ Λ₀ β V ρβ := H.mono (by omega)
    have hm2 : ∀ {χ : Torus d → ℝ}, MemSobolev ((mStar d : ℝ) + 4) χ →
        MemSobolev ((mStar d : ℝ) + 2) χ := fun hχ => memSobolev_mono_idx hχ (by linarith)
    have hdecχ : ∀ {χ : Torus d → ℝ}, Continuous χ → MemSobolev ((mStar d : ℝ) + 4) χ →
        ∀ τ : ℝ, 0 ≤ τ → ‖pL (withDensityReal ρβ) (fun v => Sg H v χ) τ‖ ≤
          Real.sqrt Λ₀ * (C * Real.exp (-c * τ) * sobolevNorm 2 (projMean (withDensityReal ρβ) χ)) := by
      intro χ hχc hχm τ hτ
      have hcont : Continuous (Sg H τ χ) := by
        obtain ⟨c2, -⟩ := frozen_path_data hd H hχc hχm (T' := τ + 1) (by linarith)
        exact cont1 (c2 τ ⟨hτ, by linarith⟩)
      refine (norm_pL_le H.thermal.1 hρc H.le_Lam hcont).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      exact hdec β V ρβ hH5 χ hχc (hm2 hχm) τ hτ
    have hdecφ := @hdecχ φ
    have hdecψ := @hdecχ ψ
    set Aφ := sobolevNorm 2 (projMean (withDensityReal ρβ) φ)
    set Aψ := sobolevNorm 2 (projMean (withDensityReal ρβ) ψ)
    set a := Real.sqrt Λ₀ * C * Aφ
    set b := Real.sqrt Λ₀ * C * Aψ
    have hE : Tendsto (fun T : ℝ => Real.exp (-c * T)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
    have hlim : Tendsto (fun T : ℝ => (a * Real.exp (-c * T)) * (‖R‖ * b * Real.exp (-c * T)))
        atTop (𝓝 0) := by
      have := (hE.const_mul a).mul (hE.const_mul (‖R‖ * b))
      simpa using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
    have hu : ‖pL (withDensityReal ρβ) (fun v => Sg H v φ) T‖ ≤ a * Real.exp (-c * T) := by
      refine (hdecφ hφ hφm T hT).trans (le_of_eq ?_)
      simp only [a, Aφ]; ring
    have hw : ‖R (pL (withDensityReal ρβ) (fun v => Sg H v ψ) T)‖ ≤ ‖R‖ * b * Real.exp (-c * T) := by
      refine (R.le_opNorm _).trans ?_
      have := hdecψ hψ hψm T hT
      calc ‖R‖ * ‖pL (withDensityReal ρβ) (fun v => Sg H v ψ) T‖ ≤
          ‖R‖ * (b * Real.exp (-c * T)) := by
            refine mul_le_mul_of_nonneg_left (this.trans (le_of_eq ?_)) (norm_nonneg _)
            simp only [b, Aψ]; ring
        _ = ‖R‖ * b * Real.exp (-c * T) := by ring
    exact (norm_inner_le_norm _ _).trans (mul_le_mul hu hw (norm_nonneg _) ((norm_nonneg _).trans hu))



end Main

end P13aPart2

/-- P13a part 2: `C_{β,μ}(φ,ψ) = 2β⁻¹ ∫_0^∞ ∫ ∇S_β(v)φ·∇S_β(v)ψ ρ_β dx dv` for continuous `φ, ψ` in
`H^{mStar+4}`, where `S_β` is the centered equilibrium semigroup (route: see the comment above). -/
theorem susceptibilityCov_eq_integral (hd : 1 ≤ d) (s : ℝ) (νm νp c₀ Λ₀ : ℝ) (β : ℝ)
    (V ρβ : Torus d → ℝ) (H : MFAdjoint.FrozenHyp d s (2 * mStar d + 4) νm νp c₀ Λ₀ β V ρβ)
    (φ ψ : Torus d → ℝ) (hφ : Continuous φ) (hφm : MemSobolev (mStar d + 4) φ)
    (hψ : Continuous ψ) (hψm : MemSobolev (mStar d + 4) ψ) :
    IntegrableOn (fun v => ∫ x, inner ℝ (Torus.grad (equilibriumSemigroup
        (mfData d s H.hs0 H.hsd V β H.hβ) ρβ v φ) x)
        (Torus.grad (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ v ψ) x) * ρβ x)
      (Set.Ici 0) ∧
    susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ ψ =
      2 * β⁻¹ * ∫ v in Set.Ici (0 : ℝ), ∫ x, inner ℝ (Torus.grad (equilibriumSemigroup
          (mfData d s H.hs0 H.hsd V β H.hβ) ρβ v φ) x)
          (Torus.grad (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ v ψ) x) * ρβ x := by
  have h3 := ClassicalPart.three_le_mStar d
  have hKS := KS_of_frozen hd H
  have := hKS.isProb
  have hρc : Continuous ρβ := H.cont (by omega)
  obtain ⟨R, hRA, hAR, hRs, -⟩ := exists_inverse hd s H.hs0 H.hsd hKS hρc β H.hβ.le
  have hc : 0 < 2 * β⁻¹ := by have := H.hβ; positivity
  have cont1 : ∀ {f : Torus d → ℝ}, Torus.IsCk 2 f → Continuous f := fun hf =>
    MFAux.continuous_of_isCk (hf.of_le (by norm_num))
  have hC1 : ∀ {χ : Torus d → ℝ}, Continuous χ → MemSobolev ((mStar d : ℝ) + 4) χ →
      ∀ v : ℝ, 0 ≤ v → Torus.IsCk 1 (Sg H v χ) := by
    intro χ hχc hχm v hv
    obtain ⟨c2, -⟩ := frozen_path_data hd H hχc hχm (T' := v + 1) (by linarith)
    exact (c2 v ⟨hv, by linarith⟩).of_le (by norm_num)
  have Pφφ := frozen_F_props hd H R hRA hRs hφ hφm hφ hφm
  have Pψψ := frozen_F_props hd H R hRA hRs hψ hψm hψ hψm
  have Pφψ := frozen_F_props hd H R hRA hRs hφ hφm hψ hψm
  have hdφ := real_diag hc Pφφ.1 Pφφ.2.1 (fun v hv => energy_nonneg H.thermal.1.nonneg) Pφφ.2.2
  have hdψ := real_diag hc Pψψ.1 Pψψ.2.1 (fun v hv => energy_nonneg H.thermal.1.nonneg) Pψψ.2.2
  have hg : IntegrableOn (fun v => ((∫ x, inner ℝ (Torus.grad (Sg H v φ) x) (Torus.grad (Sg H v φ) x) * ρβ x) +
      ∫ x, inner ℝ (Torus.grad (Sg H v ψ) x) (Torus.grad (Sg H v ψ) x) * ρβ x) / 2) (Set.Ioi 0) :=
    (hdφ.add hdψ).div_const 2
  obtain ⟨hint, hF0⟩ := real_ftc hc Pφψ.1 Pφψ.2.1 Pφψ.2.2 hg (fun v hv =>
    abs_energy_le hρc H.thermal.1.nonneg (hC1 hφ hφm v hv.le) (hC1 hψ hψm v hv.le))
  refine ⟨hint, ?_⟩
  have hcφ : Continuous (Sg H 0 φ) := by
    obtain ⟨c2, -⟩ := frozen_path_data hd H hφ hφm (T' := 1) one_pos
    exact cont1 (c2 0 ⟨le_rfl, zero_le_one⟩)
  have hcψ : Continuous (Sg H 0 ψ) := by
    obtain ⟨c2, -⟩ := frozen_path_data hd H hψ hψm (T' := 1) one_pos
    exact cont1 (c2 0 ⟨le_rfl, zero_le_one⟩)
  have hid := susceptibilityCov_eq_inner hd s H.hs0 H.hsd hKS hρc β H.hβ R hAR φ ψ hψ
    (pL (withDensityReal ρβ) (fun v => Sg H v φ) 0) (pL (withDensityReal ρβ) (fun v => Sg H v ψ) 0)
    ((pL_ae hcφ).trans (Filter.EventuallyEq.of_eq (frozen_zero hd H hφ hφm)))
    ((pL_ae hcψ).trans (Filter.EventuallyEq.of_eq (frozen_zero hd H hψ hψm)))
  rw [hid]
  exact hF0


end HRS.PDE.MFLinear
