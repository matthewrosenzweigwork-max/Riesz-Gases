import HRS.MS.S111X1E2
import HRS.MS.S111X1Aux4

/-!
# S11.1 X1 (energy), part 3: the nonlocal term as a pairing, and its bound
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ}

/-- weighted Cauchy-Schwarz -/
theorem x1_cs_w {α : Type*} [MeasurableSpace α] {μ : Measure α} {w p q : α → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hpp : Integrable (fun x => w x * p x ^ 2) μ)
    (hqq : Integrable (fun x => w x * q x ^ 2) μ) (hpq : Integrable (fun x => w x * (p x * q x)) μ) :
    (∫ x, w x * (p x * q x) ∂μ) ^ 2 ≤ (∫ x, w x * p x ^ 2 ∂μ) * ∫ x, w x * q x ^ 2 ∂μ := by
  have h := discrim_le_zero (a := ∫ x, w x * q x ^ 2 ∂μ) (b := 2 * ∫ x, w x * (p x * q x) ∂μ)
    (c := ∫ x, w x * p x ^ 2 ∂μ) (fun l => by
      have : 0 ≤ ∫ x, w x * (p x + l * q x) ^ 2 ∂μ :=
        integral_nonneg fun x => mul_nonneg (hw x) (sq_nonneg _)
      have e : ∫ x, w x * (p x + l * q x) ^ 2 ∂μ =
          (∫ x, w x * p x ^ 2 ∂μ) + 2 * l * (∫ x, w x * (p x * q x) ∂μ) + l ^ 2 * ∫ x, w x * q x ^ 2 ∂μ := by
        have e1 : ∀ x, w x * (p x + l * q x) ^ 2 =
            w x * p x ^ 2 + 2 * l * (w x * (p x * q x)) + l ^ 2 * (w x * q x ^ 2) := fun x => by ring
        simp_rw [e1]
        have hi : Integrable (fun x => w x * p x ^ 2 + 2 * l * (w x * (p x * q x))) μ :=
          hpp.add (hpq.const_mul _)
        rw [integral_add hi (hqq.const_mul _), integral_add hpp (hpq.const_mul _),
          integral_const_mul, integral_const_mul]
      rw [e] at this
      nlinarith)
  unfold discrim at h
  nlinarith

/-- the standing data on the density and the exponent -/
structure KData (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (M : ℝ) : Prop where
  hd : 1 ≤ d
  hs0 : 0 ≤ s
  hs1 : s + 1 < d
  meas : Measurable ρ
  nonneg : ∀ x, 0 ≤ ρ x
  int : Integrable ρ
  bdd : ∀ x, ρ x ≤ M

theorem KData.M_nonneg {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M) : 0 ≤ M :=
  (K.nonneg 0).trans (K.bdd 0)

theorem comp_meas_apply {a : Euc d → Euc d} (ham : Measurable a) (j : Fin d) :
    Measurable fun y => a y j :=
  (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.measurable.comp ham

/-- the nonlocal term is the plain convolution pairing -/
theorem nl_plain {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M) {a : Euc d → Euc d}
    (ham : Measurable a) {Ba : ℝ} (hBa : ∀ y, ‖a y‖ ≤ Ba) (x : Euc d) :
    (∑ j : Fin d, (convGradConvW (rieszKernelGrad d s) (fun y => ρ y * a y j) x) j) =
      ∫ y, ρ y * inner ℝ (a y) (rieszKernelGrad d s (x - y)) := by
  have hcomp : ∀ j : Fin d, ∀ y, |ρ y * a y j| ≤ Ba * ρ y := by
    intro j y
    rw [abs_mul, abs_of_nonneg (K.nonneg y), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (K.nonneg y)
    have := PiLp.norm_apply_le (a y) j
    rw [Real.norm_eq_abs] at this
    exact this.trans (hBa y)
  have hmeasj : ∀ j : Fin d, Measurable fun y => ρ y * a y j := fun j => K.meas.mul (comp_meas_apply ham j)
  have e1 : ∀ j : Fin d, (convGradConvW (rieszKernelGrad d s) (fun y => ρ y * a y j) x) j =
      ∫ y, ρ y * a y j * rieszKernelGrad d s (x - y) j := by
    intro j
    rw [conv_eq_plain K.hd K.hs0 K.hs1 K.meas K.nonneg K.int K.bdd (hmeasj j) (hcomp j) x]
    have hI := plain_integrable K.hd K.hs0 K.hs1 K.meas K.nonneg K.int K.bdd (hmeasj j) (hcomp j) x
    have := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).integral_comp_comm hI
    simpa using this.symm
  simp_rw [e1]
  have hI : ∀ j : Fin d, Integrable (fun y => ρ y * a y j * rieszKernelGrad d s (x - y) j) := by
    intro j
    have hI0 := plain_integrable K.hd K.hs0 K.hs1 K.meas K.nonneg K.int K.bdd (hmeasj j) (hcomp j) x
    have := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).integrable_comp hI0
    simpa using this
  rw [← integral_finset_sum _ (fun j _ => hI j)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- the force potential `W y = ∫ ∇g(y-x) f(x) ρ(x) dx` -/
def Wf (d : ℕ) (s : ℝ) (ρ f : Euc d → ℝ) (y : Euc d) : Euc d :=
  ∫ x, (f x * ρ x) • rieszKernelGrad d s (y - x)

theorem prod_integrable_kernel {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M) :
    Integrable (fun p : Euc d × Euc d => ρ p.1 * (ρ p.2 * ‖rieszKernelGrad d s (p.1 - p.2)‖))
      (volume.prod volume) := by
  have hmeas : Measurable fun p : Euc d × Euc d =>
      ρ p.1 * (ρ p.2 * ‖rieszKernelGrad d s (p.1 - p.2)‖) :=
    (K.meas.comp measurable_fst).mul ((K.meas.comp measurable_snd).mul
      ((kG_measurable s).comp (measurable_fst.sub measurable_snd)).norm)
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
  · exact (kG_weighted K.hd K.hs0 K.hs1 K.meas K.nonneg K.int K.bdd x).1.const_mul (ρ x)
  · have hA := fun x => (kG_weighted K.hd K.hs0 K.hs1 K.meas K.nonneg K.int K.bdd x)
    have e : ∀ x, ∫ y, ‖ρ x * (ρ y * ‖rieszKernelGrad d s (x - y)‖)‖ =
        ρ x * ∫ y, ρ y * ‖rieszKernelGrad d s (x - y)‖ := by
      intro x
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      beta_reduce
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (K.nonneg x)
        (mul_nonneg (K.nonneg y) (norm_nonneg _)))]
    simp_rw [e]
    refine (K.int.mul_const (kA d s M ρ)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · -- measurability of the inner integral
      have : Measurable fun p : Euc d × Euc d => ρ p.2 * ‖rieszKernelGrad d s (p.1 - p.2)‖ :=
        (K.meas.comp measurable_snd).mul ((kG_measurable s).comp (measurable_fst.sub measurable_snd)).norm
      exact (K.meas.aestronglyMeasurable).mul
        ((this.stronglyMeasurable.integral_prod_right').aestronglyMeasurable)
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (K.nonneg x)
        (integral_nonneg fun y => mul_nonneg (K.nonneg y) (norm_nonneg _)))]
      exact mul_le_mul_of_nonneg_left (hA x).2 (K.nonneg x)

theorem nl_swap {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M) {a : Euc d → Euc d}
    (ham : Measurable a) {Ba : ℝ} (hBa : ∀ y, ‖a y‖ ≤ Ba) {f : Euc d → ℝ} (hfm : Measurable f)
    {Bf : ℝ} (hBf : ∀ x, |f x| ≤ Bf) :
    (∫ x, f x * ρ x * ∫ y, ρ y * inner ℝ (a y) (rieszKernelGrad d s (x - y))) =
      -∫ y, ρ y * inner ℝ (a y) (Wf d s ρ f y) := by
  set F : Euc d × Euc d → ℝ := fun p => f p.1 * ρ p.1 * (ρ p.2 * inner ℝ (a p.2) (rieszKernelGrad d s (p.1 - p.2)))
    with hF
  have hFm : Measurable F := by
    refine ((hfm.comp measurable_fst).mul (K.meas.comp measurable_fst)).mul
      ((K.meas.comp measurable_snd).mul (Measurable.inner (ham.comp measurable_snd)
        ((kG_measurable s).comp (measurable_fst.sub measurable_snd))))
  have hFi : Integrable F (volume.prod volume) := by
    refine ((prod_integrable_kernel K).const_mul (Bf * Ba)).mono' hFm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [hF, Real.norm_eq_abs, abs_mul]
    have h1 : |f p.1| ≤ Bf := hBf p.1
    have h2 : |inner ℝ (a p.2) (rieszKernelGrad d s (p.1 - p.2))| ≤ Ba * ‖rieszKernelGrad d s (p.1 - p.2)‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hBa p.2) (norm_nonneg _))
    rw [abs_of_nonneg (K.nonneg p.1), abs_of_nonneg (K.nonneg p.2)]
    have hBf0 : 0 ≤ Bf := (abs_nonneg _).trans h1
    have hρ1 := K.nonneg p.1
    have hρ2 := K.nonneg p.2
    calc |f p.1| * ρ p.1 * (ρ p.2 * |inner ℝ (a p.2) (rieszKernelGrad d s (p.1 - p.2))|)
        ≤ Bf * ρ p.1 * (ρ p.2 * (Ba * ‖rieszKernelGrad d s (p.1 - p.2)‖)) := by
          gcongr
      _ = Bf * Ba * (ρ p.1 * (ρ p.2 * ‖rieszKernelGrad d s (p.1 - p.2)‖)) := by ring
  have hswap := integral_integral_swap (f := fun x y => F (x, y)) hFi
  have hL : ∀ x, ∫ y, F (x, y) = f x * ρ x * ∫ y, ρ y * inner ℝ (a y) (rieszKernelGrad d s (x - y)) := by
    intro x
    simp only [hF]
    rw [integral_const_mul]
  simp_rw [hL] at hswap
  rw [hswap]
  have hR : ∀ y, ∫ x, F (x, y) = -(ρ y * inner ℝ (a y) (Wf d s ρ f y)) := by
    intro y
    have hint : Integrable (fun x => (f x * ρ x) • rieszKernelGrad d s (y - x)) := by
      have hh : ∀ x, |f x * ρ x| ≤ Bf * ρ x := by
        intro x
        rw [abs_mul, abs_of_nonneg (K.nonneg x)]
        exact mul_le_mul_of_nonneg_right (hBf x) (K.nonneg x)
      exact plain_integrable K.hd K.hs0 K.hs1 K.meas K.nonneg K.int K.bdd (hfm.mul K.meas) hh y
    have e1 : ∀ x, F (x, y) = ρ y * (-inner ℝ (a y) ((f x * ρ x) • rieszKernelGrad d s (y - x))) := by
      intro x
      simp only [hF]
      have : rieszKernelGrad d s (x - y) = -rieszKernelGrad d s (y - x) := by
        rw [← HRS.MS.R2Interp.s102_rieszKernelGrad_neg, neg_sub]
      rw [this, inner_neg_right, inner_smul_right]
      ring
    simp_rw [e1]
    rw [integral_const_mul, integral_neg, integral_inner hint (a y)]
    unfold Wf
    ring
  simp_rw [hR]
  rw [integral_neg]

theorem Wf_meas {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M) {f : Euc d → ℝ}
    (hfm : Measurable f) : Measurable (Wf d s ρ f) := by
  unfold Wf
  have : Measurable fun p : Euc d × Euc d => (f p.2 * ρ p.2) • rieszKernelGrad d s (p.1 - p.2) :=
    ((hfm.comp measurable_snd).mul (K.meas.comp measurable_snd)).smul
      ((kG_measurable s).comp (measurable_fst.sub measurable_snd))
  exact (this.stronglyMeasurable.integral_prod_right').measurable

/-- pointwise bound of the force potential -/
theorem Wf_sq_le {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M) {f : Euc d → ℝ}
    (hfm : Measurable f) {Bf : ℝ} (hBf : ∀ x, |f x| ≤ Bf) (y : Euc d) :
    ‖Wf d s ρ f y‖ ^ 2 ≤ kA d s M ρ * ∫ x, ρ x * ‖rieszKernelGrad d s (y - x)‖ * f x ^ 2 := by
  set w : Euc d → ℝ := fun x => ρ x * ‖rieszKernelGrad d s (y - x)‖ with hw
  have hw0 : ∀ x, 0 ≤ w x := fun x => mul_nonneg (K.nonneg x) (norm_nonneg _)
  have hwi : Integrable w := (kG_weighted K.hd K.hs0 K.hs1 K.meas K.nonneg K.int K.bdd y).1
  have hwm : Measurable w := K.meas.mul ((kG_measurable s).comp (measurable_const.sub measurable_id)).norm
  have hBf0 : 0 ≤ Bf := (abs_nonneg _).trans (hBf 0)
  have hpp : Integrable (fun x => w x * |f x| ^ 2) := by
    refine (hwi.mul_const (Bf ^ 2)).mono' (hwm.mul ((hfm.abs).pow_const 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 x) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (by nlinarith [hBf x, abs_nonneg (f x)]) (hw0 x)
  have hqq : Integrable (fun x => w x * (1 : ℝ) ^ 2) := by simpa using hwi
  have hpq : Integrable (fun x => w x * (|f x| * 1)) := by
    refine (hwi.mul_const Bf).mono' (hwm.mul (hfm.abs.mul measurable_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 x) (mul_nonneg (abs_nonneg _) zero_le_one))]
    simpa using mul_le_mul_of_nonneg_left (hBf x) (hw0 x)
  have hcs := x1_cs_w hw0 hpp hqq hpq
  have hnorm : ‖Wf d s ρ f y‖ ≤ ∫ x, w x * (|f x| * 1) := by
    unfold Wf
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hw, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (K.nonneg x)]
    ring
  have hA := (kG_weighted K.hd K.hs0 K.hs1 K.meas K.nonneg K.int K.bdd y).2
  have h1 : ∫ x, w x * 1 ^ 2 ≤ kA d s M ρ := by simpa [hw] using hA
  have h2 : ∫ x, w x * |f x| ^ 2 = ∫ x, ρ x * ‖rieszKernelGrad d s (y - x)‖ * f x ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hw, sq_abs]
  have hAnn : 0 ≤ ∫ x, w x * 1 ^ 2 := integral_nonneg fun x => by simpa using hw0 x
  calc ‖Wf d s ρ f y‖ ^ 2 ≤ (∫ x, w x * (|f x| * 1)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∫ x, w x * |f x| ^ 2) * ∫ x, w x * 1 ^ 2 := hcs
    _ ≤ (∫ x, w x * |f x| ^ 2) * kA d s M ρ :=
        mul_le_mul_of_nonneg_left h1 (integral_nonneg fun x => mul_nonneg (hw0 x) (sq_nonneg _))
    _ = _ := by rw [h2, mul_comm]

theorem kA_nonneg {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M) : 0 ≤ kA d s M ρ := by
  unfold kA
  have := kσ_nonneg s
  have h1 : 0 ≤ ∫ z, HRS.MH.DualityRd.db1G (d := d) (s + 1) z :=
    integral_nonneg fun z => HRS.MH.DualityRd.db1G_nonneg _ _
  have h2 : 0 ≤ ∫ y, ρ y := integral_nonneg K.nonneg
  have := K.M_nonneg
  positivity

theorem Wf_L2 {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M) {f : Euc d → ℝ}
    (hfm : Measurable f) {Bf : ℝ} (hBf : ∀ x, |f x| ≤ Bf) :
    ∫ y, ρ y * ‖Wf d s ρ f y‖ ^ 2 ≤ kA d s M ρ ^ 2 * ∫ x, ρ x * f x ^ 2 := by
  set A := kA d s M ρ with hA
  have hA0 : 0 ≤ A := kA_nonneg K
  have hBf0 : 0 ≤ Bf := (abs_nonneg _).trans (hBf 0)
  set H : Euc d × Euc d → ℝ := fun p => ρ p.1 * (ρ p.2 * ‖rieszKernelGrad d s (p.1 - p.2)‖ * f p.2 ^ 2)
    with hH
  have hHm : Measurable H :=
    (K.meas.comp measurable_fst).mul (((K.meas.comp measurable_snd).mul
      ((kG_measurable s).comp (measurable_fst.sub measurable_snd)).norm).mul
        ((hfm.comp measurable_snd).pow_const 2))
  have hHi : Integrable H (volume.prod volume) := by
    refine ((prod_integrable_kernel K).const_mul (Bf ^ 2)).mono' hHm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    have h1 := K.nonneg p.1
    have h2 := K.nonneg p.2
    simp only [hH]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 (mul_nonneg (mul_nonneg h2 (norm_nonneg _)) (sq_nonneg _)))]
    have : f p.2 ^ 2 ≤ Bf ^ 2 := by nlinarith [hBf p.2, abs_nonneg (f p.2), sq_abs (f p.2)]
    calc ρ p.1 * (ρ p.2 * ‖rieszKernelGrad d s (p.1 - p.2)‖ * f p.2 ^ 2)
        ≤ ρ p.1 * (ρ p.2 * ‖rieszKernelGrad d s (p.1 - p.2)‖ * Bf ^ 2) := by gcongr
      _ = Bf ^ 2 * (ρ p.1 * (ρ p.2 * ‖rieszKernelGrad d s (p.1 - p.2)‖)) := by ring
  set g : Euc d → ℝ := fun y => ∫ x, ρ x * ‖rieszKernelGrad d s (y - x)‖ * f x ^ 2 with hg
  have hHy : ∀ y, ∫ x, H (y, x) = ρ y * g y := by
    intro y; simp only [hH, hg]; rw [integral_const_mul]
  have hgi : Integrable (fun y => ρ y * g y) := by
    have := hHi.integral_prod_left
    simpa [hHy] using this
  have hmono : ∫ y, ρ y * ‖Wf d s ρ f y‖ ^ 2 ≤ ∫ y, A * (ρ y * g y) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
      mul_nonneg (K.nonneg y) (sq_nonneg _)) (hgi.const_mul A) (Filter.Eventually.of_forall fun y => ?_)
    calc ρ y * ‖Wf d s ρ f y‖ ^ 2 ≤ ρ y * (A * g y) :=
          mul_le_mul_of_nonneg_left (Wf_sq_le K hfm hBf y) (K.nonneg y)
      _ = A * (ρ y * g y) := by ring
  refine hmono.trans ?_
  rw [integral_const_mul]
  have hswap := integral_integral_swap (f := fun y x => H (y, x)) hHi
  simp_rw [hHy] at hswap
  have hinner : ∀ x, ∫ y, H (y, x) ≤ A * (ρ x * f x ^ 2) := by
    intro x
    have e : ∀ y, ‖rieszKernelGrad d s (y - x)‖ = ‖rieszKernelGrad d s (x - y)‖ := fun y => by
      rw [← kG_norm_neg s (x - y), neg_sub]
    have h1 : ∫ y, H (y, x) = (ρ x * f x ^ 2) * ∫ y, ρ y * ‖rieszKernelGrad d s (x - y)‖ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hH, e]
      ring
    rw [h1, mul_comm A]
    exact mul_le_mul_of_nonneg_left (kG_weighted K.hd K.hs0 K.hs1 K.meas K.nonneg K.int K.bdd x).2
      (mul_nonneg (K.nonneg x) (sq_nonneg _))
  have hrhs : Integrable (fun x => A * (ρ x * f x ^ 2)) := by
    refine (K.int.mul_const (A * Bf ^ 2)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (measurable_const.mul (K.meas.mul (hfm.pow_const 2))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA0 (mul_nonneg (K.nonneg x) (sq_nonneg _)))]
      have : f x ^ 2 ≤ Bf ^ 2 := by nlinarith [hBf x, abs_nonneg (f x), sq_abs (f x)]
      have hρx := K.nonneg x
      calc A * (ρ x * f x ^ 2) ≤ A * (ρ x * Bf ^ 2) := by gcongr
        _ = ρ x * (A * Bf ^ 2) := by ring
  have hfin : ∫ x, ∫ y, H (y, x) ≤ ∫ x, A * (ρ x * f x ^ 2) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => integral_nonneg fun y => ?_)
      hrhs (Filter.Eventually.of_forall hinner)
    simp only [hH]
    exact mul_nonneg (K.nonneg y) (mul_nonneg (mul_nonneg (K.nonneg x) (norm_nonneg _)) (sq_nonneg _))
  calc A * ∫ y, ρ y * g y = A * ∫ x, ∫ y, H (y, x) := by rw [← hswap]
    _ ≤ A * ∫ x, A * (ρ x * f x ^ 2) := mul_le_mul_of_nonneg_left hfin hA0
    _ = A ^ 2 * ∫ x, ρ x * f x ^ 2 := by rw [integral_const_mul]; ring

theorem Wf_bdd {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M) {f : Euc d → ℝ}
    {Bf : ℝ} (hBf : ∀ x, |f x| ≤ Bf) (y : Euc d) : ‖Wf d s ρ f y‖ ≤ kA d s M ρ * Bf := by
  have hBf0 : 0 ≤ Bf := (abs_nonneg _).trans (hBf 0)
  have hwi := (kG_weighted K.hd K.hs0 K.hs1 K.meas K.nonneg K.int K.bdd y)
  unfold Wf
  refine (norm_integral_le_of_norm_le (hwi.1.const_mul Bf) (Filter.Eventually.of_forall fun x => ?_)).trans ?_
  · rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (K.nonneg x)]
    have := mul_le_mul_of_nonneg_right (hBf x) (mul_nonneg (K.nonneg x) (norm_nonneg (rieszKernelGrad d s (y - x))))
    nlinarith [this]
  · rw [integral_const_mul]
    nlinarith [hwi.2, hBf0]

/-- the energy bound for the nonlocal pairing -/
theorem nl_bound {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ} (K : KData d s ρ M) {a : Euc d → Euc d}
    (ham : Measurable a) {Ba : ℝ} (hBa : ∀ y, ‖a y‖ ≤ Ba) {f : Euc d → ℝ} (hfm : Measurable f)
    {Bf : ℝ} (hBf : ∀ x, |f x| ≤ Bf) :
    |∫ x, f x * ρ x * ∫ y, ρ y * inner ℝ (a y) (rieszKernelGrad d s (x - y))| ≤
      kA d s M ρ * Real.sqrt (∫ y, ρ y * ‖a y‖ ^ 2) * Real.sqrt (∫ x, ρ x * f x ^ 2) := by
  rw [nl_swap K ham hBa hfm hBf, abs_neg]
  set A := kA d s M ρ with hA
  have hA0 : 0 ≤ A := kA_nonneg K
  have hBf0 : 0 ≤ Bf := (abs_nonneg _).trans (hBf 0)
  have hBa0 : 0 ≤ Ba := (norm_nonneg _).trans (hBa 0)
  have hWm := Wf_meas K hfm
  have hamn : Measurable fun y => ‖a y‖ := ham.norm
  have hWn : Measurable fun y => ‖Wf d s ρ f y‖ := hWm.norm
  have hpp : Integrable (fun y => ρ y * ‖a y‖ ^ 2) := by
    refine (K.int.mul_const (Ba ^ 2)).mono' (K.meas.mul (hamn.pow_const 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (K.nonneg y) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (by nlinarith [hBa y, norm_nonneg (a y)]) (K.nonneg y)
  have hqq : Integrable (fun y => ρ y * ‖Wf d s ρ f y‖ ^ 2) := by
    refine (K.int.mul_const ((A * Bf) ^ 2)).mono' (K.meas.mul (hWn.pow_const 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (K.nonneg y) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (by nlinarith [Wf_bdd K hBf y, norm_nonneg (Wf d s ρ f y)]) (K.nonneg y)
  have hpq : Integrable (fun y => ρ y * (‖a y‖ * ‖Wf d s ρ f y‖)) := by
    refine (K.int.mul_const (Ba * (A * Bf))).mono' (K.meas.mul (hamn.mul hWn)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (K.nonneg y) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hBa y) (Wf_bdd K hBf y) (norm_nonneg _) hBa0) (K.nonneg y)
  have hcs := x1_cs_w K.nonneg hpp hqq hpq
  have h1 : |∫ y, ρ y * inner ℝ (a y) (Wf d s ρ f y)| ≤ ∫ y, ρ y * (‖a y‖ * ‖Wf d s ρ f y‖) := by
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun y => abs_nonneg _) hpq (Filter.Eventually.of_forall fun y => ?_))
    beta_reduce
    rw [abs_mul, abs_of_nonneg (K.nonneg y)]
    exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (K.nonneg y)
  have h2 := Wf_L2 K hfm hBf
  have hQ0 : 0 ≤ ∫ y, ρ y * ‖a y‖ ^ 2 := integral_nonneg fun y => mul_nonneg (K.nonneg y) (sq_nonneg _)
  have hF0 : 0 ≤ ∫ x, ρ x * f x ^ 2 := integral_nonneg fun y => mul_nonneg (K.nonneg y) (sq_nonneg _)
  have h3 : ∫ y, ρ y * (‖a y‖ * ‖Wf d s ρ f y‖) ≤
      Real.sqrt (∫ y, ρ y * ‖a y‖ ^ 2) * (A * Real.sqrt (∫ x, ρ x * f x ^ 2)) := by
    have hsq : (∫ y, ρ y * (‖a y‖ * ‖Wf d s ρ f y‖)) ^ 2 ≤
        (∫ y, ρ y * ‖a y‖ ^ 2) * (A ^ 2 * ∫ x, ρ x * f x ^ 2) :=
      hcs.trans (mul_le_mul_of_nonneg_left h2 hQ0)
    have : (∫ y, ρ y * (‖a y‖ * ‖Wf d s ρ f y‖)) ≤
        Real.sqrt ((∫ y, ρ y * ‖a y‖ ^ 2) * (A ^ 2 * ∫ x, ρ x * f x ^ 2)) :=
      Real.le_sqrt_of_sq_le hsq
    refine this.trans (le_of_eq ?_)
    rw [Real.sqrt_mul hQ0, Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA0]
  calc _ ≤ _ := h1
    _ ≤ _ := h3
    _ = _ := by ring

end HRS.MS.S111X1
