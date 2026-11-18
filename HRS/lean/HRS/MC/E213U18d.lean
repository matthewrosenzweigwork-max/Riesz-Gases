import HRS.MC.E213U18c
import HRS.Equilibrium.PairCorrection
import HRS.Kernel.GradReg

/-!
# Packet e213u18 (part d): the pair kernel `h_f(x,y) = (∇f(x) - ∇f(y))·∇g(x-y)`; Wick coefficients as plain
iterated integrals, and the limit `∑_{S×S} ĥ_{kl} c_k d_l → ∬ h χ χ'`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U18

open HRS HRS.Sec7

variable {d : ℕ}

theorem u18_K_integrable {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s + 1 < d) :
    Integrable (fun z : Torus d => ‖periodicRieszGrad d s z‖) := by
  obtain ⟨C, hC⟩ := KernelGrad.periodicRieszGrad_bound_tdist (d := d) (s := s) hd hs0 (by linarith)
  have hint := KernelGrad.integrable_norm_rpow_neg (d := d) (by omega) (α := s + 1) hs1
  have hmeas : Measurable fun z : Torus d => ‖periodicRieszGrad d s z‖ :=
    (KernelGrad.measurable_periodicRieszGrad (by linarith)).norm
  refine Integrable.mono' ((hint.const_mul |C|).add (integrable_const |C|)) hmeas.aestronglyMeasurable ?_
  filter_upwards [KernelGrad.torus_ae_ne' (by omega)] with z hz
  have h1 := hC z hz
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h2 : KernelGrad.tdist z 0 ^ (-s - 1) ≤ ‖z‖ ^ (-(s + 1)) := by
    rw [show -s - 1 = -(s + 1) by ring]
    exact Real.rpow_le_rpow_of_nonpos hpos (KernelGrad.norm_le_tdist z) (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  calc ‖periodicRieszGrad d s z‖ ≤ C * (KernelGrad.tdist z 0 ^ (-s - 1) + 1) := h1
    _ ≤ |C| * (KernelGrad.tdist z 0 ^ (-s - 1) + 1) := by
        have hT0 : 0 ≤ KernelGrad.tdist z 0 := by rw [KernelGrad.tdist_zero_right]; exact norm_nonneg _
        exact mul_le_mul_of_nonneg_right (le_abs_self C)
          (add_nonneg (Real.rpow_nonneg hT0 _) zero_le_one)
    _ ≤ |C| * (‖z‖ ^ (-(s + 1)) + 1) := by gcongr
    _ = _ := by simp [mul_add]


/-- A pair kernel dominated by an integrable convolution kernel `G(x-y)`. -/
structure PairKer (G : Torus d → ℝ) (h : Torus d → Torus d → ℝ) (a : ℝ) : Prop where
  meas : Measurable (fun p : Torus d × Torus d => h p.1 p.2)
  ha : 0 ≤ a
  G_int : Integrable G
  G_nonneg : ∀ z, 0 ≤ G z
  bound : ∀ x y, |h x y| ≤ a * G (x - y)

namespace PairKer

variable {G : Torus d → ℝ} {h : Torus d → Torus d → ℝ} {a : ℝ}

theorem row_meas (H : PairKer G h a) (x : Torus d) : Measurable fun y => h x y :=
  H.meas.comp (measurable_const.prodMk measurable_id)

theorem col_meas (H : PairKer G h a) (y : Torus d) : Measurable fun x => h x y :=
  H.meas.comp (measurable_id.prodMk measurable_const)

theorem row_int (H : PairKer G h a) (x : Torus d) : Integrable (fun y => h x y) := by
  refine Integrable.mono' ((H.G_int.comp_sub_left x).const_mul a) (H.row_meas x).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]; exact H.bound x y

theorem col_int (H : PairKer G h a) (y : Torus d) : Integrable (fun x => h x y) := by
  refine Integrable.mono' ((H.G_int.comp_sub_right y).const_mul a) (H.col_meas y).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]; exact H.bound x y

theorem row_L1 (H : PairKer G h a) (x : Torus d) : ∫ y, |h x y| ≤ a * ∫ z, G z := by
  have h1 : ∫ y, |h x y| ≤ ∫ y, a * G (x - y) :=
    integral_mono (H.row_int x).abs ((H.G_int.comp_sub_left x).const_mul a) fun y => H.bound x y
  rw [integral_const_mul, integral_sub_left_eq_self (fun z => G z) volume x] at h1
  exact h1

theorem col_L1 (H : PairKer G h a) (y : Torus d) : ∫ x, |h x y| ≤ a * ∫ z, G z := by
  have h1 : ∫ x, |h x y| ≤ ∫ x, a * G (x - y) :=
    integral_mono (H.col_int y).abs ((H.G_int.comp_sub_right y).const_mul a) fun x => H.bound x y
  rw [integral_const_mul, integral_sub_right_eq_self (fun z => G z) y] at h1
  exact h1


theorem rowInt_meas (H : PairKer G h a) {g : Torus d → ℝ} (hg : Measurable g) :
    Measurable fun x => ∫ y, h x y * g y := by
  have := (H.meas.mul (hg.comp measurable_snd)).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (Torus d)))
  exact this.measurable

theorem row_mul_int (H : PairKer G h a) {g : Torus d → ℝ} (hg : Measurable g) {M : ℝ}
    (hgb : ∀ y, |g y| ≤ M) (x : Torus d) : Integrable (fun y => h x y * g y) := by
  refine Integrable.mono' ((H.row_int x).abs.mul_const M) ((H.row_meas x).mul hg).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hgb y) (abs_nonneg _)

theorem rowInt_bound (H : PairKer G h a) {g : Torus d → ℝ} (hg : Measurable g) {M : ℝ}
    (hgb : ∀ y, |g y| ≤ M) (x : Torus d) : |∫ y, h x y * g y| ≤ a * (∫ z, G z) * M := by
  have h0 : (0 : ℝ) ≤ M := (abs_nonneg _).trans (hgb (Classical.arbitrary _))
  calc |∫ y, h x y * g y| ≤ ∫ y, |h x y * g y| := abs_integral_le_integral_abs
    _ ≤ ∫ y, |h x y| * M := by
        refine integral_mono (H.row_mul_int hg hgb x).abs ((H.row_int x).abs.mul_const M) fun y => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hgb y) (abs_nonneg _)
    _ = (∫ y, |h x y|) * M := integral_mul_const _ _
    _ ≤ (a * ∫ z, G z) * M := mul_le_mul_of_nonneg_right (H.row_L1 x) h0


theorem prod_int (H : PairKer G h a) {F g : Torus d → ℝ} (hF : Measurable F) (hg : Measurable g) {MF Mg : ℝ}
    (hFb : ∀ x, |F x| ≤ MF) (hgb : ∀ y, |g y| ≤ Mg) :
    Integrable (fun p : Torus d × Torus d => h p.1 p.2 * F p.1 * g p.2)
      ((volume : Measure (Torus d)).prod volume) := by
  have hm : Measurable fun p : Torus d × Torus d => h p.1 p.2 * F p.1 * g p.2 :=
    (H.meas.mul (hF.comp measurable_fst)).mul (hg.comp measurable_snd)
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  have hF0 : (0 : ℝ) ≤ MF := (abs_nonneg _).trans (hFb (Classical.arbitrary _))
  have hg0 : (0 : ℝ) ≤ Mg := (abs_nonneg _).trans (hgb (Classical.arbitrary _))
  refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
  · have := (H.row_mul_int hg hgb x).mul_const (F x)
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only []
    ring
  · refine Integrable.of_bound (C := a * (∫ z, G z) * MF * Mg) ?_ (Eventually.of_forall fun x => ?_)
    · exact hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    · have hnn : 0 ≤ ∫ y, ‖h (x, y).1 (x, y).2 * F (x, y).1 * g (x, y).2‖ := integral_nonneg fun y => norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      calc ∫ y, ‖h (x, y).1 (x, y).2 * F (x, y).1 * g (x, y).2‖
          ≤ ∫ y, |h x y| * MF * Mg := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
              (((H.row_int x).abs.mul_const MF).mul_const Mg) (Eventually.of_forall fun y => ?_)
            simp only [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul (mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg _)) (hgb y) (abs_nonneg _)
              (mul_nonneg (abs_nonneg _) hF0)
        _ = (∫ y, |h x y|) * MF * Mg := by
            rw [integral_mul_const, integral_mul_const]
        _ ≤ a * (∫ z, G z) * MF * Mg := by
            gcongr
            exact H.row_L1 x


theorem realMode_meas (k : NonzeroLattice d) : Measurable (Torus.realMode k) :=
  (Torus.continuous_realMode k).measurable

theorem realMode_bdd (k : NonzeroLattice d) (x : Torus d) : |Torus.realMode k x| ≤ Real.sqrt 2 :=
  Torus.abs_realMode_le k x

theorem wickCoeff_eq (H : PairKer G h a) {μ : Measure (Torus d)} [IsFiniteMeasure μ] {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d))) (k l : NonzeroLattice d) :
    wickCoeff μ h k l = ∫ x, ∫ y, h x y * Torus.realMode k x * Torus.realMode l y := by
  set b : Torus d → ℝ := fun y => ∫ x', h x' y ∂μ with hb
  set A : Torus d → ℝ := fun x => ∫ y', h x y' ∂μ with hA
  set c : ℝ := ∫ x', ∫ y', h x' y' ∂μ ∂μ with hc
  have hb_meas : Measurable b := by
    have := H.meas.stronglyMeasurable.integral_prod_left' (μ := μ)
    exact this.measurable
  have hb_bd : ∀ y, |b y| ≤ Λ * (a * ∫ z, G z) := by
    intro y
    have hi : Integrable (fun x => |h x y|) (ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
      (H.col_int y).abs.smul_measure ENNReal.ofReal_ne_top
    calc |b y| ≤ ∫ x', |h x' y| ∂μ := by
          rw [← Real.norm_eq_abs]
          refine (norm_integral_le_integral_norm _).trans ?_
          simp only [Real.norm_eq_abs, le_refl]
      _ ≤ ∫ x', |h x' y| ∂(ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
          integral_mono_measure hμ (Eventually.of_forall fun _ => abs_nonneg _) hi
      _ = Λ * ∫ x', |h x' y| := by
          rw [integral_smul_measure, ENNReal.toReal_ofReal hΛ, smul_eq_mul]
      _ ≤ Λ * (a * ∫ z, G z) := mul_le_mul_of_nonneg_left (H.col_L1 y) hΛ
  set Bl : ℝ := ∫ y, b y * Torus.realMode l y with hBl
  have hbe : ∀ y, |b y * Torus.realMode l y| ≤ Λ * (a * ∫ z, G z) * Real.sqrt 2 := fun y => by
    rw [abs_mul]
    exact mul_le_mul (hb_bd y) (realMode_bdd l y) (abs_nonneg _) ((abs_nonneg _).trans (hb_bd y))
  have hbi : Integrable (fun y => b y * Torus.realMode l y) :=
    Integrable.of_bound (hb_meas.mul (realMode_meas l)).aestronglyMeasurable _
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hbe y)
  have hel : ∫ y, Torus.realMode l y = 0 := Torus.integral_realMode l
  have hek : ∫ x, Torus.realMode k x = 0 := Torus.integral_realMode k
  have hcontl : Integrable (Torus.realMode l) :=
    (Torus.continuous_realMode l).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hHl_meas := H.rowInt_meas (realMode_meas l)
  have hHl_bd := H.rowInt_bound (realMode_meas l) (realMode_bdd l)
  have inner : ∀ x, ∫ y, canonicalCenter μ h x y * Torus.realMode k x * Torus.realMode l y =
      Torus.realMode k x * (∫ y, h x y * Torus.realMode l y) - Torus.realMode k x * Bl := by
    intro x
    have e : (fun y => canonicalCenter μ h x y * Torus.realMode k x * Torus.realMode l y) =
        fun y => (Torus.realMode k x * (h x y * Torus.realMode l y) -
          (A x * Torus.realMode k x) * Torus.realMode l y) -
          (Torus.realMode k x * (b y * Torus.realMode l y) - (c * Torus.realMode k x) * Torus.realMode l y) := by
      funext y; unfold canonicalCenter; simp only [hA, hb, hc]; ring
    have i1 : Integrable (fun y => Torus.realMode k x * (h x y * Torus.realMode l y)) :=
      (H.row_mul_int (realMode_meas l) (realMode_bdd l) x).const_mul _
    have i2 : Integrable (fun y => (A x * Torus.realMode k x) * Torus.realMode l y) := hcontl.const_mul _
    have i3 : Integrable (fun y => Torus.realMode k x * (b y * Torus.realMode l y)) := hbi.const_mul _
    have i4 : Integrable (fun y => (c * Torus.realMode k x) * Torus.realMode l y) := hcontl.const_mul _
    have j1 : Integrable (fun y => Torus.realMode k x * (h x y * Torus.realMode l y) -
        (A x * Torus.realMode k x) * Torus.realMode l y) := i1.sub i2
    have j2 : Integrable (fun y => Torus.realMode k x * (b y * Torus.realMode l y) -
        (c * Torus.realMode k x) * Torus.realMode l y) := i3.sub i4
    rw [e, integral_sub j1 j2, integral_sub i1 i2, integral_sub i3 i4,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, hel]
    simp only [hBl]
    ring
  have outer : ∀ x, ∫ y, h x y * Torus.realMode k x * Torus.realMode l y =
      Torus.realMode k x * (∫ y, h x y * Torus.realMode l y) := by
    intro x
    rw [← integral_const_mul]
    congr 1; funext y; ring
  unfold wickCoeff
  simp_rw [inner, outer]
  have hint : Integrable (fun x => Torus.realMode k x * (∫ y, h x y * Torus.realMode l y)) := by
    refine Integrable.of_bound ((realMode_meas k).mul hHl_meas).aestronglyMeasurable
      (Real.sqrt 2 * (a * (∫ z, G z) * Real.sqrt 2)) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (realMode_bdd k x) (hHl_bd x) (abs_nonneg _) (Real.sqrt_nonneg _)
  have hcontk : Integrable (Torus.realMode k) :=
    (Torus.continuous_realMode k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_sub hint (hcontk.mul_const Bl), integral_mul_const, hek]
  ring


theorem wickCoeff_symm (H : PairKer G h a) (hsym : ∀ x y, h x y = h y x) {μ : Measure (Torus d)}
    [IsFiniteMeasure μ] {Λ : ℝ} (hΛ : 0 ≤ Λ) (hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)))
    (k l : NonzeroLattice d) : wickCoeff μ h k l = wickCoeff μ h l k := by
  rw [wickCoeff_eq H hΛ hμ, wickCoeff_eq H hΛ hμ]
  have hp := H.prod_int (realMode_meas k) (realMode_meas l) (realMode_bdd k) (realMode_bdd l)
  rw [integral_integral_swap hp]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only []
  rw [hsym y x]
  ring


/-- The finite Fourier partial sum. -/
def fsum (c : NonzeroLattice d → ℝ) (S : Finset (NonzeroLattice d)) (x : Torus d) : ℝ :=
  ∑ k ∈ S, c k * Torus.realMode k x

theorem fsum_meas (c : NonzeroLattice d → ℝ) (S : Finset (NonzeroLattice d)) : Measurable (fsum c S) := by
  unfold fsum
  exact Finset.measurable_sum _ fun k _ => (measurable_const.mul (realMode_meas k))

theorem fsum_bdd {c : NonzeroLattice d → ℝ} (hc : Summable fun k => |c k|) (S : Finset (NonzeroLattice d))
    (x : Torus d) : |fsum c S x| ≤ Real.sqrt 2 * ∑' k, |c k| := by
  unfold fsum
  calc |∑ k ∈ S, c k * Torus.realMode k x| ≤ ∑ k ∈ S, |c k * Torus.realMode k x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ S, |c k| * Real.sqrt 2 := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (realMode_bdd k x) (abs_nonneg _)
    _ = Real.sqrt 2 * ∑ k ∈ S, |c k| := by rw [← Finset.sum_mul, mul_comm]
    _ ≤ Real.sqrt 2 * ∑' k, |c k| := by
        gcongr
        exact hc.sum_le_tsum S (fun _ _ => abs_nonneg _)

theorem outer_eq (H : PairKer G h a) (k l : NonzeroLattice d) :
    ∫ x, ∫ y, h x y * Torus.realMode k x * Torus.realMode l y =
      ∫ x, Torus.realMode k x * ∫ y, h x y * Torus.realMode l y := by
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun y => by ring)

theorem hint_kl (H : PairKer G h a) (k l : NonzeroLattice d) :
    Integrable (fun x => Torus.realMode k x * ∫ y, h x y * Torus.realMode l y) := by
  refine Integrable.of_bound ((realMode_meas k).mul (H.rowInt_meas (realMode_meas l))).aestronglyMeasurable
    (Real.sqrt 2 * (a * (∫ z, G z) * Real.sqrt 2)) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (realMode_bdd k x) (H.rowInt_bound (realMode_meas l) (realMode_bdd l) x)
    (abs_nonneg _) (Real.sqrt_nonneg _)

theorem pair_limit (H : PairKer G h a) {χ χ' : Torus d → ℝ} (hχ : Continuous χ) (hχ' : Continuous χ')
    (hs : Summable fun k : Lattice d => ‖Torus.fcoef χ k‖) (hs' : Summable fun k : Lattice d => ‖Torus.fcoef χ' k‖)
    (hm : Torus.mean χ = 0) (hm' : Torus.mean χ' = 0) :
    Tendsto (fun S : Finset (NonzeroLattice d) => ∑ k ∈ S, ∑ l ∈ S,
        (∫ x, ∫ y, h x y * Torus.realMode k x * Torus.realMode l y) *
          (Torus.funRealCoeff χ k * Torus.funRealCoeff χ' l)) atTop
      (𝓝 (∫ x, ∫ y, h x y * χ x * χ' y)) := by
  set c : NonzeroLattice d → ℝ := fun k => Torus.funRealCoeff χ k with hcdef
  set e : NonzeroLattice d → ℝ := fun l => Torus.funRealCoeff χ' l with hedef
  have hint : Integrable χ := hχ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint' : Integrable χ' := hχ'.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcs := Torus.summable_norm_funRealCoeff hint hs
  have hes := Torus.summable_norm_funRealCoeff hint' hs'
  set M : ℝ := Real.sqrt 2 * ∑' k, |c k| with hM
  set M' : ℝ := Real.sqrt 2 * ∑' k, |e k| with hM'
  have hM0 : 0 ≤ M := mul_nonneg (Real.sqrt_nonneg _) (tsum_nonneg fun _ => abs_nonneg _)
  have hM0' : 0 ≤ M' := mul_nonneg (Real.sqrt_nonneg _) (tsum_nonneg fun _ => abs_nonneg _)
  have hf_tend : ∀ x, Tendsto (fun S => fsum c S x) atTop (𝓝 (χ x)) := by
    intro x
    have := Torus.hasSum_realExpansion hχ hs x
    rw [hm, sub_zero] at this
    exact this
  have hg_tend : ∀ y, Tendsto (fun S => fsum e S y) atTop (𝓝 (χ' y)) := by
    intro y
    have := Torus.hasSum_realExpansion hχ' hs' y
    rw [hm', sub_zero] at this
    exact this
  -- step 1: the finite sums as iterated integrals
  have step1 : ∀ S : Finset (NonzeroLattice d), ∑ k ∈ S, ∑ l ∈ S,
        (∫ x, ∫ y, h x y * Torus.realMode k x * Torus.realMode l y) * (c k * e l) =
      ∫ x, fsum c S x * ∫ y, h x y * fsum e S y := by
    intro S
    have e1 : ∀ x, fsum c S x * ∫ y, h x y * fsum e S y =
        ∑ k ∈ S, ∑ l ∈ S, (c k * e l) * (Torus.realMode k x * ∫ y, h x y * Torus.realMode l y) := by
      intro x
      have hin : ∫ y, h x y * fsum e S y = ∑ l ∈ S, e l * ∫ y, h x y * Torus.realMode l y := by
        have hfun : (fun y => h x y * fsum e S y) = fun y => ∑ l ∈ S, e l * (h x y * Torus.realMode l y) := by
          funext y; unfold fsum; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
        rw [hfun, integral_finset_sum _ (fun l _ =>
          (H.row_mul_int (realMode_meas l) (realMode_bdd l) x).const_mul (e l))]
        exact Finset.sum_congr rfl fun l _ => by rw [integral_const_mul]
      rw [hin]; unfold fsum; rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    rw [integral_congr_ae (Eventually.of_forall e1), integral_finset_sum _ (fun k _ =>
      integrable_finset_sum _ (fun l _ => (H.hint_kl k l).const_mul _))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finset_sum _ (fun l _ => (H.hint_kl k l).const_mul _)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, H.outer_eq k l]
    ring
  refine (tendsto_congr step1).mpr ?_
  have hI_meas : ∀ S, Measurable fun x => ∫ y, h x y * fsum e S y := fun S => H.rowInt_meas (fsum_meas e S)
  have hI_bd : ∀ S x, |∫ y, h x y * fsum e S y| ≤ a * (∫ z, G z) * M' :=
    fun S x => H.rowInt_bound (fsum_meas e S) (fsum_bdd hes S) x
  have hinner : ∀ x, Tendsto (fun S => ∫ y, h x y * fsum e S y) atTop (𝓝 (∫ y, h x y * χ' y)) := by
    intro x
    refine tendsto_integral_filter_of_dominated_convergence (fun y => |h x y| * M') ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun S => ((H.row_meas x).mul (fsum_meas e S)).aestronglyMeasurable
    · refine Eventually.of_forall fun S => Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (fsum_bdd hes S y) (abs_nonneg _)
    · exact (H.row_int x).abs.mul_const _
    · exact Eventually.of_forall fun y => (hg_tend y).const_mul _
  have hmain := tendsto_integral_filter_of_dominated_convergence (fun _ : Torus d => M * (a * (∫ z, G z) * M'))
    (μ := (volume : Measure (Torus d))) (l := (atTop : Filter (Finset (NonzeroLattice d))))
    (F := fun S x => fsum c S x * ∫ y, h x y * fsum e S y)
    (f := fun x => χ x * ∫ y, h x y * χ' y) ?_ ?_ ?_ ?_
  · have hfin : ∫ x, ∫ y, h x y * χ x * χ' y = ∫ x, χ x * ∫ y, h x y * χ' y := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun y => by ring)
    rw [hfin]; exact hmain
  · exact Eventually.of_forall fun S => ((fsum_meas c S).mul (hI_meas S)).aestronglyMeasurable
  · refine Eventually.of_forall fun S => Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (fsum_bdd hcs S x) (hI_bd S x) (abs_nonneg _) hM0
  · exact integrable_const _
  · exact Eventually.of_forall fun x => (hf_tend x).mul (hinner x)

end PairKer

end HRS.MC.E213U18

end
