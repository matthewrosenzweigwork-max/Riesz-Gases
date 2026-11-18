import HRS.MS.LpDissDefs
import HRS.MS.CzElemBAux1

/-!
# S.A.16.C1: quantitative vector power convexity

`sa16bd_power_bregman`: for `p ≥ 2` the Bregman divergence of `v ↦ |v|^p / p` dominates
`(4^(2-p)/32) (|a|+|b|)^(p-2) |a-b|²`.  Proof: regularize to `(|v|²+η²)^(p/2)/p`, apply a
one-dimensional second order Taylor lower bound on the segment, and let `η → 0`.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open HRS HRS.Whole HRS.Whole.AppendixA

universe u

namespace HRS.Whole.AppendixA.BreakdownSA16

/-! ### a one-dimensional second order lower bound -/

lemma sa16bd_taylor_lower (G G1 G2 : ℝ → ℝ) (hG : ∀ t, HasDerivAt G (G1 t) t)
    (hG1 : ∀ t, HasDerivAt G1 (G2 t) t) (h0 : ∀ t, 0 ≤ G2 t) {α β K : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1) (hK : ∀ t ∈ Set.Icc α β, K ≤ G2 t) :
    K * (β - α) ^ 2 / 2 ≤ G 1 - G 0 - G1 0 := by
  have hG1mono : Monotone G1 := monotone_of_deriv_nonneg (fun t => (hG1 t).differentiableAt)
    (fun t => by rw [(hG1 t).deriv]; exact h0 t)
  set u : ℝ → ℝ := fun t => G t - G 0 - t * G1 0 with hu
  have hu' : ∀ t, HasDerivAt u (G1 t - G1 0) t := by
    intro t
    have := ((hG t).sub_const (G 0)).sub ((hasDerivAt_id t).mul_const (G1 0))
    exact this.congr_deriv (by ring)
  have humono : MonotoneOn u (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact fun t _ => (hu' t).continuousAt.continuousWithinAt
    · exact fun t _ => (hu' t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hu' t).deriv]
      have := hG1mono ht.1.le
      linarith
  set w : ℝ → ℝ := fun t => u t - K * (t - α) ^ 2 / 2 with hw
  have hw' : ∀ t, HasDerivAt w (G1 t - G1 0 - K * (t - α)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => K * (t - α) ^ 2 / 2) (K * (t - α)) t := by
      have := (((hasDerivAt_id t).sub_const α).pow 2).const_mul K |>.div_const 2
      exact this.congr_deriv (by simp; ring)
    exact (hu' t).sub h1
  have hMVT := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc α β)
    (f := G1) (C := K)
    (fun t _ => (hG1 t).continuousAt.continuousWithinAt)
    (fun t _ => (hG1 t).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [interior_Icc] at ht
      rw [(hG1 t).deriv]
      exact hK t ⟨ht.1.le, ht.2.le⟩)
  have hwmono : MonotoneOn w (Set.Icc α β) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc α β)
    · exact fun t _ => (hw' t).continuousAt.continuousWithinAt
    · exact fun t _ => (hw' t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hw' t).deriv]
      have h1 := hMVT α ⟨le_refl _, hαβ⟩ t ⟨ht.1.le, ht.2.le⟩ ht.1.le
      have h2 := hG1mono (show (0:ℝ) ≤ α from hα)
      have h3 := hG1mono (show α ≤ t from ht.1.le)
      linarith
  have e1 : u 0 = 0 := by simp [hu]
  have e2 : u 1 = G 1 - G 0 - G1 0 := by simp [hu]
  have s1 : u 0 ≤ u α := humono ⟨le_refl _, zero_le_one⟩ ⟨hα, hαβ.trans hβ⟩ hα
  have s2 : u β ≤ u 1 := humono ⟨hα.trans hαβ, hβ⟩ ⟨zero_le_one, le_refl _⟩ hβ
  have s3 : w α ≤ w β := hwmono ⟨le_refl _, hαβ⟩ ⟨hαβ, le_refl _⟩ hαβ
  have wα : w α = u α := by simp [hw]
  have wβ : w β = u β - K * (β - α) ^ 2 / 2 := rfl
  linarith

/-! ### `vnorm` as a Euclidean norm -/

lemma sa16bd_vnorm_eq_norm {ι : Type u} [Fintype ι] (v : ι → ℝ) :
    vnorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [vnorm, Real.norm_eq_abs, sq_abs]

lemma sa16bd_vnorm_le {ι : Type u} [Fintype ι] (x y z : ι → ℝ) (c : ℝ)
    (h : ∀ i, x i = y i + c * z i) : vnorm x ≤ vnorm y + |c| * vnorm z := by
  have hx : (WithLp.toLp 2 x : EuclideanSpace ℝ ι) =
      (WithLp.toLp 2 y : EuclideanSpace ℝ ι) + c • (WithLp.toLp 2 z : EuclideanSpace ℝ ι) := by
    ext i
    simp [h i]
  rw [sa16bd_vnorm_eq_norm, sa16bd_vnorm_eq_norm, sa16bd_vnorm_eq_norm, hx]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]

lemma sa16bd_vnorm_sq {ι : Type u} [Fintype ι] (v : ι → ℝ) : vnorm v ^ 2 = ∑ i, v i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

lemma sa16bd_vnorm_rpow {ι : Type u} [Fintype ι] (v : ι → ℝ) (q : ℝ) :
    vnorm v ^ q = (∑ i, v i ^ 2) ^ (q / 2) := by
  unfold vnorm
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  congr 1
  ring

/-! ### the regularized potential along a segment -/

/-- the regularized squared radius at `a + t (b - a)` -/
def sa16bd_S {ι : Type u} [Fintype ι] (a b : ι → ℝ) (η t : ℝ) : ℝ :=
  ∑ i, (a i + t * (b i - a i)) ^ 2 + η ^ 2

/-- the directional derivative `v(t) · h` -/
def sa16bd_D {ι : Type u} [Fintype ι] (a b : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, (a i + t * (b i - a i)) * (b i - a i)

lemma sa16bd_S_pos {ι : Type u} [Fintype ι] (a b : ι → ℝ) {η : ℝ} (hη : 0 < η) (t : ℝ) :
    0 < sa16bd_S a b η t := by
  unfold sa16bd_S
  have : 0 ≤ ∑ i, (a i + t * (b i - a i)) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  positivity

lemma sa16bd_S_deriv {ι : Type u} [Fintype ι] (a b : ι → ℝ) (η t : ℝ) :
    HasDerivAt (sa16bd_S a b η) (2 * sa16bd_D a b t) t := by
  have h1 : ∀ i ∈ (Finset.univ : Finset ι),
      HasDerivAt (fun t : ℝ => (a i + t * (b i - a i)) ^ 2)
        (2 * ((a i + t * (b i - a i)) * (b i - a i))) t := by
    intro i _
    have := (((hasDerivAt_id t).mul_const (b i - a i)).const_add (a i)).pow 2
    exact this.congr_deriv (by simp; ring)
  have h2 := (HasDerivAt.fun_sum h1).add_const (η ^ 2)
  unfold sa16bd_S sa16bd_D
  rw [Finset.mul_sum]
  exact h2

/-- first derivative of the regularized potential -/
def sa16bd_G1 {ι : Type u} [Fintype ι] (a b : ι → ℝ) (p η t : ℝ) : ℝ :=
  sa16bd_S a b η t ^ (p / 2 - 1) * sa16bd_D a b t

/-- second derivative of the regularized potential -/
def sa16bd_G2 {ι : Type u} [Fintype ι] (a b : ι → ℝ) (p η t : ℝ) : ℝ :=
  (2 * sa16bd_D a b t) * (p / 2 - 1) * sa16bd_S a b η t ^ (p / 2 - 1 - 1) * sa16bd_D a b t +
    sa16bd_S a b η t ^ (p / 2 - 1) * ∑ i, (b i - a i) * (b i - a i)

lemma sa16bd_G_deriv {ι : Type u} [Fintype ι] (a b : ι → ℝ) {p : ℝ} (hp : 2 ≤ p) {η : ℝ}
    (hη : 0 < η) (t : ℝ) :
    HasDerivAt (fun t => sa16bd_S a b η t ^ (p / 2) / p) (sa16bd_G1 a b p η t) t := by
  have h := ((sa16bd_S_deriv a b η t).rpow_const (p := p / 2)
    (Or.inl (sa16bd_S_pos a b hη t).ne')).div_const p
  convert h using 1
  unfold sa16bd_G1
  have hp0 : p ≠ 0 := by linarith
  field_simp

lemma sa16bd_G1_deriv {ι : Type u} [Fintype ι] (a b : ι → ℝ) {p : ℝ} {η : ℝ}
    (hη : 0 < η) (t : ℝ) :
    HasDerivAt (sa16bd_G1 a b p η) (sa16bd_G2 a b p η t) t := by
  have hD : HasDerivAt (sa16bd_D a b) (∑ i, (b i - a i) * (b i - a i)) t := by
    have h1 : ∀ i ∈ (Finset.univ : Finset ι),
        HasDerivAt (fun t : ℝ => (a i + t * (b i - a i)) * (b i - a i))
          ((b i - a i) * (b i - a i)) t := by
      intro i _
      have := (((hasDerivAt_id t).mul_const (b i - a i)).const_add (a i)).mul_const (b i - a i)
      simpa using this
    exact HasDerivAt.fun_sum h1
  have hS := (sa16bd_S_deriv a b η t).rpow_const (p := p / 2 - 1)
    (Or.inl (sa16bd_S_pos a b hη t).ne')
  have := hS.mul hD
  unfold sa16bd_G1 sa16bd_G2
  convert this using 1

lemma sa16bd_G2_nonneg {ι : Type u} [Fintype ι] (a b : ι → ℝ) {p : ℝ} (hp : 2 ≤ p) {η : ℝ}
    (hη : 0 < η) (t : ℝ) :
    sa16bd_S a b η t ^ (p / 2 - 1) * ∑ i, (b i - a i) * (b i - a i) ≤ sa16bd_G2 a b p η t := by
  unfold sa16bd_G2
  have hS := sa16bd_S_pos a b hη t
  have h1 : 0 ≤ (2 * sa16bd_D a b t) * (p / 2 - 1) * sa16bd_S a b η t ^ (p / 2 - 1 - 1) *
      sa16bd_D a b t := by
    have : 0 ≤ sa16bd_S a b η t ^ (p / 2 - 1 - 1) := Real.rpow_nonneg hS.le _
    have h2 : 0 ≤ p / 2 - 1 := by linarith
    have : (2 * sa16bd_D a b t) * (p / 2 - 1) * sa16bd_S a b η t ^ (p / 2 - 1 - 1) *
        sa16bd_D a b t = 2 * (p / 2 - 1) * sa16bd_S a b η t ^ (p / 2 - 1 - 1) *
          sa16bd_D a b t ^ 2 := by ring
    rw [this]
    positivity
  linarith

lemma sa16bd_G2_nonneg' {ι : Type u} [Fintype ι] (a b : ι → ℝ) {p : ℝ} (hp : 2 ≤ p) {η : ℝ}
    (hη : 0 < η) (t : ℝ) : 0 ≤ sa16bd_G2 a b p η t := by
  refine le_trans ?_ (sa16bd_G2_nonneg a b hp hη t)
  have := sa16bd_S_pos a b hη t
  have h2 : 0 ≤ ∑ i, (b i - a i) * (b i - a i) := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  positivity

/-- a pointwise lower bound on the segment gives a lower bound on `G2` -/
lemma sa16bd_G2_lower {ι : Type u} [Fintype ι] (a b : ι → ℝ) {p : ℝ} (hp : 2 ≤ p) {η : ℝ}
    (hη : 0 < η) {r : ℝ} (hr : 0 ≤ r) (t : ℝ)
    (ht : r ≤ vnorm (fun i => a i + t * (b i - a i))) :
    r ^ (p - 2) * ∑ i, (b i - a i) * (b i - a i) ≤ sa16bd_G2 a b p η t := by
  refine le_trans ?_ (sa16bd_G2_nonneg a b hp hη t)
  have h2 : 0 ≤ ∑ i, (b i - a i) * (b i - a i) := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  refine mul_le_mul_of_nonneg_right ?_ h2
  have hS : r ^ 2 ≤ sa16bd_S a b η t := by
    unfold sa16bd_S
    have h3 : r ^ 2 ≤ vnorm (fun i => a i + t * (b i - a i)) ^ 2 := by gcongr
    rw [sa16bd_vnorm_sq] at h3
    nlinarith [sq_nonneg η]
  have h4 : (r ^ 2) ^ (p / 2 - 1) ≤ sa16bd_S a b η t ^ (p / 2 - 1) :=
    Real.rpow_le_rpow (by positivity) hS (by linarith)
  have h5 : (r ^ 2) ^ (p / 2 - 1) = r ^ (p - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
    congr 1
    push_cast
    ring
  rwa [h5] at h4

/-! ### the regularized inequality -/

lemma sa16bd_reg_bregman {ι : Type u} [Fintype ι] (a b : ι → ℝ) {p : ℝ} (hp : 2 ≤ p) {η : ℝ}
    (hη : 0 < η) :
    ((vnorm a + vnorm b) / 4) ^ (p - 2) * (∑ i, (b i - a i) * (b i - a i)) / 32 ≤
      (∑ i, b i ^ 2 + η ^ 2) ^ (p / 2) / p - (∑ i, a i ^ 2 + η ^ 2) ^ (p / 2) / p -
        sa16bd_G1 a b p η 0 := by
  set R := vnorm a + vnorm b with hR
  have hRa : 0 ≤ vnorm a := Real.sqrt_nonneg _
  have hRb : 0 ≤ vnorm b := Real.sqrt_nonneg _
  have hR0 : 0 ≤ R / 4 := by rw [hR]; positivity
  have hh : vnorm (fun i => b i - a i) ≤ R := by
    have := sa16bd_vnorm_le (fun i => b i - a i) b a (-1) (fun i => by ring)
    simpa [hR, add_comm] using this
  have hg0 : ∀ t, HasDerivAt (fun t => sa16bd_S a b η t ^ (p / 2) / p) (sa16bd_G1 a b p η t) t :=
    sa16bd_G_deriv a b hp hη
  have hg1 : ∀ t, HasDerivAt (sa16bd_G1 a b p η) (sa16bd_G2 a b p η t) t :=
    sa16bd_G1_deriv a b hη
  have hnn := sa16bd_G2_nonneg' a b hp hη
  have hS0 : sa16bd_S a b η 0 = ∑ i, a i ^ 2 + η ^ 2 := by simp [sa16bd_S]
  have hS1 : sa16bd_S a b η 1 = ∑ i, b i ^ 2 + η ^ 2 := by simp [sa16bd_S]
  set K := (R / 4) ^ (p - 2) * ∑ i, (b i - a i) * (b i - a i) with hK
  have hK0 : 0 ≤ K := mul_nonneg (Real.rpow_nonneg hR0 _)
    (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  have key : ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 1 →
      (∀ t ∈ Set.Icc α β, R / 4 ≤ vnorm (fun i => a i + t * (b i - a i))) →
      K * (β - α) ^ 2 / 2 ≤ (∑ i, b i ^ 2 + η ^ 2) ^ (p / 2) / p -
        (∑ i, a i ^ 2 + η ^ 2) ^ (p / 2) / p - sa16bd_G1 a b p η 0 := by
    intro α β hα hαβ hβ hlow
    have := sa16bd_taylor_lower _ _ _ hg0 hg1 hnn hα hαβ hβ
      (fun t ht => sa16bd_G2_lower a b hp hη hR0 t (hlow t ht))
    simpa [hS0, hS1] using this
  by_cases hcase : R / 2 ≤ vnorm a
  · have := key 0 (1 / 4) (le_refl _) (by norm_num) (by norm_num) (by
      intro t ht
      have h1 := sa16bd_vnorm_le a (fun i => a i + t * (b i - a i)) (fun i => b i - a i) (-t)
        (fun i => by ring)
      have h2 : |(-t)| = t := by rw [abs_neg, abs_of_nonneg ht.1]
      rw [h2] at h1
      have h3 : t * vnorm (fun i => b i - a i) ≤ 1 / 4 * R := by
        calc t * vnorm (fun i => b i - a i) ≤ t * R := by
                exact mul_le_mul_of_nonneg_left hh ht.1
          _ ≤ 1 / 4 * R := by
                have : 0 ≤ R := add_nonneg hRa hRb
                nlinarith [ht.2]
      linarith)
    refine le_trans ?_ this
    nlinarith [hK0]
  · have hcase' : R / 2 ≤ vnorm b := by
      simp only [hR] at *
      linarith [not_le.mp hcase]
    have := key (3 / 4) 1 (by norm_num) (by norm_num) (le_refl _) (by
      intro t ht
      have h1 := sa16bd_vnorm_le b (fun i => a i + t * (b i - a i)) (fun i => b i - a i) (1 - t)
        (fun i => by ring)
      have h2 : |(1 - t)| = 1 - t := abs_of_nonneg (by linarith [ht.2])
      rw [h2] at h1
      have h3 : (1 - t) * vnorm (fun i => b i - a i) ≤ 1 / 4 * R := by
        calc (1 - t) * vnorm (fun i => b i - a i) ≤ (1 - t) * R := by
                exact mul_le_mul_of_nonneg_left hh (by linarith [ht.2])
          _ ≤ 1 / 4 * R := by
                have : 0 ≤ R := add_nonneg hRa hRb
                nlinarith [ht.1]
      linarith)
    refine le_trans ?_ this
    nlinarith [hK0]

/-! ### the limit `η → 0` -/

lemma sa16bd_cont_rpow {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) :
    ContinuousAt (fun η : ℝ => (x + η ^ 2) ^ r) 0 := by
  have h : ContinuousAt (fun η : ℝ => x + η ^ 2) 0 := by fun_prop
  exact h.rpow_const (Or.inr hr)

theorem sa16bd_power_bregman {ι : Type u} [Fintype ι] (p : ℝ) (hp : 2 ≤ p)
    (a b : ι → ℝ) :
    0 < sa16bd_convexityConst p ∧
      sa16bd_convexityConst p * (vnorm a + vnorm b) ^ (p - 2) *
          vnorm (fun i => a i - b i) ^ 2 ≤
        vnorm a ^ (p - 2) * (∑ i, a i * (a i - b i)) -
          (vnorm a ^ p - vnorm b ^ p) / p := by
  refine ⟨by unfold sa16bd_convexityConst; positivity, ?_⟩
  have hp0 : 0 < p := by linarith
  set Fn : ℝ → ℝ := fun η =>
    (∑ i, b i ^ 2 + η ^ 2) ^ (p / 2) / p - (∑ i, a i ^ 2 + η ^ 2) ^ (p / 2) / p +
      (∑ i, a i ^ 2 + η ^ 2) ^ (p / 2 - 1) * ∑ i, a i * (a i - b i) with hFn
  have hcont : ContinuousAt Fn 0 := by
    have hb := sa16bd_cont_rpow (x := ∑ i, b i ^ 2) (r := p / 2)
      (Finset.sum_nonneg fun i _ => sq_nonneg _) (by linarith)
    have ha := sa16bd_cont_rpow (x := ∑ i, a i ^ 2) (r := p / 2)
      (Finset.sum_nonneg fun i _ => sq_nonneg _) (by linarith)
    have ha' := sa16bd_cont_rpow (x := ∑ i, a i ^ 2) (r := p / 2 - 1)
      (Finset.sum_nonneg fun i _ => sq_nonneg _) (by linarith)
    exact ((hb.div_const p).sub (ha.div_const p)).add (ha'.mul continuousAt_const)
  have hlim : Tendsto Fn (𝓝[>] 0) (𝓝 (Fn 0)) :=
    (hcont.tendsto).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      ((vnorm a + vnorm b) / 4) ^ (p - 2) * (∑ i, (b i - a i) * (b i - a i)) / 32 ≤ Fn η := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    have := sa16bd_reg_bregman a b hp (Set.mem_Ioi.mp hη)
    have hG : sa16bd_G1 a b p η 0 = -((∑ i, a i ^ 2 + η ^ 2) ^ (p / 2 - 1) * ∑ i, a i * (a i - b i)) := by
      unfold sa16bd_G1 sa16bd_D sa16bd_S
      simp only [zero_mul, add_zero]
      rw [← mul_neg, ← Finset.sum_neg_distrib]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hG] at this
    simp only [hFn]
    linarith
  have hge := ge_of_tendsto hlim hev
  have hRa := Real.sqrt_nonneg (∑ i, a i ^ 2)
  have e1 : Fn 0 = vnorm b ^ p / p - vnorm a ^ p / p + vnorm a ^ (p - 2) * ∑ i, a i * (a i - b i) := by
    simp only [hFn, sa16bd_vnorm_rpow]
    simp only [zero_pow two_ne_zero, add_zero]
    have : p / 2 - 1 = (p - 2) / 2 := by ring
    rw [this]
  have e2 : ((vnorm a + vnorm b) / 4) ^ (p - 2) = (vnorm a + vnorm b) ^ (p - 2) *
      (4 : ℝ) ^ (2 - p) := by
    have hnn : 0 ≤ vnorm a + vnorm b := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.div_rpow hnn (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
    congr 2
    ring
  have e3 : ∑ i, (b i - a i) * (b i - a i) = vnorm (fun i => a i - b i) ^ 2 := by
    rw [sa16bd_vnorm_sq]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, e3] at hge
  unfold sa16bd_convexityConst
  have : vnorm b ^ p / p - vnorm a ^ p / p = -((vnorm a ^ p - vnorm b ^ p) / p) := by ring
  nlinarith [hge, this]

end HRS.Whole.AppendixA.BreakdownSA16
