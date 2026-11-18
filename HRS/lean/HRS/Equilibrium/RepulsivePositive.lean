/-
# HRS.Equilibrium.RepulsivePositive — package REP-04: Fourier positivity and the deterministic cap

A kernel `f(x) = ∑_k c_k cos(2πk·x)` with `c_k ≥ 0` summable is bounded by `∑ c_k`, positive
definite (`∑_{i,j} w_i w_j f(x_i - x_j) = ∑_k c_k |∑_i w_i e_k(x_i)|² ≥ 0`), and the centred
kernel `f̃` satisfies `|f̃| ≤ 4 ∑ c_k` and `-∑_{i≠j} f̃(x_i,x_j) ≤ ∑_i f̃(x_i,x_i) ≤ 4N ∑ c_k`,
i.e. `iidNeg_N(f̃) ≤ 2 ∑ c_k`.  Applied to the band this gives the `L^∞` bound and the
deterministic cap (M2) of the master kernel (DGR `lem:logLargeScaleCancellation`(i),
eq:logEtaNu), and to the tail the bound `iidNeg_N((heatTail)~) ≤ 2 heatTail d b 0` that replaces
the Euclidean infrared pairing argument.

`sorry`-ed specifications; see `docs/REPULSIVE_PLAN.md` (REP-04).
-/
import HRS.Equilibrium.RepulsiveBridge
import HRS.Equilibrium.RepulsiveBand

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Repulsive

variable {d : ℕ}

/-! ### Auxiliary identities (REP-04) -/

/-- Addition formula for the cosine mode: `cos(k·(x-y)) = cos(k·x)cos(k·y) + sin(k·x)sin(k·y)`. -/
theorem rp04_cosMode_sub (k : Lattice d) (x y : Torus d) :
    Torus.cosMode k (x - y) = Torus.cosMode k x * Torus.cosMode k y +
      Torus.sinMode k x * Torus.sinMode k y := by
  have hadd : ∀ u v : Torus d, Torus.mode k (u + v) = Torus.mode k u * Torus.mode k v := by
    intro u v
    unfold Torus.mode UnitAddTorus.mFourier
    simp only [ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, smul_add,
      AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]
  have hn : Torus.mode k y * (starRingEnd ℂ) (Torus.mode k y) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Torus.norm_mode]
    simp
  have h1 : Torus.mode k x = Torus.mode k (x - y) * Torus.mode k y := by
    rw [← hadd]
    simp
  have h2 : Torus.mode k (x - y) = Torus.mode k x * (starRingEnd ℂ) (Torus.mode k y) := by
    calc Torus.mode k (x - y)
        = Torus.mode k (x - y) * (Torus.mode k y * (starRingEnd ℂ) (Torus.mode k y)) := by
          rw [hn, mul_one]
      _ = Torus.mode k x * (starRingEnd ℂ) (Torus.mode k y) := by rw [h1]; ring
  unfold Torus.cosMode Torus.sinMode
  rw [h2]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Sum of squares over a double finite sum. -/
theorem rp04_sum_sum_sq {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    ∑ i, ∑ j, (u i * u j + v i * v j) = (∑ i, u i) ^ 2 + (∑ i, v i) ^ 2 := by
  simp only [sq, Finset.sum_mul_sum, Finset.sum_add_distrib]

/-- Exchange of a double finite sum with a `∑'` over the index `k`. -/
theorem rp04_tsum_comm {ι β : Type*} [Fintype ι] (T : ι → ι → β → ℝ)
    (hT : ∀ i j, Summable (T i j)) :
    ∑ i, ∑ j, ∑' k, T i j k = ∑' k, ∑ i, ∑ j, T i j k := by
  calc ∑ i, ∑ j, ∑' k, T i j k = ∑ i, ∑' k, ∑ j, T i j k :=
        Finset.sum_congr rfl fun i _ => (Summable.tsum_finsetSum fun j _ => hT i j).symm
    _ = ∑' k, ∑ i, ∑ j, T i j k :=
        (Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hT i j).symm

theorem rp04_norm_mul {u v p q : ℝ} (hu : ‖u‖ ≤ p) (hv : ‖v‖ ≤ q) (hp : 0 ≤ p) :
    ‖u * v‖ ≤ p * q := by
  rw [norm_mul]
  exact mul_le_mul hu hv (norm_nonneg _) hp

theorem rp04_norm_add {u v p q : ℝ} (hu : ‖u‖ ≤ p) (hv : ‖v‖ ≤ q) : ‖u + v‖ ≤ p + q :=
  (norm_add_le u v).trans (add_le_add hu hv)

theorem rp04_norm_sub {u v p q : ℝ} (hu : ‖u‖ ≤ p) (hv : ‖v‖ ≤ q) : ‖u - v‖ ≤ p + q :=
  (norm_sub_le u v).trans (add_le_add hu hv)

/-! ### Generic statements for nonnegative cosine series -/

section Generic

variable (c : Lattice d → ℝ) (hc : ∀ k, 0 ≤ c k) (hs : Summable c)
include hc hs

/-- Each term `c_k cos(2πk·x)` of a nonnegative cosine series is dominated by `c_k`. -/
theorem rp04_norm_le (k : Lattice d) (x : Torus d) : ‖c k * Torus.cosMode k x‖ ≤ c k := by
  rw [norm_mul, Real.norm_of_nonneg (hc k)]
  exact mul_le_of_le_one_right (hc k) (Torus.norm_cosMode_le k x)

/-- `∑_k c_k φ_k` is summable when `‖φ_k‖ ≤ K`. -/
theorem rp04_summable (φ : Lattice d → ℝ) (K : ℝ) (hK : ∀ k, ‖φ k‖ ≤ K) :
    Summable fun k : Lattice d => c k * φ k :=
  Summable.of_norm_bounded (hs.mul_right K) fun k => by
    rw [norm_mul, Real.norm_of_nonneg (hc k)]
    exact mul_le_mul_of_nonneg_left (hK k) (hc k)

theorem abs_tsum_cosMode_le (x : Torus d) :
    |∑' k : Lattice d, c k * Torus.cosMode k x| ≤ ∑' k : Lattice d, c k := by
  have hb : ∀ k, ‖c k * Torus.cosMode k x‖ ≤ c k := fun k => rp04_norm_le c hc hs k x
  have hn : Summable fun k : Lattice d => ‖c k * Torus.cosMode k x‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hb hs
  rw [← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hn).trans (Summable.tsum_le_tsum hb hn hs)

/-- Positive definiteness of a nonnegative cosine series on finitely many points. -/
theorem gram_nonneg {N : ℕ} (X : Config d N) (w : Fin N → ℝ) :
    0 ≤ ∑ i, ∑ j, w i * w j * ∑' k : Lattice d, c k * Torus.cosMode k (X i - X j) := by
  have hterm : ∀ i j, w i * w j * ∑' k : Lattice d, c k * Torus.cosMode k (X i - X j)
      = ∑' k : Lattice d, w i * w j * (c k * Torus.cosMode k (X i - X j)) := fun i j =>
    tsum_mul_left.symm
  have hsum : ∀ i j, Summable fun k : Lattice d =>
      w i * w j * (c k * Torus.cosMode k (X i - X j)) := fun i j =>
    Summable.of_norm_bounded (hs.mul_left ‖w i * w j‖) fun k => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (rp04_norm_le c hc hs k _) (norm_nonneg _)
  have hkey : ∀ k : Lattice d, ∑ i, ∑ j, w i * w j * (c k * Torus.cosMode k (X i - X j))
      = c k * ((∑ i, w i * Torus.cosMode k (X i)) ^ 2 + (∑ i, w i * Torus.sinMode k (X i)) ^ 2) := by
    intro k
    have e : ∀ i j, w i * w j * (c k * Torus.cosMode k (X i - X j)) = c k *
        ((w i * Torus.cosMode k (X i)) * (w j * Torus.cosMode k (X j)) +
          (w i * Torus.sinMode k (X i)) * (w j * Torus.sinMode k (X j))) := fun i j => by
      rw [rp04_cosMode_sub]
      ring
    simp only [e, ← Finset.mul_sum, rp04_sum_sum_sq]
  have hrw : ∑ i, ∑ j, w i * w j * ∑' k : Lattice d, c k * Torus.cosMode k (X i - X j)
      = ∑' k : Lattice d, ∑ i, ∑ j, w i * w j * (c k * Torus.cosMode k (X i - X j)) := by
    simp only [hterm]
    exact rp04_tsum_comm (fun i j k => w i * w j * (c k * Torus.cosMode k (X i - X j))) hsum
  rw [hrw]
  refine tsum_nonneg fun k => ?_
  rw [hkey k]
  exact mul_nonneg (hc k) (by positivity)

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {f : Torus d → ℝ}
  (hf : ∀ x, f x = ∑' k : Lattice d, c k * Torus.cosMode k x)
include hf

theorem abs_convMeasure_le_tsum (x : Torus d) : |convMeasure f μ x| ≤ ∑' k : Lattice d, c k := by
  have hB : ∀ z, ‖f z‖ ≤ ∑' k : Lattice d, c k := fun z => by
    rw [Real.norm_eq_abs, hf z]
    exact abs_tsum_cosMode_le c hc hs z
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => f (x - y))
    (C := ∑' k : Lattice d, c k) (Filter.Eventually.of_forall fun y => hB (x - y))
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact h

theorem abs_energyPairing_le_tsum : |energyPairing f μ μ| ≤ ∑' k : Lattice d, c k := by
  have hC : ∀ x, ‖convMeasure f μ x‖ ≤ ∑' k : Lattice d, c k := fun x => by
    rw [Real.norm_eq_abs]
    exact abs_convMeasure_le_tsum c hc hs hf x
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => convMeasure f μ x)
    (C := ∑' k : Lattice d, c k) (Filter.Eventually.of_forall hC)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact h

/-- `|f̃(x,y)| ≤ 4 ∑ c_k`. -/
theorem abs_pairKernel_le_tsum (x y : Torus d) :
    |pairKernel f μ (x, y)| ≤ 4 * ∑' k : Lattice d, c k := by
  have hf1 : ∀ z, |f z| ≤ ∑' k : Lattice d, c k := fun z => by
    rw [hf z]
    exact abs_tsum_cosMode_le c hc hs z
  obtain ⟨a1, a2⟩ := abs_le.mp (hf1 (x - y))
  obtain ⟨b1, b2⟩ := abs_le.mp (abs_convMeasure_le_tsum (μ := μ) c hc hs hf x)
  obtain ⟨e1, e2⟩ := abs_le.mp (abs_convMeasure_le_tsum (μ := μ) c hc hs hf y)
  obtain ⟨g1, g2⟩ := abs_le.mp (abs_energyPairing_le_tsum (μ := μ) c hc hs hf)
  simp only [pairKernel, centeredKernel]
  rw [abs_le]
  constructor <;> linarith

/-- Positive definiteness of the centred kernel against the empirical measure:
`∑_{i,j} f̃(x_i, x_j) = ∬ f d(ν_N - Nμ) d(ν_N - Nμ) ≥ 0` for `ν_N = ∑_i δ_{x_i}`. -/
theorem sum_pairKernel_nonneg {N : ℕ} (X : Config d N) :
    0 ≤ ∑ i, ∑ j, pairKernel f μ (X i, X j) := by
  -- basic integrability and bounds of the cosine/sine modes against `μ`
  have hcI : ∀ k : Lattice d, Integrable (Torus.cosMode k) μ := fun k =>
    Integrable.of_bound (Torus.continuous_cosMode k).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => Torus.norm_cosMode_le k z)
  have hsI : ∀ k : Lattice d, Integrable (Torus.sinMode k) μ := fun k =>
    Integrable.of_bound (Torus.continuous_sinMode k).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => Torus.norm_sinMode_le k z)
  have ha1 : ∀ k : Lattice d, ‖∫ y, Torus.cosMode k y ∂μ‖ ≤ 1 := fun k => by
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => Torus.cosMode k y)
      (C := 1) (Filter.Eventually.of_forall fun y => Torus.norm_cosMode_le k y)
    rwa [probReal_univ, mul_one] at h
  have hb1 : ∀ k : Lattice d, ‖∫ y, Torus.sinMode k y ∂μ‖ ≤ 1 := fun k => by
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => Torus.sinMode k y)
      (C := 1) (Filter.Eventually.of_forall fun y => Torus.norm_sinMode_le k y)
    rwa [probReal_univ, mul_one] at h
  have hcont : ∀ (k : Lattice d) (x : Torus d),
      Continuous fun y : Torus d => Torus.cosMode k (x - y) := fun k x =>
    (Torus.continuous_cosMode k).comp (continuous_const.sub continuous_id)
  have hcontS : ∀ (k : Lattice d) (x : Torus d),
      Continuous fun y : Torus d => Torus.sinMode k (x - y) := fun k x =>
    (Torus.continuous_sinMode k).comp (continuous_const.sub continuous_id)
  -- Gaussian-free form of the convolution: `∫ cos(k·(x-z)) dμ(z) = cos(k·x) a_k + sin(k·x) b_k`
  have hH : ∀ (k : Lattice d) (x : Torus d), ∫ z, Torus.cosMode k (x - z) ∂μ =
      Torus.cosMode k x * (∫ y, Torus.cosMode k y ∂μ) +
        Torus.sinMode k x * (∫ y, Torus.sinMode k y ∂μ) := by
    intro k x
    simp only [rp04_cosMode_sub]
    rw [integral_add ((hcI k).const_mul _) ((hsI k).const_mul _), integral_const_mul,
      integral_const_mul]
  have hbd : ∀ (k : Lattice d) (z : Torus d), ‖c k * Torus.cosMode k z‖ ≤ c k :=
    rp04_norm_le c hc hs
  -- bounds on the one-body coefficients
  have hBb : ∀ (k : Lattice d) (x : Torus d),
      ‖Torus.cosMode k x * (∫ y, Torus.cosMode k y ∂μ) +
        Torus.sinMode k x * (∫ y, Torus.sinMode k y ∂μ)‖ ≤ 2 := fun k x => by
    have h := rp04_norm_add
      (rp04_norm_mul (Torus.norm_cosMode_le k x) (ha1 k) zero_le_one)
      (rp04_norm_mul (Torus.norm_sinMode_le k x) (hb1 k) zero_le_one)
    linarith
  have hDb : ∀ k : Lattice d,
      ‖(∫ y, Torus.cosMode k y ∂μ) * (∫ y, Torus.cosMode k y ∂μ) +
        (∫ y, Torus.sinMode k y ∂μ) * (∫ y, Torus.sinMode k y ∂μ)‖ ≤ 2 := fun k => by
    have h := rp04_norm_add (rp04_norm_mul (ha1 k) (ha1 k) zero_le_one)
      (rp04_norm_mul (hb1 k) (hb1 k) zero_le_one)
    linarith
  have hQb : ∀ (k : Lattice d) (x y : Torus d),
      ‖(Torus.cosMode k x - ∫ z, Torus.cosMode k z ∂μ) *
          (Torus.cosMode k y - ∫ z, Torus.cosMode k z ∂μ) +
        (Torus.sinMode k x - ∫ z, Torus.sinMode k z ∂μ) *
          (Torus.sinMode k y - ∫ z, Torus.sinMode k z ∂μ)‖ ≤ 8 := by
    intro k x y
    have p1 := rp04_norm_mul
      (rp04_norm_sub (Torus.norm_cosMode_le k x) (ha1 k))
      (rp04_norm_sub (Torus.norm_cosMode_le k y) (ha1 k)) (by norm_num)
    have p2 := rp04_norm_mul
      (rp04_norm_sub (Torus.norm_sinMode_le k x) (hb1 k))
      (rp04_norm_sub (Torus.norm_sinMode_le k y) (hb1 k)) (by norm_num)
    have s := rp04_norm_add p1 p2
    linarith
  -- the one-body potential `F(x) = ∫ f(x-y) dμ(y)` as a Fourier series (dominated convergence)
  have hF1 : ∀ x : Torus d, ∫ y, f (x - y) ∂μ = ∑' k : Lattice d, c k *
      (Torus.cosMode k x * (∫ y, Torus.cosMode k y ∂μ) +
        Torus.sinMode k x * (∫ y, Torus.sinMode k y ∂μ)) := by
    intro x
    have hint : ∀ k : Lattice d, Integrable (fun y => c k * Torus.cosMode k (x - y)) μ :=
      fun k => Integrable.of_bound ((hcont k x).const_mul (c k)).aestronglyMeasurable (c k)
        (Filter.Eventually.of_forall fun y => hbd k (x - y))
    have hnorm : ∀ k : Lattice d, ∫ y, ‖c k * Torus.cosMode k (x - y)‖ ∂μ ≤ c k := fun k => by
      calc ∫ y, ‖c k * Torus.cosMode k (x - y)‖ ∂μ ≤ ∫ _y, c k ∂μ :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
              (integrable_const _) (Filter.Eventually.of_forall fun y => hbd k (x - y))
        _ = c k := by simp
    have hsum : Summable fun k : Lattice d => ∫ y, ‖c k * Torus.cosMode k (x - y)‖ ∂μ :=
      Summable.of_nonneg_of_le (fun k => integral_nonneg fun y => norm_nonneg _) hnorm hs
    calc ∫ y, f (x - y) ∂μ = ∫ y, ∑' k : Lattice d, c k * Torus.cosMode k (x - y) ∂μ := by
          simp only [hf]
      _ = ∑' k : Lattice d, ∫ y, c k * Torus.cosMode k (x - y) ∂μ :=
          (integral_tsum_of_summable_integral_norm hint hsum).symm
      _ = _ := tsum_congr fun k => by rw [integral_const_mul, hH k x]
  have hCM' : ∀ x : Torus d, convMeasure f μ x = ∑' k : Lattice d, c k *
      (Torus.cosMode k x * (∫ y, Torus.cosMode k y ∂μ) +
        Torus.sinMode k x * (∫ y, Torus.sinMode k y ∂μ)) := fun x => hF1 x
  -- the energy `∬ f dμ dμ` as a Fourier series
  have hGb : ∀ (k : Lattice d) (x : Torus d),
      ‖c k * (Torus.cosMode k x * (∫ y, Torus.cosMode k y ∂μ) +
        Torus.sinMode k x * (∫ y, Torus.sinMode k y ∂μ))‖ ≤ c k * 2 := fun k x => by
    rw [norm_mul, Real.norm_of_nonneg (hc k)]
    exact mul_le_mul_of_nonneg_left (hBb k x) (hc k)
  have hE : energyPairing f μ μ = ∑' k : Lattice d, c k *
      ((∫ y, Torus.cosMode k y ∂μ) * (∫ y, Torus.cosMode k y ∂μ) +
        (∫ y, Torus.sinMode k y ∂μ) * (∫ y, Torus.sinMode k y ∂μ)) := by
    have hG : ∀ k : Lattice d, Integrable (fun x => c k * (Torus.cosMode k x *
        (∫ y, Torus.cosMode k y ∂μ) + Torus.sinMode k x * (∫ y, Torus.sinMode k y ∂μ))) μ :=
      fun k => Integrable.of_bound
        (((((Torus.continuous_cosMode k).mul continuous_const).add
          ((Torus.continuous_sinMode k).mul continuous_const)).const_mul (c k)).aestronglyMeasurable)
        (c k * 2) (Filter.Eventually.of_forall fun x => hGb k x)
    have hGsum : Summable fun k : Lattice d => ∫ x, ‖c k * (Torus.cosMode k x *
        (∫ y, Torus.cosMode k y ∂μ) + Torus.sinMode k x * (∫ y, Torus.sinMode k y ∂μ))‖ ∂μ := by
      refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun x => norm_nonneg _)
        (fun k => ?_) (hs.mul_right 2)
      calc ∫ x, ‖c k * (Torus.cosMode k x * (∫ y, Torus.cosMode k y ∂μ) +
            Torus.sinMode k x * (∫ y, Torus.sinMode k y ∂μ))‖ ∂μ
          ≤ ∫ _x, c k * 2 ∂μ := integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun x => norm_nonneg _) (integrable_const _)
            (Filter.Eventually.of_forall fun x => hGb k x)
        _ = c k * 2 := by simp
    show ∫ x, ∫ y, f (x - y) ∂μ ∂μ = _
    simp only [hF1]
    rw [← integral_tsum_of_summable_integral_norm hG hGsum]
    refine tsum_congr fun k => ?_
    rw [integral_const_mul, integral_add ((hcI k).mul_const _) ((hsI k).mul_const _),
      integral_mul_const, integral_mul_const]
  -- the centred kernel at a pair of points is a single Fourier series of squares
  have hpk : ∀ i j : Fin N, pairKernel f μ (X i, X j) = ∑' k : Lattice d, c k *
      ((Torus.cosMode k (X i) - ∫ y, Torus.cosMode k y ∂μ) *
          (Torus.cosMode k (X j) - ∫ y, Torus.cosMode k y ∂μ) +
        (Torus.sinMode k (X i) - ∫ y, Torus.sinMode k y ∂μ) *
          (Torus.sinMode k (X j) - ∫ y, Torus.sinMode k y ∂μ)) := by
    intro i j
    have hA := rp04_summable c hc hs (fun k => Torus.cosMode k (X i - X j)) 1
      (fun k => Torus.norm_cosMode_le k _)
    have hBi := rp04_summable c hc hs (fun k => Torus.cosMode k (X i) *
        (∫ y, Torus.cosMode k y ∂μ) + Torus.sinMode k (X i) * (∫ y, Torus.sinMode k y ∂μ)) 2
      (fun k => hBb k (X i))
    have hBj := rp04_summable c hc hs (fun k => Torus.cosMode k (X j) *
        (∫ y, Torus.cosMode k y ∂μ) + Torus.sinMode k (X j) * (∫ y, Torus.sinMode k y ∂μ)) 2
      (fun k => hBb k (X j))
    have hD := rp04_summable c hc hs (fun k => (∫ y, Torus.cosMode k y ∂μ) *
        (∫ y, Torus.cosMode k y ∂μ) + (∫ y, Torus.sinMode k y ∂μ) *
        (∫ y, Torus.sinMode k y ∂μ)) 2 (fun k => hDb k)
    have hsum := ((hA.hasSum.sub hBi.hasSum).sub hBj.hasSum).add hD.hasSum
    simp only [pairKernel, centeredKernel]
    rw [hf (X i - X j), hCM' (X i), hCM' (X j), hE, ← hsum.tsum_eq]
    refine tsum_congr fun k => ?_
    simp only [rp04_cosMode_sub]
    ring
  -- exchange the finite sums with `∑_k`; each term is `c_k` times a sum of squares
  simp only [hpk]
  rw [rp04_tsum_comm _ (fun i j => rp04_summable c hc hs _ 8 (fun k => hQb k (X i) (X j)))]
  refine tsum_nonneg fun k => ?_
  simp only [← Finset.mul_sum, rp04_sum_sum_sq]
  exact mul_nonneg (hc k) (by positivity)

/-- The deterministic cap: `iidNeg_N(f̃) ≤ 2 ∑ c_k`. -/
theorem iidNegativeStatistic_le_of_posdef {N : ℕ} (X : Config d N) :
    DGRHS.Concentration.iidNegativeStatistic N (pairKernel f μ) X ≤ 2 * ∑' k : Lattice d, c k := by
  have hS := sum_pairKernel_nonneg (μ := μ) c hc hs hf X
  have hC0 : 0 ≤ ∑' k : Lattice d, c k := tsum_nonneg hc
  have hdiag : ∑ i, pairKernel f μ (X i, X i) ≤ N * (4 * ∑' k : Lattice d, c k) := by
    calc ∑ i, pairKernel f μ (X i, X i)
        ≤ ∑ _i : Fin N, 4 * ∑' k : Lattice d, c k := Finset.sum_le_sum fun i _ =>
          (le_abs_self _).trans (abs_pairKernel_le_tsum (μ := μ) c hc hs hf (X i) (X i))
      _ = N * (4 * ∑' k : Lattice d, c k) := by simp
  have hoff : DGRHS.Concentration.iidCoupledSum N (pairKernel f μ) X =
      (∑ i, ∑ j, pairKernel f μ (X i, X j)) - ∑ i, pairKernel f μ (X i, X i) := by
    unfold DGRHS.Concentration.iidCoupledSum DGRHS.Decoupling.offDiagonalSum
    have e : ∀ i j : Fin N, (if i ≠ j then pairKernel f μ (X i, X j) else 0) =
        pairKernel f μ (X i, X j) - (if i = j then pairKernel f μ (X i, X j) else 0) := by
      intro i j
      by_cases h : i = j <;> simp [h]
    simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  unfold DGRHS.Concentration.iidNegativeStatistic
  rw [hoff]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.cast_zero, mul_zero, div_zero]
    linarith
  · have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_iff₀ (by positivity)]
    linarith

end Generic

/-! ### Applications to the band and the tail -/

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- `heatBand d a b 0 ≤ bandSupConst d · log(b/a)` (`0 < a ≤ b ≤ 1`). -/
theorem heatBand_zero_le (hd : 2 ≤ d) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    heatBand d a b 0 ≤ bandSupConst d * Real.log (b / a) := by
  have hb0 : 0 < b := ha.trans_le hab
  have hsub : 0 ≤ KernelAux.subA d 0 := rb_subA_nonneg hd
  have hpt : ∀ t ∈ Set.Ioc a b, heatWeight d t * psiFn (0 : Torus d) t ≤
      Real.pi ^ ((d : ℝ) / 2) * thetaConst d * t⁻¹ := by
    intro t ht
    have ht0 : 0 < t := ha.trans ht.1
    have ht1 : t ≤ 1 := ht.2.trans hb
    have h1 := one_add_psiFn_zero_le (d := d) ht0 ht1
    have hw : 0 ≤ heatWeight d t := rb_heatWeight_nonneg ht0
    have hpsi : psiFn (0 : Torus d) t ≤ (Real.pi / t) ^ ((d : ℝ) / 2) * thetaConst d := by
      linarith
    refine (mul_le_mul_of_nonneg_left hpsi hw).trans (le_of_eq ?_)
    unfold heatWeight
    rw [Real.div_rpow Real.pi_pos.le ht0.le, Real.rpow_sub_one ht0.ne']
    have hp : t ^ ((d : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos ht0 _).ne'
    field_simp
  have hint : ∫ t in Set.Ioc a b, heatWeight d t * psiFn (0 : Torus d) t ≤
      ∫ t in Set.Ioc a b, Real.pi ^ ((d : ℝ) / 2) * thetaConst d * t⁻¹ := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
        mul_nonneg (rb_heatWeight_nonneg (ha.trans ht.1)) (psiFn_zero_nonneg (ha.trans ht.1))
    · have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc a b) := fun t ht =>
        (continuousAt_inv₀ (ne_of_gt (ha.trans_le ht.1))).continuousWithinAt
      exact Integrable.const_mul ((hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self) _
    · exact ae_restrict_of_forall_mem measurableSet_Ioc hpt
  have hlog : ∫ t in Set.Ioc a b, Real.pi ^ ((d : ℝ) / 2) * thetaConst d * t⁻¹ =
      Real.pi ^ ((d : ℝ) / 2) * thetaConst d * Real.log (b / a) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hab, integral_inv_of_pos ha hb0]
  unfold heatBand bandSupConst
  calc KernelAux.subA d 0 * ∫ t in Set.Ioc a b, heatWeight d t * psiFn (0 : Torus d) t
      ≤ KernelAux.subA d 0 * (Real.pi ^ ((d : ℝ) / 2) * thetaConst d * Real.log (b / a)) :=
        mul_le_mul_of_nonneg_left (hint.trans hlog.le) hsub
    _ = _ := by ring

/-- `masterKernel` is `2β` times the centred pair kernel of the band `heatBand d (α²) (δ²)`. -/
theorem masterKernel_eq_smul (α δ β : ℝ) (p : Torus d × Torus d) :
    masterKernel d α δ β μ p = (2 * β) * pairKernel (heatBand d (α ^ 2) (δ ^ 2)) μ p := rfl

/-- The band value at the origin (the sum of its coefficients) is at most `2 C log(δ/α)`. -/
theorem heatBand_sq_zero_le (hd : 2 ≤ d) {α δ : ℝ} (hα : 0 < α) (hαδ : α ≤ δ) (hδ : δ ≤ 1) :
    heatBand d (α ^ 2) (δ ^ 2) 0 ≤ 2 * (bandSupConst d * Real.log (δ / α)) := by
  have hα2 : 0 < α ^ 2 := pow_pos hα 2
  have hab : α ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hα.le hαδ 2
  have hδ2 : δ ^ 2 ≤ 1 := pow_le_one₀ (le_trans hα.le hαδ) hδ
  have h := heatBand_zero_le hd hα2 hab hδ2
  have hlog : Real.log (δ ^ 2 / α ^ 2) = 2 * Real.log (δ / α) := by
    rw [← div_pow, Real.log_pow]
    norm_num
  rw [hlog] at h
  exact h.trans (le_of_eq (by ring))

theorem masterKernel_log_nonneg {α δ : ℝ} (hα : 0 < α) (hαδ : α ≤ δ) :
    0 ≤ Real.log (δ / α) :=
  Real.log_nonneg ((one_le_div hα).mpr hαδ)

/-- `|q| ≤ 2β · 4 · heatBand d α² δ² 0 ≤ 16 β bandSupConst d log(δ/α)` (`0 < α ≤ δ ≤ 1`). -/
theorem abs_masterKernel_le (hd : 2 ≤ d) {α δ β : ℝ} (hα : 0 < α) (hαδ : α ≤ δ) (hδ : δ ≤ 1)
    (hβ : 0 ≤ β) (p : Torus d × Torus d) :
    |masterKernel d α δ β μ p| ≤ 16 * β * bandSupConst d * Real.log (δ / α) := by
  obtain ⟨x, y⟩ := p
  have hα2 : 0 < α ^ 2 := pow_pos hα 2
  have hab : α ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hα.le hαδ 2
  have hS : |pairKernel (heatBand d (α ^ 2) (δ ^ 2)) μ (x, y)| ≤
      4 * ∑' k : Lattice d, bandCoeff d (α ^ 2) (δ ^ 2) k :=
    abs_pairKernel_le_tsum (bandCoeff d (α ^ 2) (δ ^ 2)) (bandCoeff_nonneg hd hα2.le hab)
      (summable_bandCoeff hd hα2 hab) (heatBand_eq_tsum hd hα2 hab) x y
  rw [← heatBand_zero_eq_tsum hd hα2 hab] at hS
  have hB := heatBand_sq_zero_le hd hα hαδ hδ
  rw [masterKernel_eq_smul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * β)]
  calc 2 * β * |pairKernel (heatBand d (α ^ 2) (δ ^ 2)) μ (x, y)|
      ≤ 2 * β * (4 * heatBand d (α ^ 2) (δ ^ 2) 0) :=
        mul_le_mul_of_nonneg_left hS (by linarith)
    _ ≤ 2 * β * (4 * (2 * (bandSupConst d * Real.log (δ / α)))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ = 16 * β * bandSupConst d * Real.log (δ / α) := by ring

theorem continuous_masterKernel (hd : 2 ≤ d) {α δ β : ℝ} (hα : 0 < α) :
    Continuous (masterKernel d α δ β μ) := by
  have hc : Continuous (heatBand d (α ^ 2) (δ ^ 2)) := continuous_heatBand hd (pow_pos hα 2)
  have e : masterKernel d α δ β μ =
      fun p => (2 * β) * pairKernel (heatBand d (α ^ 2) (δ ^ 2)) μ p := rfl
  rw [e]
  exact (continuous_pairKernel hc μ).const_mul (2 * β)

theorem measurable_masterKernel (hd : 2 ≤ d) {α δ β : ℝ} (hα : 0 < α) :
    Measurable (masterKernel d α δ β μ) := by
  exact (continuous_masterKernel hd hα).measurable

theorem memLp_top_masterKernel (hd : 2 ≤ d) {α δ β : ℝ} (hα : 0 < α) (hαδ : α ≤ δ) (hδ : δ ≤ 1)
    (hβ : 0 ≤ β) : MemLp (masterKernel d α δ β μ) ∞ (μ.prod μ) := by
  refine MemLp.of_bound (measurable_masterKernel hd hα).aestronglyMeasurable
    (16 * β * bandSupConst d * Real.log (δ / α)) (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs]
  exact abs_masterKernel_le hd hα hαδ hδ hβ p

theorem eLpNormEssSup_masterKernel_le (hd : 2 ≤ d) {α δ β : ℝ} (hα : 0 < α) (hαδ : α ≤ δ)
    (hδ : δ ≤ 1) (hβ : 0 ≤ β) :
    (eLpNormEssSup (masterKernel d α δ β μ) (μ.prod μ)).toReal ≤
      16 * β * bandSupConst d * Real.log (δ / α) := by
  have hC : 0 ≤ 16 * β * bandSupConst d * Real.log (δ / α) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hβ) (bandSupConst_pos hd).le)
      (masterKernel_log_nonneg hα hαδ)
  apply ENNReal.toReal_le_of_le_ofReal hC
  apply eLpNormEssSup_le_of_ae_bound
  refine ae_of_all _ fun p => ?_
  rw [Real.norm_eq_abs]
  exact abs_masterKernel_le hd hα hαδ hδ hβ p

theorem masterKernel_symm (hd : 2 ≤ d) (α δ β : ℝ) (x y : Torus d) :
    masterKernel d α δ β μ (x, y) = masterKernel d α δ β μ (y, x) := by
  have hev : ∀ z : Torus d, heatBand d (α ^ 2) (δ ^ 2) (-z) = heatBand d (α ^ 2) (δ ^ 2) z := by
    intro z
    unfold heatBand
    simp only [psiFn_neg]
  rw [masterKernel_eq_smul, masterKernel_eq_smul, pairKernel_symm hev μ x y]

/-- Continuity of the convolution `x ↦ ∫ f(x - y) dμ(y)` of a continuous `f`. -/
theorem convMeasure_continuous_aux {f : Torus d → ℝ} (hf : Continuous f) (μ : Measure (Torus d))
    [IsFiniteMeasure μ] : Continuous (convMeasure f μ) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  unfold convMeasure
  refine continuous_of_dominated (F := fun x y => f (x - y)) (bound := fun _ => C)
    (fun x => ?_) (fun x => ae_of_all _ fun a => hC _ (Set.mem_univ _)) (integrable_const C)
    (ae_of_all _ fun a => hf.comp (continuous_id.sub continuous_const))
  exact (hf.measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable

theorem integral_masterKernel_eq_zero (hd : 2 ≤ d) {α δ β : ℝ} (hα : 0 < α) (x : Torus d) :
    ∫ y, masterKernel d α δ β μ (x, y) ∂μ = 0 := by
  have hc : Continuous (heatBand d (α ^ 2) (δ ^ 2)) := continuous_heatBand hd (pow_pos hα 2)
  have hconv : Integrable (convMeasure (heatBand d (α ^ 2) (δ ^ 2)) μ) μ :=
    (convMeasure_continuous_aux hc μ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hx : Integrable (fun y => heatBand d (α ^ 2) (δ ^ 2) (x - y)) μ :=
    (hc.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h0 := integral_pairKernel_eq_zero hconv x hx
  have e : (fun y => masterKernel d α δ β μ (x, y)) =
      fun y => (2 * β) * pairKernel (heatBand d (α ^ 2) (δ ^ 2)) μ (x, y) := rfl
  rw [e, integral_const_mul, h0, mul_zero]

/-- The deterministic cap (M2): `iidNeg_N(q) ≤ 2β · 2 heatBand d α² δ² 0 ≤ masterCap d α δ β`. -/
theorem iidNegativeStatistic_masterKernel_le (hd : 2 ≤ d) {α δ β : ℝ} (hα : 0 < α) (hαδ : α ≤ δ)
    (hδ : δ ≤ 1) (hβ : 0 ≤ β) {N : ℕ} (X : Config d N) :
    DGRHS.Concentration.iidNegativeStatistic N (masterKernel d α δ β μ) X ≤ masterCap d α δ β := by
  have hα2 : 0 < α ^ 2 := pow_pos hα 2
  have hab : α ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hα.le hαδ 2
  have h := iidNegativeStatistic_le_of_posdef (μ := μ) (f := heatBand d (α ^ 2) (δ ^ 2))
    (bandCoeff d (α ^ 2) (δ ^ 2)) (bandCoeff_nonneg hd hα2.le hab)
    (summable_bandCoeff hd hα2 hab) (heatBand_eq_tsum hd hα2 hab) X
  rw [← heatBand_zero_eq_tsum hd hα2 hab] at h
  have hB := heatBand_sq_zero_le hd hα hαδ hδ
  have hsmul := iidNegativeStatistic_smul (2 * β) (pairKernel (heatBand d (α ^ 2) (δ ^ 2)) μ) X
  have e : masterKernel d α δ β μ =
      fun p => (2 * β) * pairKernel (heatBand d (α ^ 2) (δ ^ 2)) μ p := rfl
  rw [e, hsmul]
  have hI : DGRHS.Concentration.iidNegativeStatistic N (pairKernel (heatBand d (α ^ 2) (δ ^ 2)) μ) X
      ≤ 2 * (2 * (bandSupConst d * Real.log (δ / α))) := by linarith
  have h2β : 0 ≤ 2 * β := by linarith
  have key := mul_le_mul_of_nonneg_left hI h2β
  unfold masterCap
  linarith

theorem masterCap_pos (hd : 2 ≤ d) {α δ β : ℝ} (hα : 0 < α) (hαδ : α ≤ δ) (hβ : 0 ≤ β) :
    0 < masterCap d α δ β := by
  unfold masterCap
  have hL := masterKernel_log_nonneg hα hαδ
  have hC := (bandSupConst_pos hd).le
  have h8 : 0 ≤ 8 * β * bandSupConst d * Real.log (δ / α) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hβ) hC) hL
  linarith

/-- The tail has no infrared problem on the torus: `iidNeg_N((heatTail d b)~) ≤ 2 heatTail d b 0`. -/
theorem iidNegativeStatistic_heatTail_le (hd : 2 ≤ d) {b : ℝ} (hb : 0 < b) {N : ℕ}
    (X : Config d N) :
    DGRHS.Concentration.iidNegativeStatistic N (pairKernel (heatTail d b) μ) X ≤
      2 * heatTail d b 0 := by
  have h := iidNegativeStatistic_le_of_posdef (μ := μ) (f := heatTail d b) (tailCoeff d b)
    (tailCoeff_nonneg hd hb.le) (summable_tailCoeff hd hb) (heatTail_eq_tsum hd hb) X
  rw [heatTail_zero_eq_tsum hd hb]
  exact h

theorem heatTail_zero_nonneg (hd : 2 ≤ d) {b : ℝ} (hb : 0 < b) : 0 ≤ heatTail d b 0 := by
  rw [heatTail_zero_eq_tsum hd hb]
  exact tsum_nonneg fun k => tailCoeff_nonneg hd hb.le k

end Repulsive

end HRS

end
