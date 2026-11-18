import HRS.Equilibrium.QuadraticLimit.GibbsAuxD
import HRS.Equilibrium.QuadraticLimit.GibbsAuxG

/-!
# Lemma 7.5, `q08_gibbs_approx`: the finite-rank closeness estimates, concretely (prefix `q08gl_`)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q08

variable {d : ℕ} (D : Q08Data d)

section Closeness

variable {m : ℕ} {u : Fin m → Torus d → ℝ}

theorem q08gl_hYV_none (hu : q08gl_UData D.μ u) (H : Matrix (Fin m) (Fin m) ℝ) (hH : ∀ i j, H i j = H j i)
    (α : Fin D.p → Fin m → ℝ) (N : ℕ) (hN : 1 ≤ N) (E : ℝ)
    (hE : ∀ x, |q08gl_kap u H x x - H.trace| ≤ E) :
    MemLp (fun X : Config d N => q08gl_V D N none X - q08gl_fvec H α none (q08gl_Sv u N X)) 2 (D.prodLaw N) ∧
      ∫ X, (q08gl_V D N none X - q08gl_fvec H α none (q08gl_Sv u N X)) ^ 2 ∂(D.prodLaw N) ≤
        (3 / 2) * ∫ z : Torus d × Torus d, (q08e_kt D.μ D.h z.1 z.2 - q08gl_kap u H z.1 z.2) ^ 2 ∂(D.μ.prod D.μ) +
          3 * (∫ z : Torus d × Torus d, D.h z.1 z.2 ^ 2 ∂(D.μ.prod D.μ)) / N + 3 * E ^ 2 / (4 * N) := by
  haveI := q08_isProb_μ D
  exact q08gl_quad_L2 hu D.h D.hmeas (q08gl_h_sq_int D) D.hsymm H hH N hN E hE

theorem q08gl_hYV_some (hu : q08gl_UData D.μ u) (α : Fin D.p → Fin m → ℝ) (b : Fin D.p) (N : ℕ) (hN : 1 ≤ N) :
    MemLp (fun X : Config d N => q08gl_V D N (some b) X - q08gl_fvec (0 : Matrix (Fin m) (Fin m) ℝ) α (some b)
        (q08gl_Sv u N X)) 2 (D.prodLaw N) ∧
      ∫ X, (q08gl_V D N (some b) X - q08gl_fvec (0 : Matrix (Fin m) (Fin m) ℝ) α (some b)
          (q08gl_Sv u N X)) ^ 2 ∂(D.prodLaw N) =
        ∫ x, (D.φ b x - pair D.μ (D.φ b) - ∑ k, α b k * u k x) ^ 2 ∂D.μ := by
  haveI := q08_isProb_μ D
  obtain ⟨hφm, M, hM⟩ := D.hφ b
  set r : Torus d → ℝ := fun x => D.φ b x - pair D.μ (D.φ b) - ∑ k, α b k * u k x with hr
  have hrm : Measurable r := by
    refine (hφm.sub_const _).sub (Finset.measurable_sum _ fun k _ => measurable_const.mul (hu.meas k))
  choose Mu hMu using hu.bdd
  have hrb : ∀ x, |r x| ≤ M + |pair D.μ (D.φ b)| + ∑ k, |α b k| * Mu k := fun x => by
    simp only [hr]
    have h1 : |D.φ b x - pair D.μ (D.φ b) - ∑ k, α b k * u k x| ≤
        |D.φ b x| + |pair D.μ (D.φ b)| + |∑ k, α b k * u k x| := by
      calc _ ≤ |D.φ b x - pair D.μ (D.φ b)| + |∑ k, α b k * u k x| := abs_sub _ _
        _ ≤ _ := by gcongr; exact abs_sub _ _
    have h2 : |∑ k, α b k * u k x| ≤ ∑ k, |α b k| * Mu k :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hMu k x) (abs_nonneg _))
    linarith [hM x]
  have hr0 : ∫ x, r x ∂D.μ = 0 := by
    have hint : Integrable (D.φ b) D.μ :=
      Integrable.of_bound hφm.aestronglyMeasurable M
        (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x)
    simp only [hr]
    have h1 : Integrable (fun x => D.φ b x - pair D.μ (D.φ b)) D.μ := hint.sub (integrable_const _)
    have h3 : ∀ k : Fin m, Integrable (fun x => α b k * u k x) D.μ := fun k => (q08gl_int_u hu k).const_mul _
    have h2 : Integrable (fun x => ∑ k, α b k * u k x) D.μ := integrable_finsetSum _ fun k _ => h3 k
    rw [integral_sub h1 h2, integral_sub hint (integrable_const _), integral_finsetSum _ fun k _ => h3 k]
    simp [pair, integral_const_mul, hu.cent]
  have hid : ∀ X : Config d N, q08gl_V D N (some b) X - q08gl_fvec (0 : Matrix (Fin m) (Fin m) ℝ) α (some b)
      (q08gl_Sv u N X) = (Real.sqrt N)⁻¹ * ∑ i, r (X i) := by
    intro X
    simp only [q08gl_V, q08gl_Lin, q08gl_fvec, Option.elim, q08gl_fl, q08gl_Sv, WithLp.ofLp_toLp, hr]
    rw [Finset.sum_sub_distrib]
    have : ∑ k, α b k * ((Real.sqrt N)⁻¹ * ∑ i, u k (X i)) = (Real.sqrt N)⁻¹ * ∑ i, ∑ k, α b k * u k (X i) := by
      calc ∑ k, α b k * ((Real.sqrt N)⁻¹ * ∑ i, u k (X i)) = ∑ k, (Real.sqrt N)⁻¹ * ∑ i, α b k * u k (X i) :=
            Finset.sum_congr rfl fun k _ => by
              rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
        _ = (Real.sqrt N)⁻¹ * ∑ k, ∑ i, α b k * u k (X i) := by rw [← Finset.mul_sum]
        _ = (Real.sqrt N)⁻¹ * ∑ i, ∑ k, α b k * u k (X i) := by rw [Finset.sum_comm]
    rw [mul_sub, this]
    simp only [Finset.sum_sub_distrib]
    ring
  simp_rw [hid]
  exact q08gl_lin_L2 r hrm _ hrb hr0 N hN

/-- The mean of the Riesz kernel `∬ g(x - y)`. -/
def q08gl_gbar : ℝ := ∫ x, ∫ y, periodicRiesz d D.s (x - y) ∂D.μ ∂D.μ

theorem q08gl_x_eq (N : ℕ) (X : Config d N) :
    q08gl_x D N X = q08e_Z D.μ (fun x y => periodicRiesz d D.s (x - y)) X - (1 / 2) * q08gl_gbar D := by
  unfold q08gl_x q08gl_gbar modulatedEnergyKernel q08e_Z
  simp only [modulatedEnergy]
  ring

theorem q08gl_hxy (hu : q08gl_UData D.μ u) (H : Matrix (Fin m) (Fin m) ℝ) (hH : ∀ i j, H i j = H j i)
    (N : ℕ) (hN : 1 ≤ N) (E : ℝ) (hE : ∀ x, |q08gl_kap u H x x - H.trace| ≤ E) :
    MemLp (fun X : Config d N => q08gl_x D N X - q08gl_psi H (q08gl_gbar D) (q08gl_Sv u N X)) 2
        (D.prodLaw N) ∧
      ∫ X, (q08gl_x D N X - q08gl_psi H (q08gl_gbar D) (q08gl_Sv u N X)) ^ 2 ∂(D.prodLaw N) ≤
        (3 / 2) * ∫ z : Torus d × Torus d, (q08e_kt D.μ (fun x y => periodicRiesz d D.s (x - y)) z.1 z.2 -
            q08gl_kap u H z.1 z.2) ^ 2 ∂(D.μ.prod D.μ) +
          3 * (∫ z : Torus d × Torus d, periodicRiesz d D.s (z.1 - z.2) ^ 2 ∂(D.μ.prod D.μ)) / N +
            3 * E ^ 2 / (4 * N) := by
  haveI := q08_isProb_μ D
  have h := q08gl_quad_L2 hu (fun x y : Torus d => periodicRiesz d D.s (x - y)) (q08gl_kg_meas D)
    (q08gl_g_sq_int D) (q08gl_kg_symm D) H hH N hN E hE
  have hid : ∀ X : Config d N, q08gl_x D N X - q08gl_psi H (q08gl_gbar D) (q08gl_Sv u N X) =
      q08e_Z D.μ (fun x y => periodicRiesz d D.s (x - y)) X -
        (1 / 2) * (q08gl_Q H (q08gl_Sv u N X) - H.trace) := by
    intro X
    rw [q08gl_x_eq]
    unfold q08gl_psi
    ring
  simp_rw [hid]
  exact h

theorem q08gl_Sv_meas (u : Fin m → Torus d → ℝ) (hu : ∀ k, Measurable (u k)) (N : ℕ) :
    Measurable (q08gl_Sv u N : Config d N → EuclideanSpace ℝ (Fin m)) := by
  unfold q08gl_Sv
  refine (WithLp.measurable_toLp 2 (Fin m → ℝ)).comp (measurable_pi_iff.2 fun k => ?_)
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => (hu k).comp (measurable_pi_apply i))

end Closeness

section Constants

variable {m : ℕ} {u : Fin m → Torus d → ℝ}

/-- `‖kap A‖_F ≤ ‖k_c‖ + ‖k_c - kap A‖`. -/
theorem q08gl_frob_bound {T : Type*} [MeasurableSpace T] {μ : Measure T} [IsProbabilityMeasure μ]
    {u : Fin m → T → ℝ} (hu : q08gl_UData μ u) (k : T → T → ℝ) (hm : Measurable (Function.uncurry k))
    (hk : Integrable (fun z : T × T => k z.1 z.2 ^ 2) (μ.prod μ)) (hs : ∀ x y, k x y = k y x)
    (A : Matrix (Fin m) (Fin m) ℝ) (δ : ℝ)
    (hδ : ∫ z : T × T, (q08e_kt μ k z.1 z.2 - q08gl_kap u A z.1 z.2) ^ 2 ∂(μ.prod μ) ≤ δ ^ 2) :
    ∑ i, ∑ j, A i j ^ 2 ≤ (Real.sqrt (∫ z : T × T, k z.1 z.2 ^ 2 ∂(μ.prod μ)) + |δ|) ^ 2 := by
  have hkt : MemLp (fun z : T × T => q08e_kt μ k z.1 z.2) 2 (μ.prod μ) := q08e_kt_memLp μ k hm hk
  have hkap : MemLp (fun z : T × T => q08gl_kap u A z.1 z.2) 2 (μ.prod μ) := q08gl_kap_memLp A hu
  have hd : MemLp (fun z : T × T => q08gl_kap u A z.1 z.2 - q08e_kt μ k z.1 z.2) 2 (μ.prod μ) :=
    hkap.sub hkt
  have h := q08gl_mink (μ.prod μ) hkt hd
  have e1 : ∫ z : T × T, (q08e_kt μ k z.1 z.2 + (q08gl_kap u A z.1 z.2 - q08e_kt μ k z.1 z.2)) ^ 2 ∂(μ.prod μ) =
      ∑ i, ∑ j, A i j ^ 2 := by
    rw [← q08gl_kap_sq A hu]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only; ring
  have e2 : ∫ z : T × T, (q08gl_kap u A z.1 z.2 - q08e_kt μ k z.1 z.2) ^ 2 ∂(μ.prod μ) =
      ∫ z : T × T, (q08e_kt μ k z.1 z.2 - q08gl_kap u A z.1 z.2) ^ 2 ∂(μ.prod μ) := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only; ring
  have hnorm := q08e_kt_norm_le μ k hm hk hs
  beta_reduce at h
  rw [e1] at h
  have hsq : Real.sqrt (∫ z : T × T, q08e_kt μ k z.1 z.2 ^ 2 ∂(μ.prod μ)) ≤
      Real.sqrt (∫ z : T × T, k z.1 z.2 ^ 2 ∂(μ.prod μ)) := Real.sqrt_le_sqrt hnorm
  have hsq2 : Real.sqrt (∫ z : T × T, (q08gl_kap u A z.1 z.2 - q08e_kt μ k z.1 z.2) ^ 2 ∂(μ.prod μ)) ≤ |δ| := by
    rw [e2]
    calc _ ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt hδ
      _ = |δ| := Real.sqrt_sq_eq_abs δ
  have hnn : 0 ≤ ∑ i, ∑ j, A i j ^ 2 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have : Real.sqrt (∑ i, ∑ j, A i j ^ 2) ≤ Real.sqrt (∫ z : T × T, k z.1 z.2 ^ 2 ∂(μ.prod μ)) + |δ| := by
    refine h.trans ?_
    linarith
  calc ∑ i, ∑ j, A i j ^ 2 = Real.sqrt (∑ i, ∑ j, A i j ^ 2) ^ 2 := (Real.sq_sqrt hnn).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) this 2

theorem q08gl_alpha_bound (hu : q08gl_UData D.μ u) (b : Fin D.p) (α : Fin m → ℝ) (δ : ℝ)
    (hδ : ∫ x, (D.φ b x - pair D.μ (D.φ b) - ∑ k, α k * u k x) ^ 2 ∂D.μ ≤ δ ^ 2) :
    ∑ k, α k ^ 2 ≤ (2 * q08gl_Mphi D b + |δ|) ^ 2 := by
  haveI := q08_isProb_μ D
  obtain ⟨hφm, -⟩ := D.hφ b
  have hg1m : Measurable (fun x => D.φ b x - pair D.μ (D.φ b)) := hφm.sub_const _
  have hg1b : ∀ x, |D.φ b x - pair D.μ (D.φ b)| ≤ 2 * q08gl_Mphi D b := fun x => by
    have := q08gl_Mphi_spec D b x
    have := q08gl_pair_bdd D b
    calc |D.φ b x - pair D.μ (D.φ b)| ≤ |D.φ b x| + |pair D.μ (D.φ b)| := abs_sub _ _
      _ ≤ 2 * q08gl_Mphi D b := by linarith
  have hg1 : MemLp (fun x => D.φ b x - pair D.μ (D.φ b)) 2 D.μ :=
    MemLp.of_bound hg1m.aestronglyMeasurable (2 * q08gl_Mphi D b)
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hg1b x)
  have hg2m : Measurable (fun x => ∑ k, α k * u k x) :=
    Finset.measurable_sum _ fun k _ => measurable_const.mul (hu.meas k)
  choose Mu hMu using hu.bdd
  have hg2 : MemLp (fun x => ∑ k, α k * u k x) 2 D.μ :=
    MemLp.of_bound hg2m.aestronglyMeasurable (∑ k, |α k| * Mu k) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hMu k x) (abs_nonneg _))
  have hr : MemLp (fun x => D.φ b x - pair D.μ (D.φ b) - ∑ k, α k * u k x) 2 D.μ := hg1.sub hg2
  have h := q08gl_mink D.μ hg1 (hr.neg)
  have e1 : ∫ x, ((D.φ b x - pair D.μ (D.φ b)) + -(D.φ b x - pair D.μ (D.φ b) - ∑ k, α k * u k x)) ^ 2 ∂D.μ =
      ∑ k, α k ^ 2 := by
    have := q08gl_orth_comb hu α α
    rw [show ∑ k, α k * α k = ∑ k, α k ^ 2 from Finset.sum_congr rfl fun k _ => (sq (α k)).symm] at this
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only; ring
  have e2 : ∫ x, (-(D.φ b x - pair D.μ (D.φ b) - ∑ k, α k * u k x)) ^ 2 ∂D.μ =
      ∫ x, (D.φ b x - pair D.μ (D.φ b) - ∑ k, α k * u k x) ^ 2 ∂D.μ :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only [neg_sq])
  have hg1sq : ∫ x, (D.φ b x - pair D.μ (D.φ b)) ^ 2 ∂D.μ ≤ (2 * q08gl_Mphi D b) ^ 2 := by
    have h1 : ∫ x, (D.φ b x - pair D.μ (D.φ b)) ^ 2 ∂D.μ ≤ ∫ _x, (2 * q08gl_Mphi D b) ^ 2 ∂D.μ :=
      integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) (integrable_const _)
        (Eventually.of_forall fun x => by
          have := hg1b x
          nlinarith [abs_nonneg (D.φ b x - pair D.μ (D.φ b)), sq_abs (D.φ b x - pair D.μ (D.φ b))])
    simpa using h1
  simp only [Pi.neg_apply] at h
  beta_reduce at h
  rw [e1, e2] at h
  have hnn : 0 ≤ ∑ k, α k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hs1 : Real.sqrt (∫ x, (D.φ b x - pair D.μ (D.φ b)) ^ 2 ∂D.μ) ≤ 2 * q08gl_Mphi D b := by
    calc _ ≤ Real.sqrt ((2 * q08gl_Mphi D b) ^ 2) := Real.sqrt_le_sqrt hg1sq
      _ = 2 * q08gl_Mphi D b := Real.sqrt_sq (by have := q08gl_Mphi_nonneg D b; positivity)
  have hs2 : Real.sqrt (∫ x, (D.φ b x - pair D.μ (D.φ b) - ∑ k, α k * u k x) ^ 2 ∂D.μ) ≤ |δ| := by
    calc _ ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt hδ
      _ = |δ| := Real.sqrt_sq_eq_abs δ
  have : Real.sqrt (∑ k, α k ^ 2) ≤ 2 * q08gl_Mphi D b + |δ| := by linarith
  calc ∑ k, α k ^ 2 = Real.sqrt (∑ k, α k ^ 2) ^ 2 := (Real.sq_sqrt hnn).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) this 2

/-- Lipschitz transport to the index set `Option (Fin p)`. -/
theorem q08gl_Ft_lip {p : ℕ} (F : ℝ × (Fin p → ℝ) → ℝ) (K : ℝ≥0) (hF : LipschitzWith K F)
    (v v' : Option (Fin p) → ℝ) :
    |q08gl_Ft F v - q08gl_Ft F v'| ≤ (K : ℝ) * ∑ o, |v o - v' o| := by
  unfold q08gl_Ft
  have h1 := hF.dist_le_mul (v none, fun b => v (some b)) (v' none, fun b => v' (some b))
  rw [Real.dist_eq] at h1
  have hs : 0 ≤ ∑ b : Fin p, |v (some b) - v' (some b)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h2 : dist (v none, fun b => v (some b)) (v' none, fun b => v' (some b)) ≤
      |v none - v' none| + ∑ b : Fin p, |v (some b) - v' (some b)| := by
    rw [Prod.dist_eq]
    refine max_le ?_ ?_
    · simp only [Real.dist_eq]; linarith
    · rw [dist_pi_le_iff (by positivity)]
      intro b
      rw [Real.dist_eq]
      have : |v (some b) - v' (some b)| ≤ ∑ b : Fin p, |v (some b) - v' (some b)| :=
        Finset.single_le_sum (f := fun b : Fin p => |v (some b) - v' (some b)|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ b)
      linarith [abs_nonneg (v none - v' none)]
  rw [Fintype.sum_option]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 K.2)

theorem q08gl_Ft_bdd {p : ℕ} (F : ℝ × (Fin p → ℝ) → ℝ) (M : ℝ) (hM : ∀ z, |F z| ≤ M)
    (v : Option (Fin p) → ℝ) : |q08gl_Ft F v| ≤ M := hM _

/-- Quadratic growth of the finite-rank statistics. -/
theorem q08gl_fvec_growth (H : Matrix (Fin m) (Fin m) ℝ) (α : Fin D.p → Fin m → ℝ) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ (o : Option (Fin D.p)) (s : EuclideanSpace ℝ (Fin m)),
      |q08gl_fvec H α o s| ≤ Cf * (1 + ‖s‖ ^ 2) := by
  set c : ℝ := ∑ i, ∑ j, |H i j| with hc
  set a : ℝ := ∑ b, ∑ k, |α b k| with ha
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun k _ => abs_nonneg _
  refine ⟨(1 / 2) * (c + |H.trace|) + a, by positivity, fun o s => ?_⟩
  have hs : ∀ i, |s i| ≤ ‖s‖ := fun i => by
    have := PiLp.norm_apply_le s i
    simpa [Real.norm_eq_abs] using this
  have hn0 : 0 ≤ ‖s‖ := norm_nonneg _
  cases o with
  | none =>
    have hQ : |q08gl_Q H s| ≤ c * ‖s‖ ^ 2 := by
      unfold q08gl_Q
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [hc, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_mul, abs_mul]
      have h1 : |s i| * |s j| ≤ ‖s‖ ^ 2 := by
        rw [sq]; exact mul_le_mul (hs i) (hs j) (abs_nonneg _) hn0
      calc |H i j| * |s i| * |s j| = |H i j| * (|s i| * |s j|) := by ring
        _ ≤ |H i j| * ‖s‖ ^ 2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    show |(1 / 2) * (q08gl_Q H s - H.trace)| ≤ _
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h2 : |q08gl_Q H s - H.trace| ≤ c * ‖s‖ ^ 2 + |H.trace| := (abs_sub _ _).trans (by linarith)
    have : 0 ≤ ‖s‖ ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hc0 this, abs_nonneg H.trace]
  | some b =>
    show |∑ k, α b k * s k| ≤ _
    have h1 : |∑ k, α b k * s k| ≤ (∑ k, |α b k|) * ‖s‖ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hs k) (abs_nonneg _)
    have h2 : ∑ k, |α b k| ≤ a := by
      rw [ha]
      exact Finset.single_le_sum (f := fun b => ∑ k, |α b k|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ b)
    have h3 : ‖s‖ ≤ 1 + ‖s‖ ^ 2 := by nlinarith [sq_nonneg (‖s‖ - 1)]
    have h4 : 0 ≤ ∑ k, |α b k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    calc |∑ k, α b k * s k| ≤ (∑ k, |α b k|) * ‖s‖ := h1
      _ ≤ a * (1 + ‖s‖ ^ 2) := mul_le_mul h2 h3 hn0 ha0
      _ ≤ _ := by nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2) * (c + |H.trace|)) (by positivity : (0 : ℝ) ≤ 1 + ‖s‖ ^ 2)]

/-- Gaussian facts on the finite-rank weight. -/
theorem q08gl_b_facts (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef) (β g F2 : ℝ) (hβ : 0 ≤ β)
    (hF2 : ∑ i, ∑ j, A i j ^ 2 ≤ F2) :
    MemLp (fun s => Real.exp (-β * q08gl_psi A g s)) 2 (q08gl_gam m) ∧
      Integrable (fun s => Real.exp (-β * q08gl_psi A g s) ^ 3) (q08gl_gam m) ∧
      ∫ s, Real.exp (-β * q08gl_psi A g s) ^ 2 ∂(q08gl_gam m) ≤
        Real.exp (((2 : ℕ) : ℝ) * β * g / 2 + (((2 : ℕ) : ℝ) * β) ^ 2 * F2 / 2) ∧
      ∫ s, Real.exp (-β * q08gl_psi A g s) ^ 3 ∂(q08gl_gam m) ≤
        Real.exp (((3 : ℕ) : ℝ) * β * g / 2 + (((3 : ℕ) : ℝ) * β) ^ 2 * F2 / 2) := by
  have hbm : Measurable (fun s : EuclideanSpace ℝ (Fin m) => Real.exp (-β * q08gl_psi A g s)) :=
    (Real.continuous_exp.comp (continuous_const.mul (q08gl_psi_cont A g))).measurable
  have hbb : ∀ s : EuclideanSpace ℝ (Fin m), |Real.exp (-β * q08gl_psi A g s)| ≤ Real.exp (β * (A.trace + g) / 2) :=
    fun s => by
      rw [abs_of_pos (Real.exp_pos _)]; exact q08gl_b_bound A hA β g hβ s
  refine ⟨?_, ?_, q08gl_b_int_le A hA β g F2 hβ hF2 2, q08gl_b_int_le A hA β g F2 hβ hF2 3⟩
  · exact MemLp.of_bound hbm.aestronglyMeasurable _ (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]; exact hbb s)
  · refine Integrable.of_bound ((hbm.pow_const 3).aestronglyMeasurable) (Real.exp (β * (A.trace + g) / 2) ^ 3)
      (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hbb s) 3

/-- Gaussian facts on the finite-rank statistics. -/
theorem q08gl_f_facts (H : Matrix (Fin m) (Fin m) ℝ) (hH : ∀ i j, H i j = H j i) (α : Fin D.p → Fin m → ℝ)
    (FH2 : ℝ) (hFH : ∑ i, ∑ j, H i j ^ 2 ≤ FH2) (Fa : Fin D.p → ℝ) (hFa : ∀ b, ∑ k, α b k ^ 2 ≤ Fa b) :
    ∀ o : Option (Fin D.p), MemLp (q08gl_fvec H α o) 2 (q08gl_gam m) ∧
      Real.sqrt (∫ s, q08gl_fvec H α o s ^ 2 ∂(q08gl_gam m)) ≤ Real.sqrt FH2 + ∑ b, Real.sqrt (Fa b) := by
  intro o
  have hnn : 0 ≤ ∑ b, Real.sqrt (Fa b) := Finset.sum_nonneg fun b _ => Real.sqrt_nonneg _
  cases o with
  | none =>
    refine ⟨q08gl_fq_memLp 1 H, ?_⟩
    have h := q08gl_fq_L2 H hH
    have hFH0 : 0 ≤ ∑ i, ∑ j, H i j ^ 2 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have : ∫ s, q08gl_fq H s ^ 2 ∂(q08gl_gam m) ≤ FH2 := by
      have : (1 / 2) * ∑ i, ∑ j, H i j ^ 2 ≤ ∑ i, ∑ j, H i j ^ 2 := by linarith
      linarith
    exact (Real.sqrt_le_sqrt this).trans (by linarith)
  | some b =>
    refine ⟨q08gl_fl_memLp 1 (α b), ?_⟩
    have h := q08gl_fl_L2 (m := m) (α b)
    have h2 : ∫ s, q08gl_fl (α b) s ^ 2 ∂(q08gl_gam m) ≤ Fa b := h ▸ hFa b
    have h3 : Real.sqrt (Fa b) ≤ ∑ b', Real.sqrt (Fa b') :=
      Finset.single_le_sum (f := fun b' => Real.sqrt (Fa b')) (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ b)
    exact (Real.sqrt_le_sqrt h2).trans (by linarith [Real.sqrt_nonneg FH2])

end Constants

section Main

/-- `N⁻¹`-terms become small. -/
theorem q08gl_eventually_small (c ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, c / (N : ℝ) < ε := by
  have := (tendsto_const_div_atTop_nhds_zero_nat c).eventually (gt_mem_nhds hε)
  exact this

set_option maxHeartbeats 1600000 in
/-- **The finite-rank approximation theorem** (Gibbs side): for finite-rank data approximating the
kernels `g_c`, `h_c` and the tests `φ_a` to accuracy `δ`, the Gibbs expectation of `F` of the
statistic converges to the corresponding Gaussian Wick integral against `N(0, M)`,
`M (1 + β K') = 1`. -/
theorem q08gl_main (F : ℝ × (Fin D.p → ℝ) → ℝ) (hb : ∃ M, ∀ z, |F z| ≤ M)
    (hl : ∃ K : ℝ≥0, LipschitzWith K F) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (m : ℕ) (u : Fin m → Torus d → ℝ) (K' H' M : Matrix (Fin m) (Fin m) ℝ)
      (α : Fin D.p → Fin m → ℝ), q08gl_UData D.μ u → K'.PosSemidef → (∀ i j, H' i j = H' j i) →
      M * (1 + D.β • K') = 1 →
      ∫ z : Torus d × Torus d, (q08e_kt D.μ (fun x y => periodicRiesz d D.s (x - y)) z.1 z.2 -
          q08gl_kap u K' z.1 z.2) ^ 2 ∂(D.μ.prod D.μ) ≤ δ ^ 2 →
      ∫ z : Torus d × Torus d, (q08e_kt D.μ D.h z.1 z.2 - q08gl_kap u H' z.1 z.2) ^ 2 ∂(D.μ.prod D.μ) ≤ δ ^ 2 →
      (∀ b, ∫ x, (D.φ b x - pair D.μ (D.φ b) - ∑ k, α b k * u k x) ^ 2 ∂D.μ ≤ δ ^ 2) →
      ∀ᶠ N : ℕ in atTop,
        |∫ X : Config d N, F ((N : ℝ) * (modulatedEnergy D.h X D.μ -
              ∫ Y, modulatedEnergy D.h Y D.μ ∂(D.Gibbs N)),
            fun a => Real.sqrt N * ((1 / (N : ℝ)) * ∑ i, D.φ a (X i) -
              pair (firstMarginal (D.Gibbs N)) (D.φ a))) ∂(D.Gibbs N) -
          ∫ s, F ((1 / 2) * ∑ k, ∑ l, H' k l * (s k * s l - M k l), fun b => ∑ k, α b k * s k)
            ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) M)| ≤ η := by
  obtain ⟨MF, hMF⟩ := hb
  obtain ⟨KF, hKF⟩ := hl
  obtain ⟨Cp, hCp0, hCp⟩ := q08gl_pressure D
  have hFc : Continuous F := hKF.continuous
  have hβ : 0 ≤ D.β := D.hβ.le
  haveI := q08_isProb_μ D
  -- constants
  set Gg : ℝ := ∫ z : Torus d × Torus d, periodicRiesz d D.s (z.1 - z.2) ^ 2 ∂(D.μ.prod D.μ) with hGg
  set Gh : ℝ := ∫ z : Torus d × Torus d, D.h z.1 z.2 ^ 2 ∂(D.μ.prod D.μ) with hGh
  set F2 : ℝ := (Real.sqrt Gg + 1) ^ 2 with hF2
  set FH2 : ℝ := (Real.sqrt Gh + 1) ^ 2 with hFH2
  set Fa : Fin D.p → ℝ := fun b => (2 * q08gl_Mphi D b + 1) ^ 2 with hFa
  set gb : ℝ := q08gl_gbar D with hgb
  set B₂ : ℝ := Real.exp (((2 : ℕ) : ℝ) * D.β * gb / 2 + (((2 : ℕ) : ℝ) * D.β) ^ 2 * F2 / 2) with hB₂
  set B₃ : ℝ := Real.exp (((3 : ℕ) : ℝ) * D.β * gb / 2 + (((3 : ℕ) : ℝ) * D.β) ^ 2 * F2 / 2) with hB₃
  set Bf : ℝ := Real.sqrt FH2 + ∑ b, Real.sqrt (Fa b) with hBf
  have hBf0 : 0 ≤ Bf := add_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun b _ => Real.sqrt_nonneg _)
  obtain ⟨δGA, hδGA, hGA⟩ := q08gl_GA (ι := Option (Fin D.p)) (q08gl_Ft F) MF (KF : ℝ) (q08gl_Ft_cont F hFc)
    (fun v => hMF _) KF.2 (q08gl_Ft_lip F KF hKF) D.β hβ (Real.exp (-Cp)) (Real.exp Cp) (Real.exp Cp)
    (q08gl_BV D) B₂ B₃ Bf (Real.exp_pos _) (Real.exp_pos _).le (Real.exp_pos _).le (q08gl_BV_nonneg D)
    (Real.exp_pos _).le (Real.exp_pos _).le hBf0 η hη
  refine ⟨min 1 (min (δGA / 2) (δGA ^ 2 / 2)), lt_min one_pos (lt_min (by positivity) (by positivity)), ?_⟩
  intro m u K' H' M α hu hK' hH' hM hρK hρH hθ
  set δ' : ℝ := min 1 (min (δGA / 2) (δGA ^ 2 / 2)) with hδ'
  have hδ0 : 0 < δ' := lt_min one_pos (lt_min (by positivity) (by positivity))
  have hδ1 : δ' ≤ 1 := min_le_left _ _
  have hδ2 : δ' ≤ δGA / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ' ≤ δGA ^ 2 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  -- Gaussian-side facts
  have hFK : ∑ i, ∑ j, K' i j ^ 2 ≤ F2 := by
    have h := q08gl_frob_bound hu (fun x y : Torus d => periodicRiesz d D.s (x - y)) (q08gl_kg_meas D)
      (q08gl_g_sq_int D) (q08gl_kg_symm D) K' δ' hρK
    refine h.trans ?_
    rw [hF2]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    rw [abs_of_pos hδ0]
    linarith
  have hFH : ∑ i, ∑ j, H' i j ^ 2 ≤ FH2 := by
    have h := q08gl_frob_bound hu D.h D.hmeas (q08gl_h_sq_int D) D.hsymm H' δ' hρH
    refine h.trans ?_
    rw [hFH2]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    rw [abs_of_pos hδ0]
    linarith
  have hFα : ∀ b, ∑ k, α b k ^ 2 ≤ Fa b := fun b => by
    have h := q08gl_alpha_bound D hu b (α b) δ' (hθ b)
    refine h.trans ?_
    rw [hFa]
    refine pow_le_pow_left₀ (by have := q08gl_Mphi_nonneg D b; positivity) ?_ 2
    rw [abs_of_pos hδ0]
    linarith
  obtain ⟨hb2, hb3, hB2, hB3⟩ := q08gl_b_facts K' hK' D.β gb F2 hβ hFK
  have hfγ := q08gl_f_facts D H' hH' α FH2 hFH Fa hFα
  obtain ⟨Cf, hCf0, hCf⟩ := q08gl_fvec_growth D H' α
  -- Gibbs-side facts
  have hpow : ∀ N : ℕ, 1 ≤ N → ∀ q : ℕ, 1 ≤ q → q ≤ 3 →
      Integrable (fun X => q08gl_a D N X ^ q) (D.prodLaw N) ∧
        Real.exp (-Cp) ≤ ∫ X, q08gl_a D N X ^ q ∂(D.prodLaw N) ∧
        ∫ X, q08gl_a D N X ^ q ∂(D.prodLaw N) ≤ Real.exp Cp :=
    fun N hN q h1 h3 => q08gl_pow_facts D Cp hCp N hN q h1 h3
  have ha2 : ∀ n : ℕ, MemLp (q08gl_a D (n + 1)) 2 (D.prodLaw (n + 1)) := fun n =>
    (memLp_two_iff_integrable_sq (q08gl_a_meas D (n + 1)).aestronglyMeasurable).2
      (hpow (n + 1) (by omega) 2 (by norm_num) (by norm_num)).1
  have ha3 : ∀ n : ℕ, Integrable (fun X => q08gl_a D (n + 1) X ^ 3) (D.prodLaw (n + 1)) := fun n =>
    (hpow (n + 1) (by omega) 3 (by norm_num) (by norm_num)).1
  have hA2 : ∀ n : ℕ, ∫ X, q08gl_a D (n + 1) X ^ 2 ∂(D.prodLaw (n + 1)) ≤ Real.exp Cp := fun n =>
    (hpow (n + 1) (by omega) 2 (by norm_num) (by norm_num)).2.2
  have hA3 : ∀ n : ℕ, ∫ X, q08gl_a D (n + 1) X ^ 3 ∂(D.prodLaw (n + 1)) ≤ Real.exp Cp := fun n =>
    (hpow (n + 1) (by omega) 3 (by norm_num) (by norm_num)).2.2
  have hz : ∀ n : ℕ, Real.exp (-Cp) ≤ ∫ X, q08gl_a D (n + 1) X ∂(D.prodLaw (n + 1)) := fun n => by
    have := (hpow (n + 1) (by omega) 1 le_rfl (by norm_num)).2.1
    simpa using this
  have hzpos : ∀ n : ℕ, 0 < ∫ X, q08gl_a D (n + 1) X ∂(D.prodLaw (n + 1)) := fun n =>
    lt_of_lt_of_le (Real.exp_pos _) (hz n)
  -- the CLT
  have hclt : ∀ Ψ : EuclideanSpace ℝ (Fin m) → ℝ, Continuous Ψ → ∀ C₀ : ℝ,
      (∀ s, |Ψ s| ≤ C₀ * (1 + ‖s‖ ^ 2)) →
        Tendsto (fun n : ℕ => ∫ X : Config d (n + 1), Ψ (q08gl_Sv u (n + 1) X) ∂(D.prodLaw (n + 1))) atTop
          (𝓝 (∫ s, Ψ s ∂(q08gl_gam m))) := by
    intro Ψ hΨ C₀ hgr
    have hu2 : ∀ i, MemLp (u i) 2 D.μ := fun i => by
      obtain ⟨M', hM'⟩ := hu.bdd i
      exact MemLp.of_bound (hu.meas i).aestronglyMeasurable M'
        (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM' x)
    have := q08_clt_quadratic D.μ m u hu.meas hu2 hu.cent hu.orth Ψ hΨ C₀ hgr
    exact (tendsto_add_atTop_iff_nat 1).2 this
  -- closeness of the true statistics to the finite-rank ones
  obtain ⟨CH, hCH⟩ := q08gl_kap_bdd H' hu
  obtain ⟨CK, hCK⟩ := q08gl_kap_bdd K' hu
  have hEH : ∀ x, |q08gl_kap u H' x x - H'.trace| ≤ CH + |H'.trace| := fun x =>
    (abs_sub _ _).trans (add_le_add (hCH x x) le_rfl)
  have hEK : ∀ x, |q08gl_kap u K' x x - K'.trace| ≤ CK + |K'.trace| := fun x =>
    (abs_sub _ _).trans (add_le_add (hCK x x) le_rfl)
  have hδGA2 : 0 < δGA ^ 2 / 2 := by positivity
  have hδGA4 : 0 < δGA ^ 4 / 2 := by positivity
  have hYVev : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ ∀ o : Option (Fin D.p),
      MemLp (fun X : Config d N => q08gl_V D N o X - q08gl_fvec H' α o (q08gl_Sv u N X)) 2 (D.prodLaw N) ∧
        Real.sqrt (∫ X, (q08gl_V D N o X - q08gl_fvec H' α o (q08gl_Sv u N X)) ^ 2 ∂(D.prodLaw N)) ≤ δGA := by
    filter_upwards [eventually_ge_atTop 1,
      q08gl_eventually_small (3 * Gh + 3 * (CH + |H'.trace|) ^ 2 / 4) (δGA ^ 2 / 2) hδGA2] with N hN hsmall
    refine ⟨hN, fun o => ?_⟩
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    cases o with
    | none =>
      obtain ⟨hm1, hi1⟩ := q08gl_hYV_none D hu H' hH' α N hN (CH + |H'.trace|) hEH
      refine ⟨hm1, ?_⟩
      refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      have h1 : (3 / 2) * ∫ z : Torus d × Torus d, (q08e_kt D.μ D.h z.1 z.2 - q08gl_kap u H' z.1 z.2) ^ 2
          ∂(D.μ.prod D.μ) ≤ (3 / 2) * (δGA / 2) ^ 2 := by
        refine mul_le_mul_of_nonneg_left (hρH.trans ?_) (by norm_num)
        exact pow_le_pow_left₀ hδ0.le hδ2 2
      have h2 : 3 * Gh / N + 3 * (CH + |H'.trace|) ^ 2 / (4 * N) =
          (3 * Gh + 3 * (CH + |H'.trace|) ^ 2 / 4) / N := by field_simp
      have h5 : (3 / 2) * (δGA / 2) ^ 2 = 3 / 8 * δGA ^ 2 := by ring
      have h6 := sq_nonneg δGA
      linarith [hi1, h1, h2, hsmall, h5, h6]
    | some b =>
      obtain ⟨hm1, hi1⟩ := q08gl_hYV_some D hu α b N hN
      refine ⟨hm1, ?_⟩
      refine Real.sqrt_le_iff.2 ⟨hδGA.le, ?_⟩
      have h4 : ∫ x, (D.φ b x - pair D.μ (D.φ b) - ∑ k, α b k * u k x) ^ 2 ∂D.μ ≤ δ' ^ 2 := hθ b
      have : δ' ^ 2 ≤ δGA ^ 2 := pow_le_pow_left₀ hδ0.le (by linarith) 2
      show ∫ X, (q08gl_V D N (some b) X - q08gl_fvec H' α (some b) (q08gl_Sv u N X)) ^ 2 ∂(D.prodLaw N) ≤ δGA ^ 2
      have e : ∫ X, (q08gl_V D N (some b) X - q08gl_fvec H' α (some b) (q08gl_Sv u N X)) ^ 2 ∂(D.prodLaw N) =
          ∫ x, (D.φ b x - pair D.μ (D.φ b) - ∑ k, α b k * u k x) ^ 2 ∂D.μ := hi1
      rw [e]; linarith
  have hK'sym : ∀ i j, K' i j = K' j i := fun i j => by
    have := hK'.isHermitian.apply j i
    simpa using this
  have hxyev : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧
      Integrable (fun X : Config d N => |q08gl_x D N X - q08gl_psi K' gb (q08gl_Sv u N X)|) (D.prodLaw N) ∧
        ∫ X, |q08gl_x D N X - q08gl_psi K' gb (q08gl_Sv u N X)| ∂(D.prodLaw N) ≤ δGA ^ 2 := by
    filter_upwards [eventually_ge_atTop 1,
      q08gl_eventually_small (3 * Gg + 3 * (CK + |K'.trace|) ^ 2 / 4) (δGA ^ 4 / 2) hδGA4] with N hN hsmall
    refine ⟨hN, ?_⟩
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    obtain ⟨hm1, hi1⟩ := q08gl_hxy D hu K' hK'sym N hN (CK + |K'.trace|) hEK
    refine ⟨(hm1.integrable one_le_two).abs, ?_⟩
    have h0 := q08gl_integral_le_sqrt (D.prodLaw N) hm1
    refine h0.trans ?_
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have h1 : (3 / 2) * ∫ z : Torus d × Torus d, (q08e_kt D.μ (fun x y => periodicRiesz d D.s (x - y)) z.1 z.2 -
        q08gl_kap u K' z.1 z.2) ^ 2 ∂(D.μ.prod D.μ) ≤ (3 / 2) * (δGA ^ 2 / 2) ^ 2 := by
      refine mul_le_mul_of_nonneg_left (hρK.trans ?_) (by norm_num)
      exact pow_le_pow_left₀ hδ0.le hδ3 2
    have h2 : 3 * Gg / N + 3 * (CK + |K'.trace|) ^ 2 / (4 * N) =
        (3 * Gg + 3 * (CK + |K'.trace|) ^ 2 / 4) / N := by field_simp
    have h5 : (3 / 2) * (δGA ^ 2 / 2) ^ 2 = 3 / 8 * δGA ^ 4 := by ring
    have h6 : ((δGA ^ 2) ^ 2) = δGA ^ 4 := by ring
    have h7 := pow_pos hδGA 4
    linarith [hi1, h1, h2, hsmall, h5, h6, h7]
  have hYV' : ∀ᶠ n : ℕ in atTop, ∀ o : Option (Fin D.p),
      MemLp (fun ω => q08gl_V D (n + 1) o ω - q08gl_fvec H' α o (q08gl_Sv u (n + 1) ω)) 2 (D.prodLaw (n + 1)) ∧
        Real.sqrt (∫ ω, (q08gl_V D (n + 1) o ω - q08gl_fvec H' α o (q08gl_Sv u (n + 1) ω)) ^ 2
          ∂(D.prodLaw (n + 1))) ≤ δGA :=
    (tendsto_add_atTop_nat 1).eventually (hYVev.mono fun N hN => hN.2)
  have hxy' : ∀ᶠ n : ℕ in atTop,
      Integrable (fun ω => |q08gl_x D (n + 1) ω - q08gl_psi K' gb (q08gl_Sv u (n + 1) ω)|) (D.prodLaw (n + 1)) ∧
        ∫ ω, |q08gl_x D (n + 1) ω - q08gl_psi K' gb (q08gl_Sv u (n + 1) ω)| ∂(D.prodLaw (n + 1)) ≤ δGA ^ 2 :=
    (tendsto_add_atTop_nat 1).eventually (hxyev.mono fun N hN => hN.2)
  have hmain := hGA m (fun n => Config d (n + 1)) (fun n => inferInstance) (fun n => D.prodLaw (n + 1))
    (fun n => q08gl_prodLaw_prob D (n + 1)) (fun n => q08gl_Sv u (n + 1))
    (fun n => q08gl_Sv_meas u hu.meas (n + 1)) (q08gl_gam m) inferInstance hclt (q08gl_psi K' gb)
    (q08gl_psi_cont K' gb) (q08gl_fvec H' α) (fun o => q08gl_fvec_cont H' α o) Cf hCf0 hCf hb2 hb3 hB2 hB3
    (fun o => (hfγ o).1) (fun o => (hfγ o).2) (fun n => q08gl_a D (n + 1)) (fun n => q08gl_x D (n + 1))
    (fun n => q08gl_V D (n + 1)) (fun n => q08gl_x_meas D (n + 1)) (fun n ω => q08gl_a_eq D (n + 1) ω)
    ha2 ha3 hA2 hA3 hz (fun n o => q08gl_V_meas D (n + 1) o)
    (fun n o => q08gl_V_memLp D (n + 1) (by omega) o) (fun n o => q08gl_V_L2 D (n + 1) (by omega) o)
    hYV' hxy'
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hmain
  filter_upwards [eventually_ge_atTop (n₀ + 1)] with N hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have h := hn₀ n (by omega)
  rw [← q08gl_gibbs_Phi D (by omega) (hzpos n) F,
    q08gl_tilt_ident K' H' M hK' D.β gb hβ hM α F hFc MF hMF] at h
  exact h

end Main

end HRS.Q08

end
