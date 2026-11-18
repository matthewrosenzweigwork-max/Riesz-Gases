import HRS.Equilibrium.QuadraticLimit.Features
import HRS.Equilibrium.QuadraticLimit.GibbsAuxE

/-!
# Lemma 7.5, `q08_gibbs_approx`: finite-rank kernels and the Hoeffding `L²` approximation
(prefix `q08gl_`)

For a finite bounded orthonormal centred family `u` and a symmetric matrix `A`, the finite-rank
degenerate kernel `κ_A(x,y) = ∑ A_kl u_k(x) u_l(y)` satisfies
`½ (S_Nᵀ A S_N - tr A) = (2N)⁻¹ ∑_{i≠j} κ_A(X_i,X_j) + ½ (N⁻¹ ∑_i κ_A(X_i,X_i) - tr A)`,
and the centred energy `N F_N^k + ½∬k` of an `L²` kernel `k` is within `L²(μ^{⊗N})` of it, up to
`‖k_c - κ_A‖_{L²} + O(N^{-1/2})`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q08

section Kappa

variable {T : Type*} [MeasurableSpace T] {m : ℕ}

/-- The finite-rank kernel `∑ A_kl u_k(x) u_l(y)`. -/
def q08gl_kap (u : Fin m → T → ℝ) (A : Matrix (Fin m) (Fin m) ℝ) (x y : T) : ℝ :=
  ∑ k, ∑ l, A k l * u k x * u l y

/-- Hypotheses on the finite family `u`. -/
structure q08gl_UData (μ : Measure T) (u : Fin m → T → ℝ) : Prop where
  meas : ∀ k, Measurable (u k)
  bdd : ∀ k, ∃ M, ∀ x, |u k x| ≤ M
  cent : ∀ k, ∫ x, u k x ∂μ = 0
  orth : ∀ k l, ∫ x, u k x * u l x ∂μ = if k = l then 1 else 0

variable {μ : Measure T} [IsProbabilityMeasure μ] {u : Fin m → T → ℝ}

theorem q08gl_kap_meas (A : Matrix (Fin m) (Fin m) ℝ) (hu : ∀ k, Measurable (u k)) :
    Measurable (Function.uncurry (q08gl_kap u A)) := by
  unfold q08gl_kap Function.uncurry
  refine Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_
  exact ((measurable_const.mul ((hu k).comp measurable_fst)).mul ((hu l).comp measurable_snd))

theorem q08gl_kap_symm (A : Matrix (Fin m) (Fin m) ℝ) (hA : ∀ k l, A k l = A l k) (x y : T) :
    q08gl_kap u A x y = q08gl_kap u A y x := by
  unfold q08gl_kap
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hA k l]; ring

theorem q08gl_kap_bdd (A : Matrix (Fin m) (Fin m) ℝ) (hu : q08gl_UData μ u) :
    ∃ C, ∀ x y, |q08gl_kap u A x y| ≤ C := by
  choose M hM using hu.bdd
  refine ⟨∑ k, ∑ l, |A k l| * M k * M l, fun x y => ?_⟩
  unfold q08gl_kap
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hM k x) (abs_nonneg _)) (hM l y) (abs_nonneg _)
    (by have := (abs_nonneg (u k x)).trans (hM k x); positivity)

theorem q08gl_kap_deg (A : Matrix (Fin m) (Fin m) ℝ) (hu : q08gl_UData μ u) (x : T) :
    ∫ y, q08gl_kap u A x y ∂μ = 0 := by
  have hint : ∀ l, Integrable (u l) μ := fun l => by
    obtain ⟨M, hM⟩ := hu.bdd l
    exact Integrable.of_bound (hu.meas l).aestronglyMeasurable M
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hM y)
  unfold q08gl_kap
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (hint l).const_mul _]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => (hint l).const_mul _]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [integral_const_mul, hu.cent l, mul_zero]

theorem q08gl_int_u (hu : q08gl_UData μ u) (k : Fin m) : Integrable (u k) μ := by
  obtain ⟨M, hM⟩ := hu.bdd k
  exact Integrable.of_bound (hu.meas k).aestronglyMeasurable M
    (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hM y)

theorem q08gl_int_uu (hu : q08gl_UData μ u) (k l : Fin m) : Integrable (fun x => u k x * u l x) μ := by
  obtain ⟨M, hM⟩ := hu.bdd k
  obtain ⟨M', hM'⟩ := hu.bdd l
  refine Integrable.of_bound ((hu.meas k).mul (hu.meas l)).aestronglyMeasurable (M * M')
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hM y) (hM' y) (abs_nonneg _) ((abs_nonneg _).trans (hM y))

/-- Orthonormality for finite linear combinations. -/
theorem q08gl_orth_comb (hu : q08gl_UData μ u) (c d : Fin m → ℝ) :
    ∫ y, (∑ k, c k * u k y) * (∑ l, d l * u l y) ∂μ = ∑ k, c k * d k := by
  have h1 : ∀ y, (∑ k, c k * u k y) * (∑ l, d l * u l y) = ∑ k, ∑ l, (c k * d l) * (u k y * u l y) := by
    intro y; rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [h1]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (q08gl_int_uu hu k l).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => (q08gl_int_uu hu k l).const_mul _]
  simp_rw [integral_const_mul, hu.orth k]
  simp

theorem q08gl_kap_memLp (A : Matrix (Fin m) (Fin m) ℝ) (hu : q08gl_UData μ u) :
    MemLp (Function.uncurry (q08gl_kap u A)) 2 (μ.prod μ) := by
  obtain ⟨C, hC⟩ := q08gl_kap_bdd A hu
  exact MemLp.of_bound (q08gl_kap_meas A hu.meas).aestronglyMeasurable C
    (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs, Function.uncurry] using hC z.1 z.2)

theorem q08gl_kap_sq (A : Matrix (Fin m) (Fin m) ℝ) (hu : q08gl_UData μ u) :
    ∫ z : T × T, q08gl_kap u A z.1 z.2 ^ 2 ∂(μ.prod μ) = ∑ k, ∑ l, A k l ^ 2 := by
  have hint : Integrable (fun z : T × T => q08gl_kap u A z.1 z.2 ^ 2) (μ.prod μ) :=
    (q08gl_kap_memLp A hu).integrable_sq
  rw [integral_prod _ hint]
  -- for fixed `x`, `κ(x, ·) = ∑_l c_l(x) u_l`
  set c : Fin m → T → ℝ := fun l x => ∑ k, A k l * u k x with hc
  have hk : ∀ x y, q08gl_kap u A x y = ∑ l, c l x * u l y := by
    intro x y
    unfold q08gl_kap
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hc]; simp only [Finset.sum_mul]
  have hy : ∀ x, ∫ y, q08gl_kap u A x y ^ 2 ∂μ = ∑ l, c l x ^ 2 := by
    intro x
    have := q08gl_orth_comb hu (fun l => c l x) (fun l => c l x)
    simp_rw [hk, sq]
    simpa [sq] using this
  simp_rw [hy]
  have hcint : ∀ l, Integrable (fun x => c l x ^ 2) μ := by
    intro l
    have : ∀ x, c l x ^ 2 = ∑ k, ∑ k', (A k l * A k' l) * (u k x * u k' x) := by
      intro x; rw [hc]; simp only [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
      ring
    simp_rw [this]
    exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun k' _ => (q08gl_int_uu hu k k').const_mul _
  rw [integral_finsetSum _ fun l _ => hcint l]
  calc ∑ l, ∫ x, c l x ^ 2 ∂μ = ∑ l, ∑ k, A k l ^ 2 := by
        refine Finset.sum_congr rfl fun l _ => ?_
        have := q08gl_orth_comb hu (fun k => A k l) (fun k => A k l)
        simpa [hc, sq] using this
    _ = ∑ k, ∑ l, A k l ^ 2 := Finset.sum_comm

theorem q08gl_kap_diag (A : Matrix (Fin m) (Fin m) ℝ) (hu : q08gl_UData μ u) :
    ∫ x, q08gl_kap u A x x ∂μ = A.trace := by
  unfold q08gl_kap
  have hi : ∀ k l, Integrable (fun x => A k l * u k x * u l x) μ := fun k l => by
    have := (q08gl_int_uu hu k l).const_mul (A k l)
    simpa [mul_assoc] using this
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hi k l]
  simp_rw [integral_finsetSum _ fun l _ => hi _ l]
  unfold Matrix.trace
  refine Finset.sum_congr rfl fun k _ => ?_
  have : ∀ l, ∫ x, A k l * u k x * u l x ∂μ = if k = l then A k l else 0 := by
    intro l
    have : ∀ x, A k l * u k x * u l x = A k l * (u k x * u l x) := fun x => by ring
    simp_rw [this, integral_const_mul, hu.orth k l]
    by_cases h : k = l <;> simp [h]
  simp_rw [this]
  simp

end Kappa

section Approx

variable {T : Type*} [MeasurableSpace T] {m : ℕ} {μ : Measure T} [IsProbabilityMeasure μ]
  {u : Fin m → T → ℝ}

/-- The normalised sum `S_N = N^{-1/2} ∑_i u(X_i)`. -/
def q08gl_Sv (u : Fin m → T → ℝ) (N : ℕ) (X : Fin N → T) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun k => (Real.sqrt N)⁻¹ * ∑ i, u k (X i))

/-- The quadratic form of `S_N` is the double sum of the finite-rank kernel. -/
theorem q08gl_quad_id (A : Matrix (Fin m) (Fin m) ℝ) (N : ℕ) (hN : 1 ≤ N) (X : Fin N → T) :
    q08gl_Q A (q08gl_Sv u N X) =
      (1 / (N : ℝ)) * (q08e_DD (q08gl_kap u A) X + ∑ i, q08gl_kap u A (X i) (X i)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ = 1 / (N : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt hN0.le, one_div]
  have h1 : ∑ i, ∑ j, q08gl_kap u A (X i) (X j) =
      q08e_DD (q08gl_kap u A) X + ∑ i, q08gl_kap u A (X i) (X i) := by
    unfold q08e_DD
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∀ j, q08gl_kap u A (X i) (X j) = (if i = j then 0 else q08gl_kap u A (X i) (X j)) +
        (if i = j then q08gl_kap u A (X i) (X j) else 0) := by
      intro j; split_ifs <;> simp
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp
  have key : ∀ f : Fin m → Fin m → Fin N → Fin N → ℝ,
      ∑ k, ∑ l, ∑ i, ∑ j, f k l i j = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := by
    intro f
    calc ∑ k, ∑ l, ∑ i, ∑ j, f k l i j = ∑ k, ∑ i, ∑ l, ∑ j, f k l i j :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ l, ∑ j, f k l i j := Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ j, ∑ l, f k l i j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have e1 : ∀ k l : Fin m, A k l * ((Real.sqrt N)⁻¹ * ∑ i, u k (X i)) * ((Real.sqrt N)⁻¹ * ∑ j, u l (X j)) =
      (1 / (N : ℝ)) * ∑ i, ∑ j, A k l * u k (X i) * u l (X j) := by
    intro k l
    rw [← hsq]
    calc A k l * ((Real.sqrt N)⁻¹ * ∑ i, u k (X i)) * ((Real.sqrt N)⁻¹ * ∑ j, u l (X j))
        = ((Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹) * (A k l * ((∑ i, u k (X i)) * (∑ j, u l (X j)))) := by ring
      _ = ((Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹) * (A k l * ∑ i, ∑ j, u k (X i) * u l (X j)) := by
        rw [Finset.sum_mul_sum]
      _ = _ := by
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
  have hQ : q08gl_Q A (q08gl_Sv u N X) = ∑ k, ∑ l, (1 / (N : ℝ)) * ∑ i, ∑ j, A k l * u k (X i) * u l (X j) := by
    unfold q08gl_Q
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [q08gl_Sv, WithLp.ofLp_toLp]
    exact e1 k l
  rw [hQ, ← h1]
  have e2 : ∑ k, ∑ l, (1 / (N : ℝ)) * ∑ i, ∑ j, A k l * u k (X i) * u l (X j) =
      (1 / (N : ℝ)) * ∑ k, ∑ l, ∑ i, ∑ j, A k l * u k (X i) * u l (X j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
  rw [e2]
  congr 1
  rw [key (fun k l i j => A k l * u k (X i) * u l (X j))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rfl

theorem q08gl_DD_sub (f g : T → T → ℝ) {N : ℕ} (X : Fin N → T) :
    q08e_DD (fun x y => f x y - g x y) X = q08e_DD f X - q08e_DD g X := by
  unfold q08e_DD
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

set_option maxHeartbeats 800000 in
/-- Hoeffding approximation of the centred energy of an `L²` kernel by the finite-rank statistic. -/
theorem q08gl_quad_L2 (hu : q08gl_UData μ u) (k : T → T → ℝ) (hm : Measurable (Function.uncurry k))
    (hk : Integrable (fun z : T × T => k z.1 z.2 ^ 2) (μ.prod μ)) (hs : ∀ x y, k x y = k y x)
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : ∀ i j, A i j = A j i) (N : ℕ) (hN : 1 ≤ N) (E : ℝ)
    (hE : ∀ x, |q08gl_kap u A x x - A.trace| ≤ E) :
    MemLp (fun X : Fin N → T => q08e_Z μ k X - (1 / 2) * (q08gl_Q A (q08gl_Sv u N X) - A.trace)) 2
        (Measure.pi fun _ : Fin N => μ) ∧
      ∫ X : Fin N → T, (q08e_Z μ k X - (1 / 2) * (q08gl_Q A (q08gl_Sv u N X) - A.trace)) ^ 2
          ∂(Measure.pi fun _ : Fin N => μ) ≤
        (3 / 2) * ∫ z : T × T, (q08e_kt μ k z.1 z.2 - q08gl_kap u A z.1 z.2) ^ 2 ∂(μ.prod μ) +
          3 * (∫ z : T × T, k z.1 z.2 ^ 2 ∂(μ.prod μ)) / N + 3 * E ^ 2 / (4 * N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set πN : Measure (Fin N → T) := Measure.pi fun _ : Fin N => μ with hπN
  set κ' : T → T → ℝ := fun x y => q08e_kt μ k x y - q08gl_kap u A x y with hκ'
  have hκ'm : Measurable (Function.uncurry κ') :=
    (q08e_kt_meas μ k hm hk).sub (q08gl_kap_meas A hu.meas)
  have hκ's : ∀ x y, κ' x y = κ' y x := fun x y => by
    simp only [hκ']; rw [q08e_kt_symm μ k hs x y, q08gl_kap_symm A hA x y]
  have hκ'L2 : MemLp (Function.uncurry κ') 2 (μ.prod μ) :=
    (q08e_kt_memLp μ k hm hk).sub (q08gl_kap_memLp A hu)
  have hκ'd : ∀ x, ∫ y, κ' x y ∂μ = 0 := by
    intro x
    by_cases hx : Integrable (fun y => q08e_kt μ k x y) μ
    · have : Integrable (fun y => q08gl_kap u A x y) μ := by
        obtain ⟨C, hC⟩ := q08gl_kap_bdd A hu
        exact Integrable.of_bound ((q08gl_kap_meas A hu.meas).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable C
          (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC x y)
      simp only [hκ']
      rw [integral_sub hx this, q08e_kt_degenerate μ k hm hk x, q08gl_kap_deg A hu x, sub_zero]
    · apply integral_undef
      intro hint
      apply hx
      have : Integrable (fun y => q08gl_kap u A x y) μ := by
        obtain ⟨C, hC⟩ := q08gl_kap_bdd A hu
        exact Integrable.of_bound ((q08gl_kap_meas A hu.meas).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable C
          (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC x y)
      refine (hint.add this).congr (Eventually.of_forall fun y => ?_)
      simp only [hκ', Pi.add_apply]; ring
  obtain ⟨hDmem, hDint⟩ := q08e_DD_second μ κ' hκ'm hκ's hκ'd hκ'L2 N
  -- the linear parts
  obtain ⟨hl2, hl0, hlle⟩ := q08e_ell_facts μ k hm hk
  have hlm : Measurable (fun x => q08e_a μ k x - q08e_m μ k) :=
    (q08e_a_meas' μ k hm hk).sub measurable_const
  obtain ⟨hLmem, hLint⟩ := q08e_lin_second μ (fun x => q08e_a μ k x - q08e_m μ k) hlm hl2 hl0 N
  -- the diagonal part
  set w : T → ℝ := fun x => q08gl_kap u A x x - A.trace with hw
  have hdm : Measurable (fun x => q08gl_kap u A x x) :=
    (q08gl_kap_meas A hu.meas).comp (measurable_id.prodMk measurable_id)
  have hwm : Measurable w := hdm.sub measurable_const
  have hw2 : MemLp w 2 μ :=
    MemLp.of_bound hwm.aestronglyMeasurable E (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hE x)
  have hdint : Integrable (fun x => q08gl_kap u A x x) μ := by
    obtain ⟨C, hC⟩ := q08gl_kap_bdd A hu
    exact Integrable.of_bound hdm.aestronglyMeasurable C
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x x)
  have hw0 : ∫ x, w x ∂μ = 0 := by
    simp only [hw]
    rw [integral_sub hdint (integrable_const _), q08gl_kap_diag A hu]
    simp
  obtain ⟨hWmem, hWint⟩ := q08e_lin_second μ w hwm hw2 hw0 N
  have hwsq : ∫ x, w x ^ 2 ∂μ ≤ E ^ 2 := by
    have h1 : ∫ x, w x ^ 2 ∂μ ≤ ∫ x, E ^ 2 ∂μ :=
      integral_mono hw2.integrable_sq (integrable_const _) fun x => by
        have := hE x
        simp only [hw]
        nlinarith [abs_nonneg (q08gl_kap u A x x - A.trace), sq_abs (q08gl_kap u A x x - A.trace)]
    simpa using h1
  -- the three pieces
  set P1 : (Fin N → T) → ℝ := fun X => (1 / (2 * (N : ℝ))) * q08e_DD κ' X with hP1
  set P2 : (Fin N → T) → ℝ := fun X => (1 / (N : ℝ)) * ∑ i, (q08e_a μ k (X i) - q08e_m μ k) with hP2
  set P3 : (Fin N → T) → ℝ := fun X => (1 / (2 * (N : ℝ))) * ∑ i, w (X i) with hP3
  have hmem1 : MemLp P1 2 πN := hDmem.const_mul _
  have hmem2 : MemLp P2 2 πN := hLmem.const_mul _
  have hmem3 : MemLp P3 2 πN := hWmem.const_mul _
  have hid : ∀ X : Fin N → T, q08e_Z μ k X - (1 / 2) * (q08gl_Q A (q08gl_Sv u N X) - A.trace) =
      P1 X - P2 X - P3 X := by
    intro X
    rw [q08e_Z_eq μ k hN X, q08gl_quad_id A N hN X]
    simp only [hP1, hP2, hP3, hκ', hw]
    rw [q08gl_DD_sub (q08e_kt μ k) (q08gl_kap u A)]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hfun : (fun X : Fin N → T => q08e_Z μ k X - (1 / 2) * (q08gl_Q A (q08gl_Sv u N X) - A.trace)) =
      fun X => P1 X - P2 X - P3 X := funext hid
  rw [hfun]
  simp_rw [hid]
  refine ⟨(hmem1.sub hmem2).sub hmem3, ?_⟩
  have hρ : ∫ z : T × T, (q08e_kt μ k z.1 z.2 - q08gl_kap u A z.1 z.2) ^ 2 ∂(μ.prod μ) =
      ∫ z : T × T, κ' z.1 z.2 ^ 2 ∂(μ.prod μ) := rfl
  rw [hρ]
  set r : ℝ := ∫ z : T × T, κ' z.1 z.2 ^ 2 ∂(μ.prod μ) with hr
  set Qk : ℝ := ∫ z : T × T, k z.1 z.2 ^ 2 ∂(μ.prod μ) with hQk
  have hr0 : 0 ≤ r := integral_nonneg fun z => sq_nonneg _
  have hI1 : ∫ X, P1 X ^ 2 ∂πN = (1 / (2 * (N : ℝ))) ^ 2 * (2 * N * (N - 1) * r) := by
    simp only [hP1, mul_pow]
    rw [integral_const_mul, hDint]
  have hI2 : ∫ X, P2 X ^ 2 ∂πN = (1 / (N : ℝ)) ^ 2 * (N * ∫ x, (q08e_a μ k x - q08e_m μ k) ^ 2 ∂μ) := by
    simp only [hP2, mul_pow]
    rw [integral_const_mul, hLint]
  have hI3 : ∫ X, P3 X ^ 2 ∂πN = (1 / (2 * (N : ℝ))) ^ 2 * (N * ∫ x, w x ^ 2 ∂μ) := by
    simp only [hP3, mul_pow]
    rw [integral_const_mul, hWint]
  have hbd : ∫ X, (P1 X - P2 X - P3 X) ^ 2 ∂πN ≤
      ∫ X, (3 * P1 X ^ 2 + 3 * P2 X ^ 2 + 3 * P3 X ^ 2) ∂πN := by
    refine integral_mono ((hmem1.sub hmem2).sub hmem3).integrable_sq
      (((hmem1.integrable_sq.const_mul 3).add (hmem2.integrable_sq.const_mul 3)).add
        (hmem3.integrable_sq.const_mul 3)) fun X => ?_
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (P1 X + P2 X), sq_nonneg (P1 X + P3 X), sq_nonneg (P2 X - P3 X),
      sq_nonneg (P1 X - P2 X + P3 X), sq_nonneg (P1 X - P2 X - P3 X)]
  have hsum : ∫ X, (3 * P1 X ^ 2 + 3 * P2 X ^ 2 + 3 * P3 X ^ 2) ∂πN =
      3 * ∫ X, P1 X ^ 2 ∂πN + 3 * ∫ X, P2 X ^ 2 ∂πN + 3 * ∫ X, P3 X ^ 2 ∂πN := by
    have i1 : Integrable (fun X => 3 * P1 X ^ 2) πN := hmem1.integrable_sq.const_mul 3
    have i2 : Integrable (fun X => 3 * P2 X ^ 2) πN := hmem2.integrable_sq.const_mul 3
    have i3 : Integrable (fun X => 3 * P3 X ^ 2) πN := hmem3.integrable_sq.const_mul 3
    have i12 : Integrable (fun X => 3 * P1 X ^ 2 + 3 * P2 X ^ 2) πN := i1.add i2
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul, integral_const_mul]
  refine hbd.trans ?_
  rw [hsum]
  rw [hI1, hI2, hI3]
  have hwsq' := hwsq
  have hl' : ∫ x, (q08e_a μ k x - q08e_m μ k) ^ 2 ∂μ ≤ Qk := hlle
  have e1 : 3 * ((1 / (2 * (N : ℝ))) ^ 2 * (2 * N * (N - 1) * r)) = (3 / 2) * r - (3 / 2) * r / N := by
    field_simp
  have e2 : (1 / (N : ℝ)) ^ 2 * (N * ∫ x, (q08e_a μ k x - q08e_m μ k) ^ 2 ∂μ) =
      (∫ x, (q08e_a μ k x - q08e_m μ k) ^ 2 ∂μ) / N := by field_simp
  have e3 : (1 / (2 * (N : ℝ))) ^ 2 * (N * ∫ x, w x ^ 2 ∂μ) = (∫ x, w x ^ 2 ∂μ) / (4 * N) := by
    field_simp; ring
  rw [e2, e3]
  have h4 : 0 ≤ (3 / 2) * r / N := by positivity
  have h5 : (∫ x, (q08e_a μ k x - q08e_m μ k) ^ 2 ∂μ) / N ≤ Qk / N := div_le_div_of_nonneg_right hl' hN0.le
  have h6 : (∫ x, w x ^ 2 ∂μ) / (4 * N) ≤ E ^ 2 / (4 * N) :=
    div_le_div_of_nonneg_right hwsq (by positivity)
  have e4 : 3 * Qk / N = 3 * (Qk / N) := by ring
  have e5 : 3 * E ^ 2 / (4 * N) = 3 * (E ^ 2 / (4 * N)) := by ring
  rw [e4, e5]
  nlinarith

/-- Second moment of a normalised sum of centred bounded variables. -/
theorem q08gl_lin_L2 (r : T → ℝ) (hrm : Measurable r) (C : ℝ) (hC : ∀ x, |r x| ≤ C)
    (hr0 : ∫ x, r x ∂μ = 0) (N : ℕ) (hN : 1 ≤ N) :
    MemLp (fun X : Fin N → T => (Real.sqrt N)⁻¹ * ∑ i, r (X i)) 2 (Measure.pi fun _ : Fin N => μ) ∧
      ∫ X : Fin N → T, ((Real.sqrt N)⁻¹ * ∑ i, r (X i)) ^ 2 ∂(Measure.pi fun _ : Fin N => μ) =
        ∫ x, r x ^ 2 ∂μ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hr2 : MemLp r 2 μ :=
    MemLp.of_bound hrm.aestronglyMeasurable C (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)
  obtain ⟨hm2, hint⟩ := q08e_lin_second μ r hrm hr2 hr0 N
  refine ⟨hm2.const_mul _, ?_⟩
  simp_rw [mul_pow]
  rw [integral_const_mul, hint, inv_pow, Real.sq_sqrt hN0.le]
  field_simp

end Approx

end HRS.Q08

end
