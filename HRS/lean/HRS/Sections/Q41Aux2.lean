import Mathlib
import HRS.Sections.Q41Aux1

/-!
# Packet Q41, helper 2: unboundedness from a stationary kernel with decaying covariance

If `X : ℝ → Ω → ℝ` has Gaussian finite-dimensional laws `N(0, (ρ(|τ_a - τ_b|))_{ab})` for
nonnegative times, with `ρ(0) > 0` and `ρ(u) → 0` as `u → ∞`, then a.s. `sup_{t ≥ 0} |X_t| = ∞`
(`q41_ae_unbounded_of_kernel`).  One picks a sparse sequence of times along which the covariance
matrix is diagonally dominant and applies `NondegGauss.ae_unbounded`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Matrix

namespace HRS.Q41

/-- the geometric weights `2^{-(i+1)}` -/
def q41_q (i : ℕ) : ℝ := (1 / 2 : ℝ) ^ (i + 1)

lemma q41_q_pos (i : ℕ) : 0 < q41_q i := by unfold q41_q; positivity

lemma q41_q_le_half (i : ℕ) : q41_q i ≤ 1 / 2 := by
  unfold q41_q
  calc (1 / 2 : ℝ) ^ (i + 1) ≤ (1 / 2) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = 1 / 2 := by norm_num

lemma q41_q_anti {i j : ℕ} (h : i ≤ j) : q41_q j ≤ q41_q i := by
  unfold q41_q
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

lemma q41_sum_q_le (L : ℕ) : ∑ j : Fin L, q41_q j ≤ 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => q41_q j) L]
  have h := sum_geometric_two_le L
  unfold q41_q
  have : ∑ j ∈ Finset.range L, (1 / 2 : ℝ) ^ (j + 1) = (1 / 2) * ∑ j ∈ Finset.range L, (1 / 2 : ℝ) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this]
  linarith

/-- Diagonal dominance: a symmetric matrix with diagonal `ρ₀` and off-diagonal entries
`≤ ρ₀ q_i q_j` has quadratic form `≥ (ρ₀/2) |w|²`. -/
lemma q41_quad_lower {L : ℕ} {ρ0 : ℝ} (hρ0 : 0 < ρ0) (Γ : Matrix (Fin L) (Fin L) ℝ)
    (hdiag : ∀ i, Γ i i = ρ0)
    (hoff : ∀ i j, i ≠ j → |Γ i j| ≤ ρ0 * (q41_q i * q41_q j)) (w : Fin L → ℝ) :
    ρ0 / 2 * ∑ i, w i ^ 2 ≤ ∑ i, ∑ j, w i * Γ i j * w j := by
  have hterm : ∀ i j : Fin L, (if i = j then ρ0 * w i ^ 2 else 0) - ρ0 * (q41_q i * q41_q j) * (|w i| * |w j|)
      ≤ w i * Γ i j * w j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [if_true, hdiag]
      have : 0 ≤ ρ0 * (q41_q i * q41_q i) * (|w i| * |w i|) := by
        have := q41_q_pos i; positivity
      nlinarith [abs_mul_abs_self (w i)]
    · simp only [hij, if_false, zero_sub]
      have h1 := hoff i j hij
      have h2 : |w i * Γ i j * w j| ≤ ρ0 * (q41_q i * q41_q j) * (|w i| * |w j|) := by
        rw [abs_mul, abs_mul]
        calc |w i| * |Γ i j| * |w j| = |Γ i j| * (|w i| * |w j|) := by ring
          _ ≤ ρ0 * (q41_q i * q41_q j) * (|w i| * |w j|) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
      linarith [neg_abs_le (w i * Γ i j * w j)]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm i j
  have hdiagsum : ∑ i : Fin L, ∑ j : Fin L, (if i = j then ρ0 * w i ^ 2 else 0) = ρ0 * ∑ i, w i ^ 2 := by
    simp [Finset.mul_sum]
  -- bound of the error term
  have herr : ∑ i : Fin L, ∑ j : Fin L, ρ0 * (q41_q i * q41_q j) * (|w i| * |w j|) ≤
      ρ0 / 2 * ∑ i, w i ^ 2 := by
    have h1 : ∀ i j : Fin L, ρ0 * (q41_q i * q41_q j) * (|w i| * |w j|) ≤
        ρ0 * (q41_q i * q41_q j) * ((w i ^ 2 + w j ^ 2) / 2) := by
      intro i j
      have : 0 ≤ ρ0 * (q41_q i * q41_q j) := by
        have := q41_q_pos i; have := q41_q_pos j; positivity
      refine mul_le_mul_of_nonneg_left ?_ this
      nlinarith [sq_nonneg (|w i| - |w j|), sq_abs (w i), sq_abs (w j)]
    refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j).trans ?_
    have h2 : ∑ i : Fin L, ∑ j : Fin L, ρ0 * (q41_q i * q41_q j) * ((w i ^ 2 + w j ^ 2) / 2) =
        ∑ i : Fin L, ∑ j : Fin L, ρ0 * (q41_q i * q41_q j) * w i ^ 2 := by
      have h3 : ∑ i : Fin L, ∑ j : Fin L, ρ0 * (q41_q i * q41_q j) * ((w i ^ 2 + w j ^ 2) / 2) =
          (∑ i : Fin L, ∑ j : Fin L, ρ0 * (q41_q i * q41_q j) * w i ^ 2) / 2 +
          (∑ i : Fin L, ∑ j : Fin L, ρ0 * (q41_q i * q41_q j) * w j ^ 2) / 2 := by
        have hh : ∀ i j : Fin L, ρ0 * (q41_q i * q41_q j) * ((w i ^ 2 + w j ^ 2) / 2) =
            ρ0 * (q41_q i * q41_q j) * w i ^ 2 / 2 + ρ0 * (q41_q i * q41_q j) * w j ^ 2 / 2 := by
          intro i j; ring
        simp only [hh, Finset.sum_add_distrib, Finset.sum_div]
      have h4 : ∑ i : Fin L, ∑ j : Fin L, ρ0 * (q41_q i * q41_q j) * w j ^ 2 =
          ∑ i : Fin L, ∑ j : Fin L, ρ0 * (q41_q i * q41_q j) * w i ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [h3, h4]; ring
    rw [h2]
    have h5 : ∀ i : Fin L, ∑ j : Fin L, ρ0 * (q41_q i * q41_q j) * w i ^ 2 ≤
        ρ0 * (q41_q i * w i ^ 2) := by
      intro i
      have : ∑ j : Fin L, ρ0 * (q41_q i * q41_q j) * w i ^ 2 =
          ρ0 * (q41_q i * w i ^ 2) * ∑ j : Fin L, q41_q j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [this]
      have h6 : 0 ≤ ρ0 * (q41_q i * w i ^ 2) := by
        have := q41_q_pos i; positivity
      calc ρ0 * (q41_q i * w i ^ 2) * ∑ j : Fin L, q41_q j ≤ ρ0 * (q41_q i * w i ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left (q41_sum_q_le L) h6
        _ = _ := by ring
    refine (Finset.sum_le_sum fun i _ => h5 i).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := q41_q_le_half i
    have := sq_nonneg (w i)
    nlinarith [mul_nonneg hρ0.le (sq_nonneg (w i))]
  have hsub : ∑ i : Fin L, ∑ j : Fin L, ((if i = j then ρ0 * w i ^ 2 else 0) -
      ρ0 * (q41_q i * q41_q j) * (|w i| * |w j|)) =
      ρ0 * ∑ i, w i ^ 2 - ∑ i : Fin L, ∑ j : Fin L, ρ0 * (q41_q i * q41_q j) * (|w i| * |w j|) := by
    rw [← hdiagsum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
  rw [hsub] at hsum
  linarith

/-- A sparse sequence of nonnegative times along which `ρ` is tiny. -/
lemma q41_exists_times {ρ : ℝ → ℝ} {ρ0 : ℝ} (hρ0 : 0 < ρ0) (hdec : Tendsto ρ atTop (𝓝 0)) :
    ∃ t : ℕ → ℝ, Monotone t ∧ (∀ n, 0 ≤ t n) ∧
      ∀ i j : ℕ, i < j → |ρ (t j - t i)| ≤ ρ0 * (q41_q i * q41_q j) := by
  have hT : ∀ n : ℕ, ∃ T : ℝ, ∀ u, T ≤ u → |ρ u| ≤ ρ0 * (q41_q n * q41_q n) := by
    intro n
    have hε : 0 < ρ0 * (q41_q n * q41_q n) := by have := q41_q_pos n; positivity
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hdec) _ hε
    exact ⟨N, fun u hu => by simpa [Real.dist_eq] using (hN u hu).le⟩
  choose T hT using hT
  let t : ℕ → ℝ := fun n => Nat.rec 0 (fun k tk => tk + max (T (k + 1)) 0 + 1) n
  have ht_succ : ∀ n, t (n + 1) = t n + max (T (n + 1)) 0 + 1 := fun n => rfl
  have ht0 : t 0 = 0 := rfl
  have hmono : Monotone t := monotone_nat_of_le_succ fun n => by
    rw [ht_succ]; have := le_max_right (T (n + 1)) 0; linarith
  refine ⟨t, hmono, fun n => ?_, fun i j hij => ?_⟩
  · rw [← ht0]; exact hmono (Nat.zero_le n)
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have h1 : t i ≤ t j' := hmono (by omega)
    have h2 : T (j' + 1) ≤ t (j' + 1) - t i := by
      rw [ht_succ]
      have := le_max_left (T (j' + 1)) 0
      linarith
    refine (hT (j' + 1) _ h2).trans ?_
    have := q41_q_anti (show i ≤ j' + 1 by omega)
    have hq := q41_q_pos (j' + 1)
    have hqi := q41_q_pos i
    refine mul_le_mul_of_nonneg_left ?_ hρ0.le
    nlinarith

lemma q41_measurable_toLp {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (f : Fin p → Ω → ℝ)
    (hf : ∀ a, Measurable (f a)) :
    Measurable (fun ω => (WithLp.toLp 2 (fun a => f a ω) : EuclideanSpace ℝ (Fin p))) := by
  have h1 : Measurable (fun ω a => f a ω) := measurable_pi_iff.2 hf
  exact (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp h1

/-- Almost sure unboundedness for a Gaussian family with stationary decaying kernel. -/
theorem q41_ae_unbounded_of_kernel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ → Ω → ℝ) (hX : ∀ t, Measurable (X t)) (ρ : ℝ → ℝ)
    (hρ0 : 0 < ρ 0) (hdec : Tendsto ρ atTop (𝓝 0))
    (hlaw : ∀ (p : ℕ) (τ : Fin p → ℝ), (∀ a, 0 ≤ τ a) →
      P.map (fun ω => (WithLp.toLp 2 (fun a => X (τ a) ω) : EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun a b => ρ |τ a - τ b|)) :
    ∀ᵐ ω ∂P, ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ M < |X t ω| := by
  obtain ⟨t, htm, ht0, htb⟩ := q41_exists_times hρ0 hdec
  set W : ℕ → Ω → ℝ := fun n ω => X (t n) ω with hW
  let Γ : ∀ L : ℕ, Matrix (Fin L) (Fin L) ℝ := fun L => Matrix.of fun a b => ρ |t a - t b|
  let V : ∀ L : ℕ, Ω → EuclideanSpace ℝ (Fin L) :=
    fun L ω => (WithLp.toLp 2 (fun a : Fin L => X (t a) ω) : EuclideanSpace ℝ (Fin L))
  have hVm : ∀ L, Measurable (V L) := fun L => q41_measurable_toLp (fun a : Fin L => fun ω => X (t a) ω)
    (fun a => hX _)
  have hlawL : ∀ L, P.map (V L) = multivariateGaussian 0 (Γ L) := fun L =>
    hlaw L (fun a => t a) (fun a => ht0 a)
  -- diagonal dominance of `Γ L`
  have hdiag : ∀ L (i : Fin L), Γ L i i = ρ 0 := by intro L i; simp [Γ]
  have hoff : ∀ L (i j : Fin L), i ≠ j → |Γ L i j| ≤ ρ 0 * (q41_q i * q41_q j) := by
    intro L i j hij
    simp only [Γ, Matrix.of_apply]
    rcases lt_or_gt_of_ne (show (i : ℕ) ≠ j from fun h => hij (Fin.ext h)) with h | h
    · have := htb i j h
      have e : |t i - t j| = t j - t i := by
        rw [abs_sub_comm]; exact abs_of_nonneg (by linarith [htm h.le])
      rw [e]; exact this
    · have := htb j i h
      have e : |t i - t j| = t i - t j := abs_of_nonneg (by linarith [htm h.le])
      rw [e, mul_comm (q41_q i)]; exact this
  have hΓsymm : ∀ L, (Γ L).IsHermitian := by
    intro L
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp [Γ, abs_sub_comm]
  have hΓquad : ∀ L (w : Fin L → ℝ), ρ 0 / 2 * ∑ i, w i ^ 2 ≤ ∑ i, ∑ j, w i * Γ L i j * w j :=
    fun L w => q41_quad_lower hρ0 (Γ L) (hdiag L) (hoff L) w
  have hΓpsd : ∀ L, (Γ L).PosSemidef := by
    intro L
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hΓsymm L) fun x => ?_
    have h1 := hΓquad L x
    have h2 : 0 ≤ ρ 0 / 2 * ∑ i, x i ^ 2 := by positivity
    have h3 : star x ⬝ᵥ (Γ L *ᵥ x) = ∑ i, ∑ j, x i * Γ L i j * x j := by
      simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h3]; linarith
  have hHG : ∀ L, HasGaussianLaw (V L) P := fun L =>
    ⟨(hVm L).aemeasurable, by rw [hlawL L]; infer_instance⟩
  have hgauss : IsGaussianProcess W P := by
    refine ⟨fun I => ?_⟩
    classical
    set L : ℕ := I.sup id + 1 with hL
    have hlt : ∀ i : I, (i : ℕ) < L := fun i => by
      have : (i : ℕ) ≤ I.sup id := Finset.le_sup (f := id) i.2
      omega
    let K0 : EuclideanSpace ℝ (Fin L) →ₗ[ℝ] (I → ℝ) :=
      { toFun := fun x i => x ⟨i.1, hlt i⟩
        map_add' := fun x y => by ext; simp
        map_smul' := fun c x => by ext; simp }
    let K : EuclideanSpace ℝ (Fin L) →L[ℝ] (I → ℝ) := LinearMap.toContinuousLinearMap K0
    have : (fun ω => I.restrict (fun n => W n ω)) = K ∘ V L := by
      funext ω i
      simp [K, K0, V, W, Finset.restrict_def]
    rw [this]
    exact (hHG L).map K
  have hmeas : ∀ i, Measurable (W i) := fun i => hX _
  have hcov : ∀ L (i j : Fin L), cov[W i, W j; P] = Γ L i j := by
    intro L i j
    have h1 : cov[W i, W j; P] = cov[fun x : EuclideanSpace ℝ (Fin L) => x i,
        fun x : EuclideanSpace ℝ (Fin L) => x j; P.map (V L)] := by
      rw [covariance_map]
      · rfl
      · exact (continuous_apply i |>.comp (PiLp.continuous_ofLp 2 _)).aestronglyMeasurable
      · exact (continuous_apply j |>.comp (PiLp.continuous_ofLp 2 _)).aestronglyMeasurable
      · exact (hVm L).aemeasurable
    rw [h1, hlawL L]
    exact covariance_eval_multivariateGaussian (hΓpsd L) i j
  have hcent : ∀ i, ∫ ω, W i ω ∂P = 0 := by
    intro i
    have h1 : ∫ ω, W i ω ∂P = ∫ x, x ⟨i, Nat.lt_succ_self i⟩ ∂(P.map (V (i + 1))) := by
      exact (integral_map (μ := P) (φ := V (i + 1)) (hVm (i + 1)).aemeasurable
        (f := fun x : EuclideanSpace ℝ (Fin (i + 1)) => x.ofLp ⟨i, Nat.lt_succ_self i⟩)
        (continuous_apply _ |>.comp (PiLp.continuous_ofLp 2 _)).aestronglyMeasurable).symm
    rw [h1, hlawL]
    have hint : Integrable (id : EuclideanSpace ℝ (Fin (i + 1)) → _) (multivariateGaussian 0 (Γ (i + 1))) :=
      IsGaussian.integrable_id
    have := (EuclideanSpace.proj (𝕜 := ℝ) (⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1))).integral_comp_comm hint
    simpa using this
  have hnd : NondegGauss W P (ρ 0 / 2) :=
    { gauss := hgauss
      meas := hmeas
      centered := hcent
      var := fun L w => by
        rw [q41_var_eq_quad hgauss hmeas L w]
        have := hΓquad L w
        refine this.trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hcov L i j]; ring }
  filter_upwards [hnd.ae_unbounded (by positivity)] with ω hω M
  obtain ⟨n, hn⟩ := hω M
  exact ⟨t n, ht0 n, hn⟩

end HRS.Q41
