import Mathlib

/-!
# Packet Q41, helper 5: a centred Gaussian sequence with a prescribed positive semidefinite kernel

For `K : ℕ → ℕ → ℝ` symmetric with all finite blocks positive semidefinite there is a centred
Gaussian process `X : ℕ → (ℕ → ℝ) → ℝ` on `(ℕ → ℝ, ⊗ N(0,1))` with `cov[X_i, X_j] = K i j`
(`q41_exists_gaussian_process`).  Construction: `X_n = ∑_{i<n} a_{n,i} X_i + σ_n ω_n`, where
`a_n` solves the (always solvable, by positive semidefiniteness) regression equation
`∑_i a_{n,i} K_{ij} = K_{nj}` and `σ_n² = K_{nn} - ∑_i a_{n,i} K_{ni}`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Matrix

namespace HRS.Q41

/-- The regression equation is solvable for a positive semidefinite kernel. -/
lemma q41_range_solvable (n : ℕ) (K : ℕ → ℕ → ℝ) (hsymm : ∀ i j, K i j = K j i)
    (hK : ∀ c : Fin (n + 1) → ℝ, 0 ≤ ∑ i, ∑ j, c i * c j * K i j) :
    ∃ a : Fin n → ℝ, ∀ j : Fin n, ∑ i : Fin n, a i * K i j = K n j := by
  classical
  set G : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun (i j : Fin n) => K i j with hG
  have hGs : G.IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp [hG, hsymm]
  set T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := Matrix.toEuclideanLin G with hT
  have hTs : T.IsSymmetric := Matrix.isHermitian_iff_isSymmetric.1 hGs
  have hTapp : ∀ (y : EuclideanSpace ℝ (Fin n)) (i : Fin n), T y i = ∑ j : Fin n, K i j * y j := by
    intro y i
    simp [hT, hG, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]
  set c : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun j : Fin n => K n j) with hc
  -- `c` is orthogonal to `ker T`
  have hperp : c ∈ (LinearMap.ker T)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have hGy : ∀ i : Fin n, ∑ j : Fin n, K i j * y j = 0 := by
      intro i
      rw [← hTapp y i, hy]; rfl
    have hKnn : 0 ≤ K n n := by
      have := hK (Pi.single (Fin.last n) 1)
      have e : ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (Pi.single (Fin.last n) (1 : ℝ) : Fin (n + 1) → ℝ) i *
          (Pi.single (Fin.last n) (1 : ℝ) : Fin (n + 1) → ℝ) j * K i j = K n n := by
        simp [Pi.single_apply, mul_ite, Finset.sum_ite_eq']
      rw [e] at this
      exact this
    have hqf : ∀ t : ℝ, 0 ≤ K n n - 2 * t * ∑ j : Fin n, K n j * y j := by
      intro t
      have := hK (Fin.snoc (α := fun _ => ℝ) (fun j => t * y j) (-1))
      simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last,
        Fin.val_castSucc, Finset.sum_add_distrib] at this
      have e1 : ∑ i : Fin n, ∑ j : Fin n, t * y i * (t * y j) * K i j = 0 := by
        have : ∀ i : Fin n, ∑ j : Fin n, t * y i * (t * y j) * K i j =
            t ^ 2 * y i * ∑ j : Fin n, K i j * y j := by
          intro i
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        simp_rw [this, hGy]
        simp
      have e2 : ∑ i : Fin n, t * y i * (-1) * K i n = -t * ∑ j : Fin n, K n j * y j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsymm i n]
        ring
      have e3 : ∑ j : Fin n, (-1) * (t * y j) * K n j = -t * ∑ j : Fin n, K n j * y j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e1, e2, e3] at this
      nlinarith
    have hy0 : ∑ j : Fin n, K n j * y j = 0 := by
      set s := ∑ j : Fin n, K n j * y j with hs
      by_contra hne
      have h1 := hqf ((K n n + 1) / (2 * s))
      have h2 : 2 * ((K n n + 1) / (2 * s)) * s = K n n + 1 := by field_simp
      rw [h2] at h1
      linarith
    simpa [hc, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using hy0
  have hmem : c ∈ LinearMap.range T := by
    have : (LinearMap.range T)ᗮ = LinearMap.ker T := hTs.orthogonal_range
    rw [← this, Submodule.orthogonal_orthogonal] at hperp
    exact hperp
  obtain ⟨a, ha⟩ := hmem
  refine ⟨fun i => a i, fun j => ?_⟩
  have := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v j) ha
  simp only [hTapp, hc] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsymm i j]
  ring

/-- Regression data for the sequential Gaussian construction. -/
structure GPData (K : ℕ → ℕ → ℝ) where
  a : ∀ n : ℕ, Fin n → ℝ
  σ : ℕ → ℝ
  reg : ∀ n (j : Fin n), ∑ i : Fin n, a n i * K i j = K n j
  var : ∀ n, K n n = ∑ i : Fin n, ∑ j : Fin n, a n i * a n j * K i j + σ n ^ 2

lemma q41_exists_gpData (K : ℕ → ℕ → ℝ) (hsymm : ∀ i j, K i j = K j i)
    (hK : ∀ n (c : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, c i * c j * K i j) : Nonempty (GPData K) := by
  classical
  have hex : ∀ n : ℕ, ∃ a : Fin n → ℝ, (∀ j : Fin n, ∑ i : Fin n, a i * K i j = K n j) ∧
      0 ≤ K n n - ∑ i : Fin n, a i * K n i := by
    intro n
    obtain ⟨a, ha⟩ := q41_range_solvable n K hsymm (hK (n + 1))
    refine ⟨a, ha, ?_⟩
    have h1 := hK (n + 1) (Fin.snoc (α := fun _ => ℝ) (fun i => -a i) 1)
    simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last,
      Fin.val_castSucc, Finset.sum_add_distrib] at h1
    have e1 : ∑ i : Fin n, ∑ j : Fin n, -a i * -a j * K i j = ∑ i : Fin n, a i * K n i := by
      have : ∀ j : Fin n, ∑ i : Fin n, -a i * -a j * K i j = a j * K n j := by
        intro j
        have := ha j
        calc ∑ i : Fin n, -a i * -a j * K i j = a j * ∑ i : Fin n, a i * K i j := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
          _ = a j * K n j := by rw [this]
      rw [Finset.sum_comm]
      simp_rw [this]
    have e2 : ∑ i : Fin n, -a i * 1 * K i n = -∑ i : Fin n, a i * K n i := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hsymm i n]; ring
    have e3 : ∑ j : Fin n, 1 * -a j * K n j = -∑ i : Fin n, a i * K n i := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e1, e2, e3] at h1
    linarith
  choose a ha hpos using hex
  refine ⟨⟨a, fun n => Real.sqrt (K n n - ∑ i : Fin n, a n i * K n i), ha, fun n => ?_⟩⟩
  rw [Real.sq_sqrt (hpos n)]
  have : ∑ i : Fin n, ∑ j : Fin n, a n i * a n j * K i j = ∑ i : Fin n, a n i * K n i := by
    have h2 : ∀ j : Fin n, ∑ i : Fin n, a n i * a n j * K i j = a n j * K n j := by
      intro j
      calc ∑ i : Fin n, a n i * a n j * K i j = a n j * ∑ i : Fin n, a n i * K i j := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
        _ = a n j * K n j := by rw [ha n j]
    rw [Finset.sum_comm]
    simp_rw [h2]
  rw [this]; ring

section Construction

variable {K : ℕ → ℕ → ℝ}

/-- coefficient of `ω_j` in `X_n` -/
def gpL (D : GPData K) (n j : ℕ) : ℝ :=
  (∑ i : Fin n, D.a n i * gpL D i j) + if j = n then D.σ n else 0
termination_by n
decreasing_by exact i.2

lemma gpL_unfold (D : GPData K) (n j : ℕ) :
    gpL D n j = (∑ i : Fin n, D.a n i * gpL D i j) + if j = n then D.σ n else 0 := by
  rw [gpL]

lemma gpL_eq_zero (D : GPData K) : ∀ n j : ℕ, n < j → gpL D n j = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro j hj
    rw [gpL_unfold]
    have h1 : ∀ i : Fin n, gpL D i j = 0 := fun i => ih i i.2 j (lt_trans i.2 hj)
    simp [h1, show j ≠ n by omega]

/-- finite inner product of coefficient rows -/
def gpIp (D : GPData K) (M n m : ℕ) : ℝ := ∑ j ∈ Finset.range M, gpL D n j * gpL D m j

lemma gpIp_comm (D : GPData K) (M n m : ℕ) : gpIp D M n m = gpIp D M m n := by
  unfold gpIp
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

lemma gpIp_gram (hsymm : ∀ i j, K i j = K j i) (D : GPData K) :
    ∀ n m : ℕ, m ≤ n → ∀ M : ℕ, n + 1 ≤ M → gpIp D M n m = K n m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m hmn M hM
    have hexp : ∀ r : ℕ, gpIp D M n r = ∑ i : Fin n, D.a n i * gpIp D M i r +
        D.σ n * gpL D r n := by
      intro r
      unfold gpIp
      simp_rw [gpL_unfold D n]
      simp only [add_mul, Finset.sum_add_distrib]
      congr 1
      · simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      · rw [Finset.sum_eq_single n]
        · simp
        · intro j _ hj; simp [hj]
        · intro hn; exfalso; exact hn (Finset.mem_range.2 (by omega))
    have hK' : ∀ i r : ℕ, i < n → r < n → gpIp D M i r = K i r := by
      intro i r hi hr
      rcases le_total r i with h | h
      · exact ih i hi r h M (by omega)
      · rw [gpIp_comm, hsymm]; exact ih r hr i h M (by omega)
    have hlt : ∀ m : ℕ, m < n → gpIp D M n m = K n m := by
      intro m hlt
      rw [hexp m, gpL_eq_zero D m n hlt]
      have : ∀ i : Fin n, D.a n i * gpIp D M i m = D.a n i * K i m := fun i => by
        rw [hK' i m i.2 hlt]
      simp_rw [this]
      simp only [mul_zero, add_zero]
      exact D.reg n ⟨m, hlt⟩
    rcases lt_or_eq_of_le hmn with hm | heq
    · exact hlt m hm
    · subst heq
      rw [hexp m]
      have h3 : gpL D m m = D.σ m := by
        rw [gpL_unfold]
        have : ∀ i : Fin m, gpL D i m = 0 := fun i => gpL_eq_zero D i m i.2
        simp [this]
      have h5 : ∀ i : Fin m, gpIp D M i m = K m i := fun i => by
        rw [gpIp_comm]; exact hlt i i.2
      simp_rw [h5]
      rw [h3]
      have h6 : ∑ i : Fin m, ∑ j : Fin m, D.a m i * D.a m j * K i j = ∑ i : Fin m, D.a m i * K m i := by
        have h2 : ∀ j : Fin m, ∑ i : Fin m, D.a m i * D.a m j * K i j = D.a m j * K m j := by
          intro j
          calc ∑ i : Fin m, D.a m i * D.a m j * K i j = D.a m j * ∑ i : Fin m, D.a m i * K i j := by
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
            _ = D.a m j * K m j := by rw [D.reg m j]
        rw [Finset.sum_comm]
        simp_rw [h2]
      have := D.var m
      rw [h6] at this
      linarith

/-- the process `X_n = ∑_{j ≤ n} L_{nj} ω_j` -/
def gpX (D : GPData K) (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), gpL D n j * ω j

lemma gpX_eq (D : GPData K) (n M : ℕ) (hM : n + 1 ≤ M) (ω : ℕ → ℝ) :
    gpX D n ω = ∑ j ∈ Finset.range M, gpL D n j * ω j := by
  unfold gpX
  refine Finset.sum_subset (Finset.range_mono hM) fun j hj hj' => ?_
  have : n < j := by
    simp only [Finset.mem_range] at hj hj'
    omega
  rw [gpL_eq_zero D n j this, zero_mul]

/-- The standard Gaussian product measure. -/
abbrev gpP : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => gaussianReal 0 1

lemma gp_coord_gauss (i : ℕ) : HasGaussianLaw (fun ω : ℕ → ℝ => ω i) gpP := by
  refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
  rw [show (fun ω : ℕ → ℝ => ω i) = (fun ω => ω i) from rfl, Measure.infinitePi_map_eval]
  infer_instance

lemma gp_coord_indep : iIndepFun (fun (i : ℕ) (ω : ℕ → ℝ) => ω i) gpP :=
  iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1) (X := fun _ x => x) (fun _ => measurable_id)

lemma gp_coord_process : IsGaussianProcess (fun (i : ℕ) (ω : ℕ → ℝ) => ω i) gpP := by
  refine ⟨fun I => ?_⟩
  have h1 : iIndepFun (fun (i : I) (ω : ℕ → ℝ) => ω i) gpP :=
    gp_coord_indep.precomp (g := fun i : I => (i : ℕ)) Subtype.val_injective
  exact iIndepFun.hasGaussianLaw (fun i => gp_coord_gauss i) h1

lemma gp_coord_cov (i j : ℕ) :
    cov[fun ω : ℕ → ℝ => ω i, fun ω : ℕ → ℝ => ω j; gpP] = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, covariance_self (measurable_pi_apply i).aemeasurable]
    have h1 : variance (fun x : ℝ => x) (gpP.map (fun ω : ℕ → ℝ => ω i)) =
        variance (fun ω : ℕ → ℝ => ω i) gpP := by
      have hm : AEMeasurable (fun ω : ℕ → ℝ => ω i) gpP := (measurable_pi_apply i).aemeasurable
      have := variance_map (μ := gpP) (X := fun x : ℝ => x) (Y := fun ω : ℕ → ℝ => ω i)
        aemeasurable_id' hm
      rw [this]
      rfl
    rw [← h1, Measure.infinitePi_map_eval]
    simpa using variance_fun_id_gaussianReal (μ := 0) (v := 1)
  · rw [if_neg hij]
    exact (gp_coord_indep.indepFun hij).covariance_eq_zero (gp_coord_gauss i).memLp_two
      (gp_coord_gauss j).memLp_two

lemma gpX_meas (D : GPData K) (n : ℕ) : Measurable (gpX D n) := by
  unfold gpX
  exact Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).const_mul _

lemma gpX_process (D : GPData K) : IsGaussianProcess (gpX D) gpP := by
  refine IsGaussianProcess.of_isGaussianProcess gp_coord_process fun n => ?_
  classical
  let I : Finset ℕ := Finset.range (n + 1)
  let L0 : (I → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ j : I, gpL D n j * x j
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring }
  refine ⟨I, LinearMap.toContinuousLinearMap L0, fun ω => ?_⟩
  simp only [LinearMap.coe_toContinuousLinearMap', L0, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.restrict_def]
  unfold gpX
  rw [← Finset.sum_coe_sort I (fun j => gpL D n j * ω j)]
  rfl

lemma gpX_mean (D : GPData K) (n : ℕ) : ∫ ω, gpX D n ω ∂gpP = 0 := by
  unfold gpX
  rw [integral_finset_sum]
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul]
    have : ∫ ω : ℕ → ℝ, ω j ∂gpP = 0 := by
      have h := (gp_coord_gauss j).map_eq_gaussianReal
      have h2 : ∫ x, x ∂(gpP.map (fun ω : ℕ → ℝ => ω j)) = ∫ ω : ℕ → ℝ, ω j ∂gpP :=
        integral_map (measurable_pi_apply j).aemeasurable aestronglyMeasurable_id
      rw [← h2, Measure.infinitePi_map_eval]
      simp
    rw [this, mul_zero]
  · intro j _
    exact ((gp_coord_gauss j).memLp_two.integrable (by norm_num)).const_mul _

lemma gpX_cov (hsymm : ∀ i j, K i j = K j i) (D : GPData K) (n m : ℕ) :
    cov[gpX D n, gpX D m; gpP] = K n m := by
  have key : ∀ n m : ℕ, m ≤ n → cov[gpX D n, gpX D m; gpP] = K n m := by
    intro n m hmn
    set M := n + 1
    rw [funext (gpX_eq D n M le_rfl), funext (gpX_eq D m M (by omega))]
    have hmem : ∀ j : ℕ, MemLp (fun ω : ℕ → ℝ => ω j) 2 gpP := fun j => (gp_coord_gauss j).memLp_two
    have h1 : ∀ j ∈ Finset.range M, MemLp (fun ω : ℕ → ℝ => gpL D n j * ω j) 2 gpP :=
      fun j _ => (hmem j).const_mul _
    have h2 : ∀ j ∈ Finset.range M, MemLp (fun ω : ℕ → ℝ => gpL D m j * ω j) 2 gpP :=
      fun j _ => (hmem j).const_mul _
    rw [covariance_fun_sum_fun_sum' h1 h2]
    have : ∀ j l : ℕ, cov[fun ω : ℕ → ℝ => gpL D n j * ω j, fun ω : ℕ → ℝ => gpL D m l * ω l; gpP] =
        gpL D n j * gpL D m l * (if j = l then 1 else 0) := by
      intro j l
      rw [covariance_const_mul_left, covariance_const_mul_right, gp_coord_cov]; ring
    simp_rw [this]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
    rw [← gpIp_gram hsymm D n m hmn M le_rfl]
    unfold gpIp
    refine Finset.sum_congr rfl fun j hj => ?_
    simp [Finset.mem_range.1 hj]
  rcases le_total m n with h | h
  · exact key n m h
  · rw [covariance_comm, key m n h, hsymm]

end Construction

/-- A centred Gaussian process with a prescribed positive semidefinite kernel on `ℕ`. -/
theorem q41_exists_gaussian_process (K : ℕ → ℕ → ℝ) (hsymm : ∀ i j, K i j = K j i)
    (hK : ∀ n (c : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, c i * c j * K i j) :
    ∃ X : ℕ → (ℕ → ℝ) → ℝ, (∀ n, Measurable (X n)) ∧
      IsGaussianProcess X (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) ∧
      (∀ n, ∫ ω, X n ω ∂(Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) = 0) ∧
      ∀ n m, cov[X n, X m; Measure.infinitePi fun _ : ℕ => gaussianReal 0 1] = K n m := by
  obtain ⟨D⟩ := q41_exists_gpData K hsymm hK
  exact ⟨gpX D, gpX_meas D, gpX_process D, gpX_mean D, gpX_cov hsymm D⟩

end HRS.Q41
