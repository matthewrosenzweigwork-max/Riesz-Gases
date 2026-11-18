import HRS.MS.CovMeasAux4

/-!
# S10.1 (worker S101B), part 5: the operator trick

For a smooth map `Γ : ℝ^d → H` into a Hilbert space and a bounded bilinear form `Bil` on `H` put
`F_Bil(x) = Σ_k Bil(∂_kΓ(x), ∂_kΓ(x))`.  `Bil ↦ F_Bil` is linear, `F_Bil` is a weighted test function of `E_{r,P}` with
`‖D^jF_Bil‖_∞ ≤ C_F ‖Bil‖` (`Γ ∈ C^{r+1}`, `‖D^jΓ‖ ≤ B`), hence for a bounded linear functional `η` on `E_{r,P}` (`IsBoundedLinearOnE`)
the form `D(u,v) = η(F_{u⊗v})` is a bounded symmetric bilinear form on `H` with `Σ_i |D(e_i,f_i)| ≤ dualNormE(η) · c` for orthonormal
families (the form `Σ ε_i e_i ⊗ f_i` has norm `≤ 1`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq

variable {d : ℕ}

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `∂_kΓ(x)`. -/
def s101Gk (Γ : Euc d → H) (k : Fin d) (x : Euc d) : H :=
  fderiv ℝ Γ x (EuclideanSpace.single k (1 : ℝ))

/-- `F_Bil(x) = Σ_k Bil(∂_kΓ(x), ∂_kΓ(x))`. -/
def s101Fm (Γ : Euc d → H) (Bil : H →L[ℝ] H →L[ℝ] ℝ) (x : Euc d) : ℝ :=
  ∑ k : Fin d, Bil (s101Gk Γ k x) (s101Gk Γ k x)

lemma s101_Gk_contDiff {Γ : Euc d → H} {n : ℕ} (hΓ : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Γ) (k : Fin d) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun x => s101Gk Γ k x) :=
  (hΓ.fderiv_right (m := n) (by push_cast; exact le_rfl)).clm_apply contDiff_const

lemma s101_Gk_bound {Γ : Euc d → H} {n : ℕ} (hΓ : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Γ) (k : Fin d)
    {B : ℝ} (hB : ∀ j ≤ n + 1, ∀ x, ‖iteratedFDeriv ℝ j Γ x‖ ≤ B) :
    ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i (fun x => s101Gk Γ k x) x‖ ≤ B := by
  intro i hi x
  have h1 := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fderiv ℝ Γ)
    (c := EuclideanSpace.single k (1 : ℝ)) (x := x) (N := (n : WithTop ℕ∞)) (n := i)
    ((hΓ.fderiv_right (m := n) (by push_cast; exact le_rfl)).contDiffAt) (by exact_mod_cast hi)
  rw [norm_iteratedFDeriv_fderiv] at h1
  have h2 : ‖(EuclideanSpace.single k (1 : ℝ) : Euc d)‖ = 1 := by simp
  rw [h2, one_mul] at h1
  exact h1.trans (hB (i + 1) (by omega) x)

lemma s101_Fm_contDiff {Γ : Euc d → H} {n : ℕ} (hΓ : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Γ)
    (Bil : H →L[ℝ] H →L[ℝ] ℝ) : ContDiff ℝ (n : WithTop ℕ∞) (s101Fm Γ Bil) := by
  unfold s101Fm
  refine ContDiff.sum fun k _ => ?_
  exact Bil.isBoundedBilinearMap.contDiff.comp ((s101_Gk_contDiff hΓ k).prodMk (s101_Gk_contDiff hΓ k))

/-- The bound constant. -/
def s101Cf (d n : ℕ) (B : ℝ) : ℝ := (d : ℝ) * 2 ^ n * B ^ 2

lemma s101_Fm_bound {Γ : Euc d → H} {n : ℕ} (hΓ : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Γ)
    {B : ℝ} (hB : ∀ j ≤ n + 1, ∀ x, ‖iteratedFDeriv ℝ j Γ x‖ ≤ B) (Bil : H →L[ℝ] H →L[ℝ] ℝ) :
    ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (s101Fm Γ Bil) x‖ ≤ s101Cf d n B * ‖Bil‖ := by
  intro j hj x
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) x)
  have hGk := fun k => s101_Gk_contDiff hΓ k
  have hGb := fun k => s101_Gk_bound hΓ k hB
  have hterm : ∀ k : Fin d, ‖iteratedFDeriv ℝ j (fun x => Bil (s101Gk Γ k x) (s101Gk Γ k x)) x‖ ≤
      ‖Bil‖ * (2 ^ n * B ^ 2) := by
    intro k
    have h1 := ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear Bil (hGk k) (hGk k) x
      (n := j) (by exact_mod_cast hj)
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (ContinuousLinearMap.opNorm_nonneg _)
    calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x => s101Gk Γ k x) x‖ *
          ‖iteratedFDeriv ℝ (j - i) (fun x => s101Gk Γ k x) x‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (B * B) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ j := by simpa [Nat.lt_succ_iff] using hi
          have a1 := hGb k i (hi'.trans hj) x
          have a2 := hGb k (j - i) ((Nat.sub_le _ _).trans hj) x
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact mul_le_mul a1 a2 (norm_nonneg _) hB0
      _ = 2 ^ j * (B * B) := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose j
      _ ≤ 2 ^ n * B ^ 2 := by
          rw [← sq]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) (sq_nonneg _)
  have hsum : iteratedFDeriv ℝ j (s101Fm Γ Bil) x =
      ∑ k : Fin d, iteratedFDeriv ℝ j (fun x => Bil (s101Gk Γ k x) (s101Gk Γ k x)) x := by
    unfold s101Fm
    refine iteratedFDeriv_fun_sum_apply fun k _ => ?_
    exact (Bil.isBoundedBilinearMap.contDiff.comp
      ((hGk k).prodMk (hGk k))).contDiffAt.of_le (by exact_mod_cast hj)
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k : Fin d, ‖iteratedFDeriv ℝ j (fun x => Bil (s101Gk Γ k x) (s101Gk Γ k x)) x‖
      ≤ ∑ _k : Fin d, ‖Bil‖ * (2 ^ n * B ^ 2) := Finset.sum_le_sum fun k _ => hterm k
    _ = s101Cf d n B * ‖Bil‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, s101Cf]
        ring

lemma s101_Fm_add (Γ : Euc d → H) (Bil₁ Bil₂ : H →L[ℝ] H →L[ℝ] ℝ) :
    s101Fm Γ (Bil₁ + Bil₂) = s101Fm Γ Bil₁ + s101Fm Γ Bil₂ := by
  funext x
  simp [s101Fm, Finset.sum_add_distrib]

lemma s101_Fm_smul (Γ : Euc d → H) (a : ℝ) (Bil : H →L[ℝ] H →L[ℝ] ℝ) :
    s101Fm Γ (a • Bil) = a • s101Fm Γ Bil := by
  funext x
  simp [s101Fm, Finset.mul_sum]

lemma s101_Fm_sum (Γ : Euc d → H) {ι : Type*} (s : Finset ι) (Bil : ι → H →L[ℝ] H →L[ℝ] ℝ) :
    s101Fm Γ (∑ i ∈ s, Bil i) = ∑ i ∈ s, s101Fm Γ (Bil i) := by
  classical
  induction s using Finset.induction_on with
  | empty => funext x; simp [s101Fm]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, s101_Fm_add, ih]

/-- The rank-one bilinear form `(a,b) ↦ ⟨u,a⟩⟨v,b⟩`. -/
def s101Rk (u v : H) : H →L[ℝ] H →L[ℝ] ℝ := (innerSL ℝ u).smulRight (innerSL ℝ v)

lemma s101Rk_apply (u v a b : H) : s101Rk u v a b = inner ℝ u a * inner ℝ v b := by
  simp [s101Rk]

lemma s101Rk_add_left (u u' v : H) : s101Rk (u + u') v = s101Rk u v + s101Rk u' v := by
  ext a b; simp [s101Rk_apply, inner_add_left, add_mul]

lemma s101Rk_add_right (u v v' : H) : s101Rk u (v + v') = s101Rk u v + s101Rk u v' := by
  ext a b; simp [s101Rk_apply, inner_add_left, mul_add]

lemma s101Rk_smul_left (c : ℝ) (u v : H) : s101Rk (c • u) v = c • s101Rk u v := by
  ext a b; simp [s101Rk_apply, inner_smul_left, mul_assoc]

lemma s101Rk_smul_right (c : ℝ) (u v : H) : s101Rk u (c • v) = c • s101Rk u v := by
  ext a b; simp [s101Rk_apply, inner_smul_left]; ring

lemma norm_s101Rk_le (u v : H) : ‖s101Rk u v‖ ≤ ‖u‖ * ‖v‖ := by
  unfold s101Rk
  rw [ContinuousLinearMap.norm_smulRight_apply]
  simp

lemma s101Fm_Rk_symm (Γ : Euc d → H) (u v : H) : s101Fm Γ (s101Rk u v) = s101Fm Γ (s101Rk v u) := by
  funext x
  simp only [s101Fm, s101Rk_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- A signed sum of rank-one forms along orthonormal families has norm `≤ 1`. -/
lemma norm_signed_Rk_le {n : ℕ} {e f : Fin n → H} (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f)
    (ε : Fin n → ℝ) (hε : ∀ i, |ε i| ≤ 1) : ‖∑ i, ε i • s101Rk (e i) (f i)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun b => ?_
  simp only [sum_apply, smul_apply, s101Rk_apply, smul_eq_mul,
    Real.norm_eq_abs]
  have hA := he.sum_inner_products_le (s := Finset.univ) (x := a)
  have hB := hf.sum_inner_products_le (s := Finset.univ) (x := b)
  simp only [Real.norm_eq_abs, sq_abs] at hA hB
  calc |∑ i, ε i * (inner ℝ (e i) a * inner ℝ (f i) b)|
      ≤ ∑ i, |ε i * (inner ℝ (e i) a * inner ℝ (f i) b)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |inner ℝ (e i) a| * |inner ℝ (f i) b| := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_mul]
        have := hε i
        have h0 : 0 ≤ |inner ℝ (e i) a| * |inner ℝ (f i) b| := by positivity
        nlinarith [abs_nonneg (ε i)]
    _ ≤ Real.sqrt (∑ i, |inner ℝ (e i) a| ^ 2) * Real.sqrt (∑ i, |inner ℝ (f i) b| ^ 2) := by
        have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => |inner ℝ (e i) a|)
          (fun i => |inner ℝ (f i) b|)
        exact this
    _ ≤ ‖a‖ * ‖b‖ := by
        refine mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (norm_nonneg _)
        · rw [← Real.sqrt_sq (norm_nonneg a)]
          exact Real.sqrt_le_sqrt (by simpa [sq_abs] using hA)
        · rw [← Real.sqrt_sq (norm_nonneg b)]
          exact Real.sqrt_le_sqrt (by simpa [sq_abs] using hB)
    _ = 1 * ‖a‖ * ‖b‖ := by ring

end Abstract

end HRS.MS.CovMeas
