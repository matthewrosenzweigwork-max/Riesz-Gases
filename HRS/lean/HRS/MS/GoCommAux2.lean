import HRS.Whole.Hermite
import HRS.Whole.Oscillator
import HRS.MP.RdInit
import HRS.MS.GoCommAux1

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Go
open HRS HRS.Whole

variable {d : ℕ}

/-! ### One-dimensional ladder relations -/

lemma s55_hc_pos (n : ℕ) : 0 < hermiteConst n := by
  unfold hermiteConst
  have : 0 < (n.factorial : ℝ) * Real.sqrt Real.pi :=
    mul_pos (by exact_mod_cast n.factorial_pos) (Real.sqrt_pos.2 Real.pi_pos)
  exact inv_pos.2 (Real.sqrt_pos.2 this)

lemma s55_hc_succ (n : ℕ) : hermiteConst (n + 1) * Real.sqrt ((n : ℝ) + 1) = hermiteConst n := by
  unfold hermiteConst
  rw [Nat.factorial_succ]
  push_cast
  have h1 : 0 < (n.factorial : ℝ) * Real.sqrt Real.pi :=
    mul_pos (by exact_mod_cast n.factorial_pos) (Real.sqrt_pos.2 Real.pi_pos)
  have h2 : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  rw [mul_assoc, Real.sqrt_mul (by positivity)]
  have h3 : 0 < Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) := Real.sqrt_pos.2 h1
  field_simp


lemma s55_hP0 (y : ℝ) : hermitePoly 0 y = 1 := by simp [hermitePoly]

lemma s55_dhP0 (y : ℝ) : deriv (hermitePoly 0) y = 0 := by
  rw [deriv_hermitePoly]; simp

lemma s55_ladder_x_succ (n : ℕ) (x : ℝ) :
    x * hermiteFun (n + 1) x = Real.sqrt (((n : ℝ) + 1) / 2) * hermiteFun n x +
      Real.sqrt (((n : ℝ) + 2) / 2) * hermiteFun (n + 2) x := by
  have hP : hermitePoly (n + 2) (Real.sqrt 2 * x) = Real.sqrt 2 * x * hermitePoly (n + 1) (Real.sqrt 2 * x)
      - ((n : ℝ) + 1) * hermitePoly n (Real.sqrt 2 * x) := by
    rw [hermitePoly_succ (n + 1), deriv_hermitePoly_succ n]
  have hc1 := s55_hc_succ n
  have hc2 := s55_hc_succ (n + 1)
  have hq : Real.sqrt (((n + 1 : ℕ) : ℝ) + 1) = Real.sqrt ((n : ℝ) + 2) := by
    congr 1; push_cast; ring
  rw [hq] at hc2
  simp only [hermiteFun_eq]
  rw [hP]
  have hp0 : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hq0 : 0 < Real.sqrt ((n : ℝ) + 2) := Real.sqrt_pos.2 (by positivity)
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hpp : Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) = (n : ℝ) + 1 :=
    Real.mul_self_sqrt (by positivity)
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [Real.sqrt_div (by positivity), Real.sqrt_div (by positivity)]
  have ha : hermiteConst n = hermiteConst (n + 1) * Real.sqrt ((n : ℝ) + 1) := hc1.symm
  have he : hermiteConst (n + 2) = hermiteConst (n + 1) / Real.sqrt ((n : ℝ) + 2) := by
    rw [eq_div_iff hq0.ne']; exact hc2
  rw [ha, he]
  field_simp
  rw [Real.sq_sqrt (by positivity)]
  ring


lemma s55_ladder_x_zero (x : ℝ) :
    x * hermiteFun 0 x = Real.sqrt (1 / 2) * hermiteFun 1 x := by
  have hc : hermiteConst 1 = hermiteConst 0 := by
    have := s55_hc_succ 0
    simpa using this
  have h1 : hermitePoly 1 (Real.sqrt 2 * x) = Real.sqrt 2 * x := by
    rw [hermitePoly_succ 0, s55_hP0, s55_dhP0]; ring
  simp only [hermiteFun_eq]
  rw [hc, h1, s55_hP0]
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [Real.sqrt_div (by norm_num), Real.sqrt_one]
  field_simp

lemma s55_ladder_x (n : ℕ) (x : ℝ) :
    x * hermiteFun n x = Real.sqrt ((n : ℝ) / 2) * hermiteFun (n - 1) x +
      Real.sqrt (((n : ℝ) + 1) / 2) * hermiteFun (n + 1) x := by
  cases n with
  | zero => simpa using s55_ladder_x_zero x
  | succ m =>
    have := s55_ladder_x_succ m x
    have e1 : (((m + 1 : ℕ) : ℝ)) / 2 = ((m : ℝ) + 1) / 2 := by push_cast; ring
    have e2 : (((m + 1 : ℕ) : ℝ) + 1) / 2 = ((m : ℝ) + 2) / 2 := by push_cast; ring
    rw [e1, e2]
    simpa using this

lemma s55_hasDerivAt_h (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteFun n) (Real.sqrt ((n : ℝ) / 2) * hermiteFun (n - 1) x -
      Real.sqrt (((n : ℝ) + 1) / 2) * hermiteFun (n + 1) x) x := by
  have hbase := (((hasDerivAt_hermitePoly_sqrt n x).const_mul (hermiteConst n)).mul (hasDerivAt_gauss x))
  have hfun : ((fun y => hermiteConst n * hermitePoly n (Real.sqrt 2 * y)) * gauss) = hermiteFun n := by
    funext y; exact (hermiteFun_eq n y).symm
  rw [hfun] at hbase
  refine hbase.congr_deriv ?_
  cases n with
  | zero =>
    have hd : Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.derivative (Polynomial.hermite 0)) = 0 := by simp
    have key := s55_ladder_x_zero x
    have e : hermiteFun 0 x = hermiteConst 0 * gauss x := by rw [hermiteFun_eq, s55_hP0]; ring
    have hL : hermiteConst 0 * (Real.sqrt 2 * (Polynomial.aeval (Real.sqrt 2 * x)
        (Polynomial.derivative (Polynomial.hermite 0)))) * gauss x +
        hermiteConst 0 * hermitePoly 0 (Real.sqrt 2 * x) * (-x * gauss x) = -(x * hermiteFun 0 x) := by
      rw [hd, s55_hP0, e]; ring
    rw [hL, key]
    simp
  | succ m =>
    set y := Real.sqrt 2 * x with hy
    have hA : Polynomial.aeval y (Polynomial.derivative (Polynomial.hermite (m + 1))) =
        ((m : ℝ) + 1) * hermitePoly m y := by
      rw [← deriv_hermitePoly, deriv_hermitePoly_succ]
    rw [hA]
    have hladder := s55_ladder_x_succ m x
    have hc1 := s55_hc_succ m
    have hp0 : 0 < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hq0 : 0 < Real.sqrt ((m : ℝ) + 2) := Real.sqrt_pos.2 (by positivity)
    have hpp : Real.sqrt ((m : ℝ) + 1) ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hss : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hHm : hermiteFun m x = Real.sqrt ((m : ℝ) + 1) * (hermiteConst (m + 1) * hermitePoly m y * gauss x) := by
      rw [hermiteFun_eq, ← hc1]; ring
    have e1 : (((m + 1 : ℕ) : ℝ)) / 2 = ((m : ℝ) + 1) / 2 := by push_cast; ring
    have e2 : (((m + 1 : ℕ) : ℝ) + 1) / 2 = ((m : ℝ) + 2) / 2 := by push_cast; ring
    rw [e1, e2]
    have hh1 : hermiteFun (m + 1) x = hermiteConst (m + 1) * hermitePoly (m + 1) y * gauss x := hermiteFun_eq _ _
    simp only [Nat.add_sub_cancel]
    rw [Real.sqrt_div (by positivity)] at hladder ⊢
    rw [Real.sqrt_div (by positivity)] at hladder ⊢
    have hxh : x * hermiteFun (m + 1) x = Real.sqrt ((m : ℝ) + 1) / Real.sqrt 2 * hermiteFun m x +
        Real.sqrt ((m : ℝ) + 2) / Real.sqrt 2 * hermiteFun (m + 2) x := hladder
    have : hermiteConst (m + 1) * (Real.sqrt 2 * (((m : ℝ) + 1) * hermitePoly m y)) * gauss x +
        hermiteConst (m + 1) * hermitePoly (m + 1) y * (-x * gauss x) =
        Real.sqrt 2 * ((m : ℝ) + 1) * (hermiteConst (m + 1) * hermitePoly m y * gauss x) - x * hermiteFun (m + 1) x := by
      rw [hh1]; ring
    rw [this, hxh, hHm]
    field_simp
    rw [hss, hpp]; ring


/-! ### Ladder relations for `hermiteFunD` -/

lemma s55_update_h (β : MultiIndex d) (i : Fin d) (k : ℕ) (x : Euc d) :
    hermiteFunD (Function.update β i k) x =
      (∏ j ∈ Finset.univ.erase i, hermiteFun (β j) (x j)) * hermiteFun k (x i) := by
  rw [hermiteFunD_split (Function.update β i k) i x]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  · rw [Function.update_self]

lemma s55_xmul_D (β : MultiIndex d) (i : Fin d) (x : Euc d) :
    x i * hermiteFunD β x =
      Real.sqrt ((β i : ℝ) / 2) * hermiteFunD (Function.update β i (β i - 1)) x +
      Real.sqrt (((β i : ℝ) + 1) / 2) * hermiteFunD (Function.update β i (β i + 1)) x := by
  rw [hermiteFunD_split β i x, s55_update_h, s55_update_h]
  have := s55_ladder_x (β i) (x i)
  calc x i * ((∏ j ∈ Finset.univ.erase i, hermiteFun (β j) (x j)) * hermiteFun (β i) (x i))
      = (∏ j ∈ Finset.univ.erase i, hermiteFun (β j) (x j)) * (x i * hermiteFun (β i) (x i)) := by ring
    _ = _ := by rw [this]; ring

lemma s55_fderiv_D (β : MultiIndex d) (i : Fin d) (x : Euc d) :
    fderiv ℝ (hermiteFunD β) x (EuclideanSpace.single i (1 : ℝ)) =
      Real.sqrt ((β i : ℝ) / 2) * hermiteFunD (Function.update β i (β i - 1)) x -
      Real.sqrt (((β i : ℝ) + 1) / 2) * hermiteFunD (Function.update β i (β i + 1)) x := by
  have hline := (hermiteFunD_line_data β i).1 x
  have hdiff : DifferentiableAt ℝ (hermiteFunD β) x :=
    ((contDiff_hermiteFunD β).differentiable (by simp)) x
  rw [← hdiff.lineDeriv_eq_fderiv, hline.lineDeriv, (s55_hasDerivAt_h (β i) (x i)).deriv,
    s55_update_h, s55_update_h]
  ring

/-! ### Hermite combinations -/

/-- `f` is a finite combination of Hermite functions `h_β`, `|β| ≤ |α| + n`, with `ℓ¹`-norm of the coefficients
at most `A`. -/
def GComb (α : MultiIndex d) (n : ℕ) (A : ℝ) (f : Euc d → ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℝ) (β : ι → MultiIndex d),
    (∀ t, (β t).degree ≤ α.degree + n) ∧ ∑ t, |c t| ≤ A ∧
      f = fun x => ∑ t, c t * hermiteFunD (β t) x

lemma s55_GComb_base (α : MultiIndex d) : GComb α 0 1 (hermiteFunD α) := by
  refine ⟨Unit, inferInstance, fun _ => 1, fun _ => α, fun _ => by simp, by simp, ?_⟩
  funext x; simp

lemma GComb.mono {α : MultiIndex d} {n : ℕ} {A A' : ℝ} {f : Euc d → ℝ} (h : GComb α n A f) (hA : A ≤ A') :
    GComb α n A' f := by
  obtain ⟨ι, hι, c, β, h1, h2, h3⟩ := h
  exact ⟨ι, hι, c, β, h1, h2.trans hA, h3⟩

lemma GComb.congr {α : MultiIndex d} {n : ℕ} {A : ℝ} {f g : Euc d → ℝ} (h : GComb α n A f)
    (hfg : ∀ x, f x = g x) : GComb α n A g := by
  have : f = g := funext hfg
  rwa [← this]

lemma s55_deg_update_le (β : MultiIndex d) (i : Fin d) :
    MultiIndex.degree (Function.update β i (β i - 1)) ≤ β.degree := by
  unfold MultiIndex.degree
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : j = i
  · subst hj; simp
  · rw [Function.update_of_ne hj]

lemma s55_deg_update_succ (β : MultiIndex d) (i : Fin d) :
    MultiIndex.degree (Function.update β i (β i + 1)) = β.degree + 1 := by
  unfold MultiIndex.degree
  rw [Finset.sum_update_of_mem (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have : Finset.univ \ {i} = Finset.univ.erase i := by ext; simp
  rw [this]; ring

lemma s55_sqrt_le (D : ℕ) (b : ℕ) (hb : b ≤ D) :
    Real.sqrt ((b : ℝ) / 2) ≤ Real.sqrt ((D : ℝ) + 1) ∧
      Real.sqrt (((b : ℝ) + 1) / 2) ≤ Real.sqrt ((D : ℝ) + 1) := by
  have hb' : (b : ℝ) ≤ D := by exact_mod_cast hb
  constructor <;> apply Real.sqrt_le_sqrt <;> linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)]


lemma s55_comb_step {α : MultiIndex d} {n : ℕ} {A : ℝ} {f : Euc d → ℝ} (i : Fin d) (σ : ℝ) (hσ : |σ| = 1)
    (T : (Euc d → ℝ) → Euc d → ℝ)
    (hT : ∀ (β : MultiIndex d) (x : Euc d), T (hermiteFunD β) x =
      Real.sqrt ((β i : ℝ) / 2) * hermiteFunD (Function.update β i (β i - 1)) x +
      σ * Real.sqrt (((β i : ℝ) + 1) / 2) * hermiteFunD (Function.update β i (β i + 1)) x)
    (hlin : ∀ (ι : Type) (_ : Fintype ι) (c : ι → ℝ) (β : ι → MultiIndex d) (x : Euc d),
      T (fun y => ∑ t, c t * hermiteFunD (β t) y) x = ∑ t, c t * T (hermiteFunD (β t)) x)
    (h : GComb α n A f) :
    GComb α (n + 1) (2 * Real.sqrt ((α.degree : ℝ) + n + 1) * A) (T f) := by
  obtain ⟨ι, hι, c, β, h1, h2, h3⟩ := h
  let _ := hι
  refine ⟨ι × Bool, inferInstance,
    fun p => if p.2 then c p.1 * σ * Real.sqrt (((β p.1 i : ℝ) + 1) / 2)
      else c p.1 * Real.sqrt ((β p.1 i : ℝ) / 2),
    fun p => if p.2 then Function.update (β p.1) i (β p.1 i + 1)
      else Function.update (β p.1) i (β p.1 i - 1), ?_, ?_, ?_⟩
  · intro p
    obtain ⟨t, b⟩ := p
    have := h1 t
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      exact (s55_deg_update_le _ _).trans (this.trans (by omega))
    · simp only [ite_true]
      rw [s55_deg_update_succ]; omega
  · have hb : ∀ t, β t i ≤ α.degree + n := fun t =>
      (Finset.single_le_sum (f := β t) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (h1 t)
    have hsq : ∀ t, Real.sqrt ((β t i : ℝ) / 2) + Real.sqrt (((β t i : ℝ) + 1) / 2) ≤
        2 * Real.sqrt ((α.degree : ℝ) + n + 1) := by
      intro t
      have := s55_sqrt_le (α.degree + n) (β t i) (hb t)
      push_cast at this
      linarith [this.1, this.2]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
    calc ∑ t, (|c t * σ * Real.sqrt (((β t i : ℝ) + 1) / 2)| + |c t * Real.sqrt ((β t i : ℝ) / 2)|)
        ≤ ∑ t, |c t| * (2 * Real.sqrt ((α.degree : ℝ) + n + 1)) := by
          refine Finset.sum_le_sum fun t _ => ?_
          simp only [abs_mul, hσ, mul_one, abs_of_nonneg (Real.sqrt_nonneg _)]
          nlinarith [hsq t, abs_nonneg (c t)]
      _ = (∑ t, |c t|) * (2 * Real.sqrt ((α.degree : ℝ) + n + 1)) := by rw [Finset.sum_mul]
      _ ≤ A * (2 * Real.sqrt ((α.degree : ℝ) + n + 1)) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 2 * Real.sqrt ((α.degree : ℝ) + n + 1) * A := by ring
  · funext x
    rw [h3, hlin ι hι c β x]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hT]; ring

lemma GComb.mulX {α : MultiIndex d} {n : ℕ} {A : ℝ} {f : Euc d → ℝ} (i : Fin d) (h : GComb α n A f) :
    GComb α (n + 1) (2 * Real.sqrt ((α.degree : ℝ) + n + 1) * A) (fun x => x i * f x) := by
  refine s55_comb_step (T := fun g x => x i * g x) i 1 (by simp) ?_ ?_ h
  · intro β x
    rw [s55_xmul_D]; ring
  · intro ι _ c β x
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring

lemma GComb.deriv {α : MultiIndex d} {n : ℕ} {A : ℝ} {f : Euc d → ℝ} (i : Fin d) (h : GComb α n A f) :
    GComb α (n + 1) (2 * Real.sqrt ((α.degree : ℝ) + n + 1) * A)
      (fun x => fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))) := by
  refine s55_comb_step (T := fun g x => fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) i (-1) (by simp) ?_ ?_ h
  · intro β x
    rw [s55_fderiv_D]; ring
  · intro ι hι c β x
    let _ := hι
    have hd : ∀ y, HasFDerivAt (fun y => ∑ t, c t * hermiteFunD (β t) y)
        (∑ t, c t • fderiv ℝ (hermiteFunD (β t)) y) y := by
      intro y
      refine HasFDerivAt.fun_sum fun t _ => ?_
      exact (((contDiff_hermiteFunD (β t)).differentiable (by simp)) y).hasFDerivAt.const_mul (c t)
    rw [(hd x).fderiv]
    simp


/-- the step factor for words of length at most `N` -/
def KK (α : MultiIndex d) (N : ℕ) : ℝ := 2 * Real.sqrt ((α.degree : ℝ) + N + 1)

lemma KK_nonneg (α : MultiIndex d) (N : ℕ) : 0 ≤ KK α N := by unfold KK; positivity

lemma GComb.mulX_iter {α : MultiIndex d} {n : ℕ} {A : ℝ} {f : Euc d → ℝ} (i : Fin d) (N : ℕ)
    (h : GComb α n A f) (hA : 0 ≤ A) : ∀ m : ℕ, n + m ≤ N →
    GComb α (n + m) (KK α N ^ m * A) (fun x => x i ^ m * f x) := by
  intro m
  induction m with
  | zero =>
    intro _
    simpa using h
  | succ m ih =>
    intro hm
    have h1 := (ih (by omega)).mulX i
    refine (h1.mono ?_).congr ?_
    · have hK : 2 * Real.sqrt ((α.degree : ℝ) + ((n + m : ℕ) : ℝ) + 1) ≤ KK α N := by
        unfold KK
        have : ((n + m : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : n + m ≤ N)
        have := Real.sqrt_le_sqrt (show (α.degree : ℝ) + ((n + m : ℕ) : ℝ) + 1 ≤ α.degree + N + 1 by linarith)
        linarith
      have hp : 0 ≤ KK α N ^ m * A := mul_nonneg (pow_nonneg (KK_nonneg α N) _) hA
      calc 2 * Real.sqrt ((α.degree : ℝ) + ((n + m : ℕ) : ℝ) + 1) * (KK α N ^ m * A)
          ≤ KK α N * (KK α N ^ m * A) := mul_le_mul_of_nonneg_right hK hp
        _ = KK α N ^ (m + 1) * A := by ring
    · intro x; simp only [pow_succ]; ring


lemma s55_partialDeriv_succ {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {j : ℕ} (idx : Fin (j + 1) → Fin d)
    (x : Euc d) :
    partialDeriv idx f x = fderiv ℝ (partialDeriv (Fin.tail idx) f) x (EuclideanSpace.single (idx 0) (1 : ℝ)) := by
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ j f) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top j)
  set u : Fin j → Euc d := fun l => EuclideanSpace.single (Fin.tail idx l) (1 : ℝ) with hu
  set E : ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ u with hE
  have hfun : partialDeriv (Fin.tail idx) f = fun y => E (iteratedFDeriv ℝ j f y) := rfl
  have hd : HasFDerivAt (partialDeriv (Fin.tail idx) f) (E.comp (fderiv ℝ (iteratedFDeriv ℝ j f) x)) x := by
    rw [hfun]
    exact E.hasFDerivAt.comp x (hdiff x).hasFDerivAt
  rw [hd.fderiv]
  unfold partialDeriv
  rw [iteratedFDeriv_succ_apply_left]
  rfl

lemma s55_partial_comb (α : MultiIndex d) (N : ℕ) :
    ∀ (j : ℕ) (idx : Fin j → Fin d), j ≤ N → GComb α j (KK α N ^ j) (partialDeriv idx (hermiteFunD α)) := by
  intro j
  induction j with
  | zero =>
    intro idx _
    refine ((s55_GComb_base α).mono (by simp)).congr fun x => ?_
    unfold partialDeriv
    rw [iteratedFDeriv_zero_apply]
  | succ j ih =>
    intro idx hj
    have h1 := (ih (Fin.tail idx) (by omega)).deriv (idx 0)
    refine (h1.mono ?_).congr fun x => ?_
    · have hK : 2 * Real.sqrt ((α.degree : ℝ) + j + 1) ≤ KK α N := by
        unfold KK
        have : (j : ℝ) ≤ N := by exact_mod_cast (by omega : j ≤ N)
        have := Real.sqrt_le_sqrt (show (α.degree : ℝ) + j + 1 ≤ α.degree + N + 1 by linarith)
        linarith
      calc 2 * Real.sqrt ((α.degree : ℝ) + j + 1) * KK α N ^ j ≤ KK α N * KK α N ^ j :=
            mul_le_mul_of_nonneg_right hK (pow_nonneg (KK_nonneg α N) _)
        _ = KK α N ^ (j + 1) := by ring
    · exact (s55_partialDeriv_succ (contDiff_hermiteFunD α) idx x).symm


/-! ### Sup bounds with weights -/

lemma GComb.sup_le {α : MultiIndex d} {n : ℕ} {A : ℝ} {f : Euc d → ℝ} (h : GComb α n A f) {C : ℝ}
    (hC : ∀ (β : MultiIndex d) (x : Euc d), |hermiteFunD β x| ≤ C) (x : Euc d) : |f x| ≤ A * C := by
  obtain ⟨ι, hι, c, β, h1, h2, h3⟩ := h
  let _ := hι
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (fun _ => 0) 0)
  rw [h3]
  calc |∑ t, c t * hermiteFunD (β t) x| ≤ ∑ t, |c t * hermiteFunD (β t) x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t, |c t| * C := Finset.sum_le_sum fun t _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC _ _) (abs_nonneg _)
    _ = (∑ t, |c t|) * C := by rw [Finset.sum_mul]
    _ ≤ A * C := mul_le_mul_of_nonneg_right h2 hC0

lemma s55_jb_pow_le (p : ℕ) (x : Euc d) :
    jbracket x ^ (2 * p) ≤ ((d : ℝ) + 1) ^ p * (1 + ∑ i, (x i) ^ (2 * p)) := by
  have hjb : jbracket x ^ 2 = 1 + ∑ i, (x i) ^ 2 := by
    rw [HRS.MP.RdInit.mri_jb_sq, EuclideanSpace.norm_sq_eq]
    simp
  rw [pow_mul, hjb]
  cases p with
  | zero => simp
  | succ q =>
    set f : Option (Fin d) → ℝ := fun o => o.elim 1 (fun i => (x i) ^ 2) with hf
    have hf0 : ∀ o ∈ (Finset.univ : Finset (Option (Fin d))), 0 ≤ f o := by
      intro o _
      cases o <;> simp [hf] <;> positivity
    have h1 := pow_sum_le_card_mul_sum_pow hf0 q
    have hs : ∑ o, f o = 1 + ∑ i, (x i) ^ 2 := by
      rw [Fintype.sum_option]; simp [hf]
    have hs2 : ∑ o, f o ^ (q + 1) = 1 + ∑ i, ((x i) ^ 2) ^ (q + 1) := by
      rw [Fintype.sum_option]; simp [hf]
    rw [hs, hs2, Finset.card_univ, Fintype.card_option, Fintype.card_fin] at h1
    have hd1 : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    calc (1 + ∑ i, (x i) ^ 2) ^ (q + 1) ≤ ((d + 1 : ℕ) : ℝ) ^ q * (1 + ∑ i, ((x i) ^ 2) ^ (q + 1)) := by
          exact_mod_cast h1
      _ ≤ ((d : ℝ) + 1) ^ (q + 1) * (1 + ∑ i, ((x i) ^ 2) ^ (q + 1)) := by
          push_cast
          refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hd1 (Nat.le_succ q)) ?_
          have : 0 ≤ ∑ i, ((x i) ^ 2) ^ (q + 1) := Finset.sum_nonneg fun i _ => by positivity
          linarith
      _ = _ := by simp only [← pow_mul]

lemma s55_weighted_comb_bound {α : MultiIndex d} {n : ℕ} {A : ℝ} {g : Euc d → ℝ} (N : ℕ)
    (hg : GComb α n A g) (hA : 0 ≤ A) (p : ℕ) (hnp : n + 2 * p ≤ N) (hK1 : 1 ≤ KK α N) {C : ℝ}
    (hC : ∀ (β : MultiIndex d) (x : Euc d), |hermiteFunD β x| ≤ C) (x : Euc d) :
    jbracket x ^ (2 * p) * |g x| ≤ ((d : ℝ) + 1) ^ p * (1 + d) * (KK α N ^ (2 * p) * (A * C)) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (fun _ => 0) 0)
  have hK0 : 0 ≤ KK α N := KK_nonneg α N
  have hKp : 1 ≤ KK α N ^ (2 * p) := one_le_pow₀ hK1
  have hAC : 0 ≤ A * C := mul_nonneg hA hC0
  have hg0 : |g x| ≤ A * C := hg.sup_le hC x
  have hterm : ∀ i : Fin d, |(x i) ^ (2 * p) * g x| ≤ KK α N ^ (2 * p) * (A * C) := by
    intro i
    have := (hg.mulX_iter i N hA (2 * p) hnp).sup_le hC x
    simpa [mul_assoc] using this
  have hpos : ∀ i : Fin d, 0 ≤ (x i) ^ (2 * p) := fun i => by
    rw [pow_mul]; positivity
  calc jbracket x ^ (2 * p) * |g x|
      ≤ (((d : ℝ) + 1) ^ p * (1 + ∑ i, (x i) ^ (2 * p))) * |g x| :=
        mul_le_mul_of_nonneg_right (s55_jb_pow_le p x) (abs_nonneg _)
    _ = ((d : ℝ) + 1) ^ p * (|g x| + ∑ i, |(x i) ^ (2 * p) * g x|) := by
        have : ∑ i, |(x i) ^ (2 * p) * g x| = (∑ i, (x i) ^ (2 * p)) * |g x| := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [abs_mul, abs_of_nonneg (hpos i)]
        rw [this]; ring
    _ ≤ ((d : ℝ) + 1) ^ p * (KK α N ^ (2 * p) * (A * C) + ∑ _i : Fin d, KK α N ^ (2 * p) * (A * C)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ (Finset.sum_le_sum fun i _ => hterm i)) (by positivity)
        calc |g x| ≤ A * C := hg0
          _ = 1 * (A * C) := by ring
          _ ≤ KK α N ^ (2 * p) * (A * C) := mul_le_mul_of_nonneg_right hKp hAC
    _ = ((d : ℝ) + 1) ^ p * (1 + d) * (KK α N ^ (2 * p) * (A * C)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring


/-! ### The decay norm of the Hermite functions -/

lemma s55_KK_ge_one (α : MultiIndex d) (N : ℕ) : 1 ≤ KK α N := by
  unfold KK
  have : (1 : ℝ) ≤ Real.sqrt ((α.degree : ℝ) + N + 1) := by
    rw [Real.one_le_sqrt]; have := (Nat.cast_nonneg α.degree : (0 : ℝ) ≤ α.degree)
    have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith
  linarith

lemma s55_KK_le (α : MultiIndex d) (N : ℕ) :
    KK α N ≤ 2 * Real.sqrt ((N : ℝ) + 1) * Real.sqrt (oscEigenvalue d α) := by
  unfold KK
  have h1 : (α.degree : ℝ) + N + 1 ≤ ((N : ℝ) + 1) * oscEigenvalue d α := by
    unfold oscEigenvalue
    have h0 : (0 : ℝ) ≤ α.degree := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    nlinarith [mul_nonneg h2 h0, mul_nonneg h2 h3]
  have := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_mul (by positivity)] at this
  linarith

lemma s55_decay_hermite (k : ℕ) (b : ℝ) (hb : 0 ≤ b) (N0 : ℕ) (hN : k + 2 * ⌈(b + k) / 2⌉₊ ≤ N0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α : MultiIndex d,
      decayNormE k b (hermiteFunD α) ≤ ENNReal.ofReal (C * Real.sqrt (oscEigenvalue d α) ^ N0) := by
  obtain ⟨Cinf, hC⟩ := hermiteFunD_uniform_bound (d := d)
  have hC0 : 0 ≤ Cinf := (abs_nonneg _).trans (hC (fun _ => 0) 0)
  set p : ℕ := ⌈(b + k) / 2⌉₊ with hp
  refine ⟨((d : ℝ) + 1) ^ (p + 1) * Cinf * (2 * Real.sqrt ((N0 : ℝ) + 1)) ^ N0, by positivity, fun α => ?_⟩
  unfold decayNormE
  refine s55_dse_le fun j hj idx x => ?_
  have hKK1 := s55_KK_ge_one α N0
  have hcomb := s55_partial_comb α N0 j idx (by omega)
  have hb2 : b + j ≤ ((2 * p : ℕ) : ℝ) := by
    have h1 : (b + k) / 2 ≤ p := Nat.le_ceil _
    have h2 : (j : ℝ) ≤ k := by exact_mod_cast hj
    push_cast; linarith
  have h1 : jbracket x ^ (b + j) ≤ jbracket x ^ (2 * p) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (HRS.MS.Adj.ad1_one_le_jb x) hb2
  have hK0 : 0 ≤ KK α N0 := KK_nonneg α N0
  have hA : 0 ≤ KK α N0 ^ j := pow_nonneg hK0 _
  have h2 := s55_weighted_comb_bound N0 hcomb hA p (by omega) hKK1 hC x
  have h3 : KK α N0 ^ (2 * p) * (KK α N0 ^ j * Cinf) ≤ KK α N0 ^ N0 * Cinf := by
    rw [← mul_assoc, ← pow_add]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hKK1 (by omega)) hC0
  have h4 : KK α N0 ^ N0 ≤ (2 * Real.sqrt ((N0 : ℝ) + 1)) ^ N0 * Real.sqrt (oscEigenvalue d α) ^ N0 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hK0 (by simpa [mul_assoc] using s55_KK_le α N0) N0
  have hd0 : (0 : ℝ) ≤ ((d : ℝ) + 1) ^ p * (1 + d) := by positivity
  calc jbracket x ^ (b + j) * |partialDeriv idx (hermiteFunD α) x|
      ≤ jbracket x ^ (2 * p) * |partialDeriv idx (hermiteFunD α) x| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ ≤ ((d : ℝ) + 1) ^ p * (1 + d) * (KK α N0 ^ (2 * p) * (KK α N0 ^ j * Cinf)) := h2
    _ ≤ ((d : ℝ) + 1) ^ p * (1 + d) * (KK α N0 ^ N0 * Cinf) := mul_le_mul_of_nonneg_left h3 hd0
    _ ≤ ((d : ℝ) + 1) ^ p * (1 + d) * (((2 * Real.sqrt ((N0 : ℝ) + 1)) ^ N0 *
          Real.sqrt (oscEigenvalue d α) ^ N0) * Cinf) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 hC0) hd0
    _ = ((d : ℝ) + 1) ^ (p + 1) * Cinf * (2 * Real.sqrt ((N0 : ℝ) + 1)) ^ N0 *
          Real.sqrt (oscEigenvalue d α) ^ N0 := by ring

end HRS.MS.Go
