import HRS.MS.R2WinOrbNLAux8

/-!
# S10.3 (nonlinear branch), part 9: finite-smoothness jet classes `Bd`, `Sy` and their calculus

Prefix `s103n`, namespace `HRS.MS.R2WinOrbNL`.  `Bd N A f`: `f ∈ C^N` with `‖D^j f(x)‖ ≤ A` (`j ≤ N`).  `Sy N A f`: `‖D^j f(x)‖ ≤ A/(1+‖x‖)`.
Sums, scalar multiples, products (`Bd × Bd`, `Sy × Bd`), directional derivatives, the multiplication by a coordinate (`Sy N → Bd N`) and the
Laplacian.  These replace the `C^∞` symbol calculus `ul6S` for functions of finite smoothness.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole

variable {d : ℕ}

/-- Bounded jets up to order `N`. -/
def Bd (N : ℕ) (A : ℝ) (f : Euc d → ℝ) : Prop :=
  ContDiff ℝ (N : WithTop ℕ∞) f ∧ ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A

/-- Jets up to order `N` decaying like `(1+‖x‖)⁻¹`. -/
def Sy (N : ℕ) (A : ℝ) (f : Euc d → ℝ) : Prop :=
  ContDiff ℝ (N : WithTop ℕ∞) f ∧ ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A * (1 + ‖x‖)⁻¹

theorem Bd.nonneg {N : ℕ} {A : ℝ} {f : Euc d → ℝ} (h : Bd N A f) : 0 ≤ A :=
  (norm_nonneg _).trans (h.2 0 (Nat.zero_le _) 0)

theorem Sy.nonneg {N : ℕ} {A : ℝ} {f : Euc d → ℝ} (h : Sy N A f) : 0 ≤ A := by
  have := h.2 0 (Nat.zero_le _) 0
  simp only [norm_zero, add_zero, inv_one, mul_one] at this
  exact (norm_nonneg _).trans this

theorem Sy.bd {N : ℕ} {A : ℝ} {f : Euc d → ℝ} (h : Sy N A f) : Bd N A f := by
  refine ⟨h.1, fun j hj x => (h.2 j hj x).trans ?_⟩
  have hA := h.nonneg
  have : (1 + ‖x‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg x])
  nlinarith

theorem Bd.mono_N {N N' : ℕ} (hN : N' ≤ N) {A : ℝ} {f : Euc d → ℝ} (h : Bd N A f) : Bd N' A f :=
  ⟨h.1.of_le (by exact_mod_cast hN), fun j hj x => h.2 j (hj.trans hN) x⟩

theorem Sy.mono_N {N N' : ℕ} (hN : N' ≤ N) {A : ℝ} {f : Euc d → ℝ} (h : Sy N A f) : Sy N' A f :=
  ⟨h.1.of_le (by exact_mod_cast hN), fun j hj x => h.2 j (hj.trans hN) x⟩

theorem Bd.mono_A {N : ℕ} {A A' : ℝ} (hA : A ≤ A') {f : Euc d → ℝ} (h : Bd N A f) : Bd N A' f :=
  ⟨h.1, fun j hj x => (h.2 j hj x).trans hA⟩

theorem Sy.mono_A {N : ℕ} {A A' : ℝ} (hA : A ≤ A') {f : Euc d → ℝ} (h : Sy N A f) : Sy N A' f :=
  ⟨h.1, fun j hj x => (h.2 j hj x).trans
    (mul_le_mul_of_nonneg_right hA (inv_nonneg.2 (by linarith [norm_nonneg x])))⟩

theorem Bd.zero (N : ℕ) : Bd N 0 (fun _ : Euc d => (0 : ℝ)) := by
  refine ⟨contDiff_const, fun j _ x => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · rw [iteratedFDeriv_const_of_ne hj.ne']; simp

theorem Bd.add {N : ℕ} {A B : ℝ} {f g : Euc d → ℝ} (hf : Bd N A f) (hg : Bd N B g) :
    Bd N (A + B) (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, fun j hj x => ?_⟩
  have e : (fun x => f x + g x) = f + g := rfl
  rw [e, iteratedFDeriv_add_apply (hf.1.of_le (by exact_mod_cast hj)).contDiffAt
    (hg.1.of_le (by exact_mod_cast hj)).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hf.2 j hj x) (hg.2 j hj x))

theorem Bd.smul {N : ℕ} {A : ℝ} {f : Euc d → ℝ} (hf : Bd N A f) (c : ℝ) :
    Bd N (|c| * A) (fun x => c * f x) := by
  refine ⟨contDiff_const.mul hf.1, fun j hj x => ?_⟩
  have e : (fun x => c * f x) = c • f := by funext x; simp
  rw [e, iteratedFDeriv_const_smul_apply (hf.1.of_le (by exact_mod_cast hj)).contDiffAt, norm_smul,
    Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hf.2 j hj x) (abs_nonneg _)

theorem Sy.add {N : ℕ} {A B : ℝ} {f g : Euc d → ℝ} (hf : Sy N A f) (hg : Sy N B g) :
    Sy N (A + B) (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, fun j hj x => ?_⟩
  have e : (fun x => f x + g x) = f + g := rfl
  rw [e, iteratedFDeriv_add_apply (hf.1.of_le (by exact_mod_cast hj)).contDiffAt
    (hg.1.of_le (by exact_mod_cast hj)).contDiffAt]
  refine (norm_add_le _ _).trans ?_
  have := add_le_add (hf.2 j hj x) (hg.2 j hj x)
  linarith

theorem Sy.smul {N : ℕ} {A : ℝ} {f : Euc d → ℝ} (hf : Sy N A f) (c : ℝ) :
    Sy N (|c| * A) (fun x => c * f x) := by
  refine ⟨contDiff_const.mul hf.1, fun j hj x => ?_⟩
  have e : (fun x => c * f x) = c • f := by funext x; simp
  rw [e, iteratedFDeriv_const_smul_apply (hf.1.of_le (by exact_mod_cast hj)).contDiffAt, norm_smul,
    Real.norm_eq_abs]
  calc |c| * ‖iteratedFDeriv ℝ j f x‖ ≤ |c| * (A * (1 + ‖x‖)⁻¹) :=
        mul_le_mul_of_nonneg_left (hf.2 j hj x) (abs_nonneg _)
    _ = _ := by ring

theorem Bd.sum {N : ℕ} {ι : Type*} (S : Finset ι) (f : ι → Euc d → ℝ) (A : ι → ℝ)
    (h : ∀ i ∈ S, Bd N (A i) (f i)) : Bd N (∑ i ∈ S, A i) (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using Bd.zero (d := d) N
  | insert a S ha ih =>
    have h1 := h a (Finset.mem_insert_self _ _)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have := h1.add h2
    simp only [Finset.sum_insert ha]
    exact this

theorem Bd.mul {N : ℕ} {A B : ℝ} {f g : Euc d → ℝ} (hf : Bd N A f) (hg : Bd N B g) :
    Bd N (2 ^ N * A * B) (fun x => f x * g x) := by
  have hA := hf.nonneg
  have hB := hg.nonneg
  refine ⟨hf.1.mul hg.1, fun j hj x => ?_⟩
  refine (norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := f) (g := g) (N := (N : ℕ∞ω)) hf.1 hg.1 x
    (n := j) (by exact_mod_cast hj)).trans ?_
  have hterm : ∀ l ∈ Finset.range (j + 1),
      (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l f x‖ * ‖iteratedFDeriv ℝ (j - l) g x‖ ≤
        (j.choose l : ℝ) * (A * B) := by
    intro l hl
    have hl' : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul (hf.2 l (by omega) x) (hg.2 (j - l) (by omega) x) (norm_nonneg _) hA
  calc _ ≤ ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * (A * B) := Finset.sum_le_sum hterm
    _ = (2 : ℝ) ^ j * (A * B) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose j
    _ ≤ (2 : ℝ) ^ N * (A * B) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) (mul_nonneg hA hB)
    _ = _ := by ring

theorem Sy.mul_bd {N : ℕ} {A B : ℝ} {f g : Euc d → ℝ} (hf : Sy N A f) (hg : Bd N B g) :
    Sy N (2 ^ N * A * B) (fun x => f x * g x) := by
  have hA := hf.nonneg
  have hB := hg.nonneg
  refine ⟨hf.1.mul hg.1, fun j hj x => ?_⟩
  refine (norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := f) (g := g) (N := (N : ℕ∞ω)) hf.1 hg.1 x
    (n := j) (by exact_mod_cast hj)).trans ?_
  have hw : 0 ≤ (1 + ‖x‖)⁻¹ := inv_nonneg.2 (by linarith [norm_nonneg x])
  have hterm : ∀ l ∈ Finset.range (j + 1),
      (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l f x‖ * ‖iteratedFDeriv ℝ (j - l) g x‖ ≤
        (j.choose l : ℝ) * (A * (1 + ‖x‖)⁻¹ * B) := by
    intro l hl
    have hl' : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul (hf.2 l (by omega) x) (hg.2 (j - l) (by omega) x) (norm_nonneg _)
      (mul_nonneg hA hw)
  calc _ ≤ ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * (A * (1 + ‖x‖)⁻¹ * B) :=
        Finset.sum_le_sum hterm
    _ = (2 : ℝ) ^ j * (A * (1 + ‖x‖)⁻¹ * B) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose j
    _ ≤ (2 : ℝ) ^ N * (A * (1 + ‖x‖)⁻¹ * B) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) (by positivity)
    _ = _ := by ring

theorem Bd.deriv {N : ℕ} {A : ℝ} {f : Euc d → ℝ} (hf : Bd (N + 1) A f) (v : Euc d) :
    Bd N (A * ‖v‖) (fun y => fderiv ℝ f y v) := by
  have hd1 : ContDiff ℝ (N : WithTop ℕ∞) (fderiv ℝ f) :=
    hf.1.fderiv_right (by exact_mod_cast le_refl (N + 1))
  refine ⟨hd1.clm_apply contDiff_const, fun m hm y => ?_⟩
  refine (norm_iteratedFDeriv_clm_apply_const (N := (N : WithTop ℕ∞)) (c := v) (n := m)
    hd1.contDiffAt (by exact_mod_cast hm)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  have := hf.2 (m + 1) (by omega) y
  calc ‖v‖ * ‖iteratedFDeriv ℝ (m + 1) f y‖ ≤ ‖v‖ * A := mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := by ring

theorem Sy.deriv {N : ℕ} {A : ℝ} {f : Euc d → ℝ} (hf : Sy (N + 1) A f) (v : Euc d) :
    Sy N (A * ‖v‖) (fun y => fderiv ℝ f y v) := by
  have hd1 : ContDiff ℝ (N : WithTop ℕ∞) (fderiv ℝ f) :=
    hf.1.fderiv_right (by exact_mod_cast le_refl (N + 1))
  refine ⟨hd1.clm_apply contDiff_const, fun m hm y => ?_⟩
  refine (norm_iteratedFDeriv_clm_apply_const (N := (N : WithTop ℕ∞)) (c := v) (n := m)
    hd1.contDiffAt (by exact_mod_cast hm)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  have := hf.2 (m + 1) (by omega) y
  calc ‖v‖ * ‖iteratedFDeriv ℝ (m + 1) f y‖ ≤ ‖v‖ * (A * (1 + ‖y‖)⁻¹) :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := by ring

theorem s103n_proj_norm_le (i : Fin d) : ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    simpa using PiLp.norm_apply_le v i

theorem s103n_coord_iter (i : Fin d) (x : Euc d) (l : ℕ) :
    ‖iteratedFDeriv ℝ l (fun y : Euc d => y i) x‖ ≤
      (if l = 0 then ‖x‖ else 0) + (if l = 1 then 1 else 0) := by
  rcases l with _ | n
  · rw [norm_iteratedFDeriv_zero]
    simp only [if_true, Nat.zero_ne_one, if_false, add_zero]
    exact PiLp.norm_apply_le x i
  · have hfd : fderiv ℝ (fun y : Euc d => y i) = fun _ => (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) := by
      funext y
      exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.fderiv
    rw [← norm_iteratedFDeriv_fderiv, hfd]
    rcases n with _ | n
    · rw [norm_iteratedFDeriv_zero]
      have := s103n_proj_norm_le i
      simpa using this
    · rw [iteratedFDeriv_const_of_ne (by omega)]
      simp

theorem Sy.xmul {N : ℕ} {A : ℝ} {f : Euc d → ℝ} (hf : Sy N A f) (i : Fin d) :
    Bd N ((N + 1) * A) (fun x => x i * f x) := by
  have hA := hf.nonneg
  have hc : ContDiff ℝ (N : WithTop ℕ∞) (fun y : Euc d => y i) :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff
  refine ⟨hc.mul hf.1, fun j hj x => ?_⟩
  refine (norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := fun y : Euc d => y i) (g := f)
    (N := (N : ℕ∞ω)) hc hf.1 x (n := j) (by exact_mod_cast hj)).trans ?_
  have hw : 0 ≤ (1 + ‖x‖)⁻¹ := inv_nonneg.2 (by linarith [norm_nonneg x])
  have hx1 : ‖x‖ * (1 + ‖x‖)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by linarith [norm_nonneg x])]; linarith
  have hw1 : (1 + ‖x‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg x])
  have hterm : ∀ l ∈ Finset.range (j + 1),
      (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fun y : Euc d => y i) x‖ * ‖iteratedFDeriv ℝ (j - l) f x‖ ≤
        (if l = 0 then A else 0) + (if l = 1 then (j : ℝ) * A else 0) := by
    intro l hl
    have hl' : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hfj := hf.2 (j - l) (by omega) x
    have hc' := s103n_coord_iter i x l
    by_cases h0 : l = 0
    · subst h0
      simp only [if_true, Nat.zero_ne_one, if_false, add_zero, Nat.choose_zero_right, Nat.cast_one,
        one_mul, tsub_zero] at hc' hfj ⊢
      calc ‖iteratedFDeriv ℝ 0 (fun y : Euc d => y i) x‖ * ‖iteratedFDeriv ℝ j f x‖ ≤
          ‖x‖ * (A * (1 + ‖x‖)⁻¹) := mul_le_mul hc' hfj (norm_nonneg _) (norm_nonneg _)
        _ = A * (‖x‖ * (1 + ‖x‖)⁻¹) := by ring
        _ ≤ A * 1 := mul_le_mul_of_nonneg_left hx1 hA
        _ = A := mul_one A
    · by_cases h1 : l = 1
      · subst h1
        simp only [one_ne_zero, if_false, zero_add, if_true, Nat.choose_one_right] at hc' ⊢
        calc (j : ℝ) * ‖iteratedFDeriv ℝ 1 (fun y : Euc d => y i) x‖ * ‖iteratedFDeriv ℝ (j - 1) f x‖
            ≤ (j : ℝ) * 1 * (A * (1 + ‖x‖)⁻¹) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hc' (Nat.cast_nonneg _)) hfj (norm_nonneg _)
                (by positivity)
          _ ≤ (j : ℝ) * 1 * (A * 1) := by gcongr
          _ = (j : ℝ) * A := by ring
      · simp only [h0, h1, if_false, add_zero] at hc' ⊢
        have : ‖iteratedFDeriv ℝ l (fun y : Euc d => y i) x‖ = 0 := le_antisymm hc' (norm_nonneg _)
        rw [this]; simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_range, Nat.succ_pos, if_true]
  by_cases hj1 : 1 ≤ j
  · simp only [Nat.lt_succ_iff, hj1, if_true]
    have : (j : ℝ) ≤ N := by exact_mod_cast hj
    nlinarith
  · simp only [Nat.lt_succ_iff, hj1, if_false]
    nlinarith

theorem s103n_lap_eq {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (x : Euc d) :
    Laplacian.laplacian f x = ∑ i : Fin d,
      fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))) x (EuclideanSpace.single i (1 : ℝ)) := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply]
  have := (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).hasFDerivAt.comp x
    hfd.hasFDerivAt
  have e : (fun y => fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))) =
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))) ∘ (fderiv ℝ f) := rfl
  rw [e, this.fderiv]
  simp

theorem Bd.lap {N : ℕ} {A : ℝ} {f : Euc d → ℝ} (hf : Bd (N + 2) A f) :
    Bd N (d * A) (fun x => Laplacian.laplacian f x) := by
  have hn : ∀ i : Fin d, ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := fun i => by simp
  have hfun : (fun x => Laplacian.laplacian f x) = fun x => ∑ i : Fin d,
      fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))) x
        (EuclideanSpace.single i (1 : ℝ)) :=
    funext fun x => s103n_lap_eq (hf.1.of_le (by exact_mod_cast Nat.le_add_left 2 N)) x
  rw [hfun]
  have := Bd.sum (N := N) Finset.univ (fun i x => fderiv ℝ (fun y => fderiv ℝ f y
    (EuclideanSpace.single i (1 : ℝ))) x (EuclideanSpace.single i (1 : ℝ))) (fun _ => A) (fun i _ => by
      have h1 := hf.deriv (EuclideanSpace.single i (1 : ℝ))
      have h2 := h1.deriv (EuclideanSpace.single i (1 : ℝ))
      rw [hn i] at h1 h2
      simpa using h2)
  simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this

end HRS.MS.R2WinOrbNL

end
