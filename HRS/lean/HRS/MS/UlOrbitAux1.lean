import HRS.MS.UlTailTie
import HRS.MS.UlTie1
import HRS.MS.MovOscAux4

/-!
# UL-6 (S5.1 part 2, orbit data), part 1: quantitative symbol calculus

Infrastructure packet UL-6 (supplement `W:r2:orbit-bounds`); not a manuscript row.  Helper lemmas carry the
prefix `ul6_`; namespace `HRS.MS.Ul`.

`ul6S P m A g` : `‖D^j g(x)‖ ≤ A (1+‖x‖)^{P-j}` for `j ≤ m` (an inequality only; smoothness is a separate
hypothesis).  Unlike `UlSym` of `UlTail`, the constant `A` is explicit, so that linear bounds
`‖L^a f‖ ≤ C ‖f‖` can be obtained: `ul6_L_step` says that the generator `L` maps `ul6S P0 (m+2) A g` into
`ul6S P0 m (C A) (L g)`, `P0 = -(s+1)`, with `C` depending only on `m` and the data.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.Ul

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-- weighted bounds on the derivatives up to order `m` -/
def ul6S (P : ℝ) (m : ℕ) (A : ℝ) (g : Euc d → ℝ) : Prop :=
  ∀ j ≤ m, ∀ x : Euc d, ‖iteratedFDeriv ℝ j g x‖ ≤ A * (1 + ‖x‖) ^ (P - j)

lemma ul6_w_pos' (x : Euc d) : 0 < 1 + ‖x‖ := by positivity

lemma ul6S_nonneg {P : ℝ} {m : ℕ} {A : ℝ} {g : Euc d → ℝ} (h : ul6S P m A g) : 0 ≤ A := by
  have := h 0 (Nat.zero_le _) 0
  simp only [norm_zero, add_zero, Nat.cast_zero, sub_zero, Real.one_rpow, mul_one] at this
  exact (norm_nonneg _).trans this

lemma ul6S_mono_P {P P' : ℝ} (hP : P ≤ P') {m : ℕ} {A : ℝ} {g : Euc d → ℝ} (h : ul6S P m A g) :
    ul6S P' m A g := fun j hj x => (h j hj x).trans
  (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x])
    (by linarith)) (ul6S_nonneg h))

lemma ul6S_mono_m {P : ℝ} {m m' : ℕ} (hm : m' ≤ m) {A : ℝ} {g : Euc d → ℝ} (h : ul6S P m A g) :
    ul6S P m' A g := fun j hj x => h j (hj.trans hm) x

lemma ul6S_mono_A {P : ℝ} {m : ℕ} {A A' : ℝ} (hA : A ≤ A') {g : Euc d → ℝ} (h : ul6S P m A g) :
    ul6S P m A' g := fun j hj x => (h j hj x).trans
  (mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg (ul6_w_pos' x).le _))

lemma ul6S_zero (P : ℝ) (m : ℕ) : ul6S P m 0 (fun _ : Euc d => (0 : ℝ)) := by
  intro j _ x
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · rw [iteratedFDeriv_const_of_ne hj.ne']; simp

lemma ul6S_add {P : ℝ} {m : ℕ} {A B : ℝ} {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (h1 : ul6S P m A f) (h2 : ul6S P m B g) : ul6S P m (A + B) (fun x => f x + g x) := by
  intro j hj x
  have e : (fun x => f x + g x) = f + g := rfl
  rw [e, iteratedFDeriv_add_apply (ult_cdat hf j x) (ult_cdat hg j x)]
  refine (norm_add_le _ _).trans ?_
  nlinarith [h1 j hj x, h2 j hj x]

lemma ul6S_smul {P : ℝ} {m : ℕ} {A : ℝ} {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g) (c : ℝ)
    (h : ul6S P m A g) : ul6S P m (|c| * A) (fun x => c * g x) := by
  intro j hj x
  have e : (fun x => c * g x) = fun x => c • g x := rfl
  rw [e, iteratedFDeriv_const_smul_apply' (ult_cdat hg j x), norm_smul, Real.norm_eq_abs]
  calc |c| * ‖iteratedFDeriv ℝ j g x‖ ≤ |c| * (A * (1 + ‖x‖) ^ (P - j)) :=
        mul_le_mul_of_nonneg_left (h j hj x) (abs_nonneg c)
    _ = |c| * A * (1 + ‖x‖) ^ (P - j) := by ring

lemma ul6S_sum {P : ℝ} {m : ℕ} {ι : Type*} (S : Finset ι) (f : ι → Euc d → ℝ) (A : ι → ℝ)
    (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i)) (h : ∀ i ∈ S, ul6S P m (A i) (f i)) :
    ul6S P m (∑ i ∈ S, A i) (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using ul6S_zero P m
  | insert a S ha ih =>
    have h1 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hsm : ContDiff ℝ ∞ (fun x => ∑ i ∈ S, f i x) := ContDiff.sum fun i hi =>
      hf i (Finset.mem_insert_of_mem hi)
    have := ul6S_add (hf a (Finset.mem_insert_self a S)) hsm (h a (Finset.mem_insert_self a S)) h1
    simpa [Finset.sum_insert ha] using this

lemma ul6S_partial {P : ℝ} {m : ℕ} {A : ℝ} {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g) (u : Euc d)
    (h : ul6S P (m + 1) A g) : ul6S (P - 1) m (‖u‖ * A) (fun y => fderiv ℝ g y u) := by
  intro j hj x
  have hL : ‖(ContinuousLinearMap.apply ℝ ℝ u : (Euc d →L[ℝ] ℝ) →L[ℝ] ℝ)‖ ≤ ‖u‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg u) fun f => by
      simpa [mul_comm] using f.le_opNorm u
  have hfd : ContDiff ℝ ∞ (fderiv ℝ g) := (contDiff_infty_iff_fderiv.1 hg).2
  have h1 := (ContinuousLinearMap.apply ℝ ℝ u).norm_iteratedFDeriv_comp_left (f := fderiv ℝ g)
    (x := x) (N := ∞) (n := j) (hfd.contDiffAt) (by exact_mod_cast le_top)
  have e : (fun y => fderiv ℝ g y u) = (ContinuousLinearMap.apply ℝ ℝ u) ∘ (fderiv ℝ g) := rfl
  rw [e]
  refine h1.trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  have h2 := h (j + 1) (by omega) x
  have e2 : (1 + ‖x‖) ^ (P - ((j + 1 : ℕ) : ℝ)) = (1 + ‖x‖) ^ (P - 1 - (j : ℝ)) := by
    congr 1; push_cast; ring
  rw [e2] at h2
  calc _ ≤ ‖u‖ * ‖iteratedFDeriv ℝ (j + 1) g x‖ :=
        mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ ≤ ‖u‖ * (A * (1 + ‖x‖) ^ (P - 1 - (j : ℝ))) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg u)
    _ = ‖u‖ * A * (1 + ‖x‖) ^ (P - 1 - (j : ℝ)) := by ring

lemma ul6S_mul {p q : ℝ} {m : ℕ} {A B : ℝ} {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (h1 : ul6S p m A f) (h2 : ul6S q m B g) :
    ul6S (p + q) m (2 ^ m * (A * B)) (fun x => f x * g x) := by
  intro j hj x
  have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := f) (g := g) (N := (j : ℕ∞ω))
    (hf.of_le (by exact_mod_cast le_top)) (hg.of_le (by exact_mod_cast le_top)) x
    (n := j) le_rfl
  refine hmul.trans ?_
  have hA := ul6S_nonneg h1
  have hB := ul6S_nonneg h2
  have hw := ul6_w_pos' x
  have hterm : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
      ‖iteratedFDeriv ℝ (j - i) g x‖ ≤ (j.choose i : ℝ) * (A * B) * (1 + ‖x‖) ^ (p + q - (j : ℝ)) := by
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e : (1 + ‖x‖) ^ (p + q - (j : ℝ)) =
        (1 + ‖x‖) ^ (p - (i : ℝ)) * (1 + ‖x‖) ^ (q - ((j - i : ℕ) : ℝ)) := by
      rw [← Real.rpow_add hw, Nat.cast_sub hi']; congr 1; ring
    rw [e]
    have a1 := h1 i (hi'.trans hj) x
    have a2 := h2 (j - i) (by omega) x
    calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g x‖
        ≤ (j.choose i : ℝ) * (A * (1 + ‖x‖) ^ (p - (i : ℝ))) *
          (B * (1 + ‖x‖) ^ (q - ((j - i : ℕ) : ℝ))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left a1 (by positivity)) a2 (norm_nonneg _) ?_
          positivity
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hsum : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j := by
    exact_mod_cast Nat.sum_range_choose j
  rw [hsum]
  have h2j : (2 : ℝ) ^ j ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hj
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have hpw : 0 ≤ (1 + ‖x‖) ^ (p + q - (j : ℝ)) := Real.rpow_nonneg hw.le _
  calc 2 ^ j * (A * B) * (1 + ‖x‖) ^ (p + q - (j : ℝ))
      ≤ 2 ^ m * (A * B) * (1 + ‖x‖) ^ (p + q - (j : ℝ)) := by gcongr
    _ = _ := by ring

lemma ul6S_lap {P : ℝ} {m : ℕ} {A : ℝ} {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g)
    (h : ul6S P (m + 2) A g) :
    ul6S (P - 2) m (d * A) (fun x => Laplacian.laplacian g x) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ g) := (contDiff_infty_iff_fderiv.1 hg).2
  have hfun : (fun x => Laplacian.laplacian g x) = fun x => ∑ i : Fin d,
      fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ))) x
        (EuclideanSpace.single i (1 : ℝ)) := by
    funext x
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g
      (EuclideanSpace.basisFun (Fin d) ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply]
    have hd1 : DifferentiableAt ℝ (fderiv ℝ g) x := (hfd.differentiable (by simp)) x
    have := (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).hasFDerivAt.comp x
      hd1.hasFDerivAt
    have e : (fun y => fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ))) =
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))) ∘ (fderiv ℝ g) := rfl
    rw [e, this.fderiv]
    simp
  rw [hfun]
  have hpart : ∀ i : Fin d, ul6S (P - 1 - 1) m (1 * (1 * A))
      (fun x => fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ))) x
        (EuclideanSpace.single i (1 : ℝ))) := by
    intro i
    have h1 : ul6S (P - 1) (m + 1) (1 * A) (fun y => fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ))) := by
      have := ul6S_partial (m := m + 1) hg (EuclideanSpace.single i (1 : ℝ)) h
      simpa using this
    have h1c : ContDiff ℝ ∞ (fun y => fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ))) :=
      hfd.clm_apply contDiff_const
    have := ul6S_partial (m := m) h1c (EuclideanSpace.single i (1 : ℝ)) h1
    simpa using this
  have hs := ul6S_sum (P := P - 1 - 1) (m := m) Finset.univ _ (fun _ => 1 * (1 * A))
    (fun i _ => (hfd.clm_apply contDiff_const).fderiv_right (m := ∞) (by simp) |>.clm_apply contDiff_const)
    (fun i _ => hpart i)
  have e1 : P - 1 - 1 = P - 2 := by ring
  rw [e1] at hs
  simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hs

lemma ul6_sym_to_S {p : ℝ} {g : Euc d → ℝ} (hg : UlSym p g) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ul6S p m A g := by
  choose C hC0 hC using hg.2
  refine ⟨∑ i ∈ Finset.range (m + 1), C i, Finset.sum_nonneg fun i _ => hC0 i, fun j hj x => ?_⟩
  refine (hC j x).trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (ul6_w_pos' x).le _))
  exact Finset.single_le_sum (f := C) (fun i _ => hC0 i) (Finset.mem_range.2 (by omega))

/-! ### Weighted sup bounds of Schwartz functions by `oscNorm` -/

lemma ul6_osc_mono {a b : ℕ} (h : a ≤ b) (f : SchwartzMap (Euc d) ℝ) :
    oscNorm (a : ℝ) f ≤ oscNorm (b : ℝ) f :=
  (HRS.MS.MovOsc.mo_mono (by exact_mod_cast h) (memOsc_schwartz (b : ℝ) f)).2

lemma ul6_proj_norm_le (i : Fin d) : ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    simpa using PiLp.norm_apply_le v i

lemma ul6_lin_iter (i : Fin d) (a : ℝ) (x : Euc d) (hx : x i = a) (l : ℕ) :
    ‖iteratedFDeriv ℝ l (fun y : Euc d => y i - a) x‖ ≤ if l = 1 then 1 else 0 := by
  rcases l with _ | n
  · simp [hx]
  · have hfd : fderiv ℝ (fun y : Euc d => y i - a) = fun _ => (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) := by
      funext y
      have := ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt (x := y)).sub_const a
      exact this.fderiv
    rw [← norm_iteratedFDeriv_fderiv, hfd]
    rcases n with _ | n
    · rw [norm_iteratedFDeriv_zero]
      simpa using ul6_proj_norm_le i
    · rw [iteratedFDeriv_const_of_ne (by omega)]
      simp

lemma ul6_pt_xmul (f : Euc d → ℝ) (hf : ContDiff ℝ ∞ f) (i : Fin d) (j : ℕ) (x : Euc d) :
    |x i| * ‖iteratedFDeriv ℝ j f x‖ ≤ ‖iteratedFDeriv ℝ j (fun y => y i * f y) x‖ +
      j * ‖iteratedFDeriv ℝ (j - 1) f x‖ := by
  set a : ℝ := x i with ha
  have hl : ContDiff ℝ ∞ (fun y : Euc d => y i - a) :=
    ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff).sub contDiff_const
  have h1 : ContDiff ℝ ∞ (fun y : Euc d => (y i - a) * f y) := hl.mul hf
  have h2 : ContDiff ℝ ∞ (fun y : Euc d => a • f y) := hf.const_smul a
  have e : (fun y : Euc d => y i * f y) = (fun y => (y i - a) * f y) + fun y => a • f y := by
    funext y; simp only [Pi.add_apply, smul_eq_mul]; ring
  have hD : iteratedFDeriv ℝ j (fun y => y i * f y) x = iteratedFDeriv ℝ j (fun y => (y i - a) * f y) x +
      a • iteratedFDeriv ℝ j f x := by
    rw [e, iteratedFDeriv_add_apply (ult_cdat h1 j x) (ult_cdat h2 j x),
      iteratedFDeriv_const_smul_apply' (ult_cdat hf j x)]
  have hn : ‖a • iteratedFDeriv ℝ j f x‖ ≤ ‖iteratedFDeriv ℝ j (fun y => y i * f y) x‖ +
      ‖iteratedFDeriv ℝ j (fun y => (y i - a) * f y) x‖ := by
    have : a • iteratedFDeriv ℝ j f x = iteratedFDeriv ℝ j (fun y => y i * f y) x -
        iteratedFDeriv ℝ j (fun y => (y i - a) * f y) x := by rw [hD]; abel
    rw [this]; exact norm_sub_le _ _
  rw [norm_smul, Real.norm_eq_abs] at hn
  refine hn.trans (add_le_add le_rfl ?_)
  have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := fun y : Euc d => y i - a) (g := f)
    (N := (j : ℕ∞ω)) (hl.of_le (by exact_mod_cast le_top)) (hf.of_le (by exact_mod_cast le_top)) x
    (n := j) le_rfl
  refine hmul.trans ?_
  have hterm : ∀ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fun y : Euc d => y i - a) x‖ *
      ‖iteratedFDeriv ℝ (j - l) f x‖ ≤ if l = 1 then (j : ℝ) * ‖iteratedFDeriv ℝ (j - 1) f x‖ else 0 := by
    intro l _
    have hb := ul6_lin_iter i a x rfl l
    by_cases hl1 : l = 1
    · subst hl1
      simp only [ite_true] at hb ⊢
      simp only [Nat.choose_one_right]
      calc (j : ℝ) * ‖iteratedFDeriv ℝ 1 (fun y : Euc d => y i - a) x‖ * ‖iteratedFDeriv ℝ (j - 1) f x‖
          ≤ (j : ℝ) * 1 * ‖iteratedFDeriv ℝ (j - 1) f x‖ := by gcongr
        _ = _ := by ring
    · simp only [hl1, ite_false] at hb ⊢
      have : ‖iteratedFDeriv ℝ l (fun y : Euc d => y i - a) x‖ = 0 := le_antisymm hb (norm_nonneg _)
      rw [this]; simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · exact le_rfl
  · simp at h
    simp [h]

lemma ul6_norm_le_sum (x : Euc d) : ‖x‖ ≤ ∑ i, |x i| := ult_norm_le_sum_abs x

theorem ul6_weighted (N : ℕ) : ∀ j : ℕ, ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧ ∀ (f : SchwartzMap (Euc d) ℝ) (x : Euc d),
    (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ j f x‖ ≤ C * oscNorm (n : ℝ) f := by
  induction N with
  | zero =>
    intro j
    have hlt : (j : ℝ) + (d : ℝ) / 2 < ((⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast; exact Nat.lt_floor_add_one _
    obtain ⟨C, hC0, hC⟩ := HRS.MS.MovOsc.mo_sobolev_emb (d := d) j _ hlt
    refine ⟨C, ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1, hC0, fun f x => ?_⟩
    have := hC f x
    push_cast at this ⊢
    simpa using this
  | succ N ih =>
    intro j
    obtain ⟨C0, n0, hC0, h0⟩ := ih j
    obtain ⟨C1, n1, hC1, h1⟩ := ih (j - 1)
    obtain ⟨Cx, hCx0, hCx⟩ := HRS.MS.MovOsc.mo_xmul (d := d) (n0 : ℝ)
    refine ⟨C0 + d * (C0 * Cx + j * C1), max (n0 + 1) n1, by positivity, fun f x => ?_⟩
    have hw := ul6_w_pos' x
    have hw0 : 0 ≤ (1 + ‖x‖) ^ N := by positivity
    have hf : ContDiff ℝ ∞ (f : Euc d → ℝ) := f.smooth _
    have hxi : ∀ i : Fin d, (1 + ‖x‖) ^ N * (|x i| * ‖iteratedFDeriv ℝ j f x‖) ≤
        C0 * Cx * oscNorm ((max (n0 + 1) n1 : ℕ) : ℝ) f + j * (C1 * oscNorm ((max (n0 + 1) n1 : ℕ) : ℝ) f) := by
      intro i
      have hp := ul6_pt_xmul f hf i j x
      have e1 : (fun y => y i * f y) = ⇑(HRS.MS.MovOsc.mova1_X i f) := funext fun y => by simp
      rw [e1] at hp
      have a1 := h0 (HRS.MS.MovOsc.mova1_X i f) x
      have a2 := h1 f x
      have a3 : oscNorm (n0 : ℝ) ⇑(HRS.MS.MovOsc.mova1_X i f) ≤ Cx * oscNorm ((n0 : ℝ) + 1) f := by
        have := (hCx i f).2
        rwa [e1] at this
      have b1 : oscNorm ((n0 : ℝ) + 1) f ≤ oscNorm ((max (n0 + 1) n1 : ℕ) : ℝ) f := by
        have := ul6_osc_mono (a := n0 + 1) (b := max (n0 + 1) n1) (le_max_left _ _) f
        simpa using this
      have b2 : oscNorm (n1 : ℝ) f ≤ oscNorm ((max (n0 + 1) n1 : ℕ) : ℝ) f :=
        ul6_osc_mono (le_max_right _ _) f
      calc (1 + ‖x‖) ^ N * (|x i| * ‖iteratedFDeriv ℝ j f x‖)
          ≤ (1 + ‖x‖) ^ N * (‖iteratedFDeriv ℝ j (⇑(HRS.MS.MovOsc.mova1_X i f)) x‖ +
              j * ‖iteratedFDeriv ℝ (j - 1) f x‖) := mul_le_mul_of_nonneg_left hp hw0
        _ = (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ j (⇑(HRS.MS.MovOsc.mova1_X i f)) x‖ +
              j * ((1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ (j - 1) f x‖) := by ring
        _ ≤ C0 * oscNorm (n0 : ℝ) ⇑(HRS.MS.MovOsc.mova1_X i f) + j * (C1 * oscNorm (n1 : ℝ) f) := by
            gcongr
        _ ≤ C0 * (Cx * oscNorm ((n0 : ℝ) + 1) f) + j * (C1 * oscNorm (n1 : ℝ) f) := by gcongr
        _ ≤ C0 * (Cx * oscNorm ((max (n0 + 1) n1 : ℕ) : ℝ) f) +
              j * (C1 * oscNorm ((max (n0 + 1) n1 : ℕ) : ℝ) f) := by gcongr
        _ = _ := by ring
    have hsum : (1 + ‖x‖) ^ N * (‖x‖ * ‖iteratedFDeriv ℝ j f x‖) ≤
        ∑ i : Fin d, (C0 * Cx * oscNorm ((max (n0 + 1) n1 : ℕ) : ℝ) f +
          j * (C1 * oscNorm ((max (n0 + 1) n1 : ℕ) : ℝ) f)) := by
      calc (1 + ‖x‖) ^ N * (‖x‖ * ‖iteratedFDeriv ℝ j f x‖)
          ≤ (1 + ‖x‖) ^ N * ((∑ i, |x i|) * ‖iteratedFDeriv ℝ j f x‖) := by
            gcongr; exact ul6_norm_le_sum x
        _ = ∑ i, (1 + ‖x‖) ^ N * (|x i| * ‖iteratedFDeriv ℝ j f x‖) := by
            rw [Finset.sum_mul, Finset.mul_sum]
        _ ≤ _ := Finset.sum_le_sum fun i _ => hxi i
    have hb0 : oscNorm (n0 : ℝ) f ≤ oscNorm ((max (n0 + 1) n1 : ℕ) : ℝ) f :=
      ul6_osc_mono (by omega) f
    have a0 := h0 f x
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    calc (1 + ‖x‖) ^ (N + 1) * ‖iteratedFDeriv ℝ j f x‖
        = (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ j f x‖ + (1 + ‖x‖) ^ N * (‖x‖ * ‖iteratedFDeriv ℝ j f x‖) := by
          ring
      _ ≤ C0 * oscNorm (n0 : ℝ) f + d * (C0 * Cx * oscNorm ((max (n0 + 1) n1 : ℕ) : ℝ) f +
          j * (C1 * oscNorm ((max (n0 + 1) n1 : ℕ) : ℝ) f)) := add_le_add a0 hsum
      _ ≤ C0 * oscNorm ((max (n0 + 1) n1 : ℕ) : ℝ) f + d * (C0 * Cx * oscNorm ((max (n0 + 1) n1 : ℕ) : ℝ) f +
          j * (C1 * oscNorm ((max (n0 + 1) n1 : ℕ) : ℝ) f)) := by gcongr
      _ = _ := by ring

theorem ul6_schwartz_S (s : ℝ) (m : ℕ) : ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧
    ∀ f : SchwartzMap (Euc d) ℝ, ul6S (-(s + 1)) m (C * oscNorm (n : ℝ) f) f := by
  have hj : ∀ j : ℕ, ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧ ∀ (f : SchwartzMap (Euc d) ℝ) (x : Euc d),
      (1 + ‖x‖) ^ (j + ⌈s + 1⌉₊) * ‖iteratedFDeriv ℝ j f x‖ ≤ C * oscNorm (n : ℝ) f :=
    fun j => ul6_weighted (j + ⌈s + 1⌉₊) j
  choose C n hC0 hC using hj
  refine ⟨∑ j ∈ Finset.range (m + 1), C j, ∑ j ∈ Finset.range (m + 1), n j, Finset.sum_nonneg fun j _ => hC0 j,
    fun f j hj x => ?_⟩
  have hjm : j ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
  have hw := ul6_w_pos' x
  have h1 : (1 + ‖x‖) ^ (-(s + 1) - (j : ℝ)) * (1 + ‖x‖) ^ (j + ⌈s + 1⌉₊) ≥ 1 := by
    have hnat : ((j + ⌈s + 1⌉₊ : ℕ) : ℝ) = (j : ℝ) + (⌈s + 1⌉₊ : ℝ) := by push_cast; ring
    rw [← Real.rpow_natCast, hnat, ← Real.rpow_add hw]
    refine Real.one_le_rpow (by linarith [norm_nonneg x]) ?_
    have : s + 1 ≤ (⌈s + 1⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  have h2 : ‖iteratedFDeriv ℝ j f x‖ ≤ C j * oscNorm (n j : ℝ) f * (1 + ‖x‖) ^ (-(s + 1) - (j : ℝ)) := by
    have := hC j f x
    have hp : 0 < (1 + ‖x‖) ^ (j + ⌈s + 1⌉₊) := by positivity
    have hq : 0 ≤ (1 + ‖x‖) ^ (-(s + 1) - (j : ℝ)) := Real.rpow_nonneg hw.le _
    calc ‖iteratedFDeriv ℝ j f x‖ ≤ ‖iteratedFDeriv ℝ j f x‖ *
          ((1 + ‖x‖) ^ (-(s + 1) - (j : ℝ)) * (1 + ‖x‖) ^ (j + ⌈s + 1⌉₊)) := by
          nlinarith [norm_nonneg (iteratedFDeriv ℝ j f x)]
      _ = (1 + ‖x‖) ^ (j + ⌈s + 1⌉₊) * ‖iteratedFDeriv ℝ j f x‖ * (1 + ‖x‖) ^ (-(s + 1) - (j : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this hq
  refine h2.trans ?_
  have hq : 0 ≤ (1 + ‖x‖) ^ (-(s + 1) - (j : ℝ)) := Real.rpow_nonneg hw.le _
  have hosc : oscNorm (n j : ℝ) f ≤ oscNorm ((∑ j ∈ Finset.range (m + 1), n j : ℕ) : ℝ) f :=
    ul6_osc_mono (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) hjm) f
  have hCj : C j ≤ ∑ j ∈ Finset.range (m + 1), C j :=
    Finset.single_le_sum (f := C) (fun _ _ => hC0 _) hjm
  have hC00 : 0 ≤ ∑ j ∈ Finset.range (m + 1), C j := Finset.sum_nonneg fun j _ => hC0 j
  exact mul_le_mul_of_nonneg_right (mul_le_mul hCj hosc (Real.sqrt_nonneg _) hC00) hq

/-! ### The generator on the symbol classes -/

lemma ul6_rapid_S {ρ : Euc d → ℝ} (hρ : UlRapid ρ) (P : ℝ) (m : ℕ) : ∃ R : ℝ, 0 ≤ R ∧ ul6S P m R ρ :=
  ul6_sym_to_S (ult_rapid_sym hρ P) m

/-- the nonlocal term, one component: a symbol bound with explicit constant -/
lemma ul6_nl_S (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) {ρ : Euc d → ℝ}
    (hρ : UlRapid ρ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ) (g : Euc d → ℝ), ContDiff ℝ ∞ g → ul6S (-(s + 1)) (m + 2) A g →
      ∀ j : Fin d, ul6S (-(s + 1)) m (C * A) (fun x => (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ y * (-(fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))))) x) j) := by
  set L : ℝ := (d : ℝ) + m + s + 4 with hL
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hL1 : (d : ℝ) + m + s + 3 < L := by simp only [hL]; linarith
  have hLd : (d : ℝ) < L := by simp only [hL]; linarith
  obtain ⟨R, hR0, hR⟩ := ul6_rapid_S hρ (-L) (m + 1)
  have hcore := fun j : Fin d => ult_core hd (ult_ker_kap hs0 hsd j) m hL1
  choose Cj hCj0 hCj using hcore
  refine ⟨(∑ j, Cj j) * (2 ^ (m + 1) * R), by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hCj0 j
    positivity, fun A g hg hS j => ?_⟩
  set A' : ℝ := 2 ^ (m + 1) * R * A with hA'
  have hA0 : 0 ≤ A := ul6S_nonneg hS
  have hA'0 : 0 ≤ A' := by positivity
  have hfd : ContDiff ℝ ∞ (fderiv ℝ g) := (contDiff_infty_iff_fderiv.1 hg).2
  have hpart : ContDiff ℝ ∞ (fun y => fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) :=
    hfd.clm_apply contDiff_const
  set h : Euc d → ℝ := fun y => ρ y * (-(fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ)))) with hh
  have hhc : ContDiff ℝ ∞ h := hρ.1.mul hpart.neg
  have hnorm : ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ = 1 := by simp
  have hS1 : ul6S (-(s + 1) - 1) (m + 1) (‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ * A)
      (fun y => fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) :=
    ul6S_partial hg _ hS
  have hS2 := ul6S_smul hpart (-1) hS1
  have hS3 := ul6S_mul (f := ρ) (g := fun y => (-1 : ℝ) * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ)))
    hρ.1 (contDiff_const.mul hpart) hR hS2
  have hhe : h = fun y => ρ y * ((-1 : ℝ) * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) := by
    funext y; simp only [hh]; ring
  have hdec : U2Dec (m + 1) L A' h := by
    refine ⟨hhc.of_le (by exact_mod_cast le_top), fun i hi y => ?_⟩
    have h1 := hS3 i hi y
    rw [← hhe] at h1
    have hc1 : 2 ^ (m + 1) * (R * (|(-1 : ℝ)| * (‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ * A))) = A' := by
      simp only [hnorm, hA']; simp; ring
    rw [hc1] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hA'0)
    unfold u2Wt
    refine Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg y]) ?_
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith
  have hfun : (fun x => (convGradConvW (rieszKernelGrad d s) h x) j) = ultK (u2_kap d s j) h :=
    funext fun x => (ult_conv_comp hd hs0 hsd hLd hA'0 (ult_U2Dec_mono hdec (by omega : 1 ≤ m + 1)) x).2 j
  obtain ⟨_, hbd⟩ := hCj j A' h hA'0 hdec
  intro i hi x
  rw [hfun]
  refine (hbd i hi x).trans ?_
  have hex : -(s + 1 + (i : ℝ)) = -(s + 1) - (i : ℝ) := by ring
  rw [hex]
  have hq : 0 ≤ (1 + ‖x‖) ^ (-(s + 1) - (i : ℝ)) := Real.rpow_nonneg (ul6_w_pos' x).le _
  have hCle : Cj j ≤ ∑ j, Cj j :=
    Finset.single_le_sum (f := Cj) (fun j _ => hCj0 j) (Finset.mem_univ j)
  refine mul_le_mul_of_nonneg_right ?_ hq
  calc Cj j * A' = Cj j * (2 ^ (m + 1) * R) * A := by simp only [hA']; ring
    _ ≤ (∑ j, Cj j) * (2 ^ (m + 1) * R) * A := by gcongr

theorem ul6_L_step (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (ν : ℝ)
    (Q : Matrix (Fin d) (Fin d) ℝ) {ρ : Euc d → ℝ} (hρ : UlRapid ρ) {σ : Euc d → Euc d}
    (hσ : ∀ i, UlRapid (fun x => σ x i)) {c : Euc d → Euc d}
    (hc : c = fun x => σ x - convGradConvW (rieszKernelGrad d s) ρ x) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ) (g : Euc d → ℝ), UlSym (-(s + 1)) g → ul6S (-(s + 1)) (m + 2) A g →
      ul6S (-(s + 1)) m (C * A) (fun x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x) := by
  set P : ℝ := -(s + 1) with hP
  have hP0 : P ≤ 0 := by simp only [hP]; linarith
  have hP1 : P ≤ 1 := by linarith
  have hb : ∀ i : Fin d, UlSym 1 (fun x => (-(Torus.matVec Q x) + c x) i) := by
    intro i
    have hL := ult_sym_clm ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Q)))
    have hK := ult_sym_mono hP1 (ult_K_comp_sym hd hs0 hsd hρ i)
    have h3 := ult_sym_add (ult_sym_add (ult_sym_neg hL) (ult_rapid_sym (hσ i) 1))
      (ult_sym_neg hK)
    refine (show (fun x => (-(Torus.matVec Q x) + c x) i) = _ from ?_) ▸ h3
    funext x
    subst hc
    simp [Torus.matVec]
    ring
  choose Bi hBi0 hBi using fun i => ul6_sym_to_S (hb i) m
  obtain ⟨CN, hCN0, hCN⟩ := ul6_nl_S hd hs0 hsd hρ m
  have hBs : 0 ≤ ∑ i, Bi i := Finset.sum_nonneg fun i _ => hBi0 i
  refine ⟨|ν| * d + 2 ^ m * ∑ i, Bi i + d * CN, by positivity, fun A g hsym hS => ?_⟩
  have hA0 := ul6S_nonneg hS
  have hg : ContDiff ℝ ∞ g := hsym.1
  have hfd : ContDiff ℝ ∞ (fderiv ℝ g) := (contDiff_infty_iff_fderiv.1 hg).2
  have hlapS := ul6S_lap (m := m) hg hS
  have hlapC : ContDiff ℝ ∞ (fun x => Laplacian.laplacian g x) := (ult_lap_sym hsym).1
  -- T1
  have T1 : ul6S P m (|ν| * (d * A)) (fun x => ν * Laplacian.laplacian g x) :=
    ul6S_mono_P (by linarith) (ul6S_smul hlapC ν hlapS)
  -- T2
  have T2i : ∀ i : Fin d, ul6S P m (2 ^ m * (Bi i * (‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ * A)))
      (fun x => (-(Torus.matVec Q x) + c x) i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) := by
    intro i
    have hp := ul6S_mono_m (m' := m) (by omega) (ul6S_partial (m := m + 1) hg
      (EuclideanSpace.single i (1 : ℝ)) hS)
    have hm := ul6S_mul (hb i).1 (hfd.clm_apply contDiff_const) (hBi i) hp
    have e1 : (1 : ℝ) + (P - 1) = P := by ring
    rw [e1] at hm
    exact hm
  have T2c : ∀ i : Fin d, ContDiff ℝ ∞
      (fun x => (-(Torus.matVec Q x) + c x) i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) :=
    fun i => (hb i).1.mul (hfd.clm_apply contDiff_const)
  have T2 := ul6S_sum (P := P) (m := m) Finset.univ _ _ (fun i _ => T2c i) (fun i _ => T2i i)
  -- T3
  have T3i : ∀ j : Fin d, ul6S P m (CN * A) (fun x => (convGradConvW (rieszKernelGrad d s)
      (fun y => ρ y * (-(fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))))) x) j) :=
    fun j => hCN A g hg hS j
  have T3c : ∀ j : Fin d, ContDiff ℝ ∞ (fun x => (convGradConvW (rieszKernelGrad d s)
      (fun y => ρ y * (-(fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))))) x) j) := by
    intro j
    refine (ult_K_comp_sym hd hs0 hsd (ult_sym_rapid fun q => ?_) j).1
    have h1 := ult_sym_mul (ult_rapid_sym hρ (q - (P - 1)))
      (ult_sym_neg (ult_sym_partial (EuclideanSpace.single j (1 : ℝ)) hsym))
    have e1 : q - (P - 1) + (P - 1) = q := by ring
    rw [e1] at h1
    exact h1
  have T3 := ul6S_sum (P := P) (m := m) Finset.univ _ _ (fun j _ => T3c j) (fun j _ => T3i j)
  have T3' := ul6S_smul (ContDiff.sum fun j _ => T3c j) (-1) T3
  have hT1c : ContDiff ℝ ∞ (fun x => ν * Laplacian.laplacian g x) := contDiff_const.mul hlapC
  have hT2c : ContDiff ℝ ∞ (fun x => ∑ i : Fin d,
      (-(Torus.matVec Q x) + c x) i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) :=
    ContDiff.sum fun i _ => T2c i
  have hT3c : ContDiff ℝ ∞ (fun x => ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
      (fun y => ρ y * (-(fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))))) x) j) :=
    ContDiff.sum fun j _ => T3c j
  have hT12 := ul6S_add hT1c hT2c T1 T2
  have hfin := ul6S_add (hT1c.add hT2c) (contDiff_const.mul hT3c) hT12 T3'
  have e : (fun x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x) = fun x =>
      (ν * Laplacian.laplacian g x + ∑ i : Fin d, (-(Torus.matVec Q x) + c x) i *
        fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) +
      (-1) * ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ y * (-(fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))))) x) j := by
    funext x
    rw [ult_gen_eq]; ring
  rw [e]
  have hnormE : ∀ i : Fin d, ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := fun i => by simp
  refine ul6S_mono_A ?_ hfin
  simp only [hnormE, norm_one, one_mul, abs_neg, abs_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h1 : ∑ i : Fin d, 2 ^ m * (Bi i * A) = 2 ^ m * (∑ i, Bi i) * A := by
    rw [← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]
  rw [h1]
  exact le_of_eq (by ring)

/-! ### The orbit data: linear bounds in `oscNorm` -/

theorem ul6_orbit_S (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (a : ℕ) :
    ∀ m : ℕ, ∃ n : ℕ, ∀ (ν : ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ)
      (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ) (σ : Euc d → Euc d)
      (hσ : ∀ i, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = fun x => σ x i) (c : Euc d → Euc d)
      (hc : c = fun x => σ x - convGradConvW (rieszKernelGrad d s) ρ x),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SchwartzMap (Euc d) ℝ,
        ul6S (-(s + 1)) m (C * oscNorm (n : ℝ) f)
          ((fun g x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x)^[a] ⇑f) := by
  induction a with
  | zero =>
    intro m
    obtain ⟨C, n, hC0, hC⟩ := ul6_schwartz_S (d := d) s m
    exact ⟨n, fun ν Q ρ hρ σ hσ c hc => ⟨C, hC0, fun f => by simpa using hC f⟩⟩
  | succ a ih =>
    intro m
    obtain ⟨n, hn⟩ := ih (m + 2)
    refine ⟨n, fun ν Q ρ hρ σ hσ c hc => ?_⟩
    obtain ⟨C1, hC10, hC1⟩ := hn ν Q ρ hρ σ hσ c hc
    obtain ⟨ψ, hψ⟩ := hρ
    have hρr : UlRapid ρ := by rw [← hψ]; exact ult_schwartz_rapid ψ
    choose φ hφ using hσ
    have hσr : ∀ i, UlRapid (fun x => σ x i) := fun i => by rw [← hφ i]; exact ult_schwartz_rapid (φ i)
    obtain ⟨C2, hC20, hC2⟩ := ul6_L_step (by omega) hs0 hsd ν Q hρr hσr hc m
    refine ⟨C2 * C1, by positivity, fun f => ?_⟩
    rw [Function.iterate_succ_apply']
    obtain ⟨hcd, hdec, _⟩ := orbitData_decay hd hs0 hsd ν Q ρ ⟨ψ, hψ⟩ σ (fun i => ⟨φ i, hφ i⟩) c hc f a
    have hsym : UlSym (-(s + 1)) ((fun g x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x)^[a] ⇑f) :=
      ⟨hcd, fun m' => by
        obtain ⟨C, hC0, hC⟩ := hdec m'
        refine ⟨C, hC0, fun x => ?_⟩
        rw [show -(s + 1) - (m' : ℝ) = -(s + 1 + (m' : ℝ)) by ring]
        exact hC x⟩
    have := hC2 _ _ hsym (hC1 f)
    have e : C2 * (C1 * oscNorm (n : ℝ) f) = C2 * C1 * oscNorm (n : ℝ) f := by ring
    rw [e] at this
    exact this

theorem ul6_ul_of_S {θ : Euc d → ℝ} (hθ : IsUlCutoff θ) (K : ℕ) :
    ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ (P A : ℝ) (g : Euc d → ℝ), P ≤ 0 → ContDiff ℝ ∞ g → ul6S P K A g →
      ulNormE K θ g ≤ ENNReal.ofReal (Cu * A) := by
  obtain ⟨χ, hχ⟩ := ul0_exists_ulocCutoff d
  obtain ⟨Ce, hCe, hequ⟩ := ul_equiv K θ χ hθ hχ
  obtain ⟨Cc, hCc, hcb⟩ := ulocNormE_le_cb K χ hχ
  refine ⟨Ce * (Cc * (K + 1)), by positivity, fun P A g hP hg hS => ?_⟩
  have hA0 := ul6S_nonneg hS
  have hb : ∀ j ≤ K, ∀ x : Euc d, ‖iteratedFDeriv ℝ j g x‖ ≤ A := by
    intro j hj x
    refine (hS j hj x).trans ?_
    have : (1 + ‖x‖) ^ (P - j) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
      (by linarith [norm_nonneg x]) (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
    nlinarith
  have hmem : HRS.MemCb K g := ⟨hg.of_le (by exact_mod_cast le_top), fun j hj =>
    ⟨A, by rintro _ ⟨x, rfl⟩; exact hb j hj x⟩⟩
  have hcb' : HRS.cbNorm K g ≤ (K + 1) * A := by
    unfold HRS.cbNorm
    calc ∑ j ∈ Finset.range (K + 1), ⨆ x, ‖iteratedFDeriv ℝ j g x‖
        ≤ ∑ j ∈ Finset.range (K + 1), A :=
          Finset.sum_le_sum fun j hj => ciSup_le fun x => hb j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) x
      _ = _ := by simp
  have h1 := hcb g hmem
  calc ulNormE K θ g ≤ ENNReal.ofReal Ce * ulocNormE K χ g := (hequ g).1
    _ ≤ ENNReal.ofReal Ce * ENNReal.ofReal (Cc * HRS.cbNorm K g) := by gcongr
    _ = ENNReal.ofReal (Ce * (Cc * HRS.cbNorm K g)) := by rw [ENNReal.ofReal_mul hCe.le]
    _ ≤ ENNReal.ofReal (Ce * (Cc * (K + 1)) * A) := by
        apply ENNReal.ofReal_le_ofReal
        have : Ce * (Cc * HRS.cbNorm K g) ≤ Ce * (Cc * ((K + 1) * A)) := by gcongr
        calc Ce * (Cc * HRS.cbNorm K g) ≤ Ce * (Cc * ((K + 1) * A)) := this
          _ = _ := by ring

/-- **The orbit data `L^a f`, `a ≤ 3`, in `H^K_ul`:** `J` depends on `d, s, K` only. -/
theorem ul6_orbit_ul (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) {θ : Euc d → ℝ}
    (hθ : IsUlCutoff θ) (K : ℕ) :
    ∃ J : ℕ, ∀ (ν : ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ)
      (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ) (σ : Euc d → Euc d)
      (hσ : ∀ i, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = fun x => σ x i) (c : Euc d → Euc d)
      (hc : c = fun x => σ x - convGradConvW (rieszKernelGrad d s) ρ x),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : SchwartzMap (Euc d) ℝ) (a : ℕ), a ≤ 3 →
        ulNormE K θ ((fun g x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x)^[a] ⇑f) ≤
          ENNReal.ofReal (C * oscNorm (J : ℝ) f) := by
  choose n hn using fun a : Fin 4 => ul6_orbit_S hd hs0 hsd (a : ℕ) K
  obtain ⟨Cu, hCu0, hCu⟩ := ul6_ul_of_S hθ K
  refine ⟨Finset.univ.sup n, fun ν Q ρ hρ σ hσ c hc => ?_⟩
  have h4 : ∀ a : Fin 4, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SchwartzMap (Euc d) ℝ,
      ul6S (-(s + 1)) K (C * oscNorm (n a : ℝ) f)
        ((fun g x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x)^[(a : ℕ)] ⇑f) :=
    fun a => hn a ν Q ρ hρ σ hσ c hc
  choose C hC0 hC using h4
  obtain ⟨ψ, hψ⟩ := hρ
  choose φ hφ using hσ
  refine ⟨Cu * ∑ a : Fin 4, C a, mul_nonneg hCu0 (Finset.sum_nonneg fun a _ => hC0 a), fun f a ha => ?_⟩
  set a' : Fin 4 := ⟨a, by omega⟩ with ha'
  have hcd : ContDiff ℝ ∞ ((fun g x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x)^[a] ⇑f) :=
    (orbitData_decay hd hs0 hsd ν Q ρ ⟨ψ, hψ⟩ σ (fun i => ⟨φ i, hφ i⟩) c hc f a).1
  have h1 := hCu (-(s + 1)) _ _ (by linarith) hcd (hC a' f)
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  have hosc : oscNorm (n a' : ℝ) f ≤ oscNorm ((Finset.univ.sup n : ℕ) : ℝ) f :=
    ul6_osc_mono (Finset.le_sup (f := n) (Finset.mem_univ a')) f
  have ho0 : 0 ≤ oscNorm ((Finset.univ.sup n : ℕ) : ℝ) f := Real.sqrt_nonneg _
  have hCa : C a' ≤ ∑ a : Fin 4, C a :=
    Finset.single_le_sum (f := C) (fun a _ => hC0 a) (Finset.mem_univ a')
  have hsum0 : 0 ≤ ∑ a : Fin 4, C a := Finset.sum_nonneg fun a _ => hC0 a
  have ho1 : 0 ≤ oscNorm (n a' : ℝ) f := Real.sqrt_nonneg _
  calc Cu * (C a' * oscNorm (n a' : ℝ) f) ≤ Cu * ((∑ a : Fin 4, C a) * oscNorm ((Finset.univ.sup n : ℕ) : ℝ) f) := by
        gcongr
    _ = _ := by ring

end HRS.MS.Ul
