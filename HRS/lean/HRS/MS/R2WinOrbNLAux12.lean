import HRS.MS.R2WinOrbNLAux11

/-!
# S10.3 (nonlinear branch), part 12: the classes `SyN p` (decay `(1+‖x‖)^{-p}`) and the generator maps decaying-gradient functions to `Sy`

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.  `SyN p N A f`: `f ∈ C^N` and `‖D^j f(x)‖ (1+‖x‖)^p ≤ A` for `j ≤ N` (natural `p`).
`s103n_Lt_sy`: if every partial derivative `∂_i g` lies in `SyN 2 (N+1) A` (and `g ∈ C^{N+2}`), then `L_h g ∈ Sy N ((C₀+C₁ A_h) A)` for a density `h` with
`U2Dec (N+1) L A_h h`: the transport term `x·∇g` has the decay `(1+‖x‖)^{-1}`, the others are as in `s103n_Lt_bd`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.BreakdownS67 HRS.MS.MovLin HRS.MS.MovAdj HRS.MS.MovOsc HRS.MS.Ul HRS.MS.Who

variable {d : ℕ}

/-- Jets up to order `N` decaying like `(1+‖x‖)^{-p}`. -/
def SyN (p N : ℕ) (A : ℝ) (f : Euc d → ℝ) : Prop :=
  ContDiff ℝ (N : WithTop ℕ∞) f ∧ ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j f x‖ * (1 + ‖x‖) ^ p ≤ A

theorem SyN.bd {p N : ℕ} {A : ℝ} {f : Euc d → ℝ} (h : SyN p N A f) : Bd N A f := by
  refine ⟨h.1, fun j hj x => ?_⟩
  have h1 : 1 ≤ (1 + ‖x‖) ^ p := one_le_pow₀ (by linarith [norm_nonneg x])
  calc ‖iteratedFDeriv ℝ j f x‖ ≤ ‖iteratedFDeriv ℝ j f x‖ * (1 + ‖x‖) ^ p := by
        nlinarith [norm_nonneg (iteratedFDeriv ℝ j f x)]
    _ ≤ A := h.2 j hj x

theorem SyN.mono_p {p q N : ℕ} (hpq : q ≤ p) {A : ℝ} {f : Euc d → ℝ} (h : SyN p N A f) : SyN q N A f := by
  refine ⟨h.1, fun j hj x => ?_⟩
  have h1 : (1 + ‖x‖) ^ q ≤ (1 + ‖x‖) ^ p := pow_le_pow_right₀ (by linarith [norm_nonneg x]) hpq
  exact (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans (h.2 j hj x)

theorem SyN.mono_N {p N N' : ℕ} (hN : N' ≤ N) {A : ℝ} {f : Euc d → ℝ} (h : SyN p N A f) : SyN p N' A f :=
  ⟨h.1.of_le (by exact_mod_cast hN), fun j hj x => h.2 j (hj.trans hN) x⟩

theorem SyN.mono_A {p N : ℕ} {A A' : ℝ} (hA : A ≤ A') {f : Euc d → ℝ} (h : SyN p N A f) :
    SyN p N A' f := ⟨h.1, fun j hj x => (h.2 j hj x).trans hA⟩

theorem SyN.zero (p N : ℕ) : SyN p N 0 (fun _ : Euc d => (0 : ℝ)) := by
  refine ⟨contDiff_const, fun j _ x => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · rw [iteratedFDeriv_const_of_ne hj.ne']; simp

theorem SyN.add {p N : ℕ} {A B : ℝ} {f g : Euc d → ℝ} (hf : SyN p N A f) (hg : SyN p N B g) :
    SyN p N (A + B) (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, fun j hj x => ?_⟩
  have e : (fun x => f x + g x) = f + g := rfl
  rw [e, iteratedFDeriv_add_apply (hf.1.of_le (by exact_mod_cast hj)).contDiffAt
    (hg.1.of_le (by exact_mod_cast hj)).contDiffAt]
  have hp : 0 ≤ (1 + ‖x‖) ^ p := by positivity
  calc ‖iteratedFDeriv ℝ j f x + iteratedFDeriv ℝ j g x‖ * (1 + ‖x‖) ^ p ≤
      (‖iteratedFDeriv ℝ j f x‖ + ‖iteratedFDeriv ℝ j g x‖) * (1 + ‖x‖) ^ p :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) hp
    _ = ‖iteratedFDeriv ℝ j f x‖ * (1 + ‖x‖) ^ p + ‖iteratedFDeriv ℝ j g x‖ * (1 + ‖x‖) ^ p := by ring
    _ ≤ A + B := add_le_add (hf.2 j hj x) (hg.2 j hj x)

theorem SyN.smul {p N : ℕ} {A : ℝ} {f : Euc d → ℝ} (hf : SyN p N A f) (c : ℝ) :
    SyN p N (|c| * A) (fun x => c * f x) := by
  refine ⟨contDiff_const.mul hf.1, fun j hj x => ?_⟩
  have e : (fun x => c * f x) = c • f := by funext x; simp
  rw [e, iteratedFDeriv_const_smul_apply (hf.1.of_le (by exact_mod_cast hj)).contDiffAt, norm_smul,
    Real.norm_eq_abs]
  calc |c| * ‖iteratedFDeriv ℝ j f x‖ * (1 + ‖x‖) ^ p =
      |c| * (‖iteratedFDeriv ℝ j f x‖ * (1 + ‖x‖) ^ p) := by ring
    _ ≤ |c| * A := mul_le_mul_of_nonneg_left (hf.2 j hj x) (abs_nonneg _)

theorem SyN.sum {p N : ℕ} {ι : Type*} (S : Finset ι) (f : ι → Euc d → ℝ) (A : ι → ℝ)
    (h : ∀ i ∈ S, SyN p N (A i) (f i)) : SyN p N (∑ i ∈ S, A i) (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using SyN.zero (d := d) p N
  | insert a S ha ih =>
    have h1 := h a (Finset.mem_insert_self _ _)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have := h1.add h2
    simp only [Finset.sum_insert ha]
    exact this

theorem SyN.mul_bd {p N : ℕ} {A B : ℝ} {f g : Euc d → ℝ} (hf : SyN p N A f) (hg : Bd N B g) :
    SyN p N (2 ^ N * A * B) (fun x => f x * g x) := by
  have hA : 0 ≤ A := hf.bd.nonneg
  have hB := hg.nonneg
  refine ⟨hf.1.mul hg.1, fun j hj x => ?_⟩
  refine (mul_le_mul_of_nonneg_right (norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := f) (g := g)
    (N := (N : ℕ∞ω)) hf.1 hg.1 x (n := j) (by exact_mod_cast hj)) (by positivity)).trans ?_
  have hp : 0 ≤ (1 + ‖x‖) ^ p := by positivity
  have hterm : ∀ l ∈ Finset.range (j + 1),
      (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l f x‖ * ‖iteratedFDeriv ℝ (j - l) g x‖ * (1 + ‖x‖) ^ p ≤
        (j.choose l : ℝ) * (A * B) := by
    intro l hl
    have hl' : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have h1 := hf.2 l (by omega) x
    have h2 := hg.2 (j - l) (by omega) x
    calc (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l f x‖ * ‖iteratedFDeriv ℝ (j - l) g x‖ * (1 + ‖x‖) ^ p =
        (j.choose l : ℝ) * ((‖iteratedFDeriv ℝ l f x‖ * (1 + ‖x‖) ^ p) *
          ‖iteratedFDeriv ℝ (j - l) g x‖) := by ring
      _ ≤ (j.choose l : ℝ) * (A * B) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul h1 h2 (norm_nonneg _) hA
  calc (∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l f x‖ *
        ‖iteratedFDeriv ℝ (j - l) g x‖) * (1 + ‖x‖) ^ p
      = ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l f x‖ *
        ‖iteratedFDeriv ℝ (j - l) g x‖ * (1 + ‖x‖) ^ p := by rw [Finset.sum_mul]
    _ ≤ ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * (A * B) := Finset.sum_le_sum hterm
    _ = (2 : ℝ) ^ j * (A * B) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose j
    _ ≤ (2 : ℝ) ^ N * (A * B) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) (mul_nonneg hA hB)
    _ = _ := by ring

theorem SyN.deriv {p N : ℕ} {A : ℝ} {f : Euc d → ℝ} (hf : SyN p (N + 1) A f) (v : Euc d) :
    SyN p N (A * ‖v‖) (fun y => fderiv ℝ f y v) := by
  have hd1 : ContDiff ℝ (N : WithTop ℕ∞) (fderiv ℝ f) :=
    hf.1.fderiv_right (by exact_mod_cast le_refl (N + 1))
  refine ⟨hd1.clm_apply contDiff_const, fun m hm y => ?_⟩
  have h1 := norm_iteratedFDeriv_clm_apply_const (N := (N : WithTop ℕ∞)) (c := v) (n := m)
    hd1.contDiffAt (by exact_mod_cast hm) (x := y)
  rw [norm_iteratedFDeriv_fderiv] at h1
  have h2 := hf.2 (m + 1) (by omega) y
  calc ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ f y v) y‖ * (1 + ‖y‖) ^ p ≤
      (‖v‖ * ‖iteratedFDeriv ℝ (m + 1) f y‖) * (1 + ‖y‖) ^ p :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ‖v‖ * (‖iteratedFDeriv ℝ (m + 1) f y‖ * (1 + ‖y‖) ^ p) := by ring
    _ ≤ ‖v‖ * A := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = A * ‖v‖ := by ring

theorem SyN.xmul {p N : ℕ} {A : ℝ} {f : Euc d → ℝ} (hf : SyN (p + 1) N A f) (i : Fin d) :
    SyN p N ((N + 1) * A) (fun x => x i * f x) := by
  have hA : 0 ≤ A := hf.bd.nonneg
  have hc : ContDiff ℝ (N : WithTop ℕ∞) (fun y : Euc d => y i) :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff
  refine ⟨hc.mul hf.1, fun j hj x => ?_⟩
  refine (mul_le_mul_of_nonneg_right (norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := fun y : Euc d => y i)
    (g := f) (N := (N : ℕ∞ω)) hc hf.1 x (n := j) (by exact_mod_cast hj)) (by positivity)).trans ?_
  have hp1 : 0 < (1 + ‖x‖) ^ (p + 1) := by positivity
  have hp : 0 ≤ (1 + ‖x‖) ^ p := by positivity
  -- ‖x‖ (1+‖x‖)^p ≤ (1+‖x‖)^{p+1}
  have hx : ‖x‖ * (1 + ‖x‖) ^ p ≤ (1 + ‖x‖) ^ (p + 1) := by
    rw [pow_succ]; nlinarith [norm_nonneg x]
  have hx2 : (1 + ‖x‖) ^ p ≤ (1 + ‖x‖) ^ (p + 1) := pow_le_pow_right₀ (by linarith [norm_nonneg x]) (by omega)
  have hterm : ∀ l ∈ Finset.range (j + 1),
      (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fun y : Euc d => y i) x‖ * ‖iteratedFDeriv ℝ (j - l) f x‖ *
        (1 + ‖x‖) ^ p ≤ (if l = 0 then A else 0) + (if l = 1 then (j : ℝ) * A else 0) := by
    intro l hl
    have hl' : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hfj := hf.2 (j - l) (by omega) x
    have hc' := s103n_coord_iter i x l
    by_cases h0 : l = 0
    · subst h0
      simp only [if_true, Nat.zero_ne_one, if_false, add_zero, Nat.choose_zero_right, Nat.cast_one,
        one_mul, tsub_zero] at hc' hfj ⊢
      calc ‖iteratedFDeriv ℝ 0 (fun y : Euc d => y i) x‖ * ‖iteratedFDeriv ℝ j f x‖ * (1 + ‖x‖) ^ p
          ≤ ‖x‖ * ‖iteratedFDeriv ℝ j f x‖ * (1 + ‖x‖) ^ p := by
            gcongr
        _ = (‖x‖ * (1 + ‖x‖) ^ p) * ‖iteratedFDeriv ℝ j f x‖ := by ring
        _ ≤ (1 + ‖x‖) ^ (p + 1) * ‖iteratedFDeriv ℝ j f x‖ :=
            mul_le_mul_of_nonneg_right hx (norm_nonneg _)
        _ = ‖iteratedFDeriv ℝ j f x‖ * (1 + ‖x‖) ^ (p + 1) := by ring
        _ ≤ A := hfj
    · by_cases h1 : l = 1
      · subst h1
        simp only [one_ne_zero, if_false, zero_add, if_true, Nat.choose_one_right] at hc' ⊢
        calc (j : ℝ) * ‖iteratedFDeriv ℝ 1 (fun y : Euc d => y i) x‖ * ‖iteratedFDeriv ℝ (j - 1) f x‖ *
            (1 + ‖x‖) ^ p ≤ (j : ℝ) * 1 * ‖iteratedFDeriv ℝ (j - 1) f x‖ * (1 + ‖x‖) ^ p := by
              gcongr
          _ = (j : ℝ) * (‖iteratedFDeriv ℝ (j - 1) f x‖ * (1 + ‖x‖) ^ p) := by ring
          _ ≤ (j : ℝ) * (‖iteratedFDeriv ℝ (j - 1) f x‖ * (1 + ‖x‖) ^ (p + 1)) := by
              gcongr
          _ ≤ (j : ℝ) * A := mul_le_mul_of_nonneg_left hfj (Nat.cast_nonneg _)
      · simp only [h0, h1, if_false, add_zero] at hc' ⊢
        have : ‖iteratedFDeriv ℝ l (fun y : Euc d => y i) x‖ = 0 := le_antisymm hc' (norm_nonneg _)
        rw [this]; simp
  calc (∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fun y : Euc d => y i) x‖ *
        ‖iteratedFDeriv ℝ (j - l) f x‖) * (1 + ‖x‖) ^ p
      = ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fun y : Euc d => y i) x‖ *
        ‖iteratedFDeriv ℝ (j - l) f x‖ * (1 + ‖x‖) ^ p := by rw [Finset.sum_mul]
    _ ≤ ∑ l ∈ Finset.range (j + 1), ((if l = 0 then A else 0) + (if l = 1 then (j : ℝ) * A else 0)) :=
        Finset.sum_le_sum hterm
    _ ≤ (N + 1) * A := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
        simp only [Finset.mem_range, Nat.succ_pos, if_true]
        by_cases hj1 : 1 ≤ j
        · simp only [Nat.lt_succ_iff, hj1, if_true]
          have : (j : ℝ) ≤ N := by exact_mod_cast hj
          nlinarith
        · simp only [Nat.lt_succ_iff, hj1, if_false]
          nlinarith

theorem Sy.toSyN {N : ℕ} {A : ℝ} {f : Euc d → ℝ} (h : Sy N A f) : SyN 1 N A f := by
  refine ⟨h.1, fun j hj x => ?_⟩
  have hx : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
  calc ‖iteratedFDeriv ℝ j f x‖ * (1 + ‖x‖) ^ 1 ≤ A * (1 + ‖x‖)⁻¹ * (1 + ‖x‖) ^ 1 :=
        mul_le_mul_of_nonneg_right (h.2 j hj x) (by positivity)
    _ = A := by rw [pow_one]; field_simp

theorem SyN.toSy {N : ℕ} {A : ℝ} {f : Euc d → ℝ} (h : SyN 1 N A f) : Sy N A f := by
  refine ⟨h.1, fun j hj x => ?_⟩
  have hx : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
  have := h.2 j hj x
  rw [pow_one] at this
  rw [← div_eq_mul_inv, le_div_iff₀ hx]
  exact this

set_option maxHeartbeats 3200000 in
theorem s103n_Lt_sy {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (a β : ℝ) (N : ℕ) {L : ℝ}
    (hL : (d : ℝ) + N + s + 3 < L) :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ ∀ (Ah : ℝ) (h : Euc d → ℝ), 0 ≤ Ah → U2Dec (N + 1) L Ah h →
      ∀ (A : ℝ) (g : Euc d → ℝ), ContDiff ℝ ((N + 2 : ℕ) : WithTop ℕ∞) g →
        (∀ i : Fin d, SyN 2 (N + 1) A (fun y => fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ)))) →
        Sy N ((C0 + C1 * Ah) * A)
          (fun x => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => h)) 0 g x) := by
  obtain ⟨Cf, hCf0, hCf⟩ := s103n_force_sy hd hs0 hsd N hL
  refine ⟨|β⁻¹| * (d * 1) + d * (|a| * (N + 1)), d * 2 ^ N * Cf + d * (Cf * 2 ^ (N + 1)),
    by positivity, by positivity, fun Ah h hAh hdec A g hgc hDS => ?_⟩
  have hA : 0 ≤ A := (hDS ⟨0, by omega⟩).bd.nonneg
  have hn : ∀ i : Fin d, ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := fun i => by simp
  have hDg : ∀ i : Fin d, Bd (N + 1) A (fun y => fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ))) :=
    fun i => (hDS i).bd
  -- the four terms, all in `SyN 1 N`
  have T1 : SyN 1 N (∑ i : Fin d, A * 1)
      (fun x => ∑ i : Fin d, fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ))) x
        (EuclideanSpace.single i (1 : ℝ))) :=
    SyN.sum Finset.univ _ _ (fun i _ => by
      have := ((hDS i).deriv (EuclideanSpace.single i (1 : ℝ))).mono_p (p := 2) (q := 1) (by norm_num)
      rw [hn i] at this
      exact this)
  have T1' : SyN 1 N (|β⁻¹| * ∑ i : Fin d, A * 1)
      (fun x => β⁻¹ * ∑ i : Fin d, fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ))) x
        (EuclideanSpace.single i (1 : ℝ))) := T1.smul β⁻¹
  have T2 : SyN 1 N (∑ i : Fin d, |(-a)| * ((N + 1) * A))
      (fun x => ∑ i : Fin d, (-a) * (x i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ)))) :=
    SyN.sum Finset.univ _ _ (fun i _ => ((hDS i).mono_N (Nat.le_succ N)).xmul i |>.smul (-a))
  have hFS : ∀ i : Fin d, SyN 1 N (Cf * Ah) (fun x => movForce d s h x i) :=
    fun i => (hCf Ah h hAh hdec i).toSyN
  have T3 : SyN 1 N (∑ i : Fin d, |(-1 : ℝ)| * (2 ^ N * (Cf * Ah) * A))
      (fun x => ∑ i : Fin d, (-1 : ℝ) * (movForce d s h x i *
        fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ)))) :=
    SyN.sum Finset.univ _ _ (fun i _ => ((hFS i).mul_bd ((hDg i).mono_N (Nat.le_succ N))).smul (-1))
  have hhj : ∀ j : Fin d, U2Dec (N + 1) L (Ah * A * 2 ^ (N + 1))
      (fun y => h y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) := fun j =>
    who_u2dec_mul hdec (hDg j).1 (fun i hi y => (hDg j).2 i hi y)
  have T4 : SyN 1 N (∑ j : Fin d, Cf * (Ah * A * 2 ^ (N + 1)))
      (fun x => ∑ j : Fin d, movForce d s (fun y => h y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) x j) :=
    SyN.sum Finset.univ _ _ (fun j _ => (hCf _ _ (by positivity) (hhj j) j).toSyN)
  have hsum := (T1'.add (T2.add T3)).add T4
  have hfun : (fun x => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => h)) 0 g x) =
      fun x => (β⁻¹ * ∑ i : Fin d, fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ))) x
          (EuclideanSpace.single i (1 : ℝ)) + (∑ i : Fin d, (-a) * (x i *
        fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) + ∑ i : Fin d, (-1 : ℝ) * (movForce d s h x i *
        fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))))) +
        ∑ j : Fin d, movForce d s (fun y => h y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) x j := by
    funext x
    rw [s67_gen_eq s a β h 0 g x, s67bd26_inner, s103n_lap_eq (hgc.of_le (by exact_mod_cast
      (by omega : 2 ≤ N + 2)))]
    have hJ : s67J d s h g x = ∑ j : Fin d, movForce d s
        (fun y => h y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) x j := by
      unfold s67J
      refine Finset.sum_congr rfl fun j _ => ?_
      have hg' : (fun y => h y * gradient g y j) =
          fun y => h y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ)) :=
        funext fun y => by rw [mov2d_grad_coord]
      show (movForce d s (fun y => h y * gradient g y j) x) j = _
      rw [hg']
    rw [hJ, ← Finset.sum_add_distrib]
    have e : ∀ i : Fin d, (-(a • x) - movForce d s h x) i * gradient g x i =
        (-a) * (x i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) +
          (-1 : ℝ) * (movForce d s h x i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) := by
      intro i
      rw [mov2d_grad_coord]
      simp only [PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    simp only [e]
  rw [hfun]
  refine SyN.toSy (hsum.mono_A ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, abs_neg, abs_one]
  nlinarith [mul_nonneg hA hAh, mul_nonneg (mul_nonneg hA hAh) hCf0]

end HRS.MS.R2WinOrbNL

end
