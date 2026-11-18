import HRS.PDE.EnergyAux

/-!
# Multiplication by bounded functions on finitely supported coefficient sequences

`boxFin`, `trigFun`, the pairing identity `pairing_eq_integral` (Fourier coefficients of a product
tested against a trigonometric polynomial), Parseval for trigonometric polynomials, and the
`ℓ²` bound `l2_mul_le` for multiplication by a bounded continuous function.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-- The box `{k : |k|_∞ ≤ n}` as a finset. -/
def boxFin (d n : ℕ) : Finset (Lattice d) := Fintype.piFinset fun _ => Finset.Icc (-(n : ℤ)) n

theorem mem_boxFin {n : ℕ} {k : Lattice d} : k ∈ boxFin d n ↔ InBox n k := by
  simp only [boxFin, Fintype.mem_piFinset, Finset.mem_Icc, InBox, abs_le]

theorem eq_zero_of_isTrigPoly {n : ℕ} {c : Coeff d} (hc : IsTrigPoly n c) {k : Lattice d}
    (hk : k ∉ boxFin d n) : c k = 0 := by
  by_contra h; exact hk (mem_boxFin.mpr (hc k h))

theorem exists_boxFin_superset (S : Finset (Lattice d)) : ∃ n, S ⊆ boxFin d n := by
  refine ⟨∑ k ∈ S, ∑ i, (k i).natAbs, fun k hk => mem_boxFin.mpr fun i => ?_⟩
  have h1 : (k i).natAbs ≤ ∑ i, (k i).natAbs :=
    Finset.single_le_sum (f := fun i => (k i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have h2 : ∑ i, (k i).natAbs ≤ ∑ k ∈ S, ∑ i, (k i).natAbs :=
    Finset.single_le_sum (f := fun k => ∑ i, (k i).natAbs) (fun _ _ => Nat.zero_le _) hk
  have := h1.trans h2
  rw [Int.abs_eq_natAbs]
  exact_mod_cast this

/-- The trigonometric polynomial with coefficients `c` supported in the box of radius `n`. -/
def trigFun (n : ℕ) (c : Coeff d) (x : Torus d) : ℂ := ∑ k ∈ boxFin d n, c k * Torus.mode k x

theorem continuous_trigFun (n : ℕ) (c : Coeff d) : Continuous (trigFun n c) :=
  continuous_finsetSum _ fun k _ => continuous_const.mul (Torus.continuous_mode k)

theorem integrable_of_continuous' {E : Type*} [NormedAddCommGroup E] {f : Torus d → E}
    (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem coeffOf_eq (φ : Torus d → ℝ) (n : Lattice d) :
    coeffOf φ n = ∫ x, Torus.mode (-n) x * (φ x : ℂ) := by
  unfold coeffOf Torus.funFourierCoeff UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul]
  rw [Torus.volume_eq_pi_haar]
  rfl

theorem mulCoeff_of_trig {n : ℕ} {c : Coeff d} (hc : IsTrigPoly n c) (a : Coeff d)
    (k : Lattice d) : mulCoeff a c k = ∑ l ∈ boxFin d n, a (k - l) * c l := by
  unfold mulCoeff
  exact tsum_eq_sum fun l hl => by rw [eq_zero_of_isTrigPoly hc hl, mul_zero]

theorem trigFun_expand (n n' : ℕ) (c h : Coeff d) (x : Torus d) (φx : ℂ) :
    φx * trigFun n c x * conj (trigFun n' h x) =
      ∑ k ∈ boxFin d n', ∑ l ∈ boxFin d n,
        (conj (h k) * c l) * (Torus.mode (l + -k) x * φx) := by
  unfold trigFun
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, ← Torus.mode_neg, Torus.mode_add]
  ring

/-- The pairing of the Fourier coefficients of `φ u` against a trigonometric polynomial `h` is the
integral `∫ φ u \bar h`. -/
theorem pairing_eq_integral (φ : Torus d → ℝ) (hφ : Continuous φ) (n n' : ℕ) (c h : Coeff d)
    (hc : IsTrigPoly n c) :
    ∑ k ∈ boxFin d n', conj (h k) * mulCoeff (coeffOf φ) c k =
      ∫ x, (φ x : ℂ) * trigFun n c x * conj (trigFun n' h x) := by
  simp_rw [trigFun_expand n n' c h]
  have hint : ∀ k l : Lattice d, Integrable fun x : Torus d =>
      (conj (h k) * c l) * (Torus.mode (l + -k) x * (φ x : ℂ)) := fun k l =>
    integrable_of_continuous' (continuous_const.mul ((Torus.continuous_mode _).mul
      (Complex.continuous_ofReal.comp hφ)))
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun l _ => hint k l)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ (fun l _ => hint k l), mulCoeff_of_trig hc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, coeffOf_eq]
  have : -(k - l) = l + -k := by abel
  rw [this]
  ring

/-- Parseval for trigonometric polynomials. -/
theorem integral_trigFun_mul_conj (n : ℕ) (c h : Coeff d) :
    ∫ x, trigFun n c x * conj (trigFun n h x) = ∑ k ∈ boxFin d n, c k * conj (h k) := by
  have := trigFun_expand n n c h
  have e : ∀ x, trigFun n c x * conj (trigFun n h x) = ∑ k ∈ boxFin d n, ∑ l ∈ boxFin d n,
        (conj (h k) * c l) * (Torus.mode (l + -k) x * 1) := by
    intro x
    have := trigFun_expand n n c h x 1
    simpa using this
  simp_rw [e]
  have hint : ∀ k l : Lattice d, Integrable fun x : Torus d =>
      (conj (h k) * c l) * (Torus.mode (l + -k) x * 1) := fun k l =>
    integrable_of_continuous' (continuous_const.mul ((Torus.continuous_mode _).mul continuous_const))
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun l _ => hint k l)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_finsetSum _ (fun l _ => hint k l)]
  simp_rw [integral_const_mul, mul_one]
  have hz : ∀ l, ∫ x : Torus d, Torus.mode (l + -k) x = if l = k then 1 else 0 := by
    intro l
    rw [Torus.integral_mode]
    simp [add_neg_eq_zero]
  simp_rw [hz]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' (boxFin d n) k, if_pos hk]
  ring

theorem integral_norm_sq_trigFun (n : ℕ) (c : Coeff d) :
    ∫ x, ‖trigFun n c x‖ ^ 2 = ∑ k ∈ boxFin d n, ‖c k‖ ^ 2 := by
  have h := integral_trigFun_mul_conj n c c
  have e : ∀ z : ℂ, z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.mul_conj']; push_cast; ring
  simp_rw [e] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h


/-- `ℓ²` bound for multiplication by a bounded continuous function (Bessel): for every finite
set `S`, `∑_{k∈S} |(φ̂ * c)(k)|² ≤ K² ∑ |c|²`. -/
theorem l2_mul_le (φ : Torus d → ℝ) (hφ : Continuous φ) (K : ℝ) (hK : ∀ x, |φ x| ≤ K)
    (n : ℕ) (c : Coeff d) (hc : IsTrigPoly n c) (S : Finset (Lattice d)) :
    ∑ k ∈ S, ‖mulCoeff (coeffOf φ) c k‖ ^ 2 ≤ K ^ 2 * ∑ k ∈ boxFin d n, ‖c k‖ ^ 2 := by
  classical
  obtain ⟨n', hSn'⟩ := exists_boxFin_superset S
  set γ : Coeff d := mulCoeff (coeffOf φ) c with hγ
  set H : Coeff d := fun k => if k ∈ S then γ k else 0 with hH
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK (Classical.arbitrary _))
  have hLHS : ∑ k ∈ boxFin d n', conj (H k) * γ k = ((∑ k ∈ S, ‖γ k‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Finset.sum_subset hSn' (f := fun k => conj (H k) * γ k)]
    · push_cast
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [hH, hk, ite_true]
      rw [mul_comm, Complex.mul_conj']
    · intro k _ hk
      simp [hH, hk]
  have hHnorm : ∑ k ∈ boxFin d n', ‖H k‖ ^ 2 = ∑ k ∈ S, ‖γ k‖ ^ 2 := by
    rw [← Finset.sum_subset hSn' (f := fun k => ‖H k‖ ^ 2)]
    · exact Finset.sum_congr rfl fun k hk => by simp [hH, hk]
    · intro k _ hk; simp [hH, hk]
  have hP := pairing_eq_integral φ hφ n n' c H hc
  rw [hLHS] at hP
  set u := trigFun n c with hu
  set Hf := trigFun n' H with hHf
  have hcu := continuous_trigFun n c
  have hcH := continuous_trigFun n' H
  have hint1 : Integrable fun x => ‖(φ x : ℂ) * u x * conj (Hf x)‖ :=
    (integrable_of_continuous' (by
      have := Complex.continuous_ofReal.comp hφ
      exact ((this.mul hcu).mul (Complex.continuous_conj.comp hcH)))).norm
  have hint2 : Integrable fun x => ‖u x‖ ^ 2 := integrable_of_continuous' (hcu.norm.pow 2)
  have hint3 : Integrable fun x => ‖Hf x‖ ^ 2 := integrable_of_continuous' (hcH.norm.pow 2)
  have hmono : ∫ x, ‖(φ x : ℂ) * u x * conj (Hf x)‖ ≤ ∫ x, (K ^ 2 * ‖u x‖ ^ 2 + ‖Hf x‖ ^ 2) / 2 := by
    refine integral_mono hint1 (((hint2.const_mul _).add hint3).div_const _) fun x => ?_
    simp only [norm_mul, Complex.norm_real, RCLike.norm_conj]
    have h1 : ‖φ x‖ ≤ K := hK x
    have h2 : ‖φ x‖ * ‖u x‖ * ‖Hf x‖ ≤ K * ‖u x‖ * ‖Hf x‖ := by gcongr
    nlinarith [sq_nonneg (K * ‖u x‖ - ‖Hf x‖)]
  have hnorm : ‖((∑ k ∈ S, ‖γ k‖ ^ 2 : ℝ) : ℂ)‖ ≤ ∫ x, ‖(φ x : ℂ) * u x * conj (Hf x)‖ := by
    rw [hP]; exact norm_integral_le_integral_norm _
  have hrhs : ∫ x, (K ^ 2 * ‖u x‖ ^ 2 + ‖Hf x‖ ^ 2) / 2 =
      (K ^ 2 * ∑ k ∈ boxFin d n, ‖c k‖ ^ 2 + ∑ k ∈ S, ‖γ k‖ ^ 2) / 2 := by
    rw [integral_div, integral_add (hint2.const_mul _) hint3, integral_const_mul,
      integral_norm_sq_trigFun, integral_norm_sq_trigFun, hHnorm]
  have hpos : 0 ≤ ∑ k ∈ S, ‖γ k‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Complex.norm_real, Real.norm_of_nonneg hpos] at hnorm
  linarith

end HRS.PDE
