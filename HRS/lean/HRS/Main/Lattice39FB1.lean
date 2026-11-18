import HRS.Main.Lattice39FinalSpec

/-!
# Example A.39 final form, packet `l39b`: D1 (`lattice39f_I2`) and the assembly of `InitialFluctuation`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory BoundedContinuousFunction

namespace HRS

namespace Main

variable {d : ℕ}

/-- (l39b) Bridge: a continuous `H^m` function with `m > d/2 + j` is `C^j`. -/
theorem l39b_isCk_of_memSobolev (j : ℕ) (m : ℝ) (hm : (d : ℝ) / 2 + j < m) {ψ : Torus d → ℝ}
    (hψc : Continuous ψ) (hψ : MemSobolev m ψ) : Torus.IsCk j ψ := by
  have hint : Integrable ψ := hψc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcm := (PDE.hsNormSq_coeffOf _ ψ hψ).1
  have hd : (d : ℝ) / 2 < m := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hs := PDE.summable_norm_of_memHs _ hd _ hcm
  have hre : PDE.IsRealCoeff (PDE.coeffOf ψ) := PDE.isRealCoeff_coeffOf ψ hint
  obtain ⟨C, hC⟩ := PDE.toFun_isCk_le (d := d) j m hm
  have := (hC _ hcm hre).1
  rwa [PDE.toFun_coeffOf ψ hψc hs] at this

/-- (l39b) `d/2 + 2 < m_*`. -/
theorem l39b_mStar_gt (d : ℕ) : (d : ℝ) / 2 + ((2 : ℕ) : ℝ) < ((PDE.mStar d : ℕ) : ℝ) := by
  unfold PDE.mStar
  push_cast
  have := Nat.lt_floor_add_one ((d : ℝ) / 2)
  linarith

/-- (l39b) `cbNorm` is nonnegative. -/
theorem l39b_cbNorm_nonneg (k : ℕ) (φ : Torus d → ℝ) : 0 ≤ Torus.cbNorm k φ :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

/-- (l39b) deterministic core of D1. -/
theorem l39b_I2_det (hd : 1 ≤ d) (a : Torus d → Euc d) (ha : Torus.IsSmooth a) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ (n : ℕ), 1 ≤ n → ∀ κ : ℝ, 0 < κ →
    ∀ Cin : ℝ, Ca * (1 + κ⁻¹ + κ * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ))) ≤ Cin →
    ∀ ψ : Torus d → ℝ, MemSobolev ((PDE.mStar d : ℕ) : ℝ) ψ → Continuous ψ →
      (κ * (pair (empirical (perturbedLattice n κ a)) ψ - pair volume ψ)) ^ 2 +
        (∫ x, ψ x * (-Torus.div a x)) ^ 2 ≤
      Cin ^ 2 * sobolevNorm ((PDE.mStar d : ℕ) : ℝ) ψ ^ 2 := by
  have ha1 : Torus.IsCk 1 a := by
    unfold Torus.IsSmooth Torus.IsCk at *
    exact ha.of_le (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := perturbedLattice_stat hd
  obtain ⟨Ce, hCe⟩ := cbNorm_le_sobolevNorm (d := d) 2 ((PDE.mStar d : ℕ) : ℝ) (l39b_mStar_gt d)
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (InitialDataAux.continuous_div a ha1).continuousOn
  set M0 : ℝ := max M 0 with hM0
  have hM0nn : 0 ≤ M0 := le_max_right _ _
  have hMb : ∀ x, |Torus.div a x| ≤ M0 := fun x => by
    have := hM x trivial
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  set A := Torus.cbNorm 1 a with hA
  set B : ℝ := |C| * (A ^ 2 + 1) * Ce with hB
  set G : ℝ := M0 * Ce with hG
  refine ⟨Real.sqrt (2 * B ^ 2 + 3 * G ^ 2), Real.sqrt_nonneg _, ?_⟩
  intro n hn κ hκ Cin hCin ψ hψ hψc
  set S := sobolevNorm ((PDE.mStar d : ℕ) : ℝ) ψ with hS
  have hψ2 : Torus.IsCk 2 ψ := by
    have := l39b_isCk_of_memSobolev (d := d) 2 ((PDE.mStar d : ℕ) : ℝ) (l39b_mStar_gt d) hψc hψ
    exact_mod_cast this
  have hcb : Torus.cbNorm 2 ψ ≤ Ce * S := hCe ψ hψ hψ2
  have hcb0 : 0 ≤ Torus.cbNorm 2 ψ := l39b_cbNorm_nonneg 2 ψ
  set cb := Torus.cbNorm 2 ψ with hcbdef
  set Nn : ℝ := ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ)) with hNn
  have hNn0 : 0 ≤ Nn := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set E0 : ℝ := κ⁻¹ + κ * Nn with hE0
  have hE00 : 0 ≤ E0 := by positivity
  have hstat := hC n hn κ hκ a ha1 ψ hψ2
  set x := κ * (pair (empirical (perturbedLattice n κ a)) ψ - pair volume ψ) with hx
  set y := ∫ x, ψ x * (-Torus.div a x) with hy
  have hxy : |x - y| ≤ |C| * (A ^ 2 + 1) * E0 * cb := by
    have e1 : x - y = κ * (pair (empirical (perturbedLattice n κ a)) ψ - ∫ x, ψ x) +
        ∫ x, ψ x * Torus.div a x := by
      rw [hx, hy]
      simp only [pair, mul_neg, integral_neg]
      ring
    rw [e1]
    refine hstat.trans ?_
    have h1 : C * (κ⁻¹ * cb * A ^ 2 + κ * Nn * cb) ≤ |C| * (κ⁻¹ * cb * A ^ 2 + κ * Nn * cb) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    refine h1.trans ?_
    have h2 : κ⁻¹ * cb * A ^ 2 + κ * Nn * cb ≤ (A ^ 2 + 1) * E0 * cb := by
      rw [hE0]
      have : 0 ≤ κ⁻¹ * cb := by positivity
      have : 0 ≤ κ * Nn * cb := by positivity
      nlinarith [sq_nonneg A, mul_nonneg (sq_nonneg A) (mul_nonneg (mul_nonneg hκ.le hNn0) hcb0)]
    calc |C| * _ ≤ |C| * ((A ^ 2 + 1) * E0 * cb) := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
      _ = _ := by ring
  have hy_le : |y| ≤ cb * M0 := by
    have hb : ∀ z : Torus d, ‖ψ z * (-Torus.div a z)‖ ≤ cb * M0 := fun z => by
      rw [norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (PDE.abs_le_cbNorm 2 ψ hψ2 z) (hMb z) (abs_nonneg _) hcb0
    have := norm_integral_le_of_norm_le_const (μ := (volume : Measure (Torus d)))
      (f := fun z => ψ z * (-Torus.div a z)) (C := cb * M0) (Filter.Eventually.of_forall hb)
    simpa [hy] using this
  have hP0 : 0 ≤ |C| * (A ^ 2 + 1) := by positivity
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hD : |x - y| ≤ |B * E0 * S| := by
    refine (hxy.trans ?_).trans (le_abs_self _)
    calc |C| * (A ^ 2 + 1) * E0 * cb ≤ |C| * (A ^ 2 + 1) * E0 * (Ce * S) :=
          mul_le_mul_of_nonneg_left hcb (by positivity)
      _ = B * E0 * S := by rw [hB]; ring
  have hY : |y| ≤ |G * S| := by
    refine (hy_le.trans ?_).trans (le_abs_self _)
    calc cb * M0 ≤ (Ce * S) * M0 := mul_le_mul_of_nonneg_right hcb hM0nn
      _ = G * S := by rw [hG]; ring
  have hD2 : (x - y) ^ 2 ≤ (B * E0 * S) ^ 2 := sq_le_sq.mpr hD
  have hY2 : y ^ 2 ≤ (G * S) ^ 2 := sq_le_sq.mpr hY
  have hx2 : x ^ 2 + y ^ 2 ≤ 2 * (x - y) ^ 2 + 3 * y ^ 2 := by nlinarith [sq_nonneg (x - 2 * y)]
  set E' : ℝ := 1 + κ⁻¹ + κ * Nn with hE'
  have hE'1 : 1 ≤ E' := by
    have : 0 ≤ κ⁻¹ := by positivity
    have : 0 ≤ κ * Nn := by positivity
    linarith
  have hE0E : E0 ≤ E' := by rw [hE', hE0]; linarith
  have hCin0 : Real.sqrt (2 * B ^ 2 + 3 * G ^ 2) * E' ≤ Cin := hCin
  have hCin2 : (2 * B ^ 2 + 3 * G ^ 2) * E' ^ 2 ≤ Cin ^ 2 := by
    have hq : 0 ≤ 2 * B ^ 2 + 3 * G ^ 2 := by positivity
    have h0 : 0 ≤ Real.sqrt (2 * B ^ 2 + 3 * G ^ 2) * E' := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
    have := pow_le_pow_left₀ h0 hCin0 2
    rwa [mul_pow, Real.sq_sqrt hq] at this
  have hE02 : E0 ^ 2 ≤ E' ^ 2 := pow_le_pow_left₀ hE00 hE0E 2
  have hE'2 : 1 ≤ E' ^ 2 := one_le_pow₀ hE'1
  calc x ^ 2 + y ^ 2 ≤ 2 * (B * E0 * S) ^ 2 + 3 * (G * S) ^ 2 := by linarith
    _ = (2 * B ^ 2 * E0 ^ 2 + 3 * G ^ 2) * S ^ 2 := by ring
    _ ≤ ((2 * B ^ 2 + 3 * G ^ 2) * E' ^ 2) * S ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg S)
        have h1 := mul_le_mul_of_nonneg_left hE02 (sq_nonneg B)
        have h2 := mul_le_mul_of_nonneg_left hE'2 (sq_nonneg G)
        linarith
    _ ≤ Cin ^ 2 * S ^ 2 := mul_le_mul_of_nonneg_right hCin2 (sq_nonneg S)

/-- D1 (`I2` at a lattice `N = n^d`, `m₀ = m_* = mStar d`), relocated proof. -/
theorem lattice39f_I2_proof (hd : 1 ≤ d) (a : Torus d → Euc d) (ha : Torus.IsSmooth a) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ (n : ℕ), 1 ≤ n → ∀ κ : ℝ, 0 < κ →
    ∀ Cin : ℝ, Ca * (1 + κ⁻¹ + κ * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ))) ≤ Cin →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → Config d (n ^ d)) (η : Ω → (Torus d → ℝ) → ℝ),
      (∀ᵐ ω ∂P, X₀ ω = perturbedLattice n κ a) →
      (∀ ω ψ, η ω ψ = ∫ x, ψ x * (-Torus.div a x)) →
      ∀ ψ : Torus d → ℝ, MemSobolev ((PDE.mStar d : ℕ) : ℝ) ψ → Continuous ψ →
        ∫⁻ ω, ENNReal.ofReal ((κ * (pair (empirical (X₀ ω)) ψ - pair volume ψ)) ^ 2) ∂P +
          ∫⁻ ω, ENNReal.ofReal ((η ω ψ) ^ 2) ∂P ≤
        ENNReal.ofReal (Cin ^ 2 * sobolevNorm ((PDE.mStar d : ℕ) : ℝ) ψ ^ 2) := by
  obtain ⟨Ca, hCa0, hCa⟩ := l39b_I2_det hd a ha
  refine ⟨Ca, hCa0, ?_⟩
  intro n hn κ hκ Cin hCin Ω _ P _ X₀ η hX hη ψ hψ hψc
  have key := hCa n hn κ hκ Cin hCin ψ hψ hψc
  have h1 : ∫⁻ ω, ENNReal.ofReal ((κ * (pair (empirical (X₀ ω)) ψ - pair volume ψ)) ^ 2) ∂P =
      ENNReal.ofReal ((κ * (pair (empirical (perturbedLattice n κ a)) ψ - pair volume ψ)) ^ 2) := by
    rw [lintegral_congr_ae (g := fun _ => ENNReal.ofReal
      ((κ * (pair (empirical (perturbedLattice n κ a)) ψ - pair volume ψ)) ^ 2))
      (by filter_upwards [hX] with ω hω; rw [hω])]
    simp
  have h2 : ∫⁻ ω, ENNReal.ofReal ((η ω ψ) ^ 2) ∂P =
      ENNReal.ofReal ((∫ x, ψ x * (-Torus.div a x)) ^ 2) := by
    simp [hη]
  rw [h1, h2, ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal key

example := (@lattice39f_I2_proof : type_of% @lattice39f_I2)

end Main

end HRS
