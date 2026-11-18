import HRS.Main.GFEVAux11

/-!
# Packet GFEVG, part 12: norm continuity of the density path in `C^j` (from weak continuity and uniform decay)
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54

variable {d : ℕ}

theorem gfev_abs_funRealCoeff_le (φ : Torus d → ℝ) (hφ : Integrable φ) (k : NonzeroLattice d) :
    |Torus.funRealCoeff φ k| ≤ Real.sqrt 2 * ‖coeffOf φ k.1‖ := by
  have h := Torus.integral_mode_mul_real hφ k.1
  rw [← ClassicalAux.coeffOf_apply] at h
  have hre : |(coeffOf φ k.1).re| ≤ ‖coeffOf φ k.1‖ := Complex.abs_re_le_norm _
  have him : |(coeffOf φ k.1).im| ≤ ‖coeffOf φ k.1‖ := Complex.abs_im_le_norm _
  have e1 : (coeffOf φ k.1).re = Torus.cosCoeff φ k.1 := by rw [h]; simp
  have e2 : (coeffOf φ k.1).im = -Torus.sinCoeff φ k.1 := by rw [h]; simp
  rw [e1] at hre
  rw [e2, abs_neg] at him
  rw [Torus.funRealCoeff_eq]
  have h2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  split_ifs
  · rw [abs_mul, abs_of_nonneg h2]; exact mul_le_mul_of_nonneg_left hre h2
  · rw [abs_mul, abs_of_nonneg h2]; exact mul_le_mul_of_nonneg_left him h2

/-- A weakly continuous family with uniform `C^n` bounds is norm continuous in `C^j`, `j + 2d + 1 ≤ n`. -/
theorem gfev_cb_tendsto {f : ℝ → Torus d → ℝ} {n j : ℕ} {Λ c₀ : ℝ} (hd : 1 ≤ d) (hn : j + 2 * d + 1 ≤ n)
    (hf : ∀ t, Torus.IsCk (n : WithTop ℕ∞) (f t)) (hb : ∀ t, Torus.cbNorm n (f t) ≤ Λ)
    (hmean : ∀ t, Torus.mean (f t) = c₀)
    (hc : ∀ ψ : Torus d → ℝ, Continuous ψ → Continuous fun t => ∫ x, ψ x * f t x) (t₀ : ℝ) :
    Tendsto (fun t => Torus.cbNorm j (fun x => f t x - f t₀ x)) (𝓝 t₀) (𝓝 0) := by
  have hcont : ∀ t, Continuous (f t) := fun t => Torus.continuous_of_continuous_lift (hf t).continuous
  have hint : ∀ t, Integrable (f t) := fun t => ClassicalAux.integrable_of_continuous (hcont t)
  have hjn : j ≤ n := by omega
  set m'' : ℝ := ((j + d : ℕ) : ℝ) with hm''
  have hdj : (d : ℝ) / 2 + (j : ℝ) < m'' := by
    rw [hm'']; push_cast
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨Ccb, hCcb⟩ := cbNorm_le_sobolevNorm (d := d) j m'' hdj
  set c1 : ℝ := ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n with hc1
  have hΛ0 : 0 ≤ Λ := (R2Aux.cbNorm_nonneg' n (f t₀)).trans (hb t₀)
  set B : ℝ := Λ * c1 + Λ with hB
  have hB0 : 0 ≤ B := by positivity
  -- coefficient bound
  have hcoef : ∀ t (k : NonzeroLattice d), |Torus.funRealCoeff (f t) k| ≤
      Real.sqrt 2 * B * Lattice.jp k.1 ^ (-(n : ℝ)) := by
    intro t k
    refine (gfev_abs_funRealCoeff_le _ (hint t) k).trans ?_
    have := gfev_coeff_decay (f t) n Λ (hf t) (hb t) k.1
    calc Real.sqrt 2 * ‖coeffOf (f t) k.1‖ ≤ Real.sqrt 2 * (B * Lattice.jp k.1 ^ (-(n : ℝ))) :=
          mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
      _ = _ := by ring
  have hm2 : (d : ℝ) < 2 * ((n : ℝ) - m'') := by
    rw [hm'']; push_cast
    have : (j + 2 * d + 1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hS : Summable fun k : NonzeroLattice d => 8 * B ^ 2 * Lattice.jp k.1 ^ (-(2 * ((n : ℝ) - m''))) :=
    (summable_jp_rpow (d := d) ((n : ℝ) - m'') hm2).mul_left _
  -- the difference
  set Δ : ℝ → Torus d → ℝ := fun t x => f t x - f t₀ x with hΔ
  have hΔc : ∀ t, Continuous (Δ t) := fun t => (hcont t).sub (hcont t₀)
  have hΔco : ∀ t k, Torus.funRealCoeff (Δ t) k = Torus.funRealCoeff (f t) k - Torus.funRealCoeff (f t₀) k := by
    intro t k
    exact funRealCoeff_sub' (ClassicalAux.memLp_two_of_continuous (hcont t))
      (ClassicalAux.memLp_two_of_continuous (hcont t₀)) k
  have hterm : ∀ t k, Lattice.jp k.1 ^ (2 * m'') * Torus.funRealCoeff (Δ t) k ^ 2 ≤
      8 * B ^ 2 * Lattice.jp k.1 ^ (-(2 * ((n : ℝ) - m''))) := by
    intro t k
    rw [hΔco]
    have h1 := hcoef t k
    have h2 := hcoef t₀ k
    have h3 : |Torus.funRealCoeff (f t) k - Torus.funRealCoeff (f t₀) k| ≤
        2 * (Real.sqrt 2 * B * Lattice.jp k.1 ^ (-(n : ℝ))) := by
      have := abs_sub (Torus.funRealCoeff (f t) k) (Torus.funRealCoeff (f t₀) k)
      linarith
    have h4 : (Torus.funRealCoeff (f t) k - Torus.funRealCoeff (f t₀) k) ^ 2 ≤
        (2 * (Real.sqrt 2 * B * Lattice.jp k.1 ^ (-(n : ℝ)))) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h3 2
    have hj := Torus.jp_pos k.1
    have h5 : (2 * (Real.sqrt 2 * B * Lattice.jp k.1 ^ (-(n : ℝ)))) ^ 2 =
        8 * B ^ 2 * Lattice.jp k.1 ^ (-(2 * (n : ℝ))) := by
      have : (Lattice.jp k.1 ^ (-(n : ℝ))) ^ 2 = Lattice.jp k.1 ^ (-(2 * (n : ℝ))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hj.le]; congr 1; push_cast; ring
      have h2' : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      calc (2 * (Real.sqrt 2 * B * Lattice.jp k.1 ^ (-(n : ℝ)))) ^ 2
          = 4 * (Real.sqrt 2 ^ 2) * B ^ 2 * (Lattice.jp k.1 ^ (-(n : ℝ))) ^ 2 := by ring
        _ = _ := by rw [h2', this]; ring
    have h6 : Lattice.jp k.1 ^ (2 * m'') * Lattice.jp k.1 ^ (-(2 * (n : ℝ))) =
        Lattice.jp k.1 ^ (-(2 * ((n : ℝ) - m''))) := by
      rw [← Real.rpow_add hj]; congr 1; ring
    calc Lattice.jp k.1 ^ (2 * m'') * (Torus.funRealCoeff (f t) k - Torus.funRealCoeff (f t₀) k) ^ 2
        ≤ Lattice.jp k.1 ^ (2 * m'') * (8 * B ^ 2 * Lattice.jp k.1 ^ (-(2 * (n : ℝ)))) :=
          mul_le_mul_of_nonneg_left (h4.trans h5.le) (Real.rpow_nonneg hj.le _)
      _ = 8 * B ^ 2 * (Lattice.jp k.1 ^ (2 * m'') * Lattice.jp k.1 ^ (-(2 * (n : ℝ)))) := by ring
      _ = _ := by rw [h6]
  have hMem : ∀ t, MemSobolev m'' (Δ t) := by
    intro t
    refine ⟨ClassicalAux.memLp_two_of_continuous (hΔc t), ?_⟩
    exact Summable.of_nonneg_of_le (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _))
      (fun k => hterm t k) hS
  have hmeanΔ : ∀ t, Torus.mean (Δ t) = 0 := by
    intro t
    have := integral_sub (hint t) (hint t₀)
    unfold Torus.mean at *
    simp only [hΔ]
    rw [this]
    have h1 := hmean t
    have h2 := hmean t₀
    unfold Torus.mean at h1 h2
    rw [h1, h2]; ring
  -- each coefficient is continuous and vanishes at `t₀`
  have hkc : ∀ k : NonzeroLattice d, Continuous fun t => Torus.funRealCoeff (f t) k := by
    intro k
    have := hc (Torus.realMode k) (Torus.continuous_realMode k)
    exact this
  have hlim : Tendsto (fun t => ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m'') *
      Torus.funRealCoeff (Δ t) k ^ 2) (𝓝 t₀) (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 t₀)
      (f := fun t (k : NonzeroLattice d) => Lattice.jp k.1 ^ (2 * m'') * Torus.funRealCoeff (Δ t) k ^ 2)
      (g := fun _ => 0) (bound := fun k => 8 * B ^ 2 * Lattice.jp k.1 ^ (-(2 * ((n : ℝ) - m''))))
      hS (fun k => ?_) (Eventually.of_forall fun t k => ?_)
    · simpa using this
    · have hcc : Continuous fun t => Lattice.jp k.1 ^ (2 * m'') * Torus.funRealCoeff (Δ t) k ^ 2 := by
        have e : ∀ t, Torus.funRealCoeff (Δ t) k = Torus.funRealCoeff (f t) k - Torus.funRealCoeff (f t₀) k :=
          fun t => hΔco t k
        simp_rw [e]
        exact continuous_const.mul (((hkc k).sub continuous_const).pow 2)
      have h0 : Lattice.jp k.1 ^ (2 * m'') * Torus.funRealCoeff (Δ t₀) k ^ 2 = 0 := by
        rw [hΔco]; simp
      have := hcc.tendsto t₀
      rwa [h0] at this
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _))]
      exact hterm t k
  have hsob : Tendsto (fun t => sobolevNorm m'' (Δ t)) (𝓝 t₀) (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hlim
    simp only [Real.sqrt_zero] at h
    refine h.congr fun t => ?_
    simp only [Function.comp, sobolevNorm, hmeanΔ t]; simp
  have hcb : ∀ t, Torus.cbNorm j (Δ t) ≤ Ccb * sobolevNorm m'' (Δ t) := fun t =>
    hCcb (Δ t) (hMem t) ((ET.isCk_mono' hjn (hf t)).sub (ET.isCk_mono' hjn (hf t₀)))
  have hz := hsob.const_mul Ccb
  rw [mul_zero] at hz
  refine squeeze_zero (fun t => R2Aux.cbNorm_nonneg' j _) (fun t => hcb t) hz

end HRS.GF
