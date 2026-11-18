import HRS.Main.ThermLinPlan2

/-!
# THERMLIN2 Mo3: `tl2_traceNorm_covForm_diff` (C3)

Pattern of `t25p_trace_le_entries` (T25PAux15): trace norm `≤` `ℓ¹` norm of the entries
`2q w_k w_l ∫ F_{kl} (ρ₁ - ρ₂) dx`, `|F_{kl}| ≤ 2d ⟨k⟩⟨l⟩`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q48c

variable {d : ℕ}

/-- The `(k,l)` entry of `covForm m q (ρ₁ dx) - covForm m q (ρ₂ dx)` is bounded by `4 q d w_k⟨k⟩ w_l⟨l⟩ ‖ρ₁-ρ₂‖_{L¹}`. -/
theorem tl2Mo_entry_diff_le {m : ℝ} (hm : (d : ℝ) / 2 + 2 < m) {q : ℝ} (hq : 0 ≤ q) {ρ₁ ρ₂ : Torus d → ℝ}
    (hc₁ : Continuous ρ₁) (hc₂ : Continuous ρ₂) (hP₁ : IsProbDensity ρ₁) (hP₂ : IsProbDensity ρ₂)
    (k l : NonzeroLattice d) :
    |(covForm m q (withDensityReal ρ₁) - covForm m q (withDensityReal ρ₂)) (basis d m k) (basis d m l)| ≤
      4 * q * d * ((wt m k * Lattice.jp k.1) * (wt m l * Lattice.jp l.1)) * ∫ x, |ρ₁ x - ρ₂ x| := by
  haveI := isFiniteMeasure_withDensityReal_of_cont hc₁
  haveI := isFiniteMeasure_withDensityReal_of_cont hc₂
  have hint : ∀ {f : Torus d → ℝ}, Continuous f → Integrable f (volume : Measure (Torus d)) := fun hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hF := continuous_Fkl k l
  rw [_root_.sub_apply, ContinuousLinearMap.sub_apply, covForm_basis hm hq, covForm_basis hm hq,
    HRS.PDE.MFPairing.integral_withDensityReal hP₁.measurable hP₁.nonneg,
    HRS.PDE.MFPairing.integral_withDensityReal hP₂.measurable hP₂.nonneg, ← mul_sub,
    ← integral_sub (f := fun x => ρ₁ x * Fkl k l x) (g := fun x => ρ₂ x * Fkl k l x) (hint (hc₁.mul hF)) (hint (hc₂.mul hF))]
  have hw := wt_pos (m := m) k
  have hw' := wt_pos (m := m) l
  have hjk := Torus.jp_pos k.1
  have hjl := Torus.jp_pos l.1
  have hK0 : 0 ≤ 2 * d * (Lattice.jp k.1 * Lattice.jp l.1) := by positivity
  have h1 : |∫ x, (ρ₁ x * Fkl k l x - ρ₂ x * Fkl k l x)| ≤ (∫ x, |ρ₁ x - ρ₂ x|) * (2 * d * (Lattice.jp k.1 * Lattice.jp l.1)) := by
    have e1 : |∫ x, (ρ₁ x * Fkl k l x - ρ₂ x * Fkl k l x)| ≤ ∫ x, |ρ₁ x * Fkl k l x - ρ₂ x * Fkl k l x| := by
      simpa [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := (volume : Measure (Torus d)))
          (fun x => ρ₁ x * Fkl k l x - ρ₂ x * Fkl k l x)
    refine e1.trans ?_
    rw [← integral_mul_const]
    refine integral_mono (hint ((hc₁.mul hF).sub (hc₂.mul hF)).abs) (hint (((hc₁.sub hc₂).abs).mul continuous_const)) fun x => ?_
    show |ρ₁ x * Fkl k l x - ρ₂ x * Fkl k l x| ≤ |ρ₁ x - ρ₂ x| * (2 * d * (Lattice.jp k.1 * Lattice.jp l.1))
    rw [← sub_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_Fkl_le k l x) (abs_nonneg _)
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * q * (wt m k * wt m l))]
  calc 2 * q * (wt m k * wt m l) * |∫ x, (ρ₁ x * Fkl k l x - ρ₂ x * Fkl k l x)|
      ≤ 2 * q * (wt m k * wt m l) * ((∫ x, |ρ₁ x - ρ₂ x|) * (2 * d * (Lattice.jp k.1 * Lattice.jp l.1))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

/-- C3 (proof). -/
theorem tl2_traceNorm_covForm_diff_proof (m : ℝ) (hm : (d : ℝ) + 2 < m) (q : ℝ) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ₁ ρ₂ : Torus d → ℝ, Continuous ρ₁ → Continuous ρ₂ → IsProbDensity ρ₁ → IsProbDensity ρ₂ →
      traceNormForm (covForm m q (withDensityReal ρ₁) - covForm m q (withDensityReal ρ₂)) ≤
        C * ∫ x, |ρ₁ x - ρ₂ x| := by
  have hm1 : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hm2 : (d : ℝ) + 1 < m := by linarith
  have hs := summable_s (d := d) (m := m) hm2
  have hnn : ∀ k : NonzeroLattice d, 0 ≤ wt m k * Lattice.jp k.1 := fun k =>
    mul_nonneg (wt_pos k).le (Torus.jp_pos k.1).le
  have hsum2 : Summable fun p : NonzeroLattice d × NonzeroLattice d =>
      (wt m p.1 * Lattice.jp p.1.1) * (wt m p.2 * Lattice.jp p.2.1) := hs.mul_of_nonneg hs hnn hnn
  have hT0 : 0 ≤ ∑' p : NonzeroLattice d × NonzeroLattice d,
      (wt m p.1 * Lattice.jp p.1.1) * (wt m p.2 * Lattice.jp p.2.1) :=
    tsum_nonneg fun p => mul_nonneg (hnn p.1) (hnn p.2)
  refine ⟨4 * q * d * ∑' p : NonzeroLattice d × NonzeroLattice d,
      (wt m p.1 * Lattice.jp p.1.1) * (wt m p.2 * Lattice.jp p.2.1), by positivity, ?_⟩
  intro ρ₁ ρ₂ hc₁ hc₂ hP₁ hP₂
  set I : ℝ := ∫ x, |ρ₁ x - ρ₂ x| with hI
  have hent := fun p : NonzeroLattice d × NonzeroLattice d =>
    tl2Mo_entry_diff_le hm1 hq hc₁ hc₂ hP₁ hP₂ p.1 p.2
  have hsumB : Summable fun p : NonzeroLattice d × NonzeroLattice d =>
      4 * q * d * ((wt m p.1 * Lattice.jp p.1.1) * (wt m p.2 * Lattice.jp p.2.1)) * I :=
    (hsum2.mul_left (4 * q * d)).mul_right I
  have hsumQ : Summable fun p : NonzeroLattice d × NonzeroLattice d =>
      |(covForm m q (withDensityReal ρ₁) - covForm m q (withDensityReal ρ₂)) (basis d m p.1) (basis d m p.2)| :=
    Summable.of_nonneg_of_le (fun p => abs_nonneg _) hent hsumB
  calc traceNormForm (covForm m q (withDensityReal ρ₁) - covForm m q (withDensityReal ρ₂))
      ≤ ∑' p : NonzeroLattice d × NonzeroLattice d,
        |(covForm m q (withDensityReal ρ₁) - covForm m q (withDensityReal ρ₂)) (basis d m p.1) (basis d m p.2)| :=
        t25p_traceNormForm_le_entries (basis d m) _ hsumQ
    _ ≤ ∑' p : NonzeroLattice d × NonzeroLattice d,
        4 * q * d * ((wt m p.1 * Lattice.jp p.1.1) * (wt m p.2 * Lattice.jp p.2.1)) * I :=
        Summable.tsum_le_tsum hent hsumQ hsumB
    _ = _ := by
        rw [tsum_mul_right, tsum_mul_left]

example := (@tl2_traceNorm_covForm_diff_proof : type_of% @tl2_traceNorm_covForm_diff)

end HRS.ThermLin.Plan2
