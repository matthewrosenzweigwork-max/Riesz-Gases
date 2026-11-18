import HRS.MS.R2ChaosAux56

/-!
# HRS.MS.R2ChaosAux57 -- S9.6 (P3, part 2): chaos isometry bound, `S94KOK` for polynomial kernels, uniform `L²` bound

Packet S94 (S9.6), namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole HRS.MS.R2Poly

variable {d : ℕ}

section Bound

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
  [IsProbabilityMeasure P'] {z : ℕ → Ω' → ℝ} {Λ : ℝ}

theorem s94_chaos_bound (hz : S94GSeq P' z Λ) (hΛ0 : 0 ≤ Λ) {a : ℕ → Euc d → ℝ} (ha : ∀ i, IsR2Test (a i))
    (hon : ∀ i j, ∫ x, Whole.projMean μ (a i) x * Whole.projMean μ (a j) x ∂μ = if i = j then 1 else 0)
    {k : Euc d → Euc d → ℝ} (hk : S94KOK μ k) {Q : Ω' → ℝ}
    (hQ : s94WickL2 P' μ a z (r2CenterKernel μ k) Q) :
    eLpNorm Q 2 P' ≤ ENNReal.ofReal (Real.sqrt 2 * Λ * 4) * eLpNorm (fun q : Euc d × Euc d => k q.1 q.2) 2 (μ.prod μ) := by
  have cenmem : MemLp (fun q : Euc d × Euc d => r2CenterKernel μ k q.1 q.2) 2 (μ.prod μ) :=
    lt_of_le_of_lt (s94_eLpNorm_center_le (μ := μ) hk.meas) (ENNReal.mul_lt_top (by norm_num) hk.memLp)
  set D : ℝ≥0∞ := eLpNorm (fun q : Euc d × Euc d => k q.1 q.2) 2 (μ.prod μ) with hD
  have hDfin : D ≠ ⊤ := hk.memLp.eLpNorm_ne_top
  have hzero : s94WickL2 P' μ a z (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ)) := by
    refine ⟨MemLp.zero, ?_⟩
    simp [s94Sec, r2WickCoeff]
  have hlip := s94_wick_lipschitz hz hΛ0 ha hon
    (s94_center_measurable (μ := μ) hk.meas) (s94_center_symm hk.symm) cenmem
    (k' := fun _ _ => (0 : ℝ)) measurable_const (fun _ _ => rfl) MemLp.zero hQ hzero
  have hcen : eLpNorm (fun q : Euc d × Euc d => r2CenterKernel μ k q.1 q.2 - 0) 2 (μ.prod μ) ≤
      ENNReal.ofReal (4 * D.toReal) := by
    have := s94_eLpNorm_center_le (μ := μ) hk.meas
    simp only [sub_zero]
    refine this.trans ?_
    have e4 : ENNReal.ofReal 4 = 4 := by norm_num
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hDfin, e4]
  have hsq := s94_integral_sq_le_of_eLpNorm
    (((s94_center_measurable (μ := μ) hk.meas).sub measurable_const).aestronglyMeasurable) (by positivity) hcen
  have hQQ : eLpNorm (fun ζ => Q ζ - 0) 2 P' ≤ ENNReal.ofReal (Real.sqrt 2 * Λ * (4 * D.toReal)) := by
    refine s94_eLpNorm_le_of_sq (hQ.1.sub MemLp.zero) (by positivity) ?_
    calc _ ≤ 2 * Λ ^ 2 * ∫ q, (r2CenterKernel μ k q.1 q.2 - 0) ^ 2 ∂(μ.prod μ) := hlip
      _ ≤ 2 * Λ ^ 2 * (4 * D.toReal) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (Real.sqrt 2 * Λ * (4 * D.toReal)) ^ 2 := by
        rw [show (Real.sqrt 2 * Λ * (4 * D.toReal)) ^ 2 = Real.sqrt 2 ^ 2 * Λ ^ 2 * (4 * D.toReal) ^ 2 by ring,
          Real.sq_sqrt (by norm_num)]
  simp only [sub_zero] at hQQ
  refine hQQ.trans (le_of_eq ?_)
  rw [show Real.sqrt 2 * Λ * (4 * D.toReal) = (Real.sqrt 2 * Λ * 4) * D.toReal by ring,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hDfin]

end Bound

section PolyOK

variable {s M L C₀ c₀ Pw B : ℝ} {ρ : Euc d → ℝ}

theorem s94_kok_poly (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hρ : IsRound2Density d s M L ρ)
    (hG : HasR2GaussianUpper C₀ c₀ ρ) (hPw : 0 ≤ Pw) (hB : 0 ≤ B) {k : Euc d → Euc d → ℝ}
    (hk : IsR2PolyPairKernel s Pw B k) : S94KOK (Whole.withDensityReal ρ) k := by
  obtain ⟨r1, R1⟩ := s94_poly_int_facts hd hs0 hs hρ hG hPw hB hk
  refine ⟨hk.measurable, hk.symm, ?_, r1, R1⟩
  have := s94_poly_memLp hd hs0 hs hρ hG hPw hB hk (q := 2) (by norm_num) (by linarith)
  have e2 : ENNReal.ofReal 2 = 2 := by norm_num
  rwa [e2] at this

theorem s94_poly_L2_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hρ : IsRound2Density d s M L ρ)
    (hG : HasR2GaussianUpper C₀ c₀ ρ) (hPw : 0 ≤ Pw) (hB : 0 ≤ B) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ {k : Euc d → Euc d → ℝ}, IsR2PolyPairKernel s Pw B k →
      eLpNorm (fun q : Euc d × Euc d => k q.1 q.2) 2 ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ))
        ≤ ENNReal.ofReal κ := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  let G : Euc d → Euc d → ℝ := fun x y => B * (jbracket x + jbracket y) ^ Pw * (1 + rieszWeight s (x - y))
  have hGk : IsR2PolyPairKernel s Pw B G := by
    refine ⟨?_, fun x y => ?_, fun x y hxy => ?_⟩
    · exact (measurable_const.mul (((s95_jb_meas.comp measurable_fst).add (s95_jb_meas.comp measurable_snd)).pow_const Pw)).mul
        (measurable_const.add ((HRS.MS.Wr.wr3_measurable_rieszWeight (d := d) s).comp (measurable_fst.sub measurable_snd)))
    · show B * (jbracket x + jbracket y) ^ Pw * (1 + rieszWeight s (x - y)) =
        B * (jbracket y + jbracket x) ^ Pw * (1 + rieszWeight s (y - x))
      rw [add_comm (jbracket x), show rieszWeight s (x - y) = rieszWeight s (y - x) by
        unfold rieszWeight; rw [norm_sub_rev]]
    · have hW := HRS.MS.Wr.wr3_rieszWeight_nonneg (d := d) s (x - y)
      have : 0 ≤ B * (jbracket x + jbracket y) ^ Pw * (1 + rieszWeight s (x - y)) := by
        have h1 : 0 < jbracket x := lt_of_lt_of_le zero_lt_one (s95_one_le_jb x)
        have h2 : 0 < jbracket y := lt_of_lt_of_le zero_lt_one (s95_one_le_jb y)
        positivity
      exact le_of_eq (abs_of_nonneg this)
  have hmem := s94_poly_memLp hd hs0 hs hρ hG hPw hB hGk (q := 2) (by norm_num) (by linarith)
  have hmem' : MemLp (fun q : Euc d × Euc d => G q.1 q.2) 2 ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)) := by
    have e2 : ENNReal.ofReal 2 = 2 := by norm_num
    rwa [e2] at hmem
  refine ⟨(eLpNorm (fun q : Euc d × Euc d => G q.1 q.2) 2
    ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ))).toReal, ENNReal.toReal_nonneg, fun {k} hk => ?_⟩
  rw [ENNReal.ofReal_toReal hmem'.eLpNorm_ne_top]
  have hae : ∀ᵐ q ∂((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)), ‖k q.1 q.2‖ ≤ ‖G q.1 q.2‖ := by
    filter_upwards [s94_ae_offdiag hd hρ] with q hq
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_trans (abs_nonneg _) (hGk.bound q.1 q.2 hq))]
    exact hk.bound q.1 q.2 hq
  exact eLpNorm_mono_ae hk.measurable.aestronglyMeasurable hae

end PolyOK

end HRS.MS.R2Chaos
