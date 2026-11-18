import HRS.MS.R2InterpAux106

/-!
# S10.2 (worker S10R), part 107 (packet M2c): `IsR2L1F` for `η_N` along a continuous particle path
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {Pw : ℝ}

theorem s102_Meta_continuous (hP0 : 0 ≤ Pw) (C0 : ℝ) {N : ℕ} {Ω : Type} (μ : Measure (Euc d))
    (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) (hcz : ∀ k, Continuous fun t : ℝ≥0 => X t ζ k) :
    Continuous fun u : ℝ => s102_Meta C0 Pw μ (X u.toNNReal ζ) := by
  unfold s102_Meta
  have hj : Continuous fun z : Euc d => jbracket z ^ Pw :=
    (by unfold jbracket; fun_prop : Continuous fun z : Euc d => jbracket z).rpow_const
      (fun z => Or.inl (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb z)).ne')
  refine continuous_const.mul ((continuous_const.mul (continuous_finsetSum _ fun k _ => ?_)).add continuous_const)
  exact hj.comp ((hcz k).comp continuous_real_toNNReal)

theorem s102_eta_L1F (hd : 1 ≤ d) (hP0 : 0 ≤ Pw) (r : ℕ) (hr : (d : ℝ) / 2 < r) {N : ℕ} (hN : 0 < N) (T : ℝ)
    {Ω : Type} (μ : Measure (Euc d)) (hμ : Integrable (fun x => jbracket x ^ Pw) μ)
    (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) (hcz : ∀ k, Continuous fun t : ℝ≥0 => X t ζ k) :
    IsR2L1F r Pw T (s102_etaf μ X ζ) := by
  obtain ⟨C0, hC0, hb⟩ := s102_eta_bound hd hP0 r hr hN μ hμ
  refine ⟨fun u _ => ?_, fun f hf => ?_, ?_⟩
  · have hz := s102_Z_fluct hd hP0 r hr hN (X u.toNNReal ζ) μ hμ (Real.sqrt N)
    exact ⟨hz.add, hz.smul, hz.bdd⟩
  · unfold s102_etaf
    simp_rw [HRS.Whole.pair_empirical hN]
    refine (((measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)).sub measurable_const)).const_mul _
    exact hf.1.continuous.measurable.comp (((hcz k).comp continuous_real_toNNReal).measurable)
  · have hcont := s102_Meta_continuous hP0 C0 μ X ζ hcz
    have hnn : ∀ u : ℝ, 0 ≤ s102_Meta C0 Pw μ (X u.toNNReal ζ) := by
      intro u
      unfold s102_Meta
      have h1 : 0 ≤ ∫ x, jbracket x ^ Pw ∂μ := integral_nonneg fun x => Real.rpow_nonneg (by unfold jbracket; positivity) _
      have h2 : 0 ≤ (N : ℝ)⁻¹ * ∑ k, jbracket (X u.toNNReal ζ k) ^ Pw :=
        mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (by unfold jbracket; positivity) _)
      positivity
    calc ∫⁻ u in Icc (0 : ℝ) T, dualNormE r Pw (s102_etaf μ X ζ u)
        ≤ ∫⁻ u in Icc (0 : ℝ) T, ENNReal.ofReal (s102_Meta C0 Pw μ (X u.toNNReal ζ)) :=
          lintegral_mono fun u : ℝ => s102_dualNormE_le (hnn u) (fun f hf => hb (X u.toNNReal ζ) f hf)
      _ < ⊤ := (hcont.integrableOn_Icc (μ := volume)).lintegral_lt_top

end HRS.MS.R2Interp

end
