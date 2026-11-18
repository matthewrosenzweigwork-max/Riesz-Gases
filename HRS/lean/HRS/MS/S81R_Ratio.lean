import HRS.MS.S81G_Conv

/-!
# S81R, packet R8b: the density ratio of the regularised to the singular Gibbs law

`s81r_ratio`: `Γ_M = Γ.withDensity (ofReal ∘ r)` with `r = q_M/q > 0` (ratio of the Lebesgue densities), and
`r ≥ Z/Z_M` `Γ`-almost everywhere (because `k_M ≤ g`).  `s81r_law_withDensity`: the law of `X₀` under the reweighted measure.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.MS.MfeConf HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl HRS.MS.S81G
open scoped ENNReal NNReal

namespace HRS.MS.S81R

variable {d N : ℕ} {D : Whole.WholeDyn d}

theorem s81r_ratio (H : S81Hyp D) (M : ℕ) :
    ∃ r : Whole.EucConfig d N → ℝ, Measurable r ∧ (∀ x, 0 < r x) ∧
      sb1Gam D (sb1kM d D.s M) N =
        (sb1Gam D (Whole.rieszKernel d D.s) N).withDensity (fun x => ENNReal.ofReal (r x)) ∧
      (∀ᵐ x ∂(sb1Gam D (Whole.rieszKernel d D.s) N),
        sb1Gz D (Whole.rieszKernel d D.s) N / sb1Gz D (sb1kM d D.s M) N ≤ r x) := by
  have hz := s81g_sing_gz_pos (N := N) H
  have hzM := s81g_reg_gz_pos (N := N) H M
  have hm : Measurable (sb1Gq D (Whole.rieszKernel d D.s) N) :=
    (s81g_Gw_meas (s81g_sing_meas H)).div_const _
  have hmM : Measurable (sb1Gq D (sb1kM d D.s M) N) :=
    (s81g_Gw_meas (s81g_reg_meas H M)).div_const _
  have hz' := hz.ne'
  have hzM' := hzM.ne'
  have hq0 : ∀ x, 0 < sb1Gq D (Whole.rieszKernel d D.s) N x := fun x => div_pos (Real.exp_pos _) hz
  have hqM0 : ∀ x, 0 < sb1Gq D (sb1kM d D.s M) N x := fun x => div_pos (Real.exp_pos _) hzM
  have hr : Measurable (fun x => sb1Gq D (sb1kM d D.s M) N x / sb1Gq D (Whole.rieszKernel d D.s) N x) :=
    hmM.div hm
  refine ⟨fun x => sb1Gq D (sb1kM d D.s M) N x / sb1Gq D (Whole.rieszKernel d D.s) N x,
    hr, fun x => div_pos (hqM0 x) (hq0 x), ?_, ?_⟩
  · unfold sb1Gam sb1Dm
    rw [← withDensity_mul _ hm.ennreal_ofReal hr.ennreal_ofReal]
    congr 1
    funext x
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (hq0 x).le]
    congr 1
    have := (hq0 x).ne'
    field_simp
  · have hae := sb1_sing_le D H.invβ_pos H.s_nonneg H.d_pos (N := N) M
    have hac : sb1Gam D (Whole.rieszKernel d D.s) N ≪ (volume : Measure (Whole.EucConfig d N)) := by
      unfold sb1Gam sb1Dm
      exact withDensity_absolutelyContinuous _ _
    refine hac.ae_le ?_
    filter_upwards [hae] with x hx
    unfold sb1Gw at hx
    have hge : sb1Gz D (Whole.rieszKernel d D.s) N / sb1Gz D (sb1kM d D.s M) N *
        sb1Gq D (Whole.rieszKernel d D.s) N x ≤ sb1Gq D (sb1kM d D.s M) N x := by
      unfold sb1Gq
      have : sb1Gz D (Whole.rieszKernel d D.s) N / sb1Gz D (sb1kM d D.s M) N *
          (Real.exp (-D.invβ⁻¹ * sb1Hs D (Whole.rieszKernel d D.s) N x) /
            sb1Gz D (Whole.rieszKernel d D.s) N) =
          Real.exp (-D.invβ⁻¹ * sb1Hs D (Whole.rieszKernel d D.s) N x) /
            sb1Gz D (sb1kM d D.s M) N := by
        field_simp
      rw [this]
      exact div_le_div_of_nonneg_right hx hzM.le
    exact (le_div_iff₀ (hq0 x)).2 hge

/-- the law of `X₀` under a reweighting of its initial value -/
theorem s81r_law_withDensity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {E : Type*}
    [MeasurableSpace E] {X0 : Ω → E} (hX : Measurable X0) (f : E → ℝ≥0∞) (hf : Measurable f) :
    (P.withDensity (fun ω => f (X0 ω))).map X0 = (P.map X0).withDensity f := by
  ext A hA
  rw [Measure.map_apply hX hA, withDensity_apply _ (hX hA), withDensity_apply _ hA,
    setLIntegral_map hA hf hX]

end HRS.MS.S81R
