import HRS.MS.Fp81S21WickG7

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HRS.Fp81.S21

/-- The finite half-Wick estimate for an orthonormal family of reference
`L²` inputs under a bounded Gaussian linear extension. -/
theorem fp81s21_wickG_orthonormal_family_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {n : ℕ} {f : Fin n → Lp ℝ 2 μ}
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (Kstar : ℝ)
    (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ m (v : Fin m → Lp ℝ 2 μ),
      HRS.IsCenteredGaussian (P.map fun ω => fun i => (L (v i)) ω))
    (hf : Orthonormal ℝ f) (c : Fin n → Fin n → ℝ) :
    ∫ ω, ((1 / 2 : ℝ) * ∑ i, ∑ j, c i j *
      ((L (f i)) ω * (L (f j)) ω -
        ∫ ω', (L (f i)) ω' * (L (f j)) ω' ∂P)) ^ 2 ∂P ≤
      (1 / 2 : ℝ) * Kstar ^ 4 * ∑ i, ∑ j, c i j ^ 2 := by
  classical
  let Y : Ω → Fin n → ℝ := fun ω i => (L (f i)) ω
  have hYm : AEMeasurable Y P :=
    aemeasurable_pi_iff.2 fun i =>
      (Lp.stronglyMeasurable (L (f i))).aestronglyMeasurable.aemeasurable
  have hJ : HRS.IsCenteredGaussian (P.map Y) := hJoint n f
  let g : Fin n → Ω → ℝ := fun i ω => (L (f i)) ω
  have hFamily : HRS.MS.R2Chaos.S94GFam P g := by
    refine ⟨?_, ?_⟩
    · intro i
      exact (Lp.stronglyMeasurable (L (f i))).aestronglyMeasurable.aemeasurable
    · intro α
      let M : (Fin n → ℝ) →L[ℝ] ℝ :=
        ∑ i, α i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i
      let V : Ω → ℝ := HRS.MS.R2Chaos.s94lin g α
      have hVeq : V = fun ω => M (Y ω) := by
        funext ω
        simp [V, HRS.MS.R2Chaos.s94lin, M, Y, g,
          ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.proj_apply, smul_eq_mul]
      have hgl : HasGaussianLaw Y P := ⟨hYm, hJ.1⟩
      have hVlaw : HasGaussianLaw V P := by
        rw [hVeq]
        exact hgl.map_fun M
      have hVmean : ∫ ω, V ω ∂P = 0 := by
        rw [hVeq]
        calc
          ∫ ω, M (Y ω) ∂P = ∫ y, M y ∂(P.map Y) :=
            (integral_map hYm M.continuous.aestronglyMeasurable).symm
          _ = 0 := hJ.2 M
      refine ⟨Var[V; P].toNNReal, ?_⟩
      calc
        P.map (HRS.MS.R2Chaos.s94lin g α) = P.map V := rfl
        _ = gaussianReal (∫ ω, V ω ∂P) Var[V; P].toNNReal := hVlaw.map_eq_gaussianReal
        _ = gaussianReal 0 _ := by rw [hVmean]
  have hCov : ∀ α : Fin n → ℝ,
      HRS.MS.R2Chaos.s94q P g α ≤ Kstar ^ 2 * ∑ i, α i ^ 2 := by
    intro α
    let v : Lp ℝ 2 μ := ∑ i, α i • f i
    have hLv : L v = ∑ i, α i • L (f i) := by
      simp [v, map_sum, map_smul]
    have hsum : (∑ i : Fin n, α i • L (f i) : Lp ℝ 2 P) =ᵐ[P]
        fun ω => ∑ i, α i * (L (f i)) ω := by
      have h1 : (∑ i : Fin n, α i • L (f i) : Lp ℝ 2 P) =ᵐ[P]
          fun ω => ∑ i, (α i • L (f i) : Lp ℝ 2 P) ω := by
        simpa using HRS.A33.a33_coeFn_sum (P := P) Finset.univ
          (fun i => α i • L (f i))
      have h2 : ∀ᵐ ω ∂P, ∀ i : Fin n,
          (α i • L (f i) : Lp ℝ 2 P) ω = α i * (L (f i)) ω := by
        rw [ae_all_iff]
        intro i
        filter_upwards [Lp.coeFn_smul (α i) (L (f i))] with ω hω
        simpa [smul_eq_mul] using hω
      filter_upwards [h1, h2] with ω hω hωi
      rw [hω]
      exact Finset.sum_congr rfl fun i _ => hωi i
    have hrepr : HRS.MS.R2Chaos.s94lin g α =ᵐ[P] fun ω => (L v) ω := by
      have hLvAE : (L v) =ᵐ[P]
          (∑ i : Fin n, α i • L (f i) : Lp ℝ 2 P) := by
        filter_upwards [ae_of_all P fun ω =>
          congrFun (congrArg (fun q : Lp ℝ 2 P => (q : Ω → ℝ)) hLv) ω] with ω hω
        exact hω
      filter_upwards [hLvAE, hsum] with ω hωv hωs
      simpa [HRS.MS.R2Chaos.s94lin, g] using (hωv.trans hωs).symm
    have hnormV : ‖v‖ ^ 2 = ∑ i, α i ^ 2 := by
      have horth : ∀ i j, inner ℝ (f i) (f j) = if i = j then 1 else 0 :=
        orthonormal_iff_ite.mp hf
      rw [← real_inner_self_eq_norm_sq, sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inner_sum]
      simp only [inner_smul_left, inner_smul_right, horth,
        RCLike.conj_to_real]
      simp [mul_ite, Finset.sum_ite_eq, sq]
    have hq : HRS.MS.R2Chaos.s94q P g α = ‖L v‖ ^ 2 := by
      unfold HRS.MS.R2Chaos.s94q
      calc
        ∫ ω, HRS.MS.R2Chaos.s94lin g α ω ^ 2 ∂P =
            ∫ ω, (L v) ω ^ 2 ∂P := by
              refine integral_congr_ae ?_
              filter_upwards [hrepr] with ω hω
              rw [hω]
        _ = inner ℝ (L v) (L v) := by
              rw [L2.inner_def]
              exact integral_congr_ae (ae_of_all P fun ω => by simp)
        _ = ‖L v‖ ^ 2 := real_inner_self_eq_norm_sq _
    have hLvBound : ‖L v‖ ≤ Kstar * ‖v‖ := by
      calc
        ‖L v‖ ≤ ‖L‖ * ‖v‖ := L.le_opNorm v
        _ ≤ Kstar * ‖v‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    have hK : 0 ≤ Kstar := le_trans (norm_nonneg L) hL
    have hsq : ‖L v‖ ^ 2 ≤ (Kstar * ‖v‖) ^ 2 := by
      have hA : 0 ≤ ‖L v‖ := norm_nonneg _
      have hB : 0 ≤ Kstar * ‖v‖ := mul_nonneg hK (norm_nonneg _)
      nlinarith
    calc
      HRS.MS.R2Chaos.s94q P g α = ‖L v‖ ^ 2 := hq
      _ ≤ Kstar ^ 2 * ∑ i, α i ^ 2 := by
        calc
          ‖L v‖ ^ 2 ≤ (Kstar * ‖v‖) ^ 2 := hsq
          _ = Kstar ^ 2 * ∑ i, α i ^ 2 := by rw [← hnormV]; ring
  exact fp81s21_wickG_finite_half_wick_bound hFamily Kstar hCov c

#print axioms fp81s21_wickG_orthonormal_family_bound

end HRS.Fp81.S21

end
