import HRS.MS.R26T8AB08b1

/-!
# S8.2 T8A B08b: `r26t8a_recent_block_identity` (Pro contract, verbatim)
Same scheme as B08a with `l = a0`, `h = b = a0 + t`, followed by the time shift `r ↦ a0 + r` of the drift integral.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

set_option maxHeartbeats 25600000 in
theorem r26t8a_recent_block_identity (d N : ℕ) (hd : 2≤d) (hN : 2≤N) (a beta m M C Cf c : ℝ)
    (ha : 0<a) (hbeta : 0<beta) (hM : 0≤M) (hC : 0≤C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) {Omega : Type} [mOmega : MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d)
    (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X)
    (F : Filtration ℝ mOmega) (W' : ℝ≥0 → Omega → (Fin N×Fin d) → ℝ)
    (hfilt : IsWholeFilteredSolution P F W' W X) (T a0 : ℝ) (hT : 0<T) (ha0 : 0≤a0)
    (alpha : MultiIndex d) (G : ℝ → Omega → ℝ)
    (hGc : ∀ w, ContinuousOn (fun t => G t w) (Set.Icc 0 T))
    (hG : ∀ t∈Set.Icc 0 T, G t =ᵐ[P] itoIntegral P F W'
      (r26t8a_clipIntegrand a0 (a0+t) (r26t8a_noiseAge a beta m rho Psi alpha X 0 (a0+t))) (a0+t)) :
    ∀ᵐ w ∂P, ∀ t∈Set.Icc 0 T,
      HRS.MS.S82BD.s82Recent (HRS.MS.S82BD.s82Centered d N a beta m rho P X) a0 t alpha w =
        -r26t8a_QAge a beta m rho Psi alpha 0 0 (X (a0+t).toNNReal w)+r26t8a_QAge a beta m rho Psi alpha 0 t (X a0.toNNReal w)+
          (∫ r in Set.Icc 0 t, r26t8a_VAge a beta m rho Psi alpha 0 (t-r) (X (a0+r).toNNReal w))+G t w := by
  classical
  have hfix : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ w ∂P,
      HRS.MS.S82BD.s82Recent (HRS.MS.S82BD.s82Centered d N a beta m rho P X) a0 t alpha w =
        -r26t8a_QAge a beta m rho Psi alpha 0 0 (X (a0 + t).toNNReal w) +
          r26t8a_QAge a beta m rho Psi alpha 0 t (X a0.toNNReal w) +
          (∫ r in Set.Icc 0 t, r26t8a_VAge a beta m rho Psi alpha 0 (t - r) (X (a0 + r).toNNReal w)) + G t w := by
    intro t ht
    have h1 := r26t8a_b08_fixed d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb P X0 W X hX F W'
      hfilt alpha (a0 + t) a0 (a0 + t) (by linarith [ht.1]) ha0 (by linarith [ht.1]) le_rfl
    filter_upwards [h1, hG t ht] with w hw1 hw2
    have hS : HRS.MS.S82BD.s82Recent (HRS.MS.S82BD.s82Centered d N a beta m rho P X) a0 t alpha w =
        ∫ r in Set.Icc a0 (a0 + t), scalarForcing a beta rho
          (propagatorW (critCoeff d a beta rho) r (a0 + t) (oscTestFun m alpha)) (X r.toNNReal w) := by
      show ∫ r in Set.Icc a0 (a0 + t), HRS.MS.S82BD.s82Centered d N a beta m rho P X alpha (a0 + t) r w = _
      refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      exact r26t8a_b07c_pointwise d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb P X0 W X hX alpha
        (a0 + t) r (ha0.trans hr.1) hr.2 w
    have hshift : ∫ r in Set.Icc a0 (a0 + t), r26t8a_VAge a beta m rho Psi alpha 0 (a0 + t - r) (X r.toNNReal w) =
        ∫ r in Set.Icc 0 t, r26t8a_VAge a beta m rho Psi alpha 0 (t - r) (X (a0 + r).toNNReal w) := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [ht.1]),
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.1]
      have := intervalIntegral.integral_comp_add_left
        (fun r => r26t8a_VAge a beta m rho Psi alpha 0 (a0 + t - r) (X r.toNNReal w)) (a := 0) (b := t) a0
      simp only [add_zero] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun r _ => ?_
      beta_reduce
      rw [show a0 + t - (a0 + r) = t - r by ring]
    rw [hS, hw1, hw2, hshift, sub_self, show a0 + t - a0 = t by ring]
  have hrat : ∀ᵐ w ∂P, ∀ q : ℚ, (q : ℝ) ∈ Set.Icc (0 : ℝ) T →
      HRS.MS.S82BD.s82Recent (HRS.MS.S82BD.s82Centered d N a beta m rho P X) a0 q alpha w =
        -r26t8a_QAge a beta m rho Psi alpha 0 0 (X (a0 + q).toNNReal w) +
          r26t8a_QAge a beta m rho Psi alpha 0 q (X a0.toNNReal w) +
          (∫ r in Set.Icc 0 (q : ℝ), r26t8a_VAge a beta m rho Psi alpha 0 (q - r) (X (a0 + r).toNNReal w)) + G q w := by
    rw [ae_all_iff]
    intro q
    by_cases hq : (q : ℝ) ∈ Set.Icc (0 : ℝ) T
    · filter_upwards [hfix q hq] with w hw _ using hw
    · exact Filter.Eventually.of_forall fun w hq' => absurd hq' hq
  have hcont7 := r26t8a_actual_block_continuity d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb P X0 W X
    hX T a0 hT ha0
  filter_upwards [hrat, hcont7, (hX.solution (a0 + T)).cont, (hX.solution (a0 + T)).no_collision] with w hw1 hw2 hw3 hw4
  intro t ht
  have hxc : Continuous fun r : ℝ => X r.toNNReal w := (continuous_pi hw3).comp continuous_real_toNNReal
  have hU : ∀ r ∈ Set.Icc (0 : ℝ) (a0 + T), X r.toNNReal w ∉ eucCollisionSet d N := fun r hr =>
    hw4 r.toNNReal (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2)
  have hRc := r26t8a_b08b_cont d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha
    (fun r => X r.toNNReal w) hxc a0 T hT.le ha0 hU
  have hLc := (hw2 alpha).1
  have hGw := hGc w
  have hEq : Set.EqOn
      (fun t : ℝ => HRS.MS.S82BD.s82Recent (HRS.MS.S82BD.s82Centered d N a beta m rho P X) a0 t alpha w)
      (fun t : ℝ => (-r26t8a_QAge a beta m rho Psi alpha 0 0 (X (a0 + t).toNNReal w) +
          r26t8a_QAge a beta m rho Psi alpha 0 t (X a0.toNNReal w) +
          (∫ r in Set.Icc 0 t, r26t8a_VAge a beta m rho Psi alpha 0 (t - r) (X (a0 + r).toNNReal w))) + G t w)
      (Set.Icc 0 T) := by
    refine Set.EqOn.of_subset_closure (s := Set.Ioo 0 T ∩ Set.range ((↑) : ℚ → ℝ)) ?_ hLc (hRc.add hGw)
      (fun t ht => ⟨ht.1.1.le, ht.1.2.le⟩) ?_
    · rintro t ⟨htI, q, rfl⟩
      exact hw1 q ⟨htI.1.le, htI.2.le⟩
    · have hd' : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
      have := hd'.open_subset_closure_inter (isOpen_Ioo (a := (0 : ℝ)) (b := T))
      intro t ht
      have hcl : closure (Set.Ioo (0 : ℝ) T) = Set.Icc 0 T := closure_Ioo hT.ne
      rw [← hcl] at ht
      exact closure_minimal this isClosed_closure ht
  exact hEq ht

end HRS.MS.R26T8A

end
