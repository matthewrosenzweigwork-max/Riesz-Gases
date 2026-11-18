import HRS.MS.R26T8AB08a2

/-!
# S8.2 T8A B08a: `r26t8a_old_block_identity` (Pro contract, verbatim)
At every rational observed time `t` the fixed-horizon identity (B08a1, from O06 and B07c) holds almost surely, with
`G t = ∫_l^h noise dW` (`s07b_local`); the two sides are a.s. continuous in `t` on `[0,T]` (B07b, B08a2, `hGc`), hence
equal for all `t`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

set_option maxHeartbeats 25600000 in
theorem r26t8a_old_block_identity (d N : ℕ) (hd : 2≤d) (hN : 2≤N) (a beta m M C Cf c : ℝ)
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
    (alpha : MultiIndex d) (j : ℕ)
    (G : ℝ → Omega → ℝ) (hGc : ∀ w, ContinuousOn (fun t => G t w) (Set.Icc 0 T))
    (hG : ∀ t∈Set.Icc 0 T, G t =ᵐ[P] itoIntegral P F W'
      (r26t8a_clipIntegrand (max 0 (a0-((j:ℝ)+1))) (max 0 (a0-(j:ℝ)))
        (r26t8a_noiseAge a beta m rho Psi alpha X 0 (a0+t))) (max 0 (a0-(j:ℝ)))) :
    ∀ᵐ w ∂P, ∀ t∈Set.Icc 0 T,
      let l := max 0 (a0-((j:ℝ)+1))
      let h := max 0 (a0-(j:ℝ))
      HRS.MS.S82BD.s82Past (HRS.MS.S82BD.s82Centered d N a beta m rho P X) a0 j t alpha w =
        -r26t8a_QAge a beta m rho Psi alpha 0 (a0+t-h) (X h.toNNReal w)+r26t8a_QAge a beta m rho Psi alpha 0 (a0+t-l) (X l.toNNReal w)+
          (∫ r in Set.Icc l h, r26t8a_VAge a beta m rho Psi alpha 0 (a0+t-r) (X r.toNNReal w))+G t w := by
  classical
  set l : ℝ := max 0 (a0 - ((j : ℝ) + 1)) with hl
  set h : ℝ := max 0 (a0 - (j : ℝ)) with hh
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hl0 : 0 ≤ l := le_max_left _ _
  have hlh : l ≤ h := max_le_max le_rfl (by linarith)
  have hha : h ≤ a0 := max_le ha0 (by linarith)
  -- the pointwise formula for the past block
  have hPast : ∀ t : ℝ, 0 ≤ t → ∀ w, HRS.MS.S82BD.s82Past (HRS.MS.S82BD.s82Centered d N a beta m rho P X) a0 j t alpha w =
      ∫ r in Set.Icc l h, scalarForcing a beta rho
        (propagatorW (critCoeff d a beta rho) r (a0 + t) (oscTestFun m alpha)) (X r.toNNReal w) := by
    intro t ht w
    show ∫ r in Set.Icc l h, HRS.MS.S82BD.s82Centered d N a beta m rho P X alpha (a0 + t) r w = _
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    exact r26t8a_b07c_pointwise d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb P X0 W X hX alpha
      (a0 + t) r (hl0.trans hr.1) (by linarith [hr.2, hha, ht]) w
  -- the identity at each fixed time
  have hfix : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ w ∂P,
      HRS.MS.S82BD.s82Past (HRS.MS.S82BD.s82Centered d N a beta m rho P X) a0 j t alpha w =
        -r26t8a_QAge a beta m rho Psi alpha 0 (a0 + t - h) (X h.toNNReal w) +
          r26t8a_QAge a beta m rho Psi alpha 0 (a0 + t - l) (X l.toNNReal w) +
          (∫ r in Set.Icc l h, r26t8a_VAge a beta m rho Psi alpha 0 (a0 + t - r) (X r.toNNReal w)) + G t w := by
    intro t ht
    have h1 := r26t8a_b08_fixed d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb P X0 W X hX F W'
      hfilt alpha (a0 + t) l h (by linarith [ht.1]) hl0 hlh (by linarith [ht.1])
    filter_upwards [h1, hG t ht] with w hw1 hw2
    rw [hPast t ht.1 w, hw1, hw2]
  have hrat : ∀ᵐ w ∂P, ∀ q : ℚ, (q : ℝ) ∈ Set.Icc (0 : ℝ) T →
      HRS.MS.S82BD.s82Past (HRS.MS.S82BD.s82Centered d N a beta m rho P X) a0 j q alpha w =
        -r26t8a_QAge a beta m rho Psi alpha 0 (a0 + q - h) (X h.toNNReal w) +
          r26t8a_QAge a beta m rho Psi alpha 0 (a0 + q - l) (X l.toNNReal w) +
          (∫ r in Set.Icc l h, r26t8a_VAge a beta m rho Psi alpha 0 (a0 + q - r) (X r.toNNReal w)) + G q w := by
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
  have hRc := r26t8a_b08_cont d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha
    (fun r => X r.toNNReal w) hxc a0 T l h hT.le hl0 hlh hha hU
  have hLc := (hw2 alpha).2 j
  have hGw := hGc w
  have hEq : Set.EqOn
      (fun t : ℝ => HRS.MS.S82BD.s82Past (HRS.MS.S82BD.s82Centered d N a beta m rho P X) a0 j t alpha w)
      (fun t : ℝ => (-r26t8a_QAge a beta m rho Psi alpha 0 (a0 + t - h) (X h.toNNReal w) +
          r26t8a_QAge a beta m rho Psi alpha 0 (a0 + t - l) (X l.toNNReal w) +
          (∫ r in Set.Icc l h, r26t8a_VAge a beta m rho Psi alpha 0 (a0 + t - r) (X r.toNNReal w))) + G t w)
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
