import HRS.MS.R26T8AB09c

/-!
# S8.2 T8A B09d: the old block bound for one realization and one `j`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

set_option maxHeartbeats 25600000 in
theorem r26t8a_b09_past (d : ℕ) (hd : 2 ≤ d) (a beta m M C Cf c : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hCf : 0 ≤ Cf) (hc : 0 < c) (T : ℝ) (hT : 0 < T)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (N : ℕ) (hN : 2 ≤ N)
    {Omega : Type} [mOmega : MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d) (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X) (a0 : ℝ) (ha0 : 0 ≤ a0)
    (alpha : MultiIndex d) (j : ℕ) :
    AEMeasurable (HRS.MS.S82BD.s82PastSup (HRS.MS.S82BD.s82Centered d N a beta m rho P X) T a0 j alpha) P ∧
    (∫⁻ ζ, (HRS.MS.S82BD.s82PastSup (HRS.MS.S82BD.s82Centered d N a beta m rho P X) T a0 j alpha ζ) ^ 2 ∂P) ^
        (1 / 2 : ℝ) ≤ ENNReal.ofReal
      ((2 * r26t8a_b09_B1 d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT +
        r26t8a_b09_B2 d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT +
        r26t8a_b09_B3 d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT) *
        HRS.MS.S82BD.s82Weight d m alpha * (N : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-c * (j : ℝ))) := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hW0 : 0 ≤ HRS.MS.S82BD.s82Weight d m alpha := by
    unfold HRS.MS.S82BD.s82Weight oscEigenvalue
    exact Real.rpow_nonneg (by positivity) _
  set w0 := HRS.MS.S82BD.s82Weight d m alpha with hw0
  have hNr : 0 ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hN0.le _
  have hE : 0 < Real.exp (-c * (j : ℝ)) := Real.exp_pos _
  have hj0' : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  by_cases hja : (j : ℝ) ≤ a0
  swap
  · -- empty old interval: the block is zero
    have hlt : a0 - (j : ℝ) < 0 := by linarith
    have hz : ∀ t w, HRS.MS.S82BD.s82Past (HRS.MS.S82BD.s82Centered d N a beta m rho P X) a0 j t alpha w = 0 := by
      intro t w
      unfold HRS.MS.S82BD.s82Past
      rw [max_eq_left (by linarith : a0 - ((j : ℝ) + 1) ≤ 0), max_eq_left hlt.le, Set.Icc_self]
      simp
    have h0 : HRS.MS.S82BD.s82PastSup (HRS.MS.S82BD.s82Centered d N a beta m rho P X) T a0 j alpha = fun _ => 0 := by
      funext w
      simp [HRS.MS.S82BD.s82PastSup, hz]
    rw [h0]
    refine ⟨aemeasurable_const, ?_⟩
    simp
  -- nonempty old interval `[l,h]`, `h = a0 - j`
  obtain ⟨F, W', hfilt⟩ := hX.filtered
  have hs1 := (Classical.choose_spec (r26t8a_old_endpoint d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT))
  have hs2 := (Classical.choose_spec (r26t8a_old_drift d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT))
  have hs3 := (Classical.choose_spec (r26t8a_old_noise d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT))
  set B1 := Classical.choose (r26t8a_old_endpoint d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT) with hB1
  set B2 := Classical.choose (r26t8a_old_drift d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT) with hB2
  set B3 := Classical.choose (r26t8a_old_noise d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT) with hB3
  have hB1n : 0 ≤ B1 := hs1.1
  have hB2n : 0 ≤ B2 := hs2.1
  have hB3n : 0 ≤ B3 := hs3.1
  set l : ℝ := max 0 (a0 - ((j : ℝ) + 1)) with hl
  set h : ℝ := max 0 (a0 - (j : ℝ)) with hh
  have hhe : h = a0 - (j : ℝ) := max_eq_right (by linarith)
  have hl0 : 0 ≤ l := le_max_left _ _
  have hlh : l ≤ h := max_le_max le_rfl (by linarith)
  have hha : h ≤ a0 - (j : ℝ) := hhe.le
  have hh1 : h - l ≤ 1 := by
    have : a0 - ((j : ℝ) + 1) ≤ l := le_max_right _ _
    linarith
  have hh0 : 0 ≤ h := hl0.trans hlh
  obtain ⟨h1hm, h1hb⟩ := hs1.2 rho hrho Psi hPsi horb N hN P X0 W X hX a0 ha0 alpha j h hh0 hha
  obtain ⟨h1lm, h1lb⟩ := hs1.2 rho hrho Psi hPsi horb N hN P X0 W X hX a0 ha0 alpha j l hl0 (hlh.trans hha)
  obtain ⟨h2m, h2b⟩ := hs2.2 rho hrho Psi hPsi horb N hN P X0 W X hX a0 ha0 alpha j l h hl0 hlh hha hh1
  obtain ⟨G, hGm, hGc, hGae, hGb⟩ := hs3.2 rho hrho Psi hPsi horb N hN P X0 W X hX a0 ha0 alpha F W' hfilt j l h hl0 hlh
    hha hh1
  have hid := r26t8a_old_block_identity d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb P X0 W X hX
    F W' hfilt T a0 hT ha0 alpha j G hGc hGae
  set S : ℝ → Omega → ℝ := fun t w =>
    HRS.MS.S82BD.s82Past (HRS.MS.S82BD.s82Centered d N a beta m rho P X) a0 j t alpha w with hS
  set Y0 : ℝ → Omega → ℝ := fun t w => -r26t8a_QAge a beta m rho Psi alpha 0 (a0 + t - h) (X h.toNNReal w) with hY0
  set Y1 : ℝ → Omega → ℝ := fun t w => r26t8a_QAge a beta m rho Psi alpha 0 (a0 + t - l) (X l.toNNReal w) with hY1
  set Y2 : ℝ → Omega → ℝ := fun t w =>
    ∫ r in Set.Icc l h, r26t8a_VAge a beta m rho Psi alpha 0 (a0 + t - r) (X r.toNNReal w) with hY2
  set Y : Fin 4 → ℝ → Omega → ℝ := ![Y0, Y1, Y2, G] with hY
  set e : ℝ := w0 * (N : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-c * (j : ℝ)) with he
  set b : Fin 4 → ℝ := ![B1 * e, B1 * e, B2 * e, B3 * e] with hb
  have he0 : 0 ≤ e := by positivity
  have hb0 : ∀ i, 0 ≤ b i := by
    intro i; fin_cases i <;> simp [hb] <;> positivity
  have hsum : ∀ᵐ w ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, S t w = ∑ i, Y i t w := by
    filter_upwards [hid] with w hw t ht
    rw [Fin.sum_univ_four]
    simp only [hS, hY, hY0, hY1, hY2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_three]
    rw [hw t ht]
  have hneg : (fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖Y0 t w‖ₑ) =
      fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖r26t8a_QAge a beta m rho Psi alpha 0 (a0 + (t : ℝ) - h) (X h.toNNReal w)‖ₑ := by
    funext w; simp [hY0]
  have hGsup : AEMeasurable (fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖G t w‖ₑ) P := by
    refine r26t8a_b04_sup_meas P T G (fun t ht => ?_) (Eventually.of_forall hGc)
    exact (hGm.comp (measurable_const.prodMk measurable_id)).aemeasurable
  have hm : ∀ i, AEMeasurable (fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖Y i t w‖ₑ) P := by
    intro i; fin_cases i
    · show AEMeasurable (fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖Y0 t w‖ₑ) P
      rw [hneg]; exact h1hm
    · exact h1lm
    · exact h2m
    · exact hGsup
  have hbd : ∀ i, (r26t8a_scalarSupSq P T (Y i)) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (b i) := by
    intro i; fin_cases i
    · show (r26t8a_scalarSupSq P T Y0) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (B1 * e)
      have : r26t8a_scalarSupSq P T Y0 = r26t8a_scalarSupSq P T (fun t w =>
          r26t8a_QAge a beta m rho Psi alpha 0 (a0 + t - h) (X h.toNNReal w)) := by
        unfold r26t8a_scalarSupSq; simp [hY0]
      rw [this]
      refine h1hb.trans (le_of_eq ?_)
      congr 1; simp only [he, hw0, mul_assoc]
    · show (r26t8a_scalarSupSq P T Y1) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (B1 * e)
      refine h1lb.trans (le_of_eq ?_)
      congr 1; simp only [he, hw0, mul_assoc]
    · show (r26t8a_scalarSupSq P T Y2) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (B2 * e)
      refine h2b.trans (le_of_eq ?_)
      congr 1; simp only [he, hw0, mul_assoc]
    · show (r26t8a_scalarSupSq P T G) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (B3 * e)
      refine hGb.trans (le_of_eq ?_)
      congr 1; simp only [he, hw0, mul_assoc]
  have hbl := r26t8a_b09_blocks P T S Y b hb0 hsum hm hbd
  have hsumb : ∑ i, b i = (2 * B1 + B2 + B3) * w0 * (N : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-c * (j : ℝ)) := by
    rw [Fin.sum_univ_four]; simp only [hb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_three, he]; ring
  rw [hsumb] at hbl
  refine ⟨?_, hbl⟩
  have hslY : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i, AEMeasurable (Y i t) P := by
    intro t ht i
    have hXm : ∀ s : ℝ≥0, Measurable (X s) := fun s => (hX.solution (s : ℝ)).adapted s
    have hk : 1 ≤ testOrder d := by unfold testOrder; omega
    have hQ : ∀ v : ℝ, 0 ≤ v → ∀ s : ℝ≥0, Measurable (fun w => r26t8a_QAge a beta m rho Psi alpha 0 v (X s w)) := by
      intro v hv s
      obtain ⟨A, hA⟩ : ∃ A, TestBound (testOrder d) A (r26t8a_ageTest a beta m rho alpha 0 v) :=
        ⟨_, horb.bound alpha v hv 0 (by norm_num)⟩
      exact (r26t8a_b04_Qmeas d N a beta M C hk rho Psi hPsi hA).comp (hXm s)
    fin_cases i
    · exact (hQ _ (by linarith [ht.1, ha0, hha, hj0']) _).neg.aemeasurable
    · exact (hQ _ (by linarith [ht.1, ha0, hha, hj0']) _).aemeasurable
    · exact r26t8a_b09_Vslice d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha 0
        (by norm_num) P X0 W X hX (fun r => a0 + t - r) (fun r => r) (continuous_const.sub continuous_id)
        continuous_id (Set.Icc l h) measurableSet_Icc h
        (fun r hr => ⟨by linarith [hr.2, ht.1, hha, hj0'], hl0.trans hr.1, hr.2⟩)
    · exact (hGm.comp (measurable_const.prodMk measurable_id)).aemeasurable
  have hslS : ∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (S t) P := by
    intro t ht
    have : AEMeasurable (fun w => ∑ i, Y i t w) P :=
      Finset.aemeasurable_fun_sum _ fun i _ => hslY t ht i
    exact this.congr (hsum.mono fun w hw => (hw t ht).symm)
  have hcS : ∀ᵐ w ∂P, ContinuousOn (fun t => S t w) (Set.Icc 0 T) := by
    filter_upwards [r26t8a_actual_block_continuity d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb P
      X0 W X hX T a0 hT ha0] with w hw using (hw alpha).2 j
  have hsup := r26t8a_b04_sup_meas P T S hslS hcS
  have heq : HRS.MS.S82BD.s82PastSup (HRS.MS.S82BD.s82Centered d N a beta m rho P X) T a0 j alpha =
      fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖S t w‖ₑ := by
    funext w
    simp only [HRS.MS.S82BD.s82PastSup, Real.enorm_eq_ofReal_abs, hS]
  rw [heq]; exact hsup

end HRS.MS.R26T8A

end
