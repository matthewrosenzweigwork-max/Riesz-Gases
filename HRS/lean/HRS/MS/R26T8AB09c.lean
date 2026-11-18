import HRS.MS.R26T8AB09b
import HRS.MS.R26T8AB04
import HRS.MS.R26T8AB03
import HRS.MS.R26T8AB05
import HRS.MS.R26T8AB06
import HRS.MS.R26T8AB02
import HRS.MS.R26T8AB07b
import HRS.MS.R26T8AB08a
import HRS.MS.R26T8AB08b
import HRS.MS.R26T8AV08b

/-!
# S8.2 T8A B09c: the six block constants, and the recent block bound for one realization
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

section Consts
variable (d : ℕ) (hd : 2 ≤ d) (a beta m M C Cf c : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
  (hC : 0 ≤ C) (hCf : 0 ≤ Cf) (hc : 0 < c) (T : ℝ) (hT : 0 < T)

def r26t8a_b09_B1 : ℝ := Classical.choose (r26t8a_old_endpoint d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT)
def r26t8a_b09_B2 : ℝ := Classical.choose (r26t8a_old_drift d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT)
def r26t8a_b09_B3 : ℝ := Classical.choose (r26t8a_old_noise d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT)
def r26t8a_b09_B4 : ℝ := Classical.choose (r26t8a_recent_endpoint d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT)
def r26t8a_b09_B5 : ℝ := Classical.choose (r26t8a_recent_drift d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT)
def r26t8a_b09_B6 : ℝ := Classical.choose (r26t8a_recent_noise d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT)

end Consts

set_option maxHeartbeats 25600000 in
theorem r26t8a_b09_recent (d : ℕ) (hd : 2 ≤ d) (a beta m M C Cf c : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hCf : 0 ≤ Cf) (hc : 0 < c) (T : ℝ) (hT : 0 < T)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (N : ℕ) (hN : 2 ≤ N)
    {Omega : Type} [mOmega : MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d) (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X) (a0 : ℝ) (ha0 : 0 ≤ a0)
    (alpha : MultiIndex d) :
    AEMeasurable (HRS.MS.S82BD.s82RecentSup (HRS.MS.S82BD.s82Centered d N a beta m rho P X) T a0 alpha) P ∧
    (∫⁻ ζ, (HRS.MS.S82BD.s82RecentSup (HRS.MS.S82BD.s82Centered d N a beta m rho P X) T a0 alpha ζ) ^ 2 ∂P) ^
        (1 / 2 : ℝ) ≤ ENNReal.ofReal
      ((r26t8a_b09_B4 d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT +
        r26t8a_b09_B5 d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT +
        r26t8a_b09_B6 d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT) *
        HRS.MS.S82BD.s82Weight d m alpha * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  classical
  obtain ⟨F, W', hfilt⟩ := hX.filtered
  have hrev := r26t8a_canonical_reversible_windows d N hd hN a beta ha hbeta P X0 W X hX
  have hs4 := (Classical.choose_spec (r26t8a_recent_endpoint d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT))
  have hs5 := (Classical.choose_spec (r26t8a_recent_drift d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT))
  have hs6 := (Classical.choose_spec (r26t8a_recent_noise d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT))
  obtain ⟨h4m, h4b⟩ := hs4.2 rho hrho Psi hPsi horb N hN P X0 W X hX a0 ha0 alpha hrev
  obtain ⟨h5m, h5b⟩ := hs5.2 rho hrho Psi hPsi horb N hN P X0 W X hX a0 ha0 alpha
  obtain ⟨G, hGm, hGc, hGae, hGb⟩ := hs6.2 rho hrho Psi hPsi horb N hN P X0 W X hX a0 ha0 alpha F W' hfilt
  have hid := r26t8a_recent_block_identity d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb P X0 W X hX
    F W' hfilt T a0 hT ha0 alpha G hGc hGae
  set B4 := r26t8a_b09_B4 d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT with hB4
  set B5 := r26t8a_b09_B5 d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT with hB5
  set B6 := r26t8a_b09_B6 d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT with hB6
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hW0 : 0 ≤ HRS.MS.S82BD.s82Weight d m alpha := by
    unfold HRS.MS.S82BD.s82Weight oscEigenvalue
    exact Real.rpow_nonneg (by positivity) _
  set w0 := HRS.MS.S82BD.s82Weight d m alpha with hw0
  have hNr : 0 ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hN0.le _
  have hB4n : 0 ≤ B4 := hs4.1
  have hB5n : 0 ≤ B5 := hs5.1
  have hB6n : 0 ≤ B6 := hs6.1
  set S : ℝ → Omega → ℝ := fun t w =>
    HRS.MS.S82BD.s82Recent (HRS.MS.S82BD.s82Centered d N a beta m rho P X) a0 t alpha w with hS
  set Y4 : ℝ → Omega → ℝ := fun t w =>
    -r26t8a_QAge a beta m rho Psi alpha 0 0 (X (a0 + t).toNNReal w) +
      r26t8a_QAge a beta m rho Psi alpha 0 t (X a0.toNNReal w) with hY4
  set Y5 : ℝ → Omega → ℝ := fun t w =>
    ∫ r in Set.Icc 0 t, r26t8a_VAge a beta m rho Psi alpha 0 (t - r) (X (a0 + r).toNNReal w) with hY5
  set Y : Fin 3 → ℝ → Omega → ℝ := ![Y4, Y5, G] with hY
  set b : Fin 3 → ℝ := ![B4 * w0 * (N : ℝ) ^ (-(1 / 2 : ℝ)), B5 * w0 * (N : ℝ) ^ (-(1 / 2 : ℝ)),
    B6 * w0 * (N : ℝ) ^ (-(1 / 2 : ℝ))] with hb
  have hb0 : ∀ i, 0 ≤ b i := by
    intro i; fin_cases i <;> simp [hb] <;> positivity
  have hsum : ∀ᵐ w ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, S t w = ∑ i, Y i t w := by
    filter_upwards [hid] with w hw t ht
    rw [Fin.sum_univ_three]
    simp only [hS, hY, hY4, hY5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [hw t ht]
  have hGsup : AEMeasurable (fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖G t w‖ₑ) P := by
    refine r26t8a_b04_sup_meas P T G (fun t ht => ?_) (Eventually.of_forall hGc)
    exact (hGm.comp (measurable_const.prodMk measurable_id)).aemeasurable
  have hm : ∀ i, AEMeasurable (fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖Y i t w‖ₑ) P := by
    intro i; fin_cases i
    · exact h4m
    · exact h5m
    · exact hGsup
  have hbd : ∀ i, (r26t8a_scalarSupSq P T (Y i)) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (b i) := by
    intro i; fin_cases i
    · exact h4b
    · exact h5b
    · exact hGb
  have hbl := r26t8a_b09_blocks P T S Y b hb0 hsum hm hbd
  have hsumb : ∑ i, b i = (B4 + B5 + B6) * w0 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Fin.sum_univ_three]; simp only [hb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]; ring
  rw [hsumb] at hbl
  refine ⟨?_, hbl⟩
  -- measurability of the actual supremum
  have hslY : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i, AEMeasurable (Y i t) P := by
    intro t ht i
    fin_cases i
    · exact (r26t8a_b04_cont d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha P X0 W X hX
        a0 T ha0 hT).1 t ht
    · exact r26t8a_b09_Vslice d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha 0
        (by norm_num) P X0 W X hX (fun r => t - r) (fun r => a0 + r) (continuous_const.sub continuous_id)
        (continuous_const.add continuous_id) (Set.Icc 0 t) measurableSet_Icc (a0 + t)
        (fun r hr => ⟨by linarith [hr.2], by linarith [hr.1], by linarith [hr.2]⟩)
    · exact (hGm.comp (measurable_const.prodMk measurable_id)).aemeasurable
  have hslS : ∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (S t) P := by
    intro t ht
    have : AEMeasurable (fun w => ∑ i, Y i t w) P :=
      Finset.aemeasurable_fun_sum _ fun i _ => hslY t ht i
    exact this.congr (hsum.mono fun w hw => (hw t ht).symm)
  have hcS : ∀ᵐ w ∂P, ContinuousOn (fun t => S t w) (Set.Icc 0 T) := by
    filter_upwards [r26t8a_actual_block_continuity d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb P
      X0 W X hX T a0 hT ha0] with w hw using (hw alpha).1
  have hsup := r26t8a_b04_sup_meas P T S hslS hcS
  have heq : HRS.MS.S82BD.s82RecentSup (HRS.MS.S82BD.s82Centered d N a beta m rho P X) T a0 alpha =
      fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖S t w‖ₑ := by
    funext w
    simp only [HRS.MS.S82BD.s82RecentSup, Real.enorm_eq_ofReal_abs, hS]
  rw [heq]; exact hsup

end HRS.MS.R26T8A

end
