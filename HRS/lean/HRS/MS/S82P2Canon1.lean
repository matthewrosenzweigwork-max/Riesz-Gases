import HRS.MS.S82P2Pair5
import HRS.MP.RdRemainder

/-!
# S8.2 (S82P2): `canonicalP` is a probability measure under the domination field (UNCOMPILED DRAFT)
`HRS.Whole.canonicalGibbs` is `ofReal(Z)⁻¹ • withDensity`; if `Z = 0` (junk) the measure would have infinite
mass, contradicting `canonicalP ≤ C • unpinnedReference` with `unpinnedReference` a probability measure.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

lemma s82p2_canonicalP_prob {d N : ℕ} {a beta C0 : ℝ} {rho q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    (hW : WeakReferenceSetup d a beta rho q h C0) (hN : 2 ≤ N) :
    IsProbabilityMeasure (canonicalP d N a beta) := by
  have hdom := hW.domination N hN
  have hprob0 := hW.probability N hN 0 N (by omega) (by omega) (fun i : Fin 0 => i.elim0)
  have hfin : canonicalP d N a beta Set.univ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (hdom Set.univ)
    have : (unpinnedReference q h (HRS.Whole.withDensityReal rho) beta N) Set.univ = 1 :=
      hprob0.measure_univ
    rw [Measure.smul_apply, smul_eq_mul, this, mul_one]
    exact ENNReal.ofReal_ne_top
  -- measurability of the weight
  have hgm : Measurable (HRS.Whole.rieszKernel d (criticalS d)) := HRS.MP.RdRem.mrr_measurable_rieszKernel _
  have hHm : Measurable (fun X : EucConfig d N =>
      -beta * HRS.Whole.canonicalHamiltonian (HRS.Whole.rieszKernel d (criticalS d)) (HRS.Whole.confinement a) X) := by
    refine measurable_const.mul ?_
    unfold HRS.Whole.canonicalHamiltonian
    refine (Finset.measurable_sum _ fun i _ => ?_).add (measurable_const.mul
      (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_))
    · unfold HRS.Whole.confinement
      exact ((measurable_const.mul ((measurable_pi_apply i).norm.pow_const 2)).div_const _)
    · exact hgm.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
  have hZ0 : 0 ≤ HRS.Whole.canonicalPartition (HRS.Whole.rieszKernel d (criticalS d)) (HRS.Whole.confinement a) N beta :=
    integral_nonneg fun X => (Real.exp_pos _).le
  unfold canonicalP at hfin ⊢
  unfold HRS.Whole.canonicalGibbs at hfin ⊢
  by_cases hZ : 0 < HRS.Whole.canonicalPartition (HRS.Whole.rieszKernel d (criticalS d)) (HRS.Whole.confinement a) N beta
  · have hint : Integrable (fun X : EucConfig d N => Real.exp (-beta *
        HRS.Whole.canonicalHamiltonian (HRS.Whole.rieszKernel d (criticalS d)) (HRS.Whole.confinement a) X)) := by
      by_contra hni
      unfold HRS.Whole.canonicalPartition at hZ
      rw [integral_undef hni] at hZ
      exact lt_irrefl _ hZ
    refine ⟨?_⟩
    rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      smul_eq_mul]
    have := ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)
    unfold HRS.Whole.canonicalPartition at hZ ⊢
    rw [← this]
    exact ENNReal.inv_mul_cancel (by simpa using hZ) ENNReal.ofReal_ne_top
  · exfalso
    have hZz : HRS.Whole.canonicalPartition (HRS.Whole.rieszKernel d (criticalS d)) (HRS.Whole.confinement a) N beta = 0 :=
      le_antisymm (not_lt.1 hZ) hZ0
    rw [hZz, ENNReal.ofReal_zero, ENNReal.inv_zero, Measure.smul_apply, smul_eq_mul] at hfin
    have hW0 : ((volume : Measure (EucConfig d N)).withDensity fun X => ENNReal.ofReal
        (Real.exp (-beta * HRS.Whole.canonicalHamiltonian (HRS.Whole.rieszKernel d (criticalS d))
          (HRS.Whole.confinement a) X))) Set.univ = 0 := by
      by_contra hne
      exact hfin (ENNReal.top_mul hne)
    have hexpm : Measurable (fun X : EucConfig d N => ENNReal.ofReal (Real.exp (-beta *
        HRS.Whole.canonicalHamiltonian (HRS.Whole.rieszKernel d (criticalS d))
          (HRS.Whole.confinement a) X))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hHm)
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_eq_zero_iff hexpm] at hW0
    have hae : ∀ᵐ X ∂(volume : Measure (EucConfig d N)), False := by
      filter_upwards [hW0] with X hX
      have : ENNReal.ofReal (Real.exp (-beta * HRS.Whole.canonicalHamiltonian (HRS.Whole.rieszKernel d (criticalS d))
          (HRS.Whole.confinement a) X)) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _
      exact this hX
    haveI : NeZero (volume : Measure (EucConfig d N)) := inferInstance
    obtain ⟨X, hX⟩ := Filter.Eventually.exists hae
    exact hX

end HRS.MS.S82P2
