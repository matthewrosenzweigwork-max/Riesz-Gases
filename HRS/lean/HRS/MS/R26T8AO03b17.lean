import HRS.MS.R26T8AO03b16

/-!
# S8.2 T8A O03b (part 17): continuity of the corrected drift defect `D f` off collisions
`D f = scalarForcing f + L (Q f)` there; the scalar forcing is continuous (pair sums of the continuous commutator
source off the diagonal, and the continuous `aSource f`), and `L (Q f)` is continuous by O03b16.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U HRS.MS.S82W HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_o03b_Q_contDiffOn (N : ℕ) (hd : 2 ≤ d) (a beta M C : ℝ) (hC : 0 ≤ C) (rho : Euc d → ℝ)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    {A : ℝ} {f : Euc d → ℝ} (hf : TestBound (testOrder d) A f) :
    ContDiffOn ℝ 2 (r26t8a_correctedQ (N := N) a beta Psi f) (eucCollisionSet d N)ᶜ := by
  have hk : 1 ≤ testOrder d := by unfold testOrder; omega
  have hA := r26t8a_o03b_tb_nonneg hk hf
  exact (w_pairstat_jets (N := N) hd (hPsi.corrector f A hA hf) (mul_nonneg hC hA)
    (∫ Y, pairStatistic (Psi f) Y ∂(canonicalP d N a beta))).1

theorem r26t8a_o03b_SF_contOn (N : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) {A : ℝ} {f : Euc d → ℝ}
    (hf : TestBound (testOrder d) A f) :
    ContinuousOn (fun X : EucConfig d N => scalarForcing a beta rho f X) (eucCollisionSet d N)ᶜ := by
  have hgc : Continuous (gradient f) := by
    rw [r26t8a_gradient_eq_Rz]
    exact (r26t8a_Rz d).continuous.comp (hf.1.continuous_fderiv (by simp))
  have hacont := r26t8a_o03b_aSource_cont hd ha hbeta hrho hf
  set μ := HRS.Whole.withDensityReal rho with hμ
  intro X hX
  have hne : ∀ i j : Fin N, i ≠ j → X i - X j ≠ 0 := fun i j hij h => hX ⟨i, j, hij, sub_eq_zero.1 h⟩
  have hpair : ∀ i j : Fin N, i ≠ j → ContinuousAt (fun Y : EucConfig d N => hSource f (Y i) (Y j)) X := by
    intro i j hij
    have h1 : ContinuousAt (rieszKernelGrad d (criticalS d)) (X i - X j) :=
      ((HRS.MS.S113X2.s113a_rkg_contDiffOn (d := d) (criticalS d)).continuousOn.continuousAt
        (isOpen_ne.mem_nhds (hne i j hij)))
    have hsub : Continuous (fun Y : EucConfig d N => Y i - Y j) := (continuous_apply i).sub (continuous_apply j)
    have h2 : ContinuousAt (fun Y : EucConfig d N => rieszKernelGrad d (criticalS d) (Y i - Y j)) X :=
      ContinuousAt.comp (f := fun Y : EucConfig d N => Y i - Y j) h1 hsub.continuousAt
    have h3 : Continuous (fun Y : EucConfig d N => gradient f (Y i) - gradient f (Y j)) :=
      (hgc.comp (continuous_apply i)).sub (hgc.comp (continuous_apply j))
    exact h3.continuousAt.inner h2
  have hint : ∀ i : Fin N, Continuous (fun Y : EucConfig d N => ∫ y, hSource f (Y i) y ∂μ) := by
    intro i
    have : (fun Y : EucConfig d N => ∫ y, hSource f (Y i) y ∂μ) = fun Y => 2 * aSource μ f (Y i) := by
      funext Y; unfold aSource; ring
    rw [this]
    exact continuous_const.mul (hacont.comp (continuous_apply i))
  have hT : ContinuousAt (fun Y : EucConfig d N => centeredPairFunctional (hSource f) Y μ) X := by
    unfold centeredPairFunctional
    refine ContinuousAt.add (ContinuousAt.sub (ContinuousAt.mul continuousAt_const ?_)
      (ContinuousAt.mul continuousAt_const (ContinuousAt.mul continuousAt_const ?_))) continuousAt_const
    · exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j hj =>
        hpair i j (Finset.ne_of_mem_erase hj).symm
    · exact tendsto_finsetSum _ fun i _ => (hint i).continuousAt
  refine ContinuousAt.continuousWithinAt ?_
  unfold scalarForcing centerUnder
  exact ContinuousAt.mul continuousAt_const (ContinuousAt.sub hT continuousAt_const)

theorem r26t8a_o03b_D_contOn (N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta M C : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hC : 0 ≤ C) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    {A : ℝ} {f : Euc d → ℝ} (hf : TestBound (testOrder d) A f) :
    ContinuousOn (r26t8a_correctedD (N := N) a beta rho Psi f) (eucCollisionSet d N)ᶜ := by
  have hk : 1 ≤ testOrder d := by unfold testOrder; omega
  have hA := r26t8a_o03b_tb_nonneg hk hf
  have h1 := r26t8a_o03b_SF_contOn N hd a beta ha hbeta rho hrho hf
  have h2 := r26t8a_o03b_pG_contOn (N := N) a beta (r26t8a_o03b_Q_contDiffOn N hd a beta M C hC rho Psi hPsi hf)
  refine (h1.add h2).congr fun X hX => ?_
  have e := hPsi.identity N hN f A hA hf X hX
  simp only [Pi.add_apply]
  linarith

end HRS.MS.R26T8A
