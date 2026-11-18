import HRS.MS.SA12V1
import HRS.MS.ToriConvAux3
import HRS.MS.ToriCoefBAux6
import HRS.MS.ToriCoefBAux3

/-!
# S.A.12 C17, regularity of the periodic drift

For `PerSmooth` data with `PeriodicTimeSmooth T μ`: the drift `b σ = M ∇γ ⊛ μ σ - ∇V` is `C^1` in space for
every `σ ∈ [0,T]` and jointly continuous on `[0,T] × ℝ^d`.  Both are obtained from the cancellation
convolution `T_k g (x) = ∫_{Q_L} k(z)(g(x-z) - 1_N(z) g(x)) dz` of `ToriCoefB`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MS.ToriCoefB

variable {d : ℕ}

/-- Time regularity of the regularized periodic density: every spatial derivative is jointly continuous on the
time slab (verbatim from the Pro skeleton `SA12-CONSTRUCTION.lean`). -/
def PeriodicTimeSmooth (T : ℝ) (μ : ℝ → Euc d → ℝ) : Prop :=
  ∀ j : ℕ, ContinuousOn (fun q : ℝ × Euc d => iteratedFDeriv ℝ j (μ q.1) q.2) (Icc (0 : ℝ) T ×ˢ univ)

/-- Periodicity of iterated derivatives. -/
theorem sa12v_iter_periodic (L : ℝ) {u : Euc d → ℝ}
    (hu : ∀ (x : Euc d) (k : Fin d → ℤ), u (x + L • latticePt k) = u x) (j : ℕ) :
    ∀ (x : Euc d) (k : Fin d → ℤ),
      iteratedFDeriv ℝ j u (x + L • latticePt k) = iteratedFDeriv ℝ j u x := by
  intro x k
  have h1 : (fun w : Euc d => u (w + L • latticePt (d := d) k)) = u := funext fun w => hu w k
  have := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := u) j (L • latticePt (d := d) k) x
  rw [h1] at this
  exact this.symm

/-- Uniform bounds of `μ` and its first derivative on `[0,T] × ℝ^d`. -/
theorem sa12v_mu_bounds (L T : ℝ) (hL : 0 < L) (μ : ℝ → Euc d → ℝ)
    (hper : ∀ τ ∈ Icc (0 : ℝ) T, ∀ (x : Euc d) (k : Fin d → ℤ), μ τ (x + L • latticePt k) = μ τ x)
    (hTime : PeriodicTimeSmooth T μ) :
    ∃ B0 B1 : ℝ, ∀ σ ∈ Icc (0 : ℝ) T, ∀ y : Euc d,
      ‖μ σ y‖ ≤ B0 ∧ ‖fderiv ℝ (μ σ) y‖ ≤ B1 := by
  obtain ⟨B0, hB0⟩ := sa12v_bdd_param 0 T L hL
    (fun q : ℝ × Euc d => iteratedFDeriv ℝ 0 (μ q.1) q.2) (hTime 0)
    (fun σ hσ x k => sa12v_iter_periodic L (hper σ hσ) 0 x k)
  obtain ⟨B1, hB1⟩ := sa12v_bdd_param 0 T L hL
    (fun q : ℝ × Euc d => iteratedFDeriv ℝ 1 (μ q.1) q.2) (hTime 1)
    (fun σ hσ x k => sa12v_iter_periodic L (hper σ hσ) 1 x k)
  refine ⟨B0, B1, fun σ hσ y => ⟨?_, ?_⟩⟩
  · have := hB0 σ hσ y
    simpa only [norm_iteratedFDeriv_zero] using this
  · have := hB1 σ hσ y
    simpa only [norm_iteratedFDeriv_one] using this

/-- Joint continuity of the cancellation convolution in a parameter. -/
theorem sa12v_T_cont {L : ℝ} {k : Euc d → ℝ} {Kf : ℝ} (hk : tcb_Kern L k Kf) (g : ℝ → Euc d → ℝ)
    (t : ℝ) (hgc : ContinuousOn (fun p : ℝ × Euc d => g p.1 p.2) (Icc (0 : ℝ) t ×ˢ univ))
    (hdiff : ∀ σ ∈ Icc (0 : ℝ) t, Differentiable ℝ (g σ)) (B0 B1 : ℝ)
    (h0 : ∀ σ ∈ Icc (0 : ℝ) t, ∀ y, ‖g σ y‖ ≤ B0)
    (h1 : ∀ σ ∈ Icc (0 : ℝ) t, ∀ y, ‖fderiv ℝ (g σ) y‖ ≤ B1) :
    ContinuousOn (fun p : ℝ × Euc d => tcb_T L k (g p.1) p.2) (Icc (0 : ℝ) t ×ˢ univ) := by
  unfold tcb_T
  refine continuousOn_of_dominated (μ := volume.restrict (tcb_Q d L))
    (F := fun (p : ℝ × Euc d) (z : Euc d) => tcb_F k (g p.1) p.2 z)
    (bound := fun z => (tcb_N d).indicator (fun z => |k z| * ‖z‖ * B1) z + Kf * B0) ?_ ?_
    (tcb_dom_integrable hk B1 B0) ?_
  · intro p hp
    exact tcb_F_aesm hk (g p.1) (hdiff p.1 hp.1).continuous p.2 _
  · intro p hp
    filter_upwards [ae_restrict_mem (tcb_measurableSet_Q L)] with z hz
    refine (tcb_F_bound hk (g p.1) (hdiff p.1 hp.1) B1 (h1 p.1 hp.1) p.2 z hz).trans ?_
    have := mul_le_mul_of_nonneg_left (h0 p.1 hp.1 (p.2 - z)) hk.hKf
    linarith
  · refine Filter.Eventually.of_forall fun z => ?_
    unfold tcb_F
    have hshift : ContinuousOn (fun p : ℝ × Euc d => g p.1 (p.2 - z)) (Icc (0 : ℝ) t ×ˢ univ) := by
      have hmap : Set.MapsTo (fun p : ℝ × Euc d => (p.1, p.2 - z)) (Icc (0 : ℝ) t ×ˢ univ)
          (Icc (0 : ℝ) t ×ˢ univ) := fun p hp => ⟨hp.1, mem_univ _⟩
      exact hgc.comp (by fun_prop) hmap
    have hind : ContinuousOn (fun p : ℝ × Euc d => (tcb_N d).indicator (fun _ => g p.1 p.2) z)
        (Icc (0 : ℝ) t ×ˢ univ) := by
      by_cases hz : z ∈ tcb_N d
      · simpa only [Set.indicator_of_mem hz] using hgc
      · simpa only [Set.indicator_of_notMem hz] using continuousOn_const
    exact (hshift.sub hind).const_smul (k z)

/-- The coordinates of the cancellation convolution of the periodic Riesz gradient. -/
theorem sa12v_kern (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ Kf : ℝ, ∀ L : ℝ, 1 ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      ∀ i : Fin d, tcb_Kern L (fun z => gradient γ z i) Kf := by
  obtain ⟨C₀, A₀, -, -, h⟩ := tcb_kern_coord hd hs0 hsd
  exact ⟨C₀, fun L hL γ hγ i => (h L hL γ hγ i).1⟩


/-- Bound of the first `n+1` iterated derivatives of a smooth periodic function. -/
theorem sa12v_smooth_bdd (L : ℝ) (hL : 0 < L) {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u)
    (hper : ∀ (x : Euc d) (k : Fin d → ℤ), u (x + L • latticePt k) = u x) (n : ℕ) :
    ∃ Bd : ℝ, ∀ i ≤ n, ∀ y, ‖iteratedFDeriv ℝ i u y‖ ≤ Bd := by
  have hB : ∀ i : ℕ, ∃ B : ℝ, ∀ y, ‖iteratedFDeriv ℝ i u y‖ ≤ B := fun i =>
    sa12v_bdd L hL (iteratedFDeriv ℝ i u) (hu.continuous_iteratedFDeriv (by exact_mod_cast le_top))
      (sa12v_iter_periodic L hper i)
  choose Bf hBf using hB
  refine ⟨∑ i ∈ Finset.range (n + 1), |Bf i|, fun i hi y => ?_⟩
  refine (hBf i y).trans ?_
  refine (le_abs_self _).trans ?_
  exact Finset.single_le_sum (f := fun i => |Bf i|) (fun j _ => abs_nonneg _)
    (Finset.mem_range.2 (by omega))

/-- Value of `μ` as the zeroth iterated derivative: continuity in the parameters. -/
theorem sa12v_mu_joint (T : ℝ) (μ : ℝ → Euc d → ℝ) (hTime : PeriodicTimeSmooth T μ) :
    ContinuousOn (fun p : ℝ × Euc d => μ p.1 p.2) (Icc (0 : ℝ) T ×ˢ univ) := by
  have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Euc d) ℝ (fun i => i.elim0)).continuous.comp_continuousOn
    (hTime 0)
  refine h.congr fun p _ => ?_
  simp [iteratedFDeriv_zero_apply]

theorem sa12v_drift (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {T L : ℝ}
    {γ : Euc d → ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ν : ℝ} {μ : ℝ → Euc d → ℝ} {V : Euc d → ℝ}
    {b : ℝ → Euc d → Euc d} (hP : PerSmooth s T L γ M ν μ V b) (hTime : PeriodicTimeSmooth T μ) :
    (∀ σ ∈ Icc (0 : ℝ) T, ContDiff ℝ 1 (b σ)) ∧
      ContinuousOn (fun p : ℝ × Euc d => b p.1 p.2) (Icc (0 : ℝ) T ×ˢ univ) := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hP.hL
  obtain ⟨Kf, hKf⟩ := sa12v_kern hd hs0 hsd
  have hk := fun i => hKf L hP.hL γ hP.hγ i
  obtain ⟨B0, B1, hB⟩ := sa12v_mu_bounds L T hL0 μ hP.μ_periodic hTime
  set Tm : Euc d →L[ℝ] Euc d := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M) with hTm
  have hTmv : ∀ v, Tm v = Torus.matVec M v := fun v => rfl
  have hgradV : ContDiff ℝ 1 (gradient V) := by
    have := tcb_grad_contDiff V 0 hP.V_smooth
    simpa using this
  -- the vector field `F σ x = convGradConvL`
  have hFc : ∀ σ ∈ Icc (0 : ℝ) T, ∀ x : Euc d,
      b σ x = Tm (∑ i, tcb_T L (fun z => gradient γ z i) (μ σ) x •
        (EuclideanSpace.single i (1 : ℝ) : Euc d)) - gradient V x := by
    intro σ hσ x
    rw [hP.b_eq σ hσ]
    show Torus.matVec M (convGradConvL L (gradient γ) (μ σ) x) - gradient V x = _
    rw [hTmv]
    congr 2
    ext c
    rw [tcb_conv_coord (gradient γ) hk (μ σ) ((hP.μ_smooth σ hσ).of_le (by exact_mod_cast le_top))
      B0 B1 (fun y => (hB σ hσ y).1) (fun y => (hB σ hσ y).2) x c]
    simp [Pi.single_apply]
  constructor
  · intro σ hσ
    have hμs := hP.μ_smooth σ hσ
    obtain ⟨Bd, hBd⟩ := sa12v_smooth_bdd L hL0 hμs (hP.μ_periodic σ hσ) 3
    have hTi : ∀ i : Fin d, ContDiff ℝ 1 (tcb_T L (fun z => gradient γ z i) (μ σ)) := by
      intro i
      have := HRS.MS.ToriConv.tcv_T_contDiff (hk i) Bd 1 ℝ (μ σ)
        (hμs.of_le (by simp)) (fun j hj y => hBd j (by omega) y)
      simpa using this
    have hF : ContDiff ℝ 1 (fun x => ∑ i, tcb_T L (fun z => gradient γ z i) (μ σ) x •
        (EuclideanSpace.single i (1 : ℝ) : Euc d)) :=
      ContDiff.sum fun i _ => (hTi i).smul contDiff_const
    have : b σ = fun x => Tm (∑ i, tcb_T L (fun z => gradient γ z i) (μ σ) x •
        (EuclideanSpace.single i (1 : ℝ) : Euc d)) - gradient V x := funext (hFc σ hσ)
    rw [this]
    exact (Tm.contDiff.comp hF).sub hgradV
  · have hTc : ∀ i : Fin d, ContinuousOn
        (fun p : ℝ × Euc d => tcb_T L (fun z => gradient γ z i) (μ p.1) p.2)
        (Icc (0 : ℝ) T ×ˢ univ) := fun i =>
      sa12v_T_cont (hk i) μ T (sa12v_mu_joint T μ hTime)
        (fun σ hσ => (hP.μ_smooth σ hσ).differentiable (by simp)) B0 B1
        (fun σ hσ y => (hB σ hσ y).1) (fun σ hσ y => (hB σ hσ y).2)
    have hF : ContinuousOn (fun p : ℝ × Euc d => Tm (∑ i, tcb_T L (fun z => gradient γ z i) (μ p.1) p.2 •
        (EuclideanSpace.single i (1 : ℝ) : Euc d)) - gradient V p.2) (Icc (0 : ℝ) T ×ˢ univ) := by
      refine (Tm.continuous.comp_continuousOn ?_).sub ?_
      · exact continuousOn_finsetSum _ fun i _ => (hTc i).smul continuousOn_const
      · exact (hgradV.continuous.comp continuous_snd).continuousOn
    exact hF.congr fun p hp => hFc p.1 hp.1 p.2

end HRS.MH.AdjointRd.Phase2SA12Construction
