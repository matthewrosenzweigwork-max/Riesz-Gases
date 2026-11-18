import HRS.MS.SA12V3
import HRS.MS.FcauAux2
import HRS.MS.UniqN0b
import HRS.MS.UniqT3

/-!
# S.A.12 C17, the spatial identity at a fixed time

For `f` smooth periodic, `bb` of class `C^1`, `m` smooth periodic and `ψ ∈ C_c^∞`:
`∫ f · A ψ = ∫ ψ (νΔf + ⟨bb,∇f⟩ - 𝒢_L[f])` with `A = weakOpPer` at frozen coefficients.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd

variable {d : ℕ}

/-- The test operator `weakOpPer` at frozen coefficients. -/
def sa12vA (L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (m : Euc d → ℝ)
    (bb : Euc d → Euc d) (ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  ν * Laplacian.laplacian ψ x - movDiv (fun y => ψ y • bb y) x -
    (centeredBox d L).indicator (nonlocalTestPer L γ M m ψ) x

theorem sa12v_lap_cc {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) :
    Continuous (Laplacian.laplacian ψ) ∧ HasCompactSupport (Laplacian.laplacian ψ) := by
  have hc : HRS.MS.UniqT3.Cc ψ := ⟨hψ.1, hψ.2⟩
  have hfun : Laplacian.laplacian ψ = fun y => ∑ i, HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i ψ) y :=
    funext fun y => HRS.MS.UniqT3.lap_eq (hψ.1.of_le (by simp)) y
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact continuous_finsetSum _ fun i _ => ((hc.D1 i).D1 i).cont
  · refine HasCompactSupport.intro (K := tsupport ψ) hψ.2 fun x hx => ?_
    have hev : ψ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.1 hx
    rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds]
    simp

theorem sa12v_movDiv_cc {Φ : Euc d → Euc d} (hΦ : ContDiff ℝ 1 Φ) (hc : HasCompactSupport Φ) :
    Continuous (movDiv Φ) ∧ HasCompactSupport (movDiv Φ) := by
  refine ⟨?_, ?_⟩
  · unfold movDiv
    refine continuous_finsetSum _ fun i _ => ?_
    exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp
      ((hΦ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  · refine HasCompactSupport.intro (K := tsupport Φ) hc fun x hx => ?_
    have h0 : fderiv ℝ Φ x = 0 := by
      by_contra h
      exact hx ((support_fderiv_subset (𝕜 := ℝ)) (Function.mem_support.2 h))
    simp [movDiv, h0]

theorem sa12v_fderiv_coord {Φ : Euc d → Euc d} {x : Euc d} (hΦ : DifferentiableAt ℝ Φ x) (v : Euc d)
    (i : Fin d) : fderiv ℝ Φ x v i = fderiv ℝ (fun y => Φ y i) x v := by
  have h2 : fderiv ℝ (fun w => Φ w i) x = (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp (fderiv ℝ Φ x) :=
    ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp x hΦ.hasFDerivAt).fderiv
  rw [h2]
  rfl

/-- Integration by parts for the transport term. -/
theorem sa12v_transport_ibp {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) {bb : Euc d → Euc d}
    (hbb : ContDiff ℝ 1 bb) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) :
    ∫ x, ψ x * inner ℝ (bb x) (gradient f x) = -∫ x, f x * movDiv (fun y => ψ y • bb y) x := by
  have hΦ : ContDiff ℝ 1 (fun y => ψ y • bb y) := (hψ.1.of_le (by simp)).smul hbb
  have hΦc : HasCompactSupport (fun y => ψ y • bb y) := hψ.2.smul_right
  have hF : ∀ i : Fin d, ContDiff ℝ 1 (fun y => ψ y * bb y i) := fun i =>
    (hψ.1.of_le (by simp)).mul ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff.comp hbb)
  have hFc : ∀ i : Fin d, HasCompactSupport (fun y => ψ y * bb y i) := fun i =>
    hψ.2.mul_right
  have hterm : ∀ i : Fin d, ∫ x, ψ x * (bb x i * fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))) =
      -∫ x, f x * fderiv ℝ (fun y => (ψ y • bb y) i) x (EuclideanSpace.single i (1 : ℝ)) := by
    intro i
    have h := HRS.MS.UniqN0.n0_ibp (F := fun y => ψ y * bb y i) (hF i) (hFc i) (k := f)
      (fun t _ => hf.contDiffAt) (EuclideanSpace.single i 1)
    have e1 : ∀ x, ψ x * (bb x i * fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))) =
        fderiv ℝ f x (EuclideanSpace.single i 1) * (ψ x * bb x i) := fun x => by ring
    simp_rw [e1]
    have e2 : ∫ x, f x * fderiv ℝ (fun y => (ψ y • bb y) i) x (EuclideanSpace.single i (1 : ℝ)) =
        ∫ t, f t * fderiv ℝ (fun y => ψ y * bb y i) t (EuclideanSpace.single i 1) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [PiLp.smul_apply]
    rw [e2]
    linarith [h]
  have hint1 : ∀ i : Fin d, Integrable (fun x => ψ x * (bb x i *
      fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)))) := by
    intro i
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hψ.1.continuous.mul (((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp
        hbb.continuous).mul ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const))
    · exact hψ.2.mul_right
  have hint2 : ∀ i : Fin d, Integrable (fun x => f x *
      fderiv ℝ (fun y => (ψ y • bb y) i) x (EuclideanSpace.single i (1 : ℝ))) := by
    intro i
    have hcd : ContDiff ℝ 1 (fun y => (ψ y • bb y) i) := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff.comp hΦ
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hf.continuous.mul ((hcd.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    · have : HasCompactSupport (fun y => (ψ y • bb y) i) :=
        hΦc.comp_left (g := fun v : Euc d => v i) (by simp)
      exact (this.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
        (by simp) |>.mul_left
  have hL : ∀ x, ψ x * inner ℝ (bb x) (gradient f x) = ∑ i : Fin d, ψ x * (bb x i *
      fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))) := by
    intro x
    rw [← Finset.mul_sum]
    congr 1
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sa12v_grad_coord]
    simp [mul_comm]
  have hR : ∀ x, f x * movDiv (fun y => ψ y • bb y) x = ∑ i : Fin d, f x *
      fderiv ℝ (fun y => (ψ y • bb y) i) x (EuclideanSpace.single i (1 : ℝ)) := by
    intro x
    rw [movDiv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sa12v_fderiv_coord ((hΦ.differentiable one_ne_zero) x)]
  simp_rw [hL, hR]
  rw [integral_finsetSum _ (fun i _ => hint1 i), integral_finsetSum _ (fun i _ => hint2 i), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => hterm i


theorem sa12v_lap_cont {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) : Continuous (Laplacian.laplacian f) := by
  have hfun : Laplacian.laplacian f = fun y => ∑ i, HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i f) y :=
    funext fun y => HRS.MS.UniqT3.lap_eq hf y
  rw [hfun]
  refine continuous_finsetSum _ fun i _ => ?_
  have hd1 : ContDiff ℝ 1 (HRS.MS.UniqT3.D1 i f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  exact (hd1.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem sa12v_q_smooth {m H : Euc d → ℝ} (hm : ContDiff ℝ ∞ m) (hH : ContDiff ℝ ∞ H) (i : Fin d) :
    ContDiff ℝ ∞ (fun y => m y * gradient H y i) := by
  have h1 : ContDiff ℝ ∞ (fun y => gradient H y i) := by
    have : (fun y => gradient H y i) = fun y => fderiv ℝ H y (EuclideanSpace.single i (1 : ℝ)) :=
      funext fun y => sa12v_grad_coord H y i
    rw [this]
    exact (hH.fderiv_right (m := ∞) (by exact_mod_cast le_top)).clm_apply contDiff_const
  exact hm.mul h1

theorem sa12v_ntp_cont (L : ℝ) {γ : Euc d → ℝ} (hγ : LocallyIntegrable γ volume)
    (M : Matrix (Fin d) (Fin d) ℝ) {m ψ : Euc d → ℝ} (hm : ContDiff ℝ ∞ m) (hψ : IsCcInfty ψ) :
    Continuous (nonlocalTestPer L γ M m ψ) := by
  have hH : ContDiff ℝ ∞ (sa12vH γ ψ) := sa12v_H_smooth hγ hψ.1 hψ.2
  unfold nonlocalTestPer
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  refine continuous_const.mul ?_
  have : partialDeriv (fun _ : Fin 1 => j)
      (fun y => m y * gradient (fun w => ∫ u, γ (w - u) * ψ u) y i) =
      fun x => fderiv ℝ (fun y => m y * gradient (sa12vH γ ψ) y i) x (EuclideanSpace.single j (1 : ℝ)) :=
    funext fun x => sa12v_partialDeriv_one _ j x
  rw [this]
  exact (((sa12v_q_smooth hm hH i).continuous_fderiv (by simp))).clm_apply continuous_const

/-- The spatial identity at a fixed time. -/
theorem sa12v_slice (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L : ℝ} (hL : 0 < L)
    {γ : Euc d → ℝ} (hγ : IsPeriodicRieszKernel d s L γ) (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ)
    {m f : Euc d → ℝ} {bb : Euc d → Euc d}
    (hm : ContDiff ℝ ∞ m) (hmp : ∀ (x : Euc d) (k : Fin d → ℤ), m (x + L • latticePt k) = m x)
    (hf : ContDiff ℝ ∞ f) (hfp : ∀ (x : Euc d) (k : Fin d → ℤ), f (x + L • latticePt k) = f x)
    (hbb : ContDiff ℝ 1 bb) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) :
    Integrable (fun x => f x * sa12vA L γ M ν m bb ψ x) ∧
    ∫ x, f x * sa12vA L γ M ν m bb ψ x =
      ∫ x, ψ x * (ν * Laplacian.laplacian f x + inner ℝ (bb x) (gradient f x) +
        -perNonlocal L γ M m f x) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by simp)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hΦ : ContDiff ℝ 1 (fun y => ψ y • bb y) := (hψ.1.of_le (by simp)).smul hbb
  have hΦc : HasCompactSupport (fun y => ψ y • bb y) := hψ.2.smul_right
  obtain ⟨hlc, hlcs⟩ := sa12v_lap_cc hψ
  obtain ⟨hmc, hmcs⟩ := sa12v_movDiv_cc hΦ hΦc
  have hntp := sa12v_ntp_cont L hγ.locInt M hm hψ
  obtain ⟨hnl1, hnl2⟩ := sa12v_nonlocal hd hs0 hsd hL hγ M hm hmp hf hfp hψ
  have hT1 : Integrable (fun x => f x * (ν * Laplacian.laplacian ψ x)) := by
    have hs1 : HasCompactSupport (fun x => ν * Laplacian.laplacian ψ x) := hlcs.mul_left
    exact Continuous.integrable_of_hasCompactSupport (hf.continuous.mul (continuous_const.mul hlc))
      hs1.mul_left
  have hT2 : Integrable (fun x => f x * movDiv (fun y => ψ y • bb y) x) :=
    Continuous.integrable_of_hasCompactSupport (hf.continuous.mul hmc) hmcs.mul_left
  have hT3e : (fun x => f x * (centeredBox d L).indicator (nonlocalTestPer L γ M m ψ) x) =
      (centeredBox d L).indicator (fun x => f x * nonlocalTestPer L γ M m ψ x) := by
    funext x
    by_cases hx : x ∈ centeredBox d L
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hT3 : Integrable (fun x => f x * (centeredBox d L).indicator (nonlocalTestPer L γ M m ψ) x) := by
    rw [hT3e]
    exact (integrable_indicator_iff (sa12v_centered_meas L)).2
      (sa12v_integrableOn_cb L (hf.continuous.mul hntp))
  have hfA : ∀ x, f x * sa12vA L γ M ν m bb ψ x =
      f x * (ν * Laplacian.laplacian ψ x) - f x * movDiv (fun y => ψ y • bb y) x -
        f x * (centeredBox d L).indicator (nonlocalTestPer L γ M m ψ) x := by
    intro x
    unfold sa12vA
    ring
  have hfA' : (fun x => f x * sa12vA L γ M ν m bb ψ x) = fun x =>
      f x * (ν * Laplacian.laplacian ψ x) - f x * movDiv (fun y => ψ y • bb y) x -
        f x * (centeredBox d L).indicator (nonlocalTestPer L γ M m ψ) x := funext hfA
  refine ⟨?_, ?_⟩
  · rw [hfA']
    exact (hT1.sub hT2).sub hT3
  rw [hfA']
  have hT12 : Integrable (fun x => f x * (ν * Laplacian.laplacian ψ x) -
      f x * movDiv (fun y => ψ y • bb y) x) := hT1.sub hT2
  rw [integral_sub hT12 hT3, integral_sub hT1 hT2]
  -- the right side
  have hI1 : Integrable (fun x => ψ x * Laplacian.laplacian f x) :=
    Continuous.integrable_of_hasCompactSupport (hψ.1.continuous.mul (sa12v_lap_cont hf2)) hψ.2.mul_right
  have hgc : Continuous (gradient f) := by
    have : gradient f = (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ f := rfl
    rw [this]
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hf1.continuous_fderiv one_ne_zero)
  have hI2 : Integrable (fun x => ψ x * inner ℝ (bb x) (gradient f x)) :=
    Continuous.integrable_of_hasCompactSupport
      (hψ.1.continuous.mul (continuous_inner.comp (hbb.continuous.prodMk hgc))) hψ.2.mul_right
  have hrhs : (fun x => ψ x * (ν * Laplacian.laplacian f x + inner ℝ (bb x) (gradient f x) +
        -perNonlocal L γ M m f x)) = fun x => ν * (ψ x * Laplacian.laplacian f x) +
        ψ x * inner ℝ (bb x) (gradient f x) + -(ψ x * perNonlocal L γ M m f x) := by
    funext x; ring
  have hA12 : Integrable (fun x => ν * (ψ x * Laplacian.laplacian f x) +
      ψ x * inner ℝ (bb x) (gradient f x)) := (hI1.const_mul ν).add hI2
  have hNeg : Integrable (fun x => -(ψ x * perNonlocal L γ M m f x)) := hnl1.neg
  rw [hrhs, integral_add hA12 hNeg, integral_add (hI1.const_mul ν) hI2,
    integral_neg, integral_const_mul, hnl2]
  have ha := HRS.MS.Fcau.fcau_green hf2 (hψ.1.of_le (by simp)) hψ.2
  have hb := sa12v_transport_ibp hf1 hbb hψ
  have hc : ∫ x, f x * (centeredBox d L).indicator (nonlocalTestPer L γ M m ψ) x =
      ∫ x in centeredBox d L, f x * nonlocalTestPer L γ M m ψ x := by
    rw [hT3e, integral_indicator (sa12v_centered_meas L)]
  have e1 : ∫ x, f x * (ν * Laplacian.laplacian ψ x) = ν * ∫ x, f x * Laplacian.laplacian ψ x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [e1, hc, ha, hb]
  ring

end HRS.MH.AdjointRd.Phase2SA12Construction
