import HRS.MS.SpecAux38
import HRS.MS.SpecAux32

/-!
# S8P: pairings of the eigenfunctions (S8.7, packets b3, b5)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  For Schwartz `φ, ψ` and `v ≈ φ`, `w ≈ ψ` in `L²_0`:
* `s8p_mean_zero`: `∫ √ρ φ = 0` for the representative of an element of `L²_0`;
* `s8p_A_pair`: `⟨A v, w⟩ = ∫ W_φ ψ` with `W_φ = ν φ + √ρ (g * (√ρ φ))` (`mov2eW`);
* `s8p_orth_e`: `∫ e_φ f_ψ ρ dx = ∫ W_φ ψ` (the `A⁻¹`-pairing of the eigenfunctions);
* `s8p_grad_pair`: `∫ ∇e_φ · ∇e_ψ dμ = ∫ W_ψ S φ`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec HRS.MS.MovLin

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_mean_zero (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) (v : MovL2Zero ρ) (φ : 𝓢R)
    (hv : ∀ᵐ x ∂(volume : Measure (Euc d)), movFun v x = φ x) :
    ∫ x, Real.sqrt (ρ x) * φ x = 0 := by
  have h0 := (mov2d_mem_zero_iff (ρ := ρ)).1 v.2
  have hm : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d)) := by
    rw [← hψ0]; exact ψ0.memLp 2
  have e : (movSqrtLp ρ : Lp ℝ 2 (volume : Measure (Euc d))) = hm.toLp _ := by
    unfold movSqrtLp; rw [dif_pos hm]
  rw [L2.inner_def] at h0
  rw [← h0]
  refine integral_congr_ae ?_
  filter_upwards [hv, (show (hm.toLp _ : Lp ℝ 2 (volume : Measure (Euc d))) =ᵐ[volume] _ from
    hm.coeFn_toLp)] with x h1 h2
  rw [e]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [h2, ← h1]
  ring

theorem s8p_A_pair (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    {M : ℝ} (h : S8pRho d s ρ M) (φ ψ : 𝓢R) (v w : MovL2Zero ρ)
    (hv : ∀ᵐ x ∂(volume : Measure (Euc d)), movFun v x = φ x)
    (hw : ∀ᵐ x ∂(volume : Measure (Euc d)), movFun w x = ψ x) (β : ℝ) :
    ⟪s8p_Asub h (MovL2Zero ρ) β⁻¹ v, w⟫ = ∫ x, mov2eW d s β ρ φ x * ψ x := by
  rw [s8p_Asub_inner]
  have hin : ⟪(v : Lp ℝ 2 (volume : Measure (Euc d))), (w : Lp ℝ 2 (volume : Measure (Euc d)))⟫ =
      ∫ x, φ x * ψ x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hv, hw] with x h1 h2
    simp only [RCLike.inner_apply, conj_trivial]
    change (w : Lp ℝ 2 (volume : Measure (Euc d))) x * (v : Lp ℝ 2 (volume : Measure (Euc d))) x = _
    rw [show (w : Lp ℝ 2 (volume : Measure (Euc d))) x = ψ x from h2,
      show (v : Lp ℝ 2 (volume : Measure (Euc d))) x = φ x from h1]
    ring
  have hI1 : Integrable (fun x => φ x * ψ x) := (φ.memLp 2).integrable_mul (ψ.memLp 2)
  have hI2 : Integrable (fun x => mov2eW d s β ρ φ x * ψ x) :=
    (mov2e_W_memLp hd hs0 hsd hρ hE β φ).integrable_mul (ψ.memLp 2)
  have hq := s8p_qf_eq_iter h φ (v : Lp ℝ 2 (volume : Measure (Euc d)))
    (w : Lp ℝ 2 (volume : Measure (Euc d))) ψ hv hw
  rw [show ⟪v, w⟫ = ∫ x, φ x * ψ x from hin, hq]
  have e : (fun x => mov2eW d s β ρ φ x * ψ x - β⁻¹ * (φ x * ψ x)) =
      fun y => (Real.sqrt (ρ y) * ψ y) *
        HRS.Whole.convFun (rieszKernel d s) (fun z => Real.sqrt (ρ z) * φ z) y := by
    funext y; unfold mov2eW; ring
  have := integral_sub hI2 (hI1.const_mul β⁻¹)
  rw [integral_const_mul] at this
  rw [← e, this]
  ring

theorem s8p_orth_e (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (β : ℝ) (φ ψ : 𝓢R) (hψc : ∫ x, Real.sqrt (ρ x) * ψ x = 0) :
    ∫ x, s8p_E d s β ρ φ x * (ψ x / Real.sqrt (ρ x)) ∂(HRS.Whole.withDensityReal ρ) =
      ∫ x, mov2eW d s β ρ φ x * ψ x := by
  rw [mov2e_integral_mu hρ]
  have hI2 : Integrable (fun x => mov2eW d s β ρ φ x * ψ x) :=
    (mov2e_W_memLp hd hs0 hsd hρ hE β φ).integrable_mul (ψ.memLp 2)
  have hsq : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d)) := by
    refine (memLp_two_iff_integrable_sq (hρ.data.sqrt_smooth.continuous.aestronglyMeasurable)).2 ?_
    exact ((hρ.psi_GD.mul hρ.psi_GD).integrable).congr (Filter.Eventually.of_forall fun x => by simp [sq])
  have hI3 : Integrable (fun x => Real.sqrt (ρ x) * ψ x) := hsq.integrable_mul (ψ.memLp 2)
  have e : (fun x => ρ x * (s8p_E d s β ρ φ x * (ψ x / Real.sqrt (ρ x)))) =
      fun x => mov2eW d s β ρ φ x * ψ x - s8p_Cc d s ρ φ * (Real.sqrt (ρ x) * ψ x) := by
    funext x
    have hp := hρ.psi_pos x
    have hss := hρ.psi_sq x
    unfold s8p_E mov2eW s8p_U mov2eH
    generalize Real.sqrt (ρ x) = p at hp hss ⊢
    rw [← hss]
    field_simp
  rw [e, integral_sub hI2 (hI3.const_mul _), integral_const_mul, hψc]
  simp

theorem s8p_grad_pair (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (β : ℝ) (φ ψ : 𝓢R) :
    Integrable (fun x => inner ℝ (gradient (s8p_E d s β ρ φ) x) (gradient (s8p_E d s β ρ ψ) x))
        (HRS.Whole.withDensityReal ρ) ∧
      ∫ x, inner ℝ (gradient (s8p_E d s β ρ φ) x) (gradient (s8p_E d s β ρ ψ) x)
          ∂(HRS.Whole.withDensityReal ρ) = ∫ x, mov2eW d s β ρ ψ x * movS d s β ρ φ x := by
  have key : ∀ x, ρ x * inner ℝ (gradient (s8p_E d s β ρ φ) x) (gradient (s8p_E d s β ρ ψ) x) =
      ∑ i, mov2eZ d s β ρ ψ i x * mov2eZ d s β ρ φ i x := by
    intro x
    rw [HRS.MS.Mov63.mnc_inner_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [s8p_E_grad hd hs0 hsd hρ hE β φ x i, s8p_E_grad hd hs0 hsd hρ hE β ψ x i]
    have hp := hρ.psi_pos x
    have hss := hρ.psi_sq x
    generalize Real.sqrt (ρ x) = p at hp hss ⊢
    rw [← hss]
    field_simp
  have hZ : Integrable (fun x => ∑ i, mov2eZ d s β ρ ψ i x * mov2eZ d s β ρ φ i x) :=
    integrable_finsetSum _ fun i _ =>
      ((mov2e_Z_GD hd hs0 hsd hρ hE β ψ i).mul (mov2e_Z_GD hd hs0 hsd hρ hE β φ i)).integrable
  refine ⟨(mov2e_integrable_mu hρ).2 (hZ.congr (Filter.Eventually.of_forall fun x => (key x).symm)), ?_⟩
  rw [mov2e_integral_mu hρ, (s8p_WS_integral hd hs0 hsd hρ hE β φ ψ).2]
  exact integral_congr_ae (Filter.Eventually.of_forall key)

end HRS.MS.Spec
