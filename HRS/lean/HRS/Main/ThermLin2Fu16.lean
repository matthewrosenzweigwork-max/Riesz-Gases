import HRS.Main.ThermLin2Fu15

/-!
# THERMLIN2 Fu16: zero-mean modification, `Δ_r` kills constants, dual decay of `U^{r,t}`, and the `H^{m-a₀}` bound of `ψ_r`

The `H^{m-a₀}` bound uses the plan statement `tl2_Delta_bound` (B2) as a black box (the orchestrator swaps in
`tl2_Delta_bound_proof` at integration).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c

variable {d : ℕ}

section ZeroMean

theorem tl2fu_isSmooth_sub_const {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (c : ℝ) :
    Torus.IsSmooth (fun x => f x - c) := by
  unfold Torus.IsSmooth Torus.IsCk Torus.lift at *
  exact hf.sub contDiff_const

theorem tl2fu_continuous_of_smooth {f : Torus d → ℝ} (hf : Torus.IsSmooth f) : Continuous f :=
  PDE.MFAux.continuous_of_isCk (PDE.MFSemigroup.isCk_nat_of_isSmooth hf 1)

theorem tl2fu_funRealCoeff_sub_const {f : Torus d → ℝ} (hf : Continuous f) (c : ℝ) (k : NonzeroLattice d) :
    Torus.funRealCoeff (fun x => f x - c) k = Torus.funRealCoeff f k := by
  unfold Torus.funRealCoeff
  have h1 : Integrable fun x => Torus.realMode k x * f x :=
    ((HRS.continuous_realMode' k).mul hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable fun x => Torus.realMode k x * c :=
    ((HRS.continuous_realMode' k).mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have e : (fun x => Torus.realMode k x * (f x - c)) =
      fun x => Torus.realMode k x * f x - Torus.realMode k x * c := by
    funext x; ring
  rw [e, integral_sub h1 h2, integral_mul_const, Torus.integral_realMode]
  simp

theorem tl2fu_mean_sub_mean {f : Torus d → ℝ} (hf : Continuous f) :
    Torus.mean (fun x => f x - Torus.mean f) = 0 := by
  unfold Torus.mean
  have h1 : Integrable f := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_sub h1 (integrable_const _), integral_const]
  simp

theorem tl2fu_memSob_sub_const {m : ℝ} {f : Torus d → ℝ} (hf : Continuous f) (hm : MemSobolev m f) (c : ℝ) :
    MemSobolev m (fun x => f x - c) := by
  refine ⟨hm.1.sub (memLp_const c), ?_⟩
  refine hm.2.congr fun k => ?_
  rw [tl2fu_funRealCoeff_sub_const hf c k]

theorem tl2fu_lpFun_sub_const {m : ℝ} {f : Torus d → ℝ} (hf : Continuous f) (hm : MemSobolev m f) (c : ℝ) :
    lpFun m (fun x => f x - c) = lpFun m f := by
  refine NegSobolev_ext fun k => ?_
  rw [coord_lpFun (tl2fu_memSob_sub_const hf hm c), coord_lpFun hm, tl2fu_funRealCoeff_sub_const hf c k]

theorem tl2fu_sobolevNorm_zero_mean {m : ℝ} {g : Torus d → ℝ} (hg : MemSobolev m g) (h0 : Torus.mean g = 0) :
    sobolevNorm m g = ‖lpFun m g‖ := by
  unfold sobolevNorm
  rw [h0, lpFun_of_mem hg]
  have := HRS.Uniform.Q54.norm_sq_lpOf m hg
  rw [← this]
  simp [Real.sqrt_sq]

theorem tl2fu_bgen_sub_const (D : DynData d) (ρ : Torus d → ℝ) {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) (c : ℝ) :
    backwardGenerator D ρ (fun x => f x - c) = backwardGenerator D ρ f := by
  funext x
  have hg : ∀ y, Torus.grad (fun x => f x - c) y = Torus.grad f y := PDE.MFLinear.grad_sub_const f c
  have hl : Torus.laplacian (fun x => f x - c) x = Torus.laplacian f x := by
    unfold Torus.laplacian
    have hc : ContDiff ℝ 2 (Torus.lift f) := hf
    have e : Torus.lift (fun x => f x - c) = Torus.lift f - fun _ => c := rfl
    rw [e, hc.contDiffAt.laplacian_sub contDiffAt_const, InnerProductSpace.laplacian_const]
    simp
  unfold backwardGenerator
  simp only [hg, hl]

end ZeroMean

end HRS.ThermLin.Plan2
