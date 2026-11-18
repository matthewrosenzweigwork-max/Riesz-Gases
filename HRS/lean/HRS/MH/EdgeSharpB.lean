import HRS.Main.HeadlineEdgeworth
import HRS.Prob.Metrics

/-!
# EdgeSharp packets B1, B2, C1, C2: time-zero pairing, window at zero, Gaussian linear statistics

Statements copied verbatim from `HRS/MH/EdgeSharpSpec.lean`; proofs only.
B1 is a copy of `HRS.MH.MfclP.exists_pathEval_proof` (`HRS/MH/MfclA1A9.lean:22-58`); that file is not imported.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.EdgeSharp

open HRS HRS.Main

variable {d : ℕ}

/-! ### Helpers for B1 (copied from `HRS/MH/MfclA1A9.lean:22-48`) -/

private theorem memℓp_fourierVec_phiB (m : ℝ) (φ : Torus d → ℝ)
    (hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2) :
    Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k) 2 := by
  rw [Torus.memℓp_two_iff]
  refine hs.congr fun k => ?_
  rw [mul_pow, Torus.jp_rpow_sq]

/-- The `ℓ²` vector `k ↦ ⟨k⟩^{m} φ̂(k)` representing `F ↦ F(φ)` in `E_m`. -/
private def fourierVecPhiB (m : ℝ) (φ : Torus d → ℝ)
    (hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2) :
    NegSobolev d m :=
  (⟨fun k : NonzeroLattice d => Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k,
    memℓp_fourierVec_phiB m φ hs⟩ : lp (fun _ : NonzeroLattice d => ℝ) 2)

private theorem eval_eq_inner_phiB {m : ℝ} (F : NegSobolev d m) (φ : Torus d → ℝ)
    (hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2) :
    NegSobolev.eval F φ = @inner ℝ (NegSobolev d m) _ F (fourierVecPhiB m φ hs) := by
  have h := lp.inner_eq_tsum (𝕜 := ℝ) (G := fun _ : NonzeroLattice d => ℝ)
    (F : lp (fun _ : NonzeroLattice d => ℝ) 2)
    (fourierVecPhiB m φ hs : lp (fun _ : NonzeroLattice d => ℝ) 2)
  refine Eq.trans ?_ h.symm
  unfold NegSobolev.eval
  refine tsum_congr fun l => ?_
  simp only [NegSobolev.fourierCoeff, RCLike.inner_apply, conj_trivial]
  show Lattice.jp l.1 ^ m * NegSobolev.coord F l * Torus.funRealCoeff φ l =
    (Lattice.jp l.1 ^ m * Torus.funRealCoeff φ l) * NegSobolev.coord F l
  ring

/-! ### Group B: the time-zero pairing on `E_m` and `𝒳_{m,T}`, identification with `Z₀` -/

/-- [B1] The pairing `F ↦ F(φ)` is a continuous linear functional on `E_m`, and `w ↦ ⟨w⁰, φ⟩` one on path space (copy of
`HRS.MH.MfclP.exists_pathEval_proof`, `HRS/MH/MfclA1A9.lean:22-58`: `fourierVecPhi`, `eval_eq_inner_phi`, `innerSL`,
`ContinuousMap.evalCLM`; copied instead of imported because `HRS.MH.MfclA1A9` imports `HRS.MD.EQBurnClt`, which is not in the shared
build). -/
theorem exists_evalCLM (m : ℝ) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) :
    ∃ L : NegSobolev d m →L[ℝ] ℝ, ∀ F : NegSobolev d m, L F = NegSobolev.eval F φ := by
  have hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2 :=
    (HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hφ m).2
  refine ⟨innerSL ℝ (fourierVecPhiB m φ hs), fun F => ?_⟩
  rw [innerSL_apply_apply, eval_eq_inner_phiB, real_inner_comm]

/-- [B1'] Path-space version (same statement as `HRS.MH.Mfcl.exists_pathEval`). -/
theorem exists_pathEval (m T : ℝ) (hT : 0 ≤ T) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) :
    ∃ ℓ : PathSpace d m T →L[ℝ] ℝ, ∀ w : PathSpace d m T,
      ℓ w = NegSobolev.eval (w.at' ⟨0, Set.left_mem_Icc.2 hT⟩) φ := by
  have hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2 :=
    (HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hφ m).2
  refine ⟨(innerSL ℝ (fourierVecPhiB m φ hs)).comp
    (ContinuousMap.evalCLM ℝ (⟨0, Set.left_mem_Icc.2 hT⟩ : Set.Icc (0 : ℝ) T)), fun w => ?_⟩
  show innerSL ℝ (fourierVecPhiB m φ hs) (w.at' ⟨0, Set.left_mem_Icc.2 hT⟩) = _
  rw [innerSL_apply_apply, eval_eq_inner_phiB, real_inner_comm]

/-- [B2a] `pathEval` at time `0` is the slice `at' ⟨0, _⟩` (`dif_pos`). -/
theorem pathEval_zero {m T : ℝ} (hT : 0 ≤ T) (w : PathSpace d m T) :
    pathEval w 0 = w.at' ⟨0, Set.left_mem_Icc.2 hT⟩ := by
  unfold HRS.Main.pathEval
  rw [dif_pos (Set.left_mem_Icc.2 hT)]

/-- [B2b] The window at `a = 0` of a process that is continuous on `[0,T]` has time-zero slice `Z 0`.  Route: as
`HRS.MD.EQGaussWindow.eqgw_windowPath_at` (`HRS/MD/EQGaussWindow.lean:198`) but with `ContinuousOn` on `Icc 0 T` only:
`Main.windowPath = toPath`, `dif_pos` with continuity of `t ↦ Z (0+t) ω` on `Icc 0 T` (`ContinuousOn.comp_continuous`). -/
theorem windowPath_at_zero {m T : ℝ} (hT : 0 ≤ T) {Ω' : Type*} (Z : ℝ → Ω' → NegSobolev d m) (ω : Ω')
    (hc : ContinuousOn (fun t => Z t ω) (Set.Icc 0 T)) :
    (windowPath m T 0 Z ω).at' ⟨0, Set.left_mem_Icc.2 hT⟩ = Z 0 ω := by
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) T => Z (0 + (t : ℝ)) ω := by
    refine hc.comp_continuous (by fun_prop) (fun t => ?_)
    exact ⟨by simpa using t.2.1, by simpa using t.2.2⟩
  have h : windowPath m T 0 Z ω = (⟨fun t : Set.Icc (0 : ℝ) T => Z (0 + (t : ℝ)) ω, hcont⟩ :
      C(Set.Icc (0 : ℝ) T, NegSobolev d m)) := by
    unfold windowPath toPath
    exact dif_pos hcont
  rw [h]
  show Z (0 + ((⟨0, Set.left_mem_Icc.2 hT⟩ : Set.Icc (0 : ℝ) T) : ℝ)) ω = Z 0 ω
  simp

/-! ### Group C: Gaussian expectations -/

/-- [C2] Linear statistics of a Gaussian vector are in `L²`.  Route: `IsGaussian.memLp_dual` (`Mathlib.Probability.Distributions.Gaussian.Basic`)
for `ν`, `memLp_map_measure_iff`/`MemLp.comp_measurePreserving` with `hlaw`. -/
theorem memLp_two_clm {m : ℝ} (ν : Measure (NegSobolev d m)) (hν : IsCenteredGaussian ν)
    (L : NegSobolev d m →L[ℝ] ℝ) {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (hmeas : Measurable Z₀) (hlaw : law P' Z₀ = ν) :
    MemLp (fun ω => L (Z₀ ω)) 2 P' := by
  have : IsGaussian ν := hν.1
  have hL : MemLp (fun x : NegSobolev d m => L x) 2 ν := IsGaussian.memLp_dual ν L 2 (by norm_num)
  rw [← hlaw] at hL
  exact (memLp_map_measure_iff (L.continuous.measurable.aestronglyMeasurable) hmeas.aemeasurable).1 hL

/-- Characteristic function of a centred real Gaussian at `1`, real part: `∫ cos x d N(0,v) = exp(-v/2)`. -/
private theorem integral_cos_gaussianReal_zero (v : NNReal) :
    ∫ x, Real.cos x ∂(gaussianReal 0 v) = Real.exp (-(v : ℝ) / 2) := by
  have hc := charFun_gaussianReal (μ := 0) (v := v) 1
  rw [charFun_apply_real] at hc
  have hint : Integrable (fun x : ℝ => Complex.exp (((1 : ℝ) : ℂ) * (x : ℂ) * Complex.I))
      (gaussianReal 0 v) :=
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (Filter.Eventually.of_forall fun x => by
        rw [Complex.norm_exp]
        simp)
  have hcos : (fun x : ℝ => Real.cos x) =
      fun x : ℝ => (Complex.exp (((1 : ℝ) : ℂ) * (x : ℂ) * Complex.I)).re := by
    funext x
    simp [Complex.exp_ofReal_mul_I_re]
  have h2 : ∫ x, (Complex.exp (((1 : ℝ) : ℂ) * (x : ℂ) * Complex.I)).re ∂(gaussianReal 0 v)
      = (∫ x, Complex.exp (((1 : ℝ) : ℂ) * (x : ℂ) * Complex.I) ∂(gaussianReal 0 v)).re :=
    integral_re hint
  rw [hcos, h2, hc, Complex.exp_re]
  simp [neg_div]

/-- [C1] `E cos(L Z₀) > 0` for a centered Gaussian `Z₀ ∼ ν` and a continuous linear functional `L` (`= exp(-v/2)`).
Route: `P'.map (L ∘ Z₀) = ν.map L` (`Measure.map_map`, `hlaw`), `IsGaussian.map_eq_gaussianReal` (`hν.1`) with mean
`ν[L] = 0` (`hν.2 L`), `∫ cos x d(gaussianReal 0 v) = Re (charFun (gaussianReal 0 v) 1) = exp(-v/2)`
(`ProbabilityTheory.charFun_gaussianReal`, `integral_map`, `integral_re`/`Complex.ofReal_cos`), `Real.exp_pos`. -/
theorem integral_cos_clm_pos {m : ℝ} (ν : Measure (NegSobolev d m)) (hν : IsCenteredGaussian ν)
    (L : NegSobolev d m →L[ℝ] ℝ) {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (hmeas : Measurable Z₀) (hlaw : law P' Z₀ = ν) :
    0 < ∫ ω, Real.cos (L (Z₀ ω)) ∂P' := by
  have : IsGaussian ν := hν.1
  have hLm : Measurable (fun x : NegSobolev d m => L x) := L.continuous.measurable
  have hAE : AEMeasurable (fun ω => L (Z₀ ω)) P' := (hLm.comp hmeas).aemeasurable
  have hmap : P'.map (fun ω => L (Z₀ ω)) = gaussianReal 0 (Var[fun x : NegSobolev d m => L x; ν]).toNNReal := by
    have h1 : P'.map (fun ω => L (Z₀ ω)) = (P'.map Z₀).map L := by
      rw [Measure.map_map hLm hmeas]; rfl
    have hlaw' : P'.map Z₀ = ν := hlaw
    rw [h1, hlaw', IsGaussian.map_eq_gaussianReal]
    congr 1
    exact hν.2 L
  have key : ∫ ω, Real.cos (L (Z₀ ω)) ∂P' = ∫ x, Real.cos x ∂(P'.map (fun ω => L (Z₀ ω))) :=
    (integral_map hAE Real.continuous_cos.aestronglyMeasurable).symm
  rw [key, hmap, integral_cos_gaussianReal_zero]
  exact Real.exp_pos _

end HRS.MH.EdgeSharp
