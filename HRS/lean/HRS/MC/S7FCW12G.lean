import HRS.MC.S7FCW12E
import HRS.Energy.StaticLimitGauss

/-!
# FC-E packet, part G: measurability on the Gaussian side (E4, prefix `s7fcw12_`)

* `s7fcw12_summable_eval`, `s7fcw12_eval_lipschitz`: `F ↦ eval F φ` is Lipschitz for smooth `φ`.
* `s7fcw12_quad_continuous`: the Gaussian quadratic functional `F ↦ K.quad F` is continuous.
* `s7_FC_E4_limit_measurable_proof`: statement copied from `HRS/MC/S7FCPlan.lean` (`s7_FC_E4_limit_measurable`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan

open Classical

namespace HRS.MC.Sec7.S7FCW12

variable {d : ℕ}

theorem s7fcw12_summable_eval {m : ℝ} (F : NegSobolev d m) (φ : Torus d → ℝ)
    (hφ : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2) :
    Summable fun k : NonzeroLattice d => NegSobolev.coord F k * (Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k) := by
  set y : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k with hy
  have hy2 : Summable fun k : NonzeroLattice d => y k ^ 2 := by
    refine hφ.congr fun k => ?_
    simp only [hy]
    rw [mul_pow, Torus.jp_rpow_sq]
  have hF2 := (NegSobolev.coord_sq F).1
  have hcs := Torus.cs_tsum (fun k => |NegSobolev.coord F k|) (fun k => |y k|) (fun _ => abs_nonneg _)
    (fun _ => abs_nonneg _) (by simpa [sq_abs] using hF2) (by simpa [sq_abs] using hy2)
  have hs : Summable fun k : NonzeroLattice d => ‖NegSobolev.coord F k * y k‖ := by
    simpa [abs_mul] using hcs.1
  exact hs.of_norm

theorem s7fcw12_eval_sub {m : ℝ} (F G : NegSobolev d m) (φ : Torus d → ℝ)
    (hφ : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2) :
    NegSobolev.eval (F - G) φ = NegSobolev.eval F φ - NegSobolev.eval G φ := by
  have e : ∀ H : NegSobolev d m, NegSobolev.eval H φ =
      ∑' k : NonzeroLattice d, NegSobolev.coord H k * (Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k) := by
    intro H
    unfold NegSobolev.eval NegSobolev.fourierCoeff
    refine tsum_congr fun k => ?_
    ring
  rw [e, e F, e G, ← (s7fcw12_summable_eval F φ hφ).tsum_sub (s7fcw12_summable_eval G φ hφ)]
  congr 1
  funext k
  have hc : NegSobolev.coord (F - G) k = NegSobolev.coord F k - NegSobolev.coord G k := rfl
  rw [hc, sub_mul]

theorem s7fcw12_eval_lipschitz {m : ℝ} (φ : Torus d → ℝ)
    (hφ : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2) :
    LipschitzWith (Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2)).toNNReal
      (fun F : NegSobolev d m => NegSobolev.eval F φ) := by
  refine LipschitzWith.of_dist_le_mul fun F G => ?_
  rw [Real.dist_eq, Real.coe_toNNReal _ (Real.sqrt_nonneg _), dist_eq_norm]
  have h := NegSobolev.abs_eval_le (F - G) φ hφ
  rw [← s7fcw12_eval_sub F G φ hφ]
  exact h.trans_eq (mul_comm _ _)

theorem s7fcw12_quad_continuous {m : ℝ} (K : FRKernel d) :
    Continuous fun F : NegSobolev d m => K.quad F := by
  have hev : ∀ i, Continuous fun F : NegSobolev d m => NegSobolev.eval F (K.f i) := fun i =>
    (s7fcw12_eval_lipschitz (m := m) (K.f i)
      (HRS.StaticLimitAux.summable_weighted_smooth m (K.smooth i))).continuous
  unfold FRKernel.quad
  exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => continuous_const.mul ((hev i).mul (hev j)))

/-- Coordinate functionals of the Gaussian finite-rank field. -/
def s7fcw12_gaussPsi (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) :
    NonzeroLattice d → ℝ → NegSobolev d r → ℝ :=
  fun k _ F => if k ∈ S then (K k).quad F else 0

theorem s7fcw12_gaussPsi_meas (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d)
    (k : NonzeroLattice d) : Measurable fun q : ℝ × NegSobolev d r => s7fcw12_gaussPsi r S K k q.1 q.2 := by
  unfold s7fcw12_gaussPsi
  by_cases hk : k ∈ S
  · simp only [if_pos hk]
    exact (s7fcw12_quad_continuous (m := r) (K k)).measurable.comp measurable_snd
  · simp only [if_neg hk]
    exact measurable_const

theorem s7fcw12_fcGauss_eq (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (η : ℝ → Ω → NegSobolev d r) (t : ℝ) (ω : Ω) :
    fcGaussAt r S K P η t ω = NegSobolev.ofSeq r
      (fun k => s7fcw12_gaussPsi r S K k t (η t ω) - ∫ ω', s7fcw12_gaussPsi r S K k t (η t ω') ∂P) := by
  unfold fcGaussAt s7fcw12_gaussPsi
  congr 1
  funext k
  by_cases hk : k ∈ S
  · simp only [if_pos hk]
  · simp only [if_neg hk, integral_zero, sub_zero]

theorem s7_FC_E4_limit_measurable_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η)
    (B : ℝ → Ω' → NegSobolev d r) (hBm : Measurable (Function.uncurry B))
    (hBL2 : ∀ᵐ ω ∂P', MemLp (fun t => B t ω) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) :
    AEMeasurable (pairLim r T 0 η B) P' ∧
    AEMeasurable (fun ω => (procWin r T 0 η ω,
      toL2 r T (fun t => fcGaussAt r S K P' η (0 + t) ω))) P' := by
  obtain ⟨Y₀, -, hsol⟩ := hη
  have hL := hsol T
  have hW : procWin r T 0 η = HRS.Uniform.windowPath 0 T η := by
    funext ω
    rfl
  have hproc : AEMeasurable (procWin r T 0 η) P' := by
    rw [hW]
    exact HRS.Uniform.Q45.aemeasurable_windowPath' P' hT η (fun t _ => (hL.meas t).aemeasurable) hL.cont
  have hBt : Measurable fun ω => HRS.Sec7.toL2 r T (fun t => B (0 + t) ω) :=
    s7fcw12_toL2_measurable T (fun t ω => B (0 + t) ω)
      (hBm.comp ((measurable_const.add measurable_fst).prodMk measurable_snd))
  constructor
  · unfold pairLim
    exact AEMeasurable.prodMk hproc hBt.aemeasurable
  · refine AEMeasurable.prodMk hproc ?_
    simp only [zero_add]
    exact s7fcw12_coord_aemeasurable hT P' η (fun t => hL.meas t) hL.cont 0
      (s7fcw12_gaussPsi r S K) (s7fcw12_gaussPsi_meas r S K) (fun t ω => fcGaussAt r S K P' η t ω)
      (fun t _ ω => s7fcw12_fcGauss_eq r S K P' η t ω)

end HRS.MC.Sec7.S7FCW12
