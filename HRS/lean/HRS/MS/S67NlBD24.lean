import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD03
import HRS.MS.S67NlBD13
import HRS.MS.S67NlBD14

/-!
# S6.7 nonlinear breakdown, packet 24: thermal projection, weighted orthogonality, oscillator bound

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4766-4770, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definitions: `s67bd_K`, `s67bd_Q`, `s67bd_R`.
Route: `√ρ₀` is Schwartz with `∫ (√ρ₀)² = ∫ ρ₀ = 1`; Cauchy-Schwarz in `L²` bounds the pairing by
`‖h‖_{L²} = oscNorm 0 h ≤ oscNorm r h`; the triangle inequality in `Σ^r` finishes.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

def s67bd_K (d : ℕ) (s : ℝ) (ρ₀ v ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  -(∑ i, s67bd_F d s ρ₀ v x i * s67bd_W ρ₀ i ψ x) +
    Real.sqrt (ρ₀ x) *
      ∑ i, movForce d s (fun y => v y * s67bd_W ρ₀ i ψ y) x i

def s67bd_Q (ρ₀ h : Euc d → ℝ) (x : Euc d) : ℝ :=
  h x - Real.sqrt (ρ₀ x) * ∫ y, Real.sqrt (ρ₀ y) * h y

def s67bd_R (d : ℕ) (s : ℝ) (ρ₀ v ψ : Euc d → ℝ) : Euc d → ℝ :=
  s67bd_Q ρ₀ (s67bd_K d s ρ₀ v ψ)

/-- the `L²` norm of the class of an `L²` function is its `Σ^0` norm -/
lemma s67bd24_l2norm {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d))) :
    ‖hf.toLp f‖ = oscNorm 0 f := by
  rw [oscNorm_zero _ hf]
  have h2 : ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]; simp [sq]
  rw [← h2, Real.sqrt_sq (norm_nonneg _)]

theorem s67bd_projection (H : Mov2dTh d s β q ρ₀) (r : ℝ) (hr : 0 ≤ r)
    (h : Euc d → ℝ) (hh : MemOsc r h) :
    Integrable (fun x => Real.sqrt (ρ₀ x) * h x) volume ∧
    MemOsc r (s67bd_Q ρ₀ h) ∧
    Integrable (fun x => Real.sqrt (ρ₀ x) * s67bd_Q ρ₀ h x) volume ∧
    (∫ x, Real.sqrt (ρ₀ x) * s67bd_Q ρ₀ h x) = 0 ∧
    oscNorm r (s67bd_Q ρ₀ h) ≤
      (1 + oscNorm r (fun x => Real.sqrt (ρ₀ x))) * oscNorm r h := by
  obtain ⟨ψ, hψ⟩ := mov2d_sqrt_schwartz H
  set φ : Euc d → ℝ := fun x => Real.sqrt (ρ₀ x) with hφdef
  have hφ : MemOsc r φ := by
    have := memOsc_schwartz r ψ
    rwa [hψ] at this
  have hφ0 : MemOsc 0 φ := by
    have := memOsc_schwartz 0 ψ
    rwa [hψ] at this
  have hρ : ∀ x, 0 ≤ ρ₀ x := H.hρ.2.1.nonneg
  have hφsq : ∀ x, φ x * φ x = ρ₀ x := fun x => Real.mul_self_sqrt (hρ x)
  have hint1 : ∫ x, φ x ^ 2 = 1 := by
    have : (fun x => φ x ^ 2) = ρ₀ := by funext x; rw [sq]; exact hφsq x
    rw [this]; exact H.hρ.2.1.integral_one
  have hφnorm : oscNorm 0 φ = 1 := by
    rw [oscNorm_zero _ hφ0.1, hint1, Real.sqrt_one]
  have hprod : Integrable (fun x => φ x * h x) volume :=
    MemLp.integrable_mul (p := 2) (q := 2) hφ.1 hh.1
  set c : ℝ := ∫ y, φ y * h y with hc
  -- the pairing bound
  have hcb : |c| ≤ oscNorm r h := by
    have h0 : oscNorm 0 h ≤ oscNorm r h := (mo_mono hr hh).2
    have hin : c = inner ℝ (hφ.1.toLp φ) (hh.1.toLp h) := by
      rw [L2.inner_def, hc]
      refine integral_congr_ae ?_
      filter_upwards [hφ.1.coeFn_toLp, hh.1.coeFn_toLp] with x h1 h2
      rw [h1, h2]; simp [mul_comm]
    have := abs_real_inner_le_norm (hφ.1.toLp φ) (hh.1.toLp h)
    rw [← hin, s67bd24_l2norm hφ.1, s67bd24_l2norm hh.1, hφnorm, one_mul] at this
    exact this.trans h0
  -- membership of Q
  have hQfun : s67bd_Q ρ₀ h = fun x => h x - c * φ x := by
    funext x; simp only [s67bd_Q, hφdef, hc]; ring
  have hcφ := HRS.MS.MovC1.movc1_osc_smul r c hφ
  have hQmem : MemOsc r (s67bd_Q ρ₀ h) := by
    rw [hQfun]; exact mov2d_memOsc_sub hh hcφ.1
  have hφ2 : Integrable (fun x => φ x * φ x) volume :=
    MemLp.integrable_mul (p := 2) (q := 2) hφ.1 hφ.1
  have hint2 : Integrable (fun x => φ x * s67bd_Q ρ₀ h x) volume := by
    have : (fun x => φ x * s67bd_Q ρ₀ h x) = fun x => φ x * h x - c * (φ x * φ x) := by
      rw [hQfun]; funext x; ring
    rw [this]; exact hprod.sub (hφ2.const_mul c)
  refine ⟨hprod, hQmem, hint2, ?_, ?_⟩
  · have : (fun x => φ x * s67bd_Q ρ₀ h x) = fun x => φ x * h x - c * (φ x * φ x) := by
      rw [hQfun]; funext x; ring
    rw [this, integral_sub hprod (hφ2.const_mul c), integral_const_mul]
    have : ∫ x, φ x * φ x = 1 := by
      rw [← hint1]; exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [sq])
    rw [this, ← hc]; ring
  · have e1 := OscSpace.norm_ofFun _ hQmem
    have e2 := OscSpace.norm_ofFun _ hh
    have e3 := OscSpace.norm_ofFun _ hφ
    have e4 : OscSpace.ofFun r (s67bd_Q ρ₀ h) =
        OscSpace.ofFun r h - c • OscSpace.ofFun r φ := by
      rw [hQfun, mov2d_ofFun_sub hh hcφ.1, mov2d_ofFun_smul c hφ]
    calc oscNorm r (s67bd_Q ρ₀ h) = ‖OscSpace.ofFun r (s67bd_Q ρ₀ h)‖ := e1.symm
      _ = ‖OscSpace.ofFun r h - c • OscSpace.ofFun r φ‖ := by rw [e4]
      _ ≤ ‖OscSpace.ofFun r h‖ + ‖c • OscSpace.ofFun r φ‖ := norm_sub_le _ _
      _ = oscNorm r h + |c| * oscNorm r φ := by
          rw [norm_smul, Real.norm_eq_abs, e2, e3]
      _ ≤ oscNorm r h + oscNorm r h * oscNorm r φ := by
          have : 0 ≤ oscNorm r φ := Real.sqrt_nonneg _
          gcongr
      _ = _ := by ring

end HRS.MS.BreakdownS67
