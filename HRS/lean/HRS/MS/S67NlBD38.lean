import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD00
import HRS.MS.S67NlBD01
import HRS.MS.S67NlBD06
import HRS.MS.S67NlBD25
import HRS.MS.S67NlBD29
import HRS.MS.S67NlBD30
import HRS.MS.S67NlBD32
import HRS.MS.S67NlBD37

/-!
# S6.7nl.38: one finite-horizon oscillator bootstrap increment
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
Route: Duhamel (packet 32) writes the actual `ψ_r` as `T†(T-r) ψ_T` plus the source convolution; the
source `R_v` sits in `Σ^{σ-a}` with a finite bound (packets 06, 25), the convolution gains up to
`σ' = min(M, σ+δ)` (packet 37), and the terminal term is bounded by the semigroup smoothing at level `M`.
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

set_option maxHeartbeats 1600000 in
theorem s67bd_bootstrap_step (H : Mov2dTh d s β q ρ₀)
    (M m : ℕ) (hm : (d : ℝ) / 2 + 7 < m) (hmM : (M : ℝ) + 4 < m)
    (R0 c0 : ℝ) (hR0 : 0 ≤ R0) (hc0 : 0 ≤ c0)
    (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ)
    (hρ : MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ)
    (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ) (hT : 0 ≤ T)
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f)
    (hφ : MemOsc (M : ℝ) (s67psi ρ₀ φ))
    (σ : ℝ) (hσ : 2 ≤ σ) (hσM : σ ≤ M) (B : ℝ) (hB : 0 ≤ B)
    (hfin : ∀ r ∈ Icc (0 : ℝ) T, MemOsc σ (s67psi ρ₀ (f r)) ∧
      oscNorm σ (s67psi ρ₀ (f r)) ≤ B) :
    ∃ B' : ℝ, 0 ≤ B' ∧ ∀ r ∈ Icc (0 : ℝ) T,
      MemOsc (min (M : ℝ) (σ + s67bd_delta d s)) (s67psi ρ₀ (f r)) ∧
      oscNorm (min (M : ℝ) (σ + s67bd_delta d s)) (s67psi ρ₀ (f r)) ≤ B' := by
  -- index arithmetic
  have ha1 : 1 ≤ movA d s := le_max_left _ _
  have ha2 : movA d s < 2 := by
    unfold movA; exact max_lt (by norm_num) (by linarith [H.hsd])
  have hδdef : s67bd_delta d s = (2 - movA d s) / 2 := rfl
  have hδ0 : 0 < s67bd_delta d s := by rw [hδdef]; linarith
  obtain ⟨σ', hσ'⟩ : ∃ σ' : ℝ, σ' = min (M : ℝ) (σ + s67bd_delta d s) := ⟨_, rfl⟩
  rw [← hσ']
  have hσ'M : σ' ≤ M := hσ' ▸ min_le_left _ _
  have hσ'σ : σ' ≤ σ + s67bd_delta d s := hσ' ▸ min_le_right _ _
  have hp0 : 0 ≤ σ - movA d s := by linarith
  have hpq : σ - movA d s ≤ σ' := hσ' ▸ le_min (by linarith) (by linarith)
  have hgain : σ' - (σ - movA d s) < 2 := by linarith
  have hσ4 : σ + 4 < m := by linarith
  have hAM : movA d s ≤ M := by linarith
  -- ingredients
  obtain ⟨hρsm, hρpos⟩ := mov2d_rho_data H
  obtain ⟨ψs, hψs⟩ := mov2d_sqrt_schwartz H
  have hsqc : Continuous (fun x => Real.sqrt (ρ₀ x)) := by
    rw [← hψs]; exact ψs.continuous
  obtain ⟨g, hg⟩ := mov2d_sqrt_schwartz H
  obtain ⟨Ψ, R, hrep⟩ := s67bd_classical_realizations H m hm R0 c0 f0 ρ hρ T φ f hT hf
  obtain ⟨-, hRc, -⟩ := s67bd_source_continuity H m hm R0 c0 f0 ρ hρ T φ f hT hf Ψ R hrep
  obtain ⟨C25, hC25, h25⟩ := s67bd_projected_source_bound H m σ hm hσ hσ4
  obtain ⟨C37, hC37, h37⟩ := s67bd_convolution_gain H g hg (σ - movA d s) σ' T hp0 hpq hgain hT
  obtain ⟨-, -, -, c, hc, hsm⟩ := s67bd_semigroup_data H g hg
  obtain ⟨CT, hCT1, hCT⟩ := hsm M hAM
  obtain ⟨Bψ, -, hBψ⟩ := s67bd_classical_sigma2 H ρ T φ f hT hf
  -- the source bound
  set Bs : ℝ := C25 * R0 * B with hBs
  have hBs0 : 0 ≤ Bs := by positivity
  have hsrc : ∀ v ∈ Icc (0 : ℝ) T, MemOsc (σ - movA d s) (movFun (R v)) ∧
      oscNorm (σ - movA d s) (movFun (R v)) ≤ Bs := by
    intro v hv
    have hvc : Continuous (movV ρ₀ ρ v) := by
      show Continuous (fun x => (ρ v x - ρ₀ x) / Real.sqrt (ρ₀ x))
      exact ((hρ.regular v hv.1).sub hρsm.continuous).div hsqc
        (fun x => (Real.sqrt_pos.2 (hρpos x)).ne')
    obtain ⟨-, -, hψ2, hD⟩ := hBψ v hv
    obtain ⟨hmem, -, -, hn⟩ := h25 _ _ hvc (hρ.weighted v hv.1).1 hψ2 (hfin v hv).1 hD
    have hae : movFun (R v) =ᵐ[volume] _ := (hrep v hv).2
    refine ⟨HRS.MS.MovLin.mov2b_memOsc_congr hae.symm _ hmem, ?_⟩
    rw [HRS.MS.MovLin.mov2b_oscNorm_congr hae]
    refine hn.trans ?_
    have h1 : oscNorm (m : ℝ) (movV ρ₀ ρ v) ≤ R0 := by
      refine (hρ.weighted v hv.1).2.trans ?_
      have : Real.exp (-c0 * v) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hv.1])
      nlinarith
    have h2 := (hfin v hv).2
    have h3 := HRS.MS.MovC1.movc1_osc_nonneg (m : ℝ) (movV ρ₀ ρ v)
    have h4 := HRS.MS.MovC1.movc1_osc_nonneg σ (s67psi ρ₀ (f v))
    calc C25 * oscNorm (m : ℝ) (movV ρ₀ ρ v) * oscNorm σ (s67psi ρ₀ (f v))
        ≤ C25 * R0 * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hC25) h2 h4 (by positivity)
      _ = Bs := rfl
  -- terminal data
  have hfT : f T = φ := hf.terminal
  have hΨT : movFun (Ψ T) =ᵐ[volume] s67psi ρ₀ φ := by
    have := (hrep T ⟨hT, le_rfl⟩).1
    rw [hfT] at this; exact this
  have hΨTm : MemOsc (M : ℝ) (movFun (Ψ T)) :=
    HRS.MS.MovLin.mov2b_memOsc_congr hΨT.symm _ hφ
  have hΨTn : oscNorm (M : ℝ) (movFun (Ψ T)) = oscNorm (M : ℝ) (s67psi ρ₀ φ) :=
    HRS.MS.MovLin.mov2b_oscNorm_congr hΨT _
  have hN0 := HRS.MS.MovC1.movc1_osc_nonneg (M : ℝ) (s67psi ρ₀ φ)
  refine ⟨CT * oscNorm (M : ℝ) (s67psi ρ₀ φ) + C37 * Bs, by positivity, fun r hr => ?_⟩
  -- homogeneous term
  obtain ⟨hAm, hAn⟩ := hCT.1 (T - r) (sub_nonneg.2 hr.2) (Ψ T) hΨTm
  have hexp : Real.exp (-c * (T - r)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [sub_nonneg.2 hr.2])
  have hA1 := mo_mono hσ'M hAm
  have hA2 : oscNorm σ' (movFun (s67bd_Tdag H g hg (T - r) (Ψ T))) ≤
      CT * oscNorm (M : ℝ) (s67psi ρ₀ φ) := by
    refine hA1.2.trans (hAn.trans ?_)
    rw [hΨTn]
    have : CT * Real.exp (-c * (T - r)) ≤ CT := by nlinarith
    exact mul_le_mul_of_nonneg_right this hN0
  -- the source integral
  obtain ⟨hI1, hI2⟩ := h37 Bs hBs0 R hRc hsrc r hr
  -- Duhamel
  obtain ⟨-, -, heq⟩ := s67bd_duhamel_l2 H g hg m hm R0 c0 f0 ρ hρ T φ f hT hf Ψ R hrep r hr
  have hsumae : movFun (Ψ r) =ᵐ[volume] fun x =>
      movFun (s67bd_Tdag H g hg (T - r) (Ψ T)) x +
        movFun (∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (R v)) x := by
    rw [heq]; exact Lp.coeFn_add _ _
  have hψae : s67psi ρ₀ (f r) =ᵐ[volume] fun x =>
      movFun (s67bd_Tdag H g hg (T - r) (Ψ T)) x +
        movFun (∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (R v)) x :=
    (show movFun (Ψ r) =ᵐ[volume] _ from (hrep r hr).1).symm.trans hsumae
  obtain ⟨hS1, hS2⟩ := HRS.MS.MovC1.movc1_osc_add σ' hA1.1 hI1
  refine ⟨HRS.MS.MovLin.mov2b_memOsc_congr hψae.symm _ hS1, ?_⟩
  rw [HRS.MS.MovLin.mov2b_oscNorm_congr hψae]
  exact hS2.trans (add_le_add hA2 hI2)

end HRS.MS.BreakdownS67
