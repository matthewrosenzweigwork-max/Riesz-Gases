import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovAdjAux18
import HRS.MS.PoisGradAux2
import HRS.MS.S67NlBD49
import HRS.MS.S67NlBD50

/-!
# S6.7nl.51: Duhamel formula for the one-body semigroup and the nonlinear source
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
Route: the merged `s67_duhamel_abs` is applied to the data of packet 50 for `u(σ) = f(T - βσ)` on
`[0, T/β]` at `σ = (T-r)/β`, then the substitution `v = T - βσ` returns to physical time.  The
interval integrability of the physical source is the continuity of `v ↦ β⁻¹ F((T-v)/β)` on `[r,T]`
(bounded jointly continuous source composed with the clamp), and `T = 0` is a separate branch.
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

set_option maxHeartbeats 3200000 in
theorem s67bd_onebody_duhamel {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (W : ℝ≥0 → Ω → Fin d → ℝ) (hW : IsBrownianFiltration P ℱ W)
    (H : Mov2dTh d s β q ρ₀)
    (j M m : ℕ) (hM : (d : ℝ) / 2 + j + 5 < M)
    (hm : (d : ℝ) / 2 + 7 < m) (hmM : (M : ℝ) + 4 < m)
    (R0 c0 : ℝ) (hR0 : 0 ≤ R0) (hR1 : R0 ≤ 1) (hc0 : 0 ≤ c0)
    (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ)
    (hρ : MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ)
    (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ) (hT : 0 ≤ T)
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f)
    (hφ : MemOsc (M : ℝ) (s67psi ρ₀ φ)) :
    ∀ r ∈ Icc (0 : ℝ) T, ∀ x : Euc d,
      IntervalIntegrable (fun v => sg P W (β * q) (s67bd_oneBodyB d s β ρ₀)
        ((v - r) / β) (s67bd_source d s ρ₀ ρ f v) x) volume r T ∧
      f r x = sg P W (β * q) (s67bd_oneBodyB d s β ρ₀) ((T - r) / β) φ x +
        ∫ v in r..T, sg P W (β * q) (s67bd_oneBodyB d s β ρ₀)
          ((v - r) / β) (s67bd_source d s ρ₀ ρ f v) x := by
  intro r hr x
  have hβ := H.hβ
  have hq' : 0 < β * q := mul_pos hβ H.hq
  obtain ⟨Mb, -, hMb⟩ := s67bd_onebody_drift H 2
  have hdata := s67bd_onebody_data H j M m hM hm hmM R0 c0 hR0 hR1 hc0 f0 ρ hρ T φ f hT hf hφ
  have hWs := sgNoise_of_brownian hW
  rcases hT.eq_or_lt with h0 | hTpos
  · -- the zero horizon
    have hrT : r = T := by linarith [hr.1, hr.2]
    subst hrT
    refine ⟨IntervalIntegrable.refl, ?_⟩
    rw [intervalIntegral.integral_same, sub_self, zero_div,
      HRS.MS.PoisGrad.gs_sg_zero hq'.le (by norm_num) hMb hWs, add_zero]
    exact congrFun hf.terminal x
  · have hT0 : 0 ≤ T / β := (div_pos hTpos hβ).le
    have hrT : r ≤ T := hr.2
    obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = (T - r) / β := ⟨_, rfl⟩
    have hτ0 : 0 ≤ τ := by rw [hτdef]; exact div_nonneg (by linarith) hβ.le
    have hτT : τ ≤ T / β := by
      rw [hτdef]; exact div_le_div_of_nonneg_right (by linarith [hr.1]) hβ.le
    have hτ : τ ∈ Icc (0 : ℝ) (T / β) := ⟨hτ0, hτT⟩
    have hDuh := s67_duhamel_abs hW hq' (le_refl 2) hMb hdata (div_pos hTpos hβ) hτ x
    have hβτ : β * τ = T - r := by rw [hτdef]; field_simp
    have hu0 : f (T - β * 0) x = φ x := by
      rw [mul_zero, sub_zero]; exact congrFun hf.terminal x
    have huτ : f (T - β * τ) x = f r x := by rw [hβτ]; congr 1; ring
    simp only [mul_zero, sub_zero, hf.terminal, huτ] at hDuh
    -- the integrand in physical time
    obtain ⟨g, hgdef⟩ : ∃ g : ℝ → ℝ, g = fun v => sg P W (β * q) (s67bd_oneBodyB d s β ρ₀)
        ((v - r) / β) (s67bd_source d s ρ₀ ρ f v) x := ⟨_, rfl⟩
    have hint_eq : ∫ s' in (0 : ℝ)..τ, sg P W (β * q) (s67bd_oneBodyB d s β ρ₀) (τ - s')
        (fun y => β * s67bd_source d s ρ₀ ρ f (T - β * s') y) x =
        ∫ v in r..T, g v := by
      have h1 : ∀ s' : ℝ, sg P W (β * q) (s67bd_oneBodyB d s β ρ₀) (τ - s')
          (fun y => β * s67bd_source d s ρ₀ ρ f (T - β * s') y) x = β * g (T - β * s') := by
        intro s'
        have et : τ - s' = (T - β * s' - r) / β := by rw [hτdef]; field_simp; ring
        rw [hgdef]
        simp only
        rw [et]
        unfold sg
        simp only [integral_const_mul]
      simp_rw [h1]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_mul (fun v => g v) hβ.ne' T, hβτ]
      simp only [mul_zero, sub_zero, smul_eq_mul]
      rw [show T - (T - r) = r by ring]
      field_simp
    refine ⟨?_, ?_⟩
    · -- interval integrability
      obtain ⟨KS, hKS⟩ := hdata.Sbd
      have hSc : Continuous fun p : ℝ × Euc d =>
          β * s67bd_source d s ρ₀ ρ f (T - β * clampT (T / β) p.1) p.2 :=
        s67_comp_clamp (g := fun σ y => β * s67bd_source d s ρ₀ ρ f (T - β * σ) y) hT0 hdata.Scont
      have hF := s67_cont_sg_comp hW hq' (le_refl 2) hMb hT0
        (g := fun r' y => β * s67bd_source d s ρ₀ ρ f (T - β * clampT (T / β) r') y) hSc
        (fun r' y => hKS _ (clampT_mem hT0 r') y) hτ x
      obtain ⟨Fs, hFs⟩ : ∃ Fs : ℝ → ℝ, Fs = fun s' => sg P W (β * q)
          (s67bd_oneBodyB d s β ρ₀) (τ - s')
          (fun y => β * s67bd_source d s ρ₀ ρ f (T - β * clampT (T / β) s') y) x := ⟨_, rfl⟩
      have hF' : ContinuousOn Fs (Icc 0 τ) := by rw [hFs]; exact hF
      have hcomp : ContinuousOn (fun v : ℝ => (T - v) / β) (Icc r T) := by fun_prop
      have hmaps : MapsTo (fun v : ℝ => (T - v) / β) (Icc r T) (Icc (0 : ℝ) τ) := by
        intro v hv
        refine ⟨div_nonneg (by linarith [hv.2]) hβ.le, ?_⟩
        rw [hτdef]; exact div_le_div_of_nonneg_right (by linarith [hv.1]) hβ.le
      have hgc : ContinuousOn g (Icc r T) := by
        have h2 : ContinuousOn (fun v : ℝ => β⁻¹ * Fs ((T - v) / β)) (Icc r T) :=
          continuousOn_const.mul (hF'.comp hcomp hmaps)
        refine h2.congr (fun v hv => ?_)
        have hs' := hmaps hv
        have hcl : clampT (T / β) ((T - v) / β) = (T - v) / β :=
          clampT_of_mem ⟨hs'.1, hs'.2.trans hτT⟩
        have e1 : T - β * ((T - v) / β) = v := by field_simp; ring
        have e2 : τ - (T - v) / β = (v - r) / β := by rw [hτdef]; field_simp; ring
        have e3 : Fs ((T - v) / β) = β * g v := by
          rw [hFs, hgdef]
          simp only
          rw [hcl, e1, e2]
          unfold sg
          simp only [integral_const_mul]
        show g v = β⁻¹ * Fs ((T - v) / β)
        rw [e3]
        field_simp
      rw [← hgdef]
      exact hgc.intervalIntegrable_of_Icc hrT
    · rw [← hτdef, hDuh, hint_eq, hgdef]

end HRS.MS.BreakdownS67
