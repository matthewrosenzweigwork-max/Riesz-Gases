import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD02
import HRS.MS.S67NlBD03
import HRS.MS.S67NlBD08
import HRS.MS.S67NlBD14B
import HRS.MS.S67NlBD15A
import HRS.MS.S67NlBD15C
import HRS.MS.S67NlBD15E
import HRS.MS.S67NlBD15B
import HRS.MS.S67NlBD15D

/-!
# S6.7 nonlinear, packet S6.7nl.16: weighted local-force profile and the density-limit glue theorem

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4238-4245, 4757-4759, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). No owned definitions. Owns the existing glue
`s67bd_local_force_density` (historical S6.7nl.15) and the quantitative profile theorem
`s67bd_local_force_profile`; both bodies are preserved from the producer glue and integrate the
already-merged producers (15A, 15B, 15C, 15D) at the weights K and K+1.
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

theorem s67bd_local_force_density (H : Mov2dTh d s β q ρ₀)
    (m K : ℕ) (hm : (d : ℝ) / 2 + 7 < m)
    (v : Euc d → ℝ) (hvc : Continuous v) (hv : MemOsc (m : ℝ) v) :
    ∃ vn : ℕ → SchwartzMap (Euc d) ℝ,
      Tendsto (fun n => oscNorm (m : ℝ) (fun x => vn n x - v x)) atTop (𝓝 0) ∧
      ∀ i : Fin d,
        HRS.PDE.ToolboxRd.MemSobolev ((m : ℝ) - movA d s)
          (fun x => (1 + ‖x‖ ^ 2) ^ K *
            s67bd_local d s (fun y => Real.sqrt (ρ₀ y) * v y) i x) ∧
        Tendsto (fun n => s67bd_Hnorm ((m : ℝ) - movA d s)
          (fun x => (1 + ‖x‖ ^ 2) ^ K *
            (s67bd_local d s (fun y => Real.sqrt (ρ₀ y) * vn n y) i x -
             s67bd_local d s (fun y => Real.sqrt (ρ₀ y) * v y) i x))) atTop (𝓝 0) ∧
        HRS.PDE.ToolboxRd.MemSobolev ((m : ℝ) - movA d s)
          (fun x => (1 + ‖x‖ ^ 2) ^ K *
            (x i * s67bd_local d s (fun y => Real.sqrt (ρ₀ y) * v y) i x)) := by
  obtain ⟨vn, hconv, hpoint⟩ := s67bd_local_approximation H m hm v hvc hv
  obtain ⟨C, hC, hlimit⟩ := s67bd_weighted_profile_limit H m K hm
  obtain ⟨C', hC', hlimit'⟩ := s67bd_weighted_profile_limit H m (K + 1) hm
  have hb : 0 ≤ (m : ℝ) - movA d s := by
    have ha : movA d s < 2 := by unfold movA; exact max_lt (by norm_num) (by linarith [H.hsd])
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨Cx, hCx, hx⟩ := s67bd_coordinate_profile_transfer H m K hm
  refine ⟨vn, hconv, fun i => ?_⟩
  obtain ⟨w, hw, hwn, hwl, hwb⟩ := hlimit v hv vn hconv i
  have hi := s67bd_sobolev_limit_identify d _ hb
    (fun n => s67bd_profile d s ρ₀ (vn n) K i) w (s67bd_profile d s ρ₀ v K i)
    hw hwn hwl (hpoint K i).1 (hpoint K i).2.2
  obtain ⟨w', hw', hwn', hwl', hwb'⟩ := hlimit' v hv vn hconv i
  have hi' := s67bd_sobolev_limit_identify d _ hb
    (fun n => s67bd_profile d s ρ₀ (vn n) (K + 1) i) w'
    (s67bd_profile d s ρ₀ v (K + 1) i)
    hw' hwn' hwl' (hpoint (K + 1) i).1 (hpoint (K + 1) i).2.2
  refine ⟨hi.2.1, ?_, (hx v hvc hv vn hconv i hi'.2.1 hwn' hi'.2.2.1).1⟩
  simpa only [s67bd_profile, mul_sub] using hi.2.2.1

theorem s67bd_local_force_profile (H : Mov2dTh d s β q ρ₀)
    (m K : ℕ) (hm : (d : ℝ) / 2 + 7 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Euc d → ℝ, Continuous v → MemOsc (m : ℝ) v →
      ∀ i : Fin d,
        movc2_SB ((m : ℝ) - movA d s) (C * oscNorm (m : ℝ) v)
          (fun x => (1 + ‖x‖ ^ 2) ^ K *
            s67bd_local d s (fun y => Real.sqrt (ρ₀ y) * v y) i x) ∧
        movc2_SB ((m : ℝ) - movA d s) (C * oscNorm (m : ℝ) v)
          (fun x => (1 + ‖x‖ ^ 2) ^ K *
            (x i * s67bd_local d s (fun y => Real.sqrt (ρ₀ y) * v y) i x)) := by
  obtain ⟨Cb, hCb, hbase⟩ := s67bd_weighted_profile_limit H m K hm
  obtain ⟨Ch, hCh, hhigher⟩ := s67bd_weighted_profile_limit H m (K + 1) hm
  obtain ⟨Cx, hCx, hcoord⟩ := s67bd_coordinate_profile_transfer H m K hm
  have hb : 0 ≤ (m : ℝ) - movA d s := by
    have ha : movA d s < 2 := by unfold movA; exact max_lt (by norm_num) (by linarith [H.hsd])
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  refine ⟨Cb + Cx, add_nonneg hCb hCx, fun v hvc hv => ?_⟩
  obtain ⟨vn, hconv, hpoint⟩ := s67bd_local_approximation H m hm v hvc hv
  intro i
  obtain ⟨w, hw, hwn, hwl, hwb⟩ := hbase v hv vn hconv i
  have hi := s67bd_sobolev_limit_identify d _ hb
    (fun n => s67bd_profile d s ρ₀ (vn n) K i) w (s67bd_profile d s ρ₀ v K i)
    hw hwn hwl (hpoint K i).1 (hpoint K i).2.2
  obtain ⟨w', hw', hwn', hwl', hwb'⟩ := hhigher v hv vn hconv i
  have hi' := s67bd_sobolev_limit_identify d _ hb
    (fun n => s67bd_profile d s ρ₀ (vn n) (K + 1) i) w'
    (s67bd_profile d s ρ₀ v (K + 1) i)
    hw' hwn' hwl' (hpoint (K + 1) i).1 (hpoint (K + 1) i).2.2
  have hx := hcoord v hvc hv vn hconv i hi'.2.1 hwn' hi'.2.2.1
  have hvnorm : 0 ≤ oscNorm (m : ℝ) v := Real.sqrt_nonneg _
  refine ⟨⟨hi.2.1, ?_⟩, ⟨hx.1, ?_⟩⟩
  · change s67bd_Hnorm ((m : ℝ) - movA d s) (s67bd_profile d s ρ₀ v K i) ≤ _
    rw [hi.2.2.2]
    exact hwb.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCx) hvnorm)
  · exact hx.2.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCb) hvnorm)

end HRS.MS.BreakdownS67
