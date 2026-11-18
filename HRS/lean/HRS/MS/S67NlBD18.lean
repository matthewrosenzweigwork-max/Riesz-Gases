import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD03
import HRS.MS.S67NlBD12
import HRS.MS.S67NlBD13
import HRS.MS.S67NlBD14B
import HRS.MS.S67NlBD16

/-!
# S6.7 nonlinear breakdown, packet 18: local transport product at level `m - a`

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4757-4759, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). No owned definitions. With `b = m - movA` and
`r = σ - movA`: the weighted local-force profile (16) and the decay extraction `movc2_decay` give
`L_i ∈ Σ^b`; the weighted derivative (13) puts `W_i ψ` in `Σ^(σ-1) ⊆ Σ^r`; the mixed product (12)
at `(b, r)` finishes.
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

theorem s67bd_transport_local (H : Mov2dTh d s β q ρ₀) (m : ℕ) (σ : ℝ)
    (hm : (d : ℝ) / 2 + 7 < m) (hσ : 2 ≤ σ) (hσm : σ + 4 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v ψ : Euc d → ℝ,
      Continuous v → MemOsc (m : ℝ) v → ContDiff ℝ 1 ψ → MemOsc σ ψ →
      (∀ i : Fin d, MemLp (s67bd_D i ψ) 2 volume) → ∀ i : Fin d,
      MemOsc (σ - movA d s) (fun x =>
        s67bd_local d s (fun y => Real.sqrt (ρ₀ y) * v y) i x * s67bd_W ρ₀ i ψ x) ∧
      oscNorm (σ - movA d s) (fun x =>
        s67bd_local d s (fun y => Real.sqrt (ρ₀ y) * v y) i x * s67bd_W ρ₀ i ψ x) ≤
        C * oscNorm (m : ℝ) v * oscNorm σ ψ := by
  have ha1 : 1 ≤ movA d s := le_max_left _ _
  have ha2 : movA d s < 2 := by
    unfold movA; exact max_lt (by norm_num) (by linarith [H.hsd])
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set b : ℝ := (m : ℝ) - movA d s with hbdef
  set r : ℝ := σ - movA d s with hrdef
  have hbd : (d : ℝ) / 2 < b := by rw [hbdef]; linarith
  have hbpos : 0 < b := by linarith
  have hr0 : 0 ≤ r := by rw [hrdef]; linarith
  have hrb : r ≤ b - 1 := by rw [hrdef, hbdef]; linarith
  have hr1 : r ≤ σ - 1 := by rw [hrdef]; linarith
  set K : ℕ := ⌈b⌉₊ with hKdef
  have hK : b ≤ 2 * K := by
    have h1 : b ≤ (K : ℝ) := Nat.le_ceil b
    have h2 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
    push_cast; linarith
  obtain ⟨Cdec, hCdec, hdec⟩ := movc2_decay (d := d) hbpos K hK
  obtain ⟨Cp, hCp, hprof⟩ := s67bd_local_force_profile H m K hm
  obtain ⟨Cw, hCw, hW⟩ := s67bd_weighted_derivative H σ hσ
  obtain ⟨Cpr, hCpr, hprod⟩ := s67bd_product_real d b r hbd hr0 hrb
  refine ⟨Cpr * (Cdec * Cp) * Cw, by positivity, fun v ψ hv hvm hψ1 hψm hψD i => ?_⟩
  obtain ⟨hLm, hLn⟩ := hdec _ _ (hprof v hv hvm i).1
  obtain ⟨hWm, hWn⟩ := hW ψ hψ1 hψm hψD i
  obtain ⟨hWm', hWn'⟩ := mo_mono hr1 hWm
  obtain ⟨hPm, hPn⟩ := hprod _ _ hLm hWm'
  refine ⟨hPm, hPn.trans ?_⟩
  have ho1 : 0 ≤ oscNorm b (fun x =>
      s67bd_local d s (fun y => Real.sqrt (ρ₀ y) * v y) i x) := Real.sqrt_nonneg _
  have ho2 : 0 ≤ oscNorm r (s67bd_W ρ₀ i ψ) := Real.sqrt_nonneg _
  have ho3 : 0 ≤ oscNorm (m : ℝ) v := Real.sqrt_nonneg _
  have ho4 : 0 ≤ oscNorm σ ψ := Real.sqrt_nonneg _
  have h1 := hLn
  have h2 : oscNorm r (s67bd_W ρ₀ i ψ) ≤ Cw * oscNorm σ ψ := hWn'.trans hWn
  calc Cpr * oscNorm b (fun x => s67bd_local d s (fun y => Real.sqrt (ρ₀ y) * v y) i x) *
        oscNorm r (s67bd_W ρ₀ i ψ)
      ≤ Cpr * (Cdec * (Cp * oscNorm (m : ℝ) v)) * (Cw * oscNorm σ ψ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hCpr) h2 ho2 (by positivity)
    _ = _ := by ring

end HRS.MS.BreakdownS67
