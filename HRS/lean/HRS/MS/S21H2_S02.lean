import HRS.MS.S21F_S02a
import HRS.MS.S21F_S00
import HRS.MS.R2ScrAux1
import HRS.MS.R2ScrAux2

/-!
# S21H2, packet R26-T3.S02: smooth response representatives at a fixed finite order

For the ACTUAL initial reference (`TcRef` of the datum `r26t3_reference_data` at the finite order `N₀`) and `γ > 0`:
`tc5_resolvent_rep` (output order `m = 2d + 12 ≤ J = 4d + 40`, `M = ⌈(m + d/2)/(d-s)⌉ + 1`, `N₀ = m + ⌈M(d-s)+d⌉ + 1`) gives a
`C_b^m` representative `r` with `‖r‖ ≤ C‖q‖_{C_b^J}`; `s98_resp_rep` (continuity + positive density) identifies
the everywhere-defined `responseRepW = r26t3_a` with `γ⁻¹ r`.  The everywhere identity `a + γ K a = P q` uses
`Kop` depends only on the `μ₀`-class (`s98_kop_congr_ae`) and `r26t3_a = responseInverse` a.e. (`r26t3_response_ae`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole

theorem r26t3_response_smooth {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1/2)
    (R : Trajectory p δ) (hγ : 0 < p.γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Euc p.d → ℝ, MemCb (r26t3_J p.d) q →
      MemCb (r26t3_k p.d+2) (r26t3_a R q) ∧
      cbNorm (r26t3_k p.d+2) (r26t3_a R q) ≤ C * cbNorm (r26t3_J p.d) q ∧
      HRS.Whole.MemL2Zero (r26t3_mu R 0) (r26t3_a R q) ∧
      (∀ x, r26t3_a R q x + p.γ * HRS.Whole.Kop (rieszKernel p.d p.s) (r26t3_mu R 0) (r26t3_a R q) x =
        HRS.Whole.projMean (r26t3_mu R 0) q x) := by
  have hd := p.hd
  have hsd : p.s < (p.d : ℝ) := by
    have := p.hs
    have : (0 : ℝ) < p.d := by exact_mod_cast (by omega : 0 < p.d)
    linarith
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  set m : ℕ := r26t3_k p.d + 2 with hm
  have hmJ : m ≤ r26t3_J p.d := by simp only [hm, r26t3_k, r26t3_J]; omega
  set M : ℕ := ⌈((m : ℝ) + p.d / 2) / ((p.d : ℝ) - p.s)⌉₊ + 1 with hM
  have hMs : (m : ℝ) + p.d / 2 < M * ((p.d : ℝ) - p.s) := HRS.MS.Tc5.tc5_M_spec hsd m
  set N0 : ℕ := m + ⌈(M : ℝ) * ((p.d : ℝ) - p.s) + p.d⌉₊ + 1 with hN0
  have hmN : m ≤ N0 := by omega
  have hN : (M : ℝ) * ((p.d : ℝ) - p.s) + p.d < N0 := by
    have h1 := Nat.le_ceil ((M : ℝ) * ((p.d : ℝ) - p.s) + p.d)
    have : ((⌈(M : ℝ) * ((p.d : ℝ) - p.s) + p.d⌉₊ : ℕ) : ℝ) + 1 ≤ N0 := by
      rw [hN0]; push_cast; have : (0 : ℝ) ≤ m := by positivity
      linarith
    linarith
  obtain ⟨M₀, c, S, hc, hTc⟩ := href N0
  obtain ⟨C5, hC5, hC5ρ⟩ := HRS.MS.Tc5.tc5_resolvent_rep (d := p.d) p.hs0 hsd m (r26t3_J p.d) M hmJ hMs
    p.γ M₀ c S hc N0 hmN hN
  have hP : IsProbabilityMeasure (r26t3_mu R 0) := HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  refine ⟨p.γ⁻¹ * C5, by have := inv_nonneg.2 hγ.le; positivity, fun q hq => ?_⟩
  obtain ⟨r₀, r, hr₀, hae, hr, hbd, hrr⟩ := hC5ρ _ hTc p.γ hγ le_rfl q hq
  have hrc : Continuous r := hr.1.continuous
  obtain ⟨hrep, hrespW⟩ := HRS.MS.S98.s98_resp_rep (d := p.d) (by omega) p.hs0 hsd hc hTc hγ
    hq.1.continuous hrc (B := cbNorm m r) (fun x => by
      have := HRS.MS.Tc5.tc5_cb_sup_le hr x
      rwa [Real.norm_eq_abs] at this) hr₀ hae hrr
  have hrepf : r26t3_a R q = fun x => p.γ⁻¹ * r x := funext hrep
  have hsm := HRS.MS.Tc5.tc5_cb_smul p.γ⁻¹ hr
  refine ⟨?_, ?_, hrespW.1, fun x => ?_⟩
  · rw [hrepf]; exact hsm.1
  · rw [hrepf]
    refine hsm.2.trans ?_
    rw [abs_of_nonneg (inv_nonneg.2 hγ.le), mul_assoc]
    exact mul_le_mul_of_nonneg_left hbd (inv_nonneg.2 hγ.le)
  · have hae' := r26t3_response_ae hδ hδh R q (HRS.MS.Tc5.tc5_memLp_of_cb hq)
    have hK := HRS.MS.S98.s98_kop_congr_ae (g := rieszKernel p.d p.s) hae'
    rw [hK]
    show HRS.Whole.projMean (r26t3_mu R 0) q x - p.γ * HRS.Whole.Kop (rieszKernel p.d p.s)
      (r26t3_mu R 0) (HRS.Whole.responseInverse (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ q) x +
        p.γ * HRS.Whole.Kop (rieszKernel p.d p.s) (r26t3_mu R 0)
          (HRS.Whole.responseInverse (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ q) x = _
    ring

end HRS.MS.R26T3
