import HRS.MS.SA16Y5Mi1

/-!
# S.A.16 (SA16Y5) Mi2: existence and uniqueness of the mild solution, fractional order (B8, part 2)

`sa16y5f_mild`: under the hypotheses of `sa16y5f_voltKer` there is a unique `u ∈ C([0,T]; W^{m+2,p})` with
`u τ = e^{ντΔ}φ + ∫_0^τ Q s (τ-s) (u (τ-s)) ds`, `Q = sa16y5f_kernel`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Mi2
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

set_option maxHeartbeats 1600000 in
theorem sa16y5f_mild {m : ℕ} {ν T BB CN γ : ℝ} (hν : 0 < ν) (hT : 0 < T) (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1)
    (Bf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hBb : ∀ r ∈ Icc (0 : ℝ) T, ‖Bf r‖ ≤ BB)
    (hBc : ∀ x, ContinuousOn (fun r => Bf r x) (Icc 0 T))
    (Nf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p)
    (hNc : ∀ x, ContinuousOn (fun r => Nf r x) (Icc 0 T))
    (hsharp : ∀ r ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioc (0 : ℝ) T, ‖sa16y5_Qh d m p (ν * s) (Nf r)‖ ≤ CN * s ^ (-γ))
    (φ : WmpSpace d (m + 1 + 1) p) :
    ∃ u : ℝ → WmpSpace d (m + 1 + 1) p, ContinuousOn u (Icc 0 T) ∧
      (∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d (m + 1) p ν φ τ +
        voltOp (fun τ s => sa16y5f_kernel d m p ν Bf Nf s (τ - s)) u τ) ∧
      ∀ v : ℝ → WmpSpace d (m + 1 + 1) p, ContinuousOn v (Icc 0 T) →
        (∀ τ ∈ Icc (0 : ℝ) T, v τ = sa16r_f0 d (m + 1) p ν φ τ +
          voltOp (fun τ s => sa16y5f_kernel d m p ν Bf Nf s (τ - s)) v τ) → ∀ τ ∈ Icc (0 : ℝ) T, v τ = u τ := by
  obtain ⟨C, hC0, hb, hc⟩ := sa16y5f_voltKer hν hT hγ hγ1 Bf hBb hBc Nf hNc hsharp
  have hP : VoltKerG γ T C (fun τ s => sa16y5f_kernel d m p ν Bf Nf s (τ - s)) := by
    refine ⟨by linarith, hγ1, fun τ s hs hsτ hτ => ?_, fun x => ?_⟩
    · exact hb (τ - s) ⟨by linarith, by linarith⟩ s ⟨hs, hsτ.trans hτ⟩
    · have hmap : ContinuousOn (fun q : ℝ × ℝ => (q.1 - q.2, q.2))
          {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T} :=
        ((continuous_fst.sub continuous_snd).prodMk continuous_snd).continuousOn
      have hmem : ∀ q ∈ {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T},
          (fun q : ℝ × ℝ => (q.1 - q.2, q.2)) q ∈ {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) T ∧ 0 < q.2 ∧ q.2 ≤ T} :=
        fun q hq => ⟨⟨by linarith [hq.2.1], by linarith [hq.1, hq.2.2]⟩, hq.1, hq.2.1.trans hq.2.2⟩
      have h := (hc x).comp hmap hmem
      refine h.congr (fun q _ => ?_)
      rfl
  have hf0 : ContinuousOn (sa16r_f0 d (m + 1) p ν φ) (Icc 0 T) := sa16r_f0_cont hν (m + 1) φ
  have := sa16y5g_volt_exists_unique (X := WmpSpace d (m + 1 + 1) p) (γ := γ) (T := T) (C := C)
    (P := fun τ s => sa16y5f_kernel d m p ν Bf Nf s (τ - s)) hP hT hf0
  exact this

end Mi2

end HRS.Whole.AppendixA.Phase2SA16R
