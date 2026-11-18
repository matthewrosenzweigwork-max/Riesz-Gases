import HRS.MS.SA16TAp3

/-!
# S.A.16 (SA16T) Ap3b: joint continuity of the reversed-time drift and density on `[0,t] × ℝ^d`
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16P Phase2SA16Evolution Phase2SA16Transfer

section Ap3b
variable {d : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
lemma sa16t_b_cont (hd : 1 ≤ d) {s MB Λ ΛV G₀ νbar T : ℝ} {m : ℕ} {D : WholeDyn d} {μ : ℝ → Euc d → ℝ}
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) T) :
    ContinuousOn (fun q : ℝ × Euc d => sa16t_b D μ t q.1 q.2) (Icc (0 : ℝ) t ×ˢ univ) := by
  obtain ⟨hDs, hs0, hsd⟩ := hD.hs
  have h := sa16t_drift_cont (MB := MB) hd hs0 hsd m (ht.1.le.trans ht.2) hDs hD.hV hD.hμ
  have hf : ContinuousOn (fun q : ℝ × Euc d => (t - q.1, q.2)) (Icc (0 : ℝ) t ×ˢ univ) :=
    ((continuous_const.sub continuous_fst).prodMk continuous_snd).continuousOn
  have hm : MapsTo (fun q : ℝ × Euc d => (t - q.1, q.2)) (Icc (0 : ℝ) t ×ˢ univ) (Icc (0 : ℝ) T ×ˢ univ) :=
    fun q hq => ⟨⟨by linarith [hq.1.2], by linarith [hq.1.1, ht.2]⟩, trivial⟩
  have := ContinuousOn.comp (g := fun q : ℝ × Euc d => meanFieldDriftW D (μ q.1) q.2) h hf hm
  refine this.congr (fun q _ => ?_)
  simp only [Function.comp, sa16t_b]

lemma sa16t_mu_cont_rev (hd : 1 ≤ d) {s Λ T : ℝ} {m : ℕ} {μ : ℝ → Euc d → ℝ} (hμ : CoeffHypRd s m Λ T μ)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) T) :
    ContinuousOn (fun q : ℝ × Euc d => (fun σ => μ (t - σ)) q.1 q.2) (Icc (0 : ℝ) t ×ˢ univ) := by
  have h := sa16t_mu_cont hd (ht.1.le.trans ht.2) hμ
  have hf : ContinuousOn (fun q : ℝ × Euc d => (t - q.1, q.2)) (Icc (0 : ℝ) t ×ˢ univ) :=
    ((continuous_const.sub continuous_fst).prodMk continuous_snd).continuousOn
  have hm : MapsTo (fun q : ℝ × Euc d => (t - q.1, q.2)) (Icc (0 : ℝ) t ×ˢ univ) (Icc (0 : ℝ) T ×ˢ univ) :=
    fun q hq => ⟨⟨by linarith [hq.1.2], by linarith [hq.1.1, ht.2]⟩, trivial⟩
  have := ContinuousOn.comp (g := fun q : ℝ × Euc d => μ q.1 q.2) h hf hm
  exact this

end Ap3b

end HRS.Whole.AppendixA.Phase2SA16R
