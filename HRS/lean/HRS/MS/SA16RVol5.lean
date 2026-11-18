import HRS.MS.SA16RVol4

/-!
# S.A.16 (SA16R) Vol5: gain kernels `Γ s ∘ K (τ - s)`, triangle Fubini

* `GainData T C B Γ K`: `Γ s : Y →L X` (heat semigroup with gain of regularity, `‖Γ s‖ ≤ C s^{-1/2}`, strongly continuous on `(0,T]`),
  `K r : X →L Y` (bounded, strongly continuous on `[0,T]`, the perturbation).
* `GainData.voltKer`: the Duhamel kernel `gainKer Γ K τ s = Γ s ∘ K (τ - s)` satisfies `VoltKer T (C*B)`.
* `sa16r_Gamma_cont`: `(r,σ) ↦ Γ σ (g r)` is continuous on `{r ∈ [0,T], 0 < σ ≤ T}` for `g` continuous.
* `sa16r_tri_swap`: Fubini on the triangle `{0 < y ≤ x ≤ a}` for real functions.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16R

section Gain
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

structure GainData (T C B : ℝ) (Γ : ℝ → Y →L[ℝ] X) (K : ℝ → X →L[ℝ] Y) : Prop where
  Γbound : ∀ s : ℝ, 0 < s → s ≤ T → ‖Γ s‖ ≤ C * s ^ (-(1 / 2 : ℝ))
  Γcont : ∀ y : Y, ContinuousOn (fun s => Γ s y) (Ioc 0 T)
  Kbound : ∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ B
  Kcont : ∀ x : X, ContinuousOn (fun r => K r x) (Icc 0 T)

/-- the Duhamel kernel -/
def gainKer (Γ : ℝ → Y →L[ℝ] X) (K : ℝ → X →L[ℝ] Y) : ℝ → ℝ → X →L[ℝ] X :=
  fun τ s => (Γ s).comp (K (τ - s))

/-- local bound of `Γ` near a point of `(0,T]` -/
lemma GainData.local_bound {T C B : ℝ} {Γ : ℝ → Y →L[ℝ] X} {K : ℝ → X →L[ℝ] Y}
    (h : GainData T C B Γ K) (hC : 0 ≤ C) {s0 : ℝ} (hs0 : 0 < s0) :
    ∀ᶠ s in 𝓝[Ioc 0 T] s0, ‖Γ s‖ ≤ C * (s0 / 2) ^ (-(1 / 2 : ℝ)) := by
  have : ∀ᶠ s in 𝓝 s0, s0 / 2 < s := lt_mem_nhds (by linarith)
  filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with s hs hsm
  refine (h.Γbound s hsm.1 hsm.2).trans ?_
  have h3 : 0 < s0 / 2 := by linarith
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos h3 hs.le (by norm_num)) hC

end Gain

section Gain2
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma sa16r_Gamma_cont {T C B : ℝ} {Γ : ℝ → Y →L[ℝ] X} {K : ℝ → X →L[ℝ] Y}
    (h : GainData T C B Γ K) (hC : 0 ≤ C) {g : ℝ → Y} (hg : ContinuousOn g (Icc 0 T)) :
    ContinuousOn (fun q : ℝ × ℝ => Γ q.2 (g q.1)) {q | q.1 ∈ Icc (0 : ℝ) T ∧ 0 < q.2 ∧ q.2 ≤ T} := by
  intro q0 hq0
  obtain ⟨h1, h2, h3⟩ := hq0
  refine sa16r_clm_apply_strong (F := fun q : ℝ × ℝ => Γ q.2) (B := C * (q0.2 / 2) ^ (-(1 / 2 : ℝ)))
    (fun v => ?_) ?_ ?_
  · have hc : ContinuousWithinAt (fun s : ℝ => Γ s v) (Ioc 0 T) q0.2 := h.Γcont v q0.2 ⟨h2, h3⟩
    exact ContinuousWithinAt.comp (g := fun s : ℝ => Γ s v) (f := fun q : ℝ × ℝ => q.2)
      (t := Ioc 0 T) hc continuous_snd.continuousWithinAt (fun q hq => ⟨hq.2.1, hq.2.2⟩)
  · have hb := h.local_bound hC h2
    have hcomp : Tendsto (fun q : ℝ × ℝ => q.2)
        (𝓝[{q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) T ∧ 0 < q.2 ∧ q.2 ≤ T}] q0) (𝓝[Ioc 0 T] q0.2) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_snd.tendsto q0).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with q hq using (⟨hq.2.1, hq.2.2⟩ : q.2 ∈ Ioc 0 T)
    exact hcomp.eventually hb
  · exact ContinuousWithinAt.comp (g := g) (f := fun q : ℝ × ℝ => q.1) (t := Icc 0 T)
      (hg q0.1 h1) continuous_fst.continuousWithinAt (fun q hq => hq.1)

end Gain2

section Gain3
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma GainData.voltKer {T C B : ℝ} {Γ : ℝ → Y →L[ℝ] X} {K : ℝ → X →L[ℝ] Y}
    (h : GainData T C B Γ K) (hC : 0 ≤ C) (hB : 0 ≤ B) : VoltKer T (C * B) (gainKer Γ K) := by
  refine ⟨fun τ s hs hsτ hτ => ?_, fun x => ?_⟩
  · have h1 := h.Γbound s hs (hsτ.trans hτ)
    have h2 := h.Kbound (τ - s) ⟨by linarith, by linarith⟩
    calc ‖gainKer Γ K τ s‖ ≤ ‖Γ s‖ * ‖K (τ - s)‖ := (Γ s).opNorm_comp_le _
      _ ≤ (C * s ^ (-(1 / 2 : ℝ))) * B :=
          mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hs.le _))
      _ = C * B * s ^ (-(1 / 2 : ℝ)) := by ring
  · have hg : ContinuousOn (fun r => K r x) (Icc 0 T) := h.Kcont x
    have hc := sa16r_Gamma_cont h hC hg
    have hmap : ContinuousOn (fun q : ℝ × ℝ => (q.1 - q.2, q.2))
        {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T} :=
      ((continuous_fst.sub continuous_snd).prodMk continuous_snd).continuousOn
    exact hc.comp hmap (fun q hq => ⟨⟨by linarith [hq.2.1], by linarith [hq.1, hq.2.2]⟩, hq.1, hq.2.1.trans hq.2.2⟩)

end Gain3

end HRS.Whole.AppendixA.Phase2SA16R
