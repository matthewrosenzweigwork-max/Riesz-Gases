import HRS.MS.SA16Y5Vw1

/-!
# S.A.16 (SA16Y5) Vw2: the weak (integrated) equation of the mild solution for a composite kernel `C s^{-γ}` (V7')

`sa16y5g_volt_weak`: `u τ = f0 τ + ∫_0^τ Q s (τ-s) (u (τ-s)) ds` on `[0,T]`, `‖Q s r‖ ≤ C s^{-γ}`, `Q` jointly strongly continuous, and
the weak heat identities `ℓ (Q s r x) = ℓY r x + ∫_0^s ℓΔ (Q σ r x) dσ` (`HE`), `ℓ (f0 τ) = ℓ0 + ∫_0^τ ℓΔ (f0 σ) dσ` (`HE0`) give
`ℓ (u τ) = ℓ0 + ∫_0^τ (ℓΔ (u r) + ℓY r (u r)) dr`.  (Copy of `sa16r_volt_weak`, `SA16RVol7`, with a general kernel and exponent.)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16R

section Weak2
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] {γ : ℝ}

theorem sa16y5g_volt_weak {T C : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hT : 0 < T) (hC : 0 ≤ C)
    (Q : ℝ → ℝ → X →L[ℝ] X)
    (hQb : ∀ r ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioc (0 : ℝ) T, ‖Q s r‖ ≤ C * s ^ (-γ))
    (hQc : ∀ x : X, ContinuousOn (fun q : ℝ × ℝ => Q q.2 q.1 x)
      {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) T ∧ 0 < q.2 ∧ q.2 ≤ T})
    {f0 u : ℝ → X} (hf0 : ContinuousOn f0 (Icc 0 T)) (hu : ContinuousOn u (Icc 0 T))
    (hsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = f0 τ + voltOp (fun τ s => Q s (τ - s)) u τ)
    (ℓ ℓΔ : X →L[ℝ] ℝ) (ℓY : ℝ → X →L[ℝ] ℝ) (ℓ0 : ℝ) {BY : ℝ}
    (hYb : ∀ r ∈ Icc (0 : ℝ) T, ‖ℓY r‖ ≤ BY)
    (hYc : ∀ x : X, ContinuousOn (fun r => ℓY r x) (Icc 0 T))
    (HE : ∀ (x : X), ∀ r ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioc (0 : ℝ) T,
      ℓ (Q s r x) = ℓY r x + ∫ σ in (0 : ℝ)..s, ℓΔ (Q σ r x))
    (HE0 : ∀ τ ∈ Icc (0 : ℝ) T, ℓ (f0 τ) = ℓ0 + ∫ σ in (0 : ℝ)..τ, ℓΔ (f0 σ)) :
    ∀ τ ∈ Icc (0 : ℝ) T, ℓ (u τ) = ℓ0 + ∫ r in (0 : ℝ)..τ, (ℓΔ (u r) + ℓY r (u r)) := by
  intro τ hτ
  set P : ℝ → ℝ → X →L[ℝ] X := fun τ s => Q s (τ - s) with hPdef
  have hKer : VoltKerG γ T C P := by
    refine ⟨hγ0, hγ1, fun τ' s hs hsτ hτ' => ?_, fun x => ?_⟩
    · exact hQb (τ' - s) ⟨by linarith, by linarith⟩ s ⟨hs, hsτ.trans hτ'⟩
    · have hmap : ContinuousOn (fun q : ℝ × ℝ => (q.1 - q.2, q.2))
          {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T} :=
        ((continuous_fst.sub continuous_snd).prodMk continuous_snd).continuousOn
      exact (hQc x).comp hmap (fun q hq => ⟨⟨by linarith [hq.2.1], by linarith [hq.1, hq.2.2]⟩, hq.1,
        hq.2.1.trans hq.2.2⟩)
  set w : ℝ → X := fun ρ => voltOp P u ρ with hwdef
  have hwc : ContinuousOn w (Icc 0 T) := sa16y5g_volt_contOn hKer hT hu
  have hwint : ∀ ρ, w ρ = ∫ s in (0 : ℝ)..ρ, Q s (ρ - s) (u (ρ - s)) := fun ρ => rfl
  have hint : ∀ ρ ∈ Icc (0 : ℝ) T, IntegrableOn (fun s => Q s (ρ - s) (u (ρ - s))) (Ioc 0 ρ) := fun ρ hρ =>
    hKer.integrable_integrand hT hu hρ.1 hρ.2
  set H : ℝ → ℝ → ℝ := fun r σ => ℓΔ (Q σ r (u r)) with hHdef
  have hQuc : ContinuousOn (fun q : ℝ × ℝ => Q q.2 q.1 (u q.1))
      {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) T ∧ 0 < q.2 ∧ q.2 ≤ T} := by
    intro q0 hq0
    obtain ⟨h1, h2, h3⟩ := hq0
    refine sa16r_clm_apply_strong (F := fun q : ℝ × ℝ => Q q.2 q.1)
      (B := C * (q0.2 / 2) ^ (-γ)) (fun v => hQc v q0 ⟨h1, h2, h3⟩) ?_ ?_
    · have hs : ∀ᶠ q in 𝓝[{q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) T ∧ 0 < q.2 ∧ q.2 ≤ T}] q0, q0.2 / 2 < q.2 :=
        nhdsWithin_le_nhds ((continuous_snd.continuousAt).eventually (lt_mem_nhds (by linarith)))
      filter_upwards [hs, self_mem_nhdsWithin] with q hq1 hq2
      refine (hQb q.1 hq2.1 q.2 ⟨hq2.2.1, hq2.2.2⟩).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by linarith) hq1.le (by linarith)) hC
    · exact ContinuousWithinAt.comp (g := u) (f := fun q : ℝ × ℝ => q.1) (t := Icc 0 T)
        (hu q0.1 h1) continuous_fst.continuousWithinAt (fun q hq => hq.1)
  have hHc : ContinuousOn (fun q : ℝ × ℝ => H q.1 q.2)
      {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) T ∧ 0 < q.2 ∧ q.2 ≤ T} :=
    ℓΔ.continuous.comp_continuousOn hQuc
  obtain ⟨Mg, hMg0, hMg⟩ := sa16r_bdd hu
  have hHb : ∀ r ∈ Icc (0 : ℝ) T, ∀ σ ∈ Ioc (0 : ℝ) T, |H r σ| ≤ (‖ℓΔ‖ * C * Mg) * σ ^ (-γ) := by
    intro r hr σ hσ
    have h1 := hQb r hr σ hσ
    have h2 := hMg r hr
    rw [← Real.norm_eq_abs]
    calc ‖ℓΔ (Q σ r (u r))‖ ≤ ‖ℓΔ‖ * ‖Q σ r (u r)‖ := ℓΔ.le_opNorm _
      _ ≤ ‖ℓΔ‖ * (‖Q σ r‖ * ‖u r‖) := by gcongr; exact (Q σ r).le_opNorm _
      _ ≤ ‖ℓΔ‖ * ((C * σ ^ (-γ)) * Mg) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _)
            (mul_nonneg hC (Real.rpow_nonneg hσ.1.le _))) (norm_nonneg _)
      _ = (‖ℓΔ‖ * C * Mg) * σ ^ (-γ) := by ring
  have hτ0 : 0 ≤ τ := hτ.1
  have hτT : τ ≤ T := hτ.2
  have hIcc : ∀ ρ ∈ Icc (0 : ℝ) τ, ρ ∈ Icc (0 : ℝ) T := fun ρ hρ => ⟨hρ.1, hρ.2.trans hτT⟩
  -- continuity of `r ↦ ℓY r (u r)`
  have hg : ContinuousOn (fun r => ℓY r (u r)) (Icc 0 T) := by
    intro r hr
    exact sa16r_clm_apply_strong (F := ℓY) (B := BY) (fun v => hYc v r hr)
      (eventually_nhdsWithin_of_forall (fun r' hr' => hYb r' hr')) (hu r hr)
  -- (E2)
  have hE2 : ℓ (w τ) = ∫ s in Ioc 0 τ, (ℓY (τ - s) (u (τ - s)) + ∫ σ in Ioc 0 s, H (τ - s) σ) := by
    rw [hwint, ← ℓ.intervalIntegral_comp_comm
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hτ0).2 (hint τ hτ)),
      intervalIntegral.integral_of_le hτ0]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    beta_reduce
    rw [HE (u (τ - s)) (τ - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩ s ⟨hs.1, hs.2.trans hτT⟩,
      intervalIntegral.integral_of_le hs.1.le]
  have hfull : IntegrableOn (fun s => ℓ (Q s (τ - s) (u (τ - s)))) (Ioc 0 τ) := ℓ.integrable_comp (hint τ hτ)
  have hgsub : ContinuousOn (fun s : ℝ => ℓY (τ - s) (u (τ - s))) (Icc 0 τ) :=
    hg.comp (continuous_const.sub continuous_id).continuousOn
      (fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  have hYint : IntegrableOn (fun s => ℓY (τ - s) (u (τ - s))) (Ioc 0 τ) :=
    (hgsub.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hAeq : ∀ s ∈ Ioc (0 : ℝ) τ, ℓ (Q s (τ - s) (u (τ - s))) - ℓY (τ - s) (u (τ - s)) =
      ∫ σ in Ioc 0 s, H (τ - s) σ := by
    intro s hs
    rw [HE (u (τ - s)) (τ - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩ s ⟨hs.1, hs.2.trans hτT⟩,
      intervalIntegral.integral_of_le hs.1.le]
    ring
  have hAint : IntegrableOn (fun s => ∫ σ in Ioc 0 s, H (τ - s) σ) (Ioc 0 τ) :=
    (hfull.sub hYint).congr_fun hAeq measurableSet_Ioc
  have hF1 : IntegrableOn (fun q : ℝ × ℝ => H (τ - q.1) q.2) {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ τ} :=
    sa16y5g_tri_int hγ1 hτT hHc hHb (φ := fun q : ℝ × ℝ => τ - q.1) (continuous_const.sub continuous_fst)
      (fun q hq => ⟨by linarith [hq.2.2], by linarith [hq.1, hq.2.1]⟩)
  have hswap1 := sa16r_tri_swap (F := fun s σ => H (τ - s) σ) (a := τ) hF1
  have hF2 : IntegrableOn (fun q : ℝ × ℝ => H (q.1 - q.2) q.2) {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ τ} :=
    sa16y5g_tri_int hγ1 hτT hHc hHb (φ := fun q : ℝ × ℝ => q.1 - q.2) (continuous_fst.sub continuous_snd)
      (fun q hq => ⟨by linarith [hq.2.1], by linarith [hq.1, hq.2.2]⟩)
  have hswap2 := sa16r_tri_swap (F := fun ρ σ => H (ρ - σ) σ) (a := τ) hF2
  have hE6 : ∀ ρ ∈ Icc (0 : ℝ) T, ℓΔ (w ρ) = ∫ σ in Ioc 0 ρ, H (ρ - σ) σ := by
    intro ρ hρ
    rw [hwint, ← ℓΔ.intervalIntegral_comp_comm
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hρ.1).2 (hint ρ hρ)),
      intervalIntegral.integral_of_le hρ.1]
  have hE7 : ∀ σ ∈ Ioc (0 : ℝ) τ, ∫ s in Ioc σ τ, H (τ - s) σ = ∫ ρ in Ioc σ τ, H (ρ - σ) σ := by
    intro σ hσ
    rw [← intervalIntegral.integral_of_le hσ.2, ← intervalIntegral.integral_of_le hσ.2]
    have := intervalIntegral.integral_comp_sub_left (a := σ) (b := τ) (fun ρ => H (ρ - σ) σ) (τ + σ)
    have e1 : τ + σ - τ = σ := by ring
    have e2 : τ + σ - σ = τ := by ring
    rw [e1, e2] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun s _ => ?_
    beta_reduce
    congr 1; ring
  have hAB : (∫ s in Ioc 0 τ, ∫ σ in Ioc 0 s, H (τ - s) σ) = ∫ ρ in Ioc 0 τ, ℓΔ (w ρ) := by
    rw [hswap1, setIntegral_congr_fun measurableSet_Ioc (fun ρ hρ => hE6 ρ (hIcc ρ ⟨hρ.1.le, hρ.2⟩)), hswap2]
    exact setIntegral_congr_fun measurableSet_Ioc hE7
  have hY4 : ∫ s in Ioc 0 τ, ℓY (τ - s) (u (τ - s)) = ∫ r in (0 : ℝ)..τ, ℓY r (u r) := by
    rw [← intervalIntegral.integral_of_le hτ0]
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := τ) (fun r => ℓY r (u r)) τ
    simpa using this
  have hΔw : IntervalIntegrable (fun ρ => ℓΔ (w ρ)) volume 0 τ :=
    ((ℓΔ.continuous.comp_continuousOn hwc).mono (Icc_subset_Icc_right hτT)).intervalIntegrable_of_Icc hτ0
  have hΔf : IntervalIntegrable (fun ρ => ℓΔ (f0 ρ)) volume 0 τ :=
    ((ℓΔ.continuous.comp_continuousOn hf0).mono (Icc_subset_Icc_right hτT)).intervalIntegrable_of_Icc hτ0
  have hKg : IntervalIntegrable (fun r => ℓY r (u r)) volume 0 τ :=
    (hg.mono (Icc_subset_Icc_right hτT)).intervalIntegrable_of_Icc hτ0
  have hLHS : ℓ (u τ) = ℓ0 + (∫ σ in (0 : ℝ)..τ, ℓΔ (f0 σ)) + (∫ r in (0 : ℝ)..τ, ℓY r (u r)) +
      ∫ ρ in (0 : ℝ)..τ, ℓΔ (w ρ) := by
    have h1 : ℓ (u τ) = ℓ (f0 τ) + ℓ (w τ) := by rw [hsol τ hτ, map_add]
    rw [h1, HE0 τ hτ, hE2, integral_add hYint hAint, hY4, hAB, ← intervalIntegral.integral_of_le hτ0]
    ring
  have hRHS : ∫ r in (0 : ℝ)..τ, (ℓΔ (u r) + ℓY r (u r)) =
      (∫ σ in (0 : ℝ)..τ, ℓΔ (f0 σ)) + (∫ ρ in (0 : ℝ)..τ, ℓΔ (w ρ)) + ∫ r in (0 : ℝ)..τ, ℓY r (u r) := by
    have h1 : ∀ r ∈ Set.uIcc (0 : ℝ) τ, ℓΔ (u r) + ℓY r (u r) = (ℓΔ (f0 r) + ℓΔ (w r)) + ℓY r (u r) := by
      intro r hr
      rw [Set.uIcc_of_le hτ0] at hr
      have hu' : ℓΔ (u r) = ℓΔ (f0 r) + ℓΔ (w r) := by
        rw [hsol r (hIcc r hr), map_add]
      rw [hu']
    rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_add (hΔf.add hΔw) hKg,
      intervalIntegral.integral_add hΔf hΔw]
  rw [hLHS, hRHS]
  ring

end Weak2

end HRS.Whole.AppendixA.Phase2SA16R
