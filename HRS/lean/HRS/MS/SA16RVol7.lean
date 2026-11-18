import HRS.MS.SA16RVol6

/-!
# S.A.16 (SA16R) Vol7: the weak (integrated) equation of the Duhamel solution

`sa16r_volt_weak`: if `u τ = f0 τ + ∫_0^τ Γ s (K (τ-s) (u (τ-s))) ds` on `[0,T]` and the functionals satisfy the weak
heat identities `ℓ (Γ s y) = ℓY y + ∫_0^s ℓΔ (Γ σ y) dσ` (`HE`) and `ℓ (f0 τ) = ℓ0 + ∫_0^τ ℓΔ (f0 σ) dσ` (`HE0`), then
`ℓ (u τ) = ℓ0 + ∫_0^τ (ℓΔ (u r) + ℓY (K r (u r))) dr`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16R

section Weak
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

theorem sa16r_volt_weak {T C B : ℝ} {Γ : ℝ → Y →L[ℝ] X} {K : ℝ → X →L[ℝ] Y}
    (h : GainData T C B Γ K) (hC : 0 ≤ C) (hB : 0 ≤ B) (hT : 0 < T)
    {f0 : ℝ → X} (hf0 : ContinuousOn f0 (Icc 0 T)) {u : ℝ → X} (hu : ContinuousOn u (Icc 0 T))
    (hsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = f0 τ + voltOp (gainKer Γ K) u τ)
    (ℓ ℓΔ : X →L[ℝ] ℝ) (ℓY : Y →L[ℝ] ℝ) (ℓ0 : ℝ)
    (HE : ∀ (y : Y), ∀ s ∈ Ioc (0 : ℝ) T, ℓ (Γ s y) = ℓY y + ∫ σ in (0 : ℝ)..s, ℓΔ (Γ σ y))
    (HE0 : ∀ τ ∈ Icc (0 : ℝ) T, ℓ (f0 τ) = ℓ0 + ∫ σ in (0 : ℝ)..τ, ℓΔ (f0 σ)) :
    ∀ τ ∈ Icc (0 : ℝ) T, ℓ (u τ) = ℓ0 + ∫ r in (0 : ℝ)..τ, (ℓΔ (u r) + ℓY (K r (u r))) := by
  intro τ hτ
  have hKer : VoltKer T (C * B) (gainKer Γ K) := h.voltKer hC hB
  set g : ℝ → Y := fun r => K r (u r) with hgdef
  have hg : ContinuousOn g (Icc 0 T) := by
    intro r hr
    refine sa16r_clm_apply_strong (F := K) (y := u) (B := B) (fun v => h.Kcont v r hr) ?_ (hu r hr)
    exact eventually_nhdsWithin_of_forall (fun r' hr' => h.Kbound r' hr')
  set w : ℝ → X := fun ρ => voltOp (gainKer Γ K) u ρ with hwdef
  have hwc : ContinuousOn w (Icc 0 T) := sa16r_volt_contOn hKer hT hu
  have hwint : ∀ ρ, w ρ = ∫ s in (0 : ℝ)..ρ, Γ s (g (ρ - s)) := fun ρ => rfl
  have hint : ∀ ρ ∈ Icc (0 : ℝ) T, IntegrableOn (fun s => Γ s (g (ρ - s))) (Ioc 0 ρ) := fun ρ hρ =>
    hKer.integrable_integrand hT hu hρ.1 hρ.2
  set H : ℝ → ℝ → ℝ := fun r σ => ℓΔ (Γ σ (g r)) with hHdef
  have hHc : ContinuousOn (fun q : ℝ × ℝ => H q.1 q.2)
      {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) T ∧ 0 < q.2 ∧ q.2 ≤ T} :=
    ℓΔ.continuous.comp_continuousOn (sa16r_Gamma_cont h hC hg)
  obtain ⟨Mg, hMg0, hMg⟩ := sa16r_bdd hg
  have hHb : ∀ r ∈ Icc (0 : ℝ) T, ∀ σ ∈ Ioc (0 : ℝ) T,
      |H r σ| ≤ (‖ℓΔ‖ * C * Mg) * σ ^ (-(1 / 2 : ℝ)) := by
    intro r hr σ hσ
    have h1 := h.Γbound σ hσ.1 hσ.2
    have h2 := hMg r hr
    rw [← Real.norm_eq_abs]
    calc ‖ℓΔ (Γ σ (g r))‖ ≤ ‖ℓΔ‖ * ‖Γ σ (g r)‖ := ℓΔ.le_opNorm _
      _ ≤ ‖ℓΔ‖ * (‖Γ σ‖ * ‖g r‖) := by gcongr; exact (Γ σ).le_opNorm _
      _ ≤ ‖ℓΔ‖ * ((C * σ ^ (-(1 / 2 : ℝ))) * Mg) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _)
            (mul_nonneg hC (Real.rpow_nonneg hσ.1.le _))) (norm_nonneg _)
      _ = (‖ℓΔ‖ * C * Mg) * σ ^ (-(1 / 2 : ℝ)) := by ring
  -- the case τ = 0 is trivial; assume the general structure
  have hτ0 : 0 ≤ τ := hτ.1
  have hτT : τ ≤ T := hτ.2
  have hIcc : ∀ ρ ∈ Icc (0 : ℝ) τ, ρ ∈ Icc (0 : ℝ) T := fun ρ hρ => ⟨hρ.1, hρ.2.trans hτT⟩
  -- (E2) the Duhamel integral under ℓ
  have hE2 : ℓ (w τ) = ∫ s in Ioc 0 τ, (ℓY (g (τ - s)) + ∫ σ in Ioc 0 s, H (τ - s) σ) := by
    rw [hwint, ← ℓ.intervalIntegral_comp_comm
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hτ0).2 (hint τ hτ)),
      intervalIntegral.integral_of_le hτ0]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    beta_reduce
    rw [HE (g (τ - s)) s ⟨hs.1, hs.2.trans hτT⟩, intervalIntegral.integral_of_le hs.1.le]
  -- integrability facts
  have hfull : IntegrableOn (fun s => ℓ (Γ s (g (τ - s)))) (Ioc 0 τ) := ℓ.integrable_comp (hint τ hτ)
  have hgsub : ContinuousOn (fun s : ℝ => g (τ - s)) (Icc 0 τ) :=
    hg.comp (continuous_const.sub continuous_id).continuousOn
      (fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  have hYint : IntegrableOn (fun s => ℓY (g (τ - s))) (Ioc 0 τ) :=
    ((ℓY.continuous.comp_continuousOn hgsub).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hAeq : ∀ s ∈ Ioc (0 : ℝ) τ, ℓ (Γ s (g (τ - s))) - ℓY (g (τ - s)) = ∫ σ in Ioc 0 s, H (τ - s) σ := by
    intro s hs
    rw [HE (g (τ - s)) s ⟨hs.1, hs.2.trans hτT⟩, intervalIntegral.integral_of_le hs.1.le]
    ring
  have hAint : IntegrableOn (fun s => ∫ σ in Ioc 0 s, H (τ - s) σ) (Ioc 0 τ) :=
    (hfull.sub hYint).congr_fun hAeq measurableSet_Ioc
  -- Fubini, first triangle
  have hF1 : IntegrableOn (fun q : ℝ × ℝ => H (τ - q.1) q.2) {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ τ} :=
    sa16r_tri_int hτT hHc hHb (φ := fun q : ℝ × ℝ => τ - q.1) (continuous_const.sub continuous_fst)
      (fun q hq => ⟨by linarith [hq.2.2], by linarith [hq.1, hq.2.1]⟩)
  have hswap1 := sa16r_tri_swap (F := fun s σ => H (τ - s) σ) (a := τ) hF1
  -- Fubini, second triangle
  have hF2 : IntegrableOn (fun q : ℝ × ℝ => H (q.1 - q.2) q.2) {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ τ} :=
    sa16r_tri_int hτT hHc hHb (φ := fun q : ℝ × ℝ => q.1 - q.2) (continuous_fst.sub continuous_snd)
      (fun q hq => ⟨by linarith [hq.2.1], by linarith [hq.1, hq.2.2]⟩)
  have hswap2 := sa16r_tri_swap (F := fun ρ σ => H (ρ - σ) σ) (a := τ) hF2
  -- ℓΔ (w ρ)
  have hE6 : ∀ ρ ∈ Icc (0 : ℝ) T, ℓΔ (w ρ) = ∫ σ in Ioc 0 ρ, H (ρ - σ) σ := by
    intro ρ hρ
    rw [hwint, ← ℓΔ.intervalIntegral_comp_comm
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hρ.1).2 (hint ρ hρ)),
      intervalIntegral.integral_of_le hρ.1]
  -- the two inner integrals agree
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
  -- assemble
  have hY4 : ∫ s in Ioc 0 τ, ℓY (g (τ - s)) = ∫ r in (0 : ℝ)..τ, ℓY (g r) := by
    rw [← intervalIntegral.integral_of_le hτ0]
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := τ) (fun r => ℓY (g r)) τ
    simpa using this
  have hΔw : IntervalIntegrable (fun ρ => ℓΔ (w ρ)) volume 0 τ :=
    ((ℓΔ.continuous.comp_continuousOn hwc).mono (Icc_subset_Icc_right hτT)).intervalIntegrable_of_Icc hτ0
  have hΔf : IntervalIntegrable (fun ρ => ℓΔ (f0 ρ)) volume 0 τ :=
    ((ℓΔ.continuous.comp_continuousOn hf0).mono (Icc_subset_Icc_right hτT)).intervalIntegrable_of_Icc hτ0
  have hKg : IntervalIntegrable (fun r => ℓY (g r)) volume 0 τ :=
    ((ℓY.continuous.comp_continuousOn hg).mono (Icc_subset_Icc_right hτT)).intervalIntegrable_of_Icc hτ0
  have hLHS : ℓ (u τ) = ℓ0 + (∫ σ in (0 : ℝ)..τ, ℓΔ (f0 σ)) + (∫ r in (0 : ℝ)..τ, ℓY (g r)) +
      ∫ ρ in (0 : ℝ)..τ, ℓΔ (w ρ) := by
    have h1 : ℓ (u τ) = ℓ (f0 τ) + ℓ (w τ) := by rw [hsol τ hτ, map_add]
    rw [h1, HE0 τ hτ, hE2, integral_add hYint hAint, hY4, hAB, ← intervalIntegral.integral_of_le hτ0]
    ring
  have hRHS : ∫ r in (0 : ℝ)..τ, (ℓΔ (u r) + ℓY (K r (u r))) =
      (∫ σ in (0 : ℝ)..τ, ℓΔ (f0 σ)) + (∫ ρ in (0 : ℝ)..τ, ℓΔ (w ρ)) + ∫ r in (0 : ℝ)..τ, ℓY (g r) := by
    have h1 : ∀ r ∈ Set.uIcc (0 : ℝ) τ, ℓΔ (u r) + ℓY (K r (u r)) = (ℓΔ (f0 r) + ℓΔ (w r)) + ℓY (g r) := by
      intro r hr
      rw [Set.uIcc_of_le hτ0] at hr
      have hu' : ℓΔ (u r) = ℓΔ (f0 r) + ℓΔ (w r) := by
        rw [hsol r (hIcc r hr), map_add]
      rw [hu']
    rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_add (hΔf.add hΔw) hKg,
      intervalIntegral.integral_add hΔf hΔw]
  rw [hLHS, hRHS]
  ring

end Weak

end HRS.Whole.AppendixA.Phase2SA16R
