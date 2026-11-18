import HRS.Sections.QuenchAux15

/-!
# Packet QUENCH (Q27), part 16: `E sup_{t ≤ T} |G_t|² ≤ 16 σ² T` (Doob)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

section Doob

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {lam v vY : ℝ} {Y : Ω → ℝ} {G : ℝ → Ω → ℝ}

/-- Doob's `L²` inequality for a Brownian motion, up to a modification with everywhere continuous paths. -/
theorem doob_bm {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {T : ℝ} (hT : 0 ≤ T) :
    ∃ B' : ℝ → Ω → ℝ, (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → B' t ω = B t.toNNReal ω) ∧
      ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖B' t ω‖ₑ) ^ 2 ∂P ≤ 4 * ENNReal.ofReal T := by
  let W : ℝ≥0 → Ω → Unit → ℝ := fun t ω _ => B t ω
  have hW : ∀ k : Unit, IsBrownianReal (fun t ω => W t ω k) P := fun _ => hB
  have hind : iIndepFun (fun (k : Unit) ω => fun t : ℝ≥0 => W t ω k) P := iIndepFun.of_subsingleton
  have hX₀ : Measurable (fun _ : Ω => ()) := measurable_const
  have hX₀W : IndepFun (fun _ : Ω => ()) (fun ω => fun t : ℝ≥0 => W t ω) P := indepFun_const_left _ _
  obtain ⟨W', hW'm, hae, hBF⟩ := exists_isBrownianFiltration P W hW hind (fun _ : Ω => ()) hX₀ hX₀W
  refine ⟨fun t ω => ofNNRealTime W' t ω (), ?_, ?_⟩
  · filter_upwards [hae] with ω h t ht
    simp only [ofNNRealTime_apply]
    have := congrFun (h t.toNNReal) ()
    simpa [W] using this
  · have hmart := hBF.martingale ()
    have hcont : ∀ ω, Continuous fun t : ℝ => ofNNRealTime W' t ω () := fun ω =>
      (continuous_apply ()).comp (continuous_ofNNRealTime W' ω (hBF.cont ω))
    have hL2 : ∀ t, MemLp (fun ω => ofNNRealTime W' t ω ()) 2 P := fun t =>
      hBF.memLp_two_coord_real t ()
    have h1 := SimpleIntegrand.doob_L2_continuous hmart hcont hL2 T
    refine h1.trans ?_
    gcongr
    -- `∫⁻ ‖I T‖ₑ² = T`
    have hB' := (hBF.isBrownianReal ()).toIsPreBrownianReal.hasLaw_eval T.toNNReal
    have hint : Integrable (fun ω => (ofNNRealTime W' T ω ()) ^ 2) P := by
      have : Integrable (fun ω => ofNNRealTime W' T ω () * ofNNRealTime W' T ω ()) P :=
        (hL2 T).integrable_mul (hL2 T)
      simpa [sq] using this
    have hsq : ∫ ω, (ofNNRealTime W' T ω ()) ^ 2 ∂P = T := by
      have e : (fun ω => (ofNNRealTime W' T ω ()) ^ 2) = fun ω => (fun x : ℝ => x ^ 2) (W' T.toNNReal ω ()) := by
        funext ω; simp
      rw [e, ← integral_map hB'.aemeasurable (f := fun x : ℝ => x ^ 2) (by fun_prop), hB'.map_eq,
        integral_sq_gaussianReal_zero]
      simp [Real.coe_toNNReal _ hT]
    have hl : ∫⁻ ω, ‖ofNNRealTime W' T ω ()‖ₑ ^ 2 ∂P = ENNReal.ofReal T := by
      have e : ∀ ω, ‖ofNNRealTime W' T ω ()‖ₑ ^ 2 = ENNReal.ofReal ((ofNNRealTime W' T ω ()) ^ 2) := by
        intro ω
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      simp_rw [e]
      rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => sq_nonneg _), hsq]
    rw [hl]

theorem sup_G_lintegral (hN : OUNoise lam v vY P Y G) (hv : 0 < v) (hlam : 0 < lam) {σ : ℝ}
    (hσ : σ ^ 2 = 2 * lam * v) (hσ0 : 0 < σ) {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖G t ω‖ₑ) ^ 2 ∂P ≤ ENNReal.ofReal (16 * σ ^ 2 * T) := by
  obtain ⟨B', hB'ae, hB'int⟩ := doob_bm (bm_isBrownian hN hv hlam hσ) hT
  have hpath : ∀ᵐ ω ∂P, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖G t ω‖ₑ) ≤
      ENNReal.ofReal (2 * σ) * (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖B' t ω‖ₑ) := by
    filter_upwards [hB'ae, hN.cont] with ω hBω hc
    set S := ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖B' t ω‖ₑ with hS
    by_cases hSt : S = ⊤
    · rw [hSt, ENNReal.mul_top (by simpa using (by positivity : (0 : ℝ) < 2 * σ))]
      exact le_top
    · set M := S.toReal with hM
      have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
      have hBM : ∀ s ∈ Set.Icc (0 : ℝ) T, |B' s ω| ≤ M := by
        intro s hs
        have : ‖B' s ω‖ₑ ≤ S := le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => ‖B' t ω‖ₑ) s hs
        have h2 := (ENNReal.toReal_le_toReal (by simp) hSt).2 this
        simpa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] using h2
      set g : ℝ → ℝ := fun u => G (max u 0) ω with hg
      have key : ∀ s ∈ Set.Icc (0 : ℝ) T, |g s + lam * ∫ u in (0 : ℝ)..s, g u| ≤ σ * M := by
        intro s hs
        have hs0 : 0 ≤ s := hs.1
        have e1 : g s + lam * ∫ u in (0 : ℝ)..s, g u = σ * B' s ω := by
          have := hBω s hs0
          simp only [bmProc, Real.coe_toNNReal s hs0] at this
          rw [this]
          have hint : ∫ u in (0 : ℝ)..s, g u = ∫ u in Set.Icc (0 : ℝ) s, G u ω := by
            rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs0]
            refine intervalIntegral.integral_congr fun u hu => ?_
            rw [Set.uIcc_of_le hs0] at hu
            simp [hg, max_eq_left hu.1]
          have hgs : g s = G s ω := by simp [hg, max_eq_left hs0]
          rw [hint, hgs]
          field_simp
        rw [e1, abs_mul, abs_of_pos hσ0]
        exact mul_le_mul_of_nonneg_left (hBM s hs) hσ0.le
      have hbd := ode_bound hc hlam hσ0.le hM0 key
      refine iSup₂_le fun t ht => ?_
      have h1 := hbd t ht
      have e2 : g t = G t ω := by simp [hg, max_eq_left ht.1]
      rw [e2] at h1
      rw [Real.enorm_eq_ofReal_abs]
      calc ENNReal.ofReal |G t ω| ≤ ENNReal.ofReal (2 * σ * M) := ENNReal.ofReal_le_ofReal h1
        _ = ENNReal.ofReal (2 * σ) * S := by
          rw [ENNReal.ofReal_mul (by positivity), hM, ENNReal.ofReal_toReal hSt]
  calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖G t ω‖ₑ) ^ 2 ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (2 * σ) * (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖B' t ω‖ₑ)) ^ 2 ∂P :=
        lintegral_mono_ae (hpath.mono fun ω h => by gcongr)
    _ = ENNReal.ofReal (2 * σ) ^ 2 * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖B' t ω‖ₑ) ^ 2 ∂P := by
        simp_rw [mul_pow]
        rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
    _ ≤ ENNReal.ofReal (2 * σ) ^ 2 * (4 * ENNReal.ofReal T) := by gcongr
    _ = ENNReal.ofReal (16 * σ ^ 2 * T) := by
        rw [← ENNReal.ofReal_pow (by positivity), show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end Doob

end Qch

end HRS
