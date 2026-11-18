import HRS.Main.ThermLin2Fu7

/-!
# THERMLIN2 Fu8: `tl2fu_main`, the almost-sure Fubini identity for an abstract test family `ψ_r`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c HRS.Uniform.Q45 Classical

variable {d : ℕ} {m T' K : ℝ} {Vev Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
  {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
  {G : ℝ → Ω → NegSobolev d m} {Cd : ℝ → NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ}
  {Zs Zw : ℝ → Ω → NegSobolev d m} {t : ℝ} {φ : Torus d → ℝ} {ψ : ℝ → Torus d → ℝ} {B : ℝ}

/-- The variance computation: a.s. `⟨Zs^t - Zw^t, φ⟩ = ∫_0^t ⟨Zw^r, ψ_r⟩ dr`, given the weak Dyson identity
(`Tl2FuTest.hweak`). -/
theorem tl2fu_main (D : Tl2FuSetup m T' K Vev Wev P ℱ G Cd Zs Zw) (ht : t ∈ Set.Icc (0 : ℝ) T')
    (E : Tl2FuTest Vev Wev t φ ψ B) :
    ∀ᵐ ω ∂P, NegSobolev.eval (Zs t ω) φ - NegSobolev.eval (Zw t ω) φ =
      ∫ r in (0 : ℝ)..t, NegSobolev.eval (Zw r ω) (ψ r) := by
  obtain ⟨hTC, hτ, hCm⟩ := D.cov_facts
  obtain ⟨Zw', hZw'm, hZw'eq⟩ := tl2fu_modif Zw D.hZwm D.hT0.le D.hZwc
  set Fp : ℝ → Ω → ℝ := fun r ω => inner ℝ (Zw' r ω) (lpFun m (ψ r)) with hFp
  have hFpm : Measurable fun q : ℝ × Ω => Fp q.1 q.2 := hZw'm.inner (E.hψmeas.comp measurable_fst)
  have hrT : ∀ r ∈ Set.Icc (0 : ℝ) t, r ∈ Set.Icc (0 : ℝ) T' := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hFpF : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ᵐ ω ∂P, Fp r ω = NegSobolev.eval (Zw r ω) (ψ r) := by
    intro r hr
    filter_upwards [hZw'eq] with ω hω
    simp only [hFp]
    rw [hω r (hrT r hr), eval_lpFun _ (E.hψm r hr)]
  have hFL : ∀ r ∈ Set.Icc (0 : ℝ) t, MemLp (Fp r) 2 P := fun r hr =>
    (tl2fu_memLp_w D (hrT r hr) (E.hψm r hr)).ae_eq
      (Filter.EventuallyEq.symm (hFpF r hr) : (fun ω => NegSobolev.eval (Zw r ω) (ψ r)) =ᵐ[P] Fp r)
  set X : Ω → ℝ := fun ω => NegSobolev.eval (Zs t ω) φ - NegSobolev.eval (Zw t ω) φ with hXdef
  have hX : MemLp X 2 P := (tl2fu_memLp_s D ht E.hφ).sub (tl2fu_memLp_w D ht E.hφ)
  have hXm : Measurable X :=
    ((continuous_eval_const E.hφ).measurable.comp (D.hZsm t)).sub
      ((continuous_eval_const E.hφ).measurable.comp (D.hZwm t))
  -- data for E1/E2
  have hsubT : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T' := Set.Icc_subset_Icc_right ht.2
  have hc : IntegrableOn (fun σ => traceNormForm (Cd σ)) (Set.Icc 0 t) := hτ.mono_set hsubT
  have hc0 : ∀ σ ∈ Set.Icc (0 : ℝ) t, 0 ≤ traceNormForm (Cd σ) := fun σ _ => traceNormForm_nonneg _
  have hCb : ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ u v : NegSobolev d m,
      |Cd σ u v| ≤ traceNormForm (Cd σ) * (‖u‖ * ‖v‖) :=
    fun σ hσ u v => abs_apply_le_tn (hTC σ (hsubT hσ)) u v
  have hsymm : ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ u v : NegSobolev d m, Cd σ u v = Cd σ v u :=
    fun σ hσ u v => (hTC σ (hsubT hσ)).symm u v
  have hAm := tl2fu_A_meas D ht φ
  have hWm : Measurable fun p : ℝ × ℝ => tl2fuW Wev t ψ (p.1, p.2) := tl2fu_W_meas D ht E
  have haB : ∀ σ ∈ Set.Icc (0 : ℝ) t, ‖tl2fuA Vev Wev t φ σ‖ ≤ 2 * K * ‖gfb4_ell m φ‖ :=
    fun σ hσ => tl2fu_A_bound D ht φ hσ
  have hwB : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ σ ∈ Set.Icc (0 : ℝ) r, ‖tl2fuW Wev t ψ (r, σ)‖ ≤ K * B :=
    fun r hr σ hσ => tl2fu_W_bound D ht E hr hσ
  have hweak : ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ l : NegSobolev d m →L[ℝ] ℝ,
      l (tl2fuA Vev Wev t φ σ) = ∫ r in σ..t, l (tl2fuW Wev t ψ (r, σ)) :=
    fun σ hσ l => tl2fu_weak E hσ l
  have hE1 := tl2fu_E1 (t := t) Cd hCm (fun σ => traceNormForm (Cd σ)) hc hc0 hCb
    (tl2fuA Vev Wev t φ) (fun r σ => tl2fuW Wev t ψ (r, σ)) hAm hWm haB hwB hweak
  have hE2 := fun r (hr : r ∈ Set.Icc (0 : ℝ) t) => tl2fu_E2 (t := t) Cd hCm (fun σ => traceNormForm (Cd σ)) hc
    hc0 hCb hsymm (tl2fuA Vev Wev t φ) (fun r σ => tl2fuW Wev t ψ (r, σ)) hWm hwB hweak hr
  -- the covariances
  have hXF : ∀ r ∈ Set.Icc (0 : ℝ) t, ∫ ω, X ω * Fp r ω ∂P =
      ∫ σ in Set.Icc 0 r, Cd σ (tl2fuA Vev Wev t φ σ) (tl2fuW Wev t ψ (r, σ)) := by
    intro r hr
    rw [← tl2fu_cov_AF D ht E hr]
    refine integral_congr_ae ?_
    filter_upwards [hFpF r hr] with ω hω
    simp only [hXdef, hω]
  have hFF : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ r' ∈ Set.Icc (0 : ℝ) t, ∫ ω, Fp r' ω * Fp r ω ∂P =
      ∫ σ in Set.Icc 0 (min r r'), Cd σ (tl2fuW Wev t ψ (r, σ)) (tl2fuW Wev t ψ (r', σ)) := by
    intro r hr r' hr'
    rw [← tl2fu_cov_FF D ht E hr hr']
    have : ∫ ω, NegSobolev.eval (Zw r ω) (ψ r) * NegSobolev.eval (Zw r' ω) (ψ r') ∂P =
        ∫ ω, NegSobolev.eval (Zw r' ω) (ψ r') * NegSobolev.eval (Zw r ω) (ψ r) ∂P :=
      integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
    rw [this]
    refine integral_congr_ae ?_
    filter_upwards [hFpF r hr, hFpF r' hr'] with ω h1 h2
    rw [h1, h2]
  have hFFd : ∀ r ∈ Set.Icc (0 : ℝ) t, ∫ ω, Fp r ω ^ 2 ∂P ≤
      (∫ σ in Set.Icc 0 T', traceNormForm (Cd σ)) * (K * B) ^ 2 := by
    intro r hr
    refine le_trans (le_of_eq ?_) (tl2fu_FF_bound D ht E hr)
    refine integral_congr_ae ?_
    filter_upwards [hFpF r hr] with ω hω
    rw [sq, hω]
  have hXX : ∫ ω, X ω * X ω ∂P = ∫ σ in Set.Icc 0 t, Cd σ (tl2fuA Vev Wev t φ σ) (tl2fuA Vev Wev t φ σ) :=
    tl2fu_cov_AA D ht E
  have key := tl2fu_orth (t := t) Fp hFpm _ hFL hFFd X hX hXm ?_ ?_
  · filter_upwards [key, hZw'eq] with ω hω hω'
    rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc]
    have : ∫ r in Set.Icc (0 : ℝ) t, Fp r ω = ∫ r in Set.Icc (0 : ℝ) t, NegSobolev.eval (Zw r ω) (ψ r) := by
      refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      simp only [hFp]
      rw [hω' r (hrT r hr), eval_lpFun _ (E.hψm r hr)]
    rw [← this]
    exact hω
  · intro r hr
    rw [hXF r hr, ← hE2 r hr]
    refine setIntegral_congr_fun measurableSet_Icc fun r' hr' => ?_
    exact hFF r hr r' hr'
  · rw [hXX, hE1]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    exact (hXF r hr).symm

end HRS.ThermLin.Plan2
