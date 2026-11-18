import HRS.Sections.ScrnAux25
import HRS.Main.A8PAux23

/-!
# Packet SCRN, part 26: the remainder bound `E‖R‖ ≲ √N o_N ∫ K`

Universe-polymorphic copies of `gfb2_time_integral` (with a time-dependent moment bound) and
`gfb2_progressive_meas`, and the bound of `E‖R‖` from the commutator estimate `A8CommSpec`, the energy bound
`E[F_N(X^t)] ≤ 0` (`scrn_energy_bound`) and the transport bounds `K_a(r)` of the transported tests.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

open HRS.Uniform

variable {d : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

/-- Time integral of a jointly measurable process whose one-time marginals are controlled. -/
theorem scrn_time_integral_w {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (F : ℝ → Ω → ℝ) (hFm : Measurable fun p : ℝ × Ω => F p.1 p.2)
    (hnn : ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) T, 0 ≤ F r ω)
    (hint : ∀ r ∈ Set.Icc (0 : ℝ) T, Integrable (F r) P) (e : ℝ → ℝ)
    (he : IntegrableOn e (Set.Icc (0 : ℝ) T))
    (hE1 : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫ ω, F r ω ∂P ≤ e r) :
    (∀ᵐ ω ∂P, IntegrableOn (fun r => F r ω) (Set.Icc (0 : ℝ) T)) ∧
    ∫⁻ ω, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) T, F r ω) ∂P ≤ ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) T, e r) ∧
    AEMeasurable (fun ω => ∫ r in Set.Icc (0 : ℝ) T, F r ω) P := by
  have hnn_r : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, 0 ≤ F r ω := fun r hr => by
    filter_upwards [hnn] with ω hω using hω r hr
  have hmeasF : ∀ ω, Measurable fun r => F r ω := fun ω => hFm.comp measurable_prodMk_right
  have hjm : Measurable fun q : ℝ × Ω => ENNReal.ofReal (F q.1 q.2) := ENNReal.measurable_ofReal.comp hFm
  -- Tonelli
  have hswap : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (F r ω)) ∂P =
      ∫⁻ r in Set.Icc (0 : ℝ) T, (∫⁻ ω, ENNReal.ofReal (F r ω) ∂P) := by
    rw [lintegral_lintegral_swap]
    exact (hjm.comp measurable_swap).aemeasurable
  have hinner : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ ω, ENNReal.ofReal (F r ω) ∂P ≤ ENNReal.ofReal (e r) := by
    intro r hr
    rw [← ofReal_integral_eq_lintegral_ofReal (hint r hr) (hnn_r r hr)]
    exact ENNReal.ofReal_le_ofReal (hE1 r hr)
  have hbound : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (F r ω)) ∂P ≤ ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) T, e r) := by
    rw [hswap]
    calc ∫⁻ r in Set.Icc (0 : ℝ) T, (∫⁻ ω, ENNReal.ofReal (F r ω) ∂P)
        ≤ ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (e r) := by
          refine setLIntegral_mono' measurableSet_Icc fun r hr => hinner r hr
      _ = ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) T, e r) := by
          refine (ofReal_integral_eq_lintegral_ofReal he ?_).symm
          refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
          have h1 : (0 : ℝ) ≤ ∫ ω, F r ω ∂P :=
            integral_nonneg_of_ae (hnn_r r hr)
          exact h1.trans (hE1 r hr)
  have hle : ∀ᵐ ω ∂P, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) T, F r ω) ≤
      ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (F r ω) := by
    filter_upwards [hnn] with ω hω
    by_cases hi : IntegrableOn (fun r => F r ω) (Set.Icc (0 : ℝ) T)
    · rw [ofReal_integral_eq_lintegral_ofReal hi]
      exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => hω r hr)
    · rw [integral_undef hi]; simp
  have hmeasL : Measurable fun ω => ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (F r ω) :=
    (hjm.comp measurable_swap).lintegral_prod_right'
  have hfin : ∀ᵐ ω ∂P, ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (F r ω) < ⊤ := by
    refine ae_lt_top hmeasL (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound)
  refine ⟨?_, (lintegral_mono_ae hle).trans hbound, ?_⟩
  · filter_upwards [hfin, hnn] with ω hω hω'
    refine ⟨(hmeasF ω).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq ?_) hω
    refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (hω' r hr)]
  · have : StronglyMeasurable (fun q : Ω × ℝ => F q.2 q.1) := (hFm.comp measurable_swap).stronglyMeasurable
    exact (this.integral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T))).measurable.aemeasurable



/-- Joint measurability of a progressive configuration process, after clamping time to `[0,T]`. -/
theorem scrn_progressive_meas {N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ)
    (X : ℝ≥0 → Ω → Config d N) (hprog : IsProgressive ℱ (ofNNRealTime X)) {T : ℝ} (hT : 0 ≤ T) :
    Measurable fun p : ℝ × Ω => X (Real.toNNReal (Q54c.clampT T p.1)) p.2 := by
  have h1 := hprog T
  have hle : (Subtype.instMeasurableSpace (α := ℝ) (p := (· ∈ Set.Iic T))).prod (ℱ T) ≤
      (Subtype.instMeasurableSpace (α := ℝ) (p := (· ∈ Set.Iic T))).prod mΩ :=
    sup_le_sup le_rfl (MeasurableSpace.comap_mono (ℱ.le T))
  have h2 : Measurable fun p : Set.Iic T × Ω => ofNNRealTime X p.1 p.2 := h1.mono hle le_rfl
  have h3 : Measurable fun p : ℝ × Ω => ((⟨Q54c.clampT T p.1, (Q54c.clampT_mem hT p.1).2⟩ : Set.Iic T), p.2) :=
    (((Q54c.continuous_clampT T).measurable.comp measurable_fst).subtype_mk).prodMk measurable_snd
  exact h2.comp h3


end HRS
