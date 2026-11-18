import HRS.Main.ThermLinPlan2
import HRS.Main.ThermLin2Mo1

/-!
# THERMLIN2 Fu1: deterministic Fubini swaps on the triangle (helpers for `tl2_dyson_fubini`, B4)

* `tl2fu_swap`: `∫_{r∈[0,t]} ∫_{σ∈[0,r]} g σ r = ∫_{σ∈[0,t]} ∫_{r∈[σ,t]} g σ r` for bounded measurable `g`.
* `tl2fu_E1`, `tl2fu_E2`: the two identities obtained from the weak identity `ℓ(a_σ) = ∫_σ^t ℓ(w(r,σ)) dr`
  (this is the Dyson identity paired with `z`, through `tl2_dyson_pairing`) and the covariation form `Cd σ`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.Uniform.Q54c

theorem tl2fu_Icc_inter_Iic {t r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    Set.Icc (0 : ℝ) t ∩ Set.Iic r = Set.Icc 0 r := by
  ext σ
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hr.2⟩, h2⟩

theorem tl2fu_Icc_inter_Ici {t σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) t) :
    Set.Icc (0 : ℝ) t ∩ Set.Ici σ = Set.Icc σ t := by
  ext r
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨hσ.1.trans h1, h2⟩, h1⟩

/-- Swap of the order of integration on the triangle `0 ≤ σ ≤ r ≤ t`. -/
theorem tl2fu_swap {t : ℝ} (g : ℝ → ℝ → ℝ)
    (hg : Measurable (fun p : ℝ × ℝ => g p.1 p.2)) (c : ℝ → ℝ) (hc : IntegrableOn c (Set.Icc 0 t))
    (K : ℝ) (hb : ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ r ∈ Set.Icc (0 : ℝ) t, σ ≤ r → |g σ r| ≤ c σ * K) :
    ∫ r in Set.Icc (0 : ℝ) t, ∫ σ in Set.Icc (0 : ℝ) r, g σ r =
      ∫ σ in Set.Icc (0 : ℝ) t, ∫ r in Set.Icc σ t, g σ r := by
  set I := Set.Icc (0 : ℝ) t with hI
  set g' : ℝ → ℝ → ℝ := fun σ r => if σ ≤ r then g σ r else 0 with hg'
  have e1 : ∀ r ∈ I, ∫ σ in Set.Icc (0 : ℝ) r, g σ r = ∫ σ in I, g' σ r := by
    intro r hr
    have : (fun σ => g' σ r) = (Set.Iic r).indicator (fun σ => g σ r) := by
      funext σ; simp [hg', Set.indicator_apply]
    rw [this, setIntegral_indicator measurableSet_Iic, tl2fu_Icc_inter_Iic hr]
  have e2 : ∀ σ ∈ I, ∫ r in I, g' σ r = ∫ r in Set.Icc σ t, g σ r := by
    intro σ hσ
    have : (fun r => g' σ r) = (Set.Ici σ).indicator (fun r => g σ r) := by
      funext r; simp [hg', Set.indicator_apply]
    rw [this, setIntegral_indicator measurableSet_Ici, tl2fu_Icc_inter_Ici hσ]
  have hg'm : Measurable (fun p : ℝ × ℝ => g' p.1 p.2) := by
    refine Measurable.ite (measurableSet_le measurable_fst measurable_snd) hg measurable_const
  have hint : Integrable (Function.uncurry fun r σ => g' σ r)
      ((volume.restrict I).prod (volume.restrict I)) := by
    have hbd : Integrable (fun z : ℝ × ℝ => (1 : ℝ) * (c z.2 * K))
        ((volume.restrict I).prod (volume.restrict I)) :=
      (integrable_const (1 : ℝ)).mul_prod (hc.mul_const K)
    refine hbd.mono' ?_ ?_
    · exact (hg'm.comp measurable_swap).aestronglyMeasurable
    · rw [Measure.prod_restrict]
      refine (ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).2
        (Eventually.of_forall fun p hp => ?_)
      simp only [Function.uncurry, hg', Real.norm_eq_abs, one_mul]
      split_ifs with h
      · exact hb p.2 hp.2 p.1 hp.1 h
      · simp only [abs_zero]
        have := hb p.2 hp.2 p.2 hp.2 le_rfl
        exact (abs_nonneg _).trans this
  rw [setIntegral_congr_fun measurableSet_Icc (fun r hr => e1 r hr)]
  have hsw := integral_integral_swap hint
  rw [hsw]
  exact setIntegral_congr_fun measurableSet_Icc (fun σ hσ => e2 σ hσ)

section Det

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem tl2fu_interval_eq {t σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) t) (f : ℝ → ℝ) :
    ∫ r in Set.Icc σ t, f r = ∫ r in σ..t, f r := by
  rw [intervalIntegral.integral_of_le hσ.2, integral_Icc_eq_integral_Ioc]

/-- E1: from the weak identity, `∫ Cd(a,a) = ∫_r ∫_{σ ≤ r} Cd(a, w_r)`. -/
theorem tl2fu_E1 {t : ℝ} (Cd : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (hCm : ∀ u v : H, Measurable fun σ => Cd σ u v) (c : ℝ → ℝ) (hc : IntegrableOn c (Set.Icc 0 t))
    (hc0 : ∀ σ ∈ Set.Icc (0 : ℝ) t, 0 ≤ c σ)
    (hCb : ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ u v : H, |Cd σ u v| ≤ c σ * (‖u‖ * ‖v‖))
    (a : ℝ → H) (w : ℝ → ℝ → H) (ham : Measurable a) (hwm : Measurable fun p : ℝ × ℝ => w p.1 p.2)
    {Ba Bw : ℝ} (haB : ∀ σ ∈ Set.Icc (0 : ℝ) t, ‖a σ‖ ≤ Ba)
    (hwB : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ σ ∈ Set.Icc (0 : ℝ) r, ‖w r σ‖ ≤ Bw)
    (hweak : ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ l : H →L[ℝ] ℝ, l (a σ) = ∫ r in σ..t, l (w r σ)) :
    ∫ σ in Set.Icc (0 : ℝ) t, Cd σ (a σ) (a σ) =
      ∫ r in Set.Icc (0 : ℝ) t, ∫ σ in Set.Icc (0 : ℝ) r, Cd σ (a σ) (w r σ) := by
  have hmeas : Measurable (fun p : ℝ × ℝ => Cd p.1 (a p.1) (w p.2 p.1)) := by
    have h1 : Measurable fun p : ℝ × ℝ => ((a p.1, w p.2 p.1), p.1) :=
      ((ham.comp measurable_fst).prodMk (hwm.comp measurable_swap)).prodMk measurable_fst
    exact (measurable_form_apply hCm).comp h1
  rw [tl2fu_swap (t := t) (fun σ r => Cd σ (a σ) (w r σ)) hmeas c hc (Ba * Bw) ?_]
  · refine setIntegral_congr_fun measurableSet_Icc (fun σ hσ => ?_)
    rw [tl2fu_interval_eq hσ, ← hweak σ hσ (Cd σ (a σ))]
  · intro σ hσ r hr hσr
    refine (hCb σ hσ _ _).trans ?_
    have h1 := haB σ hσ
    have h2 := hwB r hr σ ⟨hσ.1, hσr⟩
    have h3 := hc0 σ hσ
    calc c σ * (‖a σ‖ * ‖w r σ‖) ≤ c σ * (Ba * Bw) := by
          apply mul_le_mul_of_nonneg_left _ h3
          exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

/-- E2: `∫_{r'} ∫_{σ ≤ r ∧ r'} Cd(w_r, w_{r'}) = ∫_{σ ≤ r} Cd(a, w_r)`. -/
theorem tl2fu_E2 {t : ℝ} (Cd : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (hCm : ∀ u v : H, Measurable fun σ => Cd σ u v) (c : ℝ → ℝ) (hc : IntegrableOn c (Set.Icc 0 t))
    (hc0 : ∀ σ ∈ Set.Icc (0 : ℝ) t, 0 ≤ c σ)
    (hCb : ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ u v : H, |Cd σ u v| ≤ c σ * (‖u‖ * ‖v‖))
    (hsymm : ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ u v : H, Cd σ u v = Cd σ v u)
    (a : ℝ → H) (w : ℝ → ℝ → H) (hwm : Measurable fun p : ℝ × ℝ => w p.1 p.2)
    {Bw : ℝ} (hwB : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ σ ∈ Set.Icc (0 : ℝ) r, ‖w r σ‖ ≤ Bw)
    (hweak : ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ l : H →L[ℝ] ℝ, l (a σ) = ∫ r in σ..t, l (w r σ))
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    ∫ r' in Set.Icc (0 : ℝ) t, ∫ σ in Set.Icc (0 : ℝ) (min r r'), Cd σ (w r σ) (w r' σ) =
      ∫ σ in Set.Icc (0 : ℝ) r, Cd σ (a σ) (w r σ) := by
  set g : ℝ → ℝ → ℝ := fun σ r' => if σ ≤ r then Cd σ (w r σ) (w r' σ) else 0 with hg
  have hmeas : Measurable (fun p : ℝ × ℝ => g p.1 p.2) := by
    have h1 : Measurable fun p : ℝ × ℝ => ((w r p.1, w p.2 p.1), p.1) :=
      ((hwm.comp (measurable_const.prodMk measurable_fst)).prodMk (hwm.comp measurable_swap)).prodMk
        measurable_fst
    exact Measurable.ite (measurableSet_le measurable_fst measurable_const)
      ((measurable_form_apply hCm).comp h1) measurable_const
  have e1 : ∀ r' ∈ Set.Icc (0 : ℝ) t, ∫ σ in Set.Icc (0 : ℝ) (min r r'), Cd σ (w r σ) (w r' σ) =
      ∫ σ in Set.Icc (0 : ℝ) r', g σ r' := by
    intro r' hr'
    have : (fun σ => g σ r') = (Set.Iic r).indicator (fun σ => Cd σ (w r σ) (w r' σ)) := by
      funext σ; simp [hg, Set.indicator_apply]
    have hset : Set.Icc (0 : ℝ) r' ∩ Set.Iic r = Set.Icc 0 (min r r') := by
      ext σ
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic, le_min_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h3, h2⟩
      · rintro ⟨h1, h3, h2⟩; exact ⟨⟨h1, h2⟩, h3⟩
    rw [this, setIntegral_indicator measurableSet_Iic, hset]
  rw [setIntegral_congr_fun measurableSet_Icc (fun r' hr' => e1 r' hr')]
  rw [tl2fu_swap (t := t) g hmeas c hc (Bw * Bw) ?_]
  · have e2 : ∀ σ ∈ Set.Icc (0 : ℝ) t, ∫ r' in Set.Icc σ t, g σ r' =
        (Set.Iic r).indicator (fun σ => Cd σ (a σ) (w r σ)) σ := by
      intro σ hσ
      by_cases hσr : σ ≤ r
      · simp only [hg, hσr, ↓reduceIte, Set.indicator_of_mem (Set.mem_Iic.2 hσr)]
        rw [tl2fu_interval_eq hσ, ← hweak σ hσ (Cd σ (w r σ))]
        exact hsymm σ hσ _ _
      · simp [hg, hσr]
    rw [setIntegral_congr_fun measurableSet_Icc (fun σ hσ => e2 σ hσ), setIntegral_indicator measurableSet_Iic,
      tl2fu_Icc_inter_Iic hr]
  · intro σ hσ r' hr' hσr'
    simp only [hg]
    split_ifs with h
    · refine (hCb σ hσ _ _).trans ?_
      have h1 := hwB r hr σ ⟨hσ.1, h⟩
      have h2 := hwB r' hr' σ ⟨hσ.1, hσr'⟩
      have h3 := hc0 σ hσ
      apply mul_le_mul_of_nonneg_left _ h3
      exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    · simp only [abs_zero]
      have h1 := hwB r hr 0 ⟨le_rfl, hr.1⟩
      have h3 := hc0 σ hσ
      have h0 : 0 ≤ Bw := (norm_nonneg _).trans h1
      exact mul_nonneg h3 (mul_nonneg h0 h0)

end Det

end HRS.ThermLin.Plan2
