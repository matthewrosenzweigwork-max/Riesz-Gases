import HRS.Prob.HilbertMartingale

/-!
# S.A.7, abstract assembly with a measure-level target

`hilbert_wasserstein_assembly_w1/_w2` need the model initial field `I` to be measurable for the initial sigma-field of the
same probability space; the field theorems only know `I` through its law.  Here the target is `μ_I ∗ Law(G_t)` for an
arbitrary probability measure `μ_I`:

* `sa6_wass_conv_le`: `W_p(μ ∗ γ, ν ∗ γ) ≤ W_p(μ, ν)`;
* `sa6_assembly_w1`, `sa6_assembly_w2`: `W_p(Law(I_emp + M_t + R), μ_I ∗ Law G_t) ≤ W_p(Law I_emp, μ_I) + D^{1/2} +
  (E‖R‖^p)^{1/p}` for `E‖M_t - G_t‖² ≤ D`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdField

section Wass

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

lemma sa6_wass_conv_le (p : ℝ) (hp : 1 ≤ p) (μ ν γ : Measure H) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure γ] :
    wassersteinE p ((μ.prod γ).map (fun z : H × H => z.1 + z.2))
      ((ν.prod γ).map (fun z : H × H => z.1 + z.2)) ≤ wassersteinE p μ ν := by
  have hp0 : 0 < p := by linarith
  refine le_iInf fun π => ?_
  obtain ⟨π, hπ⟩ := π
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hkey : ∀ (f : H × H → H), Measurable f → ∀ (ρ : Measure H), π.map f = ρ →
      ((π.prod γ).map (fun w : (H × H) × H => f w.1 + w.2)) =
        (ρ.prod γ).map (fun z : H × H => z.1 + z.2) := by
    intro f hf ρ hρ
    have e1 : (fun w : (H × H) × H => f w.1 + w.2) =
        (fun z : H × H => z.1 + z.2) ∘ (Prod.map f id) := by ext w <;> simp
    rw [e1, ← Measure.map_map (by fun_prop) (by fun_prop), ← hρ]
    congr 1
    rw [← Measure.map_prod_map _ _ hf measurable_id, Measure.map_id]
  set T : (H × H) × H → H × H := fun w => (w.1.1 + w.2, w.1.2 + w.2) with hT
  have hTm : Measurable T := by rw [hT]; fun_prop
  have hcoup : IsCoupling ((π.prod γ).map T)
      ((μ.prod γ).map (fun z : H × H => z.1 + z.2))
      ((ν.prod γ).map (fun z : H × H => z.1 + z.2)) := by
    constructor
    · rw [Measure.map_map measurable_fst hTm]
      exact hkey Prod.fst measurable_fst _ hπ.1
    · rw [Measure.map_map measurable_snd hTm]
      exact hkey Prod.snd measurable_snd _ hπ.2
  refine (wassersteinE_le_cost hcoup).trans ?_
  refine le_of_eq ?_
  congr 1
  rw [lintegral_map (by fun_prop) hTm]
  have : ∀ w : (H × H) × H, ENNReal.ofReal (‖(T w).1 - (T w).2‖ ^ p) =
      ENNReal.ofReal (‖w.1.1 - w.1.2‖ ^ p) := fun w => by
    simp [hT]
  simp only [this]
  rw [lintegral_prod _ (by fun_prop)]
  simp

lemma sa6_assembly_wp (p : ℝ) (hp : 1 ≤ p) (𝒢 : SubSigma Ω mΩ) (Iemp R Mt Gt : Ω → H)
    (μI : Measure H) [IsProbabilityMeasure μI]
    (hIemp : Measurable[𝒢.1] Iemp) (hR : AEMeasurable R P) (hMt : AEMeasurable Mt P)
    (hGt : AEMeasurable Gt P) (hind : Indep 𝒢.1 (MeasurableSpace.comap Gt inferInstance) P) :
    wassersteinE p (law P fun ω => Iemp ω + Mt ω + R ω)
        ((μI.prod (law P Gt)).map (fun z : H × H => z.1 + z.2)) ≤
      wassersteinE p (law P Iemp) μI +
        (∫⁻ ω, ENNReal.ofReal (‖Mt ω - Gt ω‖ ^ p) ∂P) ^ (1 / p) +
        (∫⁻ ω, ENNReal.ofReal (‖R ω‖ ^ p) ∂P) ^ (1 / p) := by
  have hIm : AEMeasurable Iemp P := (hIemp.mono 𝒢.2 le_rfl).aemeasurable
  have h1 : AEMeasurable (fun ω => Iemp ω + Mt ω + R ω) P := (hIm.add hMt).add hR
  have h2 : AEMeasurable (fun ω => Iemp ω + Mt ω) P := hIm.add hMt
  have h3 : AEMeasurable (fun ω => Iemp ω + Gt ω) P := hIm.add hGt
  haveI : IsProbabilityMeasure (law P Iemp) := (Measure.isProbabilityMeasure_map_iff hIm).2 inferInstance
  haveI : IsProbabilityMeasure (law P Gt) := (Measure.isProbabilityMeasure_map_iff hGt).2 inferInstance
  haveI : IsProbabilityMeasure (law P fun ω => Iemp ω + Mt ω + R ω) :=
    (Measure.isProbabilityMeasure_map_iff h1).2 inferInstance
  haveI : IsProbabilityMeasure (law P fun ω => Iemp ω + Mt ω) :=
    (Measure.isProbabilityMeasure_map_iff h2).2 inferInstance
  haveI : IsProbabilityMeasure (law P fun ω => Iemp ω + Gt ω) :=
    (Measure.isProbabilityMeasure_map_iff h3).2 inferInstance
  haveI : IsProbabilityMeasure ((μI.prod (law P Gt)).map (fun z : H × H => z.1 + z.2)) :=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance
  have t1 := wassersteinE_triangle p hp (law P fun ω => Iemp ω + Mt ω + R ω)
    (law P fun ω => Iemp ω + Mt ω) ((μI.prod (law P Gt)).map (fun z : H × H => z.1 + z.2))
  have t2 := wassersteinE_triangle p hp (law P fun ω => Iemp ω + Mt ω)
    (law P fun ω => Iemp ω + Gt ω) ((μI.prod (law P Gt)).map (fun z : H × H => z.1 + z.2))
  have c1 := wassersteinE_le_of_coupling P p hp _ _ h1 h2
  have c2 := wassersteinE_le_of_coupling P p hp _ _ h2 h3
  have c3 : wassersteinE p (law P fun ω => Iemp ω + Gt ω)
      ((μI.prod (law P Gt)).map (fun z : H × H => z.1 + z.2)) ≤ wassersteinE p (law P Iemp) μI := by
    rw [HRS.law_add_indep P 𝒢 Iemp Gt hIemp hGt hind]
    exact sa6_wass_conv_le p hp (law P Iemp) μI (law P Gt)
  have e1 : ∀ ω, ‖Iemp ω + Mt ω + R ω - (Iemp ω + Mt ω)‖ = ‖R ω‖ := fun ω => by
    rw [add_sub_cancel_left]
  have e2 : ∀ ω, ‖Iemp ω + Mt ω - (Iemp ω + Gt ω)‖ = ‖Mt ω - Gt ω‖ := fun ω => by
    rw [add_sub_add_left_eq_sub]
  simp only [e1, e2] at c1 c2
  calc _ ≤ _ := t1
    _ ≤ (∫⁻ ω, ENNReal.ofReal (‖R ω‖ ^ p) ∂P) ^ (1 / p) +
        ((∫⁻ ω, ENNReal.ofReal (‖Mt ω - Gt ω‖ ^ p) ∂P) ^ (1 / p) +
          wassersteinE p (law P Iemp) μI) := by
      refine add_le_add c1 (t2.trans ?_)
      exact add_le_add c2 c3
    _ = _ := by ring

theorem sa6_assembly_w1 (𝒢 : SubSigma Ω mΩ) (Iemp R Mt Gt : Ω → H) (μI : Measure H)
    [IsProbabilityMeasure μI] (hIemp : Measurable[𝒢.1] Iemp) (hR : AEMeasurable R P)
    (hMt : AEMeasurable Mt P) (hGt : AEMeasurable Gt P)
    (hind : Indep 𝒢.1 (MeasurableSpace.comap Gt inferInstance) P)
    (D : ℝ) (hD : 0 ≤ D) (hcoup : ∫⁻ ω, ‖Mt ω - Gt ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal D) :
    wassersteinE 1 (law P fun ω => Iemp ω + Mt ω + R ω)
        ((μI.prod (law P Gt)).map (fun z : H × H => z.1 + z.2)) ≤
      wassersteinE 1 (law P Iemp) μI + ENNReal.ofReal (Real.sqrt D) + ∫⁻ ω, ‖R ω‖ₑ ∂P := by
  have h := sa6_assembly_wp P 1 le_rfl 𝒢 Iemp R Mt Gt μI hIemp hR hMt hGt hind
  have e1 : ∀ x : H, ENNReal.ofReal (‖x‖ ^ (1 : ℝ)) = ‖x‖ₑ := fun x => by
    rw [Real.rpow_one, ofReal_norm]
  simp only [e1, div_one, ENNReal.rpow_one] at h
  refine h.trans ?_
  gcongr
  have hm : AEMeasurable (fun ω => ‖Mt ω - Gt ω‖ₑ) P := (hMt.sub hGt).enorm
  have := lintegral_rpow_mono P (fun ω => ‖Mt ω - Gt ω‖ₑ) (p := 1) (q := 2) one_pos one_le_two
  simp only [ENNReal.rpow_one, div_one, ENNReal.rpow_two] at this
  refine this.trans ?_
  have h2 : (∫⁻ ω, ‖Mt ω - Gt ω‖ₑ ^ 2 ∂P) ^ (1 / (2 : ℝ)) ≤ (ENNReal.ofReal D) ^ (1 / (2 : ℝ)) :=
    ENNReal.rpow_le_rpow hcoup (by norm_num)
  refine h2.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg hD (by norm_num), Real.sqrt_eq_rpow, one_div]

theorem sa6_assembly_w2 (𝒢 : SubSigma Ω mΩ) (Iemp R Mt Gt : Ω → H) (μI : Measure H)
    [IsProbabilityMeasure μI] (hIemp : Measurable[𝒢.1] Iemp) (hR : AEMeasurable R P)
    (hMt : AEMeasurable Mt P) (hGt : AEMeasurable Gt P)
    (hind : Indep 𝒢.1 (MeasurableSpace.comap Gt inferInstance) P)
    (D : ℝ) (hD : 0 ≤ D) (hcoup : ∫⁻ ω, ‖Mt ω - Gt ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal D) :
    wassersteinE 2 (law P fun ω => Iemp ω + Mt ω + R ω)
        ((μI.prod (law P Gt)).map (fun z : H × H => z.1 + z.2)) ≤
      wassersteinE 2 (law P Iemp) μI + ENNReal.ofReal (Real.sqrt D) +
        (∫⁻ ω, ‖R ω‖ₑ ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
  have h := sa6_assembly_wp P 2 (by norm_num) 𝒢 Iemp R Mt Gt μI hIemp hR hMt hGt hind
  have e1 : ∀ x : H, ENNReal.ofReal (‖x‖ ^ (2 : ℝ)) = ‖x‖ₑ ^ 2 := fun x => by
    rw [Real.rpow_two, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simp only [e1] at h
  refine h.trans ?_
  gcongr
  have h2 : (∫⁻ ω, ‖Mt ω - Gt ω‖ₑ ^ 2 ∂P) ^ (1 / (2 : ℝ)) ≤ (ENNReal.ofReal D) ^ (1 / (2 : ℝ)) :=
    ENNReal.rpow_le_rpow hcoup (by norm_num)
  refine h2.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg hD (by norm_num), Real.sqrt_eq_rpow, one_div]

end Wass

end HRS.MS.MainRdField
