import HRS.MC.SEdgeVocab
import HRS.Equilibrium.Q32cAux2

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B5a

open HRS.Sec7

section Aux
variable {d : ℕ} {s : ℝ}

/-- component of the gradient kernel is integrable -/
theorem b5a_G_integrable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) (k : Fin d) :
    Integrable (fun z : Torus d => (periodicRieszGrad d s z) k) :=
  (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).integrable_comp (HRS.Q66.q66_gradKernel_integrable hd hs0 hs1)


theorem b5a_J_eq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j))
    {r : Torus d → ℝ} (hr : Torus.IsSmooth r)
    (hdiv : ∀ x, ∑ j, Torus.partialDeriv j (fun y => ρ y * v j y) x = -(ρ x * r x)) :
    ∫ x, ∫ y, HRS.Q66.q66_hv d s v x y ∂(withDensityReal ρ) ∂(withDensityReal ρ) =
      2 * ∫ x, convFun (periodicRiesz d s) (fun y => ρ y * r y) x ∂(withDensityReal ρ) := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  have hs1 : s < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hρc : Continuous ρ := HRS.Q66.q66_cont_of_smooth hρ.smooth
  have hρm : Measurable ρ := hρ.density.measurable
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hρ.pos x).le
  have hρi : Integrable ρ (volume : Measure (Torus d)) :=
    hρc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ρ)
  obtain ⟨Λ, hΛ⟩ := HRS.Q66.q66_bound_of_smooth hρ.smooth
  have hvc : ∀ k, Continuous (v k) := fun k => HRS.Q66.q66_cont_of_smooth (hv k)
  have hvm : ∀ k, Measurable (v k) := fun k => (hvc k).measurable
  choose Mv hMv using fun k => HRS.Q66.q66_bound_of_smooth
    (HRS.Q66.q66_isSmooth_mul hρ.smooth (hv k))
  have hGi : ∀ k, Integrable (fun z : Torus d => (periodicRieszGrad d s z) k) :=
    fun k => b5a_G_integrable hd hs0 hs1 k
  set a : Torus d → Torus d → ℝ := fun x y =>
    ρ x * ρ y * ∑ k, v k x * (periodicRieszGrad d s (x - y)) k with ha
  set b : Torus d → Torus d → ℝ := fun x y =>
    ρ x * ρ y * ∑ k, v k y * (periodicRieszGrad d s (x - y)) k with hb
  have hak : ∀ k, Integrable (fun p : Torus d × Torus d =>
      (ρ p.1 * v k p.1) * (ρ p.2 * (periodicRieszGrad d s (p.1 - p.2)) k))
      ((volume : Measure (Torus d)).prod volume) := by
    intro k
    have h1 := Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hρi (hGi k)
    have h2 : Integrable (fun p : Torus d × Torus d =>
        (ρ p.1 * v k p.1) * (ρ p.2 * (periodicRieszGrad d s (p.1 - p.2)) k))
        ((volume : Measure (Torus d)).prod volume) :=
      h1.bdd_mul (f := fun p : Torus d × Torus d => ρ p.1 * v k p.1)
        ((hρc.mul (hvc k)).measurable.comp measurable_fst).aestronglyMeasurable
        (Eventually.of_forall fun p => by simpa [Real.norm_eq_abs] using hMv k p.1)
    exact h2
  have haint : Integrable (Function.uncurry a) ((volume : Measure (Torus d)).prod volume) := by
    have : Function.uncurry a = fun p : Torus d × Torus d => ∑ k,
        (ρ p.1 * v k p.1) * (ρ p.2 * (periodicRieszGrad d s (p.1 - p.2)) k) := by
      funext p
      simp only [ha, Function.uncurry]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    exact integrable_finsetSum _ fun k _ => hak k
  have haswap : Integrable (fun p : Torus d × Torus d => a p.2 p.1)
      ((volume : Measure (Torus d)).prod volume) := haint.swap
  have hba : ∀ x y, b x y = -a y x := by
    intro x y
    have e : y - x = -(x - y) := by abel
    simp only [ha, hb]
    simp only [e, HRS.Q66.q66_gradKernel_odd hsd, mul_neg, Finset.sum_neg_distrib]
    ring
  have hbint : Integrable (Function.uncurry b) ((volume : Measure (Torus d)).prod volume) :=
    (haswap.neg).congr (Eventually.of_forall fun p => (hba p.1 p.2).symm)
  have hpt : ∀ x y, ρ x * (ρ y * HRS.Q66.q66_hv d s v x y) = a x y - b x y := by
    intro x y
    unfold HRS.Q66.q66_hv
    simp only [ha, hb]
    rw [← mul_sub, ← Finset.sum_sub_distrib, ← mul_assoc]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have hay : ∀ x, Integrable (a x) := by
    intro x
    have : a x = fun y => ∑ k, (ρ x * v k x) *
        (ρ y * (periodicRieszGrad d s (x - y)) k) := by
      funext y
      simp only [ha]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    exact integrable_finsetSum _ fun k _ =>
      (HRS.Q66.q66_integrable_mulG hd hs0 hs1 x k hρc).const_mul _
  have hby : ∀ x, Integrable (b x) := by
    intro x
    have : b x = fun y => ∑ k, ρ x *
        ((ρ y * v k y) * (periodicRieszGrad d s (x - y)) k) := by
      funext y
      simp only [hb]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    exact integrable_finsetSum _ fun k _ =>
      (HRS.Q66.q66_integrable_mulG hd hs0 hs1 x k (hρc.mul (hvc k))).const_mul _
  have hay_int : ∀ x, ∫ y, a x y = ρ x * ∑ k, v k x *
      (∫ y, ρ y * (periodicRieszGrad d s (x - y)) k) := by
    intro x
    have : a x = fun y => ∑ k, (ρ x * v k x) *
        (ρ y * (periodicRieszGrad d s (x - y)) k) := by
      funext y
      simp only [ha]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, integral_finsetSum _ (fun k _ =>
      (HRS.Q66.q66_integrable_mulG hd hs0 hs1 x k hρc).const_mul _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    ring
  have hconv : ∀ x, ρ x * convFun (periodicRiesz d s) (fun y => ρ y * r y) x =
      -∫ y, b x y := by
    intro x
    have h1 := HRS.Q66.q66_int_hv hd hs0 hs1 hρ hv hr hdiv x
    rw [integral_withDensityReal_eq ρ hρm hρ0] at h1
    have h2 : ρ x * ∫ y, ρ y * HRS.Q66.q66_hv d s v x y = (∫ y, a x y) - ∫ y, b x y := by
      rw [← integral_const_mul, ← integral_sub (hay x) (hby x)]
      exact integral_congr_ae (Eventually.of_forall fun y => hpt x y)
    rw [h1, hay_int, mul_add] at h2
    linarith
  have hA : ∫ x, ∫ y, b x y = -∫ x, ∫ y, a x y := by
    have e1 : ∫ x, ∫ y, b x y = -∫ x, ∫ y, a y x := by
      simp_rw [hba, integral_neg]
    have e2 : ∫ x, ∫ y, a y x = ∫ x, ∫ y, a x y :=
      integral_integral_swap (f := fun x y => a y x) haswap
    rw [e1, e2]
  have hJ : ∫ x, ∫ y, HRS.Q66.q66_hv d s v x y ∂(withDensityReal ρ) ∂(withDensityReal ρ) =
      (∫ x, ∫ y, a x y) - ∫ x, ∫ y, b x y := by
    rw [integral_withDensityReal_eq ρ hρm hρ0]
    have : ∀ x, ρ x * ∫ y, HRS.Q66.q66_hv d s v x y ∂(withDensityReal ρ) =
        (∫ y, a x y) - ∫ y, b x y := by
      intro x
      rw [integral_withDensityReal_eq ρ hρm hρ0, ← integral_const_mul,
        ← integral_sub (hay x) (hby x)]
      exact integral_congr_ae (Eventually.of_forall fun y => by
        simpa using hpt x y)
    simp_rw [this]
    exact integral_sub (haint.integral_prod_left) (hbint.integral_prod_left)
  have hC : ∫ x, convFun (periodicRiesz d s) (fun y => ρ y * r y) x ∂(withDensityReal ρ) =
      ∫ x, ∫ y, a x y := by
    rw [integral_withDensityReal_eq ρ hρm hρ0]
    simp_rw [hconv, integral_neg, hA, neg_neg]
  rw [hJ, hC, hA]
  ring

end Aux

section Facts

variable {d : ℕ} {s : ℝ}

theorem b5a_Q_prob (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {N : ℕ} (hN : 1 ≤ N) :
    IsProbabilityMeasure (sed_Q d s N β ρ) := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  rcases hβ.eq_or_lt with h0 | hpos
  · show IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))
    rw [← h0, modulatedGibbs_zero]
    infer_instance
  · obtain ⟨Λ, hΛ⟩ := HRS.Q66.q66_bound_of_smooth hρ.smooth
    exact HRS.Q32c.q32c_Q_isProb hd hs0 hsd hpos (Λ := max 1 Λ) (le_max_left _ _)
      hρ.density (fun x => (le_abs_self _).trans ((hΛ x).trans (le_max_right _ _)))
      (by omega)

theorem b5a_w_facts (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ}
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {w r : Torus d → ℝ} (hr : Torus.IsSmooth r)
    (hresp : ∀ x, r x + β * Kop (periodicRiesz d s) (withDensityReal ρ) r x =
      projMean (withDensityReal ρ) w x) :
    Measurable w ∧ ∃ M, ∀ x, |w x| ≤ M := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  have hρm : Measurable ρ := hρ.density.measurable
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hρ.pos x).le
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  -- c := g * (ρ r) and its mean m
  have hrc : Continuous r := HRS.Q66.q66_cont_of_smooth hr
  have hgm : Measurable (periodicRiesz d s) := PoleCavityAux.measurable_periodicRiesz hd hs0 hsd
  have F : HRS.PDE.MFInputs.MFKernelFacts d s := HRS.PDE.MFInputs.mfKernelFacts_of_two hd s hs0 hsd
  set c : Torus d → ℝ := convFun (periodicRiesz d s) (fun y => ρ y * r y) with hc
  set m : ℝ := ∫ x, c x ∂(withDensityReal ρ) with hm
  have hcm : Measurable c := by
    have h1 : Measurable (fun p : Torus d × Torus d =>
        periodicRiesz d s (p.1 - p.2) * (ρ p.2 * r p.2)) :=
      (hgm.comp (measurable_fst.sub measurable_snd)).mul
        ((hρm.comp measurable_snd).mul (hrc.measurable.comp measurable_snd))
    exact (h1.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  obtain ⟨Mr, hMr⟩ := HRS.Q66.q66_bound_of_smooth (HRS.Q66.q66_isSmooth_mul hρ.smooth hr)
  have hcb : ∀ x, |c x| ≤ (∫ y, |periodicRiesz d s y|) * Mr := fun x =>
    HRS.PDE.MFThermalExist.convFun_bound_of_le F.integrable hMr x
  have hKr : ∀ x, Kop (periodicRiesz d s) (withDensityReal ρ) r x = c x - m := by
    intro x
    have hcc : ∀ x, ∫ y, periodicRiesz d s (x - y) * r y ∂(withDensityReal ρ) = c x := by
      intro x
      rw [integral_withDensityReal_eq ρ hρm hρ0]
      exact integral_congr_ae (Eventually.of_forall fun y => by ring)
    simp only [Kop, projMean, pair, hcc, hm]
  set u : ℝ := pair (withDensityReal ρ) w with hu
  have hw : ∀ x, w x = r x + β * (c x - m) + u := by
    intro x
    have h := hresp x
    rw [hKr x] at h
    unfold projMean at h
    linarith
  have hwm : Measurable w := by
    have : w = fun x => r x + β * (c x - m) + u := funext hw
    rw [this]
    exact (hrc.measurable.add ((hcm.sub_const m).const_mul β)).add_const u
  obtain ⟨Mr0, hMr0⟩ : ∃ M, ∀ x, |r x| ≤ M := HRS.Q66.q66_bound_of_smooth hr
  set Mw : ℝ := Mr0 + |β| * ((∫ y, |periodicRiesz d s y|) * Mr + |m|) + |u| with hMw
  have hwb : ∀ x, |w x| ≤ Mw := by
    intro x
    rw [hw x]
    calc |r x + β * (c x - m) + u| ≤ |r x + β * (c x - m)| + |u| := abs_add_le _ _
      _ ≤ (|r x| + |β * (c x - m)|) + |u| := by gcongr; exact abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul]
        have h1 : |c x - m| ≤ (∫ y, |periodicRiesz d s y|) * Mr + |m| :=
          (abs_sub _ _).trans (by linarith [hcb x])
        have := hMr0 x
        have := mul_le_mul_of_nonneg_left h1 (abs_nonneg β)
        simp only [hMw]
        linarith
  exact ⟨hwm, Mw, hwb⟩

end Facts

section Main

variable {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
  {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
include hd hs0 hs hβ hρ

theorem sed_B5a_stein_raw_proof {N : ℕ} (hN : 1 ≤ N) {w r : Torus d → ℝ} (hr : Torus.IsSmooth r)
    {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j))
    (hdiv : ∀ x, ∑ j, Torus.partialDeriv j (fun y => ρ y * v j y) x = -(ρ x * r x))
    (hresp : ∀ x, r x + β * Kop (periodicRiesz d s) (withDensityReal ρ) r x =
      projMean (withDensityReal ρ) w x)
    (hint : Integrable
      (fun X : Config d N => modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ))
      (sed_Q d s N β ρ))
    {Ψ : Config d N → ℝ} {dΨ : Fin N → Fin d → Config d N → ℝ}
    (hΨm : Measurable Ψ) (hΨb : ∃ M, ∀ X, |Ψ X| ≤ M)
    (hdΨm : ∀ (i : Fin N) (k : Fin d), Measurable (dΨ i k)) (hdΨb : ∃ M, ∀ i k X, |dΨ i k X| ≤ M)
    (hΨline : ∀ (i : Fin N) (k : Fin d) (Y : Config d N), (∀ a b : Fin N, a ≠ b → Y a ≠ Y b) →
      HasDerivAt (fun τ : ℝ => Ψ (Q84d.lineCfg i k Y τ)) (dΨ i k Y) 0) :
    ∫ X, Ψ X * ((N : ℝ) * (pair (empirical X) w - pair (withDensityReal ρ) w) +
        β * ((N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)))
      ∂(sed_Q d s N β ρ) =
    ∫ X, ∑ i, ∑ k, v k (X i) * dΨ i k X ∂(sed_Q d s N β ρ) := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hρc : Continuous ρ := HRS.Q66.q66_cont_of_smooth hρ.smooth
  have hρm : Measurable ρ := hρ.density.measurable
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hρ.pos x).le
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  -- the Gibbs law is a probability measure
  have hQ : IsProbabilityMeasure (sed_Q d s N β ρ) := by
    rcases hβ.eq_or_lt with h0 | hpos
    · show IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))
      rw [← h0, modulatedGibbs_zero]
      infer_instance
    · obtain ⟨Λ, hΛ⟩ := HRS.Q66.q66_bound_of_smooth hρ.smooth
      exact HRS.Q32c.q32c_Q_isProb hd hs0 hsd hpos (Λ := max 1 Λ) (le_max_left _ _)
        hρ.density (fun x => (le_abs_self _).trans ((hΛ x).trans (le_max_right _ _)))
        (by omega)
  -- c := g * (ρ r) and its mean m
  have hrc : Continuous r := HRS.Q66.q66_cont_of_smooth hr
  have hgm : Measurable (periodicRiesz d s) := PoleCavityAux.measurable_periodicRiesz hd hs0 hsd
  have F : HRS.PDE.MFInputs.MFKernelFacts d s := HRS.PDE.MFInputs.mfKernelFacts_of_two hd s hs0 hsd
  set c : Torus d → ℝ := convFun (periodicRiesz d s) (fun y => ρ y * r y) with hc
  set m : ℝ := ∫ x, c x ∂(withDensityReal ρ) with hm
  have hJ : ∫ x, ∫ y, HRS.Q66.q66_hv d s v x y ∂(withDensityReal ρ) ∂(withDensityReal ρ) =
      2 * m := b5a_J_eq hd hs0 hs hρ hv hr hdiv
  have hcm : Measurable c := by
    have h1 : Measurable (fun p : Torus d × Torus d =>
        periodicRiesz d s (p.1 - p.2) * (ρ p.2 * r p.2)) :=
      (hgm.comp (measurable_fst.sub measurable_snd)).mul
        ((hρm.comp measurable_snd).mul (hrc.measurable.comp measurable_snd))
    exact (h1.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  obtain ⟨Mr, hMr⟩ := HRS.Q66.q66_bound_of_smooth (HRS.Q66.q66_isSmooth_mul hρ.smooth hr)
  have hcb : ∀ x, |c x| ≤ (∫ y, |periodicRiesz d s y|) * Mr := fun x =>
    HRS.PDE.MFThermalExist.convFun_bound_of_le F.integrable hMr x
  have hKr : ∀ x, Kop (periodicRiesz d s) (withDensityReal ρ) r x = c x - m := by
    intro x
    have hcc : ∀ x, ∫ y, periodicRiesz d s (x - y) * r y ∂(withDensityReal ρ) = c x := by
      intro x
      rw [integral_withDensityReal_eq ρ hρm hρ0]
      exact integral_congr_ae (Eventually.of_forall fun y => by ring)
    simp only [Kop, projMean, pair, hcc, hm]
  set u : ℝ := pair (withDensityReal ρ) w with hu
  have hw : ∀ x, w x = r x + β * (c x - m) + u := by
    intro x
    have h := hresp x
    rw [hKr x] at h
    unfold projMean at h
    linarith
  have hwm : Measurable w := by
    have : w = fun x => r x + β * (c x - m) + u := funext hw
    rw [this]
    exact (hrc.measurable.add ((hcm.sub_const m).const_mul β)).add_const u
  obtain ⟨Mr0, hMr0⟩ : ∃ M, ∀ x, |r x| ≤ M := HRS.Q66.q66_bound_of_smooth hr
  set Mw : ℝ := Mr0 + |β| * ((∫ y, |periodicRiesz d s y|) * Mr + |m|) + |u| with hMw
  have hwb : ∀ x, |w x| ≤ Mw := by
    intro x
    rw [hw x]
    calc |r x + β * (c x - m) + u| ≤ |r x + β * (c x - m)| + |u| := abs_add_le _ _
      _ ≤ (|r x| + |β * (c x - m)|) + |u| := by gcongr; exact abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul]
        have h1 : |c x - m| ≤ (∫ y, |periodicRiesz d s y|) * Mr + |m| :=
          (abs_sub _ _).trans (by linarith [hcb x])
        have := hMr0 x
        have := mul_le_mul_of_nonneg_left h1 (abs_nonneg β)
        simp only [hMw]
        linarith
  obtain ⟨MΨ, hMΨ⟩ := id hΨb
  obtain ⟨MdΨ, hMdΨ⟩ := id hdΨb
  have hvc : ∀ k, Continuous (v k) := fun k => HRS.Q66.q66_cont_of_smooth (hv k)
  choose Mv hMv using fun k => HRS.Q66.q66_bound_of_smooth (hv k)
  have hpe : ∀ X : Config d N, pair (empirical X) w = (N : ℝ)⁻¹ * ∑ i, w (X i) :=
    fun X => pair_empirical (by omega) X w
  have hE1 : ∀ X : Config d N, (N : ℝ) * (pair (empirical X) w - u) = ∑ i, w (X i) - N * u := by
    intro X
    rw [hpe X]
    field_simp
  have hsumw : Measurable (fun X : Config d N => ∑ i, w (X i)) :=
    Finset.measurable_sum _ fun i _ => hwm.comp (measurable_pi_apply i)
  have hE1m : Measurable (fun X : Config d N => (N : ℝ) * (pair (empirical X) w - u)) := by
    simp_rw [hE1]
    exact hsumw.sub measurable_const
  have hE1b : ∀ X : Config d N, |(N : ℝ) * (pair (empirical X) w - u)| ≤ N * Mw + N * |u| := by
    intro X
    rw [hE1 X]
    have h1 : |∑ i, w (X i)| ≤ N * Mw := by
      calc |∑ i, w (X i)| ≤ ∑ i, |w (X i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, Mw := Finset.sum_le_sum fun i _ => hwb _
        _ = N * Mw := by simp
    calc |∑ i, w (X i) - N * u| ≤ |∑ i, w (X i)| + |(N : ℝ) * u| := abs_sub _ _
      _ ≤ N * Mw + N * |u| := by
        rw [abs_mul, abs_of_pos hNp]; linarith
  have hT1 : Integrable (fun X : Config d N => Ψ X * ((N : ℝ) * (pair (empirical X) w - u)))
      (sed_Q d s N β ρ) := by
    refine Integrable.of_bound (C := MΨ * (N * Mw + N * |u|)) (hΨm.mul hE1m).aestronglyMeasurable
      (Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hMΨ X) (hE1b X) (abs_nonneg _) ((abs_nonneg _).trans (hMΨ X))
  have hT2 : Integrable (fun X : Config d N => Ψ X * ((N : ℝ) *
      modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ))) (sed_Q d s N β ρ) :=
    (hint.const_mul (N : ℝ)).bdd_mul hΨm.aestronglyMeasurable
      (Eventually.of_forall fun X => by simpa [Real.norm_eq_abs] using hMΨ X)
  have hTi : Integrable (fun X : Config d N => Ψ X * ((N : ℝ) * (pair (empirical X) w -
      pair (withDensityReal ρ) w) +
      β * ((N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ))))
      (sed_Q d s N β ρ) :=
    (hT1.add (hT2.const_mul β)).congr (Eventually.of_forall fun X => by
      simp only [hu, Pi.add_apply]; ring)
  have hSm : Measurable (fun X : Config d N => ∑ i, ∑ k, v k (X i) * dΨ i k X) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ =>
      ((hvc k).measurable.comp (measurable_pi_apply i)).mul (hdΨm i k)
  have hSi : Integrable (fun X : Config d N => ∑ i, ∑ k, v k (X i) * dΨ i k X)
      (sed_Q d s N β ρ) := by
    refine Integrable.of_bound (C := ∑ _i : Fin N, ∑ k, Mv k * MdΨ) hSm.aestronglyMeasurable
      (Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs]
    calc |∑ i, ∑ k, v k (X i) * dΨ i k X| ≤ ∑ i, |∑ k, v k (X i) * dΨ i k X| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin N, ∑ k, Mv k * MdΨ := Finset.sum_le_sum fun i _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => by
            rw [abs_mul]
            exact mul_le_mul (hMv k _) (hMdΨ i k X) (abs_nonneg _)
              ((abs_nonneg _).trans (hMv k (X i))))
  have key : ∀ X : Config d N,
      Ψ X * ((N : ℝ) * (pair (empirical X) w - u) +
        β * ((N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ))) -
        ∑ i, ∑ k, v k (X i) * dΨ i k X =
      -(-(∑ i, r (X i)) * Ψ X + ∑ i, ∑ k, v k (X i) * dΨ i k X
        - β * ∑ i, ∑ k, v k (X i) * HRS.Q84d.Bik d s (HRS.Q66.q66_Vrho d s ρ) i k X * Ψ X) := by
    intro X
    have e3 := HRS.Q66.q66_T_eq hd hs0 hs hρ hv hr hdiv hN X
    rw [hJ] at e3
    have e2 : ∑ i, w (X i) = ∑ i, r (X i) + β * ∑ i, c (X i) - β * N * m + N * u := by
      calc ∑ i, w (X i) = ∑ i, (r (X i) + β * (c (X i) - m) + u) :=
            Finset.sum_congr rfl fun i _ => hw _
        _ = _ := by
          simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
    have hS : ∑ i, ∑ k, v k (X i) * HRS.Q84d.Bik d s (HRS.Q66.q66_Vrho d s ρ) i k X * Ψ X =
        (∑ i, ∑ k, v k (X i) * HRS.Q84d.Bik d s (HRS.Q66.q66_Vrho d s ρ) i k X) * Ψ X := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
    rw [hS]
    linear_combination (Ψ X) * (hE1 X + e2 - β * e3)
  have hraw := HRS.Q66.q66_stein_raw hd hs0 hs hβ hρ hN hv hr hdiv hΨm hΨb hdΨm hdΨb hΨline
  have h0 : ∫ X, (Ψ X * ((N : ℝ) * (pair (empirical X) w - u) +
        β * ((N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ))) -
        ∑ i, ∑ k, v k (X i) * dΨ i k X) ∂(sed_Q d s N β ρ) = 0 := by
    simp_rw [key]
    rw [integral_neg]
    have : (sed_Q d s N β ρ) = modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) := rfl
    rw [this, hraw, neg_zero]
  rw [integral_sub hTi hSi] at h0
  linarith

end Main


end HRS.MC.SEdge.B5a
