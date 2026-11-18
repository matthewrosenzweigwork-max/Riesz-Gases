import HRS.PDE.TorusFPEntropyMeasureAux5

/-!
# D3-b, Aux6: entropy relative to the moving reference (proof of `d3_entropy_moving`)

`H(μ|q^t) = H(μ|G) - ∫ψ^t dμ + log Z̃_t` with `Z̃_t = ∫ e^{ψ^t} dG`, `d/dt log Z̃_t = E_{q^t} ∂_tψ`, applied
to the tilted inequality `d3_tilted_inequality_proof`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

/-- Differentiation under the integral sign (as inside `d3a_ftc`). -/
theorem d3b_hasDerivAt_param {τ : ℝ} {ν : Measure (Torus n)} [IsFiniteMeasure ν] {F D : ℝ → Torus n → ℝ}
    (hF : Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n => F p.1 p.2)
    (hD : Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n => D p.1 p.2)
    (hder : ∀ x : Torus n, ∀ r ∈ Set.Ioo 0 τ, HasDerivAt (fun s => F s x) (D r x) r) :
    ∀ s ∈ Set.Ioo 0 τ, HasDerivAt (fun s => ∫ x, F s x ∂ν) (∫ x, D s x ∂ν) s := by
  obtain ⟨C, hC⟩ := d3a_bound hD
  intro s hs
  have hsI : s ∈ Set.Icc 0 τ := ⟨hs.1.le, hs.2.le⟩
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun s' x => F s' x) (F' := fun s' x => D s' x)
    (x₀ := s) (s := Set.Ioo 0 τ) (bound := fun _ => C)
    (Ioo_mem_nhds hs.1 hs.2) ?_ ?_ ?_ ?_ (integrable_const _) ?_).2
  · exact Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) fun s' hs' =>
      (d3a_contOn_space hF ⟨hs'.1.le, hs'.2.le⟩).aestronglyMeasurable
  · exact d3a_hint ν (d3a_contOn_space hF hsI)
  · exact (d3a_contOn_space hD hsI).aestronglyMeasurable
  · exact ae_of_all _ fun a s' hs' => hC s' ⟨hs'.1.le, hs'.2.le⟩ a
  · exact ae_of_all _ fun a s' hs' => hder a s' hs'

/-- `log ∫ e^{ψ_t} dP` is `C¹` with derivative `∫ ψt e^ψ / ∫ e^ψ`. -/
theorem d3b_logZ {T : ℝ} (hT : 0 < T) {P : Measure (Torus n)} [IsProbabilityMeasure P]
    {ψ ψt : ℝ → Torus n → ℝ} (hψ : IsC12Test T ψ ψt) :
    ContinuousOn (fun r => (∫ x, ψt r x * Real.exp (ψ r x) ∂P) / ∫ x, Real.exp (ψ r x) ∂P)
      (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T, Real.log (∫ x, Real.exp (ψ t x) ∂P) -
        Real.log (∫ x, Real.exp (ψ 0 x) ∂P) =
      ∫ r in Set.Icc (0 : ℝ) t, (∫ x, ψt r x * Real.exp (ψ r x) ∂P) / ∫ x, Real.exp (ψ r x) ∂P := by
  have hF : Continuous fun p : Set.Icc (0 : ℝ) T × Torus n => Real.exp (ψ p.1 p.2) :=
    Real.continuous_exp.comp hψ.continuous_f
  have hD : Continuous fun p : Set.Icc (0 : ℝ) T × Torus n => ψt p.1 p.2 * Real.exp (ψ p.1 p.2) :=
    hψ.cont_time_deriv.mul hF
  have Zc := d3a_continuousOn_integral (ν := P) (H := fun r x => Real.exp (ψ r x)) hF
  have Dc := d3a_continuousOn_integral (ν := P) (H := fun r x => ψt r x * Real.exp (ψ r x)) hD
  have Zpos : ∀ r ∈ Set.Icc (0 : ℝ) T, 0 < ∫ x, Real.exp (ψ r x) ∂P := fun r hr =>
    integral_exp_pos (d3a_hint P (d3a_contOn_space (F := fun r x => Real.exp (ψ r x)) hF hr))
  have hcont : ContinuousOn (fun r => (∫ x, ψt r x * Real.exp (ψ r x) ∂P) / ∫ x, Real.exp (ψ r x) ∂P)
      (Set.Icc 0 T) := Dc.div Zc fun r hr => (Zpos r hr).ne'
  refine ⟨hcont, fun t ht => ?_⟩
  rcases ht.1.eq_or_lt with rfl | htpos
  · simp
  have hmem : ∀ r ∈ Set.Icc (0 : ℝ) t, r ∈ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hder := d3b_hasDerivAt_param (ν := P) (τ := T) (F := fun r x => Real.exp (ψ r x))
    (D := fun r x => ψt r x * Real.exp (ψ r x)) hF hD (fun x r hr =>
      (hψ.time_deriv x r hr).exp.congr_deriv (mul_comm _ _))
  have hderlog : ∀ r ∈ Set.Ioo (0 : ℝ) t, HasDerivAt (fun s => Real.log (∫ x, Real.exp (ψ s x) ∂P))
      ((∫ x, ψt r x * Real.exp (ψ r x) ∂P) / ∫ x, Real.exp (ψ r x) ∂P) r := fun r hr =>
    (hder r ⟨hr.1, lt_of_lt_of_le hr.2 ht.2⟩).log (Zpos r (hmem r (Set.Ioo_subset_Icc_self hr))).ne'
  have hlogc : ContinuousOn (fun r => Real.log (∫ x, Real.exp (ψ r x) ∂P)) (Set.Icc 0 t) :=
    (Zc.mono (Set.Icc_subset_Icc_right ht.2)).log fun r hr => (Zpos r (hmem r hr)).ne'
  have hint : IntervalIntegrable
      (fun r => (∫ x, ψt r x * Real.exp (ψ r x) ∂P) / ∫ x, Real.exp (ψ r x) ∂P) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le htpos.le]
    exact hcont.mono (Set.Icc_subset_Icc_right ht.2)
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le htpos.le hlogc hderlog hint
  rw [intervalIntegral.integral_of_le htpos.le, ← integral_Icc_eq_integral_Ioc] at this
  linarith

/-- **Entropy relative to the moving reference** (statement of `d3_entropy_moving`). -/
theorem d3b_moving_main (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {T : ℝ} (hT : 0 < T) {μ : ℝ → Measure (Torus n)}
    (hμ : D1WeakSolution κ (d1_gradDrift U) T μ) [IsProbabilityMeasure (μ 0)]
    {ψ ψt : ℝ → Torus n → ℝ} (hψ : IsC12Test T ψ ψt)
    (hfin : relEntropy (μ 0) (d1_gibbsMeasure κ (d3_tiltPot κ U (ψ 0))) ≠ ⊤) :
    ∀ t ∈ Set.Icc 0 T,
      relEntropy (μ t) (d1_gibbsMeasure κ (d3_tiltPot κ U (ψ t))) ≠ ⊤ ∧
      ∫⁻ r in Set.Icc 0 t, d1_fisherInfo κ (d3_tiltPot κ U (ψ r)) (μ r) < ⊤ ∧
      (relEntropy (μ t) (d1_gibbsMeasure κ (d3_tiltPot κ U (ψ t)))).toReal
        + κ * (∫⁻ r in Set.Icc 0 t, d1_fisherInfo κ (d3_tiltPot κ U (ψ r)) (μ r)).toReal
      ≤ (relEntropy (μ 0) (d1_gibbsMeasure κ (d3_tiltPot κ U (ψ 0)))).toReal
        + ∫ r in Set.Icc 0 t, ∫ x, (d3_source κ U ψ ψt r x
            + ∫ y, ψt r y ∂(d1_gibbsMeasure κ (d3_tiltPot κ U (ψ r)))) ∂(μ r) := by
  haveI hP := d3a_gibbs_isProb (κ := κ) hU
  have hψc : ∀ r ∈ Set.Icc (0 : ℝ) T, Continuous (ψ r) := fun r hr =>
    d3a_continuous_of_ck1 (d3a_ck2_ck1 (hψ.c2 r hr))
  have h0T : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hq : ∀ r ∈ Set.Icc (0 : ℝ) T, d1_gibbsMeasure κ (d3_tiltPot κ U (ψ r)) =
      (d1_gibbsMeasure κ U).tilted (ψ r) := fun r hr => d3b_tilt_eq hκ hU (hψc r hr)
  have hprob : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (μ r) := fun r hr =>
    d1_isProbabilityMeasure hμ hr
  have hfinP : relEntropy (μ 0) (d1_gibbsMeasure κ U) ≠ ⊤ := by
    rw [hq 0 h0T] at hfin
    exact (d3b_klDiv_tilted_iff (hψc 0 h0T)).1 hfin
  obtain ⟨hlogc, hlogZ⟩ := d3b_logZ hT (P := d1_gibbsMeasure κ U) hψ
  have hE : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫ y, ψt r y ∂(d1_gibbsMeasure κ (d3_tiltPot κ U (ψ r))) =
      (∫ x, ψt r x * Real.exp (ψ r x) ∂(d1_gibbsMeasure κ U)) /
        ∫ x, Real.exp (ψ r x) ∂(d1_gibbsMeasure κ U) := by
    intro r hr
    rw [hq r hr, integral_tilted]
    simp only [smul_eq_mul]
    rw [← integral_div]
    congr 1
    funext x
    ring
  have hsc := d3b_source_cont (κ := κ) hU hψ
  have hSc : ContinuousOn (fun r => ∫ x, d3_source κ U ψ ψt r x ∂(μ r)) (Set.Icc 0 T) :=
    d3b_contOn_param hprob hμ.narrow hsc
  intro t ht
  have hTI : ∀ r ∈ Set.Icc (0 : ℝ) t, r ∈ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  obtain ⟨hA, hB, hC⟩ := d3b_tilted_main hn hκ hU hT hμ hfinP hψ t ht
  haveI := hprob t ht
  have hHt := d3b_klDiv_tilted_fwd (P := d1_gibbsMeasure κ U) (hψc t ht) hA
  have hH0 := d3b_klDiv_tilted_fwd (P := d1_gibbsMeasure κ U) (hψc 0 h0T) hfinP
  refine ⟨by rw [hq t ht]; exact hHt.1, hB, ?_⟩
  have hinner : ∀ r ∈ Set.Icc (0 : ℝ) t,
      ∫ x, (d3_source κ U ψ ψt r x + ∫ y, ψt r y ∂(d1_gibbsMeasure κ (d3_tiltPot κ U (ψ r)))) ∂(μ r) =
      (∫ x, d3_source κ U ψ ψt r x ∂(μ r)) +
        (∫ x, ψt r x * Real.exp (ψ r x) ∂(d1_gibbsMeasure κ U)) /
          ∫ x, Real.exp (ψ r x) ∂(d1_gibbsMeasure κ U) := by
    intro r hr
    have hrT := hTI r hr
    haveI := hprob r hrT
    rw [integral_add (d3a_hint _ (d3a_contOn_space hsc hrT)) (integrable_const _), integral_const,
      hE r hrT]
    simp
  rw [setIntegral_congr_fun measurableSet_Icc hinner]
  have hSi : IntegrableOn (fun r => ∫ x, d3_source κ U ψ ψt r x ∂(μ r)) (Set.Icc 0 t) :=
    (hSc.mono (Set.Icc_subset_Icc_right ht.2)).integrableOn_Icc
  have hEi : IntegrableOn (fun r => (∫ x, ψt r x * Real.exp (ψ r x) ∂(d1_gibbsMeasure κ U)) /
      ∫ x, Real.exp (ψ r x) ∂(d1_gibbsMeasure κ U)) (Set.Icc 0 t) :=
    (hlogc.mono (Set.Icc_subset_Icc_right ht.2)).integrableOn_Icc
  rw [integral_add hSi hEi, ← hlogZ t ht, hq t ht, hq 0 h0T, hHt.2, hH0.2]
  linarith

end HRS
