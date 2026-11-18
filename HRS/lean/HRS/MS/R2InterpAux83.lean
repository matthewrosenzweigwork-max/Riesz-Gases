import HRS.MS.R2InterpAux82

/-!
# S10.2 (worker S10R), part 83 (packet F5c): space-time integrability of the pair energy along the particle path

For a jointly measurable family of bounded pair kernels `h_r` (uniform bound `B`, `r ∈ [0,T]`) and the particle path `X`, whose time marginals have `HasR2ActualDensity`,
`(r,ζ) ↦ N F_N^{h_r}(X_r ζ)` and its centering `r2QuadFluct` are integrable on `[0,T] × Ω`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ}

theorem s102_prodInt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P] {T C : ℝ}
    {f : ℝ × Ω → ℝ} (hf : Measurable f) (hb : ∀ r ∈ Icc (0 : ℝ) T, ∫⁻ ζ, ‖f (r, ζ)‖ₑ ∂P ≤ ENNReal.ofReal C) :
    Integrable f ((volume.restrict (Icc (0 : ℝ) T)).prod P) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hf.enorm.aemeasurable]
  calc ∫⁻ r, ∫⁻ ζ, ‖f (r, ζ)‖ₑ ∂P ∂(volume.restrict (Icc (0 : ℝ) T))
      ≤ ∫⁻ r in Icc (0 : ℝ) T, ENNReal.ofReal C := by
        refine setLIntegral_mono' measurableSet_Icc fun r hr => hb r hr
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp)

theorem s102_lint_map {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω} {Y : Ω → α}
    (hY : Measurable Y) {g : α → ℝ} (hg : Measurable g) (hi : Integrable g (P.map Y)) {C : ℝ}
    (hb : ∫ x, ‖g x‖ ∂(P.map Y) ≤ C) : ∫⁻ ζ, ‖g (Y ζ)‖ₑ ∂P ≤ ENNReal.ofReal C := by
  rw [← lintegral_map hg.enorm hY, ← ofReal_integral_norm_eq_lintegral_enorm hi]
  exact ENNReal.ofReal_le_ofReal hb

theorem s102_ae_mem_prod {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P] (T : ℝ) :
    ∀ᵐ q ∂((volume.restrict (Icc (0 : ℝ) T)).prod P), q.1 ∈ Icc (0 : ℝ) T :=
  (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Icc (0 : ℝ) T)) (ν := P)).ae
    (ae_restrict_mem measurableSet_Icc)

/-- Space-time integrability from fibrewise `L¹` bounds along the time marginals. -/
theorem s102_prodInt_family {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω} [SFinite P]
    {T C : ℝ} {Y : ℝ → Ω → α} (hY : Measurable fun q : ℝ × Ω => Y q.1 q.2) (g : ℝ → α → ℝ)
    (hg : Measurable fun q : ℝ × α => g q.1 q.2)
    (hb : ∀ r ∈ Icc (0 : ℝ) T, Measurable (Y r) ∧ Integrable (g r) (P.map (Y r)) ∧
      ∫ x, ‖g r x‖ ∂(P.map (Y r)) ≤ C) :
    Integrable (fun q : ℝ × Ω => g q.1 (Y q.1 q.2)) ((volume.restrict (Icc (0 : ℝ) T)).prod P) := by
  have hm : Measurable fun q : ℝ × Ω => g q.1 (Y q.1 q.2) :=
    hg.comp (measurable_fst.prodMk hY)
  refine s102_prodInt (C := C) hm fun r hr => ?_
  obtain ⟨h1, h2, h3⟩ := hb r hr
  exact s102_lint_map h1 (hg.comp (measurable_const.prodMk measurable_id)) h2 h3

/-- Uniform `L¹` bound of the pair energy and its centering along the time marginals, as a space-time integrability statement. -/
theorem s102_quad_prodInt (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M L β p K B : ℝ) (hβ : 0 < β)
    (hp : 1 < p) {ρ : Euc d → ℝ} (hρ : IsRound2Density d s M L ρ) {N : ℕ} (hN : 2 ≤ N) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → EucConfig d N) (T : ℝ)
    (hXm : Measurable fun q : ℝ × Ω => X (min q.1 T).toNNReal q.2)
    (hdens : ∀ r ∈ Icc (0 : ℝ) T, HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ) (P.map (X r.toNNReal)))
    (hK : ℝ → Euc d → Euc d → ℝ) (hKm : Measurable fun q : ℝ × Euc d × Euc d => hK q.1 q.2.1 q.2.2)
    (hKb : ∀ r ∈ Icc (0 : ℝ) T, IsBoundedPairKernel s B (hK r)) :
    Integrable (fun q : ℝ × Ω => (N : ℝ) * pairEnergy (hK q.1) (X q.1.toNNReal q.2) (HRS.Whole.withDensityReal ρ))
      ((volume.restrict (Icc (0 : ℝ) T)).prod P) ∧
    Integrable (fun q : ℝ × Ω => r2QuadFluct (HRS.Whole.withDensityReal ρ) hK P X q.1 q.2)
      ((volume.restrict (Icc (0 : ℝ) T)).prod P) := by
  haveI := HRS.MS.R2Mt.s92_isProb_mu hρ.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  obtain ⟨C, hC0, hC⟩ := s102_comm_L1 hd hs0 hs M L β p K B hβ hp
  have hpE : Measurable fun q : ℝ × EucConfig d N => pairEnergy (hK q.1) q.2 μ :=
    HRS.MS.R2Chaos.s94_pairEnergy_measurable hKm
  have hYr : ∀ r ∈ Icc (0 : ℝ) T, (fun ζ => X (min r T).toNNReal ζ) = X r.toNNReal := fun r hr => by
    funext ζ; rw [min_eq_left hr.2]
  have hYm : ∀ r ∈ Icc (0 : ℝ) T, Measurable fun ζ => X (min r T).toNNReal ζ := fun r _ =>
    hXm.comp measurable_prodMk_left
  have hae := s102_ae_mem_prod (P := P) T
  constructor
  · have h := s102_prodInt_family (P := P) (T := T) (C := C) (Y := fun r ζ => X (min r T).toNNReal ζ) hXm
      (fun r Y => (N : ℝ) * pairEnergy (hK r) Y μ) (hpE.const_mul _) (fun r hr => by
        refine ⟨hYm r hr, ?_⟩
        rw [hYr r hr]
        obtain ⟨⟨hi, hb⟩, -⟩ := hC ρ hρ N hN _ (hdens r hr) (hK r) (hKb r hr)
        exact ⟨hi, hb⟩)
    refine h.congr ?_
    filter_upwards [hae] with q hq
    simp only [min_eq_left hq.2]
  · obtain ⟨c, hc⟩ : ∃ c : ℝ → ℝ, c = fun r => ∫ ζ', pairEnergy (hK r) (X (min r T).toNNReal ζ') μ ∂P := ⟨_, rfl⟩
    have hcm : Measurable c := by
      rw [hc]
      exact ((hpE.comp (measurable_fst.prodMk hXm)).stronglyMeasurable.integral_prod_right' (ν := P)).measurable
    have hgm : Measurable fun q : ℝ × EucConfig d N => (N : ℝ) * (pairEnergy (hK q.1) q.2 μ - c q.1) :=
      (hpE.sub (hcm.comp measurable_fst)).const_mul _
    have h := s102_prodInt_family (P := P) (T := T) (C := C) (Y := fun r ζ => X (min r T).toNNReal ζ) hXm
      (fun r Y => (N : ℝ) * (pairEnergy (hK r) Y μ - c r)) hgm (fun r hr => by
        have hpEr : Measurable fun Y : EucConfig d N => pairEnergy (hK r) Y μ :=
          Measurable.comp (g := fun q : ℝ × EucConfig d N => pairEnergy (hK q.1) q.2 μ) (f := fun Y => (r, Y)) hpE
            (measurable_const.prodMk measurable_id)
        have hmX : Measurable (X r.toNNReal) := by rw [← hYr r hr]; exact hYm r hr
        have key := (hC ρ hρ N hN (P.map (X r.toNNReal)) (hdens r hr) (hK r) (hKb r hr)).2
        have hcr : c r = ∫ Y, pairEnergy (hK r) Y μ ∂(P.map (X r.toNNReal)) := by
          rw [integral_map hmX.aemeasurable hpEr.aestronglyMeasurable, hc]
          simp only [min_eq_left hr.2]
        refine ⟨hYm r hr, ?_⟩
        have e : P.map (fun ζ => X (min r T).toNNReal ζ) = P.map (X r.toNNReal) := by rw [hYr r hr]
        show Integrable (fun Y => (N : ℝ) * (pairEnergy (hK r) Y μ - c r)) (P.map (fun ζ => X (min r T).toNNReal ζ)) ∧
          ∫ Y, ‖(N : ℝ) * (pairEnergy (hK r) Y μ - c r)‖ ∂(P.map (fun ζ => X (min r T).toNNReal ζ)) ≤ C
        rw [e, hcr]
        exact key)
    refine h.congr ?_
    filter_upwards [hae] with q hq
    rw [hc]; simp only [r2QuadFluct, min_eq_left hq.2]

end HRS.MS.R2Interp

end
