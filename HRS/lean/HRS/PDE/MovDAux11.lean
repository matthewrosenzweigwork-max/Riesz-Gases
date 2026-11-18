import HRS.PDE.MovDAux10
import HRS.PDE.MovDAux7
import HRS.PDE.MovCFinal

/-!
# MOVD Aux11: `movT_source_limit_bdd`

Instantiation of `movd_limit_bdd_abstract`.  Depends on the sorried MovSpec1 packet `movT_srcReg_tendsto` (pointwise
convergence of the regularised sources off collisions, MOVC); everything else is proved.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

theorem movd_source_limit_bdd_gen {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} {M : ℕ → ℝ}
    {Y₀ : Ω → Fin N → Euc d} {Y : ℕ → ℝ → Ω → (Fin N → Euc d)}
    (hN : 2 ≤ N) (htr : MovTraj D T ρ) (hρt : IsC12Test T ρ ρt) (hS : IsStrongSolution P D T X₀ W X)
    (seq : MovRegSeq P ℱ W' D T X₀ W X M Y₀ Y)
    (hexp : ∃ l C : ℝ, 0 < l ∧ ∀ᶠ n in atTop, ∀ r ∈ Set.Icc 0 T,
      ∫⁻ Z : Config d N, ENNReal.ofReal (Real.exp (l * |movT_srcReg D N (M n) ρ ρt r Z|))
        ∂(movT_Q (b15c_gReg d D.s (M n)) D N ρ r) ≤ ENNReal.ofReal (Real.exp C))
    (hLq : ∃ q C : ℝ, 1 < q ∧ ∀ᶠ n in atTop, ∀ r ∈ Set.Icc 0 T,
      selectedLaw P (b15c_regProcess (Y n)) r ≪ movT_Q (b15c_gReg d D.s (M n)) D N ρ r ∧
      eLpNorm ((selectedLaw P (b15c_regProcess (Y n)) r).rnDeriv
          (movT_Q (b15c_gReg d D.s (M n)) D N ρ r)) (ENNReal.ofReal q)
        (movT_Q (b15c_gReg d D.s (M n)) D N ρ r) ≤ ENNReal.ofReal C)
    (hconvT : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ Z : Config d N, Z ∉ collisionSet d N →
      Tendsto (fun n => movT_srcReg D N (M n) ρ ρt r Z) atTop (𝓝 (movT_source D N ρ r Z))) :
    (∀ r ∈ Set.Icc 0 T, Integrable (movT_source D N ρ r) (P.map (X r.toNNReal))) ∧
    IntegrableOn (fun r => ∫ Z, movT_source D N ρ r Z ∂(P.map (X r.toNNReal))) (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc 0 T,
      Tendsto (fun n => ∫ r in Set.Icc 0 t, ∫ Z, movT_srcReg D N (M n) ρ ρt r Z
        ∂(selectedLaw P (b15c_regProcess (Y n)) r)) atTop
        (𝓝 (∫ r in Set.Icc 0 t, ∫ Z, movT_source D N ρ r Z ∂(P.map (X r.toNNReal)))) := by
  by_cases hT : 0 ≤ T
  swap
  · have hE : Set.Icc (0 : ℝ) T = ∅ := Set.Icc_eq_empty (by simpa using hT)
    refine ⟨fun r hr => absurd (hr.1.trans hr.2) hT, ?_, fun t ht => absurd (ht.1.trans ht.2) hT⟩
    rw [hE]; exact integrableOn_empty
  have hN' : 0 < N := by omega
  have hXm : ∀ t, Measurable (X t) := hS.adapted
  have hcont : ∀ n : ℕ, Continuous fun p : Set.Icc (0 : ℝ) T × Config d N =>
      movT_srcReg D N (M n) ρ ρt p.1 p.2 := fun n =>
    movb_srcReg_cont hN' D htr.gradient htr.pos_temp htr.V_reg (M n) hρt htr.mf.density htr.pos
  have hSm : ∀ n, ∀ r ∈ Set.Icc (0 : ℝ) T, Measurable (movT_srcReg D N (M n) ρ ρt r) := by
    intro n r hr
    have h1 : Continuous fun Z : Config d N => ((⟨r, hr⟩ : Set.Icc (0 : ℝ) T), Z) :=
      continuous_const.prodMk continuous_id
    have h2 := (hcont n).comp' h1
    dsimp only at h2
    exact h2.measurable
  have hcoll : MeasurableSet (collisionSet d N) := (isClosed_collisionSet d N).measurableSet
  -- a.e. convergence along the regularisation
  have hconv : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ Z : Config d N, Z ∉ collisionSet d N →
      Tendsto (fun n => movT_srcReg D N (M n) ρ ρt r Z) atTop (𝓝 (movT_source D N ρ r Z)) :=
    hconvT
  have hR : ∀ r ∈ Set.Icc (0 : ℝ) T, AEStronglyMeasurable (movT_source D N ρ r)
      (P.map (X r.toNNReal)) := by
    intro r hr
    have h0 : P.map (X r.toNNReal) (collisionSet d N) = 0 := by
      rw [Measure.map_apply (hXm _) hcoll]
      refine measure_eq_zero_iff_ae_notMem.2 ?_
      filter_upwards [hS.no_collision] with ω hω
      exact hω r.toNNReal (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2)
    have hnc : ∀ᵐ Z ∂(P.map (X r.toNNReal)), Z ∉ collisionSet d N := measure_eq_zero_iff_ae_notMem.1 h0
    refine (aemeasurable_of_tendsto_metrizable_ae atTop
      (fun n => (hSm n r hr).aemeasurable) ?_).aestronglyMeasurable
    filter_upwards [hnc] with Z hZ using hconv r hr Z hZ
  have hpt : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      Tendsto (fun n => movT_srcReg D N (M n) ρ ρt r (b15c_regProcess (Y n) r.toNNReal ω)) atTop
        (𝓝 (movT_source D N ρ r (X r.toNNReal ω))) := by
    intro r hr
    filter_upwards [seq.eventually_eq, hS.no_collision] with ω h1 h2
    have hrT : ((r.toNNReal : ℝ≥0) : ℝ) ≤ T := by rw [Real.coe_toNNReal _ hr.1]; exact hr.2
    have h3 := hconv r hr (X r.toNNReal ω) (h2 r.toNNReal hrT)
    refine h3.congr' ?_
    filter_upwards [h1] with n hn
    rw [hn r.toNNReal hrT]
  have hGc : ∀ n, ContinuousOn (fun r => ∫ z, movT_srcReg D N (M n) ρ ρt r z
      ∂(P.map (b15c_regProcess (Y n) r.toNNReal))) (Set.Icc 0 T) := by
    intro n
    have h := movb_cont_integral (seq.sol n) hT (S := fun r Z => movT_srcReg D N (M n) ρ ρt r Z)
      (hcont n)
    exact continuousOn_iff_continuous_domRestrict.2 h
  exact movd_limit_bdd_abstract (P := P) (T := T)
    (Zn := fun n r ω => b15c_regProcess (Y n) r.toNNReal ω) (Z := fun r ω => X r.toNNReal ω)
    (fun n r => b15c_regProcess_measurable (seq.sol n) _) (fun r => hXm _)
    (Qn := fun n r => movT_Q (b15c_gReg d D.s (M n)) D N ρ r)
    (fun n r hr => by
      have := movT_QReg_isProb (N := N) D htr (M n) hr
      infer_instance)
    (Sn := fun n r => movT_srcReg D N (M n) ρ ρt r) (R := movT_source D N ρ) hSm hR hpt hGc hexp hLq

/-- `movd_source_limit_bdd` for all `T`: for `0 < T` the convergence is `movT_srcReg_tendsto`; for `T = 0` (where that
packet is false for an arbitrary `ρt`) the mean-field test function of `movrepair_good_test` is used, and the `ρt`-dependent
third conclusion is trivial (`Icc 0 0` is Lebesgue-null). -/
theorem movd_source_limit_bdd {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} {M : ℕ → ℝ}
    {Y₀ : Ω → Fin N → Euc d} {Y : ℕ → ℝ → Ω → (Fin N → Euc d)}
    (hN : 2 ≤ N) (htr : MovTraj D T ρ) (hρt : IsC12Test T ρ ρt) (hS : IsStrongSolution P D T X₀ W X)
    (seq : MovRegSeq P ℱ W' D T X₀ W X M Y₀ Y)
    (hexp : ∃ l C : ℝ, 0 < l ∧ ∀ᶠ n in atTop, ∀ r ∈ Set.Icc 0 T,
      ∫⁻ Z : Config d N, ENNReal.ofReal (Real.exp (l * |movT_srcReg D N (M n) ρ ρt r Z|))
        ∂(movT_Q (b15c_gReg d D.s (M n)) D N ρ r) ≤ ENNReal.ofReal (Real.exp C))
    (hLq : ∃ q C : ℝ, 1 < q ∧ ∀ᶠ n in atTop, ∀ r ∈ Set.Icc 0 T,
      selectedLaw P (b15c_regProcess (Y n)) r ≪ movT_Q (b15c_gReg d D.s (M n)) D N ρ r ∧
      eLpNorm ((selectedLaw P (b15c_regProcess (Y n)) r).rnDeriv
          (movT_Q (b15c_gReg d D.s (M n)) D N ρ r)) (ENNReal.ofReal q)
        (movT_Q (b15c_gReg d D.s (M n)) D N ρ r) ≤ ENNReal.ofReal C) :
    (∀ r ∈ Set.Icc 0 T, Integrable (movT_source D N ρ r) (P.map (X r.toNNReal))) ∧
    IntegrableOn (fun r => ∫ Z, movT_source D N ρ r Z ∂(P.map (X r.toNNReal))) (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc 0 T,
      Tendsto (fun n => ∫ r in Set.Icc 0 t, ∫ Z, movT_srcReg D N (M n) ρ ρt r Z
        ∂(selectedLaw P (b15c_regProcess (Y n)) r)) atTop
        (𝓝 (∫ r in Set.Icc 0 t, ∫ Z, movT_source D N ρ r Z ∂(P.map (X r.toNNReal)))) := by
  rcases lt_trichotomy 0 T with hT | hT | hT
  · exact movd_source_limit_bdd_gen hN htr hρt hS seq hexp hLq
      (fun r hr Z hZ => movT_srcReg_tendsto_proof_pos hN htr hρt hT seq.levels hr hZ)
  · subst hT
    obtain ⟨ρt', hρt', hgood⟩ := movrepair_good_test (N := N) hN htr
    obtain ⟨l, C, M₀, hl, hb⟩ := movT_source_exp_uniform_proof' hN htr hρt'
    have hexp' : ∃ l C : ℝ, 0 < l ∧ ∀ᶠ n in atTop, ∀ r ∈ Set.Icc (0 : ℝ) 0,
        ∫⁻ Z : Config d N, ENNReal.ofReal (Real.exp (l * |movT_srcReg D N (M n) ρ ρt' r Z|))
          ∂(movT_Q (b15c_gReg d D.s (M n)) D N ρ r) ≤ ENNReal.ofReal (Real.exp C) :=
      ⟨l, C, hl, (seq.levels.eventually_ge_atTop M₀).mono fun n hn r hr => hb (M n) hn r hr⟩
    obtain ⟨h1, h2, -⟩ := movd_source_limit_bdd_gen hN htr hρt' hS seq hexp' hLq
      (fun r hr Z hZ => hgood seq.levels hr hZ)
    refine ⟨h1, h2, fun t ht => ?_⟩
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst ht0
    have hz : (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 0) = 0 := by
      rw [Set.Icc_self]; exact Measure.restrict_eq_zero.2 Real.volume_singleton
    simp only [hz, integral_zero_measure]
    exact tendsto_const_nhds
  · have hE : Set.Icc (0 : ℝ) T = ∅ := Set.Icc_eq_empty (not_le.2 hT)
    refine ⟨fun r hr => absurd (hr.1.trans hr.2) (not_le.2 hT), ?_,
      fun t ht => absurd (ht.1.trans ht.2) (not_le.2 hT)⟩
    rw [hE]; exact integrableOn_empty

end HRS

end
