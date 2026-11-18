import HRS.Main.T25PAux1

/-!
# T25P, part 2: the evolution package at level `m` (dual uniqueness, uniqueness of convolutions, `MaxWindowsM`)

`HRS.Uniform.MaxWindows` (the hypothesis of `comparison_wasserstein`) quantifies over ALL `Z` with `IsStochConv` (a lower-integral
predicate) and a.s. continuous paths, without measurability; it is not satisfiable for a nontrivial `H` (a Bernstein-type set `A`
gives `Z'_t = v φ_A(t) 1_A + v φ_{A^c}(t) 1_{A^c}` with disjoint bumps `φ`, for the zero martingale).  The statement used in T25
(`MaxWindowsM`) adds `∀ t, Measurable (Z t)`; it follows from the existence part of `adjk_evolution_moment_proof` (B1, `p = 2`),
the uniqueness `IsStochConv` for measurable data, and the density of the rationals.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.AdjK

variable {d : ℕ}

/-! ### Dual evolutions are unique -/

theorem t25p_dual_unique {D : DynData d} {ρ : ℝ → Torus d → ℝ} {m : ℝ}
    {V₁ V₂ : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (h₁ : IsDualEvolution D ρ m V₁)
    (h₂ : IsDualEvolution D ρ m V₂) {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) : V₁ t u = V₂ t u := by
  refine ContinuousLinearMap.ext fun z => ?_
  refine HRS.Uniform.Q54.eq_of_eval_smooth fun φ hφ => ?_
  rw [h₁ u t hu hut z φ hφ, h₂ u t hu hut z φ hφ]

/-! ### Shift of the start point of a stochastic convolution -/

theorem t25p_isStochConv_shift {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (VE : ℝ → ℝ → E →L[ℝ] E) (j : H →L[ℝ] E) {M : ℝ → Ω → H} {a t : ℝ} {Z : Ω → E}
    (h : IsStochConv P VE j M a t Z) :
    IsStochConv P (fun t' r => VE (a + t') (a + r)) j (fun s ω => M (a + s) ω) 0 (t - a) Z := by
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := h ε hε
  refine ⟨δ, hδ, fun n r h0 hl hmono hmesh => ?_⟩
  have key := hh n (fun i => a + r i) (by simp [h0]) (by simp [hl]) (fun i j hij => by
    simpa using hmono hij) (fun i => by simpa using hmesh i)
  have e : ∀ ω, riemannSum (fun t' r => VE (a + t') (a + r)) j (fun s ω => M (a + s) ω) (t - a) r ω =
      riemannSum VE j M t (fun i => a + r i) ω := by
    intro ω
    unfold riemannSum
    simp [add_sub_cancel]
  simp_rw [e]
  exact key

/-- Uniqueness (a.e.) of the stochastic convolution started at `a`, for measurable data. -/
theorem t25p_stochConv_unique {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology E]
    [SecondCountableTopology H] (VE : ℝ → ℝ → E →L[ℝ] E) (j : H →L[ℝ] E) {M : ℝ → Ω → H}
    (hMm : ∀ t, Measurable (M t)) {a t : ℝ} (hat : a ≤ t) {Z₁ Z₂ : Ω → E}
    (hZ₁m : AEMeasurable Z₁ P) (hZ₂m : AEMeasurable Z₂ P) (hZ₁ : IsStochConv P VE j M a t Z₁)
    (hZ₂ : IsStochConv P VE j M a t Z₂) : Z₁ =ᵐ[P] Z₂ :=
  gfb4_isStochConv_unique P (fun t' r => VE (a + t') (a + r)) j (M := fun s ω => M (a + s) ω)
    (fun s => hMm (a + s)) (T := t - a) (t := t - a) (sub_nonneg.2 hat) (sub_nonneg.2 hat) le_rfl hZ₁m hZ₂m
    (t25p_isStochConv_shift VE j hZ₁) (t25p_isStochConv_shift VE j hZ₂)

/-! ### Density of the rationals in a window -/

theorem t25p_Icc_subset_closure_rat {a b : ℝ} (hab : a < b) : Set.Icc a b ⊆ closure (ratIcc a b) := by
  rw [← closure_Ioo hab.ne]
  refine closure_minimal ?_ isClosed_closure
  intro x hx
  have h1 := (Rat.denseRange_cast (𝕜 := ℝ)).open_subset_closure_inter isOpen_Ioo hx
  refine closure_mono ?_ h1
  rintro y ⟨hy1, ⟨q, hq'⟩⟩
  exact ⟨⟨hy1.1.le, hy1.2.le⟩, ⟨q, hq'⟩⟩

theorem t25p_ae_forall_Icc {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) {E : Type*}
    [TopologicalSpace E] [T2Space E] {a b : ℝ} (hab : a < b) (X Y : ℝ → Ω → E)
    (hX : ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc a b))
    (hY : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc a b))
    (h : ∀ t ∈ Set.Icc a b, X t =ᵐ[P] Y t) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc a b, X t ω = Y t ω := by
  have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, (q : ℝ) ∈ Set.Icc a b → X (q : ℝ) ω = Y (q : ℝ) ω := by
    refine ae_all_iff.2 fun q => ?_
    by_cases hqm : (q : ℝ) ∈ Set.Icc a b
    · filter_upwards [h _ hqm] with ω hω _ using hω
    · exact Filter.Eventually.of_forall fun ω hh => absurd hh hqm
  filter_upwards [hX, hY, hq] with ω hx hy hq t ht
  have hsub : ratIcc a b ⊆ Set.Icc a b := fun x hx => hx.1
  have heq : Set.EqOn (fun t => X t ω) (fun t => Y t ω) (ratIcc a b) := by
    rintro x ⟨hx, q, rfl⟩
    exact hq q hx
  exact Set.EqOn.of_subset_closure heq hx hy hsub (t25p_Icc_subset_closure_rat hab) ht

/-! ### `MaxWindowsM` -/

section MaxM

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The one-space maximal estimate for the evolution `V`, uniformly on windows, for MEASURABLE continuous convolutions
(sample spaces in `Type`). -/
def MaxWindowsM (V : ℝ → ℝ → H →L[ℝ] H) (T Cmax : ℝ) : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (a : ℝ), 0 ≤ a →
    ∀ (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)),
      IsHilbertMartingaleWithCovariation P ℱ (a + T) M Sg →
      ∀ Z : ℝ → Ω → H, (∀ t ∈ Set.Icc a (a + T), IsStochConv P V (ContinuousLinearMap.id ℝ H) M a t (Z t)) →
        (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc a (a + T))) → (∀ t, Measurable (Z t)) →
        ∫⁻ ω, (⨆ t ∈ Set.Icc a (a + T), ‖Z t ω‖ₑ) ^ 2 ∂P ≤
          ENNReal.ofReal Cmax *
            ∫⁻ ω, (∫⁻ r in Set.Icc a (a + T), ENNReal.ofReal (traceNormForm (Sg r ω))) ∂P

theorem t25p_maxWindowsM_of_B1 {m T C : ℝ} (hT : 0 < T)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hC : 0 ≤ C)
    (hB1 : ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (a h : ℝ), 0 ≤ a → 0 < h → h ≤ T →
      ∀ (M : ℝ → Ω → NegSobolev d m)
        (Sg : ℝ → Ω → (NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ)),
        IsHilbertMartingaleWithCovariation P ℱ (a + h) M Sg →
        ∃ Z : ℝ → Ω → NegSobolev d m,
          (∀ t ∈ Set.Icc a (a + h),
            IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) M a t (Z t)) ∧
          (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc a (a + h))) ∧
          (∀ t ∈ Set.Icc a (a + h), AEMeasurable (Z t) P) ∧
          ∫⁻ ω, (⨆ t ∈ Set.Icc a (a + h), ‖Z t ω‖ₑ) ^ (2 : ℝ) ∂P ≤
            ENNReal.ofReal C * ∫⁻ ω,
              (∫⁻ u in Set.Icc a (a + h), ENNReal.ofReal (traceNormForm (Sg u ω))) ^ ((2 : ℝ) / 2) ∂P) :
    MaxWindowsM Vev T C := by
  intro Ω mΩ P _ ℱ a ha M Sg hM Z' hZ'S hZ'c hZ'm
  obtain ⟨Z, hZS, hZc, hZm, hbd⟩ := hB1 Ω P ℱ a T ha hT le_rfl M Sg hM
  have hMm : ∀ t, Measurable (M t) := fun t => HRS.Uniform.Q07c.measurable_of_isHM hM t
  have hat : ∀ t ∈ Set.Icc a (a + T), Z' t =ᵐ[P] Z t := fun t ht =>
    t25p_stochConv_unique P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) hMm ht.1
      (hZ'm t).aemeasurable (hZm t ht) (hZ'S t ht) (hZS t ht)
  have hall := t25p_ae_forall_Icc P (a := a) (b := a + T) (by linarith) Z' Z hZ'c hZc hat
  have hlhs : ∫⁻ ω, (⨆ t ∈ Set.Icc a (a + T), ‖Z' t ω‖ₑ) ^ 2 ∂P =
      ∫⁻ ω, (⨆ t ∈ Set.Icc a (a + T), ‖Z t ω‖ₑ) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hall] with ω hω
    congr 1
    refine iSup_congr fun t => iSup_congr fun ht => ?_
    rw [hω t ht]
  rw [hlhs]
  have h2 : (2 : ℝ) / 2 = 1 := by norm_num
  simp only [ENNReal.rpow_two, h2, ENNReal.rpow_one] at hbd
  exact hbd

end MaxM

end HRS.T25P
