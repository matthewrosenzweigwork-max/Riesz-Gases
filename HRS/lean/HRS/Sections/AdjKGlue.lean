import HRS.Sections.AdjKSpec

/-!
# ADJK-SPEC glue: PROVED lemmas around the packet statements of `AdjKSpec.lean`

* `adjk_evolution_along_trajectory` (A3): Lemma 3.27 along an `IsSmoothPositiveTrajectory`.
* instances `SecondCountableTopology`, `CompleteSpace` for `PathSpace` (so it is Polish).
* `adjkEnergy_mono`, `adjkEnergy_lsc`, `adjkEnergy_measurable`; `adjk_supTail_of_moment` (Markov step: BCONV's sup bound gives the tail bound);
  `adjkLin` and `adjkLin_continuous`, `adjk_lin_along_trajectory` (the initial-data map `z ↦ V^{·,0}z`);
  `adjk_tight_of_tendstoInDistribution` (a convergent-in-law sequence is tight);
  `adjk_tight_add` (sum of tight families is tight); `adjk_tight_of_tail_bounds` (tightness in `C([0,T];E_m)` from the
  two probabilistic tail bounds, using the sorried `adjk_compactSet_isCompact`);
  `adjk_tight_of_components` (tightness of the laws of `Φ_n = Lin(η⁰_n) + Ξ_n` from `hlaw`, a continuous `Lin`, tail bounds on `Ξ_n`).
`#print axioms` of the last three lists `sorryAx` only through `adjk_compactSet_isCompact` (COMPACT).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-- **A3** (PROVED glue; TeX M L2531-2546 Lemma 3.27 along an `IsSmoothPositiveTrajectory`).  `Uniform.evolution_estimates_proof` for the
global `H^K` solution of `htr` (`K ≥ K₀(r)`), transported from `mfPath ρc` to `ρ` (`q40b_propagator_congr`): the dual evolution on `E_r`
exists, is strongly continuous, decays like `C_r e^{-c_r(t-u)}`, and has the maximal estimate for `∫V dM`.  Used by B1/BCONV/B2/C3. -/
theorem adjk_evolution_along_trajectory (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (r : ℝ) :
    ∃ Cr cr : ℝ, 0 < Cr ∧ 0 < cr ∧
      ∃ Vev : ℝ → ℝ → NegSobolev d r →L[ℝ] NegSobolev d r,
        IsDualEvolution htr.dyn ρ r Vev ∧
        (∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) ∧
        (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Cr * Real.exp (-cr * (t - u))) ∧
        ∀ T : ℝ, 0 < T → ∃ CrT : ℝ, 0 ≤ CrT ∧
          ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (ℱ : Filtration ℝ mΩ) (a : ℝ), 0 ≤ a →
            ∀ (M : ℝ → Ω → NegSobolev d r) (Sg : ℝ → Ω → (NegSobolev d r →L[ℝ] NegSobolev d r →L[ℝ] ℝ)),
              IsHilbertMartingaleWithCovariation P ℱ (a + T) M Sg →
              ∃ Z : ℝ → Ω → NegSobolev d r,
                (∀ t ∈ Set.Icc a (a + T),
                  IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d r)) M a t (Z t)) ∧
                (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc a (a + T))) ∧
                ∫⁻ ω, (⨆ t ∈ Set.Icc a (a + T), ‖Z t ω‖ₑ) ^ 2 ∂P ≤
                  ENNReal.ofReal CrT *
                    ∫⁻ ω, (∫⁻ u in Set.Icc a (a + T), ENNReal.ofReal (traceNormForm (Sg u ω))) ∂P := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨K₀, hK₀⟩ := Q54.evolution_estimates_proof hd1 s htr.hs0 htr.hsd r
  set K : ℕ := max K₀ (⌊(d : ℝ) / 2 + 6⌋₊ + 1) with hK
  have hKgt : (d : ℝ) / 2 + 6 < K := by
    have h1 : (d : ℝ) / 2 + 6 < ((⌊(d : ℝ) / 2 + 6⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast; exact Nat.lt_floor_add_one _
    exact h1.trans_le (by exact_mod_cast le_max_right _ _)
  have H := Q40b.q40b_finiteRegHyp htr hKgt
  obtain ⟨ρc, hρc, hρ⟩ := htr.global K hKgt
  obtain ⟨Cr, cr, hCr, hcr, Vev, hdual, hplain, hdec, hmax⟩ :=
    hK₀ K (le_max_left _ _) β htr.hβ V ρ₀ H ρc hρc
  refine ⟨Cr, cr, hCr, hcr, Vev, ?_, hplain, hdec, hmax⟩
  intro u t hu hut z φ hφ
  rw [hdual u t hu hut z φ hφ]
  congr 1
  funext x
  have := Q40b.q40b_propagator_congr (D := htr.dyn) (ρ := PDE.mfPath ρc) (ρ' := ρ) (t := t)
    (fun r hr => hρ r hr.1) u φ
  exact congrFun this x

/-! ### `PathSpace` is Polish -/

instance adjk_pathSpace_secondCountable {m T : ℝ} : SecondCountableTopology (PathSpace d m T) :=
  inferInstanceAs (SecondCountableTopology C(Set.Icc (0 : ℝ) T, NegSobolev d m))

instance adjk_pathSpace_complete {m T : ℝ} : CompleteSpace (PathSpace d m T) :=
  inferInstanceAs (CompleteSpace C(Set.Icc (0 : ℝ) T, NegSobolev d m))

/-! ### Energies -/

/-- PROVED.  `adjkEnergy` is antitone in the level: `‖F‖_{E_{m₂}} ≤ ‖F‖_{E_{m₁}}` for `m₁ ≤ m₂`. -/
theorem adjkEnergy_mono {m m₁ m₂ : ℝ} (h : m₁ ≤ m₂) (F : NegSobolev d m) :
    adjkEnergy m₂ m F ≤ adjkEnergy m₁ m F := by
  refine ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal ?_
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_le (Torus.jp_ge_one k.1) (by linarith)

/-! ### Tightness lemmas -/

/-- PROVED.  The laws of a sequence converging in law in a Polish space are tight (Prokhorov: the range of a convergent
sequence together with its limit is compact in `ProbabilityMeasure`). -/
theorem adjk_tight_of_tendstoInDistribution {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {Ω : ℕ → Type*}
    {mΩ : ∀ n, MeasurableSpace (Ω n)} {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {X : ∀ n, Ω n → E} {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {Z : Ω' → E} (h : TendstoInDistribution X atTop Z μ μ') :
    IsTightMeasureSet (Set.range fun n => (μ n).map (X n)) := by
  set ν : ℕ → ProbabilityMeasure E := fun n => ⟨(μ n).map (X n), inferInstance⟩ with hν
  have hc : IsCompact (closure (Set.range ν)) :=
    (h.tendsto.isCompact_insert_range).closure_of_subset (Set.subset_insert _ _)
  refine (isTightMeasureSet_of_isCompact_closure hc).subset ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨ν n, ⟨n, rfl⟩, rfl⟩

/-- PROVED.  If the laws of `A_i` and of `B_i` are tight, so are the laws of `A_i + B_i` (compact set `K₁ + K₂`). -/
theorem adjk_tight_add {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) (A B : ∀ i, Ω i → E) (hA : ∀ i, AEMeasurable (A i) (P i))
    (hB : ∀ i, AEMeasurable (B i) (P i))
    (tA : IsTightMeasureSet (Set.range fun i => (P i).map (A i)))
    (tB : IsTightMeasureSet (Set.range fun i => (P i).map (B i))) :
    IsTightMeasureSet (Set.range fun i => (P i).map (fun ω => A i ω + B i ω)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at tA tB ⊢
  intro ε hε
  obtain ⟨K₁, hK₁, h₁⟩ := tA (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨K₂, hK₂, h₂⟩ := tB (ε / 2) (ENNReal.half_pos hε.ne')
  have hKc : IsCompact ((fun p : E × E => p.1 + p.2) '' (K₁ ×ˢ K₂)) :=
    (hK₁.prod hK₂).image continuous_add
  refine ⟨_, hKc, ?_⟩
  rintro _ ⟨i, rfl⟩
  have e1 := h₁ _ ⟨i, rfl⟩
  have e2 := h₂ _ ⟨i, rfl⟩
  rw [Measure.map_apply_of_aemeasurable (hA i) hK₁.measurableSet.compl] at e1
  rw [Measure.map_apply_of_aemeasurable (hB i) hK₂.measurableSet.compl] at e2
  have hAB : AEMeasurable (fun ω => A i ω + B i ω) (P i) := (hA i).add (hB i)
  rw [Measure.map_apply_of_aemeasurable hAB hKc.measurableSet.compl]
  calc P i ((fun ω => A i ω + B i ω) ⁻¹' ((fun p : E × E => p.1 + p.2) '' (K₁ ×ˢ K₂))ᶜ)
      ≤ P i (A i ⁻¹' K₁ᶜ ∪ B i ⁻¹' K₂ᶜ) := by
        refine measure_mono fun ω hω => ?_
        by_contra hcon
        simp only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, not_or, not_not] at hcon
        exact hω ⟨(A i ω, B i ω), ⟨hcon.1, hcon.2⟩, rfl⟩
    _ ≤ P i (A i ⁻¹' K₁ᶜ) + P i (B i ⁻¹' K₂ᶜ) := measure_union_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add e1 e2
    _ = ε := ENNReal.add_halves ε

/-- PROVED (modulo COMPACT).  Tightness of the laws of paths `Ξ_i ∈ C([0,T];E_m)` from the two tail bounds: boundedness of
`sup_t ‖Ξ^t‖_{E_{m₁}}` in probability (`m₁ < m`) and asymptotic equicontinuity in `E_m`, uniformly in `i`
(probabilities of the bad `ω`-sets, so no measurability of the sets is needed). -/
theorem adjk_tight_of_tail_bounds {m T m₁ : ℝ} (hm₁ : m₁ < m) {ι : Type*} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (P : ∀ i, Measure (Ω i)) (Ξ : ∀ i, Ω i → PathSpace d m T)
    (hΞ : ∀ i, AEMeasurable (Ξ i) (P i))
    (hsup : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ i,
      P i {ω | ∃ t, ENNReal.ofReal (R ^ 2) < adjkEnergy m₁ m ((Ξ i ω).at' t)} ≤ ENNReal.ofReal ε)
    (hequi : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ i,
      P i {ω | ∃ s t : Set.Icc (0 : ℝ) T, |(s : ℝ) - t| ≤ δ ∧ η < ‖(Ξ i ω).at' s - (Ξ i ω).at' t‖} ≤
        ENNReal.ofReal ε) :
    IsTightMeasureSet (Set.range fun i => (P i).map (Ξ i)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεt
  · exact ⟨∅, isCompact_empty, fun μ _ => le_top⟩
  set ε' : ℝ := ε.toReal with hε'
  have hε'pos : 0 < ε' := ENNReal.toReal_pos hε.ne' hεt
  obtain ⟨R, hR⟩ := hsup (ε' / 2) (by positivity)
  have hδ : ∀ j : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ i,
      P i {ω | ∃ s t : Set.Icc (0 : ℝ) T, |(s : ℝ) - t| ≤ δ ∧
        1 / ((j : ℝ) + 1) < ‖(Ξ i ω).at' s - (Ξ i ω).at' t‖} ≤ ENNReal.ofReal (ε' / 2 ^ (j + 2)) :=
    fun j => hequi (ε' / 2 ^ (j + 2)) (1 / ((j : ℝ) + 1)) (by positivity) (by positivity)
  choose δ hδpos hδb using hδ
  refine ⟨adjkCompactSet d m T m₁ R δ, adjk_compactSet_isCompact d m T m₁ R hm₁ δ hδpos, ?_⟩
  rintro _ ⟨i, rfl⟩
  have hKm : MeasurableSet (adjkCompactSet d m T m₁ R δ)ᶜ :=
    (adjk_compactSet_isCompact d m T m₁ R hm₁ δ hδpos).measurableSet.compl
  rw [Measure.map_apply_of_aemeasurable (hΞ i) hKm]
  set A₀ : Set (Ω i) := {ω | ∃ t, ENNReal.ofReal (R ^ 2) < adjkEnergy m₁ m ((Ξ i ω).at' t)} with hA₀
  set A : ℕ → Set (Ω i) := fun j => {ω | ∃ s t : Set.Icc (0 : ℝ) T, |(s : ℝ) - t| ≤ δ j ∧
        1 / ((j : ℝ) + 1) < ‖(Ξ i ω).at' s - (Ξ i ω).at' t‖} with hA
  have hsub : Ξ i ⁻¹' (adjkCompactSet d m T m₁ R δ)ᶜ ⊆ A₀ ∪ ⋃ j, A j := by
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_compl_iff, adjkCompactSet, Set.mem_setOf_eq, not_and_or,
      not_forall, not_le] at hω
    rcases hω with ⟨t, ht⟩ | ⟨j, s, t, hst, h⟩
    · exact Or.inl ⟨t, ht⟩
    · exact Or.inr (Set.mem_iUnion.2 ⟨j, s, t, hst, h⟩)
  have hsum : ∑' j : ℕ, ENNReal.ofReal (ε' / 2 ^ (j + 2)) = ENNReal.ofReal (ε' / 2) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)]
    · congr 1
      have := tsum_geometric_two' (ε' / 2)
      rw [← this]
      refine tsum_congr fun j => ?_
      rw [pow_add]; field_simp
    · have := (summable_geometric_two' (ε' / 2))
      refine this.congr fun j => ?_
      rw [pow_add]; field_simp
  calc P i (Ξ i ⁻¹' (adjkCompactSet d m T m₁ R δ)ᶜ) ≤ P i (A₀ ∪ ⋃ j, A j) := measure_mono hsub
    _ ≤ P i A₀ + P i (⋃ j, A j) := measure_union_le _ _
    _ ≤ P i A₀ + ∑' j, P i (A j) := add_le_add le_rfl (measure_iUnion_le _)
    _ ≤ ENNReal.ofReal (ε' / 2) + ∑' j : ℕ, ENNReal.ofReal (ε' / 2 ^ (j + 2)) :=
        add_le_add (hR i) (ENNReal.tsum_le_tsum fun j => hδb j i)
    _ = ENNReal.ofReal ε' := by
        rw [hsum, ← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    _ = ε := ENNReal.ofReal_toReal hεt

/-- PROVED (modulo COMPACT).  The shape in which `dynamic_convergence` consumes ADJ-K: the path laws
`Φ_n = Lin(η⁰_n) + Ξ_n` in `C([0,T];E_m)` are tight when the initial laws converge (`hlaw`), `Lin` is continuous
(the map `z ↦ V^{·,0}z`, strongly continuous evolution) and `Ξ_n` (martingale convolution plus remainder) satisfies the two tail bounds
(from BCONV + KOLM + B2 + Markov).  `hid` is the mild decomposition B3 written in `C([0,T];E_m)`. -/
theorem adjk_tight_of_components {m T m₁ : ℝ} (hm₁ : m₁ < m) {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Φ Ξ : ∀ n, Ω n → PathSpace d m T) (η₀ : ∀ n, Ω n → NegSobolev d m)
    (Lin : NegSobolev d m → PathSpace d m T) (hLin : Continuous Lin)
    (hη : ∀ n, AEMeasurable (η₀ n) (P n)) (hΞ : ∀ n, AEMeasurable (Ξ n) (P n))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] (η' : Ω' → NegSobolev d m)
    (hlaw : TendstoInDistribution η₀ atTop η' P P')
    (hsup : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ n,
      P n {ω | ∃ t, ENNReal.ofReal (R ^ 2) < adjkEnergy m₁ m ((Ξ n ω).at' t)} ≤ ENNReal.ofReal ε)
    (hequi : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ n,
      P n {ω | ∃ s t : Set.Icc (0 : ℝ) T, |(s : ℝ) - t| ≤ δ ∧ η < ‖(Ξ n ω).at' s - (Ξ n ω).at' t‖} ≤
        ENNReal.ofReal ε)
    (hid : ∀ n, ∀ᵐ ω ∂P n, Φ n ω = Lin (η₀ n ω) + Ξ n ω) :
    IsTightMeasureSet (Set.range fun n => (P n).map (Φ n)) := by
  have t0 := adjk_tight_of_tendstoInDistribution hlaw
  have tLin : IsTightMeasureSet (Set.range fun n => (P n).map (fun ω => Lin (η₀ n ω))) := by
    refine (t0.map hLin).subset ?_
    rintro _ ⟨n, rfl⟩
    refine ⟨(P n).map (η₀ n), ⟨n, rfl⟩, ?_⟩
    exact AEMeasurable.map_map_of_aemeasurable hLin.aemeasurable (hη n)
  have tΞ := adjk_tight_of_tail_bounds hm₁ P Ξ hΞ hsup hequi
  have tsum := adjk_tight_add P (fun n ω => Lin (η₀ n ω)) Ξ
    (fun n => hLin.aemeasurable.comp_aemeasurable (hη n)) hΞ tLin tΞ
  refine tsum.subset ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨n, (Measure.map_congr (hid n)).symm⟩

/-! ### The initial-data map -/

/-- PROVED.  Strong continuity of an evolution gives continuity of every orbit `t ↦ V^{t,0}z` on `[0,T]`. -/
theorem adjk_orbit_continuous {m T : ℝ} {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hplain : IsPlainEvolution Vev T) (z : NegSobolev d m) :
    Continuous fun t : Set.Icc (0 : ℝ) T => Vev t 0 z := by
  have h := hplain.2.2 z
  have hmap : Continuous fun t : Set.Icc (0 : ℝ) T => ((t : ℝ), (0 : ℝ)) := by fun_prop
  exact h.comp_continuous hmap fun t => ⟨le_rfl, t.2.1, t.2.2⟩

/-- The initial-data map `z ↦ (t ↦ V^{t,0} z) ∈ C([0,T];E_m)` (the `Lin` of `adjk_tight_of_components`, TeX `V^{t,0}η_N^0`
in `P:eq:noneq-mild`, M L6566) for an evolution with continuous orbits. -/
def adjkLin (m T : ℝ) (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hc : ∀ z, Continuous fun t : Set.Icc (0 : ℝ) T => Vev t 0 z) (z : NegSobolev d m) :
    PathSpace d m T :=
  (⟨fun t => Vev t 0 z, hc z⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m))

theorem adjkLin_at {m T : ℝ} {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hc : ∀ z, Continuous fun t : Set.Icc (0 : ℝ) T => Vev t 0 z) (z : NegSobolev d m)
    (t : Set.Icc (0 : ℝ) T) : (adjkLin m T Vev hc z).at' t = Vev t 0 z := rfl

/-- PROVED.  `z ↦ V^{·,0} z` is a bounded linear (hence continuous) map `E_m → C([0,T];E_m)` when `‖V^{t,0}‖ ≤ C`. -/
theorem adjkLin_continuous {m T C : ℝ} {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hc : ∀ z, Continuous fun t : Set.Icc (0 : ℝ) T => Vev t 0 z) (hC : 0 ≤ C)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖Vev t 0‖ ≤ C) : Continuous (adjkLin m T Vev hc) := by
  have hnorm : ∀ z, ‖adjkLin m T Vev hc z‖ ≤ C * ‖z‖ := by
    intro z
    have : ‖(⟨fun t => Vev t 0 z, hc z⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m))‖ ≤ C * ‖z‖ :=
      (ContinuousMap.norm_le _ (by positivity)).2 fun t =>
        ((Vev t 0).le_opNorm z).trans (mul_le_mul_of_nonneg_right (hb t t.2) (norm_nonneg _))
    exact this
  have hsub : ∀ z z', adjkLin m T Vev hc z - adjkLin m T Vev hc z' = adjkLin m T Vev hc (z - z') := by
    intro z z'
    refine ContinuousMap.ext fun t => ?_
    show Vev t 0 z - Vev t 0 z' = Vev t 0 (z - z')
    rw [map_sub]
  refine (LipschitzWith.of_dist_le_mul (K := ⟨C, hC⟩) fun z z' => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, hsub]
  exact hnorm _

/-- PROVED.  Along an `IsSmoothPositiveTrajectory` the dual evolution of A3 yields a continuous initial-data map for every
horizon `T ≥ 0`. -/
theorem adjk_lin_along_trajectory (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (m T : ℝ)
    (hT : 0 ≤ T) :
    ∃ (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
      (hc : ∀ z, Continuous fun t : Set.Icc (0 : ℝ) T => Vev t 0 z),
      IsDualEvolution htr.dyn ρ m Vev ∧ Continuous (adjkLin m T Vev hc) := by
  obtain ⟨Cr, cr, hCr, hcr, Vev, hdual, hplain, hdec, -⟩ := adjk_evolution_along_trajectory hd htr m
  have hc : ∀ z, Continuous fun t : Set.Icc (0 : ℝ) T => Vev t 0 z :=
    fun z => adjk_orbit_continuous (hplain T hT) z
  refine ⟨Vev, hc, hdual, adjkLin_continuous hc hCr.le fun t ht => ?_⟩
  refine (hdec 0 t le_rfl ht.1).trans ?_
  have : Real.exp (-cr * (t - 0)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [ht.1])
  nlinarith

/-! ### Energy semicontinuity and the Markov step -/

/-- PROVED.  The weighted coordinate `F ↦ coord F k` is continuous on `E_m`. -/
theorem adjk_continuous_coord (m : ℝ) (k : NonzeroLattice d) :
    Continuous fun F : NegSobolev d m => NegSobolev.coord F k := by
  have : Continuous fun f : lp (fun _ : NonzeroLattice d => ℝ) 2 => f k := by
    refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun f g => ?_)
    have := lp.norm_apply_le_norm (by norm_num) (f - g) k
    simpa [dist_eq_norm, Real.dist_eq] using this
  exact this

/-- PROVED.  `adjkEnergy` is lower semicontinuous (a `tsum` of continuous nonnegative terms). -/
theorem adjkEnergy_lsc (m₁ m : ℝ) : LowerSemicontinuous (adjkEnergy (d := d) m₁ m) := by
  refine lowerSemicontinuous_tsum fun k => ?_
  exact (ENNReal.continuous_ofReal.comp
    (continuous_const.mul ((adjk_continuous_coord m k).pow 2))).lowerSemicontinuous

/-- PROVED. -/
theorem adjkEnergy_measurable (m₁ m : ℝ) : Measurable (adjkEnergy (d := d) m₁ m) :=
  (adjkEnergy_lsc m₁ m).measurable


/-- PROVED. -/
theorem ratIcc_countable (a b : ℝ) : (ratIcc a b).Countable := by
  refine (Set.countable_range ((↑) : ℚ → ℝ)).mono ?_
  rintro t ⟨-, q, rfl⟩
  exact ⟨q, rfl⟩

/-- PROVED.  Markov step: the `E_{m₁}`-sup bound `E sup_{t∈[0,T]∩ℚ} ‖Z_t‖²_{E_{m₁}} ≤ C` (first conclusion of BCONV, for a continuous
`E_m`-valued process `Z` whose path in `C([0,T];E_m)` is `Ξ`) gives the tail bound `hsup` of `adjk_tight_of_tail_bounds`
(lower semicontinuity of the energy along a continuous path reduces the supremum over `[0,T]` to rational times). -/
theorem adjk_supTail_of_moment {m T m₁ : ℝ} (hT : 0 < T) {ι : Type*} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (P : ∀ i, Measure (Ω i)) (Ξ : ∀ i, Ω i → PathSpace d m T)
    (Zf : ∀ i, ℝ → Ω i → NegSobolev d m) (hZm : ∀ i t, Measurable (Zf i t))
    (hΞZ : ∀ i, ∀ᵐ ω ∂P i, ∀ t (ht : t ∈ Set.Icc (0 : ℝ) T), (Ξ i ω).at' ⟨t, ht⟩ = Zf i t ω)
    (C : ℝ) (hC : 0 ≤ C)
    (hmom : ∀ i, ∫⁻ ω, ⨆ t ∈ ratIcc 0 T, adjkEnergy m₁ m (Zf i t ω) ∂P i ≤ ENNReal.ofReal C) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ i,
      P i {ω | ∃ t, ENNReal.ofReal (R ^ 2) < adjkEnergy m₁ m ((Ξ i ω).at' t)} ≤ ENNReal.ofReal ε := by
  intro ε hε
  set R : ℝ := Real.sqrt (C / ε) + 1 with hR
  refine ⟨R, fun i => ?_⟩
  set G : Ω i → ℝ≥0∞ := fun ω => ⨆ t ∈ ratIcc 0 T, adjkEnergy m₁ m (Zf i t ω) with hG
  have hGm : Measurable G := by
    refine Measurable.biSup _ (ratIcc_countable 0 T) fun t _ => ?_
    exact (adjkEnergy_measurable m₁ m).comp (hZm i t)
  have hR2 : C ≤ ε * R ^ 2 := by
    have h1 : C / ε ≤ R ^ 2 := by
      have := Real.sq_sqrt (div_nonneg hC hε.le)
      nlinarith [Real.sqrt_nonneg (C / ε)]
    calc C = ε * (C / ε) := by field_simp
      _ ≤ ε * R ^ 2 := mul_le_mul_of_nonneg_left h1 hε.le
  have hRpos : 0 < R ^ 2 := by positivity
  have hsub : {ω | ∃ t, ENNReal.ofReal (R ^ 2) < adjkEnergy m₁ m ((Ξ i ω).at' t)} ≤ᵐ[P i]
      {ω | ENNReal.ofReal (R ^ 2) ≤ G ω} := by
    filter_upwards [hΞZ i] with ω hω hbad
    obtain ⟨t₀, ht₀⟩ := hbad
    set c := ENNReal.ofReal (R ^ 2) with hc
    let g : ℝ → ℝ≥0∞ := fun t => adjkEnergy m₁ m ((Ξ i ω).at' (Set.projIcc 0 T hT.le t))
    have hgl : LowerSemicontinuous g := by
      refine (adjkEnergy_lsc (d := d) m₁ m).comp ?_
      have : Continuous fun t : ℝ => (Ξ i ω).at' (Set.projIcc 0 T hT.le t) := by
        have h1 : Continuous fun t : Set.Icc (0 : ℝ) T => (Ξ i ω).at' t :=
          (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from Ξ i ω).continuous
        exact h1.comp continuous_projIcc
      exact this
    have hopen : IsOpen {t : ℝ | c < g t} := hgl.isOpen_preimage c
    have ht₀g : (t₀ : ℝ) ∈ {t : ℝ | c < g t} := by
      show c < g t₀
      simp only [g, Set.projIcc_val]
      exact ht₀
    have hcl : (t₀ : ℝ) ∈ closure (Set.Ioo (0 : ℝ) T) := by
      rw [closure_Ioo hT.ne]; exact t₀.2
    obtain ⟨t₁, ht₁g, ht₁⟩ := mem_closure_iff.1 hcl _ hopen ht₀g
    have hne : ({t : ℝ | c < g t} ∩ Set.Ioo 0 T).Nonempty := ⟨t₁, ht₁g, ht₁⟩
    obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open (hopen.inter isOpen_Ioo) hne
    have hqI : (q : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨hq.2.1.le, hq.2.2.le⟩
    have hqg : c < adjkEnergy m₁ m (Zf i q ω) := by
      have := hq.1
      simp only [Set.mem_setOf_eq, g, Set.projIcc_of_mem _ hqI] at this
      rw [← hω q hqI]; exact this
    show c ≤ G ω
    exact le_iSup₂_of_le (q : ℝ) (show (q : ℝ) ∈ ratIcc 0 T from ⟨hqI, q, rfl⟩) hqg.le
  calc P i {ω | ∃ t, ENNReal.ofReal (R ^ 2) < adjkEnergy m₁ m ((Ξ i ω).at' t)}
      ≤ P i {ω | ENNReal.ofReal (R ^ 2) ≤ G ω} := measure_mono_ae hsub
    _ ≤ (∫⁻ ω, G ω ∂P i) / ENNReal.ofReal (R ^ 2) :=
        meas_ge_le_lintegral_div hGm.aemeasurable (ENNReal.ofReal_pos.2 hRpos).ne' ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C / ENNReal.ofReal (R ^ 2) := ENNReal.div_le_div_right (hmom i) _
    _ ≤ ENNReal.ofReal ε := by
        rw [ENNReal.div_le_iff (ENNReal.ofReal_pos.2 hRpos).ne' ENNReal.ofReal_ne_top, ← ENNReal.ofReal_mul hε.le]
        exact ENNReal.ofReal_le_ofReal (by linarith)

end HRS.AdjK
