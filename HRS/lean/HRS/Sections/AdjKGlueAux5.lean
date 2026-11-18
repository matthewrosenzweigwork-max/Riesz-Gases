import HRS.Sections.AdjKGlueAux4
import HRS.Sections.AdjKAFinal2
import HRS.Sections.AdjKBFinal
import HRS.Sections.AdjKDFinal
import HRS.Sections.AdjKEFinal
import HRS.Sections.DynCmpFinal2

/-!
# ADJK-GLUE, part 5: utilities for `dynamic_convergence`

Uniqueness of the dual evolution, the quadratic energy inequality, rational times for lower semicontinuous
functionals along continuous paths, and the Markov step for `ℝ≥0∞`-valued random variables.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

universe u

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjkg_ext_fourier {m : ℝ} {F G : NegSobolev d m}
    (h : ∀ k, NegSobolev.fourierCoeff F k = NegSobolev.fourierCoeff G k) : F = G := by
  have hc : ∀ k, NegSobolev.coord F k = NegSobolev.coord G k := by
    intro k
    have := h k
    unfold NegSobolev.fourierCoeff at this
    exact mul_left_cancel₀ (Real.rpow_pos_of_pos (Torus.jp_pos _) m).ne' this
  have : (F : lp (fun _ : NonzeroLattice d => ℝ) 2) = (G : lp (fun _ : NonzeroLattice d => ℝ) 2) :=
    lp.ext (funext hc)
  exact this

/-- The dual evolution is unique on `0 ≤ u ≤ t`. -/
theorem adjkg_dual_eq {m : ℝ} {D : DynData d} {ρ : ℝ → Torus d → ℝ}
    {V V' : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (h : IsDualEvolution D ρ m V)
    (h' : IsDualEvolution D ρ m V') {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) : V t u = V' t u := by
  refine ContinuousLinearMap.ext fun z => adjkg_ext_fourier fun k => ?_
  rw [← adjkd_eval_realMode, ← adjkd_eval_realMode, h u t hu hut z _ (adjkd_isSmooth_realMode k),
    h' u t hu hut z _ (adjkd_isSmooth_realMode k)]

theorem adjkg_coord_add {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (F + G) k = NegSobolev.coord F k + NegSobolev.coord G k := rfl

theorem adjkg_coord_sub {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (F - G) k = NegSobolev.coord F k - NegSobolev.coord G k := rfl

theorem adjkg_energy_add_le {m m₁ : ℝ} (F G : NegSobolev d m) :
    adjkEnergy m₁ m (F + G) ≤ 2 * adjkEnergy m₁ m F + 2 * adjkEnergy m₁ m G := by
  unfold adjkEnergy
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun k => ?_
  rw [adjkg_coord_add]
  set w : ℝ := Lattice.jp k.1 ^ (2 * (m - m₁)) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg (Torus.jp_pos _).le _
  set a := NegSobolev.coord F k
  set b := NegSobolev.coord G k
  have h1 : w * (a + b) ^ 2 ≤ 2 * (w * a ^ 2) + 2 * (w * b ^ 2) := by
    nlinarith [mul_nonneg hw0 (sq_nonneg (a - b))]
  calc ENNReal.ofReal (w * (a + b) ^ 2) ≤ ENNReal.ofReal (2 * (w * a ^ 2) + 2 * (w * b ^ 2)) :=
        ENNReal.ofReal_le_ofReal h1
    _ = 2 * ENNReal.ofReal (w * a ^ 2) + 2 * ENNReal.ofReal (w * b ^ 2) := by
        rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) (mul_nonneg hw0 (sq_nonneg _)))
          (mul_nonneg (by norm_num) (mul_nonneg hw0 (sq_nonneg _))), ENNReal.ofReal_mul (p := 2) (by norm_num),
          ENNReal.ofReal_mul (p := 2) (by norm_num)]
        simp

theorem adjkg_energy_sub_le {m m₁ : ℝ} (F G : NegSobolev d m) :
    adjkEnergy m₁ m (F - G) ≤ 2 * adjkEnergy m₁ m F + 2 * adjkEnergy m₁ m G := by
  have := adjkg_energy_add_le (m₁ := m₁) F (-G)
  have e : adjkEnergy m₁ m (-G) = adjkEnergy m₁ m G := by
    unfold adjkEnergy
    refine tsum_congr fun k => ?_
    have : NegSobolev.coord (-G) k = -NegSobolev.coord G k := rfl
    rw [this, neg_sq]
  rw [e, ← sub_eq_add_neg] at this
  exact this

/-- `‖F‖²_{E_m} = adjkEnergy m m F`. -/
theorem adjkg_energy_self {m : ℝ} (F : NegSobolev d m) : adjkEnergy m m F = ‖F‖ₑ ^ 2 := by
  obtain ⟨hs, hn⟩ := NegSobolev.coord_sq F
  have h1 : ‖F‖ₑ ^ 2 = ENNReal.ofReal (‖F‖ ^ 2) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [h1, hn, ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) hs]
  unfold adjkEnergy
  refine tsum_congr fun k => ?_
  rw [sub_self, mul_zero, Real.rpow_zero, one_mul]

/-- The norm is controlled by the energy at any lower level. -/
theorem adjkg_enorm_sq_le_energy {m m₁ : ℝ} (hm₁ : m₁ ≤ m) (F : NegSobolev d m) :
    ‖F‖ₑ ^ 2 ≤ adjkEnergy m₁ m F := by
  rw [← adjkg_energy_self]
  exact adjkEnergy_mono hm₁ F

/-- Rational times: if a lower semicontinuous functional of a continuous path exceeds `c` at some time of
`[0,T]` it exceeds `c` at some rational time. -/
theorem adjkg_rat_lsc {T : ℝ} (hT : 0 < T) {E : Type*} [TopologicalSpace E] (f : E → ℝ≥0∞)
    (hf : LowerSemicontinuous f) (w : ℝ → E) (hw : ContinuousOn w (Set.Icc 0 T)) {c : ℝ≥0∞} {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) T) (h : c < f (w t₀)) : ∃ q ∈ ratIcc 0 T, c < f (w q) := by
  let g : ℝ → ℝ≥0∞ := fun t => f (w (Set.projIcc 0 T hT.le t))
  have hgl : LowerSemicontinuous g := by
    refine hf.comp ?_
    have h1 : Continuous (Set.restrict (Set.Icc (0 : ℝ) T) w) := continuousOn_iff_continuous_restrict.1 hw
    exact h1.comp continuous_projIcc
  have hopen : IsOpen {t : ℝ | c < g t} := hgl.isOpen_preimage c
  have ht₀g : t₀ ∈ {t : ℝ | c < g t} := by
    show c < g t₀
    simp only [g, Set.projIcc_of_mem _ ht₀]
    exact h
  have hcl : t₀ ∈ closure (Set.Ioo (0 : ℝ) T) := by
    rw [closure_Ioo hT.ne]; exact ht₀
  obtain ⟨t₁, ht₁g, ht₁⟩ := mem_closure_iff.1 hcl _ hopen ht₀g
  have hne : ({t : ℝ | c < g t} ∩ Set.Ioo 0 T).Nonempty := ⟨t₁, ht₁g, ht₁⟩
  obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open (hopen.inter isOpen_Ioo) hne
  have hqI : (q : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨hq.2.1.le, hq.2.2.le⟩
  refine ⟨q, ⟨hqI, q, rfl⟩, ?_⟩
  have := hq.1
  simp only [Set.mem_setOf_eq, g, Set.projIcc_of_mem _ hqI] at this
  exact this

/-- Markov for a measurable `ℝ≥0∞`-valued function. -/
theorem adjkg_markov {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {G : Ω → ℝ≥0∞}
    (hG : AEMeasurable G P) {K : ℝ} (hK : ∫⁻ ω, G ω ∂P ≤ ENNReal.ofReal K) {R : ℝ} (hR : 0 < R) :
    P {ω | ENNReal.ofReal R ≤ G ω} ≤ ENNReal.ofReal (K / R) := by
  calc P {ω | ENNReal.ofReal R ≤ G ω} ≤ (∫⁻ ω, G ω ∂P) / ENNReal.ofReal R :=
        meas_ge_le_lintegral_div hG (ENNReal.ofReal_pos.2 hR).ne' ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K / ENNReal.ofReal R := ENNReal.div_le_div_right hK _
    _ = ENNReal.ofReal (K / R) := by
        rw [ENNReal.ofReal_div_of_pos hR]

theorem adjkg_sqrt_le (x : ℝ≥0∞) : x ^ (1 / 2 : ℝ) ≤ 1 + x := by
  by_cases hx : x ≤ 1
  · calc x ^ (1 / 2 : ℝ) ≤ 1 ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hx (by norm_num)
      _ = 1 := ENNReal.one_rpow _
      _ ≤ 1 + x := le_self_add
  · push_neg at hx
    calc x ^ (1 / 2 : ℝ) ≤ x ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
      _ = x := ENNReal.rpow_one x
      _ ≤ 1 + x := le_add_self

/-- Relocated copy (uses `adjk_compactSet_isCompact_proof`).  Tightness of the laws of paths `Ξ_i ∈ C([0,T];E_m)` from the two tail bounds: boundedness of
`sup_t ‖Ξ^t‖_{E_{m₁}}` in probability (`m₁ < m`) and asymptotic equicontinuity in `E_m`, uniformly in `i`
(probabilities of the bad `ω`-sets, so no measurability of the sets is needed). -/
theorem adjkg_tight_of_tail_bounds {m T m₁ : ℝ} (hm₁ : m₁ < m) {ι : Type*} {Ω : ι → Type*}
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
  refine ⟨adjkCompactSet d m T m₁ R δ, adjk_compactSet_isCompact_proof d m T m₁ R hm₁ δ hδpos, ?_⟩
  rintro _ ⟨i, rfl⟩
  have hKm : MeasurableSet (adjkCompactSet d m T m₁ R δ)ᶜ :=
    (adjk_compactSet_isCompact_proof d m T m₁ R hm₁ δ hδpos).measurableSet.compl
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

/-- Relocated copy (uses `adjk_compactSet_isCompact_proof`).  The shape in which `dynamic_convergence` consumes ADJ-K: the path laws
`Φ_n = Lin(η⁰_n) + Ξ_n` in `C([0,T];E_m)` are tight when the initial laws converge (`hlaw`), `Lin` is continuous
(the map `z ↦ V^{·,0}z`, strongly continuous evolution) and `Ξ_n` (martingale convolution plus remainder) satisfies the two tail bounds
(from BCONV + KOLM + B2 + Markov).  `hid` is the mild decomposition B3 written in `C([0,T];E_m)`. -/
theorem adjkg_tight_of_components {m T m₁ : ℝ} (hm₁ : m₁ < m) {Ω : ℕ → Type*}
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
  have tΞ := adjkg_tight_of_tail_bounds hm₁ P Ξ hΞ hsup hequi
  have tsum := adjk_tight_add P (fun n ω => Lin (η₀ n ω)) Ξ
    (fun n => hLin.aemeasurable.comp_aemeasurable (hη n)) hΞ tLin tΞ
  refine tsum.subset ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨n, (Measure.map_congr (hid n)).symm⟩


end HRS.AdjK
