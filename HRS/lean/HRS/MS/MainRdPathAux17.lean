import HRS.MS.MainRdPathAux16

/-!
# S.A.9, packet P3k: uniform tails of the thermal stochastic convolution

`sa9_Mq_tail`: for `t ∈ [0,T]` and `η > 0` there are `Lc`, `N₀` with
`E ∑_{ℓ ≥ Lc} ⟨φ_ℓ, Mq_N^t⟩² ≤ η` for all `N ≥ N₀`.  Choice of the parameters `R` (second moments), `δ` (net),
`Lc` (dominated convergence), `N₀` (stability) in `sa9_Mq_tail_bound`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.HNegInfra HRS.MP.RdInit
  HRS.MP.RdMart HRS.MP.RdRem HRS.MP.RdProp HRS.MS.MainRdField

variable {d : ℕ}

theorem sa9_ofReal_quarter {x : ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c) (η : ℝ) (hx : x = ENNReal.ofReal c)
    (hle : c ≤ η / 4) : x ≤ ENNReal.ofReal (η / 4) := by
  rw [hx]; exact ENNReal.ofReal_le_ofReal hle

section Main

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {Γ : ℕ}

theorem sa9_Mq_tail (B : Sa9Bundle S R Γ) (h : ℕ → mhn_Hc d)
    (hP : ∀ F : HNeg d ((Γ + 2 : ℕ) : ℝ),
      HasSum (fun n => (inner ℝ (mhn_rep ((Γ + 2 : ℕ) : ℝ) (h n)) F) ^ 2) (‖F‖ ^ 2))
    {m₀ : ℕ} (hm₀ : 1 ≤ m₀) {Kadj Kst : ℝ}
    (hAdjP : AdjointDerivInput ((Γ + 2 : ℕ) : ℝ) (m₀ + 1) S.coeff S.T Kadj)
    (L : LimitCoeffsRd d) (hAdjL : AdjointInputOneD ((Γ + 2 : ℕ) : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj)
    (hStab : AdjointStabilityInputRd S L (Γ + 2) (m₀ + 1) Γ Kst)
    (hΔ : Tendsto (fun N => coeffDiscrepancyRd S L Γ N) atTop (𝓝 0)) {m₂ : ℝ} (hm₂0 : 0 ≤ m₂)
    (hm₂ : PropagatedSecondMoment S R m₂) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {η : ℝ} (hη : 0 < η) :
    ∃ Lc N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
      ∫⁻ ζ, ∑' l, ENNReal.ofReal ((HNeg.pairing (mhn_phi (h (l + Lc))) (B.Mq N t ζ)) ^ 2) ∂(R N).P ≤
        ENNReal.ofReal η := by
  classical
  have ht0 := ht.1
  set a : ℝ := (d : ℝ) * d * |Kadj| with ha
  have ha0 : 0 ≤ a := by positivity
  -- the radius
  set Rr : ℝ := Real.sqrt (16 * d * Kadj ^ 2 * t * m₂ / η + 1) with hRr
  have hRr2 : Rr ^ 2 = 16 * d * Kadj ^ 2 * t * m₂ / η + 1 := Real.sq_sqrt (by positivity)
  have hRrpos : 0 < Rr := Real.sqrt_pos.2 (by positivity)
  -- the mesh
  set δ : ℝ := Real.sqrt (η / (32 * (d + 1) * (t + 1) * (a ^ 2 + 1))) with hδ
  have hδ2 : δ ^ 2 = η / (32 * (d + 1) * (t + 1) * (a ^ 2 + 1)) := Real.sq_sqrt (by positivity)
  have hδpos : 0 < δ := Real.sqrt_pos.2 (by positivity)
  obtain ⟨net', -, hnetfin, hcover⟩ := finite_cover_balls_of_compact
    (isCompact_closedBall (0 : Euc d) Rr) hδpos
  set net : Finset (Euc d) := hnetfin.toFinset with hnet
  have hnetp : ∀ x : Euc d, ‖x‖ ≤ Rr → ∃ y ∈ net, ‖x - y‖ < δ := by
    intro x hx
    have := hcover (by simpa using hx)
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 this
    exact ⟨y, by simpa [hnet] using hy, by simpa [dist_eq_norm] using hxy⟩
  -- the choice of `Lc`
  have hU : Tendsto (fun Lc => ∑ j : Fin d, ∑ y ∈ net, (∫⁻ r in Set.Icc (0 : ℝ) t,
      sa9_Tm h (L.coeff S) t j Lc (r, y))) atTop (𝓝 0) := by
    have : (0 : ℝ≥0∞) = ∑ j : Fin d, ∑ y ∈ net, 0 := by simp
    rw [this]
    refine tendsto_finset_sum _ fun j _ => tendsto_finset_sum _ fun y _ => ?_
    have := tendsto_lintegral_of_dominated_convergence (μ := volume.restrict (Set.Icc (0 : ℝ) t))
      (F := fun Lc r => sa9_Tm h (L.coeff S) t j Lc (r, y)) (f := fun _ => (0 : ℝ≥0∞))
      (fun _ => ENNReal.ofReal (Kadj ^ 2))
      (fun Lc => (sa9_Tm_meas h (L.coeff S) t j Lc).comp (measurable_id.prodMk measurable_const))
      (fun Lc => Eventually.of_forall fun r => sa9_Tm_le hAdjL h hP ht.2 j Lc r y)
      (by rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (by rw [Measure.restrict_apply MeasurableSet.univ]; simp))
      (Eventually.of_forall fun r => sa9_Tm_tendsto hAdjL h hP ht.2 j r y)
    simpa using this
  have hηpos : (0 : ℝ≥0∞) < ENNReal.ofReal (η / 4) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨Lc, hLc⟩ := ((ENNReal.Tendsto.const_mul hU (Or.inr (by norm_num : (8 : ℝ≥0∞) ≠ ⊤))).eventually
    (gt_mem_nhds (by rw [mul_zero]; exact hηpos))).exists
  -- the choice of `N₀`
  have hD : Tendsto (fun N => (|Kst| * (coeffDiscrepancyRd S L Γ N).toReal)) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hΔ
    simpa using this.const_mul |Kst|
  have hED : Tendsto (fun N => 4 * (d : ℝ≥0∞) * ENNReal.ofReal t * ENNReal.ofReal
      ((|Kst| * (coeffDiscrepancyRd S L Γ N).toReal) ^ 2)) atTop (𝓝 0) := by
    have h3 : Tendsto (fun N => ENNReal.ofReal ((|Kst| * (coeffDiscrepancyRd S L Γ N).toReal) ^ 2)) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (hD.pow 2)
      simpa using this
    have := ENNReal.Tendsto.const_mul h3 (Or.inr (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
      (by simp)) ENNReal.ofReal_ne_top) : (0 : ℝ≥0∞) ≠ 0 ∨ 4 * (d : ℝ≥0∞) * ENNReal.ofReal t ≠ ⊤)
    simpa using this
  have hfinev : ∀ᶠ N in atTop, coeffDiscrepancyRd S L Γ N ≠ ⊤ :=
    hΔ.eventually (ENNReal.isOpen_ne_top.mem_nhds ENNReal.zero_ne_top)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hfinev.and (hED.eventually (gt_mem_nhds hηpos)))
  refine ⟨Lc, N₀, fun N hN hN1 => ?_⟩
  obtain ⟨hfin, hDN⟩ := hN₀ N hN
  refine (sa9_Mq_tail_bound B h hP hm₀ hAdjP L hAdjL hStab hm₂ ht hN1 hfin Lc hRrpos net hnetp).trans ?_
  set ED : ℝ := (|Kst| * (coeffDiscrepancyRd S L Γ N).toReal) ^ 2 with hEDdef
  set U1 : ℝ≥0∞ := ∑ j : Fin d, ∑ y ∈ net, (∫⁻ r in Set.Icc (0 : ℝ) t, sa9_Tm h (L.coeff S) t j Lc (r, y)) with hU1
  have e : 2 * (4 * U1 + ENNReal.ofReal t * ∑ _j : Fin d, (4 * ENNReal.ofReal (((d : ℝ) * d * |Kadj| * δ) ^ 2) +
      2 * ENNReal.ofReal ED)) + 2 * d * ENNReal.ofReal (Kadj ^ 2) * ENNReal.ofReal (2 / Rr ^ 2) *
        (ENNReal.ofReal t * ENNReal.ofReal m₂) =
      8 * U1 + 2 * (ENNReal.ofReal t * ((d : ℝ≥0∞) * (4 * ENNReal.ofReal ((a * δ) ^ 2)))) +
        2 * (ENNReal.ofReal t * ((d : ℝ≥0∞) * (2 * ENNReal.ofReal ED))) +
        2 * d * ENNReal.ofReal (Kadj ^ 2) * ENNReal.ofReal (2 / Rr ^ 2) *
          (ENNReal.ofReal t * ENNReal.ofReal m₂) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (d : ℝ) * d * |Kadj| * δ = a * δ := by rw [ha]
    rw [this]
    ring
  rw [e]
  have h1 : 8 * U1 ≤ ENNReal.ofReal (η / 4) := by
    have := hLc.le
    simpa using this
  have h2 : 2 * (ENNReal.ofReal t * ((d : ℝ≥0∞) * (4 * ENNReal.ofReal ((a * δ) ^ 2)))) ≤ ENNReal.ofReal (η / 4) := by
    have : 2 * (ENNReal.ofReal t * ((d : ℝ≥0∞) * (4 * ENNReal.ofReal ((a * δ) ^ 2)))) =
        ENNReal.ofReal (2 * (t * (d * (4 * (a * δ) ^ 2)))) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul ht0, ENNReal.ofReal_mul (Nat.cast_nonneg d),
        ENNReal.ofReal_mul (by norm_num)]
      simp
    rw [this]
    refine ENNReal.ofReal_le_ofReal ?_
    have h5 : 2 * (t * (d * (4 * (a * δ) ^ 2))) ≤ 8 * (t + 1) * (d + 1) * (a ^ 2 + 1) * δ ^ 2 := by
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      nlinarith [mul_nonneg ht0 hd0, sq_nonneg (a * δ), sq_nonneg δ, mul_nonneg (mul_nonneg ht0 hd0) (sq_nonneg (a * δ)),
        mul_nonneg (mul_nonneg ht0 hd0) (sq_nonneg δ), mul_nonneg ht0 (sq_nonneg δ), mul_nonneg hd0 (sq_nonneg δ),
        mul_nonneg (sq_nonneg a) (sq_nonneg δ), mul_nonneg (mul_nonneg ht0 (sq_nonneg a)) (sq_nonneg δ),
        mul_nonneg (mul_nonneg hd0 (sq_nonneg a)) (sq_nonneg δ)]
    refine h5.trans (le_of_eq ?_)
    rw [hδ2]
    field_simp
    ring
  have h3 : 2 * (ENNReal.ofReal t * ((d : ℝ≥0∞) * (2 * ENNReal.ofReal ED))) ≤ ENNReal.ofReal (η / 4) := by
    have : 2 * (ENNReal.ofReal t * ((d : ℝ≥0∞) * (2 * ENNReal.ofReal ED))) =
        4 * (d : ℝ≥0∞) * ENNReal.ofReal t * ENNReal.ofReal ED := by ring
    rw [this]; exact hDN.le
  have h4 : 2 * d * ENNReal.ofReal (Kadj ^ 2) * ENNReal.ofReal (2 / Rr ^ 2) *
      (ENNReal.ofReal t * ENNReal.ofReal m₂) ≤ ENNReal.ofReal (η / 4) := by
    have : 2 * (d : ℝ≥0∞) * ENNReal.ofReal (Kadj ^ 2) * ENNReal.ofReal (2 / Rr ^ 2) *
        (ENNReal.ofReal t * ENNReal.ofReal m₂) = ENNReal.ofReal (2 * d * Kadj ^ 2 * (2 / Rr ^ 2) * (t * m₂)) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul ht0]
      simp
    rw [this]
    refine ENNReal.ofReal_le_ofReal ?_
    have hRrsq : 0 < Rr ^ 2 := by positivity
    have key : 2 * (d : ℝ) * Kadj ^ 2 * (2 / Rr ^ 2) * (t * m₂) = (16 * d * Kadj ^ 2 * t * m₂) / (4 * Rr ^ 2) := by
      field_simp; ring
    rw [key, div_le_iff₀ (by positivity)]
    have hηR : η * Rr ^ 2 = 16 * d * Kadj ^ 2 * t * m₂ + η := by rw [hRr2]; field_simp
    nlinarith
  calc 8 * U1 + 2 * (ENNReal.ofReal t * ((d : ℝ≥0∞) * (4 * ENNReal.ofReal ((a * δ) ^ 2)))) +
        2 * (ENNReal.ofReal t * ((d : ℝ≥0∞) * (2 * ENNReal.ofReal ED))) +
        2 * d * ENNReal.ofReal (Kadj ^ 2) * ENNReal.ofReal (2 / Rr ^ 2) *
          (ENNReal.ofReal t * ENNReal.ofReal m₂)
      ≤ ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) :=
        add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end Main

end HRS.MS.MainRdPath
