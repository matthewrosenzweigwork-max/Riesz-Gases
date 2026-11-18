import HRS.Main.ThermCond
import HRS.Main.T25PFinal

/-!
# FULLBOUNDS (assembly): abstract d_2 / W_1 / W_2 clauses of `prepared_full_bounds`

Abstract in the initial law: Theorem 2.5 (`prepared_fluctuations_proof`, `prepared_fluctuations_W2_proof`) together
with an initial-rate hypothesis for `(η_N^0, ν)` and the entropy-scale hypothesis `B_N ≤ C_b Nδ_N` gives the
d_2, W_1 and W_2 clauses of `M:prose:L805-835`.  Template: `ThermCond.lean`.

Packet prefix `fb_`.  Nothing here is frozen; no `sorry`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- `B_N > 0` (`B_N = 1 + H + Nδ_N` with `Nδ_N ≥ 1`). -/
theorem fb_B_pos (S : PreparedData d) {N : ℕ} (hN : 1 ≤ N) (f0 : Measure (Config d N)) :
    0 < S.B N f0 := by
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have h1 := (deltaN_basic hd1 S.hs0 S.hsd N hN).1
  unfold PreparedData.B
  have := ENNReal.toReal_nonneg (a := relEntropy f0 (S.refMeasure N 0))
  linarith

/-- The three ratios of Theorem 2.5 under the entropy scale `B_N ≤ C_b Nδ_N`. -/
theorem fb_ratio_facts (S : PreparedData d) {N : ℕ} (hN : 2 ≤ N) (f0 : Measure (Config d N))
    {Cb : ℝ} (hCb : 0 ≤ Cb) (hB : S.B N f0 ≤ Cb * ((N : ℝ) * deltaN d S.s N)) :
    S.B N f0 / Real.sqrt N ≤ Cb * (Real.sqrt N * deltaN d S.s N) ∧
    Real.sqrt (S.B N f0 / N) ≤ Real.sqrt Cb * (Real.sqrt N * deltaN d S.s N) ∧
    (S.B N f0 / N) ^ ((1 : ℝ) / 4) ≤ Cb ^ ((1 : ℝ) / 4) * deltaN d S.s N ^ ((1 : ℝ) / 4) := by
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hδ := therm_deltaN_pos S.hd S.hs0 S.hsd N (by omega)
  have hBp := fb_B_pos S (by omega : 1 ≤ N) f0
  obtain ⟨h1, h2⟩ := therm_ratio_bounds (by omega : 1 ≤ N) hδ hBp hB
  refine ⟨h1, ?_, ?_⟩
  · calc Real.sqrt (S.B N f0 / N) ≤ Real.sqrt (Cb * deltaN d S.s N) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt Cb * Real.sqrt (deltaN d S.s N) := Real.sqrt_mul hCb _
      _ ≤ Real.sqrt Cb * (Real.sqrt N * deltaN d S.s N) :=
        mul_le_mul_of_nonneg_left (deltaN_basic hd1 S.hs0 S.hsd N (by omega)).2 (Real.sqrt_nonneg _)
  · calc (S.B N f0 / N) ^ ((1 : ℝ) / 4) ≤ (Cb * deltaN d S.s N) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (div_nonneg hBp.le (Nat.cast_nonneg N)) h2 (by norm_num)
      _ = Cb ^ ((1 : ℝ) / 4) * deltaN d S.s N ^ ((1 : ℝ) / 4) := Real.mul_rpow hCb hδ.le

/-- The d_2 clause: Theorem 2.5's third bound, the entropy scale and the initial rate `d_2(η_N^0, ν) ≤ K_s r_N`. -/
theorem fb_smooth (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T)
    (Cb Ks : ℝ) (hCb : 0 ≤ Cb) (hKs : 0 ≤ Ks) (rs : ℕ → ℝ) (hrs : ∀ N, 2 ≤ N → 0 ≤ rs N) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        relEntropy (law P X₀) (S.refMeasure N 0) < ⊤ →
        S.B N (law P X₀) ≤ Cb * ((N : ℝ) * deltaN d S.s N) →
      ∀ (ν : Measure (NegSobolev d m)) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
        [IsProbabilityMeasure P'] (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Y₀ Y →
        smoothDist 2 (law P (fun ω => etaE m (X₀ ω) S.μ0)) ν ≤ Ks * rs N →
        smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
          C * (Real.sqrt N * deltaN d S.s N + rs N) := by
  obtain ⟨C0, c0, hC0, hc0, h0⟩ := prepared_fluctuations_proof S m hm T hT
  set K : ℝ := Ks + Cb + Real.sqrt Cb + 1 with hK
  have hK0 : 0 < K := by positivity
  refine ⟨C0 * K, mul_pos hC0 hK0, ?_⟩
  intro a ha N hN Ω _ P _ X₀ W X hSel hfilt hrel hB ν Ω' _ P' _ Y₀ Y hY hini
  have hδ := therm_deltaN_pos S.hd S.hs0 S.hsd N (by omega)
  have hx : 0 ≤ Real.sqrt N * deltaN d S.s N := by positivity
  have hy := hrs N hN
  obtain ⟨hr1, hr2, -⟩ := fb_ratio_facts S hN (law P X₀) hCb hB
  have h3 := (h0 a ha N hN P X₀ W X hSel hfilt hrel ν P' Y₀ Y hY).2
  refine h3.trans ?_
  have hin : smoothDist 2 (law P (fun ω => etaE m (X₀ ω) S.μ0)) ν +
      S.B N (law P X₀) / Real.sqrt N + Real.sqrt (S.B N (law P X₀) / N) ≤
      K * (Real.sqrt N * deltaN d S.s N + rs N) := by
    have hsq : 0 ≤ Real.sqrt Cb := Real.sqrt_nonneg _
    nlinarith [mul_nonneg hKs hy, mul_nonneg hCb hx, mul_nonneg hsq hx, mul_nonneg hx hy]
  calc C0 * _ ≤ C0 * (K * (Real.sqrt N * deltaN d S.s N + rs N)) :=
        mul_le_mul_of_nonneg_left hin hC0.le
    _ = C0 * K * (Real.sqrt N * deltaN d S.s N + rs N) := by ring

/-- The W_1 clause: Theorem 2.5's first bound (with `e^{-ca} ≤ 1`), the entropy scale and the initial rate
`W_1(η_N^0, ν) ≤ K_w r_N`. -/
theorem fb_W1 (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T)
    (Cb Kw : ℝ) (hCb : 0 ≤ Cb) (hKw : 0 ≤ Kw) (rw : ℕ → ℝ) (hrw : ∀ N, 2 ≤ N → 0 ≤ rw N) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        relEntropy (law P X₀) (S.refMeasure N 0) < ⊤ →
        S.B N (law P X₀) ≤ Cb * ((N : ℝ) * deltaN d S.s N) →
      ∀ (ν : Measure (NegSobolev d m)) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
        [IsProbabilityMeasure P'] (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Y₀ Y →
        wassersteinE 1 (law P (fun ω => etaE m (X₀ ω) S.μ0)) ν ≤ ENNReal.ofReal (Kw * rw N) →
        wassersteinE 1 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
          ENNReal.ofReal (C * (Real.sqrt N * deltaN d S.s N + deltaN d S.s N ^ ((1 : ℝ) / 4) +
            rw N)) := by
  obtain ⟨C0, c0, hC0, hc0, h0⟩ := prepared_fluctuations_proof S m hm T hT
  set K : ℝ := Kw + Cb + Cb ^ ((1 : ℝ) / 4) + 1 with hK
  have hK0 : 0 < K := by
    have : 0 ≤ Cb ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hCb _
    positivity
  refine ⟨C0 * K, mul_pos hC0 hK0, ?_⟩
  intro a ha N hN Ω _ P _ X₀ W X hSel hfilt hrel hB ν Ω' _ P' _ Y₀ Y hY hini
  have hδ := therm_deltaN_pos S.hd S.hs0 S.hsd N (by omega)
  have hx : 0 ≤ Real.sqrt N * deltaN d S.s N := by positivity
  have hq : 0 ≤ deltaN d S.s N ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hδ.le _
  have hy := hrw N hN
  have hCb4 : 0 ≤ Cb ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hCb _
  obtain ⟨hr1, -, hr3⟩ := fb_ratio_facts S hN (law P X₀) hCb hB
  have hfin : S.initW m 1 P X₀ ν ≠ ⊤ := by
    unfold PreparedData.initW
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hini
  have hW1 : (S.initW m 1 P X₀ ν).toReal ≤ Kw * rw N := by
    unfold PreparedData.initW
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hKw hy) hini
  have h1 := ((h0 a ha N hN P X₀ W X hSel hfilt hrel ν P' Y₀ Y hY).1 hfin).2
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  have he : Real.exp (-c0 * a) * (S.initW m 1 P X₀ ν).toReal ≤ Kw * rw N := by
    have hexp : Real.exp (-c0 * a) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := mul_nonneg hc0.le ha
      linarith
    calc Real.exp (-c0 * a) * (S.initW m 1 P X₀ ν).toReal ≤ 1 * (S.initW m 1 P X₀ ν).toReal :=
          mul_le_mul_of_nonneg_right hexp ENNReal.toReal_nonneg
      _ ≤ Kw * rw N := by rw [one_mul]; exact hW1
  have hin : Real.exp (-c0 * a) * (S.initW m 1 P X₀ ν).toReal + S.B N (law P X₀) / Real.sqrt N +
      (S.B N (law P X₀) / N) ^ ((1 : ℝ) / 4) ≤
      K * (Real.sqrt N * deltaN d S.s N + deltaN d S.s N ^ ((1 : ℝ) / 4) + rw N) := by
    nlinarith [mul_nonneg hKw hy, mul_nonneg hCb hx, mul_nonneg hCb4 hq, mul_nonneg hx hy,
      mul_nonneg hq hy]
  calc C0 * _ ≤ C0 * (K * (Real.sqrt N * deltaN d S.s N + deltaN d S.s N ^ ((1 : ℝ) / 4) + rw N)) :=
        mul_le_mul_of_nonneg_left hin hC0.le
    _ = C0 * K * (Real.sqrt N * deltaN d S.s N + deltaN d S.s N ^ ((1 : ℝ) / 4) + rw N) := by ring

/-- The d_2 and W_1 clauses together (plan §2.1). -/
theorem fb_smooth_W1 (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T)
    (Cb Ks Kw : ℝ) (hCb : 0 ≤ Cb) (hKs : 0 ≤ Ks) (hKw : 0 ≤ Kw) (rs rw : ℕ → ℝ)
    (hrs : ∀ N, 2 ≤ N → 0 ≤ rs N) (hrw : ∀ N, 2 ≤ N → 0 ≤ rw N) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        relEntropy (law P X₀) (S.refMeasure N 0) < ⊤ →
        S.B N (law P X₀) ≤ Cb * ((N : ℝ) * deltaN d S.s N) →
      ∀ (ν : Measure (NegSobolev d m)) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
        [IsProbabilityMeasure P'] (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Y₀ Y →
        smoothDist 2 (law P (fun ω => etaE m (X₀ ω) S.μ0)) ν ≤ Ks * rs N →
        wassersteinE 1 (law P (fun ω => etaE m (X₀ ω) S.μ0)) ν ≤ ENNReal.ofReal (Kw * rw N) →
        smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
          C * (Real.sqrt N * deltaN d S.s N + rs N) ∧
        wassersteinE 1 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
          ENNReal.ofReal (C * (Real.sqrt N * deltaN d S.s N + deltaN d S.s N ^ ((1 : ℝ) / 4) +
            rw N)) := by
  obtain ⟨C1, hC1, h1⟩ := fb_smooth S m hm T hT Cb Ks hCb hKs rs hrs
  obtain ⟨C2, hC2, h2⟩ := fb_W1 S m hm T hT Cb Kw hCb hKw rw hrw
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, ?_⟩
  intro a ha N hN Ω _ P _ X₀ W X hSel hfilt hrel hB ν Ω' _ P' _ Y₀ Y hY hs hw
  have hδ := therm_deltaN_pos S.hd S.hs0 S.hsd N (by omega)
  have hx : 0 ≤ Real.sqrt N * deltaN d S.s N := by positivity
  have hq : 0 ≤ deltaN d S.s N ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hδ.le _
  refine ⟨(h1 a ha N hN P X₀ W X hSel hfilt hrel hB ν P' Y₀ Y hY hs).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg hx (hrs N hN))),
    (h2 a ha N hN P X₀ W X hSel hfilt hrel hB ν P' Y₀ Y hY hw).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (add_nonneg (add_nonneg hx hq) (hrw N hN))))⟩

/-- The W_2 clause: Theorem 2.5's W_2 bound with `e^{-ca} ≤ 1`, the entropy scale `B_N ≤ C_b Nδ_N`, the
strong scale `J_N ≤ C_j Nδ_N` (for the fixed exponent `p₀`) and the initial rate `W_2(η_N^0, ν) ≤ K_w r_N`. -/
theorem fb_W2 (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T)
    (p₀ : ℝ) (hp₀ : 1 < p₀) (Cb Cj Kw : ℝ) (hCb : 0 ≤ Cb) (hCj : 0 ≤ Cj) (hKw : 0 ≤ Kw)
    (rw : ℕ → ℝ) (hrw : ∀ N, 2 ≤ N → 0 ≤ rw N) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        relEntropy (law P X₀) (S.refMeasure N 0) < ⊤ →
        MemLp (fun Y => (((law P X₀).rnDeriv (S.refMeasure N 0)) Y).toReal) (ENNReal.ofReal p₀)
          (S.refMeasure N 0) →
        S.B N (law P X₀) ≤ Cb * ((N : ℝ) * deltaN d S.s N) →
        S.J N (law P X₀) p₀ ≤ Cj * ((N : ℝ) * deltaN d S.s N) →
      ∀ (ν : Measure (NegSobolev d m)) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
        [IsProbabilityMeasure P'] (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Y₀ Y →
        wassersteinE 2 (law P (fun ω => etaE m (X₀ ω) S.μ0)) ν ≤ ENNReal.ofReal (Kw * rw N) →
        wassersteinE 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
          ENNReal.ofReal (C * (Real.sqrt N * deltaN d S.s N + deltaN d S.s N ^ ((1 : ℝ) / 4) +
            rw N)) := by
  obtain ⟨C0, c0, hC0, hc0, h0⟩ := prepared_fluctuations_W2_proof S m hm T hT p₀ hp₀
  set K : ℝ := Kw + Cj + Cb ^ ((1 : ℝ) / 4) + 1 with hK
  have hCb4 : 0 ≤ Cb ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hCb _
  have hK0 : 0 < K := by positivity
  refine ⟨C0 * K, mul_pos hC0 hK0, ?_⟩
  intro a ha N hN Ω _ P _ X₀ W X hSel hfilt hrel hMem hB hJ ν Ω' _ P' _ Y₀ Y hY hini
  have hδ := therm_deltaN_pos S.hd S.hs0 S.hsd N (by omega)
  have hx : 0 ≤ Real.sqrt N * deltaN d S.s N := by positivity
  have hq : 0 ≤ deltaN d S.s N ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hδ.le _
  have hy := hrw N hN
  obtain ⟨-, -, hr3⟩ := fb_ratio_facts S hN (law P X₀) hCb hB
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsq : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hN0.le).symm
  have hJr : S.J N (law P X₀) p₀ / Real.sqrt N ≤ Cj * (Real.sqrt N * deltaN d S.s N) := by
    rw [div_le_iff₀ hs0]
    calc S.J N (law P X₀) p₀ ≤ Cj * ((N : ℝ) * deltaN d S.s N) := hJ
      _ = Cj * (Real.sqrt N * deltaN d S.s N) * Real.sqrt N := by
        linear_combination (Cj * deltaN d S.s N) * hsq
  have hfin : S.initW m 2 P X₀ ν ≠ ⊤ := by
    unfold PreparedData.initW
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hini
  have hW1 : (S.initW m 2 P X₀ ν).toReal ≤ Kw * rw N := by
    unfold PreparedData.initW
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hKw hy) hini
  have h1 := h0 a ha N hN P X₀ W X hSel hfilt hrel hMem ν P' Y₀ Y hY hfin
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  have he : Real.exp (-c0 * a) * (S.initW m 2 P X₀ ν).toReal ≤ Kw * rw N := by
    have hexp : Real.exp (-c0 * a) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := mul_nonneg hc0.le ha
      linarith
    calc Real.exp (-c0 * a) * (S.initW m 2 P X₀ ν).toReal ≤ 1 * (S.initW m 2 P X₀ ν).toReal :=
          mul_le_mul_of_nonneg_right hexp ENNReal.toReal_nonneg
      _ ≤ Kw * rw N := by rw [one_mul]; exact hW1
  have hin : Real.exp (-c0 * a) * (S.initW m 2 P X₀ ν).toReal + S.J N (law P X₀) p₀ / Real.sqrt N +
      (S.B N (law P X₀) / N) ^ ((1 : ℝ) / 4) ≤
      K * (Real.sqrt N * deltaN d S.s N + deltaN d S.s N ^ ((1 : ℝ) / 4) + rw N) := by
    nlinarith [mul_nonneg hKw hy, mul_nonneg hCj hx, mul_nonneg hCb4 hq, mul_nonneg hx hy,
      mul_nonneg hq hy]
  calc C0 * _ ≤ C0 * (K * (Real.sqrt N * deltaN d S.s N + deltaN d S.s N ^ ((1 : ℝ) / 4) + rw N)) :=
        mul_le_mul_of_nonneg_left hin hC0.le
    _ = C0 * K * (Real.sqrt N * deltaN d S.s N + deltaN d S.s N ^ ((1 : ℝ) / 4) + rw N) := by ring

/-- For `d ≥ 1` and `s = 0` the scale is `δ_N = N⁻¹`. -/
theorem fb_deltaN_zero (hd : 1 ≤ d) (N : ℕ) : deltaN d 0 N = (N : ℝ)⁻¹ := by
  unfold deltaN
  have : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [if_pos this]

/-- For `s = 0`, `d ≥ 1`, `N ≥ 1`: `√N δ_N ≤ N^{-1/4}` and `δ_N^{1/4} = N^{-1/4}`. -/
theorem fb_zero_rates (hd : 1 ≤ d) {N : ℕ} (hN : 1 ≤ N) :
    Real.sqrt N * deltaN d 0 N ≤ (N : ℝ) ^ (-(1 : ℝ) / 4) ∧
    deltaN d 0 N ^ ((1 : ℝ) / 4) = (N : ℝ) ^ (-(1 : ℝ) / 4) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [fb_deltaN_zero hd N]
  constructor
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  · rw [← Real.rpow_neg_one, ← Real.rpow_mul hN0.le]
    norm_num

end Main

end HRS

end
