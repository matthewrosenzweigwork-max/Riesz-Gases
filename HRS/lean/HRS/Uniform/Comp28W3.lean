import HRS.Uniform.Comp28W2

/-!
# COMP-28, Wasserstein part, W3: the history bound `E‖∫_0^a V(a,r) dD_r‖² ≤ K² E∫_0^a w_a² ‖Sd_r‖₁ dr`

Riemann sums of an `H`-valued Hilbert martingale against deterministic operators are orthogonal sums
(`riemann_sq_le`), each cell contributing at most `‖W_i‖²` times the covariation trace of the cell; since `w_a` is increasing,
`‖V(a,r_i)‖² ≤ K² w_a(σ)²` for `σ` in the `i`-th cell, and the `L²`-limit gives `hist_bound`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Comp28

open HRS HRS.Uniform HRS.Uniform.Q07c

section Hist

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

lemma lintegral_enorm_sq_eq_ofReal {f : Ω → H} (hf : MemLp f 2 P) :
    ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P = ENNReal.ofReal (∫ ω, ‖f ω‖ ^ 2 ∂P) := by
  rw [ofReal_integral_eq_lintegral_ofReal hf.norm.integrable_sq (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
  refine lintegral_congr fun ω => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

lemma lintegral_enorm_sq_add_of_orth {A B : Ω → H} (hA : MemLp A 2 P) (hB : MemLp B 2 P)
    (h : ∫ ω, inner ℝ (A ω) (B ω) ∂P = 0) :
    ∫⁻ ω, ‖A ω + B ω‖ₑ ^ 2 ∂P = ∫⁻ ω, ‖A ω‖ₑ ^ 2 ∂P + ∫⁻ ω, ‖B ω‖ₑ ^ 2 ∂P := by
  have hAB : MemLp (fun ω => A ω + B ω) 2 P := hA.add hB
  rw [lintegral_enorm_sq_eq_ofReal hAB, lintegral_enorm_sq_eq_ofReal hA,
    lintegral_enorm_sq_eq_ofReal hB]
  have hint : Integrable (fun ω => inner ℝ (A ω) (B ω)) P :=
    (hA.norm.integrable_mul hB.norm).mono' (hA.aestronglyMeasurable.inner hB.aestronglyMeasurable)
      (ae_of_all _ fun ω => by simpa using abs_real_inner_le_norm (A ω) (B ω))
  have hi2 : Integrable (fun ω => ‖A ω‖ ^ 2 + ‖B ω‖ ^ 2) P :=
    hA.norm.integrable_sq.add hB.norm.integrable_sq
  have e : ∀ ω, ‖A ω + B ω‖ ^ 2 = ‖A ω‖ ^ 2 + ‖B ω‖ ^ 2 + 2 * inner ℝ (A ω) (B ω) := fun ω => by
    rw [norm_add_sq_real]; ring
  simp_rw [e]
  rw [integral_add hi2 (hint.const_mul 2),
    integral_add hA.norm.integrable_sq hB.norm.integrable_sq, integral_const_mul, h, mul_zero, add_zero,
    ENNReal.ofReal_add (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)]

section Riem

variable {D : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} {S : ℝ}

open HRS.Uniform.Q48d in
/-- The Riemann sum along a partition inside `[0,u]` is `ℱ_u`-measurable. -/
lemma measurable_riemann (hD : IsHilbertMartingaleWithCovariation P ℱ S D Sg)
    (V : ℝ → ℝ → H →L[ℝ] H) (a : ℝ) {n : ℕ} (r : Fin (n + 1) → ℝ) {u : ℝ} (hu : ∀ i, r i ≤ u) :
    Measurable[ℱ u] (fun ω => riemannSum V (ContinuousLinearMap.id ℝ H) D a r ω) := by
  simp_rw [riemannSum_id]
  refine Finset.measurable_sum _ fun i _ => ?_
  have h1 : Measurable[ℱ u] (D (r i.succ)) := (measurable_D hD _).mono (ℱ.mono (hu _)) le_rfl
  have h0 : Measurable[ℱ u] (D (r i.castSucc)) := (measurable_D hD _).mono (ℱ.mono (hu _)) le_rfl
  exact (V a (r i.castSucc)).continuous.measurable.comp (h1.sub h0)

open HRS.Uniform.Q48d in
lemma memLp_riemann (hD : IsHilbertMartingaleWithCovariation P ℱ S D Sg)
    (V : ℝ → ℝ → H →L[ℝ] H) (a : ℝ) {n : ℕ} (r : Fin (n + 1) → ℝ) (hr0 : ∀ i, 0 ≤ r i)
    (hrS : ∀ i, r i ≤ S) :
    MemLp (fun ω => riemannSum V (ContinuousLinearMap.id ℝ H) D a r ω) 2 P := by
  simp_rw [riemannSum_id]
  have hS : 0 ≤ S := (hr0 0).trans (hrS 0)
  refine memLp_finsetSum _ fun i _ => ?_
  have h1 := memLp_D hD hS (hr0 i.succ) (hrS _)
  have h0 := memLp_D hD hS (hr0 i.castSucc) (hrS _)
  exact (V a (r i.castSucc)).comp_memLp' (h1.sub h0)

open HRS.Uniform.Q48d in
theorem riemann_sq_le (hD : IsHilbertMartingaleWithCovariation P ℱ S D Sg) (V : ℝ → ℝ → H →L[ℝ] H) (a : ℝ) :
    ∀ (n : ℕ) (r : Fin (n + 1) → ℝ), Monotone r → 0 ≤ r 0 → r (Fin.last n) ≤ S →
      ∫⁻ ω, ‖riemannSum V (ContinuousLinearMap.id ℝ H) D a r ω‖ₑ ^ 2 ∂P ≤
        ∑ i : Fin n, ENNReal.ofReal (‖V a (r i.castSucc)‖ ^ 2) *
          ∫⁻ ω, (∫⁻ σ in Set.Ioc (r i.castSucc) (r i.succ), ENNReal.ofReal (traceNormForm (Sg σ ω))) ∂P := by
  intro n
  induction n with
  | zero =>
    intro r _ _ _
    simp [riemannSum_id]
  | succ n ih =>
    intro r hrm hr0 hrS
    set r' : Fin (n + 1) → ℝ := fun i => r i.castSucc with hr'
    have hr'm : Monotone r' := fun i j hij => hrm (Fin.castSucc_le_castSucc_iff.2 hij)
    have hr'0 : 0 ≤ r' 0 := hr0
    have hall0 : ∀ i, 0 ≤ r i := fun i => hr0.trans (hrm (Fin.zero_le i))
    have hallS : ∀ i, r i ≤ S := fun i => (hrm (Fin.le_last i)).trans hrS
    have hr'S : r' (Fin.last n) ≤ S := hallS _
    set s : ℝ := r (Fin.last n).castSucc with hs
    set s' : ℝ := r (Fin.last (n + 1)) with hs'
    have hss' : s ≤ s' := hrm (Fin.le_last _)
    have hs0 : 0 ≤ s := hall0 _
    have hsplit : ∀ ω, riemannSum V (ContinuousLinearMap.id ℝ H) D a r ω =
        riemannSum V (ContinuousLinearMap.id ℝ H) D a r' ω +
          V a s (D s' ω - D s ω) := by
      intro ω
      simp_rw [riemannSum_id]
      rw [Fin.sum_univ_castSucc]
      congr 1
    have hAu : ∀ i, r' i ≤ s := fun i => hrm (by
      show i.castSucc ≤ (Fin.last n).castSucc
      exact Fin.castSucc_le_castSucc_iff.2 (Fin.le_last i))
    have hA : Measurable[ℱ s] (fun ω => riemannSum V (ContinuousLinearMap.id ℝ H) D a r' ω) :=
      measurable_riemann hD V a r' hAu
    have hA2 := memLp_riemann hD V a r' (fun i => hall0 _) (fun i => hallS _)
    set W : H →L[ℝ] H := V a s with hW
    have hS0 : 0 ≤ S := hs0.trans (hss'.trans (hallS _))
    have hΔ2 : MemLp (fun ω => D s' ω - D s ω) 2 P :=
      (memLp_D hD hS0 (hs0.trans hss') (hallS _)).sub (memLp_D hD hS0 hs0 (hss'.trans (hallS _)))
    have hB2 : MemLp (fun ω => W (D s' ω - D s ω)) 2 P := W.comp_memLp' hΔ2
    -- orthogonality
    have horth : ∫ ω, inner ℝ (riemannSum V (ContinuousLinearMap.id ℝ H) D a r' ω)
        (W (D s' ω - D s ω)) ∂P = 0 := by
      have e : ∀ ω, inner ℝ (riemannSum V (ContinuousLinearMap.id ℝ H) D a r' ω) (W (D s' ω - D s ω)) =
          inner ℝ ((ContinuousLinearMap.adjoint W) (riemannSum V (ContinuousLinearMap.id ℝ H) D a r' ω))
            (D s' ω - D s ω) := fun ω => by
        rw [ContinuousLinearMap.adjoint_inner_left]
      simp_rw [e]
      refine orth_vec hD hs0 hss' (hallS _) ?_ ?_
      · exact (ContinuousLinearMap.adjoint W).continuous.measurable.comp hA
      · exact (ContinuousLinearMap.adjoint W).comp_memLp' hA2
    have hpyth := lintegral_enorm_sq_add_of_orth hA2 hB2 horth
    have hAB : (fun ω => ‖riemannSum V (ContinuousLinearMap.id ℝ H) D a r ω‖ₑ ^ 2) =
        fun ω => ‖riemannSum V (ContinuousLinearMap.id ℝ H) D a r' ω + W (D s' ω - D s ω)‖ₑ ^ 2 := by
      funext ω; rw [hsplit ω]
    rw [hAB, hpyth]
    -- the last cell
    have hlast : ∫⁻ ω, ‖W (D s' ω - D s ω)‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (‖W‖ ^ 2) *
        ∫⁻ ω, (∫⁻ σ in Set.Ioc s s', ENNReal.ofReal (traceNormForm (Sg σ ω))) ∂P := by
      calc ∫⁻ ω, ‖W (D s' ω - D s ω)‖ₑ ^ 2 ∂P
          ≤ ∫⁻ ω, ENNReal.ofReal (‖W‖ ^ 2) * ‖D s' ω - D s ω‖ₑ ^ 2 ∂P := by
            refine lintegral_mono fun ω => ?_
            have h1 : ‖W (D s' ω - D s ω)‖ₑ ≤ ENNReal.ofReal ‖W‖ * ‖D s' ω - D s ω‖ₑ := by
              rw [← ofReal_norm, ← ofReal_norm (D s' ω - D s ω), ← ENNReal.ofReal_mul (norm_nonneg _)]
              exact ENNReal.ofReal_le_ofReal (W.le_opNorm _)
            calc ‖W (D s' ω - D s ω)‖ₑ ^ 2 ≤ (ENNReal.ofReal ‖W‖ * ‖D s' ω - D s ω‖ₑ) ^ 2 :=
                  pow_le_pow_left' h1 2
              _ = ENNReal.ofReal (‖W‖ ^ 2) * ‖D s' ω - D s ω‖ₑ ^ 2 := by
                  rw [mul_pow, ENNReal.ofReal_pow (norm_nonneg _)]
        _ = ENNReal.ofReal (‖W‖ ^ 2) * ∫⁻ ω, ‖D s' ω - D s ω‖ₑ ^ 2 ∂P :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ _ := mul_le_mul' le_rfl (sq_incr hD hs0 hss' (hallS _))
    have hih := ih r' hr'm hr'0 hr'S
    rw [Fin.sum_univ_castSucc]
    refine add_le_add ?_ hlast
    refine hih.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hr', Fin.succ_castSucc]

end Riem


section Hist2

variable {D : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} {S : ℝ}

open HRS.Uniform.Q48d in
lemma eLpNorm_two_eq' {f : Ω → H} (hf : AEStronglyMeasurable f P) :
    eLpNorm f 2 P = (∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp [ENNReal.rpow_two]

/-- Riemann sums are bounded by the weighted covariation: the cellwise bound with `w_a` increasing. -/
lemma riemann_sq_le_weighted (hD : IsHilbertMartingaleWithCovariation P ℱ S D Sg) {a K c : ℝ} (hK : 0 ≤ K)
    (hc : 0 ≤ c) (V : ℝ → ℝ → H →L[ℝ] H)
    (hV : ∀ r : ℝ, 0 ≤ r → r ≤ a → ‖V a r‖ ≤ K * Real.exp (-c * (a - r)))
    {n : ℕ} (r : Fin (n + 1) → ℝ) (hrm : Monotone r) (h0 : r 0 = 0) (hl : r (Fin.last n) = a)
    (haS : a ≤ S) :
    ∫⁻ ω, ‖riemannSum V (ContinuousLinearMap.id ℝ H) D a r ω‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (K ^ 2) *
        ∫⁻ ω, (∫⁻ σ in Set.Icc 0 a, ENNReal.ofReal (wt c a σ ^ 2 * traceNormForm (Sg σ ω))) ∂P := by
  have hbase := riemann_sq_le hD V a n r hrm (by rw [h0]) (by rw [hl]; exact haS)
  refine hbase.trans ?_
  have hjm : ∀ x y : H, Measurable (fun p : Ω × ℝ => Sg p.2 p.1 x y) := fun x y =>
    (hD.sigma_meas x y).comp (measurable_swap (α := Ω) (β := ℝ))
  have hmeasTr : Measurable (fun p : Ω × ℝ => traceNormForm (Sg p.2 p.1)) :=
    measurable_traceNormForm (H := H) (α := Ω × ℝ) (fun p => Sg p.2 p.1) hjm
  have hmeasG : Measurable (fun p : Ω × ℝ => ENNReal.ofReal (wt c a p.2 ^ 2 * traceNormForm (Sg p.2 p.1))) :=
    (((wt_continuous c a).pow 2).measurable.comp measurable_snd |>.mul hmeasTr).ennreal_ofReal
  have hcellmeas : ∀ i : Fin n, Measurable (fun ω => ∫⁻ σ in Set.Ioc (r i.castSucc) (r i.succ),
      ENNReal.ofReal (wt c a σ ^ 2 * traceNormForm (Sg σ ω))) := fun i =>
    hmeasG.lintegral_prod_right' (ν := volume.restrict (Set.Ioc (r i.castSucc) (r i.succ)))
  -- step 1: cellwise
  have hstep1 : ∀ i : Fin n, ENNReal.ofReal (‖V a (r i.castSucc)‖ ^ 2) *
      ∫⁻ ω, (∫⁻ σ in Set.Ioc (r i.castSucc) (r i.succ), ENNReal.ofReal (traceNormForm (Sg σ ω))) ∂P ≤
      ENNReal.ofReal (K ^ 2) * ∫⁻ ω, (∫⁻ σ in Set.Ioc (r i.castSucc) (r i.succ),
        ENNReal.ofReal (wt c a σ ^ 2 * traceNormForm (Sg σ ω))) ∂P := by
    intro i
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ω => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioc fun σ hσ => ?_
    have hri0 : 0 ≤ r i.castSucc := h0 ▸ hrm (Fin.zero_le _)
    have hrile : r i.castSucc ≤ a := hl ▸ hrm (Fin.le_last _)
    have hσa : σ ≤ a := hσ.2.trans (hl ▸ hrm (Fin.le_last _))
    have hw : Real.exp (-c * (a - r i.castSucc)) ≤ wt c a σ := by
      unfold wt
      rw [Real.exp_le_exp, max_eq_left (by linarith)]
      nlinarith [hσ.1]
    have hn : ‖V a (r i.castSucc)‖ ^ 2 ≤ K ^ 2 * wt c a σ ^ 2 := by
      have h1 := hV _ hri0 hrile
      have h2 : ‖V a (r i.castSucc)‖ ≤ K * wt c a σ := h1.trans (mul_le_mul_of_nonneg_left hw hK)
      calc ‖V a (r i.castSucc)‖ ^ 2 ≤ (K * wt c a σ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
        _ = K ^ 2 * wt c a σ ^ 2 := by ring
    rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖V a (r i.castSucc)‖ ^ 2 * traceNormForm (Sg σ ω)
        ≤ (K ^ 2 * wt c a σ ^ 2) * traceNormForm (Sg σ ω) :=
          mul_le_mul_of_nonneg_right hn (traceNormForm_nonneg _)
      _ = K ^ 2 * (wt c a σ ^ 2 * traceNormForm (Sg σ ω)) := by ring
  refine (Finset.sum_le_sum fun i _ => hstep1 i).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul' le_rfl ?_
  rw [← lintegral_finset_sum' _ fun i _ => (hcellmeas i).aemeasurable]
  refine lintegral_mono fun ω => ?_
  -- cells are disjoint subsets of `Icc 0 a`
  have hdisj : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
      (fun i : Fin n => Set.Ioc (r i.castSucc) (r i.succ)) := by
    intro i _ j _ hij
    rw [Function.onFun, Set.disjoint_left]
    intro σ h1 h2
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have : r i.succ ≤ r j.castSucc := hrm (Fin.succ_le_castSucc_iff.2 hlt)
      exact absurd (h2.1) (not_lt.2 (h1.2.trans this))
    · have : r j.succ ≤ r i.castSucc := hrm (Fin.succ_le_castSucc_iff.2 hgt)
      exact absurd (h1.1) (not_lt.2 (h2.2.trans this))
  rw [← lintegral_biUnion_finset hdisj (fun i _ => measurableSet_Ioc)]
  refine lintegral_mono_set ?_
  intro σ hσ
  simp only [Finset.mem_coe, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion] at hσ
  obtain ⟨i, hi⟩ := hσ
  have hri0 : 0 ≤ r i.castSucc := h0 ▸ hrm (Fin.zero_le _)
  exact ⟨hri0.trans hi.1.le, hi.2.trans (hl ▸ hrm (Fin.le_last _))⟩

end Hist2


section Hist3

variable {D : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} {S : ℝ}

open HRS.Uniform.Q48d in
/-- **The history bound.** -/
theorem hist_bound (hD : IsHilbertMartingaleWithCovariation P ℱ S D Sg) {a K c : ℝ} (ha : 0 ≤ a)
    (haS : a ≤ S) (hK : 0 ≤ K) (hc : 0 ≤ c) (V : ℝ → ℝ → H →L[ℝ] H)
    (hV : ∀ r : ℝ, 0 ≤ r → r ≤ a → ‖V a r‖ ≤ K * Real.exp (-c * (a - r)))
    {Y : Ω → H} (hYm : AEStronglyMeasurable Y P)
    (hY : IsStochConv P V (ContinuousLinearMap.id ℝ H) D 0 a Y) :
    ∫⁻ ω, ‖Y ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (K ^ 2) *
      ∫⁻ ω, (∫⁻ σ in Set.Icc 0 a, ENNReal.ofReal (wt c a σ ^ 2 * traceNormForm (Sg σ ω))) ∂P := by
  set J : ℝ≥0∞ := ∫⁻ ω, (∫⁻ σ in Set.Icc 0 a, ENNReal.ofReal (wt c a σ ^ 2 * traceNormForm (Sg σ ω))) ∂P
    with hJ
  have hDm : ∀ τ ∈ Set.Icc (0 : ℝ) a, AEStronglyMeasurable (D τ) P := fun τ _ =>
    (measurable_of_isHM hD τ).aestronglyMeasurable
  have hSC := (isStochConv_iff hYm hDm).1 hY
  -- the bound on `eLpNorm`
  have hmain : eLpNorm Y 2 P ≤ (ENNReal.ofReal (K ^ 2) * J) ^ (1 / 2 : ℝ) := by
    refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
    have hη2 : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
    obtain ⟨δ, hδ, hδ'⟩ := hSC (η : ℝ) hη2
    obtain ⟨n, r, h0, hl, hm, hmesh⟩ := exists_part ha hδ
    have hRm := aesm_riemannSum V hDm h0 hl hm
    have h1 := hδ' n r h0 hl hm hmesh
    have h2 : eLpNorm (fun ω => riemannSum V (ContinuousLinearMap.id ℝ H) D a r ω) 2 P ≤
        (ENNReal.ofReal (K ^ 2) * J) ^ (1 / 2 : ℝ) := by
      rw [eLpNorm_two_eq' hRm]
      exact ENNReal.rpow_le_rpow (riemann_sq_le_weighted hD hK hc V hV r hm h0 hl haS) (by norm_num)
    have hsum : eLpNorm Y 2 P ≤ eLpNorm (fun ω => Y ω - riemannSum V (ContinuousLinearMap.id ℝ H) D a r ω) 2 P +
        eLpNorm (fun ω => riemannSum V (ContinuousLinearMap.id ℝ H) D a r ω) 2 P := by
      have e : Y = (fun ω => Y ω - riemannSum V (ContinuousLinearMap.id ℝ H) D a r ω) +
          (fun ω => riemannSum V (ContinuousLinearMap.id ℝ H) D a r ω) := by
        funext ω; simp
      conv_lhs => rw [e]
      exact eLpNorm_add_le (by norm_num)
    calc eLpNorm Y 2 P ≤ _ := hsum
      _ ≤ ENNReal.ofReal (η : ℝ) + (ENNReal.ofReal (K ^ 2) * J) ^ (1 / 2 : ℝ) := add_le_add h1.le h2
      _ = (ENNReal.ofReal (K ^ 2) * J) ^ (1 / 2 : ℝ) + η := by
          rw [add_comm, ENNReal.ofReal_coe_nnreal]
  rw [eLpNorm_two_eq' hYm] at hmain
  have := ENNReal.rpow_le_rpow hmain (show (0 : ℝ) ≤ 2 by norm_num)
  rwa [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
    ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one] at this

end Hist3

end Hist

end HRS.Uniform.Comp28
