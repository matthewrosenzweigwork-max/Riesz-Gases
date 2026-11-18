import HRS.Prob.Metrics

/-!
# Packet `s7_WQ_weak_ui_wasserstein`, helper 1: quantisation couplings in `W_q`

Generalisation of the `W_2` machinery of `HRS/Prob/HilbertCLT.lean` (`HilbertCLTAux`, a smooth partition of unity
`pF` about a dense sequence, the finite quantisation `quantMeas`, the coupling of a measure with its quantisation, the
optimal-style coupling of two discrete measures on a common finite set) to a separable Banach space and an
exponent `q >= 1`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.WQ

open HRS

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

section Basic

lemma wq_comm_aux (p : ℝ) (P Q : Measure B) :
    wassersteinE p P Q ≤ wassersteinE p Q P := by
  refine le_iInf fun π => ?_
  have hsw : IsCoupling (π.1.map Prod.swap) P Q := by
    refine ⟨?_, ?_⟩
    · rw [Measure.map_map measurable_fst measurable_swap]
      exact π.2.2
    · rw [Measure.map_map measurable_snd measurable_swap]
      exact π.2.1
  refine (wassersteinE_le_cost (p := p) hsw).trans (le_of_eq ?_)
  congr 1
  have hm : Measurable fun z : B × B => ENNReal.ofReal (‖z.1 - z.2‖ ^ p) :=
    ENNReal.measurable_ofReal.comp (((measurable_fst.sub measurable_snd).norm).pow_const p)
  rw [lintegral_map hm measurable_swap]
  congr 1; ext z
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [norm_sub_rev]

lemma wq_comm (p : ℝ) (P Q : Measure B) : wassersteinE p P Q = wassersteinE p Q P :=
  le_antisymm (wq_comm_aux p P Q) (wq_comm_aux p Q P)



/-- A coupling whose `q`-cost is at most `theta^q` bounds `W_q` by `theta`. -/
lemma wq_le_of_cost {q : ℝ} (hq : 1 ≤ q) {ρ ν : Measure B} {π : Measure (B × B)}
    (hπ : IsCoupling π ρ ν) {c θ : ℝ} (hθ : 0 ≤ θ) (hcθ : c ≤ θ ^ q)
    (hc : ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ q) ∂π ≤ ENNReal.ofReal c) :
    wassersteinE q ρ ν ≤ ENNReal.ofReal θ := by
  have hq0 : 0 < q := by linarith
  refine (wassersteinE_le_cost (p := q) hπ).trans ?_
  calc (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ q) ∂π) ^ (1 / q)
      ≤ (ENNReal.ofReal (θ ^ q)) ^ (1 / q) :=
        ENNReal.rpow_le_rpow (hc.trans (ENNReal.ofReal_le_ofReal hcθ)) (by positivity)
    _ = ENNReal.ofReal θ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hθ q) (by positivity),
          ← Real.rpow_mul hθ, mul_one_div_cancel hq0.ne', Real.rpow_one]

end Basic

section Quant

lemma f_le_one {L : ℕ} {f : Fin L → B → ℝ} (hf0 : ∀ k x, 0 ≤ f k x) (hf1 : ∀ x, ∑ k, f k x = 1)
    (k : Fin L) (x : B) : f k x ≤ 1 := by
  rw [← hf1 x]
  exact Finset.single_le_sum (f := fun j => f j x) (fun j _ => hf0 j x) (Finset.mem_univ k)

lemma integrable_f {L : ℕ} (ρ : Measure B) [IsProbabilityMeasure ρ] {f : Fin L → B → ℝ}
    (hfm : ∀ k, Measurable (f k)) (hf0 : ∀ k x, 0 ≤ f k x) (hf1 : ∀ x, ∑ k, f k x = 1) (k : Fin L) :
    Integrable (f k) ρ := by
  refine Integrable.of_bound (C := 1) (hfm k).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hf0 k x)]
  exact f_le_one hf0 hf1 k x

lemma quant_coupling {L : ℕ} (ρ : Measure B) [IsProbabilityMeasure ρ] (f : Fin L → B → ℝ)
    (hfm : ∀ k, Measurable (f k)) (hf0 : ∀ k x, 0 ≤ f k x) (hf1 : ∀ x, ∑ k, f k x = 1)
    (a : Fin L → B) :
    IsCoupling (∑ k, (ρ.withDensity (fun x => ENNReal.ofReal (f k x))).map (fun x => (x, a k)))
      ρ (∑ k, ENNReal.ofReal (∫ x, f k x ∂ρ) • Measure.dirac (a k)) := by
  have hmk : ∀ k, Measurable fun x : B => (x, a k) := fun k => measurable_id.prodMk measurable_const
  constructor
  · rw [Measure.map_finset_sum' measurable_fst.aemeasurable]
    have : ∀ k, ((ρ.withDensity (fun x => ENNReal.ofReal (f k x))).map (fun x => (x, a k))).map
        Prod.fst = ρ.withDensity (fun x => ENNReal.ofReal (f k x)) := by
      intro k
      rw [Measure.map_map measurable_fst (hmk k)]
      exact Measure.map_id
    simp_rw [this]
    ext s hs
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    simp_rw [withDensity_apply _ hs]
    rw [← lintegral_finsetSum (μ := ρ.restrict s) Finset.univ
      (f := fun k x => ENNReal.ofReal (f k x)) (fun k _ => (ENNReal.measurable_ofReal.comp (hfm k)))]
    have : ∀ x, ∑ k, ENNReal.ofReal (f k x) = 1 := by
      intro x
      rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hf0 k x), hf1 x, ENNReal.ofReal_one]
    simp_rw [this]
    simp
  · rw [Measure.map_finset_sum' measurable_snd.aemeasurable]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Measure.map_map measurable_snd (hmk k)]
    have : (Prod.snd ∘ fun x : B => (x, a k)) = fun _ => a k := rfl
    rw [this, Measure.map_const, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    congr 1
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_f ρ hfm hf0 hf1 k)
      (Filter.Eventually.of_forall fun x => hf0 k x)]


/-- Plateau bump of radius `δ` about `c i`. -/
def psiF (δ : ℝ) (c : ℕ → B) (i : ℕ) (x : B) : ℝ := max 0 (min 1 (2 - 2 * ‖x - c i‖ / δ))

/-- The tail product `∏_{j<N} (1 - ψ_j)`. -/
def tailF (δ : ℝ) (c : ℕ → B) (N : ℕ) (x : B) : ℝ := ∏ j ∈ Finset.range N, (1 - psiF δ c j x)

/-- The partition-of-unity piece `ψ_k ∏_{j<k}(1-ψ_j)`. -/
def phiF (δ : ℝ) (c : ℕ → B) (k : ℕ) (x : B) : ℝ := psiF δ c k x * tailF δ c k x

/-- The finite partition of unity `φ_0,…,φ_{N-1}, tail_N`. -/
def pF (δ : ℝ) (c : ℕ → B) (N : ℕ) (k : Fin (N + 1)) (x : B) : ℝ :=
  if k.val < N then phiF δ c k.val x else tailF δ c N x

/-- The anchor points `c_0,…,c_{N-1}, 0`. -/
def aF (c : ℕ → B) (N : ℕ) (k : Fin (N + 1)) : B := if k.val < N then c k.val else 0

lemma continuous_psiF (δ : ℝ) (c : ℕ → B) (i : ℕ) : Continuous (psiF δ c i) := by
  unfold psiF; fun_prop

lemma psiF_nonneg (δ : ℝ) (c : ℕ → B) (i : ℕ) (x : B) : 0 ≤ psiF δ c i x := le_max_left _ _

lemma psiF_le_one (δ : ℝ) (c : ℕ → B) (i : ℕ) (x : B) : psiF δ c i x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma psiF_eq_one {δ : ℝ} (hδ : 0 < δ) (c : ℕ → B) (i : ℕ) (x : B) (h : ‖x - c i‖ ≤ δ / 2) :
    psiF δ c i x = 1 := by
  unfold psiF
  have : 1 ≤ 2 - 2 * ‖x - c i‖ / δ := by
    have h1 : 2 * ‖x - c i‖ / δ ≤ 1 := by
      rw [div_le_iff₀ hδ]; nlinarith
    linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

lemma lt_of_psiF_ne_zero {δ : ℝ} (hδ : 0 < δ) (c : ℕ → B) (i : ℕ) (x : B)
    (h : psiF δ c i x ≠ 0) : ‖x - c i‖ < δ := by
  by_contra hc
  rw [not_lt] at hc
  apply h
  unfold psiF
  have : 2 - 2 * ‖x - c i‖ / δ ≤ 0 := by
    have : 2 * ‖x - c i‖ / δ ≥ 2 := by
      rw [ge_iff_le, le_div_iff₀ hδ]; nlinarith
    linarith
  rw [max_eq_left (le_trans (min_le_right _ _) this)]

lemma tailF_nonneg (δ : ℝ) (c : ℕ → B) (N : ℕ) (x : B) : 0 ≤ tailF δ c N x :=
  Finset.prod_nonneg fun j _ => sub_nonneg.2 (psiF_le_one δ c j x)

lemma tailF_le_one (δ : ℝ) (c : ℕ → B) (N : ℕ) (x : B) : tailF δ c N x ≤ 1 :=
  Finset.prod_le_one₀ (fun j _ => sub_nonneg.2 (psiF_le_one δ c j x))
    fun j _ => sub_le_self _ (psiF_nonneg δ c j x)

lemma continuous_tailF (δ : ℝ) (c : ℕ → B) (N : ℕ) : Continuous (tailF δ c N) := by
  unfold tailF
  exact continuous_finsetProd _ fun j _ => continuous_const.sub (continuous_psiF δ c j)

lemma tailF_succ (δ : ℝ) (c : ℕ → B) (N : ℕ) (x : B) :
    tailF δ c (N + 1) x = tailF δ c N x * (1 - psiF δ c N x) := by
  unfold tailF; rw [Finset.prod_range_succ]

lemma tailF_anti (δ : ℝ) (c : ℕ → B) (x : B) : Antitone fun N => tailF δ c N x := by
  refine antitone_nat_of_succ_le fun N => ?_
  rw [tailF_succ]
  have := tailF_nonneg δ c N x
  have := psiF_nonneg δ c N x
  nlinarith

lemma sum_phiF (δ : ℝ) (c : ℕ → B) (N : ℕ) (x : B) :
    ∑ k ∈ Finset.range N, phiF δ c k x + tailF δ c N x = 1 := by
  induction N with
  | zero => simp [tailF]
  | succ n ih =>
    rw [Finset.sum_range_succ, tailF_succ]
    unfold phiF at *
    nlinarith

lemma phiF_nonneg (δ : ℝ) (c : ℕ → B) (k : ℕ) (x : B) : 0 ≤ phiF δ c k x :=
  mul_nonneg (psiF_nonneg δ c k x) (tailF_nonneg δ c k x)

lemma continuous_phiF (δ : ℝ) (c : ℕ → B) (k : ℕ) : Continuous (phiF δ c k) :=
  (continuous_psiF δ c k).mul (continuous_tailF δ c k)

lemma pF_nonneg (δ : ℝ) (c : ℕ → B) (N : ℕ) (k : Fin (N + 1)) (x : B) : 0 ≤ pF δ c N k x := by
  unfold pF; split_ifs
  exacts [phiF_nonneg δ c _ x, tailF_nonneg δ c N x]

lemma continuous_pF (δ : ℝ) (c : ℕ → B) (N : ℕ) (k : Fin (N + 1)) : Continuous (pF δ c N k) := by
  unfold pF; split_ifs
  exacts [continuous_phiF δ c _, continuous_tailF δ c N]

lemma sum_pF (δ : ℝ) (c : ℕ → B) (N : ℕ) (x : B) : ∑ k : Fin (N + 1), pF δ c N k x = 1 := by
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ k : Fin N, pF δ c N k.castSucc x = phiF δ c k.val x := by
    intro k; simp [pF, k.2]
  have h2 : pF δ c N (Fin.last N) x = tailF δ c N x := by simp [pF]
  simp only [h1, h2]
  rw [Fin.sum_univ_eq_sum_range (fun k => phiF δ c k x) N]
  exact sum_phiF δ c N x

lemma tailF_eventually_zero {δ : ℝ} (hδ : 0 < δ) {c : ℕ → B} (hc : DenseRange c) (x : B) :
    ∃ N₀, ∀ N ≥ N₀, tailF δ c N x = 0 := by
  obtain ⟨i, hi⟩ := hc.exists_dist_lt x (half_pos hδ)
  refine ⟨i + 1, fun N hN => ?_⟩
  unfold tailF
  refine Finset.prod_eq_zero (i := i) (Finset.mem_range.2 (by omega)) ?_
  rw [psiF_eq_one hδ c i x (by rw [dist_eq_norm] at hi; exact hi.le), sub_self]

lemma tailF_eq_one_of_far {δ : ℝ} (hδ : 0 < δ) (c : ℕ → B) (N : ℕ) (x : B)
    (h : ∀ j < N, δ ≤ ‖x - c j‖) : tailF δ c N x = 1 := by
  unfold tailF
  refine Finset.prod_eq_one fun j hj => ?_
  have : psiF δ c j x = 0 := by
    by_contra hne
    exact absurd (lt_of_psiF_ne_zero hδ c j x hne) (not_lt.2 (h j (Finset.mem_range.1 hj)))
  rw [this, sub_zero]

lemma norm_le_of_tailF_ne_one {δ : ℝ} (hδ : 0 < δ) (c : ℕ → B) (N : ℕ) (x : B)
    (h : tailF δ c N x ≠ 1) : ‖x‖ ≤ ∑ j ∈ Finset.range N, ‖c j‖ + δ := by
  by_contra hcon
  apply h
  refine tailF_eq_one_of_far hδ c N x fun j hj => ?_
  by_contra hlt
  rw [not_le] at hlt
  apply hcon
  have h1 : ‖x‖ ≤ ‖x - c j‖ + ‖c j‖ := by
    calc ‖x‖ = ‖(x - c j) + c j‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have h2 : ‖c j‖ ≤ ∑ j ∈ Finset.range N, ‖c j‖ :=
    Finset.single_le_sum (f := fun j => ‖c j‖) (fun _ _ => norm_nonneg _) (Finset.mem_range.2 hj)
  linarith


lemma measurable_pF (δ : ℝ) (c : ℕ → B) (N : ℕ) (k : Fin (N + 1)) : Measurable (pF δ c N k) :=
  (continuous_pF δ c N k).measurable

/-- The finite quantisation of `ρ`. -/
def quantMeas (δ : ℝ) (c : ℕ → B) (N : ℕ) (ρ : Measure B) : Measure B :=
  ∑ k : Fin (N + 1), ENNReal.ofReal (∫ x, pF δ c N k x ∂ρ) • Measure.dirac (aF c N k)

lemma sum_integral_pF (δ : ℝ) (c : ℕ → B) (N : ℕ) (ρ : Measure B) [IsProbabilityMeasure ρ] :
    ∑ k : Fin (N + 1), ∫ x, pF δ c N k x ∂ρ = 1 := by
  rw [← integral_finsetSum _ (fun k _ => integrable_f ρ (measurable_pF δ c N)
    (pF_nonneg δ c N) (sum_pF δ c N) k)]
  simp only [sum_pF]
  simp

lemma isProb_quantMeas (δ : ℝ) (c : ℕ → B) (N : ℕ) (ρ : Measure B) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (quantMeas δ c N ρ) := by
  refine ⟨?_⟩
  simp only [quantMeas, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => integral_nonneg (pF_nonneg δ c N k)),
    sum_integral_pF, ENNReal.ofReal_one]


lemma quant_cost {q : ℝ} {L : ℕ} (ρ : Measure B) [IsProbabilityMeasure ρ] (f : Fin L → B → ℝ)
    (hfm : ∀ k, Measurable (f k)) (hf0 : ∀ k x, 0 ≤ f k x) (a : Fin L → B) :
    ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ q)
      ∂(∑ k, (ρ.withDensity (fun x => ENNReal.ofReal (f k x))).map (fun x => (x, a k))) =
    ∑ k, ∫⁻ x, ENNReal.ofReal (f k x * ‖x - a k‖ ^ q) ∂ρ := by
  rw [lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hmk : Measurable fun x : B => (x, a k) := measurable_id.prodMk measurable_const
  have hm : Measurable fun z : B × B => ENNReal.ofReal (‖z.1 - z.2‖ ^ q) :=
    ENNReal.measurable_ofReal.comp (((measurable_fst.sub measurable_snd).norm).pow_const q)
  rw [lintegral_map hm hmk]
  have hm2 : Measurable fun x : B => ENNReal.ofReal (‖x - a k‖ ^ q) :=
    ENNReal.measurable_ofReal.comp (((measurable_id.sub measurable_const).norm).pow_const q)
  have := lintegral_withDensity_eq_lintegral_mul ρ (ENNReal.measurable_ofReal.comp (hfm k)) hm2
  simp only
  refine this.trans (lintegral_congr fun x => ?_)
  simp only [Pi.mul_apply, Function.comp]
  rw [ENNReal.ofReal_mul (hf0 k x)]

lemma pF_cost_le {q : ℝ} (hq : 0 < q) {δ : ℝ} (hδ : 0 < δ) (c : ℕ → B) (N : ℕ) (x : B) :
    ∑ k : Fin (N + 1), pF δ c N k x * ‖x - aF c N k‖ ^ q ≤ δ ^ q + tailF δ c N x * ‖x‖ ^ q := by
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ k : Fin N, pF δ c N k.castSucc x * ‖x - aF c N k.castSucc‖ ^ q
      = phiF δ c k.val x * ‖x - c k.val‖ ^ q := by
    intro k; simp [pF, aF, k.2]
  have h2 : pF δ c N (Fin.last N) x * ‖x - aF c N (Fin.last N)‖ ^ q = tailF δ c N x * ‖x‖ ^ q := by
    simp [pF, aF]
  simp only [h1, h2]
  rw [Fin.sum_univ_eq_sum_range (fun k => phiF δ c k x * ‖x - c k‖ ^ q) N]
  have hk : ∀ k ∈ Finset.range N, phiF δ c k x * ‖x - c k‖ ^ q ≤ phiF δ c k x * δ ^ q := by
    intro k _
    by_cases h0 : psiF δ c k x = 0
    · simp [phiF, h0]
    · have hlt := lt_of_psiF_ne_zero hδ c k x h0
      refine mul_le_mul_of_nonneg_left ?_ (phiF_nonneg δ c k x)
      exact Real.rpow_le_rpow (norm_nonneg _) hlt.le hq.le
  have hs := sum_phiF δ c N x
  have ht := tailF_nonneg δ c N x
  have : ∑ k ∈ Finset.range N, phiF δ c k x ≤ 1 := by linarith
  calc _ ≤ ∑ k ∈ Finset.range N, phiF δ c k x * δ ^ q + tailF δ c N x * ‖x‖ ^ q := by
        exact add_le_add_left (Finset.sum_le_sum hk) _
    _ = (∑ k ∈ Finset.range N, phiF δ c k x) * δ ^ q + tailF δ c N x * ‖x‖ ^ q := by
        rw [Finset.sum_mul]
    _ ≤ _ := by
        have := mul_le_of_le_one_left (Real.rpow_nonneg hδ.le q) this
        linarith

lemma integrable_tail_rpow {q : ℝ} (hq : 0 < q) {δ : ℝ} (c : ℕ → B) (N : ℕ) (ρ : Measure B)
    (hρ : Integrable (fun x : B => ‖x‖ ^ q) ρ) :
    Integrable (fun x => tailF δ c N x * ‖x‖ ^ q) ρ := by
  refine hρ.mono' ((continuous_tailF δ c N).mul
    (continuous_norm.rpow_const fun _ => Or.inr hq.le)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (tailF_nonneg δ c N x) (Real.rpow_nonneg (norm_nonneg _) _))]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (norm_nonneg _) _) (tailF_le_one δ c N x)

lemma wq_quant_le {q : ℝ} (hq : 1 ≤ q) {δ : ℝ} (hδ : 0 < δ) (c : ℕ → B) (N : ℕ) (ρ : Measure B)
    [IsProbabilityMeasure ρ] (hρ : Integrable (fun x : B => ‖x‖ ^ q) ρ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hc : δ ^ q + ∫ x, tailF δ c N x * ‖x‖ ^ q ∂ρ ≤ θ ^ q) :
    wassersteinE q ρ (quantMeas δ c N ρ) ≤ ENNReal.ofReal θ := by
  have hq0 : 0 < q := by linarith
  refine wq_le_of_cost hq (quant_coupling ρ (pF δ c N) (measurable_pF δ c N) (pF_nonneg δ c N)
    (sum_pF δ c N) (aF c N)) hθ hc ?_
  rw [quant_cost ρ (pF δ c N) (measurable_pF δ c N) (pF_nonneg δ c N) (aF c N)]
  have hm : ∀ k : Fin (N + 1), Measurable fun x : B => pF δ c N k x * ‖x - aF c N k‖ ^ q :=
    fun k => (measurable_pF δ c N k).mul (((measurable_id.sub measurable_const).norm).pow_const q)
  have hnn : ∀ k : Fin (N + 1), ∀ x : B, 0 ≤ pF δ c N k x * ‖x - aF c N k‖ ^ q :=
    fun k x => mul_nonneg (pF_nonneg δ c N k x) (Real.rpow_nonneg (norm_nonneg _) _)
  rw [← lintegral_finsetSum (μ := ρ) Finset.univ
    (f := fun k x => ENNReal.ofReal (pF δ c N k x * ‖x - aF c N k‖ ^ q))
    (fun k _ => ENNReal.measurable_ofReal.comp (hm k))]
  have hint : Integrable (fun x => δ ^ q + tailF δ c N x * ‖x‖ ^ q) ρ :=
    (integrable_const _).add (integrable_tail_rpow hq0 c N ρ hρ)
  calc ∫⁻ x, ∑ k : Fin (N + 1), ENNReal.ofReal (pF δ c N k x * ‖x - aF c N k‖ ^ q) ∂ρ
      = ∫⁻ x, ENNReal.ofReal (∑ k : Fin (N + 1), pF δ c N k x * ‖x - aF c N k‖ ^ q) ∂ρ := by
        refine lintegral_congr fun x => ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hnn k x)]
    _ ≤ ∫⁻ x, ENNReal.ofReal (δ ^ q + tailF δ c N x * ‖x‖ ^ q) ∂ρ :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (pF_cost_le hq0 hδ c N x)
    _ = ENNReal.ofReal (∫ x, (δ ^ q + tailF δ c N x * ‖x‖ ^ q) ∂ρ) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        exact Filter.Eventually.of_forall fun x =>
          add_nonneg (Real.rpow_nonneg hδ.le _)
            (mul_nonneg (tailF_nonneg δ c N x) (Real.rpow_nonneg (norm_nonneg _) _))
    _ = _ := by
        rw [integral_add (integrable_const _) (integrable_tail_rpow hq0 c N ρ hρ)]
        simp

end Quant

end HRS.MC.Sec7.WQ
