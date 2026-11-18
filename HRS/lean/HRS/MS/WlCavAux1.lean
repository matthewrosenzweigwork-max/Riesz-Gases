import HRS.MS.WlEnsAux2

/-!
# HRS.MS.WlCavAux1 -- V-based cavity and pole ensembles, generic layer (WL-6, part 1)

Packet WL-6 of `docs/WR_LOG_PLAN.md` (Step 8 of the proof of `r2_log_static`).  Infrastructure lemmas, not
manuscript rows.  Namespace `HRS.MS.Wl`, helper prefix `wl6_`.

Everything in this file is generic in a weak potential `V : WeakPotential μ` (pair kernel `V.q`, any one-body
field `ψ` with `IsField μ ψ M M₁`, coupling `lam ≥ 0`) and uses the pair-kernel row bound as an explicit
hypothesis `hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a` (so the constants never involve `V.γ`).

* `wl6_norm`, `wl6_law`: the `V`-free normaliser and law of the field ensemble; `fieldNorm V ψ lam n = wl6_norm μ V.q ψ lam n`
  and `fieldLaw V ψ lam n = wl6_law μ V.q ψ lam n` hold by `rfl` (`wl6_fieldNorm_eq`, `wl6_fieldLaw_eq`).
* `wl6_pole q ψ c x = ψ - c q(., x)`: the field of the pole ensemble (a pole at `x` of strength `c`).  The cavity
  ensemble is `wl6_law μ q ψ lam n`, the pole ensemble is `wl6_law μ q (wl6_pole q ψ (t*lam) x) lam n`.
* Weight identities (`wl6_fieldWeight_pole`, `wl6_fieldWeight_insertAt`, `wl6_fieldWeight_insertAt_pole`), monotonicity.
* `wl6_norm_succ_ge`: Jensen, `exp(-(M₁ + lam n a)) * N_n ≤ N_{n+1}` (`N_n` the normaliser of the `n`-particle ensemble).
* `wl6_marginal_zero`: the exact first-marginal formula `(fieldLaw V ψ lam (n+1)).map (· 0) = μ.withDensity dens`,
  `dens x = e^{ψ x} N_n(pole at x) / N_{n+1}`, and `wl6_theta` = `e^{ψ x} Φ_x / Z` with `Φ_x = N_n(pole at x)/N_n ≤ 1`,
  `Z = N_{n+1}/N_n ≥ exp(-(M₁ + lam n a))` (`wl6_dens_eq_theta`, `wl6_Phi_le_one`, `wl6_Z_ge`, `wl6_theta_le`).
* `wl6_disintegration`: the exact cavity identity `∫ F(X 0, tail X) dP_{n+1} = ∫ ∫ F(x, Y) d(pole ensemble at x) d(π)(x)`.
* `wl6_one_le`, `wl6_two_le`: one- and two-particle density bounds by `C μ`, `C μ ⊗ μ` with the retained field factors
  (`e^{ψ(x)}`, and `e^{ψ x + ψ y - lam q(x,y)}`: the pair factor is kept).

Adjustment with respect to the sketch (harmless): the exact first-marginal formula is proved directly by splitting off a
coordinate (`wl6_lintegral_pi_succ`, as in the proof of `pinned_marginal_succ`), and the mixture over the pin that
`pinned_marginal_succ` gives is recovered in `WlCavAux2` (`wl_cavity_mixture`).
-/

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.External HRS.MS.Wr

/-! ### `V`-free normaliser and law -/

section Defs

variable {E : Type*} [MeasurableSpace E]

/-- The unnormalised weight `exp (∑ ψ(y_i) - lam * ∑_{i<j} q(y_i,y_j))` of the field ensemble. -/
def wl6_weight (q : E → E → ℝ) (ψ : E → ℝ) (lam : ℝ) {n : ℕ} (y : Fin n → E) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (∑ i, ψ (y i) - lam * ((1 / 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, q (y i) (y j))))

/-- The normaliser `N_n = ∫ weight dμ^{⊗ n}`. -/
def wl6_norm (μ : Measure E) (q : E → E → ℝ) (ψ : E → ℝ) (lam : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ y, wl6_weight q ψ lam y ∂(Measure.pi fun _ : Fin n => μ)

/-- The law of the field ensemble (`V`-free form of `fieldLaw`). -/
def wl6_law (μ : Measure E) (q : E → E → ℝ) (ψ : E → ℝ) (lam : ℝ) (n : ℕ) : Measure (Fin n → E) :=
  (Measure.pi fun _ : Fin n => μ).withDensity fun y => wl6_weight q ψ lam y * (wl6_norm μ q ψ lam n)⁻¹

/-- The field of the pole ensemble: a pole at `x` of strength `c` (`c = t * lam`). -/
def wl6_pole (q : E → E → ℝ) (ψ : E → ℝ) (c : ℝ) (x : E) : E → ℝ := fun z => ψ z - c * q z x

variable {μ : Measure E}

lemma wl6_weight_eq (V : WeakPotential μ) (ψ : E → ℝ) (lam : ℝ) {n : ℕ} (y : Fin n → E) :
    fieldWeight V ψ lam y = wl6_weight V.q ψ lam y := rfl

lemma wl6_fieldNorm_eq (V : WeakPotential μ) (ψ : E → ℝ) (lam : ℝ) (n : ℕ) :
    fieldNorm V ψ lam n = wl6_norm μ V.q ψ lam n := rfl

lemma wl6_fieldLaw_eq (V : WeakPotential μ) (ψ : E → ℝ) (lam : ℝ) (n : ℕ) :
    fieldLaw V ψ lam n = wl6_law μ V.q ψ lam n := rfl

end Defs

/-! ### Generic layer -/

section Generic

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

lemma wl6_fieldWeight_pole (V : WeakPotential μ) (ψ : E → ℝ) (lam c : ℝ) (x : E) {n : ℕ}
    (y : Fin n → E) :
    fieldWeight V (wl6_pole V.q ψ c x) lam y =
      ENNReal.ofReal (Real.exp (-c * ∑ k, V.q (y k) x)) * fieldWeight V ψ lam y := by
  unfold fieldWeight wl6_pole
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

lemma wl6_fieldWeight_insertAt (V : WeakPotential μ) (ψ : E → ℝ) (lam : ℝ) {n : ℕ} (i : Fin (n + 1))
    (x : E) (y : Fin n → E) :
    fieldWeight V ψ lam (insertAt i x y) =
      ENNReal.ofReal (Real.exp (ψ x - lam * ∑ k, V.q x (y k))) * fieldWeight V ψ lam y := by
  unfold fieldWeight
  rw [sum_insertAt, pairEnergy_insertAt, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

lemma wl6_fieldWeight_insertAt_pole (V : WeakPotential μ) (ψ : E → ℝ) (lam : ℝ) {n : ℕ}
    (i : Fin (n + 1)) (x : E) (y : Fin n → E) :
    fieldWeight V ψ lam (insertAt i x y) =
      ENNReal.ofReal (Real.exp (ψ x)) * fieldWeight V (wl6_pole V.q ψ lam x) lam y := by
  have hS : ∑ k, V.q x (y k) = ∑ k, V.q (y k) x := Finset.sum_congr rfl fun k _ => V.q_symm _ _
  rw [wl6_fieldWeight_insertAt, wl6_fieldWeight_pole, hS, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 3
  ring

lemma wl6_fieldWeight_mono (V : WeakPotential μ) {ψ ψ' : E → ℝ} (h : ∀ z, ψ' z ≤ ψ z) (lam : ℝ)
    {n : ℕ} (y : Fin n → E) : fieldWeight V ψ' lam y ≤ fieldWeight V ψ lam y := by
  unfold fieldWeight
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have := Finset.sum_le_sum (s := Finset.univ) fun i _ => h (y i)
  linarith

lemma wl6_fieldNorm_mono (V : WeakPotential μ) {ψ ψ' : E → ℝ} (h : ∀ z, ψ' z ≤ ψ z) (lam : ℝ)
    (n : ℕ) : fieldNorm V ψ' lam n ≤ fieldNorm V ψ lam n :=
  lintegral_mono fun y => wl6_fieldWeight_mono V h lam y

lemma wl6_pole_le (V : WeakPotential μ) (ψ : E → ℝ) {c : ℝ} (hc : 0 ≤ c) (x z : E) :
    wl6_pole V.q ψ c x z ≤ ψ z := by
  unfold wl6_pole
  have := mul_nonneg hc (V.q_nonneg z x)
  linarith

lemma wl6_isField_pole (V : WeakPotential μ) {ψ : E → ℝ} {M M₁ c a : ℝ} (hψ : IsField μ ψ M M₁)
    (hc : 0 ≤ c) (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a) (x : E) :
    IsField μ (wl6_pole V.q ψ c x) M (M₁ + c * a) := by
  have hq : Integrable (fun z => V.q z x) μ := integrable_q_left V x
  have hqm : Measurable fun z => V.q z x :=
    V.measurable_q.comp (measurable_id.prodMk measurable_const)
  have hI : ∫ z, V.q z x ∂μ ≤ a := by
    have : ∫ z, V.q z x ∂μ = ∫ z, V.q x z ∂μ := integral_congr_ae
      (Filter.Eventually.of_forall fun z => V.q_symm z x)
    rw [this]; exact hrow x
  refine ⟨hψ.measurable.sub (hqm.const_mul c), fun z => (wl6_pole_le V ψ hc x z).trans (hψ.le z),
    hψ.integrable.sub (hq.const_mul c), ?_⟩
  unfold wl6_pole
  rw [integral_sub hψ.integrable (hq.const_mul c), integral_const_mul]
  have := mul_le_mul_of_nonneg_left hI hc
  linarith [hψ.ge]

/-- `N_0 / N_1` comparison: from `c N_0 ≤ N_1` get `N_0 N_1⁻¹ ≤ c⁻¹`. -/
lemma wl6_ratio_le {c N0 N1 : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) (h0 : N0 ≠ 0) (ht : N0 ≠ ⊤)
    (h : c * N0 ≤ N1) : N0 * N1⁻¹ ≤ c⁻¹ := by
  calc N0 * N1⁻¹ ≤ N0 * (c * N0)⁻¹ := mul_le_mul' le_rfl (ENNReal.inv_le_inv.2 h)
    _ = c⁻¹ := by
        rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct), mul_left_comm, ENNReal.mul_inv_cancel h0 ht,
          mul_one]

lemma wl6_measurable_insertAt {n : ℕ} (i : Fin (n + 1)) (x : E) : Measurable (insertAt i x : (Fin n → E) → (Fin (n + 1) → E)) := by
  have : (insertAt i x : (Fin n → E) → (Fin (n + 1) → E)) =
      fun y => (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) i).symm (x, y) := rfl
  rw [this]
  exact (MeasurableEquiv.measurable _).comp measurable_prodMk_left

/-- Splitting off coordinate `i`. -/
theorem wl6_lintegral_pi_succ {n : ℕ} (i : Fin (n + 1)) (F : (Fin (n + 1) → E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ X, F X ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
      ∫⁻ x, ∫⁻ y, F (insertAt i x y) ∂(Measure.pi fun _ : Fin n => μ) ∂μ := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) i with he
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  have hsymm : ∀ (x : E) (y : Fin n → E), e.symm (x, y) = insertAt i x y := fun _ _ => rfl
  have step1 : ∫⁻ y, F y ∂(Measure.pi fun _ : Fin (n + 1) => μ)
      = ∫⁻ p, F (e.symm p) ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) := by
    have := hmp.lintegral_comp_emb e.measurableEmbedding (fun p => F (e.symm p))
    rw [← this]
    exact lintegral_congr fun y => by rw [e.symm_apply_apply]
  rw [step1, lintegral_prod (fun p => F (e.symm p)) (hF.comp e.symm.measurable).aemeasurable]
  simp only [hsymm]

lemma wl6_tail_insertAt_zero {n : ℕ} (x : E) (y : Fin n → E) :
    Fin.tail (insertAt (0 : Fin (n + 1)) x y) = y := by
  funext k
  simpa [Fin.tail] using insertAt_succAbove (0 : Fin (n + 1)) x y k

lemma wl6_insertAt_zero_zero {n : ℕ} (x : E) (y : Fin n → E) : insertAt (0 : Fin (n + 1)) x y 0 = x :=
  insertAt_same _ _ _

lemma wl6_measurable_weight (V : WeakPotential μ) {ψ : E → ℝ} (hψ : Measurable ψ) (lam : ℝ) (n : ℕ) :
    Measurable (fieldWeight V ψ lam (n := n)) := measurable_fieldWeight hψ V lam

/-! ### Jensen lower bound for the normaliser -/

/-- Jensen for the integral over one coordinate: `exp(-(M₁ + lam n a)) ≤ ∫ exp(ψ(x) - lam ∑_k q(x, y_k)) dμ(x)`. -/
lemma wl6_jensen_row (V : WeakPotential μ) {ψ : E → ℝ} {M M₁ lam a : ℝ} (hψ : IsField μ ψ M M₁)
    (hlam : 0 ≤ lam) (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a) {n : ℕ} (y : Fin n → E) :
    ENNReal.ofReal (Real.exp (-(M₁ + lam * n * a))) ≤
      ∫⁻ x, ENNReal.ofReal (Real.exp (ψ x - lam * ∑ k, V.q x (y k))) ∂μ := by
  set h : E → ℝ := fun x => ψ x - lam * ∑ k, V.q x (y k) with hh
  have hsum : Integrable (fun x => ∑ k, V.q x (y k)) μ :=
    integrable_finsetSum _ fun k _ => integrable_q_left V (y k)
  have hint : Integrable h μ := hψ.integrable.sub (hsum.const_mul _)
  have hmeas : Measurable h := hψ.measurable.sub ((Finset.measurable_sum _ fun k _ =>
    V.measurable_q.comp (measurable_id.prodMk measurable_const)).const_mul _)
  have hle : ∀ x, h x ≤ M := fun x => by
    have := mul_nonneg hlam (Finset.sum_nonneg (fun k _ => V.q_nonneg x (y k)) : 0 ≤ ∑ k, V.q x (y k))
    simp only [hh]; linarith [hψ.le x]
  have hexp : Integrable (fun x => Real.exp (h x)) μ :=
    Integrable.of_bound (Real.measurable_exp.comp hmeas).aestronglyMeasurable (Real.exp M)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_le_exp.2 (hle x))
  have hj : Real.exp (∫ x, h x ∂μ) ≤ ∫ x, Real.exp (h x) ∂μ :=
    convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hint hexp
  have hI : -(M₁ + lam * n * a) ≤ ∫ x, h x ∂μ := by
    have e : ∫ x, h x ∂μ = (∫ x, ψ x ∂μ) - lam * ∑ k, ∫ x, V.q x (y k) ∂μ := by
      rw [hh]; simp only
      rw [integral_sub hψ.integrable (hsum.const_mul _), integral_const_mul,
        integral_finset_sum _ fun k _ => integrable_q_left V (y k)]
    have h1 : ∑ k, ∫ x, V.q x (y k) ∂μ ≤ n * a := by
      calc ∑ k, ∫ x, V.q x (y k) ∂μ ≤ ∑ _k : Fin n, a := Finset.sum_le_sum fun k _ => by
              have : ∫ x, V.q x (y k) ∂μ = ∫ x, V.q (y k) x ∂μ :=
                integral_congr_ae (Filter.Eventually.of_forall fun x => V.q_symm x (y k))
              rw [this]; exact hrow _
        _ = n * a := by simp
    rw [e]
    have := mul_le_mul_of_nonneg_left h1 hlam
    nlinarith [hψ.ge]
  calc ENNReal.ofReal (Real.exp (-(M₁ + lam * n * a))) ≤ ENNReal.ofReal (∫ x, Real.exp (h x) ∂μ) :=
        ENNReal.ofReal_le_ofReal ((Real.exp_le_exp.2 hI).trans hj)
    _ = ∫⁻ x, ENNReal.ofReal (Real.exp (h x)) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hexp
          (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)

/-- **Jensen lower bound** `exp(-(M₁ + lam n a)) N_n ≤ N_{n+1}` for the normalisers of the field ensembles. -/
theorem wl6_norm_succ_ge (V : WeakPotential μ) {ψ : E → ℝ} {M M₁ lam a : ℝ} (hψ : IsField μ ψ M M₁)
    (hlam : 0 ≤ lam) (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a) (n : ℕ) :
    ENNReal.ofReal (Real.exp (-(M₁ + lam * n * a))) * fieldNorm V ψ lam n ≤
      fieldNorm V ψ lam (n + 1) := by
  have hWm : Measurable (fieldWeight V ψ lam (n := n)) := measurable_fieldWeight hψ.measurable V lam
  have hWm1 : Measurable (fieldWeight V ψ lam (n := n + 1)) :=
    measurable_fieldWeight hψ.measurable V lam
  have hqk : ∀ k : Fin n, Measurable fun p : E × (Fin n → E) => V.q p.1 (p.2 k) := fun k =>
    V.measurable_q.comp (measurable_fst.prodMk ((measurable_pi_apply k).comp measurable_snd))
  have hgm : Measurable fun p : E × (Fin n → E) =>
      ENNReal.ofReal (Real.exp (ψ p.1 - lam * ∑ k, V.q p.1 (p.2 k))) * fieldWeight V ψ lam p.2 :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hψ.measurable.comp measurable_fst).sub
      ((Finset.measurable_sum _ fun k _ => hqk k).const_mul _)))).mul (hWm.comp measurable_snd)
  have hfx : ∀ y : Fin n → E,
      Measurable fun x => ENNReal.ofReal (Real.exp (ψ x - lam * ∑ k, V.q x (y k))) := fun y =>
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hψ.measurable.sub
      ((Finset.measurable_sum _ fun k _ =>
        V.measurable_q.comp (measurable_id.prodMk measurable_const)).const_mul _)))
  unfold fieldNorm
  rw [wl6_lintegral_pi_succ 0 _ hWm1]
  simp_rw [wl6_fieldWeight_insertAt]
  rw [lintegral_lintegral_swap hgm.aemeasurable]
  calc ENNReal.ofReal (Real.exp (-(M₁ + lam * n * a))) *
        ∫⁻ y, fieldWeight V ψ lam y ∂(Measure.pi fun _ : Fin n => μ)
      = ∫⁻ y, ENNReal.ofReal (Real.exp (-(M₁ + lam * n * a))) * fieldWeight V ψ lam y
          ∂(Measure.pi fun _ : Fin n => μ) := (lintegral_const_mul _ hWm).symm
    _ ≤ ∫⁻ y, ∫⁻ x, ENNReal.ofReal (Real.exp (ψ x - lam * ∑ k, V.q x (y k))) *
          fieldWeight V ψ lam y ∂μ ∂(Measure.pi fun _ : Fin n => μ) := by
        refine lintegral_mono fun y => ?_
        rw [lintegral_mul_const _ (hfx y)]
        exact mul_le_mul' (wl6_jensen_row V hψ hlam hrow y) le_rfl

/-! ### The exact first marginal -/

/-- The density (w.r.t. `μ`) of the first marginal of the `(n+1)`-particle ensemble. -/
def wl6_dens (μ : Measure E) (q : E → E → ℝ) (ψ : E → ℝ) (lam : ℝ) (n : ℕ) (x : E) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (ψ x)) * wl6_norm μ q (wl6_pole q ψ lam x) lam n *
    (wl6_norm μ q ψ lam (n + 1))⁻¹

lemma wl6_measurable_pole (V : WeakPotential μ) {ψ : E → ℝ} (hψ : Measurable ψ) (c : ℝ) (x : E) :
    Measurable (wl6_pole V.q ψ c x) :=
  hψ.sub ((V.measurable_q.comp (measurable_id.prodMk measurable_const)).const_mul c)

lemma wl6_measurable_norm_pole (V : WeakPotential μ) {ψ : E → ℝ} (hψ : Measurable ψ) (lam c : ℝ)
    (n : ℕ) : Measurable fun x => wl6_norm μ V.q (wl6_pole V.q ψ c x) lam n := by
  have hW : Measurable (fieldWeight V ψ lam (n := n)) := measurable_fieldWeight hψ V lam
  have h : ∀ x, wl6_norm μ V.q (wl6_pole V.q ψ c x) lam n =
      ∫⁻ y, ENNReal.ofReal (Real.exp (-c * ∑ k, V.q (y k) x)) * fieldWeight V ψ lam y
        ∂(Measure.pi fun _ : Fin n => μ) := fun x => by
    rw [← wl6_fieldNorm_eq]
    unfold fieldNorm
    simp_rw [wl6_fieldWeight_pole]
  simp_rw [h]
  refine Measurable.lintegral_prod_right'
    (f := fun p : E × (Fin n → E) => ENNReal.ofReal (Real.exp (-c * ∑ k, V.q (p.2 k) p.1)) *
      fieldWeight V ψ lam p.2) ?_
  exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((Finset.measurable_sum _ fun k _ =>
    V.measurable_q.comp (((measurable_pi_apply k).comp measurable_snd).prodMk measurable_fst)).const_mul _))).mul
    (hW.comp measurable_snd)

lemma wl6_measurable_dens (V : WeakPotential μ) {ψ : E → ℝ} (hψ : Measurable ψ) (lam : ℝ) (n : ℕ) :
    Measurable (wl6_dens μ V.q ψ lam n) :=
  ((ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hψ)).mul
    (wl6_measurable_norm_pole V hψ lam lam n)).mul measurable_const

/-- **Exact first marginal.**  The first marginal of the `(n+1)`-particle field ensemble is `μ.withDensity dens`,
`dens x = e^{ψ(x)} N_n(pole at x) / N_{n+1}`. -/
theorem wl6_marginal_zero (V : WeakPotential μ) {ψ : E → ℝ} {M M₁ lam a : ℝ} (hψ : IsField μ ψ M M₁)
    (hlam : 0 ≤ lam) (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a) (n : ℕ) :
    (fieldLaw V ψ lam (n + 1)).map (fun X => X 0) = μ.withDensity (wl6_dens μ V.q ψ lam n) := by
  have hpole := wl6_isField_pole V hψ hlam hrow
  ext A hA
  rw [Measure.map_apply (measurable_pi_apply 0) hA, withDensity_apply _ hA]
  have hSm : MeasurableSet ((fun X : Fin (n + 1) → E => X 0) ⁻¹' A) := measurable_pi_apply 0 hA
  unfold fieldLaw
  rw [withDensity_apply _ hSm, ← lintegral_indicator hSm,
    wl6_lintegral_pi_succ 0 _ ((measurable_fieldDensity hψ.measurable V lam (n + 1)).indicator hSm),
    ← lintegral_indicator hA]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ A
  · have h1 : ∀ y : Fin n → E,
        insertAt (0 : Fin (n + 1)) x y ∈ (fun X : Fin (n + 1) → E => X 0) ⁻¹' A := fun y => by
      simp [hx]
    simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (h1 _)]
    unfold fieldDensity
    simp_rw [wl6_fieldWeight_insertAt_pole]
    have e : ∀ y : Fin n → E,
        ENNReal.ofReal (Real.exp (ψ x)) * fieldWeight V (wl6_pole V.q ψ lam x) lam y *
          (fieldNorm V ψ lam (n + 1))⁻¹ =
        (ENNReal.ofReal (Real.exp (ψ x)) * (fieldNorm V ψ lam (n + 1))⁻¹) *
          fieldWeight V (wl6_pole V.q ψ lam x) lam y := fun y => by ring
    simp_rw [e]
    rw [lintegral_const_mul _ (measurable_fieldWeight (hpole x).measurable V lam)]
    unfold wl6_dens
    rw [← wl6_fieldNorm_eq, ← wl6_fieldNorm_eq]
    unfold fieldNorm
    ring
  · have h1 : ∀ y : Fin n → E,
        insertAt (0 : Fin (n + 1)) x y ∉ (fun X : Fin (n + 1) → E => X 0) ⁻¹' A := fun y => by
      simp [hx]
    simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (h1 _)]

/-! ### `θ = e^ψ Φ / Z` -/

/-- `Φ_x = N_n(pole at x) / N_n ∈ [0,1]`. -/
def wl6_Phi (μ : Measure E) (q : E → E → ℝ) (ψ : E → ℝ) (lam : ℝ) (n : ℕ) (x : E) : ℝ :=
  (wl6_norm μ q (wl6_pole q ψ lam x) lam n).toReal / (wl6_norm μ q ψ lam n).toReal

/-- `Z = N_{n+1} / N_n`. -/
def wl6_Z (μ : Measure E) (q : E → E → ℝ) (ψ : E → ℝ) (lam : ℝ) (n : ℕ) : ℝ :=
  (wl6_norm μ q ψ lam (n + 1)).toReal / (wl6_norm μ q ψ lam n).toReal

/-- `θ(x) = e^{ψ(x)} Φ_x / Z`: the density of the first marginal. -/
def wl6_theta (μ : Measure E) (q : E → E → ℝ) (ψ : E → ℝ) (lam : ℝ) (n : ℕ) (x : E) : ℝ :=
  Real.exp (ψ x) * wl6_Phi μ q ψ lam n x / wl6_Z μ q ψ lam n

section Theta

variable (V : WeakPotential μ) {ψ : E → ℝ} {M M₁ lam a : ℝ}

lemma wl6_norm_ne_zero (hψ : IsField μ ψ M M₁) (n : ℕ) : wl6_norm μ V.q ψ lam n ≠ 0 :=
  (fieldNorm_pos hψ.measurable V lam n).ne'

lemma wl6_norm_ne_top (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (n : ℕ) : wl6_norm μ V.q ψ lam n ≠ ⊤ :=
  (fieldNorm_lt_top hψ hlam n).ne

lemma wl6_norm_toReal_pos (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (n : ℕ) :
    0 < (wl6_norm μ V.q ψ lam n).toReal :=
  ENNReal.toReal_pos (wl6_norm_ne_zero V hψ n) (wl6_norm_ne_top V hψ hlam n)

lemma wl6_norm_pole_le (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (x : E) :
    wl6_norm μ V.q (wl6_pole V.q ψ c x) lam n ≤ wl6_norm μ V.q ψ lam n :=
  wl6_fieldNorm_mono V (wl6_pole_le V ψ hc x) lam n

lemma wl6_Phi_nonneg (n : ℕ) (x : E) : 0 ≤ wl6_Phi μ V.q ψ lam n x :=
  div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- `Φ_x ≤ 1`. -/
lemma wl6_Phi_le_one (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (n : ℕ) (x : E) :
    wl6_Phi μ V.q ψ lam n x ≤ 1 := by
  unfold wl6_Phi
  rw [div_le_one (wl6_norm_toReal_pos V hψ hlam n)]
  exact ENNReal.toReal_mono (wl6_norm_ne_top V hψ hlam n) (wl6_norm_pole_le V hψ hlam hlam n x)

/-- `Z ≥ exp(-(M₁ + lam n a))`. -/
lemma wl6_Z_ge (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a) (n : ℕ) :
    Real.exp (-(M₁ + lam * n * a)) ≤ wl6_Z μ V.q ψ lam n := by
  unfold wl6_Z
  rw [le_div_iff₀ (wl6_norm_toReal_pos V hψ hlam n)]
  have h := wl6_norm_succ_ge V hψ hlam hrow n
  have h1 := ENNReal.toReal_mono (wl6_norm_ne_top V hψ hlam (n + 1)) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h1
  exact h1

lemma wl6_Z_pos (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (n : ℕ) : 0 < wl6_Z μ V.q ψ lam n :=
  div_pos (wl6_norm_toReal_pos V hψ hlam (n + 1)) (wl6_norm_toReal_pos V hψ hlam n)

lemma wl6_theta_nonneg (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (n : ℕ) (x : E) :
    0 ≤ wl6_theta μ V.q ψ lam n x :=
  div_nonneg (mul_nonneg (Real.exp_pos _).le (wl6_Phi_nonneg V n x)) (wl6_Z_pos V hψ hlam n).le

/-- `θ(x) ≤ e^{ψ(x)} e^{M₁ + lam n a}`. -/
lemma wl6_theta_le (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a)
    (n : ℕ) (x : E) :
    wl6_theta μ V.q ψ lam n x ≤ Real.exp (ψ x) * Real.exp (M₁ + lam * n * a) := by
  have hZ := wl6_Z_ge V hψ hlam hrow n
  have hZp := wl6_Z_pos V hψ hlam n
  have hΦ0 := wl6_Phi_nonneg V (ψ := ψ) (lam := lam) (μ := μ) n x
  have hΦ1 := wl6_Phi_le_one V hψ hlam n x
  unfold wl6_theta
  rw [div_le_iff₀ hZp]
  have h1 : Real.exp (ψ x) * wl6_Phi μ V.q ψ lam n x ≤ Real.exp (ψ x) := by
    nlinarith [Real.exp_pos (ψ x)]
  have h2 : Real.exp (M₁ + lam * n * a) * Real.exp (-(M₁ + lam * n * a)) = 1 := by
    rw [← Real.exp_add]; simp
  calc Real.exp (ψ x) * wl6_Phi μ V.q ψ lam n x ≤ Real.exp (ψ x) := h1
    _ = Real.exp (ψ x) * (Real.exp (M₁ + lam * n * a) * Real.exp (-(M₁ + lam * n * a))) := by
        rw [h2, mul_one]
    _ ≤ Real.exp (ψ x) * (Real.exp (M₁ + lam * n * a) * wl6_Z μ V.q ψ lam n) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZ (Real.exp_pos _).le)
          (Real.exp_pos _).le
    _ = _ := by ring

lemma wl6_measurable_theta (hψ : Measurable ψ) (lam : ℝ) (n : ℕ) :
    Measurable (wl6_theta μ V.q ψ lam n) := by
  unfold wl6_theta wl6_Phi
  exact (((Real.measurable_exp.comp hψ).mul
    ((wl6_measurable_norm_pole V hψ lam lam n).ennreal_toReal.div_const _))).div_const _

/-- `dens = ofReal θ`. -/
lemma wl6_dens_eq_theta (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (n : ℕ) (x : E) :
    wl6_dens μ V.q ψ lam n x = ENNReal.ofReal (wl6_theta μ V.q ψ lam n x) := by
  set P := wl6_norm μ V.q (wl6_pole V.q ψ lam x) lam n with hP
  set N0 := wl6_norm μ V.q ψ lam n with hN0
  set N1 := wl6_norm μ V.q ψ lam (n + 1) with hN1
  have hPt : P ≠ ⊤ := ne_top_of_le_ne_top (wl6_norm_ne_top V hψ hlam n)
    (wl6_norm_pole_le V hψ hlam hlam n x)
  have hN1t : N1 ≠ ⊤ := wl6_norm_ne_top V hψ hlam (n + 1)
  have h0 : 0 < N0.toReal := wl6_norm_toReal_pos V hψ hlam n
  have h1 : 0 < N1.toReal := wl6_norm_toReal_pos V hψ hlam (n + 1)
  have e : wl6_theta μ V.q ψ lam n x = Real.exp (ψ x) * P.toReal * (N1.toReal)⁻¹ := by
    unfold wl6_theta wl6_Phi wl6_Z
    rw [← hP, ← hN0, ← hN1]
    field_simp
  rw [e, ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_inv_of_pos h1,
    ENNReal.ofReal_toReal hPt, ENNReal.ofReal_toReal hN1t]
  rfl

lemma wl6_inv_ofReal_exp (E' : ℝ) :
    (ENNReal.ofReal (Real.exp (-E')))⁻¹ = ENNReal.ofReal (Real.exp E') := by
  rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg, neg_neg]

/-- The density bound `dens ≤ e^{M₁ + lam n a} e^{ψ}`. -/
lemma wl6_dens_le (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a)
    (n : ℕ) (x : E) :
    wl6_dens μ V.q ψ lam n x ≤
      ENNReal.ofReal (Real.exp (M₁ + lam * n * a)) * ENNReal.ofReal (Real.exp (ψ x)) := by
  have hratio := wl6_ratio_le (c := ENNReal.ofReal (Real.exp (-(M₁ + lam * n * a))))
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top
    (wl6_norm_ne_zero V hψ n) (wl6_norm_ne_top V hψ hlam n) (wl6_norm_succ_ge V hψ hlam hrow n)
  rw [wl6_inv_ofReal_exp] at hratio
  unfold wl6_dens
  calc ENNReal.ofReal (Real.exp (ψ x)) * wl6_norm μ V.q (wl6_pole V.q ψ lam x) lam n *
        (wl6_norm μ V.q ψ lam (n + 1))⁻¹
      ≤ ENNReal.ofReal (Real.exp (ψ x)) * wl6_norm μ V.q ψ lam n *
        (wl6_norm μ V.q ψ lam (n + 1))⁻¹ :=
        mul_le_mul' (mul_le_mul' le_rfl (wl6_norm_pole_le V hψ hlam hlam n x)) le_rfl
    _ = ENNReal.ofReal (Real.exp (ψ x)) * (wl6_norm μ V.q ψ lam n *
        (wl6_norm μ V.q ψ lam (n + 1))⁻¹) := by ring
    _ ≤ ENNReal.ofReal (Real.exp (ψ x)) * ENNReal.ofReal (Real.exp (M₁ + lam * n * a)) :=
        mul_le_mul' le_rfl hratio
    _ = _ := by ring

end Theta

/-! ### Exact cavity identity, one- and two-particle density bounds -/

section Disint

variable (V : WeakPotential μ) {ψ : E → ℝ} {M M₁ lam a : ℝ}

/-- **Exact cavity identity.**  The law of the `(n+1)`-particle field ensemble, disintegrated over the first
particle, is the mixture over its first marginal `π` of the `n`-particle pole ensembles (field `pole at x`):
`∫ F(X 0, tail X) dP_{n+1} = ∫ ∫ F(x, Y) d(P_n^{x}) dπ(x)`. -/
theorem wl6_disintegration (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam)
    (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a) (n : ℕ) (F : E × (Fin n → E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ X, F (X 0, Fin.tail X) ∂(fieldLaw V ψ lam (n + 1)) =
      ∫⁻ x, ∫⁻ Y, F (x, Y) ∂(fieldLaw V (wl6_pole V.q ψ lam x) lam n)
        ∂((fieldLaw V ψ lam (n + 1)).map (fun X => X 0)) := by
  have hpole := wl6_isField_pole V hψ hlam hrow
  rw [wl6_marginal_zero V hψ hlam hrow n]
  have hdm := wl6_measurable_dens V hψ.measurable lam n
  have hdfin : ∀ᵐ x ∂μ, wl6_dens μ V.q ψ lam n x < ⊤ := Filter.Eventually.of_forall fun x => by
    rw [wl6_dens_eq_theta V hψ hlam]; exact ENNReal.ofReal_lt_top
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hdm hdfin]
  have htail : Measurable fun X : Fin (n + 1) → E => Fin.tail X :=
    measurable_pi_iff.2 fun k => measurable_pi_apply (Fin.succ k)
  have hG : Measurable fun X : Fin (n + 1) → E => F (X 0, Fin.tail X) :=
    hF.comp ((measurable_pi_apply 0).prodMk htail)
  have hD := measurable_fieldDensity hψ.measurable V lam (n + 1)
  unfold fieldLaw
  rw [lintegral_withDensity_eq_lintegral_mul _ hD hG, wl6_lintegral_pi_succ 0 _ (hD.mul hG)]
  refine lintegral_congr fun x => ?_
  have hWp : Measurable (fieldWeight V (wl6_pole V.q ψ lam x) lam (n := n)) :=
    measurable_fieldWeight (hpole x).measurable V lam
  have hFx : Measurable (fun Y => F (x, Y)) := hF.comp measurable_prodMk_left
  have hWF : Measurable (fun y => fieldWeight V (wl6_pole V.q ψ lam x) lam y * F (x, y)) := hWp.mul hFx
  have hNp0 : fieldNorm V (wl6_pole V.q ψ lam x) lam n ≠ 0 := (fieldNorm_pos (hpole x).measurable V lam n).ne'
  have hNpt : fieldNorm V (wl6_pole V.q ψ lam x) lam n ≠ ⊤ := (fieldNorm_lt_top (hpole x) hlam n).ne
  simp only [Pi.mul_apply]
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_fieldDensity (hpole x).measurable V lam n) hFx]
  have L : ∫⁻ y, fieldDensity V ψ lam (n + 1) (insertAt 0 x y) *
        F (insertAt (0 : Fin (n + 1)) x y 0, Fin.tail (insertAt (0 : Fin (n + 1)) x y))
        ∂(Measure.pi fun _ : Fin n => μ) =
      (ENNReal.ofReal (Real.exp (ψ x)) * (fieldNorm V ψ lam (n + 1))⁻¹) *
        ∫⁻ y, fieldWeight V (wl6_pole V.q ψ lam x) lam y * F (x, y) ∂(Measure.pi fun _ : Fin n => μ) := by
    rw [← lintegral_const_mul _ hWF]
    refine lintegral_congr fun y => ?_
    simp only [wl6_tail_insertAt_zero, wl6_insertAt_zero_zero]
    unfold fieldDensity
    rw [wl6_fieldWeight_insertAt_pole]
    ring
  have R : ∫⁻ Y, (fieldDensity V (wl6_pole V.q ψ lam x) lam n * fun Y => F (x, Y)) Y
        ∂(Measure.pi fun _ : Fin n => μ) =
      (fieldNorm V (wl6_pole V.q ψ lam x) lam n)⁻¹ *
        ∫⁻ y, fieldWeight V (wl6_pole V.q ψ lam x) lam y * F (x, y) ∂(Measure.pi fun _ : Fin n => μ) := by
    rw [← lintegral_const_mul _ hWF]
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply]
    unfold fieldDensity
    ring
  rw [L, R]
  unfold wl6_dens
  rw [← wl6_fieldNorm_eq, ← wl6_fieldNorm_eq]
  set I := ∫⁻ y, fieldWeight V (wl6_pole V.q ψ lam x) lam y * F (x, y) ∂(Measure.pi fun _ : Fin n => μ)
  have h1 : fieldNorm V (wl6_pole V.q ψ lam x) lam n * (fieldNorm V (wl6_pole V.q ψ lam x) lam n)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hNp0 hNpt
  calc ENNReal.ofReal (Real.exp (ψ x)) * (fieldNorm V ψ lam (n + 1))⁻¹ * I
      = ENNReal.ofReal (Real.exp (ψ x)) * (fieldNorm V ψ lam (n + 1))⁻¹ *
          (fieldNorm V (wl6_pole V.q ψ lam x) lam n * (fieldNorm V (wl6_pole V.q ψ lam x) lam n)⁻¹) * I := by
        rw [h1, mul_one]
    _ = _ := by ring

/-- **One-particle density bound.**  `π ≤ e^{M₁ + lam n a} · (e^{ψ} μ)`: the density is bounded by `C μ` with the
retained field factor `e^{ψ(x)}`. -/
theorem wl6_one_le (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a) (n : ℕ) :
    (fieldLaw V ψ lam (n + 1)).map (fun X => X 0) ≤
      ENNReal.ofReal (Real.exp (M₁ + lam * n * a)) •
        μ.withDensity (fun x => ENNReal.ofReal (Real.exp (ψ x))) := by
  rw [wl6_marginal_zero V hψ hlam hrow n]
  refine Measure.le_iff.2 fun A hA => ?_
  rw [withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul, withDensity_apply _ hA,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono fun x => wl6_dens_le V hψ hlam hrow n x

/-- Integration against a measure dominated by `c • μ.withDensity h`. -/
lemma wl6_lintegral_le_smul {ν : Measure E} {c : ℝ≥0∞} {h : E → ℝ≥0∞} (hh : Measurable h)
    (hfin : ∀ x, h x < ⊤) (hν : ν ≤ c • μ.withDensity h) (G : E → ℝ≥0∞) :
    ∫⁻ x, G x ∂ν ≤ c * ∫⁻ x, h x * G x ∂μ := by
  calc ∫⁻ x, G x ∂ν ≤ ∫⁻ x, G x ∂(c • μ.withDensity h) := lintegral_mono' hν le_rfl
    _ = c * ∫⁻ x, G x ∂(μ.withDensity h) := lintegral_smul_measure _ _
    _ = c * ∫⁻ x, h x * G x ∂μ := by
        rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hh
          (Filter.Eventually.of_forall hfin)]
        rfl

/-- **Two-particle density bound** (`m + 2` particles).  `π₂ ≤ C · (e^{ψ(x) + ψ(y) - lam q(x,y)} μ ⊗ μ)`,
`C = e^{2 (M₁ + lam (m+1) a)}`: one retains the field factors and the pair factor `e^{-lam q(x,y)}`. -/
theorem wl6_two_le (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a) (m : ℕ) :
    (fieldLaw V ψ lam (m + 2)).map (fun X => (X 0, X (Fin.succ 0))) ≤
      ENNReal.ofReal (Real.exp (2 * (M₁ + lam * ((m : ℝ) + 1) * a))) •
        (μ.prod μ).withDensity
          (fun p => ENNReal.ofReal (Real.exp (ψ p.1 + ψ p.2 - lam * V.q p.1 p.2))) := by
  have hpole := wl6_isField_pole V hψ hlam hrow
  refine Measure.le_iff.2 fun S hS => ?_
  have hpair : Measurable fun X : Fin (m + 2) → E => (X 0, X (Fin.succ 0)) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply _)
  rw [Measure.map_apply hpair hS]
  set F : E × (Fin (m + 1) → E) → ℝ≥0∞ := fun p => S.indicator 1 (p.1, p.2 0) with hFdef
  have hF : Measurable F := (measurable_one.indicator hS).comp
    (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  have h1 : fieldLaw V ψ lam (m + 2) ((fun X : Fin (m + 2) → E => (X 0, X (Fin.succ 0))) ⁻¹' S) =
      ∫⁻ X, F (X 0, Fin.tail X) ∂(fieldLaw V ψ lam (m + 2)) := by
    rw [← lintegral_indicator_one (hpair hS)]
    refine lintegral_congr fun X => ?_
    show Set.indicator _ 1 X = S.indicator 1 (X 0, X (Fin.succ 0))
    by_cases h : (X 0, X (Fin.succ 0)) ∈ S
    · have h' : X ∈ (fun X : Fin (m + 2) → E => (X 0, X (Fin.succ 0))) ⁻¹' S := h
      rw [Set.indicator_of_mem h', Set.indicator_of_mem h]; rfl
    · have h' : X ∉ (fun X : Fin (m + 2) → E => (X 0, X (Fin.succ 0))) ⁻¹' S := h
      rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]
  rw [h1, wl6_disintegration V hψ hlam hrow (m + 1) F hF]
  -- inner bound, for each `x`
  set c₂ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (M₁ + lam * ((m : ℝ) + 1) * a)) with hc₂
  have hinner : ∀ x : E, ∫⁻ Y, F (x, Y) ∂(fieldLaw V (wl6_pole V.q ψ lam x) lam (m + 1)) ≤
      c₂ * ∫⁻ y, (Prod.mk x ⁻¹' S).indicator
        (fun y => ENNReal.ofReal (Real.exp (ψ y - lam * V.q y x))) y ∂μ := by
    intro x
    have hT : MeasurableSet (Prod.mk x ⁻¹' S) := measurable_prodMk_left hS
    have e1 : ∫⁻ Y, F (x, Y) ∂(fieldLaw V (wl6_pole V.q ψ lam x) lam (m + 1)) =
        ((fieldLaw V (wl6_pole V.q ψ lam x) lam (m + 1)).map (fun X => X 0)) (Prod.mk x ⁻¹' S) := by
      rw [Measure.map_apply (measurable_pi_apply 0) hT,
        ← lintegral_indicator_one ((measurable_pi_apply 0) hT)]
      refine lintegral_congr fun Y => ?_
      by_cases h : (x, Y 0) ∈ S <;> simp [hFdef, Set.indicator, h]
    rw [e1]
    have h2 := Measure.le_iff'.1 (wl6_one_le V (hpole x) hlam hrow m) (Prod.mk x ⁻¹' S)
    refine h2.trans ?_
    rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hT, ← lintegral_indicator hT]
    have hc : ENNReal.ofReal (Real.exp (M₁ + lam * a + lam * m * a)) = c₂ := by
      rw [hc₂]; congr 2; ring
    rw [hc]
    rfl
  refine (lintegral_mono hinner).trans ?_
  have hone := wl6_one_le V hψ hlam hrow (m + 1)
  refine (wl6_lintegral_le_smul (h := fun x => ENNReal.ofReal (Real.exp (ψ x)))
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hψ.measurable))
    (fun x => ENNReal.ofReal_lt_top) hone _).trans (le_of_eq ?_)
  set d : E × E → ℝ≥0∞ := fun p => ENNReal.ofReal (Real.exp (ψ p.1 + ψ p.2 - lam * V.q p.1 p.2)) with hd
  have hdm : Measurable d := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (((hψ.measurable.comp measurable_fst).add (hψ.measurable.comp measurable_snd)).sub
      ((V.measurable_q).const_mul lam)))
  have hpt : ∀ x : E, ENNReal.ofReal (Real.exp (ψ x)) * (c₂ * ∫⁻ y, (Prod.mk x ⁻¹' S).indicator
      (fun y => ENNReal.ofReal (Real.exp (ψ y - lam * V.q y x))) y ∂μ) =
      c₂ * ∫⁻ y, S.indicator d (x, y) ∂μ := by
    intro x
    have hT : MeasurableSet (Prod.mk x ⁻¹' S) := measurable_prodMk_left hS
    have hgm : Measurable fun y => ENNReal.ofReal (Real.exp (ψ y - lam * V.q y x)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (wl6_measurable_pole V hψ.measurable lam x))
    rw [mul_left_comm, ← lintegral_const_mul _ (hgm.indicator hT)]
    congr 1
    refine lintegral_congr fun y => ?_
    by_cases h : (x, y) ∈ S
    · have h' : y ∈ Prod.mk x ⁻¹' S := h
      rw [Set.indicator_of_mem h', Set.indicator_of_mem h, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add, hd]
      simp only
      rw [V.q_symm y x]
      congr 2
      ring
    · have h' : y ∉ Prod.mk x ⁻¹' S := h
      rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h, mul_zero]
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hS, ← lintegral_indicator hS,
    lintegral_prod _ (hdm.indicator hS).aemeasurable]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  push_cast
  ring

end Disint

end Generic

end HRS.MS.Wl
