import HRS.Uniform.Comparison
import HRS.Uniform.KotTransform

/-!
# Q48d, part 1: an `eLpNorm` toolkit for stochastic convolutions (infrastructure for Lemma 3.31)

`IsStochConv` is stated with `lintegral`s, which are only lower integrals for non-measurable integrands.  For
a.e.-strongly measurable `Z` and martingales whose values are a.e.-strongly measurable it is equivalent to the
`eLpNorm` form `SC`; with it we prove uniqueness a.e. of the stochastic convolution, the concatenation identity
`∫_0^t V(t,u) dD = V(t,a) ∫_0^a V(a,u) dD + ∫_a^t V(t,u) dD`, and the invariance under stopping.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Uniform.Q48d

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The Riemann sum with `j = id`. -/
lemma riemannSum_id (V : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → Ω → E) (t : ℝ) {n : ℕ} (r : Fin (n + 1) → ℝ) (ω : Ω) :
    riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω =
      ∑ i : Fin n, V t (r i.castSucc) (D (r i.succ) ω - D (r i.castSucc) ω) := by
  simp [riemannSum]

/-- The `eLpNorm` form of `IsStochConv`. -/
def SC (P : Measure Ω) (V : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → Ω → E) (a t : ℝ) (Z : Ω → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (r : Fin (n + 1) → ℝ), r 0 = a →
    r (Fin.last n) = t → Monotone r → (∀ i : Fin n, r i.succ - r i.castSucc < δ) →
      eLpNorm (fun ω => Z ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω) 2 P < ENNReal.ofReal ε

lemma mem_Icc_of_part {a t : ℝ} {n : ℕ} {r : Fin (n + 1) → ℝ} (h0 : r 0 = a) (hl : r (Fin.last n) = t)
    (hm : Monotone r) (i : Fin (n + 1)) : r i ∈ Icc a t :=
  ⟨h0 ▸ hm (Fin.zero_le i), hl ▸ hm (Fin.le_last i)⟩

lemma aesm_riemannSum {P : Measure Ω} (V : ℝ → ℝ → E →L[ℝ] E) {D : ℝ → Ω → E} {a t : ℝ}
    (hD : ∀ τ ∈ Icc a t, AEStronglyMeasurable (D τ) P) {n : ℕ} {r : Fin (n + 1) → ℝ} (h0 : r 0 = a)
    (hl : r (Fin.last n) = t) (hm : Monotone r) :
    AEStronglyMeasurable (fun ω => riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω) P := by
  simp_rw [riemannSum_id]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  exact (V t (r i.castSucc)).continuous.comp_aestronglyMeasurable
    ((hD _ (mem_Icc_of_part h0 hl hm _)).sub (hD _ (mem_Icc_of_part h0 hl hm _)))

lemma isStochConv_iff {P : Measure Ω} {V : ℝ → ℝ → E →L[ℝ] E} {D : ℝ → Ω → E} {a t : ℝ} {Z : Ω → E}
    (hZ : AEStronglyMeasurable Z P) (hD : ∀ τ ∈ Icc a t, AEStronglyMeasurable (D τ) P) :
    IsStochConv P V (ContinuousLinearMap.id ℝ E) D a t Z ↔ SC P V D a t Z := by
  have key : ∀ {n : ℕ} {r : Fin (n + 1) → ℝ}, r 0 = a → r (Fin.last n) = t → Monotone r →
      ∀ ε : ℝ, 0 < ε →
      ((∫⁻ ω, ‖Z ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω‖ₑ ^ 2 ∂P < ENNReal.ofReal (ε ^ 2)) ↔
        eLpNorm (fun ω => Z ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω) 2 P < ENNReal.ofReal ε) := by
    intro n r h0 hl hm ε hε
    have hmeas : AEStronglyMeasurable
        (fun ω => Z ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω) P :=
      hZ.sub (aesm_riemannSum V hD h0 hl hm)
    have hsq := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hmeas
    have e1 : ∫⁻ ω, ‖Z ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω‖ₑ ^ 2 ∂P =
        eLpNorm (fun ω => Z ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω) 2 P ^ 2 := by
      have := hsq
      simpa using this.symm
    rw [e1]
    have e2 : ENNReal.ofReal (ε ^ 2) = ENNReal.ofReal ε ^ 2 := by
      rw [ENNReal.ofReal_pow hε.le]
    rw [e2]
    exact ENNReal.pow_lt_pow_left_iff (by norm_num)
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h (ε ^ 2) (by positivity)
    exact ⟨δ, hδ, fun n r h0 hl hm hmesh => (key h0 hl hm ε hε).1 (hδ' n r h0 hl hm hmesh)⟩
  · intro h ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h (Real.sqrt ε) (Real.sqrt_pos.2 hε)
    refine ⟨δ, hδ, fun n r h0 hl hm hmesh => ?_⟩
    have := (key h0 hl hm (Real.sqrt ε) (Real.sqrt_pos.2 hε)).2 (hδ' n r h0 hl hm hmesh)
    rwa [Real.sq_sqrt hε.le] at this

/-- Uniform partitions of small mesh. -/
lemma exists_part {a t : ℝ} (hat : a ≤ t) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (r : Fin (n + 1) → ℝ), r 0 = a ∧ r (Fin.last n) = t ∧ Monotone r ∧
      ∀ i : Fin n, r i.succ - r i.castSucc < δ := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (t - a) / δ < n := exists_nat_gt _
  have hn0 : 0 < n := by
    have : 0 ≤ (t - a) / δ := div_nonneg (by linarith) hδ.le
    exact_mod_cast this.trans_lt hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  refine ⟨n, fun i => a + (i : ℕ) * ((t - a) / n), by simp, ?_, ?_, ?_⟩
  · simp only [Fin.val_last]
    field_simp
    ring
  · intro i j hij
    have : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij
    have h0 : 0 ≤ (t - a) / n := div_nonneg (by linarith) hnR.le
    simp only
    nlinarith
  · intro i
    simp only [Fin.val_succ, Fin.val_castSucc]
    push_cast
    have : (t - a) / n < δ := by
      rw [div_lt_iff₀ hnR]
      rw [div_lt_iff₀ hδ] at hn
      linarith
    linarith

lemma sc_unique {P : Measure Ω} {V : ℝ → ℝ → E →L[ℝ] E} {D : ℝ → Ω → E} {a t : ℝ} (hat : a ≤ t)
    (hD : ∀ τ ∈ Icc a t, AEStronglyMeasurable (D τ) P) {Z Z' : Ω → E} (hZ : AEStronglyMeasurable Z P)
    (hZ' : AEStronglyMeasurable Z' P) (h : SC P V D a t Z) (h' : SC P V D a t Z') : Z =ᵐ[P] Z' := by
  have hz : eLpNorm (Z - Z') 2 P = 0 := by
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_) bot_le
    have hη2 : (0 : ℝ) < (η : ℝ) / 2 := by positivity
    obtain ⟨δ, hδ, hδ'⟩ := h _ hη2
    obtain ⟨δ', hδ'0, hδ''⟩ := h' _ hη2
    obtain ⟨n, r, h0, hl, hm, hmesh⟩ := exists_part hat (lt_min hδ hδ'0)
    have a1 := hδ' n r h0 hl hm fun i => (hmesh i).trans_le (min_le_left _ _)
    have a2 := hδ'' n r h0 hl hm fun i => (hmesh i).trans_le (min_le_right _ _)
    have hR := aesm_riemannSum V hD h0 hl hm
    have : Z - Z' = (fun ω => Z ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω) -
        (fun ω => Z' ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω) := by
      funext ω; simp
    rw [this]
    calc eLpNorm _ 2 P ≤ eLpNorm (fun ω => Z ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω) 2 P +
          eLpNorm (fun ω => Z' ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω) 2 P :=
          eLpNorm_sub_le (by norm_num)
      _ ≤ ENNReal.ofReal ((η : ℝ) / 2) + ENNReal.ofReal ((η : ℝ) / 2) := add_le_add a1.le a2.le
      _ = 0 + (η : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_add hη2.le hη2.le]
          have : (η : ℝ) / 2 + (η : ℝ) / 2 = η := by ring
          rw [this, zero_add, ENNReal.ofReal_coe_nnreal]
  have := (eLpNorm_eq_zero_iff (by norm_num)).1 hz
  filter_upwards [this] with ω hω
  simpa [sub_eq_zero] using hω

lemma sc_congr_ae {P : Measure Ω} {V : ℝ → ℝ → E →L[ℝ] E} {D : ℝ → Ω → E} {a t : ℝ} {Z Z' : Ω → E}
    (h : Z =ᵐ[P] Z') (hS : SC P V D a t Z) : SC P V D a t Z' := by
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hS ε hε
  refine ⟨δ, hδ, fun n r h0 hl hm hmesh => ?_⟩
  have := hδ' n r h0 hl hm hmesh
  rwa [eLpNorm_congr_ae (g := fun ω => Z ω - riemannSum V (ContinuousLinearMap.id ℝ E) D t r ω)
    (by filter_upwards [h] with ω hω; simp [hω])]

/-- The zero convolution on a degenerate interval. -/
lemma sc_zero_interval {P : Measure Ω} {V : ℝ → ℝ → E →L[ℝ] E} {D : ℝ → Ω → E} {a : ℝ} :
    SC P V D a a (0 : Ω → E) := by
  intro ε hε
  refine ⟨1, one_pos, fun n r h0 hl hm _ => ?_⟩
  have hr : ∀ i, r i = a := fun i =>
    le_antisymm (hl ▸ hm (Fin.le_last i)) (h0 ▸ hm (Fin.zero_le i))
  have : (fun ω => (0 : Ω → E) ω - riemannSum V (ContinuousLinearMap.id ℝ E) D a r ω) = 0 := by
    funext ω
    simp [riemannSum_id, hr]
  rw [this]
  simpa using ENNReal.ofReal_pos.2 hε

end HRS.Uniform.Q48d
