import HRS.Sections.AdjKAAux6

/-!
# ADJKA part 7: calculus of `IsStochConv` (congruences, embedding, linearity, uniqueness, uniform grids)
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.AdjK

open HRS HRS.Uniform

variable {Ω : Type*} [MeasurableSpace Ω]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

theorem adjka_mem_part {a t : ℝ} {n : ℕ} {r : Fin (n + 1) → ℝ} (h0 : r 0 = a) (hn : r (Fin.last n) = t)
    (hmono : Monotone r) (i : Fin (n + 1)) : a ≤ r i ∧ r i ≤ t :=
  ⟨h0 ▸ hmono (Fin.zero_le i), hn ▸ hmono (Fin.le_last i)⟩

theorem adjka_isStochConv_congr_ev {P : Measure Ω} {V₁ V₂ : ℝ → ℝ → E →L[ℝ] E}
    {M : ℝ → Ω → E} {a t : ℝ} {Z : Ω → E} (h : ∀ s, a ≤ s → s ≤ t → V₁ t s = V₂ t s)
    (hZ : IsStochConv P V₁ (ContinuousLinearMap.id ℝ E) M a t Z) :
    IsStochConv P V₂ (ContinuousLinearMap.id ℝ E) M a t Z := by
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := hZ ε hε
  refine ⟨δ, hδ, fun n r h0 hn hmono hmesh => ?_⟩
  have := hh n r h0 hn hmono hmesh
  have e : riemannSum V₁ (ContinuousLinearMap.id ℝ E) M t r = riemannSum V₂ (ContinuousLinearMap.id ℝ E) M t r := by
    funext ω
    unfold riemannSum
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := adjka_mem_part h0 hn hmono i.castSucc
    rw [h _ hi.1 hi.2]
  rwa [e] at this

theorem adjka_isStochConv_congr_M {P : Measure Ω} {V : ℝ → ℝ → E →L[ℝ] E}
    {M M' : ℝ → Ω → E} {a t : ℝ} {Z : Ω → E} (h : ∀ τ ∈ Icc a t, ∀ ω, M τ ω = M' τ ω)
    (hZ : IsStochConv P V (ContinuousLinearMap.id ℝ E) M a t Z) :
    IsStochConv P V (ContinuousLinearMap.id ℝ E) M' a t Z := by
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := hZ ε hε
  refine ⟨δ, hδ, fun n r h0 hn hmono hmesh => ?_⟩
  have := hh n r h0 hn hmono hmesh
  have e : riemannSum V (ContinuousLinearMap.id ℝ E) M t r = riemannSum V (ContinuousLinearMap.id ℝ E) M' t r := by
    funext ω
    unfold riemannSum
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := adjka_mem_part h0 hn hmono i.castSucc
    have h2 := adjka_mem_part h0 hn hmono i.succ
    rw [h _ ⟨h1.1, h1.2⟩ ω, h _ ⟨h2.1, h2.2⟩ ω]
  rwa [e] at this


section Embed

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [NormedAddCommGroup E₂]
  [InnerProductSpace ℝ E₂]

theorem adjka_isStochConv_embed {P : Measure Ω} (ι : E₁ →L[ℝ] E₂) (hι : ∀ x, ‖ι x‖ ≤ ‖x‖)
    {Vj : ℝ → ℝ → E₁ →L[ℝ] E₁} {Vm : ℝ → ℝ → E₂ →L[ℝ] E₂} {N : ℝ → Ω → E₁} {a t : ℝ} {Z : Ω → E₁}
    (hint : ∀ s, a ≤ s → s ≤ t → ∀ x, Vm t s (ι x) = ι (Vj t s x))
    (h : IsStochConv P Vj (ContinuousLinearMap.id ℝ E₁) N a t Z) :
    IsStochConv P Vm (ContinuousLinearMap.id ℝ E₂) (fun τ ω => ι (N τ ω)) a t (fun ω => ι (Z ω)) := by
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := h ε hε
  refine ⟨δ, hδ, fun n r h0 hn hmono hmesh => ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) (hh n r h0 hn hmono hmesh)
  have e : riemannSum Vm (ContinuousLinearMap.id ℝ E₂) (fun τ ω => ι (N τ ω)) t r ω =
      ι (riemannSum Vj (ContinuousLinearMap.id ℝ E₁) N t r ω) := by
    unfold riemannSum
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := adjka_mem_part h0 hn hmono i.castSucc
    simp only [ContinuousLinearMap.id_apply]
    rw [← map_sub, hint _ h1.1 h1.2]
  rw [e, ← map_sub]
  gcongr
  exact enorm_le_iff_norm_le.2 (hι _)

end Embed


theorem adjka_sq_add_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  have h2 : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by norm_num
  rw [h2] at this
  simpa [ENNReal.rpow_two] using this

theorem adjka_eps_calc (ε : ℝ) (hε : 0 < ε) :
    (2 : ℝ≥0∞) * (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) = ENNReal.ofReal ε := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

theorem adjka_rs_aemeasurable {P : Measure Ω} (V : ℝ → ℝ → E →L[ℝ] E) {M : ℝ → Ω → E} {a t : ℝ}
    (hM : ∀ τ ∈ Icc a t, AEStronglyMeasurable (M τ) P) {n : ℕ} {r : Fin (n + 1) → ℝ}
    (h0 : r 0 = a) (hn : r (Fin.last n) = t) (hmono : Monotone r) :
    AEMeasurable (riemannSum V (ContinuousLinearMap.id ℝ E) M t r) P := by
  unfold riemannSum
  have : ∀ i : Fin n, AEMeasurable (fun ω => V t (r i.castSucc)
      ((ContinuousLinearMap.id ℝ E) (M (r i.succ) ω - M (r i.castSucc) ω))) P := fun i => by
    have h1 := adjka_mem_part h0 hn hmono i.castSucc
    have h2 := adjka_mem_part h0 hn hmono i.succ
    have := ((hM _ h2).sub (hM _ h1)).aemeasurable
    exact (V t (r i.castSucc)).continuous.measurable.comp_aemeasurable
      ((ContinuousLinearMap.id ℝ E).continuous.measurable.comp_aemeasurable this)
  have := Finset.aemeasurable_sum (μ := P) (Finset.univ : Finset (Fin n))
    (f := fun i ω => V t (r i.castSucc)
      ((ContinuousLinearMap.id ℝ E) (M (r i.succ) ω - M (r i.castSucc) ω))) fun i _ => this i
  simpa [Finset.sum_fn] using this

/-- Linearity of stochastic convolutions. -/
theorem adjka_isStochConv_add {P : Measure Ω} {V : ℝ → ℝ → E →L[ℝ] E} {M G : ℝ → Ω → E} {a t : ℝ}
    (hM : ∀ τ ∈ Icc a t, AEStronglyMeasurable (M τ) P) (hG : ∀ τ ∈ Icc a t, AEStronglyMeasurable (G τ) P)
    {Z₁ Z₂ : Ω → E} (hZ₁ : AEMeasurable Z₁ P)
    (h₁ : IsStochConv P V (ContinuousLinearMap.id ℝ E) M a t Z₁)
    (h₂ : IsStochConv P V (ContinuousLinearMap.id ℝ E) G a t Z₂) :
    IsStochConv P V (ContinuousLinearMap.id ℝ E) (fun τ ω => M τ ω + G τ ω) a t
      (fun ω => Z₁ ω + Z₂ ω) := by
  intro ε hε
  obtain ⟨δ1, hδ1, a1⟩ := h₁ (ε / 4) (by positivity)
  obtain ⟨δ2, hδ2, a2⟩ := h₂ (ε / 4) (by positivity)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun n r h0 hn hmono hmesh => ?_⟩
  have b1 := a1 n r h0 hn hmono (fun i => (hmesh i).trans_le (min_le_left _ _))
  have b2 := a2 n r h0 hn hmono (fun i => (hmesh i).trans_le (min_le_right _ _))
  have hrs : riemannSum V (ContinuousLinearMap.id ℝ E) (fun τ ω => M τ ω + G τ ω) t r =
      fun ω => riemannSum V (ContinuousLinearMap.id ℝ E) M t r ω +
        riemannSum V (ContinuousLinearMap.id ℝ E) G t r ω := by
    funext ω
    unfold riemannSum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_add, ← map_add]
    congr 2
    module
  have hf1m : AEMeasurable (fun ω => ‖Z₁ ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t r ω‖ₑ ^ 2) P :=
    ((hZ₁.sub (adjka_rs_aemeasurable V hM h0 hn hmono)).enorm).pow_const 2
  calc ∫⁻ ω, ‖(Z₁ ω + Z₂ ω) - riemannSum V (ContinuousLinearMap.id ℝ E) (fun τ ω => M τ ω + G τ ω) t r ω‖ₑ ^ 2 ∂P
      ≤ ∫⁻ ω, 2 * (‖Z₁ ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t r ω‖ₑ ^ 2 +
          ‖Z₂ ω - riemannSum V (ContinuousLinearMap.id ℝ E) G t r ω‖ₑ ^ 2) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [hrs]
        refine le_trans ?_ (adjka_sq_add_le _ _)
        gcongr
        refine le_trans (le_of_eq ?_) (enorm_add_le (Z₁ ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t r ω)
          (Z₂ ω - riemannSum V (ContinuousLinearMap.id ℝ E) G t r ω))
        congr 1
        module
    _ = 2 * (∫⁻ ω, ‖Z₁ ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t r ω‖ₑ ^ 2 ∂P +
          ∫⁻ ω, ‖Z₂ ω - riemannSum V (ContinuousLinearMap.id ℝ E) G t r ω‖ₑ ^ 2 ∂P) := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left' hf1m]
    _ < 2 * (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) := by
        refine (ENNReal.mul_lt_mul_iff_right (by simp) (by simp)).2 ?_
        exact ENNReal.add_lt_add b1 b2
    _ = ENNReal.ofReal ε := adjka_eps_calc ε hε

/-- The uniform grid `a + (t-a) i/(n+1)`. -/
def adjkGrid (a t : ℝ) (n : ℕ) : Fin (n + 2) → ℝ := fun i => a + (t - a) * ((i : ℕ) : ℝ) / ((n : ℝ) + 1)

theorem adjkGrid_zero (a t : ℝ) (n : ℕ) : adjkGrid a t n 0 = a := by simp [adjkGrid]

theorem adjkGrid_last (a t : ℝ) (n : ℕ) : adjkGrid a t n (Fin.last (n + 1)) = t := by
  simp only [adjkGrid, Fin.val_last]
  have : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem adjkGrid_mono {a t : ℝ} (hat : a ≤ t) (n : ℕ) : Monotone (adjkGrid a t n) := by
  intro i j hij
  have h : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij
  unfold adjkGrid
  have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have : (t - a) * ((i : ℕ) : ℝ) / ((n : ℝ) + 1) ≤ (t - a) * ((j : ℕ) : ℝ) / ((n : ℝ) + 1) := by
    gcongr
  linarith

theorem adjkGrid_step (a t : ℝ) (n : ℕ) (i : Fin (n + 1)) :
    adjkGrid a t n i.succ - adjkGrid a t n i.castSucc = (t - a) / ((n : ℝ) + 1) := by
  have hp : ((n : ℝ) + 1) ≠ 0 := by positivity
  simp only [adjkGrid, Fin.val_succ, Fin.val_castSucc]
  push_cast
  field_simp
  ring

/-- `L²`-uniqueness of stochastic convolutions. -/
theorem adjka_isStochConv_unique {P : Measure Ω} {V : ℝ → ℝ → E →L[ℝ] E} {M : ℝ → Ω → E} {a t : ℝ}
    (hat : a ≤ t) (hM : ∀ τ ∈ Icc a t, AEStronglyMeasurable (M τ) P) {Z₁ Z₂ : Ω → E}
    (hZ₁m : AEMeasurable Z₁ P) (hZ₂m : AEMeasurable Z₂ P)
    (h₁ : IsStochConv P V (ContinuousLinearMap.id ℝ E) M a t Z₁)
    (h₂ : IsStochConv P V (ContinuousLinearMap.id ℝ E) M a t Z₂) : Z₁ =ᵐ[P] Z₂ := by
  have key : ∀ ε : ℝ, 0 < ε → ∫⁻ ω, ‖Z₁ ω - Z₂ ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨δ1, hδ1, a1⟩ := h₁ (ε / 4) (by positivity)
    obtain ⟨δ2, hδ2, a2⟩ := h₂ (ε / 4) (by positivity)
    obtain ⟨N, hN⟩ := exists_nat_gt ((t - a) / min δ1 δ2)
    have hstep : (t - a) / ((N : ℝ) + 1) < min δ1 δ2 := by
      rw [div_lt_iff₀ (by positivity)]
      have : (t - a) / min δ1 δ2 < N + 1 := by linarith
      rw [div_lt_iff₀ (lt_min hδ1 hδ2)] at this
      linarith
    have p0 := adjkGrid_zero a t N
    have p1 := adjkGrid_last a t N
    have p2 := adjkGrid_mono hat N
    have hm1 : ∀ i : Fin (N + 1), adjkGrid a t N i.succ - adjkGrid a t N i.castSucc < δ1 := fun i => by
      rw [adjkGrid_step]; exact hstep.trans_le (min_le_left _ _)
    have hm2 : ∀ i : Fin (N + 1), adjkGrid a t N i.succ - adjkGrid a t N i.castSucc < δ2 := fun i => by
      rw [adjkGrid_step]; exact hstep.trans_le (min_le_right _ _)
    have b1 := a1 (N + 1) _ p0 p1 p2 hm1
    have b2 := a2 (N + 1) _ p0 p1 p2 hm2
    have hf1m : AEMeasurable (fun ω => ‖Z₁ ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t (adjkGrid a t N) ω‖ₑ ^ 2) P :=
      ((hZ₁m.sub (adjka_rs_aemeasurable V hM p0 p1 p2)).enorm).pow_const 2
    calc ∫⁻ ω, ‖Z₁ ω - Z₂ ω‖ₑ ^ 2 ∂P
        ≤ ∫⁻ ω, 2 * (‖Z₁ ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t (adjkGrid a t N) ω‖ₑ ^ 2 +
            ‖Z₂ ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t (adjkGrid a t N) ω‖ₑ ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          refine le_trans ?_ (adjka_sq_add_le _ _)
          gcongr
          refine le_trans (le_of_eq ?_) (enorm_sub_le (a := Z₁ ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t (adjkGrid a t N) ω)
            (b := Z₂ ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t (adjkGrid a t N) ω))
          congr 1
          abel
      _ = 2 * (∫⁻ ω, ‖Z₁ ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t (adjkGrid a t N) ω‖ₑ ^ 2 ∂P +
            ∫⁻ ω, ‖Z₂ ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t (adjkGrid a t N) ω‖ₑ ^ 2 ∂P) := by
          rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left' hf1m]
      _ ≤ 2 * (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) := by
          gcongr
      _ = ENNReal.ofReal ε := adjka_eps_calc ε hε
  have h0 : ∫⁻ ω, ‖Z₁ ω - Z₂ ω‖ₑ ^ 2 ∂P = 0 := by
    refine le_antisymm ?_ bot_le
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have := key (ε : ℝ) (by exact_mod_cast hε)
    simpa using this
  have hm : AEMeasurable (fun ω => ‖Z₁ ω - Z₂ ω‖ₑ ^ 2) P := ((hZ₁m.sub hZ₂m).enorm).pow_const 2
  rw [lintegral_eq_zero_iff' hm] at h0
  filter_upwards [h0] with ω hω
  have : ‖Z₁ ω - Z₂ ω‖ₑ = 0 := by simpa using hω
  have := enorm_eq_zero.1 this
  exact sub_eq_zero.1 this

end HRS.AdjK
