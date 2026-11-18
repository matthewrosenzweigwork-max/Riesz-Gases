import HRS.Sections.AdjKAAux13

/-!
# ADJKA part 14: the splitting `Z_t = V^{t,s} Z_s + ∫_s^t V^{t,u} dM_u`
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.AdjK

open HRS HRS.Uniform

variable {Ω : Type*} [MeasurableSpace Ω]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- Uniqueness of the `L²` limit when the second candidate is only known to be a limit along a
sequence of fine partitions. -/
theorem adjka_isStochConv_unique_seq {P : Measure Ω} {V : ℝ → ℝ → E →L[ℝ] E} {M : ℝ → Ω → E} {a t : ℝ}
    (hM : ∀ τ ∈ Icc a t, AEStronglyMeasurable (M τ) P) {Z₁ Z₂ : Ω → E}
    (hZ₁m : AEMeasurable Z₁ P) (hZ₂m : AEMeasurable Z₂ P)
    (h₁ : IsStochConv P V (ContinuousLinearMap.id ℝ E) M a t Z₁)
    (h₂ : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (r : Fin (n + 1) → ℝ), r 0 = a ∧
      r (Fin.last n) = t ∧ Monotone r ∧ (∀ i : Fin n, r i.succ - r i.castSucc < δ) ∧
      ∫⁻ ω, ‖Z₂ ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t r ω‖ₑ ^ 2 ∂P < ENNReal.ofReal ε) :
    Z₁ =ᵐ[P] Z₂ := by
  have key : ∀ ε : ℝ, 0 < ε → ∫⁻ ω, ‖Z₁ ω - Z₂ ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨δ1, hδ1, a1⟩ := h₁ (ε / 4) (by positivity)
    obtain ⟨n, r, p0, p1, p2, p3, b2⟩ := h₂ (ε / 4) (by positivity) δ1 hδ1
    have b1 := a1 n r p0 p1 p2 p3
    have hf1m : AEMeasurable (fun ω => ‖Z₁ ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t r ω‖ₑ ^ 2) P :=
      ((hZ₁m.sub (adjka_rs_aemeasurable V hM p0 p1 p2)).enorm).pow_const 2
    calc ∫⁻ ω, ‖Z₁ ω - Z₂ ω‖ₑ ^ 2 ∂P
        ≤ ∫⁻ ω, 2 * (‖Z₁ ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t r ω‖ₑ ^ 2 +
            ‖Z₂ ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t r ω‖ₑ ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          refine le_trans ?_ (adjka_sq_add_le _ _)
          gcongr
          refine le_trans (le_of_eq ?_) (enorm_sub_le (a := Z₁ ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t r ω)
            (b := Z₂ ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t r ω))
          congr 1
          abel
      _ = 2 * (∫⁻ ω, ‖Z₁ ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t r ω‖ₑ ^ 2 ∂P +
            ∫⁻ ω, ‖Z₂ ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t r ω‖ₑ ^ 2 ∂P) := by
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


/-- `Z_t = V^{t,s} Z_s + ∫_s^t V^{t,u} dM_u` almost surely. -/
theorem adjka_splitting {P : Measure Ω} {V : ℝ → ℝ → E →L[ℝ] E} {M : ℝ → Ω → E} {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t)
    (hcoc : ∀ a b c : ℝ, 0 ≤ a → a ≤ b → b ≤ c → c ≤ t → (V c b).comp (V b a) = V c a)
    (hM : ∀ τ ∈ Icc (0 : ℝ) t, AEStronglyMeasurable (M τ) P)
    {Zt Zs Z' : Ω → E} (hZt : IsStochConv P V (ContinuousLinearMap.id ℝ E) M 0 t Zt)
    (hZs : IsStochConv P V (ContinuousLinearMap.id ℝ E) M 0 s Zs)
    (hZ' : IsStochConv P V (ContinuousLinearMap.id ℝ E) M s t Z')
    (hZtm : AEMeasurable Zt P) (hZsm : AEMeasurable Zs P) (hZ'm : AEMeasurable Z' P) :
    Zt =ᵐ[P] fun ω => V t s (Zs ω) + Z' ω := by
  have hMs : ∀ τ ∈ Icc (0 : ℝ) s, AEStronglyMeasurable (M τ) P := fun τ hτ => hM τ ⟨hτ.1, hτ.2.trans hst⟩
  have hMst : ∀ τ ∈ Icc s t, AEStronglyMeasurable (M τ) P := fun τ hτ => hM τ ⟨hs.trans hτ.1, hτ.2⟩
  have hWm : AEMeasurable (fun ω => V t s (Zs ω) + Z' ω) P :=
    ((V t s).continuous.measurable.comp_aemeasurable hZsm).add hZ'm
  refine adjka_isStochConv_unique_seq hM hZtm hWm hZt ?_
  intro ε hε δ hδ
  set B : ℝ := ‖V t s‖ with hB
  have hB0 : 0 ≤ B := norm_nonneg _
  have hε1 : 0 < ε / (8 * (B ^ 2 + 1)) := by positivity
  obtain ⟨δa, hδa, ha⟩ := hZs (ε / (8 * (B ^ 2 + 1))) hε1
  obtain ⟨δb, hδb, hb⟩ := hZ' (ε / 8) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (t / min δ (min δa δb))
  have hm0 : 0 < min δ (min δa δb) := lt_min hδ (lt_min hδa hδb)
  have ht0 : 0 ≤ t := hs.trans hst
  have hstep : t / ((N : ℝ) + 1) < min δ (min δa δb) := by
    rw [div_lt_iff₀ (by positivity)]
    have : t / min δ (min δa δb) < N + 1 := by linarith
    rw [div_lt_iff₀ hm0] at this
    linarith
  have hst1 : ∀ x : ℝ, x ≤ t → x / ((N : ℝ) + 1) < min δ (min δa δb) := fun x hx =>
    lt_of_le_of_lt (div_le_div_of_nonneg_right hx (by positivity)) hstep
  refine ⟨(N + 1) + (N + 1), adjkCat s t N, adjkCat_zero s t N, adjkCat_last s t N,
    adjkCat_mono hs hst N, fun i => ?_, ?_⟩
  · exact (adjkCat_step hs hst N i).trans_lt (hstep.trans_le (min_le_left _ _))
  · -- the Riemann sum identity
    have b1 := ha (N + 1) (adjkGrid 0 s N) (adjkGrid_zero 0 s N) (adjkGrid_last 0 s N)
      (adjkGrid_mono hs N) (fun i => by
        rw [adjkGrid_step]
        exact (hst1 _ (by linarith)).trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    have b2 := hb (N + 1) (adjkGrid s t N) (adjkGrid_zero s t N) (adjkGrid_last s t N)
      (adjkGrid_mono hst N) (fun i => by
        rw [adjkGrid_step]
        exact (hst1 _ (by linarith)).trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    have hrs1 : AEMeasurable (riemannSum V (ContinuousLinearMap.id ℝ E) M s (adjkGrid 0 s N)) P :=
      adjka_rs_aemeasurable V hMs (adjkGrid_zero 0 s N) (adjkGrid_last 0 s N) (adjkGrid_mono hs N)
    have hrs2 : AEMeasurable (riemannSum V (ContinuousLinearMap.id ℝ E) M t (adjkGrid s t N)) P :=
      adjka_rs_aemeasurable V hMst (adjkGrid_zero s t N) (adjkGrid_last s t N) (adjkGrid_mono hst N)
    have hVe : ∀ x : E, ‖V t s x‖ₑ ≤ ENNReal.ofReal B * ‖x‖ₑ := fun x => by
      rw [← ofReal_norm_eq_enorm (V t s x), ← ofReal_norm_eq_enorm x, ← ENNReal.ofReal_mul hB0]
      exact ENNReal.ofReal_le_ofReal ((V t s).le_opNorm x)
    set u : Ω → ℝ≥0∞ := fun ω => ‖Zs ω - riemannSum V (ContinuousLinearMap.id ℝ E) M s (adjkGrid 0 s N) ω‖ₑ ^ 2
      with hu
    set v : Ω → ℝ≥0∞ := fun ω => ‖Z' ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t (adjkGrid s t N) ω‖ₑ ^ 2
      with hv
    have hum : AEMeasurable u P := ((hZsm.sub hrs1).enorm).pow_const 2
    have hpt : ∀ ω, ‖(V t s (Zs ω) + Z' ω) - riemannSum V (ContinuousLinearMap.id ℝ E) M t (adjkCat s t N) ω‖ₑ ^ 2 ≤
        2 * (ENNReal.ofReal (B ^ 2) * u ω + v ω) := by
      intro ω
      rw [adjka_rs_cat V M hs hst hcoc N ω]
      have e : (V t s (Zs ω) + Z' ω) - (V t s (riemannSum V (ContinuousLinearMap.id ℝ E) M s (adjkGrid 0 s N) ω) +
          riemannSum V (ContinuousLinearMap.id ℝ E) M t (adjkGrid s t N) ω) =
          V t s (Zs ω - riemannSum V (ContinuousLinearMap.id ℝ E) M s (adjkGrid 0 s N) ω) +
            (Z' ω - riemannSum V (ContinuousLinearMap.id ℝ E) M t (adjkGrid s t N) ω) := by
        rw [map_sub]; abel
      rw [e]
      refine le_trans (pow_le_pow_left' (enorm_add_le _ _) 2) (le_trans (adjka_sq_add_le _ _) ?_)
      gcongr
      calc ‖V t s (Zs ω - riemannSum V (ContinuousLinearMap.id ℝ E) M s (adjkGrid 0 s N) ω)‖ₑ ^ 2
          ≤ (ENNReal.ofReal B * ‖Zs ω - riemannSum V (ContinuousLinearMap.id ℝ E) M s (adjkGrid 0 s N) ω‖ₑ) ^ 2 :=
            pow_le_pow_left' (hVe _) 2
        _ = ENNReal.ofReal (B ^ 2) * u ω := by
            rw [mul_pow, ENNReal.ofReal_pow hB0]
    have hε8 : ENNReal.ofReal (B ^ 2) * ENNReal.ofReal (ε / (8 * (B ^ 2 + 1))) ≤ ENNReal.ofReal (ε / 8) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg B, hε]
    calc ∫⁻ ω, ‖(V t s (Zs ω) + Z' ω) - riemannSum V (ContinuousLinearMap.id ℝ E) M t (adjkCat s t N) ω‖ₑ ^ 2 ∂P
        ≤ ∫⁻ ω, 2 * (ENNReal.ofReal (B ^ 2) * u ω + v ω) ∂P := lintegral_mono hpt
      _ = 2 * (ENNReal.ofReal (B ^ 2) * ∫⁻ ω, u ω ∂P + ∫⁻ ω, v ω ∂P) := by
          rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left' (hum.const_mul _),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ 2 * (ENNReal.ofReal (ε / 8) + ENNReal.ofReal (ε / 8)) := by
          gcongr
          exact (mul_le_mul_of_nonneg_left b1.le bot_le).trans hε8
      _ = ENNReal.ofReal (ε / 8 * 4) := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (by norm_num)]
          congr 1; ring
      _ < ENNReal.ofReal ε := by
          rw [ENNReal.ofReal_lt_ofReal_iff hε]
          linarith

end HRS.AdjK
