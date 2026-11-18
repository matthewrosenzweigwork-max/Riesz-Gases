import HRS.MC.E213U3E

/-!
# Packet E213U3, part F: gluing, the block induction and the weighted bound for the window tensor

`Good`: existence of a window tensor with the evaluation predicate `SJW` and the weighted norm bound;
`u3_glue`: adjacent intervals; `u3_far_ind`: induction over the unit blocks `(j, j+1]`; `u3_decay`: the weighted bound
for `(α, β] ⊂ [0, a+T]` (near piece + blocks).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U3

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.S7PIDS HRS.MC.E213O HRS.Uniform

set_option maxSynthPendingDepth 3

variable {d : ℕ}

/-- A window tensor for `(α, β]` with the weighted bound. -/
def Good (R : Regime d) (r m T a C c : ℝ) (z : ℝ → NegSobolev d r) (α β : ℝ) : Prop :=
  ∃ X : TensorDual (PathSpace d m T) 2, SJW R r m T a z (Set.Ioc α β) X ∧
    ‖X‖ ≤ C * ∫ v in Set.Ioc α β, Real.exp (-c * (a - v)) * ‖z v‖

theorem u3_good_self (R : Regime d) (r m T a C c : ℝ) (hC : 0 ≤ C) (z : ℝ → NegSobolev d r) (α : ℝ) :
    Good R r m T a C c z α α := by
  refine ⟨0, ?_, ?_⟩
  · rw [Set.Ioc_self]; exact u3_SJW_empty R r m T a z
  · rw [Set.Ioc_self]; simp

/-- Integrability of the weighted norm. -/
theorem u3_wint {r c a T : ℝ} (hc : 0 ≤ c) {z : ℝ → NegSobolev d r} (hz : Measurable z) {S : Set ℝ}
    (hSm : MeasurableSet S) (hS : ∀ v ∈ S, v ≤ a + T) (hint : IntegrableOn (fun v => ‖z v‖) S) :
    IntegrableOn (fun v => Real.exp (-c * (a - v)) * ‖z v‖) S := by
  refine Integrable.mono' (hint.const_mul (Real.exp (c * T))) ?_ ?_
  · exact ((Real.continuous_exp.comp (by fun_prop : Continuous fun v : ℝ => -c * (a - v))).aestronglyMeasurable.mul
      hz.norm.aestronglyMeasurable)
  · refine (ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun v hv => ?_)
    have hv' : v ≤ a + T := hS v hv
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_norm]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    nlinarith [mul_nonneg hc (sub_nonneg.2 hv')]

theorem u3_glue (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m)
    (T : ℝ) (hT : 0 < T) (a C c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (z : ℝ → NegSobolev d r)
    (hz : Measurable z) {α γ β : ℝ} (h0 : 0 ≤ α) (hαγ : α ≤ γ) (hγβ : γ ≤ β) (hβ : β ≤ a + T)
    (hint : IntegrableOn (fun v => ‖z v‖) (Set.Ioc α β))
    (h₁ : Good R r m T a C c z α γ) (h₂ : Good R r m T a C c z γ β) : Good R r m T a C c z α β := by
  obtain ⟨X₁, hX₁, hn₁⟩ := h₁
  obtain ⟨X₂, hX₂, hn₂⟩ := h₂
  have hG : 0 < a + T := by linarith
  have hsub1 : Set.Ioc α γ ⊆ Set.Ioc α β := Set.Ioc_subset_Ioc_right hγβ
  have hsub2 : Set.Ioc γ β ⊆ Set.Ioc α β := Set.Ioc_subset_Ioc_left hαγ
  have hi1 : IntegrableOn (fun v => ‖z v‖) (Set.Ioc α γ) := hint.mono_set hsub1
  have hi2 : IntegrableOn (fun v => ‖z v‖) (Set.Ioc γ β) := hint.mono_set hsub2
  have hO1 : IntOK R r m (a + T) z (Set.Ioc α γ) :=
    u3_intOK R r hr m hm (a + T) hG z hz measurableSet_Ioc
      (fun v hv => ⟨lt_of_le_of_lt h0 hv.1, hv.2.trans (hγβ.trans hβ)⟩) hi1
  have hO2 : IntOK R r m (a + T) z (Set.Ioc γ β) :=
    u3_intOK R r hr m hm (a + T) hG z hz measurableSet_Ioc
      (fun v hv => ⟨lt_of_le_of_lt h0 (lt_of_le_of_lt hαγ hv.1), hv.2.trans hβ⟩) hi2
  have hdisj : Disjoint (Set.Ioc α γ) (Set.Ioc γ β) :=
    Set.disjoint_left.2 fun x hx hx' => by linarith [hx.2, hx'.1]
  refine ⟨X₁ + X₂, ?_, ?_⟩
  · have := u3_SJW_union R r m T a ha hdisj measurableSet_Ioc hX₁ hX₂ hO1 hO2
    rwa [Set.Ioc_union_Ioc_eq_Ioc hαγ hγβ] at this
  · have hw1 := u3_wint hc hz (a := a) (T := T) measurableSet_Ioc
      (fun v hv => hv.2.trans (hγβ.trans hβ)) hi1
    have hw2 := u3_wint hc hz (a := a) (T := T) measurableSet_Ioc (fun v hv => hv.2.trans hβ) hi2
    calc ‖X₁ + X₂‖ ≤ ‖X₁‖ + ‖X₂‖ := norm_add_le _ _
      _ ≤ C * (∫ v in Set.Ioc α γ, Real.exp (-c * (a - v)) * ‖z v‖) +
          C * ∫ v in Set.Ioc γ β, Real.exp (-c * (a - v)) * ‖z v‖ := add_le_add hn₁ hn₂
      _ = C * ∫ v in Set.Ioc α β, Real.exp (-c * (a - v)) * ‖z v‖ := by
          rw [← mul_add, ← setIntegral_union hdisj measurableSet_Ioc hw1 hw2,
            Set.Ioc_union_Ioc_eq_Ioc hαγ hγβ]

/-- From the block bound to `Good`. -/
theorem u3_good_of_block (R : Regime d) (r m T a j Cb C c : ℝ) (hc : 0 ≤ c) (hCb : 0 ≤ Cb)
    (hCC : Cb * Real.exp c ≤ C) (z : ℝ → NegSobolev d r) (hz : Measurable z) {α β : ℝ} (hjα : j ≤ α)
    (hβ : β ≤ a + T) (hint : IntegrableOn (fun v => ‖z v‖) (Set.Ioc α β))
    {X : TensorDual (PathSpace d m T) 2} (hX : SJW R r m T a z (Set.Ioc α β) X)
    (hn : ‖X‖ ≤ Cb * Real.exp (-c * (a - j - 1)) * ∫ v in Set.Ioc α β, ‖z v‖) :
    Good R r m T a C c z α β := by
  refine ⟨X, hX, ?_⟩
  have hw := u3_wint hc hz (a := a) (T := T) measurableSet_Ioc (fun v hv => hv.2.trans hβ) hint
  have key : ∫ v in Set.Ioc α β, Real.exp (-c * (a - j - 1)) * ‖z v‖ ≤
      ∫ v in Set.Ioc α β, Real.exp c * (Real.exp (-c * (a - v)) * ‖z v‖) := by
    refine setIntegral_mono_on (hint.const_mul _) (hw.const_mul _) measurableSet_Ioc (fun v hv => ?_)
    rw [← mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    nlinarith [mul_nonneg hc (sub_nonneg.2 (hjα.trans hv.1.le))]
  rw [integral_const_mul, integral_const_mul] at key
  have hI0 : 0 ≤ ∫ v in Set.Ioc α β, Real.exp (-c * (a - v)) * ‖z v‖ :=
    setIntegral_nonneg measurableSet_Ioc fun v _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  calc ‖X‖ ≤ Cb * Real.exp (-c * (a - j - 1)) * ∫ v in Set.Ioc α β, ‖z v‖ := hn
    _ = Cb * (Real.exp (-c * (a - j - 1)) * ∫ v in Set.Ioc α β, ‖z v‖) := by ring
    _ ≤ Cb * (Real.exp c * ∫ v in Set.Ioc α β, Real.exp (-c * (a - v)) * ‖z v‖) :=
        mul_le_mul_of_nonneg_left key hCb
    _ = (Cb * Real.exp c) * ∫ v in Set.Ioc α β, Real.exp (-c * (a - v)) * ‖z v‖ := by ring
    _ ≤ C * ∫ v in Set.Ioc α β, Real.exp (-c * (a - v)) * ‖z v‖ := mul_le_mul_of_nonneg_right hCC hI0

/-- From the near bound to `Good`. -/
theorem u3_good_of_near (R : Regime d) (r m T a Cn C c : ℝ) (hc : 0 ≤ c) (hCn : 0 ≤ Cn)
    (hCC : Cn * Real.exp c ≤ C) (z : ℝ → NegSobolev d r) (hz : Measurable z) {α β : ℝ}
    (hα : a - 1 ≤ α) (hβ : β ≤ a + T) (hint : IntegrableOn (fun v => ‖z v‖) (Set.Ioc α β))
    {X : TensorDual (PathSpace d m T) 2} (hX : SJW R r m T a z (Set.Ioc α β) X)
    (hn : ‖X‖ ≤ Cn * ∫ v in Set.Ioc α β, ‖z v‖) :
    Good R r m T a C c z α β := by
  refine ⟨X, hX, ?_⟩
  have hw := u3_wint hc hz (a := a) (T := T) measurableSet_Ioc (fun v hv => hv.2.trans hβ) hint
  have key : ∫ v in Set.Ioc α β, ‖z v‖ ≤
      ∫ v in Set.Ioc α β, Real.exp c * (Real.exp (-c * (a - v)) * ‖z v‖) := by
    refine setIntegral_mono_on hint (hw.const_mul _) measurableSet_Ioc (fun v hv => ?_)
    rw [← mul_assoc, ← Real.exp_add]
    have h1 : 1 ≤ Real.exp (c + -c * (a - v)) := by
      rw [← Real.exp_zero]
      refine Real.exp_le_exp.2 ?_
      nlinarith [mul_nonneg hc (show 0 ≤ 1 - (a - v) by linarith [hv.1])]
    calc ‖z v‖ = 1 * ‖z v‖ := (one_mul _).symm
      _ ≤ Real.exp (c + -c * (a - v)) * ‖z v‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  rw [integral_const_mul] at key
  have hI0 : 0 ≤ ∫ v in Set.Ioc α β, Real.exp (-c * (a - v)) * ‖z v‖ :=
    setIntegral_nonneg measurableSet_Ioc fun v _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  calc ‖X‖ ≤ Cn * ∫ v in Set.Ioc α β, ‖z v‖ := hn
    _ ≤ Cn * (Real.exp c * ∫ v in Set.Ioc α β, Real.exp (-c * (a - v)) * ‖z v‖) :=
        mul_le_mul_of_nonneg_left key hCn
    _ = (Cn * Real.exp c) * ∫ v in Set.Ioc α β, Real.exp (-c * (a - v)) * ‖z v‖ := by ring
    _ ≤ C * ∫ v in Set.Ioc α β, Real.exp (-c * (a - v)) * ‖z v‖ := mul_le_mul_of_nonneg_right hCC hI0

/-- Induction over the unit blocks. -/
theorem u3_far_ind (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (a C c : ℝ) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hc : 0 ≤ c) (z : ℝ → NegSobolev d r) (hz : Measurable z)
    (hB : ∀ j : ℝ, 0 ≤ j → j + 1 ≤ a → ∀ α β : ℝ, j ≤ α → α ≤ β → β ≤ j + 1 →
      IntegrableOn (fun v => ‖z v‖) (Set.Ioc α β) → Good R r m T a C c z α β) :
    ∀ n : ℕ, (n : ℝ) ≤ a → ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ n →
      IntegrableOn (fun v => ‖z v‖) (Set.Ioc α β) → Good R r m T a C c z α β := by
  intro n
  induction n with
  | zero =>
    intro hn α β h0 hαβ hβ hint
    have : α = β := by simp at hβ; linarith
    subst this
    exact u3_good_self R r m T a C c hC z α
  | succ n ih =>
    intro hn α β h0 hαβ hβ hint
    push_cast at hn hβ
    have hn' : (n : ℝ) ≤ a := by linarith
    have hβT : β ≤ a + T := by linarith
    by_cases h1 : β ≤ n
    · exact ih hn' α β h0 hαβ h1 hint
    · push_neg at h1
      by_cases h2 : (n : ℝ) ≤ α
      · exact hB n (Nat.cast_nonneg n) hn α β h2 hαβ hβ hint
      · push_neg at h2
        exact u3_glue R r hr m hm T hT a C c ha hc z hz h0 h2.le h1.le hβT hint
          (ih hn' α n h0 h2.le le_rfl (hint.mono_set (Set.Ioc_subset_Ioc_right h1.le)))
          (hB n (Nat.cast_nonneg n) hn n β le_rfl h1.le hβ
            (hint.mono_set (Set.Ioc_subset_Ioc_left h2.le)))

/-- **The weighted bound for the window tensor** (near piece + unit blocks). -/
theorem u3_decay (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (m : ℝ)
    (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hdual : IsDualEvolution R.D R.ρ m Vev)
    (hplain : ∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) (Cm cm : ℝ) (hcm : 0 < cm)
    (hdec : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Cm * Real.exp (-cm * (t - u))) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ a : ℝ, 0 ≤ a → ∀ z : ℝ → NegSobolev d r, Measurable z →
      ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ a + T → IntegrableOn (fun v => ‖z v‖) (Set.Ioc α β) →
      Good R r m T a C c z α β := by
  obtain ⟨Cn, hCn0, hnear⟩ := u3_near R r hr m hm T hT
  obtain ⟨Cb, hCb0, hblock⟩ := u3_block R r hr m hm T hT Vev hdual hplain Cm cm hcm.le hdec
  have hc0 : 0 < 2 * cm := by linarith
  refine ⟨(Cn + Cb) * Real.exp (2 * cm), 2 * cm, by positivity, hc0, fun a ha z hz α β h0 hαβ hβ hint => ?_⟩
  set c := 2 * cm with hcdef
  set C := (Cn + Cb) * Real.exp c with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hCnC : Cn * Real.exp c ≤ C := by
    rw [hCdef]; exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  have hCbC : Cb * Real.exp c ≤ C := by
    rw [hCdef]; exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  -- the near piece
  have hN : ∀ α β : ℝ, a - min a 1 ≤ α → α ≤ β → β ≤ a + T →
      IntegrableOn (fun v => ‖z v‖) (Set.Ioc α β) → Good R r m T a C c z α β := by
    intro α β hα hαβ hβ hint
    obtain ⟨X, hX, hn⟩ := hnear a ha z hz α β hα hαβ hβ hint
    exact u3_good_of_near R r m T a Cn C c hc0.le hCn0 hCnC z hz (by linarith [min_le_right a (1 : ℝ)])
      hβ hint hX hn
  -- the blocks
  have hBl : ∀ j : ℝ, 0 ≤ j → j + 1 ≤ a → ∀ α β : ℝ, j ≤ α → α ≤ β → β ≤ j + 1 →
      IntegrableOn (fun v => ‖z v‖) (Set.Ioc α β) → Good R r m T a C c z α β := by
    intro j hj hja α β hjα hαβ hβ hint
    obtain ⟨X, hX, hn⟩ := hblock a j hj hja z hz α β hjα hαβ hβ hint
    exact u3_good_of_block R r m T a j Cb C c hc0.le hCb0 hCbC z hz hjα (by linarith) hint hX hn
  -- the grid
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, n₀ = ⌊a⌋₊ := ⟨_, rfl⟩
  have hn₀a : (n₀ : ℝ) ≤ a := by rw [hn₀]; exact Nat.floor_le ha
  have han₀ : a < n₀ + 1 := by rw [hn₀]; exact Nat.lt_floor_add_one a
  have hn₀m : a - min a 1 ≤ n₀ := by
    rcases min_cases a 1 with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; simp
    · rw [h]; linarith
  have hfar := u3_far_ind R r hr m hm T hT a C c ha hC0 hc0.le z hz hBl n₀ hn₀a
  by_cases h1 : β ≤ n₀
  · exact hfar α β h0 hαβ h1 hint
  · push_neg at h1
    by_cases h2 : (n₀ : ℝ) ≤ α
    · exact hN α β (hn₀m.trans h2) hαβ hβ hint
    · push_neg at h2
      exact u3_glue R r hr m hm T hT a C c ha hc0.le z hz h0 h2.le h1.le hβ hint
        (hfar α n₀ h0 h2.le le_rfl (hint.mono_set (Set.Ioc_subset_Ioc_right h1.le)))
        (hN n₀ β hn₀m h1.le hβ (hint.mono_set (Set.Ioc_subset_Ioc_left h2.le)))

end HRS.MC.E213U3

end
