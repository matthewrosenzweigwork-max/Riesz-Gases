import HRS.MS.SuppU8Aux1

/-!
# Worker U8 aux 2: crude bound by shifted values, boundedness, and the adjoint identity
-/

noncomputable section

open MeasureTheory Metric Set

namespace HRS.U8

section Crude

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E]
  [NormedSpace ℝ E]

theorem u8_sum_shift_le (g : ℤ → ℝ) (hg : ∀ k, 0 ≤ g k) (n : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    ∑ j ∈ Finset.Icc (-(n : ℤ)) n, g (j + σ) ≤ ∑ k ∈ Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ), g k := by
  have hinj : ∀ x ∈ Finset.Icc (-(n : ℤ)) n, ∀ y ∈ Finset.Icc (-(n : ℤ)) n,
      (fun j : ℤ => j + σ) x = (fun j : ℤ => j + σ) y → x = y := by
    intro x _ y _ hxy
    simpa using hxy
  rw [← Finset.sum_image hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_image, Finset.mem_Icc] at hk ⊢
    obtain ⟨j, ⟨h1, h2⟩, rfl⟩ := hk
    push_cast
    rcases hσ with rfl | rfl <;> constructor <;> omega
  · intro k _ _
    exact hg k

theorem u8_fd_crude (y : V) : ∀ (L : List V) (u : V → E) (x : V), (∀ h ∈ L, h = y ∨ h = -y) →
    ‖u8_fd L u x‖ ≤ 2 ^ L.length * ∑ j ∈ Finset.Icc (-(L.length : ℤ)) L.length,
      ‖u (x + j • y)‖ := by
  intro L
  induction L with
  | nil =>
    intro u x _
    simp [u8_fd_nil]
  | cons h hs ih =>
    intro u x hL
    have hh : ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ h = σ • y := by
      rcases hL h (by simp) with h1 | h1
      · exact ⟨1, Or.inl rfl, by simp [h1]⟩
      · exact ⟨-1, Or.inr rfl, by simp [h1]⟩
    obtain ⟨σ, hσ, hhσ⟩ := hh
    rw [u8_fd_cons]
    have key := ih (fun x => u (x + h) - u x) x (fun g hg => hL g (by simp [hg]))
    have hb : ∀ j : ℤ, ‖(fun x => u (x + h) - u x) (x + j • y)‖ ≤
        ‖u (x + (j + σ) • y)‖ + ‖u (x + j • y)‖ := by
      intro j
      have e : x + j • y + h = x + (j + σ) • y := by
        rw [hhσ, add_zsmul]; abel
      calc ‖(fun x => u (x + h) - u x) (x + j • y)‖ = ‖u (x + j • y + h) - u (x + j • y)‖ := rfl
        _ ≤ ‖u (x + j • y + h)‖ + ‖u (x + j • y)‖ := norm_sub_le _ _
        _ = _ := by rw [e]
    set n := hs.length
    have h1 : ∑ j ∈ Finset.Icc (-(n : ℤ)) n, ‖(fun x => u (x + h) - u x) (x + j • y)‖ ≤
        ∑ j ∈ Finset.Icc (-(n : ℤ)) n, (‖u (x + (j + σ) • y)‖ + ‖u (x + j • y)‖) :=
      Finset.sum_le_sum (fun j _ => hb j)
    rw [Finset.sum_add_distrib] at h1
    have h2 := u8_sum_shift_le (fun k : ℤ => ‖u (x + k • y)‖) (fun k => norm_nonneg _) n σ hσ
    have h3 : ∑ j ∈ Finset.Icc (-(n : ℤ)) n, ‖u (x + j • y)‖ ≤
        ∑ k ∈ Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ), ‖u (x + k • y)‖ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        simp only [Finset.mem_Icc] at hk ⊢
        push_cast
        omega
      · intro k _ _; exact norm_nonneg _
    calc ‖u8_fd hs (fun x => u (x + h) - u x) x‖
        ≤ 2 ^ n * ∑ j ∈ Finset.Icc (-(n : ℤ)) n, ‖(fun x => u (x + h) - u x) (x + j • y)‖ := key
      _ ≤ 2 ^ n * (2 * ∑ k ∈ Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ), ‖u (x + k • y)‖) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      _ = 2 ^ (h :: hs).length * ∑ j ∈ Finset.Icc (-((h :: hs).length : ℤ)) (h :: hs).length,
          ‖u (x + j • y)‖ := by
        simp only [List.length_cons, pow_succ]; ring

end Crude

section Adjoint

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem u8_fd_cont_bdd (L : List V) : ∀ (u : V → ℂ), Continuous u → (∃ C, ∀ x, ‖u x‖ ≤ C) →
    Continuous (u8_fd L u) ∧ ∃ C, ∀ x, ‖u8_fd L u x‖ ≤ C := by
  induction L with
  | nil => intro u hu hb; exact ⟨hu, hb⟩
  | cons h hs ih =>
    intro u hu ⟨C, hC⟩
    rw [u8_fd_cons]
    apply ih
    · exact (hu.comp (continuous_id.add continuous_const)).sub hu
    · refine ⟨C + C, fun x => ?_⟩
      exact (norm_sub_le _ _).trans (add_le_add (hC _) (hC _))

theorem u8_fd_cont_int (L : List V) : ∀ (u : V → ℂ), Continuous u → Integrable u →
    Continuous (u8_fd L u) ∧ Integrable (u8_fd L u) := by
  induction L with
  | nil => intro u hu hi; exact ⟨hu, hi⟩
  | cons h hs ih =>
    intro u hu hi
    rw [u8_fd_cons]
    apply ih
    · exact (hu.comp (continuous_id.add continuous_const)).sub hu
    · exact (hi.comp_add_right h).sub hi

theorem u8_fd_adjoint (L : List V) : ∀ (f g : V → ℂ), Continuous f → (∃ C, ∀ x, ‖f x‖ ≤ C) →
    Continuous g → Integrable g →
    ∫ x, f x * u8_fd L g x = ∫ x, u8_fd (L.map Neg.neg) f x * g x := by
  induction L with
  | nil => intro f g _ _ _ _; rfl
  | cons h hs ih =>
    intro f g hf hfb hg hgi
    rw [u8_fd_cons]
    have hg' : Continuous (fun x => g (x + h) - g x) :=
      (hg.comp (continuous_id.add continuous_const)).sub hg
    have hgi' : Integrable (fun x => g (x + h) - g x) := (hgi.comp_add_right h).sub hgi
    rw [ih f _ hf hfb hg' hgi']
    set F := u8_fd (hs.map Neg.neg) f with hF
    obtain ⟨hFc, C0, hC0⟩ := u8_fd_cont_bdd (hs.map Neg.neg) f hf hfb
    have hcomm : u8_fd ((h :: hs).map Neg.neg) f = fun x => F (x + -h) - F x := by
      rw [List.map_cons, u8_fd_cons]
      exact u8_fd_comm _ f (-h)
    rw [hcomm]
    have i1 : Integrable (fun x => F x * g (x + h)) :=
      (hgi.comp_add_right h).bdd_mul hFc.aestronglyMeasurable (Filter.Eventually.of_forall hC0)
    have i2 : Integrable (fun x => F x * g x) :=
      hgi.bdd_mul hFc.aestronglyMeasurable (Filter.Eventually.of_forall hC0)
    have i3 : Integrable (fun x => F (x + -h) * g x) :=
      hgi.bdd_mul (hFc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun x => hC0 _))
    have e1 : ∫ x, F x * (g (x + h) - g x) = (∫ x, F x * g (x + h)) - ∫ x, F x * g x := by
      rw [← integral_sub i1 i2]
      congr 1; funext x; ring
    have e2 : ∫ x, (F (x + -h) - F x) * g x = (∫ x, F (x + -h) * g x) - ∫ x, F x * g x := by
      rw [← integral_sub i3 i2]
      congr 1; funext x; ring
    have e3 : ∫ x, F x * g (x + h) = ∫ x, F (x + -h) * g x := by
      have := integral_add_right_eq_self (μ := volume) (fun x => F (x + -h) * g x) h
      simp only [add_neg_cancel_right] at this
      exact this
    rw [e1, e2, e3]

end Adjoint

end HRS.U8
