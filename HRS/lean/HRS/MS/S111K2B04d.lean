import HRS.MS.S111K2B04c

/-!
# S11.1 continuation, B04 (part 4): the `ℓ²`-valued coordinate vector `t ↦ (η(F_α(t)))_α`

`s111k2_ell_tendsto`: dominated convergence for `ℓ²` coordinates; `s111k2_Y_cont`: continuity of `t ↦ ellVec m (η ∘ F · t)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K2

open HRS HRS.Whole HRS.MS.FixEq

variable {d : ℕ}

lemma s111k2_ellVec_norm_sq_eq {m : ℝ} {v : MultiIndex d → ℝ} (hv : Memℓp v 2) :
    ‖(ellVec m v : OscDual d m)‖ ^ 2 = ∑' α, v α ^ 2 := by
  have := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (show lp (fun _ : MultiIndex d => ℝ) 2 from (ellVec m v : OscDual d m))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at this
  have hc : ∀ i, (show lp (fun _ : MultiIndex d => ℝ) 2 from (ellVec m v : OscDual d m)) i = v i := fun i =>
    s57p_coord_ellVec hv i
  simp_rw [hc, Real.norm_eq_abs, sq_abs] at this
  exact this

lemma s111k2_memell_of_le {v : MultiIndex d → ℝ} {g : MultiIndex d → ℝ} (hg : Summable g)
    (hv : ∀ α, v α ^ 2 ≤ g α) : Memℓp v 2 :=
  memℓp_two_iff.2 (Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hv hg)

lemma s111k2_ell_tendsto {m : ℝ} {cn : ℕ → MultiIndex d → ℝ} {c g : MultiIndex d → ℝ} (hg : Summable g)
    (hcn : ∀ n α, (cn n α - c α) ^ 2 ≤ g α) (hl : ∀ α, Tendsto (fun n => cn n α) atTop (𝓝 (c α)))
    (hmn : ∀ n, Memℓp (cn n) 2) (hm : Memℓp c 2) :
    Tendsto (fun n => (ellVec m (cn n) : OscDual d m)) atTop (𝓝 (ellVec m c)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsub : ∀ n, (ellVec m (cn n) : OscDual d m) - ellVec m c = ellVec m (fun α => cn n α - c α) :=
    fun n => s57p_ellVec_sub (hmn n) hm
  have hmem : ∀ n, Memℓp (fun α => cn n α - c α) 2 := fun n => s111k2_memell_of_le hg (hcn n)
  have h1 : Tendsto (fun n => ∑' α, (cn n α - c α) ^ 2) atTop (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := fun n α => (cn n α - c α) ^ 2)
      (g := fun _ => (0 : ℝ)) (bound := g) hg
      (fun α => by simpa using ((hl α).sub_const (c α)).pow 2)
      (Eventually.of_forall fun n α => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hcn n α)
    simpa using this
  have h2 : Tendsto (fun n => ‖(ellVec m (cn n) : OscDual d m) - ellVec m c‖) atTop (𝓝 0) := by
    have h3 : ∀ n, ‖(ellVec m (cn n) : OscDual d m) - ellVec m c‖ =
        Real.sqrt (∑' α, (cn n α - c α) ^ 2) := by
      intro n
      rw [hsub n, ← Real.sqrt_sq (norm_nonneg _), s111k2_ellVec_norm_sq_eq (hmem n)]
    simp_rw [h3]
    have := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at this
    exact this
  exact h2

/-- Qualitative derivative bound of `F - F 0`. -/
lemma s111k2_g_qual {r : ℕ} {Ft : Euc d → ℝ} (hFr : ContDiff ℝ r Ft) {A B0 : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B0)
    (hbd : ∀ x, |Ft x| ≤ B0) (hAj : ∀ j : ℕ, 1 ≤ j → j ≤ r → ∀ x, ‖iteratedFDeriv ℝ j Ft x‖ ≤ A) :
    ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (fun x => Ft x - Ft 0) x‖ ≤ 2 * B0 + A := by
  intro j hj x
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    have := hbd x; have := hbd 0
    have h1 : |Ft x - Ft 0| ≤ |Ft x| + |Ft 0| := abs_sub _ _
    linarith
  · rw [s111k2_iteratedFDeriv_sub_const (hFr.of_le (by exact_mod_cast hj)) _ (by omega)]
    have := hAj j hj0 hj x
    linarith

lemma s111k2_Y_cont (m : ℝ) (r : ℕ) {P : ℝ} (hP : (d : ℝ) + 2 < 2 * P) {η : (Euc d → ℝ) → ℝ}
    (hη : IsBoundedLinearOnE r P η) (hdual : dualNormE r P η < ⊤) (I : Set ℝ)
    (F : MultiIndex d → ℝ → Euc d → ℝ) (b : MultiIndex d → ℝ) (hb0 : ∀ α, 0 ≤ b α)
    (hbs : Summable fun α => b α ^ 2)
    (hF : ∀ α, ∀ t ∈ I, ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (F α t))
    (hL : ∀ α, ∀ t ∈ I, ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 → ∀ x, ‖iteratedFDeriv ℝ j (F α t) x‖ ≤ b α)
    (hB0 : ∀ α, ∀ t ∈ I, ∃ B0 : ℝ, ∀ x, |F α t x| ≤ B0)
    (hc : ∀ α x, ContinuousOn (fun t => F α t x) I)
    (hzero : ∀ α, ∀ t ∈ I, η (F α t) = η (s111k2_g (F α) t)) :
    ContinuousOn (fun t => (ellVec m (fun α => η (F α t)) : OscDual d m)) I := by
  have hcoord : ∀ α, ContinuousOn (fun t => η (F α t)) I := fun α =>
    (s111k2_func_cont r hP hη hdual I (F α) (hb0 α) (hF α) (hL α) (hB0 α) (hc α)).congr
      fun t ht => hzero α t ht
  set K : ℝ := (dualNormE r P η).toReal * s111k2_CE d r P with hK
  have hK0 : 0 ≤ K := mul_nonneg ENNReal.toReal_nonneg (s111k2_CE_nonneg r P)
  have hbound : ∀ α, ∀ t ∈ I, |η (F α t)| ≤ K * b α := by
    intro α t ht
    rw [hzero α t ht]
    obtain ⟨B0, hB0'⟩ := hB0 α t ht
    have hB00 : 0 ≤ B0 := (abs_nonneg _).trans (hB0' 0)
    have hFr : ContDiff ℝ r (F α t) := (hF α t ht).of_le (by exact_mod_cast Nat.le_succ r)
    obtain ⟨hgC, hgl⟩ := s111k2_g_props r (hF α t ht) (hb0 α) (hL α t ht)
    have := s111k2_dual_lin hP hη hdual hgC (s111k2_g_qual hFr (hb0 α) hB00 hB0'
      (fun j h1 h2 x => hL α t ht j h1 (by omega) x)) (hb0 α) hgl
    calc |η (s111k2_g (F α) t)| ≤ (dualNormE r P η).toReal * (s111k2_CE d r P * b α) := this
      _ = K * b α := by rw [hK]; ring
  have hmemT : ∀ t ∈ I, Memℓp (fun α => η (F α t)) 2 := fun t ht =>
    s111k2_memell_of_le (hbs.mul_left (K ^ 2)) (fun α => by
      have := hbound α t ht
      calc η (F α t) ^ 2 = |η (F α t)| ^ 2 := (sq_abs _).symm
        _ ≤ (K * b α) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = K ^ 2 * b α ^ 2 := by ring)
  rw [continuousOn_iff_continuous_restrict]
  refine continuous_iff_seqContinuous.2 fun tn t₀ htn => ?_
  simp only [Set.restrict_apply, Function.comp_def]
  refine s111k2_ell_tendsto (g := fun α => 4 * K ^ 2 * b α ^ 2) (hbs.mul_left _) (fun n α => ?_)
    (fun α => ?_) (fun n => hmemT _ (tn n).2) (hmemT _ t₀.2)
  · have h1 := hbound α _ (tn n).2
    have h2 := hbound α _ t₀.2
    have h3 : |η (F α (tn n)) - η (F α t₀)| ≤ 2 * (K * b α) := by
      have := abs_sub (η (F α (tn n))) (η (F α t₀)); linarith
    calc (η (F α (tn n)) - η (F α t₀)) ^ 2 = |η (F α (tn n)) - η (F α t₀)| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * (K * b α)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
      _ = 4 * K ^ 2 * b α ^ 2 := by ring
  · exact ((hcoord α).restrict.tendsto t₀).comp htn

end HRS.MS.S111K2
