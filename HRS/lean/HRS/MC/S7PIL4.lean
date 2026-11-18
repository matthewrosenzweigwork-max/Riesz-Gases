import HRS.MC.S7PIL3

/-!
# Packet piL, part 4: pieces and gluing

`S7PIL_piece`: `|g a - g b| ≤ K (b - a)` when no observation time lies in `(a,b)`; `S7PIL_glue`: induction on the number of
observation times inside the interval; `S7PIL_lip_g`: the Lipschitz bound on `[0,T]`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIL

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

theorem S7PIL_piece (R : Regime d) (m T : ℝ) (hT : 0 < T) {q : ℕ} {t : Fin q → ℝ}
    {Λ : EuclideanSpace ℝ (Fin q) →L[ℝ] PathSpace d m T} (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i))
    (hlaw : ∀ u ∈ Set.Icc (0 : ℝ) T, (obsCov R.D R.ρ t φ u).PosSemidef)
    (CB : ℝ) (hCB0 : 0 ≤ CB)
    (hCB : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ N : PathSpace d m T [×2]→L[ℝ] ℝ,
      |∑ i, ∑ j, obsRate R.D R.ρ t φ u i j *
        N ![Λ (EuclideanSpace.single i 1), Λ (EuclideanSpace.single j 1)]| ≤ CB * ‖N‖)
    {Φ : PathSpace d m T → ℝ} (hΦ : MemCb 5 Φ) {j : ℕ} (hj : j ≤ 3) (x0 : PathSpace d m T)
    (w : Fin j → PathSpace d m T) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hno : ∀ i, ¬ (a < t i ∧ t i < b)) :
    |gaussHeat (obsCov R.D R.ρ t φ) (S7PIL_psi (iteratedFDeriv ℝ j Φ) x0 Λ w) a 0 -
        gaussHeat (obsCov R.D R.ρ t φ) (S7PIL_psi (iteratedFDeriv ℝ j Φ) x0 Λ w) b 0| ≤
      1 / 2 * (CB * (cbNorm 5 Φ * ∏ k, ‖w k‖)) * (b - a) := by
  set ψ := S7PIL_psi (iteratedFDeriv ℝ j Φ) x0 Λ w with hψdef
  set K : ℝ := 1 / 2 * (CB * (cbNorm 5 Φ * ∏ k, ‖w k‖)) with hK
  have hψ : MemCb 2 ψ := S7PIL_psi_memCb hΦ hj x0 Λ w
  have cov := HRS.MC.Sec7.S7PIS3.s7_PIS_cov_struct_proof' R T hT t φ ht hφ
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  have hAc := (cov.2.2.1 a b ha hab hb hno).1
  have hAeq := (cov.2.2.1 a b ha hab hb hno).2
  have hApsd : ∀ v ∈ Set.Icc a b, (obsRateR R.D R.ρ t φ a v).PosSemidef := fun v hv =>
    cov.2.1 a v ⟨ha.trans hv.1, hv.2.trans hb⟩ (fun i hi => by
      have := hno i
      push_neg at this
      exact hv.2.trans (this hi))
  have hSb := hlaw b ⟨ha.trans hab, hb⟩
  have hS : ∀ u ∈ Set.Icc a b, ∀ i j, obsCov R.D R.ρ t φ u i j =
      obsCov R.D R.ρ t φ b i j + ∫ v in Set.Ioc u b, obsRateR R.D R.ρ t φ a v i j := by
    intro u hu i jj
    rw [cov.2.2.2.1 u b (ha.trans hu.1) hu.2 hb i jj]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    show obsRate R.D R.ρ t φ x i jj = obsRateR R.D R.ρ t φ a x i jj
    rw [hAeq x ⟨lt_of_le_of_lt hu.1 hx.1, hx.2⟩]
  have hpde := HRS.MC.Sec7.S7PIH.s7_PIH_heat_pde_proof a b hab (obsRateR R.D R.ρ t φ a)
    (obsCov R.D R.ρ t φ) hAc hApsd hSb hS ψ hψ 0
  set g : ℝ → ℝ := fun s => gaussHeat (obsCov R.D R.ρ t φ) ψ s 0 with hg
  set f' : ℝ → ℝ := fun r => -(1 / 2 : ℝ) * ∑ i, ∑ jj, obsRateR R.D R.ρ t φ a r i jj *
        ∫ x, iteratedFDeriv ℝ 2 ψ (0 + x) ![EuclideanSpace.single i 1, EuclideanSpace.single jj 1]
          ∂(multivariateGaussian 0 (obsCov R.D R.ρ t φ r)) with hf'
  have hbound : ∀ r ∈ Set.Ioc a b, ‖f' r‖ ≤ K := by
    intro r hr
    have hr0 : r ∈ Set.Icc (0 : ℝ) T := ⟨ha.trans hr.1.le, hr.2.trans hb⟩
    have := S7PIL_deriv_bound R m T φ CB hCB0 hCB hΦ hj x0 w hr0
    simp only [hf', hAeq r hr, Real.norm_eq_abs]
    exact this
  have hmv : ∀ x ∈ Set.Ioc a b, ‖g b - g x‖ ≤ K * ‖b - x‖ := by
    intro x hx
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g) (f' := f') (s := Set.Ioc a b)
      (fun r hr => (hpde r ⟨hr.1.le, hr.2⟩).mono Set.Ioc_subset_Icc_self) hbound (convex_Ioc a b) hx
      ⟨hlt, le_rfl⟩
  have hcont : ContinuousWithinAt g (Set.Ioi a) a :=
    (hpde a ⟨le_rfl, hab⟩).continuousWithinAt.mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsGT hlt) Set.Ioo_subset_Icc_self)
  have hlim : Tendsto (fun x => ‖g b - g x‖ - K * ‖b - x‖) (𝓝[>] a) (𝓝 (‖g b - g a‖ - K * ‖b - a‖)) := by
    refine Tendsto.sub ?_ ?_
    · exact (tendsto_const_nhds.sub hcont).norm
    · exact tendsto_const_nhds.mul ((tendsto_const_nhds.sub (tendsto_nhdsWithin_of_tendsto_nhds
        tendsto_id)).norm)
  have hev : ∀ᶠ x in 𝓝[>] a, ‖g b - g x‖ - K * ‖b - x‖ ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsGT hlt] with x hx
    exact sub_nonpos.2 (hmv x ⟨hx.1, hx.2.le⟩)
  have h0 := le_of_tendsto hlim hev
  have h1 : ‖g b - g a‖ ≤ K * ‖b - a‖ := sub_nonpos.1 h0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ b - a), abs_sub_comm] at h1
  exact h1

/-- Gluing: induction on the number of observation times strictly inside the interval. -/
theorem S7PIL_glue {q : ℕ} (t : Fin q → ℝ) (T K : ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (g : ℝ → ℝ)
    (hpiece : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → (∀ i, ¬ (a < t i ∧ t i < b)) → |g a - g b| ≤ K * (b - a)) :
    ∀ n : ℕ, ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T →
      (Finset.univ.filter (fun i => a < t i ∧ t i < b)).card = n → |g a - g b| ≤ K * (b - a) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b ha hab hb hcard
    by_cases h : ∃ i, a < t i ∧ t i < b
    · obtain ⟨i0, hi0⟩ := h
      have c1 : (Finset.univ.filter (fun i => a < t i ∧ t i < t i0)).card < n := by
        rw [← hcard]
        refine Finset.card_lt_card ⟨fun i hi => ?_, fun hsub => ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          exact ⟨hi.1, hi.2.trans hi0.2⟩
        · have := hsub (by simp [hi0] : i0 ∈ Finset.univ.filter (fun i => a < t i ∧ t i < b))
          simp at this
      have c2 : (Finset.univ.filter (fun i => t i0 < t i ∧ t i < b)).card < n := by
        rw [← hcard]
        refine Finset.card_lt_card ⟨fun i hi => ?_, fun hsub => ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          exact ⟨hi0.1.trans hi.1, hi.2⟩
        · have := hsub (by simp [hi0] : i0 ∈ Finset.univ.filter (fun i => a < t i ∧ t i < b))
          simp at this
      have e1 := ih _ c1 a (t i0) ha hi0.1.le (hi0.2.le.trans hb) rfl
      have e2 := ih _ c2 (t i0) b (ha.trans hi0.1.le) hi0.2.le hb rfl
      calc |g a - g b| ≤ |g a - g (t i0)| + |g (t i0) - g b| := abs_sub_le _ _ _
        _ ≤ K * (t i0 - a) + K * (b - t i0) := add_le_add e1 e2
        _ = K * (b - a) := by ring
    · push_neg at h
      exact hpiece a b ha hab hb (fun i hi => absurd hi.2 (not_lt.2 (h i hi.1)))

/-- The Lipschitz bound on `[0,T]`. -/
theorem S7PIL_lip_g {q : ℕ} (t : Fin q → ℝ) (T K : ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (g : ℝ → ℝ)
    (hpiece : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → (∀ i, ¬ (a < t i ∧ t i < b)) → |g a - g b| ≤ K * (b - a))
    {u v : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) (hv : v ∈ Set.Icc (0 : ℝ) T) :
    |g u - g v| ≤ K * |u - v| := by
  rcases le_total u v with h | h
  · rw [abs_of_nonpos (by linarith : u - v ≤ 0)]
    have := S7PIL_glue t T K ht g hpiece _ u v hu.1 h hv.2 rfl
    linarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ u - v), abs_sub_comm]
    have := S7PIL_glue t T K ht g hpiece _ v u hv.1 h hu.2 rfl
    linarith

end HRS.MC.Sec7.S7PIL

end
