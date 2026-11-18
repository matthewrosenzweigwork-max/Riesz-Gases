import HRS.MS.WadAux174

/-!
# S8.3, packet S8H2-1: order-zero theory of `tensorU`

For a continuous pair kernel `F` with weighted decay and `|F| ≤ N w` (`w = ⟨x⟩^M⟨y⟩^M`) and `t ∈ [0,T]`: the sections `x' ↦ U_t(F x')(y)` lie in `C_M`
with `|U_t(F x')(y)| ≤ K₀ N ⟨x'⟩^M⟨y⟩^M` and `|tensorU U t F x y| ≤ K₀² N ⟨x⟩^M⟨y⟩^M` (`s8h2_sec0`); `tensorU` is additive (`s8h2_tensor_sub`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff Convolution

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8h2_memCM_sub {M : ℝ} {f g : Euc d → ℝ} (hf : MemCM M f) (hg : MemCM M g) :
    MemCM M (fun x => f x - g x) := by
  refine ⟨hf.1.sub hg.1, ?_⟩
  have := hf.2.sub hg.2
  simp only [sub_zero] at this
  exact this.congr fun x => (sub_div _ _ _).symm

theorem s8h2_slice_memCM {M : ℝ} {F : Euc d × Euc d → ℝ} (hF : Continuous F)
    (hdec : Tendsto (fun z => ‖F z‖ / s8h_w M z) (cocompact (Euc d × Euc d)) (𝓝 0)) (x' : Euc d) :
    MemCM M (fun y => F (x', y)) := by
  refine ⟨hF.comp (continuous_const.prodMk continuous_id), ?_⟩
  have h1 := (hdec.comp (s8h_tendsto_prodMk_right x')).mul_const (jbracket x' ^ M)
  simp only [zero_mul] at h1
  refine squeeze_zero_norm (fun y => ?_) h1
  have hx := Real.rpow_pos_of_pos (s83_jb_pos x') M
  have hy := Real.rpow_pos_of_pos (s83_jb_pos y) M
  have e : ‖F (x', y) / jbracket y ^ M‖ = (‖F (x', y)‖ / s8h_w M (x', y)) * jbracket x' ^ M := by
    unfold s8h_w
    simp only
    rw [norm_div, Real.norm_of_nonneg hy.le]
    field_simp
  exact e.le

section Interface

variable {a β : ℝ} {ρβ : Euc d → ℝ} {M : ℝ} {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}

theorem s8h2_sec0 (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    (hM : 0 ≤ M) {T : ℝ} (hT : 0 ≤ T) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ {F : Euc d → Euc d → ℝ} {N : ℝ}, Continuous (Function.uncurry F) →
      Tendsto (fun z => ‖Function.uncurry F z‖ / s8h_w M z) (cocompact (Euc d × Euc d)) (𝓝 0) →
      (∀ z, ‖Function.uncurry F z‖ ≤ N * s8h_w M z) → ∀ t ∈ Set.Icc 0 T,
      (∀ y, MemCM M (fun x' => U t (F x') y)) ∧
      (∀ x' y, |U t (F x') y| ≤ K0 * N * (jbracket x' ^ M * jbracket y ^ M)) ∧
      ∀ x y, |tensorU U t F x y| ≤ K0 ^ 2 * N * (jbracket x ^ M * jbracket y ^ M) := by
  obtain ⟨K0, hK0, hK⟩ := s8h_U0 hU hT
  refine ⟨K0, hK0, fun {F N} hc hdec hb t ht => ?_⟩
  have hN : 0 ≤ N := by
    have h0 := (norm_nonneg (Function.uncurry F (0, 0))).trans (hb (0, 0))
    by_contra hneg
    push Not at hneg
    have := s8h_w_pos M ((0, 0) : Euc d × Euc d)
    nlinarith
  have hsec : ∀ x', MemCM M (F x') := fun x' => s8h2_slice_memCM hc hdec x'
  have hjp : ∀ x : Euc d, 0 < jbracket x ^ M := fun x => Real.rpow_pos_of_pos (s83_jb_pos x) M
  have hW : ∀ x', Wt M (N * jbracket x' ^ M) (F x') := fun x' y => by
    have := hb (x', y)
    unfold s8h_w at this
    calc ‖F x' y‖ ≤ N * (jbracket x' ^ M * jbracket y ^ M) := this
      _ = N * jbracket x' ^ M * jbracket y ^ M := by ring
  have hUW : ∀ x', Wt M (K0 * (N * jbracket x' ^ M)) (U t (F x')) := fun x' =>
    hK t ht (F x') (hsec x') (mul_nonneg hN (hjp x').le) (hW x')
  have hbd : ∀ x' y, |U t (F x') y| ≤ K0 * N * (jbracket x' ^ M * jbracket y ^ M) := fun x' y => by
    have := hUW x' y
    rw [Real.norm_eq_abs] at this
    calc |U t (F x') y| ≤ K0 * (N * jbracket x' ^ M) * jbracket y ^ M := this
      _ = K0 * N * (jbracket x' ^ M * jbracket y ^ M) := by ring
  have hmem : ∀ y, MemCM M (fun x' => U t (F x') y) := by
    intro y
    have hy := hjp y
    refine ⟨?_, ?_⟩
    · rw [continuous_iff_continuousAt]
      intro x0
      rw [Metric.continuousAt_iff]
      intro ε hε
      have hq : 0 < K0 * jbracket y ^ M + 1 := by positivity
      obtain ⟨δ, hδ, hg⟩ := s8h_gap hM hc hdec x0 (show 0 < ε / (K0 * jbracket y ^ M + 1) by positivity)
      refine ⟨δ, hδ, fun x' hx' => ?_⟩
      rw [dist_eq_norm] at hx'
      have hdiff : Wt M (ε / (K0 * jbracket y ^ M + 1)) (fun y' => F x' y' - F x0 y') := fun y' => by
        rw [Real.norm_eq_abs]
        exact hg x' hx' y'
      have hsub := hK t ht (fun y' => F x' y' - F x0 y') (s8h2_memCM_sub (hsec x') (hsec x0))
        (div_nonneg hε.le hq.le) hdiff y
      rw [s8h_U_sub hU ht.1 (hsec x') (hsec x0)] at hsub
      rw [Real.dist_eq]
      rw [Real.norm_eq_abs] at hsub
      calc |U t (F x') y - U t (F x0) y| ≤ K0 * (ε / (K0 * jbracket y ^ M + 1)) * jbracket y ^ M := hsub
        _ = ε * ((K0 * jbracket y ^ M) / (K0 * jbracket y ^ M + 1)) := by field_simp
        _ < ε := by
          have : (K0 * jbracket y ^ M) / (K0 * jbracket y ^ M + 1) < 1 := by
            rw [div_lt_one hq]; linarith
          nlinarith
    · rw [Metric.tendsto_nhds]
      intro ε hε
      have hq : 0 < K0 * jbracket y ^ M + 1 := by positivity
      obtain ⟨ρ, hρ⟩ := s8h_far hdec (show 0 < ε / (2 * (K0 * jbracket y ^ M + 1)) by positivity)
      have hev : (Metric.closedBall (0 : Euc d) ρ)ᶜ ∈ cocompact (Euc d) :=
        (isCompact_closedBall _ _).compl_mem_cocompact
      filter_upwards [hev] with x' hx'
      have hx'' : ρ < ‖x'‖ := by
        simpa [mem_closedBall_zero_iff] using hx'
      have hWW : Wt M (ε / (2 * (K0 * jbracket y ^ M + 1)) * jbracket x' ^ M) (F x') := fun y' => by
        have := hρ x' y' (Or.inl hx'')
        unfold s8h_w at this
        rw [Real.norm_eq_abs]
        calc |F x' y'| ≤ ε / (2 * (K0 * jbracket y ^ M + 1)) * (jbracket x' ^ M * jbracket y' ^ M) := this
          _ = ε / (2 * (K0 * jbracket y ^ M + 1)) * jbracket x' ^ M * jbracket y' ^ M := by ring
      have h2 := hK t ht (F x') (hsec x') (mul_nonneg (by positivity) (hjp x').le) hWW y
      rw [Real.norm_eq_abs] at h2
      have hx0 := hjp x'
      rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hx0, div_lt_iff₀ hx0]
      calc |U t (F x') y| ≤ K0 * (ε / (2 * (K0 * jbracket y ^ M + 1)) * jbracket x' ^ M) * jbracket y ^ M := h2
        _ = ε * ((K0 * jbracket y ^ M) / (2 * (K0 * jbracket y ^ M + 1))) * jbracket x' ^ M := by
          field_simp
        _ < ε * jbracket x' ^ M := by
          have h1 : (K0 * jbracket y ^ M) / (2 * (K0 * jbracket y ^ M + 1)) < 1 := by
            rw [div_lt_one (by positivity)]; nlinarith
          have : ε * ((K0 * jbracket y ^ M) / (2 * (K0 * jbracket y ^ M + 1))) < ε * 1 :=
            mul_lt_mul_of_pos_left h1 hε
          nlinarith
  refine ⟨hmem, hbd, fun x y => ?_⟩
  have hy := hjp y
  have hWy : Wt M (K0 * N * jbracket y ^ M) (fun x' => U t (F x') y) := fun x' => by
    rw [Real.norm_eq_abs]
    calc |U t (F x') y| ≤ K0 * N * (jbracket x' ^ M * jbracket y ^ M) := hbd x' y
      _ = K0 * N * jbracket y ^ M * jbracket x' ^ M := by ring
  have h3 := hK t ht (fun x' => U t (F x') y) (hmem y) (by positivity) hWy x
  rw [Real.norm_eq_abs] at h3
  unfold tensorU
  calc |U t (fun x' => U t (F x') y) x| ≤ K0 * (K0 * N * jbracket y ^ M) * jbracket x ^ M := h3
    _ = K0 ^ 2 * N * (jbracket x ^ M * jbracket y ^ M) := by ring

theorem s8h2_tensor_sub (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    {t : ℝ} (ht : 0 ≤ t) {F G : Euc d → Euc d → ℝ} (hF : ∀ x', MemCM M (F x'))
    (hG : ∀ x', MemCM M (G x')) (hF2 : ∀ y, MemCM M (fun x' => U t (F x') y))
    (hG2 : ∀ y, MemCM M (fun x' => U t (G x') y)) (x y : Euc d) :
    tensorU U t (fun x' y' => F x' y' - G x' y') x y = tensorU U t F x y - tensorU U t G x y := by
  unfold tensorU
  have h1 : (fun x' => U t (fun y' => F x' y' - G x' y') y) =
      fun x' => U t (F x') y - U t (G x') y := by
    funext x'
    rw [s8h_U_sub hU ht (hF x') (hG x')]
  rw [h1, s8h_U_sub hU ht (hF2 y) (hG2 y)]

end Interface

end HRS.MS.Wad
