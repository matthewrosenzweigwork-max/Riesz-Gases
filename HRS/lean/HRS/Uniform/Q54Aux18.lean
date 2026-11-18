import HRS.Uniform.Q54Aux17

/-!
# Q54, part 18: strong continuity of `(t, u) ↦ V^{t,u} x` on the triangle
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54

open HRS HRS.PDE HRS.Uniform.Q48b

variable {d : ℕ}

theorem norm_le_of_sq {E : Type*} [NormedAddCommGroup E] {x : E} {κ τ N : ℝ} (hκ : 0 ≤ κ) (hτ : 0 ≤ τ)
    (hN : 0 ≤ N) (h : ‖x‖ ^ 2 ≤ κ * τ * N) :
    ‖x‖ ≤ Real.sqrt κ * Real.sqrt τ * Real.sqrt N := by
  rw [← Real.sqrt_mul hκ, ← Real.sqrt_mul (mul_nonneg hκ hτ)]
  exact Real.abs_le_sqrt h |>.trans' (le_abs_self _)

section Cont

variable {J : ℕ} {Up : ℝ → ℝ → (Torus d → ℝ) → Torus d → ℝ} {r : ℝ}
  {Vev : ℝ → ℝ → NegSobolev d r →L[ℝ] NegSobolev d r} {C C₂ A B : ℝ}

/-- the triangle -/
def Tri (T : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}

theorem holder_t_fin (h : ContData J Up r Vev C C₂ A B) (T : ℝ) (S : Finset (NonzeroLattice d))
    (ζ : NonzeroLattice d → ℝ) {u t t' : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (htt' : t ≤ t') (ht'T : t' ≤ T) :
    ‖(Vev t' u - Vev t u) (q48bFin r S ζ)‖ ≤
      Real.sqrt (Real.exp (|C₂| * T) ^ 2 * B * Real.exp (|A| * T)) * Real.sqrt (t' - t) *
        Real.sqrt (∑ k ∈ S, q48bW k ^ (-2 * (r - 2)) * ζ k ^ 2) := by
  have hκ : 0 ≤ Real.exp (|C₂| * T) ^ 2 * B * Real.exp (|A| * T) := by
    have := h.hB; positivity
  have hτ : 0 ≤ t' - t := by linarith
  have hN : 0 ≤ ∑ k ∈ S, q48bW k ^ (-2 * (r - 2)) * ζ k ^ 2 :=
    Finset.sum_nonneg fun l _ => mul_nonneg (Real.rpow_nonneg (q48bW_pos l).le _) (sq_nonneg _)
  refine norm_le_of_sq hκ hτ hN ?_
  have := fin_bound_of_fn h hu (hut.trans htt') hu hut
    (Real.exp (|C₂| * T) ^ 2 * B * Real.exp (|A| * T) * (t' - t)) (mul_nonneg hκ hτ)
    (fun φ hφ => by
      obtain ⟨h1, h2⟩ := fn_hold_t h T hu hut htt' ht'T hφ
      exact ⟨h1, h2⟩) S ζ
  exact this

theorem holder_u_fin (h : ContData J Up r Vev C C₂ A B) (T : ℝ) (S : Finset (NonzeroLattice d))
    (ζ : NonzeroLattice d → ℝ) {u u' t : ℝ} (hu : 0 ≤ u) (huu' : u ≤ u') (hu't : u' ≤ t) (htT : t ≤ T) :
    ‖(Vev t u - Vev t u') (q48bFin r S ζ)‖ ≤
      Real.sqrt (Real.exp (|C| * T) ^ 2 * B * Real.exp (|A| * T)) * Real.sqrt (u' - u) *
        Real.sqrt (∑ k ∈ S, q48bW k ^ (-2 * (r - 2)) * ζ k ^ 2) := by
  have hκ : 0 ≤ Real.exp (|C| * T) ^ 2 * B * Real.exp (|A| * T) := by
    have := h.hB; positivity
  have hτ : 0 ≤ u' - u := by linarith
  have hN : 0 ≤ ∑ k ∈ S, q48bW k ^ (-2 * (r - 2)) * ζ k ^ 2 :=
    Finset.sum_nonneg fun l _ => mul_nonneg (Real.rpow_nonneg (q48bW_pos l).le _) (sq_nonneg _)
  refine norm_le_of_sq hκ hτ hN ?_
  have := fin_bound_of_fn h hu (huu'.trans hu't) (hu.trans huu') hu't
    (Real.exp (|C| * T) ^ 2 * B * Real.exp (|A| * T) * (u' - u)) (mul_nonneg hκ hτ)
    (fun φ hφ => by
      obtain ⟨h1, h2⟩ := fn_hold_u h T hu huu' hu't htT hφ
      exact ⟨h1, h2⟩) S ζ
  exact this

theorem holder_fin (h : ContData J Up r Vev C C₂ A B) (T : ℝ) (S : Finset (NonzeroLattice d))
    (ζ : NonzeroLattice d → ℝ) :
    ∃ c : ℝ, ∀ p ∈ Tri T, ∀ q ∈ Tri T,
      ‖Vev p.1 p.2 (q48bFin r S ζ) - Vev q.1 q.2 (q48bFin r S ζ)‖ ≤
        c * (Real.sqrt |p.1 - q.1| + Real.sqrt |p.2 - q.2|) := by
  set N : ℝ := Real.sqrt (∑ k ∈ S, q48bW k ^ (-2 * (r - 2)) * ζ k ^ 2) with hN
  set x := q48bFin r S ζ with hx
  set κ₁ : ℝ := Real.sqrt (Real.exp (|C₂| * T) ^ 2 * B * Real.exp (|A| * T)) with hκ₁
  set κ₂ : ℝ := Real.sqrt (Real.exp (|C| * T) ^ 2 * B * Real.exp (|A| * T)) with hκ₂
  have hκ₁0 : 0 ≤ κ₁ := Real.sqrt_nonneg _
  have hκ₂0 : 0 ≤ κ₂ := Real.sqrt_nonneg _
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  refine ⟨(κ₁ + κ₂) * N, fun p hp q hq => ?_⟩
  obtain ⟨hp0, hp1, hp2⟩ := hp
  obtain ⟨hq0, hq1, hq2⟩ := hq
  -- direction lemmas
  have tdir : ∀ u t t' : ℝ, 0 ≤ u → u ≤ t → u ≤ t' → t ≤ T → t' ≤ T →
      ‖Vev t u x - Vev t' u x‖ ≤ κ₁ * N * Real.sqrt |t - t'| := by
    intro u t t' hu hut hut' htT ht'T
    rcases le_total t t' with htt | htt
    · have := holder_t_fin h T S ζ hu hut htt ht'T
      rw [norm_sub_rev, ← ContinuousLinearMap.sub_apply, abs_of_nonpos (by linarith)]
      rw [neg_sub]
      calc _ ≤ κ₁ * Real.sqrt (t' - t) * N := this
        _ = _ := by ring
    · have := holder_t_fin h T S ζ hu hut' htt htT
      rw [← ContinuousLinearMap.sub_apply, abs_of_nonneg (by linarith)]
      calc _ ≤ κ₁ * Real.sqrt (t - t') * N := this
        _ = _ := by ring
  have udir : ∀ u u' t : ℝ, 0 ≤ u → 0 ≤ u' → u ≤ t → u' ≤ t → t ≤ T →
      ‖Vev t u x - Vev t u' x‖ ≤ κ₂ * N * Real.sqrt |u - u'| := by
    intro u u' t hu hu' hut hu't htT
    rcases le_total u u' with huu | huu
    · have := holder_u_fin h T S ζ hu huu hu't htT
      rw [← ContinuousLinearMap.sub_apply, abs_of_nonpos (by linarith), neg_sub]
      calc _ ≤ κ₂ * Real.sqrt (u' - u) * N := this
        _ = _ := by ring
    · have := holder_u_fin h T S ζ hu' huu hut htT
      rw [norm_sub_rev, ← ContinuousLinearMap.sub_apply, abs_of_nonneg (by linarith)]
      calc _ ≤ κ₂ * Real.sqrt (u - u') * N := this
        _ = _ := by ring
  have hA0 : 0 ≤ Real.sqrt |p.1 - q.1| := Real.sqrt_nonneg _
  have hB0 : 0 ≤ Real.sqrt |p.2 - q.2| := Real.sqrt_nonneg _
  by_cases hcase : q.2 ≤ p.1
  · have e1 := udir p.2 q.2 p.1 hp0 hq0 hp1 hcase hp2
    have e2 := tdir q.2 p.1 q.1 hq0 hcase hq1 hp2 hq2
    calc ‖Vev p.1 p.2 x - Vev q.1 q.2 x‖
        = ‖(Vev p.1 p.2 x - Vev p.1 q.2 x) + (Vev p.1 q.2 x - Vev q.1 q.2 x)‖ := by
          congr 1; abel
      _ ≤ ‖Vev p.1 p.2 x - Vev p.1 q.2 x‖ + ‖Vev p.1 q.2 x - Vev q.1 q.2 x‖ := norm_add_le _ _
      _ ≤ κ₂ * N * Real.sqrt |p.2 - q.2| + κ₁ * N * Real.sqrt |p.1 - q.1| := add_le_add e1 e2
      _ ≤ _ := by
          have h1 : 0 ≤ κ₁ * N * Real.sqrt |p.1 - q.1| := by positivity
          have h2 : 0 ≤ κ₂ * N * Real.sqrt |p.2 - q.2| := by positivity
          nlinarith [mul_nonneg hκ₁0 hN0, mul_nonneg hκ₂0 hN0,
            mul_nonneg (mul_nonneg hκ₂0 hN0) hA0, mul_nonneg (mul_nonneg hκ₁0 hN0) hB0]
  · push Not at hcase
    have hq2' : p.2 ≤ q.1 := by linarith
    have e1 := tdir p.2 p.1 q.1 hp0 hp1 hq2' hp2 hq2
    have e2 := udir p.2 q.2 q.1 hp0 hq0 hq2' hq1 hq2
    calc ‖Vev p.1 p.2 x - Vev q.1 q.2 x‖
        = ‖(Vev p.1 p.2 x - Vev q.1 p.2 x) + (Vev q.1 p.2 x - Vev q.1 q.2 x)‖ := by
          congr 1; abel
      _ ≤ ‖Vev p.1 p.2 x - Vev q.1 p.2 x‖ + ‖Vev q.1 p.2 x - Vev q.1 q.2 x‖ := norm_add_le _ _
      _ ≤ κ₁ * N * Real.sqrt |p.1 - q.1| + κ₂ * N * Real.sqrt |p.2 - q.2| := add_le_add e1 e2
      _ ≤ _ := by
          nlinarith [mul_nonneg hκ₁0 hN0, mul_nonneg hκ₂0 hN0,
            mul_nonneg (mul_nonneg hκ₂0 hN0) hA0, mul_nonneg (mul_nonneg hκ₁0 hN0) hB0]

/-- Strong continuity of `(t, u) ↦ V^{t,u} x` on the triangle. -/
theorem strong_cont (h : ContData J Up r Vev C C₂ A B) (T : ℝ) (x : NegSobolev d r) :
    ContinuousOn (fun p : ℝ × ℝ => Vev p.1 p.2 x) (Tri T) := by
  set ζ : NonzeroLattice d → ℝ := fun k => NegSobolev.fourierCoeff x k with hζ
  have hfin : ∀ S : Finset (NonzeroLattice d),
      ContinuousOn (fun p : ℝ × ℝ => Vev p.1 p.2 (q48bFin r S ζ)) (Tri T) := by
    intro S
    obtain ⟨c, hc⟩ := holder_fin h T S ζ
    exact continuousOn_of_holder _ _ c hc
  have hts := tendsto_trunc x
  have hbd : ∀ p ∈ Tri T, ‖Vev p.1 p.2‖ ≤ Real.exp (|C| * T) := by
    intro p hp
    obtain ⟨hp0, hp1, hp2⟩ := hp
    exact (h.bound p.2 p.1 hp0 hp1).trans (exp_mul_le C (by linarith) (by linarith))
  have hunif : TendstoUniformlyOn (fun (S : Finset (NonzeroLattice d)) (p : ℝ × ℝ) =>
      Vev p.1 p.2 (q48bFin r S ζ)) (fun p => Vev p.1 p.2 x) atTop (Tri T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set Bd : ℝ := Real.exp (|C| * T) with hBd
    have hBd0 : 0 < Bd := Real.exp_pos _
    have hlim := (tendsto_iff_norm_sub_tendsto_zero.1 hts)
    have hev : ∀ᶠ S : Finset (NonzeroLattice d) in atTop,
        ‖q48bFin r S ζ - x‖ < ε / (Bd + 1) := by
      have := (Metric.tendsto_nhds.1 hlim) (ε / (Bd + 1)) (by positivity)
      filter_upwards [this] with S hS
      simpa using hS
    filter_upwards [hev] with S hS p hp
    rw [dist_eq_norm, ← map_sub]
    calc ‖Vev p.1 p.2 (x - q48bFin r S ζ)‖
        ≤ ‖Vev p.1 p.2‖ * ‖x - q48bFin r S ζ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ Bd * ‖q48bFin r S ζ - x‖ := by
          rw [norm_sub_rev]
          exact mul_le_mul_of_nonneg_right (hbd p hp) (norm_nonneg _)
      _ < Bd * (ε / (Bd + 1)) := mul_lt_mul_of_pos_left hS hBd0
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  exact hunif.continuousOn (Eventually.of_forall hfin).frequently

end Cont

end HRS.Uniform.Q54
