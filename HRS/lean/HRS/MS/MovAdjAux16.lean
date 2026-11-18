import HRS.MS.MovAdjAux15

/-!
# S6.7 (packet P4, part 2): the truncated functions for the Duhamel formula

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

`S67DuhData q B T u a S`: `u` is a classical solution on `[0,T]` of `∂_σ u = kolmL u + S`, `∂_σ u = a`, with `a` of linear growth and `S` bounded
(all jointly continuous).  For the cut-off index `n` we put (time clamped to `[0,T]`)
`v = χ_n u`, `a_n = χ_n a`, `F_n = χ_n S - (u kolmL χ_n + 2⟨∇χ_n, ∇u⟩)`; these are bounded, jointly continuous, and satisfy the
hypotheses of `hs_duhamel`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MS.PoisKolm HRS.MS.PoisHigh HRS.MS.Mov63 HRS.MS.FlowB

variable {d : ℕ}

structure S67DuhData (q : ℝ) (B : Euc d → Euc d) (T : ℝ) (u a S : ℝ → Euc d → ℝ) : Prop where
  c2 : ∀ σ ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (u σ)
  bd : ∃ K0 K1 K2 : ℝ, ∀ σ ∈ Icc (0 : ℝ) T, ∀ y, |u σ y| ≤ K0 ∧ ‖fderiv ℝ (u σ) y‖ ≤ K1 ∧
    ‖iteratedFDeriv ℝ 2 (u σ) y‖ ≤ K2
  ucont : ContinuousOn (fun p : ℝ × Euc d => u p.1 p.2) (Icc (0 : ℝ) T ×ˢ univ)
  gcont : ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (u p.1) p.2) (Icc (0 : ℝ) T ×ˢ univ)
  acont : ContinuousOn (fun p : ℝ × Euc d => a p.1 p.2) (Icc (0 : ℝ) T ×ˢ univ)
  agrow : ∃ Ka : ℝ, ∀ σ ∈ Icc (0 : ℝ) T, ∀ y, |a σ y| ≤ Ka * (1 + ‖y‖)
  Scont : ContinuousOn (fun p : ℝ × Euc d => S p.1 p.2) (Icc (0 : ℝ) T ×ˢ univ)
  Sbd : ∃ KS : ℝ, ∀ σ ∈ Icc (0 : ℝ) T, ∀ y, |S σ y| ≤ KS
  hint : ∀ σ ∈ Icc (0 : ℝ) T, ∀ s0 ∈ Icc (0 : ℝ) T, ∀ y, u σ y - u s0 y = ∫ r in s0..σ, a r y
  hL : ∀ σ ∈ Icc (0 : ℝ) T, ∀ y, a σ y - kolmL q B (u σ) y = S σ y

/-- The truncated solution. -/
def s67v (T : ℝ) (u : ℝ → Euc d → ℝ) (n : ℕ) (σ : ℝ) (y : Euc d) : ℝ := hsCut n y * u (clampT T σ) y

/-- The truncated time derivative. -/
def s67a' (T : ℝ) (a : ℝ → Euc d → ℝ) (n : ℕ) (σ : ℝ) (y : Euc d) : ℝ := hsCut n y * a (clampT T σ) y

/-- The truncated source. -/
def s67F (q : ℝ) (B : Euc d → Euc d) (T : ℝ) (u S : ℝ → Euc d → ℝ) (n : ℕ) (σ : ℝ) (y : Euc d) : ℝ :=
  hsCut n y * S (clampT T σ) y -
    (u (clampT T σ) y * kolmL q B (hsCut n) y + 2 * fderiv ℝ (u (clampT T σ)) y (gradient (hsCut n) y))

/-- composition with the clamp -/
theorem s67_comp_clamp {T : ℝ} (hT : 0 ≤ T) {g : ℝ → Euc d → ℝ}
    (hg : ContinuousOn (fun p : ℝ × Euc d => g p.1 p.2) (Icc (0 : ℝ) T ×ˢ univ)) :
    Continuous fun p : ℝ × Euc d => g (clampT T p.1) p.2 := by
  have h1 : Continuous fun p : ℝ × Euc d => ((clampT T p.1, p.2) : ℝ × Euc d) :=
    ((continuous_clampT T).comp continuous_fst).prodMk continuous_snd
  exact hg.comp_continuous h1 (fun p => ⟨clampT_mem hT _, mem_univ _⟩)

theorem s67_comp_clamp_g {T : ℝ} (hT : 0 ≤ T) {u : ℝ → Euc d → ℝ}
    (hg : ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (u p.1) p.2) (Icc (0 : ℝ) T ×ˢ univ)) :
    Continuous fun p : ℝ × Euc d => fderiv ℝ (u (clampT T p.1)) p.2 := by
  have h1 : Continuous fun p : ℝ × Euc d => ((clampT T p.1, p.2) : ℝ × Euc d) :=
    ((continuous_clampT T).comp continuous_fst).prodMk continuous_snd
  exact hg.comp_continuous h1 (fun p => ⟨clampT_mem hT _, mem_univ _⟩)

variable {q : ℝ} {B : Euc d → Euc d} {T : ℝ} {u a S : ℝ → Euc d → ℝ}

theorem S67DuhData.v_cont (h : S67DuhData q B T u a S) (hT : 0 ≤ T) (n : ℕ) :
    Continuous fun p : ℝ × Euc d => s67v T u n p.1 p.2 := by
  unfold s67v
  exact ((hs_cut_contDiff (d := d) n).continuous.comp continuous_snd).mul (s67_comp_clamp hT h.ucont)

theorem S67DuhData.a_cont (h : S67DuhData q B T u a S) (hT : 0 ≤ T) (n : ℕ) :
    Continuous fun p : ℝ × Euc d => s67a' T a n p.1 p.2 := by
  unfold s67a'
  exact ((hs_cut_contDiff (d := d) n).continuous.comp continuous_snd).mul (s67_comp_clamp hT h.acont)

theorem S67DuhData.F_cont (h : S67DuhData q B T u a S) (hT : 0 ≤ T) (hB : Continuous B) (n : ℕ) :
    Continuous fun p : ℝ × Euc d => s67F q B T u S n p.1 p.2 := by
  unfold s67F
  have hχ := hs_cut_contDiff (d := d) n
  have hχ2 : ContDiff ℝ 2 (hsCut (d := d) n) := hχ.of_le (by simp)
  have hcχ : Continuous fun y : Euc d => hsCut (d := d) n y := hχ.continuous
  have hkχ : Continuous fun y : Euc d => kolmL q B (hsCut n) y := by
    unfold kolmL
    refine (s67_lap_cont hχ2).add ?_
    have hgr : Continuous fun y : Euc d => gradient (hsCut (d := d) n) y := s67_grad_cont (hχ.of_le (by simp))
    exact (((continuous_id.const_smul (-q)).add hB).inner hgr)
  have hgr : Continuous fun y : Euc d => gradient (hsCut (d := d) n) y := s67_grad_cont (hχ.of_le (by simp))
  have hS := s67_comp_clamp hT h.Scont
  have hu := s67_comp_clamp hT h.ucont
  have hg := s67_comp_clamp_g hT h.gcont
  refine ((hcχ.comp continuous_snd).mul hS).sub ?_
  refine (hu.mul (hkχ.comp continuous_snd)).add (continuous_const.mul ?_)
  exact (hg.clm_apply (hgr.comp continuous_snd))

/-! ### Bounds, regularity, the integrated equation -/

theorem s67_cut_zero_val (n : ℕ) {y : Euc d} (hy : 2 * ((n : ℝ) + 1) < ‖y‖) : hsCut n y = 0 :=
  (s67_cut_zero_far n hy).self_of_nhds

theorem S67DuhData.v_bound (h : S67DuhData q B T u a S) (hT : 0 ≤ T) :
    ∃ K0 : ℝ, ∀ (n : ℕ) (σ : ℝ) (y : Euc d), |s67v T u n σ y| ≤ K0 := by
  obtain ⟨K0, K1, K2, hK⟩ := h.bd
  refine ⟨K0, fun n σ y => ?_⟩
  unfold s67v
  have h0 := (hK _ (clampT_mem hT σ) y).1
  have hb := hs_cut_bounds (d := d) n y
  rw [abs_mul, abs_of_nonneg hb.1]
  calc hsCut n y * |u (clampT T σ) y| ≤ 1 * K0 :=
        mul_le_mul hb.2 h0 (abs_nonneg _) zero_le_one
    _ = K0 := one_mul _

theorem S67DuhData.a_bound (h : S67DuhData q B T u a S) (hT : 0 ≤ T) (n : ℕ) :
    ∃ Ka' : ℝ, ∀ (σ : ℝ) (y : Euc d), |s67a' T a n σ y| ≤ Ka' := by
  obtain ⟨Ka, hKa⟩ := h.agrow
  refine ⟨|Ka| * (1 + 2 * ((n : ℝ) + 1)), fun σ y => ?_⟩
  unfold s67a'
  have hb := hs_cut_bounds (d := d) n y
  by_cases hy : ‖y‖ ≤ 2 * ((n : ℝ) + 1)
  · rw [abs_mul, abs_of_nonneg hb.1]
    have h1 := hKa _ (clampT_mem hT σ) y
    calc hsCut n y * |a (clampT T σ) y| ≤ 1 * (Ka * (1 + ‖y‖)) :=
          mul_le_mul hb.2 h1 (abs_nonneg _) zero_le_one
      _ ≤ |Ka| * (1 + 2 * ((n : ℝ) + 1)) := by
          rw [one_mul]
          calc Ka * (1 + ‖y‖) ≤ |Ka| * (1 + ‖y‖) :=
                mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
            _ ≤ |Ka| * (1 + 2 * ((n : ℝ) + 1)) :=
                mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  · push Not at hy
    rw [s67_cut_zero_val n hy]
    simp only [zero_mul, abs_zero]
    positivity

theorem S67DuhData.F_bound (h : S67DuhData q B T u a S) (hT : 0 ≤ T) {Mb : ℝ} (hB : ∀ y, ‖B y‖ ≤ Mb) :
    ∃ KF : ℝ, ∀ (n : ℕ) (σ : ℝ) (y : Euc d), |s67F q B T u S n σ y| ≤ KF := by
  obtain ⟨K0, K1, K2, hK⟩ := h.bd
  obtain ⟨KS, hKS⟩ := h.Sbd
  obtain ⟨Kχ, hKχ⟩ := s67_cut_kolmL_bound (q := q) hB (d := d)
  obtain ⟨c₁, hc₁0, hc₁⟩ := s67_cut_grad_bound (d := d)
  refine ⟨|KS| + (K0 * |Kχ| + 2 * K1 * c₁) + 0, fun n σ y => ?_⟩
  unfold s67F
  have hb := hs_cut_bounds (d := d) n y
  have hn1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  have hσ := clampT_mem hT σ
  have h1 : |hsCut n y * S (clampT T σ) y| ≤ |KS| := by
    rw [abs_mul, abs_of_nonneg hb.1]
    calc hsCut n y * |S (clampT T σ) y| ≤ 1 * |KS| :=
          mul_le_mul hb.2 ((hKS _ hσ y).trans (le_abs_self _)) (abs_nonneg _) zero_le_one
      _ = |KS| := one_mul _
  have hK0 : 0 ≤ K0 := (abs_nonneg _).trans (hK _ hσ y).1
  have hK1 : 0 ≤ K1 := (norm_nonneg _).trans (hK _ hσ y).2.1
  have h2 : |u (clampT T σ) y * kolmL q B (hsCut n) y| ≤ K0 * |Kχ| := by
    rw [abs_mul]
    exact mul_le_mul (hK _ hσ y).1 ((hKχ n y).trans (le_abs_self _)) (abs_nonneg _) hK0
  have h3 : |2 * fderiv ℝ (u (clampT T σ)) y (gradient (hsCut n) y)| ≤ 2 * K1 * c₁ := by
    rw [abs_mul, abs_two]
    have hh := (fderiv ℝ (u (clampT T σ)) y).le_opNorm (gradient (hsCut n) y)
    rw [Real.norm_eq_abs] at hh
    have hh2 : |fderiv ℝ (u (clampT T σ)) y (gradient (hsCut n) y)| ≤ K1 * c₁ := by
      refine hh.trans ?_
      calc ‖fderiv ℝ (u (clampT T σ)) y‖ * ‖gradient (hsCut n) y‖ ≤ K1 * (c₁ * ((n : ℝ) + 1)⁻¹) :=
            mul_le_mul (hK _ hσ y).2.1 (hc₁ n y) (norm_nonneg _) hK1
        _ ≤ K1 * c₁ := mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hc₁0 hn1) hK1
    nlinarith
  calc |hsCut n y * S (clampT T σ) y -
        (u (clampT T σ) y * kolmL q B (hsCut n) y + 2 * fderiv ℝ (u (clampT T σ)) y (gradient (hsCut n) y))|
      ≤ |hsCut n y * S (clampT T σ) y| +
        |u (clampT T σ) y * kolmL q B (hsCut n) y + 2 * fderiv ℝ (u (clampT T σ)) y (gradient (hsCut n) y)| :=
        abs_sub _ _
    _ ≤ |KS| + (K0 * |Kχ| + 2 * K1 * c₁) :=
        add_le_add h1 ((abs_add_le _ _).trans (add_le_add h2 h3))
    _ = _ := by ring

/-- Pointwise: the truncated source converges to `S`. -/
theorem s67F_eventually {q : ℝ} {B : Euc d → Euc d} {T : ℝ} {u S : ℝ → Euc d → ℝ} (σ : ℝ) (y : Euc d)
    {n : ℕ} (hn : ‖y‖ < (n : ℝ) + 1) : s67F q B T u S n σ y = S (clampT T σ) y := by
  unfold s67F
  have h := s67_cut_one_near (d := d) n hn
  have hv : hsCut n y = 1 := h.self_of_nhds
  have hg : gradient (hsCut n) y = 0 := by
    unfold gradient
    rw [h.fderiv_eq (𝕜 := ℝ)]
    simp
  rw [hv, hg, s67_cut_kolmL_zero_near n hn]
  simp

theorem S67DuhData.v_eventually {q : ℝ} (σ : ℝ) (y : Euc d) (u : ℝ → Euc d → ℝ) (T : ℝ)
    {n : ℕ} (hn : ‖y‖ < (n : ℝ) + 1) : s67v T u n σ y = u (clampT T σ) y := by
  unfold s67v
  rw [(s67_cut_one_near (d := d) n hn).self_of_nhds, one_mul]

end HRS.MS.MovAdj
