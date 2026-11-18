import HRS.MS.ToriCoefBAux3

/-!
# MS-TORI-COEFB, helper file 4: the cube `L¹` bound for the derivatives of `μ_L`

For `μ = perL L f` with `f` vanishing outside `B(0, L/3)` and `‖D^j f(w)‖ ≤ B ⟨w⟩^{-(d+3)}` for all `w`,
`∫_{Q_L} ‖D^j μ(x - z)‖ dz ≤ 2^d B ∫⟨w⟩^{-(d+3)}` uniformly in `x`: the box `x - Q_L` meets at most `2^d`
lattice cells (indexed by `⌊x_i/L⌋, ⌊x_i/L⌋ + 1`), on each of which `μ` is a single translate of `f`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ToriCoefB

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.ToriCoefA

variable {d : ℕ}

theorem tcb_mem_U {L : ℝ} (hL : 0 < L) (y : Euc d) :
    y ∈ tca_U L (fun i => ⌊y i / L + 1 / 2⌋) := by
  intro i
  have h1 := Int.floor_le (y i / L + 1 / 2)
  have h2 := Int.lt_floor_add_one (y i / L + 1 / 2)
  have hx : y i = L * (y i / L) := by field_simp
  show |y i - L * ((⌊y i / L + 1 / 2⌋ : ℤ) : ℝ)| < 2 * L / 3
  rw [abs_lt]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h1 hL.le]
  · nlinarith [mul_lt_mul_of_pos_left h2 hL]

theorem tcb_g_pos (y : Euc d) : 0 < tca_g y :=
  Real.rpow_pos_of_pos (tca_jbracket_pos y) _

theorem tcb_cube_l1 {L : ℝ} (hL : 0 < L) (f : Euc d → ℝ)
    (hv : ∀ y : Euc d, L / 3 ≤ ‖y‖ → f y = 0) (j : ℕ) (B : ℝ)
    (hB : ∀ w : Euc d, ‖iteratedFDeriv ℝ j f w‖ ≤ B * tca_g w) (x : Euc d) :
    ∫ z in tcb_Q d L, ‖iteratedFDeriv ℝ j (perL L f) (x - z)‖ ≤ 2 ^ d * B * ∫ w : Euc d, tca_g w := by
  classical
  have hB0 : 0 ≤ B := by
    have h := (norm_nonneg _).trans (hB 0)
    exact nonneg_of_mul_nonneg_left h (tcb_g_pos 0)
  set K : Finset (Fin d → ℤ) :=
    Fintype.piFinset (fun i => ({⌊x i / L⌋, ⌊x i / L⌋ + 1} : Finset ℤ)) with hK
  have hKcard : K.card = 2 ^ d := by
    rw [hK, Fintype.card_piFinset]
    have : ∀ i : Fin d, (({⌊x i / L⌋, ⌊x i / L⌋ + 1} : Finset ℤ)).card = 2 := fun i =>
      Finset.card_pair (by omega)
    simp [this]
  have hpt : ∀ z ∈ tcb_Q d L, ‖iteratedFDeriv ℝ j (perL L f) (x - z)‖ ≤
      ∑ k ∈ K, B * tca_g (x - z - L • latticePt k) := by
    intro z hz
    set y : Euc d := x - z with hy
    set k₀ : Fin d → ℤ := fun i => ⌊y i / L + 1 / 2⌋ with hk₀def
    have hk₀ : k₀ ∈ K := by
      rw [hK, Fintype.mem_piFinset]
      intro i
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have hzi := hz i
      have hyi : y i = x i - z i := by simp [hy]
      have e1 : x i / L < y i / L + 1 / 2 := by
        rw [hyi, sub_div]
        have hz2 : z i / L < 1 / 2 := by
          rw [div_lt_iff₀ hL]
          have := hzi.2
          linarith
        linarith
      have e2 : y i / L + 1 / 2 ≤ x i / L + 1 := by
        rw [hyi, sub_div]
        have : -(z i / L) ≤ 1 / 2 := by
          rw [neg_le, ← neg_div, le_div_iff₀ hL]
          have := hzi.1
          linarith
        linarith
      have f1 : ⌊x i / L⌋ ≤ ⌊y i / L + 1 / 2⌋ := Int.floor_mono e1.le
      have f2 : ⌊y i / L + 1 / 2⌋ ≤ ⌊x i / L + 1⌋ := Int.floor_mono e2
      rw [Int.floor_add_one] at f2
      show ⌊y i / L + 1 / 2⌋ = ⌊x i / L⌋ ∨ ⌊y i / L + 1 / 2⌋ = ⌊x i / L⌋ + 1
      omega
    rw [tca_perL_iter_norm L hL f hv k₀ y (tcb_mem_U hL y) j]
    refine (hB _).trans ?_
    exact Finset.single_le_sum (f := fun k => B * tca_g (x - z - L • latticePt k))
      (fun k _ => mul_nonneg hB0 (tcb_g_pos _).le) hk₀
  have hint1 : ∀ k : Fin d → ℤ, Integrable (fun z : Euc d => B * tca_g (x - z - L • latticePt k))
      volume := by
    intro k
    have e : (fun z : Euc d => B * tca_g (x - z - L • latticePt k)) =
        fun z => B * tca_g ((x - L • latticePt k) - z) := by
      funext z; rw [sub_right_comm]
    rw [e]
    exact (tca_g_integrable.comp_sub_left (x - L • latticePt k)).const_mul B
  have hint : Integrable (fun z : Euc d => ∑ k ∈ K, B * tca_g (x - z - L • latticePt k)) volume :=
    integrable_finset_sum _ fun k _ => hint1 k
  have hnn : 0 ≤ᵐ[volume] fun z : Euc d => ∑ k ∈ K, B * tca_g (x - z - L • latticePt k) :=
    Filter.Eventually.of_forall fun z => Finset.sum_nonneg fun k _ =>
      mul_nonneg hB0 (tcb_g_pos _).le
  calc ∫ z in tcb_Q d L, ‖iteratedFDeriv ℝ j (perL L f) (x - z)‖
      ≤ ∫ z in tcb_Q d L, ∑ k ∈ K, B * tca_g (x - z - L • latticePt k) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _)
          hint.integrableOn ?_
        filter_upwards [ae_restrict_mem (tcb_measurableSet_Q L)] with z hz
        exact hpt z hz
    _ ≤ ∫ z, ∑ k ∈ K, B * tca_g (x - z - L • latticePt k) := setIntegral_le_integral hint hnn
    _ = ∑ k ∈ K, ∫ z, B * tca_g (x - z - L • latticePt k) := integral_finset_sum _ fun k _ => hint1 k
    _ = ∑ k ∈ K, B * ∫ w : Euc d, tca_g w := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_const_mul]
        congr 1
        have e : (fun z : Euc d => tca_g (x - z - L • latticePt k)) =
            fun z => tca_g ((x - L • latticePt k) - z) := by
          funext z; rw [sub_right_comm]
        rw [e]
        exact integral_sub_left_eq_self (fun w => tca_g w) volume (x - L • latticePt k)
    _ = 2 ^ d * B * ∫ w : Euc d, tca_g w := by
        rw [Finset.sum_const, hKcard, nsmul_eq_mul]
        push_cast
        ring

/-- The weighted bound for `f = c ζ_L ρ` on all of `ℝ^d`, in the form `‖D^j f(w)‖ ≤ 2 S_j ⟨w⟩^{-(d+3)}`. -/
theorem tcb_f_weighted {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (L : ℝ) (hL : 1 ≤ L)
    (n : ℕ) (ρ : Euc d → ℝ) (hρ : ContDiff ℝ (n : WithTop ℕ∞) ρ)
    (Kz : ℕ → ℝ) (hKz : ∀ (i : ℕ) (y : Euc d), ‖iteratedFDeriv ℝ i ζ y‖ ≤ Kz i)
    (hKz0 : ∀ i, 0 ≤ Kz i) (W : ℝ) (hW0 : 0 ≤ W)
    (hWk : ∀ k : ℕ, k ≤ n → ∀ w : Euc d,
      jbracket w ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ k ρ w‖ ≤ (d : ℝ) ^ k * W)
    (c : ℝ) (hc0 : 0 < c) (hc2 : c ≤ 2) (j : ℕ) (hj : j ≤ n) (w : Euc d) :
    ‖iteratedFDeriv ℝ j (fun x => c * (ζ (L⁻¹ • x) * ρ x)) w‖ ≤ 2 * tca_S d Kz W j * tca_g w := by
  have hF : ContDiff ℝ (n : WithTop ℕ∞) (fun x => ζ (L⁻¹ • x) * ρ x) :=
    (tca_zetaL_contDiff hζ L n).mul hρ
  have e : ‖iteratedFDeriv ℝ j (fun x => c * (ζ (L⁻¹ • x) * ρ x)) w‖ =
      |c| * ‖iteratedFDeriv ℝ j (fun x => ζ (L⁻¹ • x) * ρ x) w‖ :=
    tca_const_mul_norm (fun x => ζ (L⁻¹ • x) * ρ x) n hF c j hj w
  rw [e]
  have hw := tca_mu_weighted hζ L hL n ρ hρ Kz hKz hKz0 W hW0 hWk j hj w
  have hS0 := tca_S_nonneg d Kz hKz0 W hW0 j
  have hg := tcb_g_pos w
  have h1 : ‖iteratedFDeriv ℝ j (fun x => ζ (L⁻¹ • x) * ρ x) w‖ ≤ tca_S d Kz W j * tca_g w := by
    have h2 : ‖iteratedFDeriv ℝ j (fun x => ζ (L⁻¹ • x) * ρ x) w‖ =
        (jbracket w ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j (fun x => ζ (L⁻¹ • x) * ρ x) w‖) *
          tca_g w := by
      have := tca_g_mul w
      calc _ = ‖iteratedFDeriv ℝ j (fun x => ζ (L⁻¹ • x) * ρ x) w‖ * (jbracket w ^ ((d : ℝ) + 3) * tca_g w) := by
            rw [this, mul_one]
        _ = _ := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_right hw hg.le
  have hc : |c| ≤ 2 := by rw [abs_of_pos hc0]; exact hc2
  calc |c| * ‖iteratedFDeriv ℝ j (fun x => ζ (L⁻¹ • x) * ρ x) w‖
      ≤ |c| * (tca_S d Kz W j * tca_g w) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ ≤ 2 * (tca_S d Kz W j * tca_g w) :=
        mul_le_mul_of_nonneg_right hc (mul_nonneg hS0 hg.le)
    _ = 2 * tca_S d Kz W j * tca_g w := by ring

end HRS.MS.ToriCoefB
