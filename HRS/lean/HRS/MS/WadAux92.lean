import HRS.MS.WadAux91

/-!
# S8.3, packet S8E-5, part 3: the sections `x' ↦ U_t(R x')(y)` lie in `C_M`

`S8e2a`: the pointwise form of clause (2a).  `s8e_diff_pt`: `|U_t(R x_1)(y) - U_t(R x_2)(y)| ≤ C_d e^{-ct} ε ⟨y⟩^M` if
`Wt M ε (R x_1 - R x_2)` (doubly centered `R`).  `s8e_G_cm`: `x' ↦ U_t (R x') y` is in `C_M`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- Pointwise clause (2a) for the extension `s85_Ulim`. -/
def S8e2a (a β M : ℝ) (ρβ : Euc d → ℝ) (Cd c : ℝ) : Prop :=
  ∀ {t : ℝ}, 1 ≤ t → ∀ {h : Euc d → ℝ} {C : ℝ}, MemCM M h → Wt M C h → ∀ y : Euc d,
    |s85_Ulim a β ρβ M t (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) h) y| ≤
      Cd * Real.exp (-c * t) * C * jbracket y ^ M

theorem s8e_projMean_centered {μ : Measure (Euc d)} {h : Euc d → ℝ} (h0 : ∫ y, h y ∂μ = 0) :
    HRS.Whole.projMean μ h = h := by
  funext y
  unfold HRS.Whole.projMean HRS.Whole.pair
  rw [h0, sub_zero]

theorem s8e_diff_pt (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) {Cd c : ℝ} (h2a : S8e2a a β M ρβ Cd c)
    {R : Euc d → Euc d → ℝ} (hR : MemCMpair M 0 R)
    (hdc : IsDoublyCentered (HRS.Whole.withDensityReal ρβ) R) {t : ℝ} (ht : 1 ≤ t) {x1 x2 : Euc d} {ε : ℝ}
    (hε : Wt M ε (fun y => R x1 y - R x2 y)) (y : Euc d) :
    |s85_Ulim a β ρβ M t (R x1) y - s85_Ulim a β ρβ M t (R x2) y| ≤
      Cd * Real.exp (-c * t) * ε * jbracket y ^ M := by
  have hM := hMpos.le
  have H : S85Hyp d a β t M ρβ := ⟨hd, ha, hβ, by linarith, hM, hρ⟩
  have hP : HRS.Whole.IsProbDensity ρβ := hρ.1.1
  have hg : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  have hm1 := s8e_R_cm hR x1
  have hm2 := s8e_R_cm hR x2
  have hD : MemCM M (fun y => R x1 y - R x2 y) := by
    refine ⟨hm1.1.sub hm2.1, ?_⟩
    have := hm1.2.sub hm2.2
    rw [sub_zero] at this
    refine this.congr fun y => ?_
    simp [sub_div]
  have hi1 := s8d_integrable_of_memCM hP hg hM hm1
  have hi2 := s8d_integrable_of_memCM hP hg hM hm2
  have hcen : ∫ y, (R x1 y - R x2 y) ∂(HRS.Whole.withDensityReal ρβ) = 0 := by
    rw [integral_sub hi1 hi2, hdc.2 x1, hdc.2 x2, sub_zero]
  have hlin := s85_Ulim_lin H (by linarith) le_rfl hm2 hm1 (-1) y
  have e : (fun y => -1 * R x2 y + R x1 y) = fun y => R x1 y - R x2 y := by funext y; ring
  rw [e] at hlin
  have := h2a ht hD hε y
  rw [s8e_projMean_centered hcen, hlin] at this
  rw [show s85_Ulim a β ρβ M t (R x1) y - s85_Ulim a β ρβ M t (R x2) y =
    -1 * s85_Ulim a β ρβ M t (R x2) y + s85_Ulim a β ρβ M t (R x1) y by ring]
  exact this

theorem s8e_R_wt {M : ℝ} {R : Euc d → Euc d → ℝ} {N0 : ℝ} (hN0 : ∀ z, |s8e_Qa M R z| ≤ N0) (x : Euc d) :
    Wt M (N0 * jbracket x ^ M) (R x) := fun y => by
  rw [Real.norm_eq_abs, s8e_R_eq M R x y, abs_mul, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (s83_jb_pos x).le M), abs_of_nonneg (Real.rpow_nonneg (s83_jb_pos y).le M)]
  have := hN0 (x, y)
  have h1 := Real.rpow_nonneg (s83_jb_pos x).le M
  have h2 := Real.rpow_nonneg (s83_jb_pos y).le M
  calc jbracket x ^ M * jbracket y ^ M * |s8e_Qa M R (x, y)| ≤ jbracket x ^ M * jbracket y ^ M * N0 :=
        mul_le_mul_of_nonneg_left this (mul_nonneg h1 h2)
    _ = _ := by ring

theorem s8e_G_bound (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) {Cd c : ℝ} (h2a : S8e2a a β M ρβ Cd c)
    {R : Euc d → Euc d → ℝ} (hR : MemCMpair M 0 R)
    (hdc : IsDoublyCentered (HRS.Whole.withDensityReal ρβ) R) {N0 : ℝ} (hN0 : ∀ z, |s8e_Qa M R z| ≤ N0)
    {t : ℝ} (ht : 1 ≤ t) (x' y : Euc d) :
    |s85_Ulim a β ρβ M t (R x') y| ≤ Cd * Real.exp (-c * t) * (N0 * jbracket x' ^ M) * jbracket y ^ M := by
  have := h2a ht (s8e_R_cm hR x') (s8e_R_wt hN0 x') y
  rwa [s8e_projMean_centered (hdc.2 x')] at this

end HRS.MS.Wad
