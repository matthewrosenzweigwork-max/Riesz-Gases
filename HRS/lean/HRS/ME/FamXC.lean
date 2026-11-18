/-
# HRS.ME.FamX (packet X2, part C): the frozen `HRS.Main.critical_family_fixed_limsup`

Mechanism.  Write `A_N(θ) = |√N E Y_{N,θ}³|` and `E_N(θ) = √N W₂(law Y_{N,θ}, Gaussian)`.
* `sharpness_data`: `A_N(θ) ≤ K E_N(θ)` for `N ≥ 2`, `θ ∈ [0,R]`, and `∫₀^R A_N ≥ v` for `N ≥ N₁`;
* `rate_W2_pointwise_upper`: `E_N(θ) ≤ C₀` for `N ≥ 2`, `θ ∈ [0,R]`; so `A_N ≤ K C₀` there.
Reverse Fatou on `[0,R]` gives `v ≤ ∫⁻ limsup_N ofReal(A_N(θ)) dθ`; so the set where the limsup is
positive has positive measure.  On that set, `limsup A_N ≤ K limsup E_N`, hence `limsup E_N > 0`.
-/
import HRS.ME.FamXB
import HRS.ME.FamVE

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.FamX

open HRS

/-- The absolute third-moment term `|√N E[Y_{N,θ}³]|`. -/
def absY (d : ℕ) (k : Lattice d) (β : ℝ) (N : ℕ) (θ : ℝ) : ℝ :=
  |Real.sqrt N * ∫ X, rateY d ((d : ℝ) / 2) k β N θ X ^ 3 ∂(rateGibbs d ((d : ℝ) / 2) k β θ N)|

/-- **Fixed-parameter `limsup` clause.**  On a set of positive measure in `(0, R]`, the limsup of
`√N W₂` is positive. -/
theorem critical_family_fixed_limsup_proved {d : ℕ} :
    type_of% (@HRS.Main.critical_family_fixed_limsup d) := by
  intro hd β hβ k hk ρ hρ
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hg : 0 ≤ rieszCoeff d ((d : ℝ) / 2) k := (rieszCoeff_pos hd hs0 hsd k hk).le
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k) := ⟨_, rfl⟩
  rw [← hRdef]
  have hRpos : 0 < R := by
    have := mul_nonneg hβ.le hg
    rw [hRdef]; linarith
  obtain ⟨K, v, hK, hv, N₁, hN₁, hlowN, hpt⟩ := sharpness_data hd hβ k hk
  rw [← hRdef] at hlowN hpt
  obtain ⟨C0, hC0, hW⟩ := HRS.ME.FamV.rate_W2_pointwise_upper hd hs0 hsd β hβ k R
  -- pointwise bound `√N W₂ ≤ C₀` and `|√N E Y³| ≤ K C₀`
  have hpt' : ∀ θ ∈ Set.Icc (0 : ℝ) R, ∀ N : ℕ, 2 ≤ N →
      ENNReal.ofReal (absY d k β N θ) ≤ ENNReal.ofReal K * ENNReal.ofReal C0 := by
    intro θ hθ N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
    have hsq : (N : ℝ) ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt N := by
      rw [show -(1 : ℝ) / 2 = -(1 / 2) by ring, Real.rpow_neg hNr.le, ← Real.sqrt_eq_rpow]
      simp
    have hW' := hW θ hθ (ρ θ) (hρ θ) N hN
    have hE : ENNReal.ofReal (Real.sqrt N) *
        wassersteinE 2 (Main.rateLaw d ((d : ℝ) / 2) k β N θ)
          (Main.rateGaussian d ((d : ℝ) / 2) k β (ρ θ)) ≤ ENNReal.ofReal C0 := by
      refine le_trans (mul_le_mul' le_rfl hW') (le_of_eq ?_)
      rw [← ENNReal.ofReal_mul hsqrt.le, hsq]
      congr 1
      field_simp
    exact le_trans (hpt ρ hρ N hN θ hθ) (mul_le_mul' le_rfl hE)
  -- `absY` is continuous, hence measurable
  have hGm : ∀ n : ℕ, Measurable (fun θ : ℝ => ENNReal.ofReal (absY d k β (max n 2) θ)) := by
    intro n
    have hc : Continuous (fun θ : ℝ => absY d k β (max n 2) θ) :=
      h_continuous hd hβ k hk (le_max_right n 2)
    exact hc.measurable.ennreal_ofReal
  -- lower bound for the integrals, for `N ≥ N₁`
  have hlow : ∀ N : ℕ, N₁ ≤ N →
      ENNReal.ofReal v ≤ ∫⁻ θ in Set.Ioc 0 R, ENNReal.ofReal (absY d k β N θ) := by
    intro N hN
    have hN2 : 2 ≤ N := le_trans hN₁ hN
    have hc : Continuous (fun θ : ℝ => absY d k β N θ) := h_continuous hd hβ k hk hN2
    have hint : IntegrableOn (fun θ : ℝ => absY d k β N θ) (Set.Ioc 0 R) :=
      hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    have hA := hlowN N hN
    rw [intervalIntegral.integral_of_le hRpos.le] at hA
    calc ENNReal.ofReal v ≤ ENNReal.ofReal (∫ θ in Set.Ioc 0 R, absY d k β N θ) :=
          ENNReal.ofReal_le_ofReal hA
      _ = ∫⁻ θ in Set.Ioc 0 R, ENNReal.ofReal (absY d k β N θ) :=
          ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun θ => abs_nonneg _)
  -- reverse Fatou on `Ioc 0 R`, with the reindexing `n ↦ max n 2` to get a uniform bound
  have hbd : ∀ n : ℕ, (fun θ : ℝ => ENNReal.ofReal (absY d k β (max n 2) θ)) ≤ᵐ[volume.restrict (Set.Ioc 0 R)]
      (fun _ => ENNReal.ofReal K * ENNReal.ofReal C0) := fun n => by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun θ hθ => ?_)
    exact hpt' θ (Set.Ioc_subset_Icc_self hθ) (max n 2) (le_max_right n 2)
  have hfin : ∫⁻ _θ, ENNReal.ofReal K * ENNReal.ofReal C0 ∂(volume.restrict (Set.Ioc 0 R)) ≠ ⊤ := by
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hFatou := MeasureTheory.limsup_lintegral_le
    (μ := volume.restrict (Set.Ioc 0 R))
    (f := fun n θ => ENNReal.ofReal (absY d k β (max n 2) θ))
    (fun _ => ENNReal.ofReal K * ENNReal.ofReal C0) hGm hbd hfin
  have hLB : ENNReal.ofReal v ≤ limsup
      (fun n : ℕ => ∫⁻ θ in Set.Ioc 0 R, ENNReal.ofReal (absY d k β (max n 2) θ)) atTop := by
    refine le_limsup_of_frequently_le ?_
    refine Eventually.frequently ?_
    filter_upwards [eventually_ge_atTop N₁] with n hn
    exact hlow (max n 2) (le_trans hn (le_max_left _ _))
  have hLeq : ∀ θ : ℝ,
      limsup (fun n : ℕ => ENNReal.ofReal (absY d k β (max n 2) θ)) atTop =
        limsup (fun N : ℕ => ENNReal.ofReal (absY d k β N θ)) atTop := by
    intro θ
    apply limsup_congr
    filter_upwards [eventually_ge_atTop 2] with n hn
    simp [max_eq_left hn]
  have hFat : ENNReal.ofReal v ≤
      ∫⁻ θ in Set.Ioc 0 R, limsup (fun N : ℕ => ENNReal.ofReal (absY d k β N θ)) atTop :=
    le_trans hLB (le_trans hFatou (le_of_eq (lintegral_congr hLeq)))
  -- measurability of the limsup
  have hLm : Measurable (fun θ : ℝ => limsup (fun N : ℕ => ENNReal.ofReal (absY d k β N θ)) atTop) := by
    have h := Measurable.limsup hGm
    have heq : (fun θ : ℝ => limsup (fun N : ℕ => ENNReal.ofReal (absY d k β N θ)) atTop) =
        fun θ : ℝ => limsup (fun n : ℕ => ENNReal.ofReal (absY d k β (max n 2) θ)) atTop :=
      funext fun θ => (hLeq θ).symm
    rw [heq]
    exact h
  -- the set `A`
  obtain ⟨A, hAdef⟩ : ∃ A : Set ℝ, A = Set.Ioc 0 R ∩
      {θ : ℝ | 0 < limsup (fun N : ℕ => ENNReal.ofReal (absY d k β N θ)) atTop} := ⟨_, rfl⟩
  have hAm : MeasurableSet A := by
    rw [hAdef]
    exact measurableSet_Ioc.inter (measurableSet_lt measurable_const hLm)
  have hAsub : A ⊆ Set.Ioc 0 R := by
    rw [hAdef]; exact Set.inter_subset_left
  have hAmem : ∀ θ, θ ∈ A ↔
      θ ∈ Set.Ioc 0 R ∧ 0 < limsup (fun N : ℕ => ENNReal.ofReal (absY d k β N θ)) atTop := by
    intro θ; rw [hAdef]; exact Iff.rfl
  have hpos : 0 < volume A := by
    rw [pos_iff_ne_zero]
    intro h0
    have hae : ∀ᵐ θ ∂(volume.restrict (Set.Ioc 0 R)),
        limsup (fun N : ℕ => ENNReal.ofReal (absY d k β N θ)) atTop = 0 := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with θ hθ hθI
      by_contra hne
      exact hθ ((hAmem θ).2 ⟨hθI, pos_iff_ne_zero.2 hne⟩)
    have hz : ∫⁻ θ in Set.Ioc 0 R,
        limsup (fun N : ℕ => ENNReal.ofReal (absY d k β N θ)) atTop = 0 := by
      rw [lintegral_congr_ae hae, lintegral_zero]
    rw [hz] at hFat
    exact absurd hFat (not_le.2 (ENNReal.ofReal_pos.2 hv))
  refine ⟨A, hAm, hAsub, hpos, ?_⟩
  intro θ hθ
  obtain ⟨hθI, hθL⟩ := (hAmem θ).1 hθ
  have hθR : θ ∈ Set.Icc (0 : ℝ) R := Set.Ioc_subset_Icc_self hθI
  have hL : limsup (fun N : ℕ => ENNReal.ofReal (absY d k β N θ)) atTop ≤
      ENNReal.ofReal K * limsup (fun N : ℕ => ENNReal.ofReal (Real.sqrt N) *
        wassersteinE 2 (Main.rateLaw d ((d : ℝ) / 2) k β N θ)
          (Main.rateGaussian d ((d : ℝ) / 2) k β (ρ θ))) atTop := by
    refine le_trans (limsup_le_limsup ?_)
      (le_of_eq (ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top))
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact hpt ρ hρ N hN θ hθR
  refine pos_iff_ne_zero.2 fun h0 => ?_
  rw [h0, mul_zero] at hL
  exact absurd (lt_of_lt_of_le hθL hL) (lt_irrefl _)

end HRS.ME.FamX
