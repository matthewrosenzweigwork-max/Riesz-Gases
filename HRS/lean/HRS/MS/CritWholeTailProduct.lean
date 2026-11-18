import HRS.MS.CritWholeTwoPole
import HRS.MS.CritWholeRows
import HRS.MS.CritWholeQuadEnv

/-!
# S8.1 XS, TT06: the integrated tail sum in `L^{2q}(μ^n)`

`T = tailConv` (the tail kernel integrated against the test `φ`): its mean is `O(1/H)` (Tonelli with the TT01 row), its
`6q`-th moment is bounded (TT01 for `φ = 1`; TT02 for `φ = g(x-·)`, since `tailG ≤ g`).  The generic capped-tail
`taylor_sum_bound` and the real arithmetic `taylor_real_est` at `N = ν⁸`, `H = 2ν⁵`, `M = ν³` finish.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.Wr HRS.TaylorAux

namespace HRS.Whole.S81b

variable {d : ℕ} {M βm βp : ℝ}

theorem s81b_tailG_nonneg (hd : 1 ≤ d) (H : ℝ) (hH : 0 ≤ H) (z : Euc d) : 0 ≤ tailG d H z := by
  simp only [tailG, truncKernel, critG]
  linarith [min_le_left (rieszKernel d ((d : ℝ) / 2) z) H]

theorem s81b_tailG_le (hd : 1 ≤ d) (H : ℝ) (hH : 0 ≤ H) (z : Euc d) : tailG d H z ≤ critG d z := by
  have hs0 : ((d : ℝ) / 2) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have h0 : 0 ≤ truncKernel d ((d : ℝ) / 2) H z := le_min (by
    rw [Q34.rieszKernel_eq hs0]; exact Real.rpow_nonneg (norm_nonneg _) _) hH
  simp only [tailG]; linarith

theorem s81b_tailG_neg (z : Euc d) (H : ℝ) : tailG d H (-z) = tailG d H z := by
  simp [tailG, truncKernel, critG, rieszKernel, norm_neg]

theorem s81b_tailG_meas (hd : 1 ≤ d) (H : ℝ) : Measurable (tailG d H) :=
  (s81b_critG_meas hd).sub (s81b_trunc_meas hd H)

/-- The three tail interface bounds (mass of `φ`, `L¹` with decay `1/H`, `L^p`). -/
theorem s81b_tail_bounds (hd : 2 ≤ d) (M : ℝ) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ H : ℝ, 2 ≤ H → ∀ x : Euc d, ∀ φ ∈ tests d x,
        ∫⁻ y, ENNReal.ofReal (φ y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal C ∧
        ∫⁻ z, (∫⁻ y, ENNReal.ofReal (φ y) * ENNReal.ofReal (tailG d H (y - z)) ∂(withDensityReal ρ))
          ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C / H) ∧
        ∫⁻ z, (∫⁻ y, ENNReal.ofReal (φ y) * ENNReal.ofReal (tailG d H (y - z)) ∂(withDensityReal ρ)) ^ p
          ∂(withDensityReal ρ) ≤ ENNReal.ofReal C := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < ((d : ℝ) / 2) := by linarith
  have hsd : ((d : ℝ) / 2) < d := by linarith
  obtain ⟨C1, hC10, hC1⟩ := s81b_critical_truncation_rows hd M
  obtain ⟨C2, hC20, hC2⟩ := s81b_two_pole_moments hd M p hp
  set Ch : ℝ := max (potentialBound d ((d : ℝ) / 2) M) 0 with hChdef
  have hCh0 : 0 ≤ Ch := le_max_right _ _
  set C : ℝ := 1 + Ch + C1 + C1 ^ p + C2 + Ch * C1 with hCdef
  have hC1p : 0 ≤ C1 ^ p := by positivity
  have hChC1 : 0 ≤ Ch * C1 := by positivity
  have hC1C : C1 ≤ C := by linarith
  have hChC : Ch ≤ C := by linarith
  have hC1pC : C1 ^ p ≤ C := by linarith
  have hC2C : C2 ≤ C := by linarith
  have hC1' : 1 ≤ C := by linarith
  have hChC1C : Ch * C1 ≤ C := by linarith
  refine ⟨C, by positivity, fun ρ hρ hM H hH x φ hφ => ?_⟩
  have hH0 : 0 < H := by linarith
  have hprob := Q34.isProbabilityMeasure_nu hρ
  have hgm := s81b_critG_meas hd1
  have hGm := s81b_tailG_meas hd1 H
  have hMnn : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  -- row bound in lintegral form
  have hrow : ∀ z, ∫⁻ y, ENNReal.ofReal (tailG d H (y - z)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C1 / H) := by
    intro z
    obtain ⟨hI, -, hV, -⟩ := hC1 ρ hρ hM H hH z
    have : ∫⁻ y, ENNReal.ofReal (tailG d H (y - z)) ∂(withDensityReal ρ) =
        ∫⁻ y, ENNReal.ofReal (tailG d H (z - y)) ∂(withDensityReal ρ) := by
      refine lintegral_congr fun y => ?_
      rw [← neg_sub, s81b_tailG_neg]
    rw [this, ← ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall fun y =>
      s81b_tailG_nonneg hd1 H hH0.le _)]
    exact ENNReal.ofReal_le_ofReal hV
  have hC1H : C1 / H ≤ C / H := div_le_div_of_nonneg_right hC1C hH0.le
  have hTm : ∀ φ' : Euc d → ℝ, Measurable φ' → Measurable fun z =>
      ∫⁻ y, ENNReal.ofReal (φ' y) * ENNReal.ofReal (tailG d H (y - z)) ∂(withDensityReal ρ) := by
    intro φ' hφ'
    refine Measurable.lintegral_prod_right' (f := fun p : Euc d × Euc d =>
      ENNReal.ofReal (φ' p.2) * ENNReal.ofReal (tailG d H (p.2 - p.1))) ?_
    exact (hφ'.comp measurable_snd).ennreal_ofReal.mul
      (hGm.comp (measurable_snd.sub measurable_fst)).ennreal_ofReal
  have hL1 : ∀ φ' : Euc d → ℝ, Measurable φ' →
      ∫⁻ z, (∫⁻ y, ENNReal.ofReal (φ' y) * ENNReal.ofReal (tailG d H (y - z)) ∂(withDensityReal ρ))
        ∂(withDensityReal ρ) ≤ (∫⁻ y, ENNReal.ofReal (φ' y) ∂(withDensityReal ρ)) * ENNReal.ofReal (C1 / H) := by
    intro φ' hφ'
    rw [lintegral_lintegral_swap]
    · calc ∫⁻ y, ∫⁻ z, ENNReal.ofReal (φ' y) * ENNReal.ofReal (tailG d H (y - z)) ∂(withDensityReal ρ)
            ∂(withDensityReal ρ)
          = ∫⁻ y, ENNReal.ofReal (φ' y) * ∫⁻ z, ENNReal.ofReal (tailG d H (y - z)) ∂(withDensityReal ρ)
            ∂(withDensityReal ρ) := by
            refine lintegral_congr fun y => ?_
            rw [lintegral_const_mul (f := fun z => ENNReal.ofReal (tailG d H (y - z)))]
            exact (hGm.comp (measurable_const.sub measurable_id)).ennreal_ofReal
        _ ≤ ∫⁻ y, ENNReal.ofReal (φ' y) * ENNReal.ofReal (C1 / H) ∂(withDensityReal ρ) :=
            lintegral_mono fun y => mul_le_mul' le_rfl (by
              have := hrow y
              calc _ = ∫⁻ z, ENNReal.ofReal (tailG d H (y - z)) ∂(withDensityReal ρ) := rfl
                _ ≤ _ := by
                  obtain ⟨hI, -, hV, -⟩ := hC1 ρ hρ hM H hH y
                  rw [← ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall fun z =>
                    s81b_tailG_nonneg hd1 H hH0.le _)]
                  exact ENNReal.ofReal_le_ofReal hV)
        _ = _ := lintegral_mul_const _ (ENNReal.measurable_ofReal.comp hφ')
    · exact ((hφ'.comp measurable_snd).ennreal_ofReal.mul
        (hGm.comp (measurable_snd.sub measurable_fst)).ennreal_ofReal).aemeasurable
  rcases hφ with rfl | rfl
  · refine ⟨?_, ?_, ?_⟩
    · simp only [ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one]
      exact ENNReal.ofReal_one.symm.le.trans (ENNReal.ofReal_le_ofReal hC1')
    · refine (hL1 _ measurable_const).trans ?_
      simp only [ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one, one_mul]
      exact ENNReal.ofReal_le_ofReal hC1H
    · have hpt : ∀ z, ∫⁻ y, ENNReal.ofReal 1 * ENNReal.ofReal (tailG d H (y - z)) ∂(withDensityReal ρ) ≤
          ENNReal.ofReal C1 := by
        intro z
        simp only [ENNReal.ofReal_one, one_mul]
        refine (hrow z).trans (ENNReal.ofReal_le_ofReal ?_)
        rw [div_le_iff₀ hH0]; nlinarith
      calc ∫⁻ z, (∫⁻ y, ENNReal.ofReal 1 * ENNReal.ofReal (tailG d H (y - z)) ∂(withDensityReal ρ)) ^ p
            ∂(withDensityReal ρ)
          ≤ ∫⁻ z, ENNReal.ofReal C1 ^ p ∂(withDensityReal ρ) :=
            lintegral_mono fun z => pow_le_pow_left' (hpt z) p
        _ = ENNReal.ofReal C1 ^ p := by simp
        _ = ENNReal.ofReal (C1 ^ p) := (ENNReal.ofReal_pow hC10 p).symm
        _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hC1pC
  · obtain ⟨hi, -, hle⟩ := wr13a_potential_bound hd1 hs0 hsd hρ hM x
    have hnn : ∀ y, 0 ≤ critG d (x - y) := fun y => s81b_critG_nonneg hd1 _
    have hmass0 : ∫⁻ y, ENNReal.ofReal (critG d (x - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal Ch := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnn)]
      exact ENNReal.ofReal_le_ofReal (hle.trans (le_max_left _ _))
    have hmass : ∫⁻ y, ENNReal.ofReal (critG d (x - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal C :=
      hmass0.trans (ENNReal.ofReal_le_ofReal hChC)
    refine ⟨hmass, ?_, ?_⟩
    · refine (hL1 _ (hgm.comp (measurable_const.sub measurable_id))).trans ?_
      calc (∫⁻ y, ENNReal.ofReal (critG d (x - y)) ∂(withDensityReal ρ)) * ENNReal.ofReal (C1 / H)
          ≤ ENNReal.ofReal Ch * ENNReal.ofReal (C1 / H) := by gcongr
        _ = ENNReal.ofReal (Ch * (C1 / H)) := (ENNReal.ofReal_mul hCh0).symm
        _ ≤ ENNReal.ofReal (C / H) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [← mul_div_assoc]
            exact div_le_div_of_nonneg_right hChC1C hH0.le
    · have hpt : ∀ z, ∫⁻ y, ENNReal.ofReal (critG d (x - y)) * ENNReal.ofReal (tailG d H (y - z))
          ∂(withDensityReal ρ) ≤ twoPole ρ x z := by
        intro z
        unfold twoPole
        refine lintegral_mono fun y => ?_
        rw [ENNReal.ofReal_mul (s81b_critG_nonneg hd1 _)]
        exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (s81b_tailG_le hd1 H hH0.le _))
      obtain ⟨-, hTP⟩ := hC2 ρ hρ hM x
      calc ∫⁻ z, (∫⁻ y, ENNReal.ofReal (critG d (x - y)) * ENNReal.ofReal (tailG d H (y - z))
            ∂(withDensityReal ρ)) ^ p ∂(withDensityReal ρ)
          ≤ ∫⁻ z, twoPole ρ x z ^ p ∂(withDensityReal ρ) :=
            lintegral_mono fun z => pow_le_pow_left' (hpt z) p
        _ ≤ ENNReal.ofReal C2 := hTP
        _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hC2C

theorem s81b_integrated_tail_product (hd : 2 ≤ d) (M βm βp : ℝ)
    (hβm : 0 < βm) (hβ : βm ≤ βp) (q : ℕ) (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N →
      ∀ i : Fin (N - 1), ∀ x : Euc d, ∀ φ ∈ tests d x,
        Measurable (tailConv D φ (2 * HRS.TaylorAux.taylorNu N ^ 5)) ∧
        HRS.TaylorAux.taylorLp (product D (N - 1)) ((2 * q : ℕ) : ℝ)
          (fun Y => ENNReal.ofReal (D.beta / N) *
            ∑ j ∈ Finset.univ.erase i,
              tailConv D φ (2 * HRS.TaylorAux.taylorNu N ^ 5) (Y j)) ≤
          ENNReal.ofReal (C * (HRS.TaylorAux.taylorNu N ^ 5)⁻¹) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Ct, hCt0, hCt⟩ := s81b_tail_bounds hd M (6 * q) (by omega)
  have hkb := taylor_kb_one_le q
  have hβp : 0 < βp := hβm.trans_le hβ
  refine ⟨βp * Ct / 2 + βp * taylor_kb q * Real.sqrt (Ct / 2 + 1) + βp * max Ct 1, by positivity,
    fun D N hN i x φ hφ => ?_⟩
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have hββp : D.beta ≤ βp := D.beta_mem.2
  have hprob : IsProbabilityMeasure (mu D) := Q34.isProbabilityMeasure_nu D.prob
  set ν : ℝ := taylorNu N with hν
  have hν1 : 1 ≤ ν := one_le_taylorNu N (by omega)
  have hν8 : ν ^ 8 = N := taylorNu_pow8 N
  have hν0 : 0 < ν := by linarith
  set H : ℝ := 2 * ν ^ 5 with hHdef
  have hH : 2 ≤ H := by
    have : 1 ≤ ν ^ 5 := one_le_pow₀ hν1
    rw [hHdef]; linarith
  have hH0 : 0 < H := by linarith
  have hgm := s81b_critG_meas hd1
  have hφm : Measurable φ := by
    rcases hφ with rfl | rfl
    · exact measurable_const
    · exact hgm.comp (measurable_const.sub measurable_id)
  have hGm := s81b_tailG_meas hd1 H
  have hTm : Measurable (tailConv D φ H) := by
    unfold tailConv
    refine Measurable.lintegral_prod_right' (f := fun p : Euc d × Euc d =>
      ENNReal.ofReal (φ p.2) * ENNReal.ofReal (tailG d H (p.2 - p.1))) ?_
    exact (hφm.comp measurable_snd).ennreal_ofReal.mul
      (hGm.comp (measurable_snd.sub measurable_fst)).ennreal_ofReal
  refine ⟨hTm, ?_⟩
  obtain ⟨-, hL1, hLp⟩ := hCt D.rho D.prob D.bound H hH x φ hφ
  have hB2 := taylor_sum_bound (μ := mu D) (Finset.univ.erase i) (tailConv D φ H) hTm q hq
    (m1 := Ct / H) (CT := Ct) (M := ν ^ 3) (lam := D.beta / N) (by positivity) hL1 hLp
    (by positivity) (by positivity)
  refine hB2.trans (ENNReal.ofReal_le_ofReal ?_)
  have hcard : ((Finset.univ.erase i).card : ℝ) ≤ ν ^ 8 := by
    rw [hν8, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have : N - 1 - 1 ≤ N := by omega
    exact_mod_cast this
  have := taylor_real_est (ν := ν) (β := D.beta) (Ct := Ct) (kb := taylor_kb q)
    (ℓ := ((Finset.univ.erase i).card : ℝ)) hν1 hβ0 hCt0 (by linarith) (Nat.cast_nonneg _) hcard
  rw [hν8] at this
  simp only [hHdef] at this ⊢
  refine this.trans ?_
  have hc : 0 ≤ (ν ^ 5)⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_right ?_ hc
  have h1 : 0 ≤ Ct / 2 := by positivity
  have h2 : 0 ≤ taylor_kb q * Real.sqrt (Ct / 2 + 1) := by positivity
  have h3 : 0 ≤ max Ct 1 := le_trans zero_le_one (le_max_right _ _)
  nlinarith [mul_le_mul_of_nonneg_right hββp h1, mul_le_mul_of_nonneg_right hββp h2,
    mul_le_mul_of_nonneg_right hββp h3]

end HRS.Whole.S81b
