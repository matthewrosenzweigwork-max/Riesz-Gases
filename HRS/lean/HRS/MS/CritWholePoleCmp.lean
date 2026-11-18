import HRS.MS.CritWholeTTDefs
import HRS.MS.WrMargBAux1
import HRS.MS.WrInsAux1

/-!
# S8.1 XS, TT03: pole comparison (pole-normalizer lower bound; pole law dominated by `Q_{n,nβ/N}`)

The cavity law is a bounded tilt of `Q_{n,b}`, `b = nβ/N` (extra field `(β/N) ∑ h(y_i)`), and the pole law is dominated by
the cavity law divided by the pole normalizer, which is bounded below by Jensen with the exact first moment
`wr13d_integral_X` and the cavity-marginal domination `wr13d_cavMarg_le`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.Wr

namespace HRS.Whole.S81b

variable {d : ℕ}

theorem s81b_smul_le_smul {α : Type*} [MeasurableSpace α] {μ₁ μ₂ μ₃ : Measure α} {c₁ c₂ : ℝ≥0∞}
    (h₁ : μ₁ ≤ c₁ • μ₂) (h₂ : μ₂ ≤ c₂ • μ₃) : μ₁ ≤ (c₁ * c₂) • μ₃ := by
  refine Measure.le_iff.2 fun s hs => ?_
  have := Measure.le_iff.1 h₁ s hs
  have h2 := Measure.le_iff.1 h₂ s hs
  simp only [Measure.smul_apply, smul_eq_mul] at this h2 ⊢
  calc μ₁ s ≤ c₁ * μ₂ s := this
    _ ≤ c₁ * (c₂ * μ₃ s) := by gcongr
    _ = _ := by ring

/-- The cavity law is a bounded tilt of `Q_{n, nβ/N}`. -/
theorem s81b_cavity_le_Q (hs0 : 0 < ((d : ℝ) / 2)) {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Mg β : ℝ}
    (hconv : ∀ z, convMeasure (rieszKernel d ((d : ℝ) / 2)) μ z ≤ Mg) (hβ : 0 ≤ β) (k : ℕ) :
    cavityLaw d ((d : ℝ) / 2) (k + 2) β μ ≤
      ENNReal.ofReal (Real.exp (2 * (β * max Mg 0))) •
        modulatedGibbs (rieszKernel d ((d : ℝ) / 2)) (k + 1) (((k + 1 : ℕ) : ℝ) * β / ((k + 2 : ℕ) : ℝ)) μ := by
  set s : ℝ := (d : ℝ) / 2 with hs
  have hN0 : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hk0 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  set b : ℝ := ((k + 1 : ℕ) : ℝ) * β / ((k + 2 : ℕ) : ℝ) with hb
  have hb0 : 0 ≤ b := by positivity
  have hlam : 0 ≤ β / ((k + 2 : ℕ) : ℝ) := by positivity
  have hQ := wr13a_modulatedGibbs_eq hs0 hconv hb0 k
  have hlam' : b / ((k + 1 : ℕ) : ℝ) = β / ((k + 2 : ℕ) : ℝ) := by
    rw [hb]; field_simp
  rw [hlam'] at hQ
  have hcav := wr13a_cavityLaw_eq hs0 hconv hβ (k + 2)
  rw [hQ, hcav]
  set P : Measure (EucConfig d (k + 1)) := Measure.pi fun _ => μ
  have hEm := wr13a_E_meas hs0 μ (β / ((k + 2 : ℕ) : ℝ)) β (n := k + 1)
  have hEm' := wr13a_E_meas hs0 μ (β / ((k + 2 : ℕ) : ℝ)) b (n := k + 1)
  obtain ⟨h0, h1⟩ := wr13a_tilt_ne P hEm' (fun Y => wr13a_E_le hs0 hconv hlam hb0 Y)
  have hMg : 0 ≤ max Mg 0 := le_max_right _ _
  have hU : ∀ Y : EucConfig d (k + 1),
      |wr13a_E d s μ (β / ((k + 2 : ℕ) : ℝ)) β Y - wr13a_E d s μ (β / ((k + 2 : ℕ) : ℝ)) b Y| ≤
        β * max Mg 0 := by
    intro Y
    have hS0 : 0 ≤ ∑ i, convMeasure (rieszKernel d s) μ (Y i) :=
      Finset.sum_nonneg fun i _ => wr13a_conv_nonneg hs0 μ _
    have hS1 : ∑ i, convMeasure (rieszKernel d s) μ (Y i) ≤ ((k + 1 : ℕ) : ℝ) * max Mg 0 :=
      (wr13a_sum_conv_le hconv Y).trans (by
        have : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) this)
    have hbb : β - b = β / ((k + 2 : ℕ) : ℝ) := by rw [hb]; field_simp; push_cast; ring
    have hdiff : wr13a_E d s μ (β / ((k + 2 : ℕ) : ℝ)) β Y - wr13a_E d s μ (β / ((k + 2 : ℕ) : ℝ)) b Y =
        (β / ((k + 2 : ℕ) : ℝ)) * ∑ i, convMeasure (rieszKernel d s) μ (Y i) := by
      rw [← hbb]; unfold wr13a_E; ring
    rw [hdiff, abs_of_nonneg (mul_nonneg hlam hS0)]
    calc (β / ((k + 2 : ℕ) : ℝ)) * ∑ i, convMeasure (rieszKernel d s) μ (Y i)
        ≤ (β / ((k + 2 : ℕ) : ℝ)) * (((k + 1 : ℕ) : ℝ) * max Mg 0) :=
          mul_le_mul_of_nonneg_left hS1 hlam
      _ = ((β / ((k + 2 : ℕ) : ℝ)) * ((k + 1 : ℕ) : ℝ)) * max Mg 0 := by ring
      _ ≤ β * max Mg 0 := by
          refine mul_le_mul_of_nonneg_right ?_ hMg
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          push_cast
          nlinarith
  exact ProdTransfer.tilt_le_bdd P _ _ hEm hEm' (β * max Mg 0) hU h0 h1

theorem s81b_smul_mono {α : Type*} [MeasurableSpace α] {μ₁ μ₂ : Measure α} {c c' : ℝ≥0∞}
    (h : μ₁ ≤ c • μ₂) (hc : c ≤ c') : μ₁ ≤ c' • μ₂ := by
  refine Measure.le_iff.2 fun s hs => ?_
  have := Measure.le_iff.1 h s hs
  simp only [Measure.smul_apply, smul_eq_mul] at this ⊢
  exact this.trans (by gcongr)

theorem s81b_pole_comparison (hd : 2 ≤ d) (M βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N →
      ∀ x : Euc d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        C⁻¹ ≤ poleNormalizer d ((d : ℝ) / 2) N D.beta (mu D) x t ∧
        pole D N x t ≤ ENNReal.ofReal C •
          modulatedGibbs (critG d) (N - 1) (((N - 1 : ℕ) : ℝ) * D.beta / N) (mu D) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < ((d : ℝ) / 2) := by linarith
  have hsd : ((d : ℝ) / 2) < d := by linarith
  have hβp : 0 ≤ βp := by linarith
  obtain ⟨C1, hC11, hC1⟩ := wr13d_cavMarg_le hd hs0 hsd βp M hβp
  set Mg : ℝ := max (potentialBound d ((d : ℝ) / 2) M) 0 with hMgdef
  have hMg : 0 ≤ Mg := le_max_right _ _
  refine ⟨Real.exp (βp * C1 * Mg) * Real.exp (2 * (βp * Mg)), ?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity))
      (Real.one_le_exp (by positivity))
  intro D N hN x t ht
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
  set s : ℝ := (d : ℝ) / 2 with hs
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have hββp : D.beta ≤ βp := D.beta_mem.2
  have : IsProbabilityMeasure (mu D) := wr13a_isProb_density D.prob
  have hconv := wr13a_conv_le_density hd1 hs0 hsd D.prob D.bound
  have hMg0 : 0 ≤ potentialBound d s M := wr13a_potentialBound_nonneg hd1 hs0 hsd D.prob D.bound
  have hMgeq : Mg = potentialBound d s M := max_eq_left hMg0
  have := wr13a_cavityLaw_isProb hs0 hconv hβ0.le (k + 2)
  set P0 := cavityLaw d s (k + 2) D.beta (mu D) with hP0
  have hN0 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
  -- Jensen lower bound
  set K : ℝ := D.beta * C1 * Mg with hK
  have hlow : Real.exp (-K) ≤ poleNormalizer d s (k + 2) D.beta (mu D) x t := by
    have hcoord : ∀ j : Fin (k + 2 - 1), Integrable (fun Y : EucConfig d (k + 2 - 1) => rieszKernel d s (x - Y j)) P0 :=
      fun j => wr13c2_integrable_coord hd hs0 hsd D.prob D.bound hβ0.le (N := k + 2) (by omega) x j
    have hint : Integrable (fun Y : EucConfig d (k + 2 - 1) => ∑ j, rieszKernel d s (x - Y j)) P0 :=
      integrable_finsetSum _ fun j _ => hcoord j
    set u : EucConfig d (k + 2 - 1) → ℝ := fun Y => (t * (D.beta / ((k + 2 : ℕ) : ℝ))) *
      ∑ j, rieszKernel d s (x - Y j) with hu
    have hu0 : ∀ Y, 0 ≤ u Y := fun Y => mul_nonneg (by have := ht.1; positivity)
      (Finset.sum_nonneg fun j _ => wr13a_g_nonneg hs0 _)
    have hX : ∫ Y, wr13c2_X d s (k + 2) D.beta x Y ∂P0 = -(D.beta / ((k + 1 + 1 : ℕ) : ℝ)) * ((k + 1 : ℕ) : ℝ) *
        ∫ y, rieszKernel d s (x - y) ∂(cavityMarginal d s (k + 1 + 1) D.beta (mu D)) :=
      wr13d_integral_X hd hs0 hsd D.prob D.bound hβ0.le (n := k + 1) (by omega) x
    have hXu : ∫ Y, wr13c2_X d s (k + 2) D.beta x Y ∂P0 = -(D.beta / ((k + 2 : ℕ) : ℝ)) *
        ∫ Y, ∑ j, rieszKernel d s (x - Y j) ∂P0 := integral_const_mul _ _
    have hnu : ∫ y, rieszKernel d s (x - y) ∂(cavityMarginal d s (k + 1 + 1) D.beta (mu D)) ≤
        C1 * Mg := by
      have hdom := hC1 D.rho D.prob D.bound D.beta hβ0.le hββp (k + 2) (by omega)
      have hgi : Integrable (fun y => rieszKernel d s (x - y)) (mu D) :=
        (wr13a_potential_bound hd1 hs0 hsd D.prob D.bound x).1
      have h1 : ∫ y, rieszKernel d s (x - y) ∂(cavityMarginal d s (k + 2) D.beta (mu D)) ≤
          ∫ y, rieszKernel d s (x - y) ∂(ENNReal.ofReal C1 • mu D) :=
        integral_mono_measure hdom (Filter.Eventually.of_forall fun y => wr13a_g_nonneg hs0 _)
          (hgi.smul_measure ENNReal.ofReal_ne_top)
      rw [integral_smul_measure, ENNReal.toReal_ofReal (by linarith), smul_eq_mul] at h1
      refine h1.trans ?_
      have : ∫ y, rieszKernel d s (x - y) ∂(mu D) ≤ Mg := (hconv x).trans (by rw [hMgeq])
      exact mul_le_mul_of_nonneg_left this (by linarith)
    have hnu0 : 0 ≤ ∫ y, rieszKernel d s (x - y) ∂(cavityMarginal d s (k + 1 + 1) D.beta (mu D)) :=
      integral_nonneg fun y => wr13a_g_nonneg hs0 _
    have hint_u : ∫ Y, u Y ∂P0 ≤ K := by
      have e1 : ∫ Y, u Y ∂P0 = (t * (D.beta / ((k + 2 : ℕ) : ℝ))) *
          ∫ Y, ∑ j, rieszKernel d s (x - Y j) ∂P0 := integral_const_mul _ _
      have e2 : ∫ Y, ∑ j, rieszKernel d s (x - Y j) ∂P0 =
          ((k + 1 : ℕ) : ℝ) * ∫ y, rieszKernel d s (x - y) ∂(cavityMarginal d s (k + 1 + 1) D.beta (mu D)) := by
        have hne : -(D.beta / ((k + 2 : ℕ) : ℝ)) ≠ 0 := by
          have : 0 < D.beta / ((k + 2 : ℕ) : ℝ) := by positivity
          linarith
        have := hX.symm.trans hXu
        have h3 : -(D.beta / ((k + 2 : ℕ) : ℝ)) * (((k + 1 : ℕ) : ℝ) * ∫ y, rieszKernel d s (x - y)
            ∂(cavityMarginal d s (k + 1 + 1) D.beta (mu D))) = -(D.beta / ((k + 2 : ℕ) : ℝ)) *
            ∫ Y, ∑ j, rieszKernel d s (x - Y j) ∂P0 := by
          rw [← this]; push_cast; ring
        exact (mul_left_cancel₀ hne h3).symm
      rw [e1, e2]
      have hcoef : (t * (D.beta / ((k + 2 : ℕ) : ℝ))) * ((k + 1 : ℕ) : ℝ) ≤ D.beta := by
        have : (t * (D.beta / ((k + 2 : ℕ) : ℝ))) * ((k + 1 : ℕ) : ℝ) ≤ 1 * (D.beta / ((k + 2 : ℕ) : ℝ)) *
            ((k + 2 : ℕ) : ℝ) := by
          have h2 : ((k + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by push_cast; linarith
          have h0 : 0 ≤ D.beta / ((k + 2 : ℕ) : ℝ) := by positivity
          calc _ ≤ 1 * (D.beta / ((k + 2 : ℕ) : ℝ)) * ((k + 1 : ℕ) : ℝ) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 h0) (by positivity)
            _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
        refine this.trans (le_of_eq ?_)
        field_simp
      calc (t * (D.beta / ((k + 2 : ℕ) : ℝ))) * (((k + 1 : ℕ) : ℝ) * ∫ y, rieszKernel d s (x - y)
            ∂(cavityMarginal d s (k + 1 + 1) D.beta (mu D)))
          = ((t * (D.beta / ((k + 2 : ℕ) : ℝ))) * ((k + 1 : ℕ) : ℝ)) * ∫ y, rieszKernel d s (x - y)
            ∂(cavityMarginal d s (k + 1 + 1) D.beta (mu D)) := by ring
        _ ≤ D.beta * (C1 * Mg) := mul_le_mul hcoef hnu hnu0 hβ0.le
        _ = K := by rw [hK]; ring
    have hJ := wr13a_jensen P0 (u := u) (hint.const_mul _) hu0 hint_u
    refine hJ.trans (le_of_eq ?_)
    unfold poleNormalizer
    refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
    simp only [poleWeight, hu, neg_mul]
  have hCge : Real.exp K ≤ Real.exp (βp * C1 * Mg) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hββp (by linarith)) hMg)
  have hΦ0 : 0 < poleNormalizer d s (k + 2) D.beta (mu D) x t := lt_of_lt_of_le (Real.exp_pos _) hlow
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ hlow
    rw [Real.exp_neg]
    refine inv_anti₀ (Real.exp_pos _) (hCge.trans ?_)
    exact le_mul_of_one_le_right (Real.exp_pos _).le (Real.one_le_exp (by positivity))
  · have hA : pole D (k + 2) x t ≤ ENNReal.ofReal (Real.exp K) • P0 := by
      refine Measure.le_iff.2 fun S hS => ?_
      show ((ENNReal.ofReal (poleNormalizer d s (k + 2) D.beta (mu D) x t))⁻¹ •
        P0.withDensity fun Y => ENNReal.ofReal (poleWeight d s (k + 2) D.beta x t Y)) S ≤ _
      simp only [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hS]
      refine mul_le_mul' ?_ ?_
      · calc (ENNReal.ofReal (poleNormalizer d s (k + 2) D.beta (mu D) x t))⁻¹
            ≤ (ENNReal.ofReal (Real.exp (-K)))⁻¹ := ENNReal.inv_le_inv.2 (ENNReal.ofReal_le_ofReal hlow)
          _ = ENNReal.ofReal (Real.exp K) := by
              rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg, neg_neg]
      · calc ∫⁻ a in S, ENNReal.ofReal (poleWeight d s (k + 2) D.beta x t a) ∂P0
            ≤ ∫⁻ a in S, 1 ∂P0 := setLIntegral_mono' hS fun a _ =>
              ENNReal.ofReal_le_one.2 (wr13a_poleWeight_le_one hs0 hβ0.le ht.1 (k + 2) x a)
          _ = P0 S := by simp
    have hB := s81b_cavity_le_Q hs0 hconv hβ0.le k
    have hAB := s81b_smul_le_smul hA hB
    refine s81b_smul_mono hAB ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul hCge (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
      (Real.exp_pos _).le)
    have : D.beta * Mg ≤ βp * Mg := mul_le_mul_of_nonneg_right hββp hMg
    linarith

end HRS.Whole.S81b
