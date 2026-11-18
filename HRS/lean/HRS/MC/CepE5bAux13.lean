import HRS.MC.CepE5bAux12

/-!
# Packet CEPE5B, auxiliary 13: the `n`-step inequality for `E ∫ |G_n(Z)|²`
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE5b

open HRS HRS.MC.Cepa HRS.MC.CepE4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem e5b_trace_pointwise {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J) {n r : ℝ}
    (hn : 0 < n) (hr : 0 < r) (hr2 : r ≤ 1 / 2) (z : Ch N) :
    e5b_tr a N J n z ≤ (n * (8 * (N : ℝ) ^ 3 * r / (a * Real.pi))) * inner ℝ (z - e4_rho N) (e5b_G J n z) +
      (n * (16 * (N : ℝ) ^ 5 * r) + 2 * a * Real.pi ^ 2 * N / r ^ 2) := by
  have h := e5b_trace_final ha hJ hn hr hr2 z
  have h2 := mul_le_mul_of_nonneg_left h hn.le
  have e1 : n * ((1 / n) * ∑ i : Fin N, fderiv ℝ (fderiv ℝ (e5b_Pn a N J n)) z (e5b_e i) (e5b_e i)) =
      e5b_tr a N J n z := by
    unfold e5b_tr
    field_simp
  rw [e1] at h2
  refine h2.trans (le_of_eq ?_)
  unfold e5b_Q e5b_G
  field_simp
  ring

theorem e5b_F_pointwise {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (ρ z : Ch N) :
    ‖F z‖ ^ 2 ≤ (2 * ‖F 0‖ ^ 2 + 4 * (L : ℝ) ^ 2 * ‖ρ‖ ^ 2) + (8 * (L : ℝ) ^ 2) * ((1 / 2) * ‖z - ρ‖ ^ 2) := by
  have h1 := e4_lip_growth hF z
  have h2 : ‖F z‖ ^ 2 ≤ (‖F 0‖ + L * ‖z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : ‖z‖ ≤ ‖z - ρ‖ + ‖ρ‖ := by
    have := norm_le_norm_add_norm_sub' z ρ
    linarith
  have h4 : ‖z‖ ^ 2 ≤ (‖z - ρ‖ + ‖ρ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
  have hL : (0 : ℝ) ≤ L := L.2
  have h5 : (‖F 0‖ + L * ‖z‖) ^ 2 ≤ 2 * ‖F 0‖ ^ 2 + 2 * (L : ℝ) ^ 2 * ‖z‖ ^ 2 := by
    nlinarith [sq_nonneg (‖F 0‖ - L * ‖z‖)]
  have h6 : ‖z‖ ^ 2 ≤ 2 * ‖z - ρ‖ ^ 2 + 2 * ‖ρ‖ ^ 2 := by
    nlinarith [sq_nonneg (‖z - ρ‖ - ‖ρ‖)]
  have h7 : 2 * (L : ℝ) ^ 2 * ‖z‖ ^ 2 ≤ 2 * (L : ℝ) ^ 2 * (2 * ‖z - ρ‖ ^ 2 + 2 * ‖ρ‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h6 (by positivity)
  nlinarith

/-- **The `n`-step inequality.** -/
theorem e5b_step [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) {n : ℝ} (hn : 0 < n)
    {T σ' : ℝ} {Z : ℝ → Ω → Ch N} {A : Ω → ℝ}
    (S : E4Setup P ℱ N T σ' (cep_noise π W') Z A) (hT : 0 ≤ T)
    {z0 : Ω → Ch N} (hz0 : Measurable[ℱ 0] z0) {R : ℝ} (hR : ∀ ω, ‖z0 ω‖ ≤ R)
    (heq : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Z t ω = z0 ω +
      (∫ s in (0 : ℝ)..t, (-e5b_G J n (Z s ω) + F (Z s ω))) + σ' • cep_noise π W' t ω)
    {B1 M : ℝ}
    (hB1 : ∫ ω, (∫ s in (0 : ℝ)..T, inner ℝ (Z s ω - e4_rho N) (e5b_G J n (Z s ω))) ∂P ≤ B1)
    (hM : ∫ ω, (∫ s in (0 : ℝ)..T, (1 / 2) * ‖Z s ω - e4_rho N‖ ^ 2) ∂P ≤ M * T)
    {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 1 / 2) :
    ∫ ω, (∫ s in (0 : ℝ)..T, ‖e5b_G J n (Z s ω)‖ ^ 2) ∂P ≤
      2 * (∫ ω, e5b_Pn a N J n (z0 ω) ∂P + (a / N) * HRS.MC.CepE2.cepe2_npairs N * Real.log 2) +
      ((2 * ‖F 0‖ ^ 2 + 4 * (L : ℝ) ^ 2 * ‖e4_rho N‖ ^ 2) * T + 8 * (L : ℝ) ^ 2 * (M * T)) +
      σ' ^ 2 * ((n * (8 * (N : ℝ) ^ 3 * r / (a * Real.pi))) * B1 +
        (n * (16 * (N : ℝ) ^ 5 * r) + 2 * a * Real.pi ^ 2 * N / r ^ 2) * T) := by
  classical
  set ρ : Ch N := e4_rho N with hρ
  set G : Ch N → Ch N := e5b_G J n with hGdef
  set g : Ch N → ℝ := e5b_Pn a N J n with hg
  set cL : ℝ := (a / N) * HRS.MC.CepE2.cepe2_npairs N * Real.log 2 with hcL
  have hGc : Continuous G := e5b_G_cont hJ hn
  have hFc : Continuous F := hF.continuous
  have hGb : ∀ z, ‖G z‖ ≤ ‖G 0‖ + n * ‖z‖ := e5b_G_growth hJ hn
  have hFb : ∀ z, ‖F z‖ ≤ ‖F 0‖ + (L : ℝ) * ‖z‖ := e4_lip_growth hF
  have hLp : (0 : ℝ) ≤ L := L.2
  have qGG : E4Quad fun z => ‖G z‖ ^ 2 := e5b_quad_sqnorm hGc (norm_nonneg _) hn.le hGb
  have qFF : E4Quad fun z => ‖F z‖ ^ 2 := e5b_quad_sqnorm hFc (norm_nonneg _) hLp hFb
  have qGF : E4Quad fun z => inner ℝ (G z) (F z) := e5b_quad_inner hGc hFc qGG qFF
  have hTr0 := e5b_tr_nonneg ha hJ hn (N := N) (J := J)
  have hTr1 := e5b_tr_le ha hJ hn (N := N) (J := J)
  have qtr : E4Quad (e5b_tr a N J n) :=
    ⟨e5b_tr_cont ha hJ hn, n * N, 0, by positivity, le_rfl, fun z => by
      rw [abs_of_nonneg (hTr0 z)]
      have := hTr1 z
      simp only [zero_mul, add_zero]
      exact this⟩
  have qgG : E4Quad fun z => inner ℝ (z - ρ) (G z) :=
    ⟨e4_inner_cont hGc ρ, _, _, by positivity, by positivity, e4_inner_bound (norm_nonneg _) hn.le hGb ρ⟩
  have qgq : E4Quad fun z : Ch N => (1 / 2) * ‖z - ρ‖ ^ 2 :=
    ⟨continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2), ‖ρ‖ ^ 2, 1,
      by positivity, zero_le_one, e4_q_bound ρ⟩
  set cdr : ℝ := (1 / 2) * σ' ^ 2 with hcdr
  have qd : E4Quad fun z => (-1) * ‖G z‖ ^ 2 + 1 * inner ℝ (G z) (F z) + cdr * e5b_tr a N J n z :=
    ((qGG.const_mul (-1)).add (qGF.const_mul 1)).add (qtr.const_mul cdr)
  -- Itô
  have hBc : Continuous fun z => -G z + F z := hGc.neg.add hFc
  have hg2 : ContDiff ℝ 2 g := e5b_contDiff_Pn ha hJ hn
  have hgrad : ∀ x, ‖fderiv ℝ g x‖ ≤ ‖G 0‖ + n * ‖x‖ := by
    intro x
    have : fderiv ℝ g x = innerSL ℝ (G x) := by rw [hg, e5b_fderiv_Pn ha hJ hn]; rfl
    rw [this, innerSL_apply_norm]
    exact hGb x
  set c0 : ℝ := (a / N) * HRS.MC.CepE2.cepe2_npairs N * Real.log 2 +
      |cep_chamberPot a N (e4_rho N)| + n * ‖e4_rho N‖ ^ 2 with hc0
  have hc0p : 0 ≤ c0 := by
    have : 0 ≤ HRS.MC.CepE2.cepe2_npairs N := by unfold HRS.MC.CepE2.cepe2_npairs; positivity
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    positivity
  have hd : ∀ x, ((-1) * ‖G x‖ ^ 2 + 1 * inner ℝ (G x) (F x) + cdr * e5b_tr a N J n x) =
      fderiv ℝ g x (-G x + F x) + (1 / 2) * σ' ^ 2 *
        ∑ k : Fin N, fderiv ℝ (fderiv ℝ g) x (e5b_e k) (e5b_e k) := by
    intro x
    rw [hg, e5b_fderiv_apply ha hJ hn, inner_add_right, inner_neg_right, real_inner_self_eq_norm_sq]
    unfold e5b_tr
    rw [hcdr]
    ring
  obtain ⟨hint, hEq⟩ := e5b_ito_mean hW' hπ S hT hz0 hR (Bf := fun z => -G z + F z) hBc heq hg2
    (norm_nonneg _) hn.le hgrad hc0p hn.le (fun x => e5b_Pn_abs_le ha hJ hn x) qd hd hT le_rfl
  -- lower bound for `E g(Z_T)`
  have hlow : -cL ≤ ∫ ω, g (Z T ω) ∂P := by
    calc -cL = ∫ _ω, -cL ∂P := by simp
      _ ≤ _ := integral_mono (integrable_const _) hint fun ω => e5b_Pn_lower ha.le hJ hn (Z T ω)
  -- the linear identity
  have hlin := e5b_lin3 S hT le_rfl qGG qGF qtr (-1) 1 cdr
  -- the pointwise estimates
  have qsum : E4Quad fun z => (1 / 2) * ‖G z‖ ^ 2 + (1 / 2) * ‖F z‖ ^ 2 :=
    (qGG.const_mul (1 / 2)).add (qFF.const_mul (1 / 2))
  have hGF := e4Q_int_le S hT le_rfl qGF qsum (d := 0) (fun z => by
    have h := abs_real_inner_le_norm (G z) (F z)
    have := le_abs_self (inner ℝ (G z) (F z))
    nlinarith [sq_nonneg (‖G z‖ - ‖F z‖)])
  have hsum := e4Q_lin S hT le_rfl qGG qFF (1 / 2) (1 / 2)
  have hFF := e4Q_int_le S hT le_rfl qFF (qgq.const_mul (8 * (L : ℝ) ^ 2))
    (d := 2 * ‖F 0‖ ^ 2 + 4 * (L : ℝ) ^ 2 * ‖ρ‖ ^ 2) (fun z => by
      have := e5b_F_pointwise hF ρ z
      linarith)
  set K' : ℝ := n * (8 * (N : ℝ) ^ 3 * r / (a * Real.pi)) with hK'
  set dd : ℝ := n * (16 * (N : ℝ) ^ 5 * r) + 2 * a * Real.pi ^ 2 * N / r ^ 2 with hdd
  have hK'p : 0 ≤ K' := by positivity
  have htr := e4Q_int_le S hT le_rfl qtr (qgG.const_mul K') (d := dd)
    (fun z => e5b_trace_pointwise ha hJ hn hr hr2 z)
  -- extract the scalar constants
  have e1 : ∫ ω, (∫ s in (0 : ℝ)..T, K' * inner ℝ (Z s ω - ρ) (G (Z s ω))) ∂P =
      K' * ∫ ω, (∫ s in (0 : ℝ)..T, inner ℝ (Z s ω - ρ) (G (Z s ω))) ∂P := by
    simp only [intervalIntegral.integral_const_mul, integral_const_mul]
  have e2 : ∫ ω, (∫ s in (0 : ℝ)..T, (8 * (L : ℝ) ^ 2) * ((1 / 2) * ‖Z s ω - ρ‖ ^ 2)) ∂P =
      (8 * (L : ℝ) ^ 2) * ∫ ω, (∫ s in (0 : ℝ)..T, (1 / 2) * ‖Z s ω - ρ‖ ^ 2) ∂P := by
    simp only [intervalIntegral.integral_const_mul, integral_const_mul]
  rw [e1] at htr
  rw [e2] at hFF
  simp only [zero_mul, add_zero] at hGF
  rw [hsum] at hGF
  -- combine
  set IG : ℝ := ∫ ω, (∫ s in (0 : ℝ)..T, ‖G (Z s ω)‖ ^ 2) ∂P with hIG
  set IF : ℝ := ∫ ω, (∫ s in (0 : ℝ)..T, ‖F (Z s ω)‖ ^ 2) ∂P with hIF
  set IGF : ℝ := ∫ ω, (∫ s in (0 : ℝ)..T, inner ℝ (G (Z s ω)) (F (Z s ω))) ∂P with hIGF
  set Itr : ℝ := ∫ ω, (∫ s in (0 : ℝ)..T, e5b_tr a N J n (Z s ω)) ∂P with hItr
  set IgG : ℝ := ∫ ω, (∫ s in (0 : ℝ)..T, inner ℝ (Z s ω - ρ) (G (Z s ω))) ∂P with hIgG
  set Iq : ℝ := ∫ ω, (∫ s in (0 : ℝ)..T, (1 / 2) * ‖Z s ω - ρ‖ ^ 2) ∂P with hIq
  have hdf : ∫ ω, (∫ s in (0 : ℝ)..T, ((-1) * ‖G (Z s ω)‖ ^ 2 + 1 * inner ℝ (G (Z s ω)) (F (Z s ω)) +
      cdr * e5b_tr a N J n (Z s ω))) ∂P = (-1) * IG + 1 * IGF + cdr * Itr := hlin
  rw [hdf] at hEq
  have hIq : 8 * (L : ℝ) ^ 2 * Iq ≤ 8 * (L : ℝ) ^ 2 * (M * T) :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  have hK : K' * IgG ≤ K' * B1 := mul_le_mul_of_nonneg_left hB1 hK'p
  have hItr : Itr ≤ K' * B1 + dd * T := by linarith
  have hσ : 0 ≤ σ' ^ 2 := sq_nonneg σ'
  have hItr2 : σ' ^ 2 * Itr ≤ σ' ^ 2 * (K' * B1 + dd * T) := mul_le_mul_of_nonneg_left hItr hσ
  have hcdr' : cdr * Itr = (1 / 2) * (σ' ^ 2 * Itr) := by rw [hcdr]; ring
  have hF1 : IF ≤ (2 * ‖F 0‖ ^ 2 + 4 * (L : ℝ) ^ 2 * ‖ρ‖ ^ 2) * T + 8 * (L : ℝ) ^ 2 * (M * T) := by
    linarith
  have hGF' : IGF ≤ (1 / 2) * IG + (1 / 2) * IF := by linarith
  linarith [hEq, hlow, hGF', hF1, hItr2, hcdr']

end HRS.MC.CepE5b
