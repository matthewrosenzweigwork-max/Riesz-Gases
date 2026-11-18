import HRS.Commutator.Torus.TUNITBAux1

/-!
# T-UNIT-b helpers, part 2: `remainder_bound_T`

Prefix `tunitb_`.  Torus analogue of `UREM.urem_main` (`(5.remainderbound)`): the pairing
`𝒞_{g_>}(v,ν) = pairT (commKernel ∇g_> v) X ρ` is split into the particle–particle term (Lemma 3.1,
`kernel_remainder_T`, and `energy_control_T (b)`), the mixed term (Hölder, `kernel_remainder_Lq_T`, `energy_control_T (a)`)
and the density–density term (`inhomogeneous_T_proof`, `energy_control_T (c)`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad

variable {d : ℕ} {s η : ℝ}

/-- Hölder for the one-point convolution on the torus, with integrability. -/
theorem tunitb_holder_norm {p q : ℝ≥0∞} (hpq : p⁻¹ + q⁻¹ = 1) (f ρ : Torus d → ℝ)
    (hfq : MemLp f q volume) (hρp : MemLp ρ p volume) (z : Torus d) :
    Integrable (fun y => f (z - y) * ρ y) ∧
    ∫ y, ‖f (z - y) * ρ y‖ ≤ (eLpNorm f q volume).toReal * (eLpNorm ρ p volume).toReal := by
  have hT1 : ENNReal.HolderTriple q p 1 :=
    ENNReal.holderConjugate_iff.2 (by rw [add_comm]; exact hpq)
  have hmp : MeasurePreserving (fun y : Torus d => z - y) volume volume :=
    (volume : Measure (Torus d)).measurePreserving_sub_left z
  have hfz : eLpNorm (fun y => f (z - y)) q volume = eLpNorm f q volume :=
    eLpNorm_comp_measurePreserving hfq.aestronglyMeasurable hmp
  have hfzm : AEStronglyMeasurable (fun y => f (z - y)) volume :=
    (hfq.aestronglyMeasurable).comp_measurePreserving hmp
  have hH : eLpNorm (fun y => f (z - y) * ρ y) 1 volume ≤
      eLpNorm (fun y => f (z - y)) q volume * eLpNorm ρ p volume := by
    have := MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm (p := q) (q := p) (r := 1)
      (fun a b : ℝ => a * b) (1 : ℝ≥0∞) (continuous_mul) hfzm hρp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simp [enorm_mul])
    simpa using this
  have hfin1 : eLpNorm (fun y => f (z - y)) q volume ≠ ⊤ := by
    rw [hfz]; exact (hfq.eLpNorm_lt_top).ne
  have hfin2 : eLpNorm ρ p volume ≠ ⊤ := (hρp.eLpNorm_lt_top).ne
  have hmeas : AEStronglyMeasurable (fun y => f (z - y) * ρ y) volume :=
    hfzm.mul hρp.aestronglyMeasurable
  have hlt : eLpNorm (fun y => f (z - y) * ρ y) 1 volume < ⊤ :=
    lt_of_le_of_lt hH (ENNReal.mul_lt_top hfin1.lt_top hfin2.lt_top)
  refine ⟨memLp_one_iff_integrable.1 hlt, ?_⟩
  have hstep2 : ∫ y, ‖f (z - y) * ρ y‖ = (eLpNorm (fun y => f (z - y) * ρ y) 1 volume).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm hmeas, integral_norm_eq_lintegral_enorm hmeas]
  have hstep3 : (eLpNorm (fun y => f (z - y) * ρ y) 1 volume).toReal ≤
      (eLpNorm (fun y => f (z - y)) q volume * eLpNorm ρ p volume).toReal := by
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top hfin1 hfin2) ?_
    simpa using hH
  rw [hfz] at hstep3
  rw [ENNReal.toReal_mul] at hstep3
  linarith

/-- `q⁻¹ = 1 - p⁻¹` on the reals. -/
theorem tunitb_qinv_toReal {p q : ℝ≥0∞} (hpq : p⁻¹ + q⁻¹ = 1) :
    (q⁻¹).toReal = 1 - (p⁻¹).toReal := by
  have h1 : p⁻¹ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hpq ▸ le_self_add)
  have h2 : q⁻¹ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hpq ▸ le_add_self)
  have := congrArg ENNReal.toReal hpq
  rw [ENNReal.toReal_add h1 h2] at this
  rw [ENNReal.toReal_one] at this
  linarith

/-- The pointwise bound of the commutator kernel by `L · |x-y|·|F(x-y)|`. -/
theorem tunitb_comm_pt {L : ℝ} (hL : 0 ≤ L) {v : Torus d → Euc d} (hv : IsLipschitzVF L v)
    (G : Torus d → Euc d) (x y : Torus d) :
    ‖commKernel G v x y‖ ≤ L * (KernelGrad.tdist (x - y) 0 * ‖G (x - y)‖) := by
  have hnn : 0 ≤ L * (KernelGrad.tdist (x - y) 0 * ‖G (x - y)‖) :=
    mul_nonneg hL (mul_nonneg (KernelGrad.tdist_nonneg _ _) (norm_nonneg _))
  unfold commKernel
  by_cases hxy : x = y
  · rw [if_pos hxy, norm_zero]; exact hnn
  · rw [if_neg hxy]
    have h1 : ‖inner ℝ (v x - v y) (G (x - y))‖ ≤ ‖v x - v y‖ * ‖G (x - y)‖ := norm_inner_le_norm _ _
    have h2 : ‖v x - v y‖ ≤ L * KernelGrad.tdist (x - y) 0 := by
      have := hv x y
      rwa [KernelGrad.tdist_eq_sub_zero] at this
    calc ‖inner ℝ (v x - v y) (G (x - y))‖ ≤ ‖v x - v y‖ * ‖G (x - y)‖ := h1
      _ ≤ (L * KernelGrad.tdist (x - y) 0) * ‖G (x - y)‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = L * (KernelGrad.tdist (x - y) 0 * ‖G (x - y)‖) := by ring

/-- `tScale · perio f_η = f^𝕋_η + K_s η^{d-s}`. -/
theorem tunitb_tScale_perio (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) (z : Torus d) :
    tScale s * perio (Whole.fTrunc s η : Euc d → ℝ) z = fTorus s η z + ten2K d s * η ^ ((d : ℝ) - s) := by
  have hm := tpos_integral_perio_fTrunc (d := d) hs0 hsd hη
  unfold fTorus
  rw [hm]
  unfold ten2K
  ring

/-- Upper bound for the particle sum of `f^𝕋_η` by `2 Q_η`. -/
theorem tunitb_S_le (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) (hη1 : η ≤ 1)
    {ρ : Torus d → ℝ} (hρ : BddDensityT ρ) {N : ℕ} (hN : 1 ≤ N) (X : Config d N) {Q : ℝ}
    (hB : kerEnergyT (gTorus s η) (chargeT X ρ) +
        (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTorus s η (X i - X j) +
        ∫ x, ∫ y, fTorus s η (x - y) * ρ x * ρ y ≤ 2 * Q) :
    (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTorus s η (X i - X j) ≤ 2 * Q := by
  obtain ⟨cb, hcb0, hcb⟩ := tpos_coef_bounds hd hs0 hsd
  have hI := ten2_quad_nonneg hd hs0 hsd (cb := cb) (η := η)
    (fun k hk => (hcb η hη hη1 k hk).2.2) hcb0 hη hρ
  have hk := ten2_kerEnergy_nonneg hd hs0 hsd hη hN X hρ
  linarith

/-- Particle–particle term. -/
theorem tunitb_particle_term (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ Cr : ℝ, 0 < Cr ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ {N : ℕ} (X : Config d N), 1 ≤ N →
      X ∉ collisionSet d N → ∀ (v : Torus d → Euc d) (L : ℝ), 0 ≤ L → IsLipschitzVF L v →
      |(1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, commKernel (ghiForceT s η) v (X i) (X j)| ≤
        L * Cr * ((1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTorus s η (X i - X j) +
          ten2K d s * η ^ ((d : ℝ) - s)) := by
  obtain ⟨Cr, hCr, hrem⟩ := kernel_remainder_T hd hs0 hsd
  refine ⟨Cr, hCr, fun η hη hη1 N X hN hX v L hL hv => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set M := ten2K d s * η ^ ((d : ℝ) - s) with hM
  have hM0 : 0 ≤ M := mul_nonneg (ten2K_nonneg hd hs0 hsd) (Real.rpow_nonneg hη.le _)
  set S : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, fTorus s η (X i - X j) with hS
  have hkb : ∀ i j : Fin N, j ≠ i →
      ‖commKernel (ghiForceT s η) v (X i) (X j)‖ ≤ L * Cr * (fTorus s η (X i - X j) + M) := by
    intro i j hji
    have hne : X i - X j ≠ 0 := sub_ne_zero.2 (fun h => hX ⟨i, j, fun e => hji e.symm, h⟩)
    have h1 := tunitb_comm_pt hL hv (ghiForceT s η) (X i) (X j)
    have h2 := hrem η hη hη1 (X i - X j) hne
    have h3 := tunitb_tScale_perio hs0 hsd hη (X i - X j)
    calc ‖commKernel (ghiForceT s η) v (X i) (X j)‖
        ≤ L * (KernelGrad.tdist (X i - X j) 0 * ‖ghiForceT s η (X i - X j)‖) := h1
      _ ≤ L * (Cr * (tScale s * perio (Whole.fTrunc s η : Euc d → ℝ) (X i - X j))) :=
          mul_le_mul_of_nonneg_left (by linarith) hL
      _ = L * Cr * (fTorus s η (X i - X j) + M) := by rw [h3]; ring
  have hsum : |∑ i, ∑ j ∈ Finset.univ.erase i, commKernel (ghiForceT s η) v (X i) (X j)| ≤
      L * Cr * (S + (N : ℝ) * ((N : ℝ) - 1) * M) := by
    have hcard : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, M = ((N : ℝ) - 1) * M := by
      intro i
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hN, Nat.cast_one]
    have e1 : L * Cr * (S + (N : ℝ) * ((N : ℝ) - 1) * M) =
        ∑ i, ∑ j ∈ Finset.univ.erase i, L * Cr * (fTorus s η (X i - X j) + M) := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib, hcard]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hS]
      ring
    rw [e1]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    have := hkb i j (Finset.ne_of_mem_erase hj)
    simpa [Real.norm_eq_abs] using this
  have hN1 : (N : ℝ) * ((N : ℝ) - 1) ≤ (N : ℝ) ^ 2 := by nlinarith
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 2)]
  have hLC : 0 ≤ L * Cr := mul_nonneg hL hCr.le
  calc 1 / (N : ℝ) ^ 2 * |∑ i, ∑ j ∈ Finset.univ.erase i, commKernel (ghiForceT s η) v (X i) (X j)|
      ≤ 1 / (N : ℝ) ^ 2 * (L * Cr * (S + (N : ℝ) * ((N : ℝ) - 1) * M)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 1 / (N : ℝ) ^ 2 * (L * Cr * (S + (N : ℝ) ^ 2 * M)) := by
        gcongr
    _ = L * Cr * (1 / (N : ℝ) ^ 2 * S + M) := by
        field_simp

/-- Mixed term: `|∫ K(z,y) ρ(y) dy| ≤ L · C_q · ‖ρ‖_p η^{d(1-1/p)-s}`. -/
theorem tunitb_cross_term (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (p q : ℝ≥0∞)
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    ∃ Cq : ℝ, 0 < Cq ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ ρ : Torus d → ℝ, BddDensityT ρ →
      ∀ (v : Torus d → Euc d) (L : ℝ), 0 ≤ L → IsLipschitzVF L v → ∀ z : Torus d,
      |∫ y, commKernel (ghiForceT s η) v z y * ρ y| ≤
        L * (Cq * (normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s))) := by
  obtain ⟨Cq, hCq, hLq⟩ := kernel_remainder_Lq_T hd hs0 hsd p q hp hpq
  refine ⟨Cq, hCq, fun η hη hη1 ρ hρ v L hL hv z => ?_⟩
  obtain ⟨hWq, hWn⟩ := hLq η hη hη1
  obtain ⟨B, hB⟩ := hρ.bdd
  have hρp : MemLp ρ p volume :=
    MemLp.of_bound hρ.measurable.aestronglyMeasurable B
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hB x)
  set W : Torus d → ℝ := fun x => KernelGrad.tdist x 0 * ‖ghiForceT s η x‖ with hW
  obtain ⟨hint, hhol⟩ := tunitb_holder_norm hpq W ρ hWq hρp z
  have hexp : (d : ℝ) * (q⁻¹).toReal - s = (d : ℝ) * (1 - (p⁻¹).toReal) - s := by
    rw [tunitb_qinv_toReal hpq]
  have hWn' : (eLpNorm W q volume).toReal ≤ Cq * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := by
    rw [← hexp]
    have hpos : 0 ≤ Cq * η ^ ((d : ℝ) * (q⁻¹).toReal - s) :=
      mul_nonneg hCq.le (Real.rpow_nonneg hη.le _)
    calc (eLpNorm W q volume).toReal ≤ (ENNReal.ofReal (Cq * η ^ ((d : ℝ) * (q⁻¹).toReal - s))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hWn
      _ = _ := ENNReal.toReal_ofReal hpos
  have hLn : 0 ≤ L := hL
  have hmaj : Integrable (fun y => L * ‖W (z - y) * ρ y‖) := hint.norm.const_mul L
  have hbd : ∀ y, ‖commKernel (ghiForceT s η) v z y * ρ y‖ ≤ L * ‖W (z - y) * ρ y‖ := by
    intro y
    have h1 := tunitb_comm_pt hL hv (ghiForceT s η) z y
    have hW0 : 0 ≤ W (z - y) := mul_nonneg (KernelGrad.tdist_nonneg _ _) (norm_nonneg _)
    rw [norm_mul, norm_mul, Real.norm_of_nonneg hW0]
    calc ‖commKernel (ghiForceT s η) v z y‖ * ‖ρ y‖ ≤ (L * W (z - y)) * ‖ρ y‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = L * (W (z - y) * ‖ρ y‖) := by ring
  have hn0 : 0 ≤ (eLpNorm ρ p volume).toReal := ENNReal.toReal_nonneg
  calc |∫ y, commKernel (ghiForceT s η) v z y * ρ y|
      = ‖∫ y, commKernel (ghiForceT s η) v z y * ρ y‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, L * ‖W (z - y) * ρ y‖ := norm_integral_le_of_norm_le hmaj (ae_of_all _ hbd)
    _ = L * ∫ y, ‖W (z - y) * ρ y‖ := integral_const_mul _ _
    _ ≤ L * ((eLpNorm W q volume).toReal * (eLpNorm ρ p volume).toReal) :=
        mul_le_mul_of_nonneg_left hhol hL
    _ ≤ L * ((Cq * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s)) * (eLpNorm ρ p volume).toReal) := by
        gcongr
    _ = L * (Cq * (normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s))) := by
        unfold normT; ring

theorem tunitb_rem_main (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ η₀ C : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧ 0 < C ∧ ∀ p : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp → ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ ρ : Torus d → ℝ, BddDensityT ρ → ∀ (N : ℕ) (X : Config d N), 1 ≤ N → X ∉ collisionSet d N →
      ∀ (v : Torus d → Euc d) (K : ℝ), TorusSubTransport d s v K →
        |CcommT (ghiForceT s η) v (chargeT X ρ)| ≤ C * K * scaleQT s Cp p η X ρ := by
  obtain ⟨Cr, hCr, hpart⟩ := tunitb_particle_term hd hs0 hsd
  obtain ⟨Ci, hCi, hinh⟩ := inhomogeneous_T_proof hd hs0 hsd
  obtain ⟨Cb, η₀, hCb, hη₀, hη₀1, hEC⟩ := energy_control_T hd hs0 hsd
  have hK2 : 0 < 2 + ten2K d s := by have := ten2K_nonneg hd hs0 hsd; linarith
  refine ⟨η₀, Cr * (2 + ten2K d s) + 2 + Ci * Cb, hη₀, hη₀1, by positivity, fun p hp => ?_⟩
  have hp1 : 1 ≤ p := (tunit_one_lt_p hd hs0 hsd hp).le
  have hpp : p.HolderConjugate (ENNReal.conjExponent p) := ENNReal.HolderConjugate.conjExponent hp1
  have hpq : p⁻¹ + (ENNReal.conjExponent p)⁻¹ = 1 := hpp.inv_add_inv_eq_one
  obtain ⟨Cq, hCq, hcross⟩ := tunitb_cross_term hd hs0 hsd p (ENNReal.conjExponent p) hp hpq
  obtain ⟨Cp0, hCp0, hE⟩ := hEC p hp
  refine ⟨Cp0 + Cq, by positivity, fun Cp hCp η hη hηη₀ ρ hρ N X hN hX v K hv => ?_⟩
  have hη1 : η ≤ 1 := hηη₀.trans hη₀1
  have hCpge : Cp0 ≤ Cp := by linarith
  obtain ⟨hA, hB, hC, -⟩ := hE Cp hCpge η hη hηη₀ ρ hρ N X hN hX
  obtain ⟨hA0, -, -, -⟩ := hE Cp0 le_rfl η hη hηη₀ ρ hρ N X hN hX
  set Q := scaleQT s Cp p η X ρ with hQ
  set T : ℝ := η ^ (-s) / (N : ℝ) + normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) with hT
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hnp1 : 1 ≤ normT p ρ := ten2_normT_ge_one hp1 hρ
  have hηe : 0 ≤ η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := Real.rpow_nonneg hη.le _
  have hηs : 0 ≤ η ^ (-s) / (N : ℝ) := by
    have : 0 ≤ η ^ (-s) := Real.rpow_nonneg hη.le _
    positivity
  have hT0 : 0 ≤ T := by
    have : 0 ≤ normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := mul_nonneg (by linarith) hηe
    linarith
  have hQ0 : 0 ≤ Q := tunitb_Q_nonneg hp1 hη hN hA hρ
  -- `Q ≥ (1 + Cq) T`
  have hQT : Cq * T ≤ Q := by
    have e : scaleQT s Cp p η X ρ = scaleQT s Cp0 p η X ρ + (Cp - Cp0) * T := by
      unfold scaleQT; rw [hT]; ring
    have h1 : (Cp - Cp0) * T ≥ Cq * T := mul_le_mul_of_nonneg_right (by linarith) hT0
    rw [hQ]
    linarith
  have hnT : Cq * (normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s)) ≤ Q := by
    have : Cq * (normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s)) ≤ Cq * T :=
      mul_le_mul_of_nonneg_left (by linarith) hCq.le
    linarith
  have hv0 := hv
  obtain ⟨L, F, hL0, hF0, hLip, -, hLF⟩ := hv0
  have hv' : TorusSubTransport d s v K := hv
  have hLK : L ≤ K := by linarith
  have hK0 : 0 ≤ K := by linarith
  -- pairing formula
  have hG := tunit_full_good hd hs0 hsd hρ hL0 hLip
  have hGglo := tunit_glo_good hd hs0 hsd hη hρ hL0 hLip
  have hGg : TDecGood ρ (commKernel (ghiForceT s η) v) :=
    (hG.sub hGglo).congr' (fun x y => by rw [tunit_commKer_split_gh s η v x y]; ring)
  have hid : CcommT (ghiForceT s η) v (chargeT X ρ) = pairT (commKernel (ghiForceT s η) v) X ρ := by
    unfold CcommT
    rw [tunit_pair2_formula hρ hN X hGg,
      tunit_pairT_formula X hGg (fun x => tunit_commKer_diag _ _ x)]
  rw [hid]
  unfold pairT
  -- (A)
  have hSle := tunitb_S_le hd hs0 hsd hη hη1 hρ hN X hB
  have hM0 : 0 ≤ ten2K d s * η ^ ((d : ℝ) - s) :=
    mul_nonneg (ten2K_nonneg hd hs0 hsd) (Real.rpow_nonneg hη.le _)
  have hηQ : η ^ ((d : ℝ) - s) ≤ Q := by
    have h1 : η ^ ((d : ℝ) - s) ≤ η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) :=
      Real.rpow_le_rpow_of_exponent_ge hη hη1 (by
        have hpinv0 : 0 ≤ (p⁻¹).toReal := ENNReal.toReal_nonneg
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        nlinarith)
    have h2 : η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) ≤
        normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := by
      calc _ = 1 * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hnp1 hηe
    linarith
  have hMQ : ten2K d s * η ^ ((d : ℝ) - s) ≤ ten2K d s * Q :=
    mul_le_mul_of_nonneg_left hηQ (ten2K_nonneg hd hs0 hsd)
  have hAb := hpart η hη hη1 X hN hX v L hL0 hLip
  have hA' : |(1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, commKernel (ghiForceT s η) v (X i) (X j)| ≤
      K * (Cr * ((2 + ten2K d s) * Q)) := by
    refine hAb.trans ?_
    have e1 : (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTorus s η (X i - X j) +
        ten2K d s * η ^ ((d : ℝ) - s) ≤ (2 + ten2K d s) * Q := by nlinarith
    calc L * Cr * ((1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTorus s η (X i - X j) +
          ten2K d s * η ^ ((d : ℝ) - s)) ≤ L * Cr * ((2 + ten2K d s) * Q) :=
          mul_le_mul_of_nonneg_left e1 (by positivity)
      _ ≤ K * Cr * ((2 + ten2K d s) * Q) := by gcongr
      _ = K * (Cr * ((2 + ten2K d s) * Q)) := by ring
  -- (B)
  have hBi : ∀ i, |∫ y, commKernel (ghiForceT s η) v (X i) y * ρ y| ≤ K * Q := by
    intro i
    refine (hcross η hη hη1 ρ hρ v L hL0 hLip (X i)).trans ?_
    calc L * (Cq * (normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s))) ≤ L * Q :=
          mul_le_mul_of_nonneg_left hnT hL0
      _ ≤ K * Q := mul_le_mul_of_nonneg_right hLK hQ0
  have hB' : |(2 / (N : ℝ)) * ∑ i, ∫ y, commKernel (ghiForceT s η) v (X i) y * ρ y| ≤ 2 * (K * Q) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / N)]
    have hsum := (Finset.abs_sum_le_sum_abs (fun i => ∫ y, commKernel (ghiForceT s η) v (X i) y * ρ y)
      Finset.univ).trans (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hBi i)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    calc 2 / (N : ℝ) * |∑ i, ∫ y, commKernel (ghiForceT s η) v (X i) y * ρ y|
        ≤ 2 / (N : ℝ) * ((N : ℝ) * (K * Q)) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 2 * (K * Q) := by field_simp
  -- (C)
  have hρ2 : MemLp ρ 2 volume := by
    obtain ⟨B, hB⟩ := hρ.bdd
    exact MemLp.of_bound hρ.measurable.aestronglyMeasurable B
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hB x)
  have hC' : |∫ x, ∫ y, commKernel (ghiForceT s η) v x y * ρ x * ρ y| ≤ Ci * K * (Cb * Q) := by
    have h3 := hinh η hη hη1 v K hv' ρ hρ2
    change |CcommFunT (ghiForceT s η) v ρ| ≤ _
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity)]
    calc ENNReal.ofReal |CcommFunT (ghiForceT s η) v ρ|
        ≤ ENNReal.ofReal (Ci * K) *
            (ENNReal.ofReal (η ^ (-s)) * sobSqT η (-Whole.alphaE d s) (fun k => Torus.fcoef ρ k)) := h3
      _ ≤ ENNReal.ofReal (Ci * K) * ENNReal.ofReal (Cb * Q) := by gcongr
      _ = ENNReal.ofReal (Ci * K * (Cb * Q)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  -- assemble
  have a1 := abs_le.1 hA'
  have a2 := abs_le.1 hB'
  have a3 := abs_le.1 hC'
  have e3 : Ci * K * (Cb * Q) = Ci * Cb * K * Q := by ring
  have e4 : (Cr * (2 + ten2K d s) + 2 + Ci * Cb) * K * Q =
      K * (Cr * ((2 + ten2K d s) * Q)) + 2 * (K * Q) + Ci * K * (Cb * Q) := by ring
  rw [e4]
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]

end HRS.Commutator.TorusNote
