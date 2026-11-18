import HRS.Whole.Q09BAux1
import HRS.Whole.Q09BAux3

/-!
# Packet Q09-B, part 4: glue between `RdStanding` and the abstract Itô moment bound
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

namespace HRS.Whole.Q09B

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-! ### Data of the selected flows -/

theorem q09b_flow_data {Ω : Type} [MeasurableSpace Ω] {N : ℕ} {P : Measure Ω}
    {D : WholeDyn d} {T : ℝ} {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → EucConfig d N} (h : SelectedFlowRd P D T X₀ W X) :
    (∀ᵐ ζ ∂P, X 0 ζ = X₀ ζ) ∧
    (∀ᵐ ζ ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      (∀ i, IntegrableOn (fun s : ℝ => particleDriftW D (X (Real.toNNReal s) ζ) i)
        (Set.Icc 0 (t : ℝ))) ∧
      ∀ i, X t ζ i = X 0 ζ i +
        (∫ s in Set.Icc (0 : ℝ) t, particleDriftW D (X (Real.toNNReal s) ζ) i) +
        Real.sqrt (2 * D.invβ) • (W t ζ i - W 0 ζ i)) ∧
    (∀ᵐ ζ ∂P, ∀ i, Continuous fun t => X t ζ i) ∧
    (∀ t : ℝ≥0, Measurable (X t)) := by
  rcases h.flow with ⟨h1, -⟩ | ⟨-, -, -, -, h1⟩ | ⟨-, -, -, -, h1⟩
  · exact ⟨h1.init, h1.eqn, h1.cont, h1.adapted⟩
  · exact ⟨h1.toContact.init, h1.toContact.eqn, h1.toContact.cont, h1.toContact.adapted⟩
  · exact ⟨h1.init, h1.eqn, h1.cont, h1.adapted⟩

theorem q09b_measurable_rkg (s : ℝ) : Measurable (rieszKernelGrad d s) := by
  unfold rieszKernelGrad gradient
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp
    (measurable_fderiv ℝ _)

theorem q09b_measurable_driftVec (D : WholeDyn d) (hV : Measurable (gradient D.V)) {N : ℕ} :
    Measurable (fun x : EucConfig d N => fun i => particleDriftW D x i) := by
  refine measurable_pi_iff.2 fun i => ?_
  have hsum : Measurable fun x : EucConfig d N =>
      ∑ j ∈ Finset.univ.erase i, Torus.matVec D.M (rieszKernelGrad d D.s (x i - x j)) := by
    refine Finset.measurable_sum _ fun j _ => ?_
    exact (LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin D.M)).measurable.comp
      ((q09b_measurable_rkg D.s).comp ((measurable_pi_apply i).sub (measurable_pi_apply j)))
  have h2 : Measurable fun x : EucConfig d N => gradient D.V (x i) :=
    hV.comp (measurable_pi_apply i)
  unfold particleDriftW
  exact (hsum.const_smul ((1 : ℝ) / N)).sub h2

theorem q09b_measurable_kernel (s : ℝ) : Measurable (rieszKernel d s) := by
  unfold rieszKernel
  by_cases h : s = 0
  · simp only [h, ite_true]
    exact (Real.measurable_log.comp measurable_norm).neg
  · simp only [h, ite_false]
    exact measurable_norm.pow_const _

theorem q09b_measurable_u (s Mn : ℝ) {N : ℕ} : Measurable (q09b_u d s Mn N) := by
  unfold q09b_u
  by_cases hs : s = 0
  · simp only [hs, ite_true]
    exact measurable_const
  · simp only [hs, ite_false]
    refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
    refine Finset.measurable_sum _ fun j _ => ?_
    exact (q09b_measurable_kernel s).comp ((measurable_pi_apply i).sub (measurable_pi_apply j))

theorem q09b_measurable_init {Ω : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ} {P : Measure Ω}
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hF : IsWholeFilteredSolution P ℱ W' W X) (s : ℝ) : Measurable[ℱ s] (X 0) := by
  rcases le_or_gt 0 s with hs | hs
  · exact (hF.adapted 0).mono (ℱ.mono (by simpa using hs)) le_rfl
  · have h := hF.progressive.adapted s
    have e : ofNNRealTime X s = X 0 := by
      funext z
      simp [ofNNRealTime_apply, Real.toNNReal_of_nonpos hs.le]
    rw [e] at h
    exact h

theorem q09b_grad_bound {N : ℕ} (hN : 0 < N) (x : EucConfig d N) :
    ‖fderiv ℝ (q09b_g d N) x‖ ≤ 1 * (1 + q09b_g d N x) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine ContinuousLinearMap.opNorm_le_bound _ (by have := q09b_g_nonneg d N x; linarith)
    fun h => ?_
  rw [q09b_fderiv_g, Real.norm_eq_abs]
  have hi : ∀ i, |2 * inner ℝ (x i) (h i)| ≤ (1 + ‖x i‖ ^ 2) * ‖h‖ := by
    intro i
    have h1 : |inner ℝ (x i) (h i)| ≤ ‖x i‖ * ‖h i‖ := abs_real_inner_le_norm _ _
    have h2 : ‖h i‖ ≤ ‖h‖ := norm_le_pi_norm h i
    rw [abs_mul, abs_two]
    calc 2 * |inner ℝ (x i) (h i)| ≤ 2 * (‖x i‖ * ‖h‖) := by
          have : ‖x i‖ * ‖h i‖ ≤ ‖x i‖ * ‖h‖ := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
          linarith
      _ ≤ (1 + ‖x i‖ ^ 2) * ‖h‖ := by
          nlinarith [sq_nonneg (‖x i‖ - 1), norm_nonneg h]
  calc |(N : ℝ)⁻¹ * ∑ i, 2 * inner ℝ (x i) (h i)|
      = (N : ℝ)⁻¹ * |∑ i, 2 * inner ℝ (x i) (h i)| := by
        rw [abs_mul, abs_of_pos (inv_pos.2 hNpos)]
    _ ≤ (N : ℝ)⁻¹ * ∑ i, (1 + ‖x i‖ ^ 2) * ‖h‖ :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => hi i)) (inv_nonneg.2 hNpos.le)
    _ = 1 * (1 + q09b_g d N x) * ‖h‖ := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib]
        simp only [q09b_g, q09b_sl, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_one]
        field_simp

theorem q09b_Lam_nonneg (S : WholeMainData d) {r : ℕ} {Λ : ℝ} (h : MeanFieldRegularityRd S r Λ) :
    0 ≤ Λ := by
  obtain ⟨hmem, hfin, hΛ⟩ := (h.regular 1 le_rfl).1 0 ⟨le_rfl, S.hT.le⟩
  have hcb : 0 ≤ cbNorm r (S.ρ 1 0) :=
    Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have := ENNReal.toReal_nonneg (a := weightedSupE r ((d : ℝ) + 3) (S.ρ 1 0))
  linarith

theorem q09b_rho_le (S : WholeMainData d) {r : ℕ} {Λ : ℝ} (h : MeanFieldRegularityRd S r Λ)
    {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) : ∀ x, S.ρ N t x ≤ Λ := by
  obtain ⟨hmem, hfin, hΛ⟩ := (h.regular N hN).1 t ht
  exact Q09A.rho_le_of_cbNorm hmem ENNReal.toReal_nonneg hΛ

theorem q09b_huE (S : WholeMainData d) (R : ∀ N, RealizationRd d N) {MB Λ ΛV G₀ m20 C₀ : ℝ}
    {𝔈 : ℕ → ℝ} {r mV : ℕ} (h : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {Ē : ℝ}
    (hĒ : ∀ N : ℕ, 1 ≤ N → 𝔈 N ≤ Ē) (hMB : 0 ≤ MB) {N : ℕ} (hN : 1 ≤ N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) S.T) :
    ∫⁻ ζ, ENNReal.ofReal (q09b_u d S.s (MB * d) N ((R N).X (Real.toNNReal t) ζ)) ∂(R N).P ≤
      ENNReal.ofReal (2 * (MB * d) * S.s * Ē + 2 * (MB * d) * S.s * (Λ * q09b_I d S.s + 1)) := by
  by_cases hs : S.s = 0
  · have : ∀ x : EucConfig d N, q09b_u d S.s (MB * d) N x = 0 := fun x => by simp [q09b_u, hs]
    simp [this]
  · have hspos : 0 < S.s := lt_of_le_of_ne S.hs0 (Ne.symm hs)
    have hN0 : 0 < N := hN
    have hΛ := q09b_Lam_nonneg S h.mean_field
    have hρprob := (h.mean_field.solution N hN).density t ht
    have hρΛ := q09b_rho_le S h.mean_field hN ht
    have hMn : 0 ≤ MB * d := mul_nonneg hMB (Nat.cast_nonneg _)
    have hC₀ : 0 ≤ C₀ := h.energy.completion.1
    have hI : 0 ≤ q09b_I d S.s :=
      integral_nonneg fun z => q09b_kernel_nonneg hspos z
    have hĒ0 : 0 ≤ Ē := (h.energy.pos N hN).le.trans (hĒ N hN)
    set Mn : ℝ := MB * d with hMndef
    set B : ℝ := Λ * q09b_I d S.s + 1 with hB
    have hB0 : 0 ≤ B := by positivity
    have hc : 0 ≤ 2 * Mn * S.s := by positivity
    set Φ : (R N).Ω → ℝ := fun ζ => correctedEnergyRd S C₀ Λ N ((R N).X (Real.toNNReal t) ζ) t with hΦ
    have hpt : ∀ ζ, ENNReal.ofReal (q09b_u d S.s Mn N ((R N).X (Real.toNNReal t) ζ)) ≤
        ENNReal.ofReal (2 * Mn * S.s) * ENNReal.ofReal (Φ ζ) + ENNReal.ofReal (2 * Mn * S.s * B) := by
      intro ζ
      have h1 := q09b_u_energy_bound hN0 hspos S.hsd hMn hC₀ hΛ hρprob hρΛ
        ((R N).X (Real.toNNReal t) ζ)
      calc ENNReal.ofReal (q09b_u d S.s Mn N ((R N).X (Real.toNNReal t) ζ))
          ≤ ENNReal.ofReal (2 * Mn * S.s * Φ ζ + 2 * Mn * S.s * B) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [← hB] at h1
            simp only [hΦ, correctedEnergyRd]
            linarith [h1]
        _ ≤ ENNReal.ofReal (2 * Mn * S.s * Φ ζ) + ENNReal.ofReal (2 * Mn * S.s * B) :=
            ENNReal.ofReal_add_le
        _ = _ := by rw [ENNReal.ofReal_mul hc]
    calc ∫⁻ ζ, ENNReal.ofReal (q09b_u d S.s Mn N ((R N).X (Real.toNNReal t) ζ)) ∂(R N).P
        ≤ ∫⁻ ζ, (ENNReal.ofReal (2 * Mn * S.s) * ENNReal.ofReal (Φ ζ) +
            ENNReal.ofReal (2 * Mn * S.s * B)) ∂(R N).P := lintegral_mono hpt
      _ = ENNReal.ofReal (2 * Mn * S.s) * ∫⁻ ζ, ENNReal.ofReal (Φ ζ) ∂(R N).P +
            ENNReal.ofReal (2 * Mn * S.s * B) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          simp
      _ ≤ ENNReal.ofReal (2 * Mn * S.s) * ENNReal.ofReal (𝔈 N) +
            ENNReal.ofReal (2 * Mn * S.s * B) := by
          gcongr
          exact h.energy.bound N hN t ht
      _ ≤ ENNReal.ofReal (2 * Mn * S.s) * ENNReal.ofReal Ē +
            ENNReal.ofReal (2 * Mn * S.s * B) := by
          gcongr
          exact hĒ N hN
      _ = ENNReal.ofReal (2 * Mn * S.s * Ē + 2 * Mn * S.s * B) := by
          rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_add (mul_nonneg hc hĒ0)
            (mul_nonneg hc hB0)]

theorem q09b_m20_nonneg (S : WholeMainData d) (R : ∀ N, RealizationRd d N) {MB Λ ΛV G₀ m20 C₀ : ℝ}
    {𝔈 : ℕ → ℝ} {r mV : ℕ} (h : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) : 0 ≤ m20 := by
  by_contra hneg
  push_neg at hneg
  have hI := h.second_moment 2 (by norm_num)
  rw [ENNReal.ofReal_of_nonpos hneg.le] at hI
  have hflow := h.flow 2 (by norm_num)
  have hm : Measurable (fun ζ => secondMomentOf (empirical ((R 2).X₀ ζ))) :=
    Q09A.measurable_secondMoment_empirical (by norm_num) hflow.init_meas
  have h0 : ∀ᵐ ζ ∂(R 2).P, ENNReal.ofReal (secondMomentOf (empirical ((R 2).X₀ ζ))) = 0 :=
    (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp hm)).1 (le_antisymm hI bot_le)
  obtain ⟨ζ, h1, h2⟩ := (h0.and hflow.init_distinct).exists
  have hsm : secondMomentOf (empirical ((R 2).X₀ ζ)) =
      ((2 : ℕ) : ℝ)⁻¹ * ∑ i : Fin 2, ‖(R 2).X₀ ζ i‖ ^ 2 :=
    pair_empirical (by norm_num) _ _
  rw [ENNReal.ofReal_eq_zero, hsm, Fin.sum_univ_two] at h1
  have h3 : ‖(R 2).X₀ ζ 0‖ ^ 2 = 0 := by
    have := sq_nonneg ‖(R 2).X₀ ζ 0‖
    have := sq_nonneg ‖(R 2).X₀ ζ 1‖
    push_cast at h1
    nlinarith
  have h4 : ‖(R 2).X₀ ζ 1‖ ^ 2 = 0 := by
    have := sq_nonneg ‖(R 2).X₀ ζ 0‖
    have := sq_nonneg ‖(R 2).X₀ ζ 1‖
    push_cast at h1
    nlinarith
  have e0 : (R 2).X₀ ζ 0 = 0 := norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h3)
  have e1 : (R 2).X₀ ζ 1 = 0 := norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h4)
  exact h2 ⟨0, 1, by decide, by rw [e0, e1]⟩

/-- The particle second moment bound for one `N ≥ 1` and one time. -/
theorem q09b_perN (S : WholeMainData d) (R : ∀ N, RealizationRd d N) {MB Λ ΛV G₀ m20 C₀ : ℝ}
    {𝔈 : ℕ → ℝ} {r mV : ℕ} (h : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hmV : 2 ≤ mV)
    {νbar Ē : ℝ} (hν : ∀ N, S.invβ N ≤ νbar) (hĒ : ∀ N : ℕ, 1 ≤ N → 𝔈 N ≤ Ē)
    {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) :
    ∫⁻ ζ, ENNReal.ofReal (q09b_g d N ((R N).X (Real.toNNReal t) ζ)) ∂(R N).P ≤
      ENNReal.ofReal (Real.exp ((G₀ + 2 * ΛV) * S.T) *
        (m20 + ((MB * d + G₀ + 2 * νbar * d) +
          (2 * (MB * d) * S.s * Ē + 2 * (MB * d) * S.s * (Λ * q09b_I d S.s + 1))) * S.T)) := by
  classical
  have hN0 : 0 < N := hN
  obtain ⟨ℱ, W', hF⟩ := h.filtered N
  have hflow := h.flow N hN
  obtain ⟨hinit, heqn, hcont, hmeas⟩ := q09b_flow_data hflow
  have hMB : 0 ≤ MB := (abs_nonneg _).trans (h.matrix_bound ⟨0, S.hd⟩ ⟨0, S.hd⟩)
  have hG₀ : 0 ≤ G₀ := (norm_nonneg _).trans h.potential.2.2
  have hΛV : 0 ≤ ΛV := (norm_nonneg _).trans (h.potential.2.1 2 le_rfl hmV 0)
  have hΛ := q09b_Lam_nonneg S h.mean_field
  have hm20 := q09b_m20_nonneg S R h
  have hν0 : 0 ≤ S.invβ N := S.hinvβ N
  have hνN : S.invβ N ≤ νbar := hν N
  have hνb : 0 ≤ νbar := hν0.trans hνN
  have hĒ0 : 0 ≤ Ē := (h.energy.pos N hN).le.trans (hĒ N hN)
  have hMn : 0 ≤ MB * d := mul_nonneg hMB (Nat.cast_nonneg _)
  have hspos : 0 ≤ S.s := S.hs0
  set D : WholeDyn d := S.dyn N with hD
  have hDs : D.s = S.s := rfl
  have hDM : PDE.MatBound MB D.M := h.matrix_bound
  have hDV : VHypRd mV ΛV G₀ D.V := h.potential
  have hGV : Measurable (gradient D.V) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp
      (measurable_fderiv ℝ _)
  -- the constants
  set A : ℝ := 2 * (MB * d) * S.s * Ē + 2 * (MB * d) * S.s * (Λ * q09b_I d S.s + 1) with hAdef
  have hA : 0 ≤ A := by
    by_cases hs : S.s = 0
    · simp [hAdef, hs]
    · have hsp : 0 < S.s := lt_of_le_of_ne hspos (Ne.symm hs)
      have hI : 0 ≤ q09b_I d S.s := integral_nonneg fun z => q09b_kernel_nonneg hsp z
      have : 0 ≤ Λ * q09b_I d S.s + 1 := by positivity
      positivity
  have hc : 0 ≤ G₀ + 2 * ΛV := by positivity
  have hc0 : 0 ≤ MB * d + G₀ + 2 * νbar * d := by positivity
  -- hypotheses of the abstract bound
  have hX0 : ∀ t : ℝ, Measurable[ℱ t] ((R N).X 0) := fun t => q09b_measurable_init hF t
  have hXcont : ∀ᵐ ζ ∂(R N).P, Continuous fun t => (R N).X t ζ := by
    filter_upwards [hcont] with ζ hζ
    exact continuous_pi hζ
  have hb : IsProgressive ℱ (ofNNRealTime
      (fun t ζ => (fun i => particleDriftW D ((R N).X t ζ) i : EucConfig d N))) :=
    fun i => (q09b_measurable_driftVec D hGV).comp (hF.progressive i)
  have hbint : ∀ᵐ ζ ∂(R N).P, IntegrableOn (fun s : ℝ =>
      (fun t ζ => (fun i => particleDriftW D ((R N).X t ζ) i : EucConfig d N))
        (Real.toNNReal s) ζ) (Set.Icc 0 S.T) := by
    filter_upwards [heqn] with ζ hζ
    have := (hζ (Real.toNNReal S.T) (by rw [Real.coe_toNNReal _ S.hT.le])).1
    rw [Real.coe_toNNReal _ S.hT.le] at this
    rw [IntegrableOn, integrable_pi_iff]
    exact this
  have hX : ∀ᵐ ζ ∂(R N).P, ∀ t : ℝ≥0, (t : ℝ) ≤ S.T →
      (R N).X t ζ = (R N).X 0 ζ + (∫ s in Set.Icc (0 : ℝ) t,
        (fun t ζ => (fun i => particleDriftW D ((R N).X t ζ) i : EucConfig d N))
          (Real.toNNReal s) ζ) +
        ∑ k, (W' t ζ k - W' 0 ζ k) • q09b_noise d N (S.invβ N) k := by
    filter_upwards [heqn, hF.coords] with ζ he hc t ht
    obtain ⟨hI, hE⟩ := he t ht
    have hIe : Integrable (fun s : ℝ => (fun i => particleDriftW D ((R N).X (Real.toNNReal s) ζ) i :
        EucConfig d N)) (volume.restrict (Set.Icc 0 (t : ℝ))) := by
      rw [integrable_pi_iff]
      exact hI
    funext i
    have hA1 : (∫ s in Set.Icc (0 : ℝ) t, (fun i => particleDriftW D ((R N).X (Real.toNNReal s) ζ) i :
        EucConfig d N)) i = ∫ s in Set.Icc (0 : ℝ) t,
          particleDriftW D ((R N).X (Real.toNNReal s) ζ) i :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).integral_comp_comm hIe).symm
    have hnoise : (∑ k, (W' t ζ k - W' 0 ζ k) • q09b_noise d N (S.invβ N) k) i =
        Real.sqrt (2 * S.invβ N) • ((R N).W t ζ i - (R N).W 0 ζ i) := by
      ext j
      simp only [Finset.sum_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, Pi.smul_apply,
        q09b_noise, Fintype.sum_prod_type, hc t, hc 0]
      simp [Pi.single_apply, mul_comm]
    show (R N).X t ζ i = ((R N).X 0 ζ + _ + _) i
    simp only [Pi.add_apply]
    rw [hA1, hnoise, hE i]
    rfl
  have hu : IsProgressive ℱ (ofNNRealTime
      (fun t ζ => q09b_u d S.s (MB * d) N ((R N).X t ζ))) :=
    fun i => (q09b_measurable_u S.s (MB * d)).comp (hF.progressive i)
  have hu0 : ∀ (t : ℝ≥0) ζ, 0 ≤ q09b_u d S.s (MB * d) N ((R N).X t ζ) :=
    fun t ζ => q09b_u_nonneg hspos hMn _
  have hdrift : ∀ᵐ ζ ∂(R N).P, ∀ s : ℝ≥0, (s : ℝ) ≤ S.T →
      fderiv ℝ (q09b_g d N) ((R N).X s ζ) (fun i => particleDriftW D ((R N).X s ζ) i) +
        (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ (q09b_g d N)) ((R N).X s ζ)
          (q09b_noise d N (S.invβ N) k) (q09b_noise d N (S.invβ N) k)
        ≤ (G₀ + 2 * ΛV) * q09b_g d N ((R N).X s ζ) + (MB * d + G₀ + 2 * νbar * d) +
          q09b_u d S.s (MB * d) N ((R N).X s ζ) := by
    refine Filter.Eventually.of_forall fun ζ s hs => ?_
    exact q09b_drift_le hN0 hspos hmV hMB hG₀ hΛV D hDs hDM hDV hν0 hνN _
  have huE : ∀ s : ℝ≥0, (s : ℝ) ≤ S.T →
      ∫⁻ ζ, ENNReal.ofReal (q09b_u d S.s (MB * d) N ((R N).X s ζ)) ∂(R N).P ≤ ENNReal.ofReal A := by
    intro s hs
    have := q09b_huE S R h hĒ hMB hN (t := (s : ℝ)) ⟨s.2, hs⟩
    simpa [Real.toNNReal_coe] using this
  have hm : ∫⁻ ζ, ENNReal.ofReal (q09b_g d N ((R N).X 0 ζ)) ∂(R N).P ≤ ENNReal.ofReal m20 := by
    have h1 := h.second_moment N hN
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) h1
    filter_upwards [hinit] with ζ hζ
    rw [hζ]
    congr 1
    exact (pair_empirical hN0 _ (fun y : Euc d => ‖y‖ ^ 2)).symm
  have key := q09b_moment_bound (P := (R N).P) hF.brownian S.hT (q09b_g d N) (q09b_contDiff_g d N)
    (q09b_g_nonneg d N) 1 (fun x => q09b_grad_bound hN0 x) (q09b_noise d N (S.invβ N)) (R N).X hmeas
    hX0 hF.progressive hXcont _ hb hbint hX (G₀ + 2 * ΛV) (MB * d + G₀ + 2 * νbar * d) A m20 hc hc0
    hA hm20 _ hu hu0 hdrift huE hm
  have := key (Real.toNNReal t) (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2)
  exact this

/-- Lemma S.A.18 (`B:lem:moments`) in the form of `PropagatedSecondMoment`. -/
theorem q09b_moments (s MB Λ ΛV G₀ νbar T Ē : ℝ) (r mV : ℕ) (hmV : 2 ≤ mV) :
    ∃ C : ℝ, ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ) (C₀ m20 : ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈 → (∀ N : ℕ, 1 ≤ N → 𝔈 N ≤ Ē) →
        PropagatedSecondMoment S R (C * (1 + m20)) := by
  classical
  refine ⟨Real.exp ((G₀ + 2 * ΛV) * T) *
      (1 + ((MB * d + G₀ + 2 * νbar * d) +
        (2 * (MB * d) * s * Ē + 2 * (MB * d) * s * (Λ * q09b_I d s + 1))) * T) +
      Λ * q09b_K d, ?_⟩
  intro S hs hT hν R 𝔈 C₀ m20 h hĒ N hN t ht
  have hMB : 0 ≤ MB := (abs_nonneg _).trans (h.matrix_bound ⟨0, S.hd⟩ ⟨0, S.hd⟩)
  have hG₀ : 0 ≤ G₀ := (norm_nonneg _).trans h.potential.2.2
  have hΛV : 0 ≤ ΛV := (norm_nonneg _).trans (h.potential.2.1 2 le_rfl hmV 0)
  have hΛ := q09b_Lam_nonneg S h.mean_field
  have hm20 := q09b_m20_nonneg S R h
  have hν0 : 0 ≤ S.invβ N := S.hinvβ N
  have hνb : 0 ≤ νbar := hν0.trans (hν N)
  have hĒ0 : 0 ≤ Ē := (h.energy.pos N hN).le.trans (hĒ N hN)
  have hMn : 0 ≤ MB * d := mul_nonneg hMB (Nat.cast_nonneg _)
  have hT0 : 0 < T := hT ▸ S.hT
  have hs0 : 0 ≤ s := hs ▸ S.hs0
  have hA : 0 ≤ 2 * (MB * d) * s * Ē + 2 * (MB * d) * s * (Λ * q09b_I d s + 1) := by
    by_cases hs' : s = 0
    · simp [hs']
    · have hsp : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs')
      have hI : 0 ≤ q09b_I d s := integral_nonneg fun z => q09b_kernel_nonneg hsp z
      have : 0 ≤ Λ * q09b_I d s + 1 := by positivity
      positivity
  have hc0 : 0 ≤ MB * d + G₀ + 2 * νbar * d := by positivity
  have hK : 0 ≤ q09b_K d := integral_nonneg fun x => Real.rpow_nonneg (by positivity) _
  have hper := q09b_perN S R h hmV hν hĒ hN ht
  rw [hs, hT] at hper
  have hmf := q09b_mf_second_moment (h.mean_field.regular N hN)
    (fun t ht => (h.mean_field.solution N hN).density t ht) ht
  have hsm : ∀ ζ, secondMomentOf (empirical ((R N).X (Real.toNNReal t) ζ)) =
      q09b_g d N ((R N).X (Real.toNNReal t) ζ) := fun ζ =>
    pair_empirical (by omega) _ (fun y : Euc d => ‖y‖ ^ 2)
  set E1 : ℝ := Real.exp ((G₀ + 2 * ΛV) * T) *
    (m20 + ((MB * d + G₀ + 2 * νbar * d) +
      (2 * (MB * d) * s * Ē + 2 * (MB * d) * s * (Λ * q09b_I d s + 1))) * T) with hE1
  have hcT : 0 ≤ ((MB * d + G₀ + 2 * νbar * d) +
      (2 * (MB * d) * s * Ē + 2 * (MB * d) * s * (Λ * q09b_I d s + 1))) * T :=
    mul_nonneg (add_nonneg hc0 hA) hT0.le
  have hE1nn : 0 ≤ E1 := by positivity
  have hΛK : 0 ≤ Λ * q09b_K d := mul_nonneg hΛ hK
  have hmfnn : 0 ≤ secondMomentOf (withDensityReal (S.ρ N t)) := Q09A.secondMomentOf_nonneg _
  calc ∫⁻ ζ, ENNReal.ofReal (secondMomentOf (empirical ((R N).X (Real.toNNReal t) ζ)) +
        secondMomentOf (withDensityReal (S.ρ N t))) ∂(R N).P
      ≤ ∫⁻ ζ, (ENNReal.ofReal (q09b_g d N ((R N).X (Real.toNNReal t) ζ)) +
          ENNReal.ofReal (secondMomentOf (withDensityReal (S.ρ N t)))) ∂(R N).P := by
        refine lintegral_mono fun ζ => ?_
        rw [hsm ζ]
        exact ENNReal.ofReal_add_le
    _ = ∫⁻ ζ, ENNReal.ofReal (q09b_g d N ((R N).X (Real.toNNReal t) ζ)) ∂(R N).P +
          ENNReal.ofReal (secondMomentOf (withDensityReal (S.ρ N t))) := by
        rw [lintegral_add_right _ measurable_const]
        simp
    _ ≤ ENNReal.ofReal E1 + ENNReal.ofReal (Λ * q09b_K d) :=
        add_le_add hper (ENNReal.ofReal_le_ofReal hmf)
    _ = ENNReal.ofReal (E1 + Λ * q09b_K d) := (ENNReal.ofReal_add hE1nn hΛK).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have he : 0 < Real.exp ((G₀ + 2 * ΛV) * T) := Real.exp_pos _
        simp only [hE1]
        nlinarith [mul_nonneg (mul_nonneg he.le hcT) hm20, mul_nonneg hΛK hm20, he]

end HRS.Whole.Q09B
