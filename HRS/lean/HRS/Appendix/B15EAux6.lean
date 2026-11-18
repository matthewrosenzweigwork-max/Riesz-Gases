import HRS.Appendix.B15EAux5

/-!
# Packet B15E, part 6: Stage 1 -- the level-`M` regularised entropy inequality for `V ∈ C²`

Smooth approximants `V_k ≤ V` of `V` (`d1_exists_C2_approx`, shifted down by a constant), the regularised
SDEs for `D_k = {D with V := V_k}`, D2 + D3 for each `k` (`b15e_law_entropy`), Gronwall convergence
`Y^k → Y` and lower semicontinuity of entropy and Fisher information as `k → ∞`.
-/

noncomputable section

open MeasureTheory InformationTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-! ### Smooth approximants from below -/

/-- `C²` functions on the torus are approximated from below by smooth ones, with the gradients converging
uniformly: `V_k ≤ V`, `V - V_k ≤ 2/(k+1)`, `‖∇V_k - ∇V‖ ≤ 1/(k+1)`. -/
theorem b15e_smooth_approx_below {V : Torus d → ℝ} (hV : Torus.IsCk 2 V) :
    ∃ Vk : ℕ → Torus d → ℝ, (∀ k, Torus.IsSmooth (Vk k)) ∧ (∀ k x, Vk k x ≤ V x) ∧
      (∀ k x, V x - Vk k x ≤ 2 * (1 / ((k : ℝ) + 1))) ∧
      (∀ k x, ‖Torus.grad (Vk k) x - Torus.grad V x‖ ≤ 1 / ((k : ℝ) + 1)) := by
  have h := fun k : ℕ => d1_exists_C2_approx (n := d) hV (ε := 1 / ((k : ℝ) + 1)) (by positivity)
  choose ψ hψs hψb using h
  refine ⟨fun k x => ψ k x - 1 / ((k : ℝ) + 1), fun k => ?_, fun k x => ?_, fun k x => ?_, fun k x => ?_⟩
  · have := (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (ψ k)) from hψs k)
    exact this.sub contDiff_const
  · have := (abs_le.1 (hψb k x).1).1
    linarith
  · have := (abs_le.1 (hψb k x).1).2
    linarith
  · have e : Torus.grad (fun x => ψ k x - 1 / ((k : ℝ) + 1)) x = Torus.grad (ψ k) x := by
      unfold Torus.grad gradient
      have : Torus.lift (fun x => ψ k x - 1 / ((k : ℝ) + 1)) =
          fun y => Torus.lift (ψ k) y - 1 / ((k : ℝ) + 1) := rfl
      rw [this, fderiv_sub_const]
    rw [e, norm_sub_rev]
    exact (hψb k x).2.1

/-! ### Comparison of the data `D` and `D_k = {D with V := V_k}` -/

theorem b15e_potentialReg_withV (D : DynData d) (V' : Torus d → ℝ) (M : ℝ) :
    (b15c_potentialReg (N := N) (b15e_withV D V') M) =
      fun X => b15c_potentialReg (N := N) D M X + ∑ i, (V' - D.V) (X i) := by
  funext X
  simp only [b15c_potentialReg, b15c_potentialOf, b15e_withV, Pi.sub_apply, Finset.sum_sub_distrib]
  ring

theorem b15e_liftedDriftReg_sub (D : DynData d) (V' : Torus d → ℝ) (M : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x, ‖Torus.grad V' x - Torus.grad D.V x‖ ≤ ε) (y : Fin N → Euc d) :
    ‖b15c_liftedDriftReg (N := N) (b15e_withV D V') M y - b15c_liftedDriftReg (N := N) D M y‖ ≤ ε := by
  refine (pi_norm_le_iff_of_nonneg hε).2 fun i => ?_
  have e : (b15c_liftedDriftReg (N := N) (b15e_withV D V') M y - b15c_liftedDriftReg (N := N) D M y) i =
      -(Torus.grad V' (Torus.mk (y i)) - Torus.grad D.V (Torus.mk (y i))) := by
    simp only [b15c_liftedDriftReg, b15c_liftedDriftOf, b15e_withV, Pi.sub_apply]
    abel
  rw [e, norm_neg]
  exact h _

theorem b15e_isCk_of_isSmooth {V : Torus d → ℝ} (h : Torus.IsSmooth V) : Torus.IsCk 2 V :=
  (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from h).of_le
    (by first | exact WithTop.coe_le_coe.2 le_top | (norm_cast; exact le_top) | simp)

theorem b15e_lawOf_eq_selectedLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℝ → Ω → Fin N → Euc d) {r : ℝ} (hr : 0 ≤ r) :
    d1_lawOf P Y r = selectedLaw P (b15c_regProcess Y) r := by
  have h := d1_lawOf_eq_regProcess P Y (Real.toNNReal r)
  rw [Real.coe_toNNReal r hr] at h
  exact h

theorem b15e_selectedLaw_zero_of_init {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ' : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {b : ℝ → (Fin N → Euc d) → (Fin N → Euc d)} {σ : (Fin N × Fin d) → (Fin N → Euc d)}
    {Y₀ : Ω → Fin N → Euc d} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hY : IsAdditiveSDESolution P ℱ' W' b σ Y₀ (fun _ => ⊤) Y) :
    selectedLaw P (b15c_regProcess Y) 0 = P.map (fun ω i => Torus.mk (Y₀ ω i)) := by
  unfold selectedLaw
  have : b15c_regProcess Y (Real.toNNReal 0) = fun ω i => Torus.mk (Y₀ ω i) := by
    funext ω i
    simp [b15c_regProcess, projectPath, hY.init ω]
  rw [this]

/-- **The level-`M` regularised entropy inequality for smooth `V`**, in the configuration-space language
(D2 + D3 + the bridges): `𝓗_{U^M}(P^t) + invβ ∫_0^t 𝓘_{U^M}(P^r) dr ≤ 𝓗_{U^M}(P^0)`. -/
theorem b15e_reg_ineq_smooth (hNd : 1 ≤ N * d) (D : DynData d) (hβ : 0 < D.invβ)
    (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) (hV : Torus.IsSmooth D.V) (M : ℝ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ' : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW' : IsBrownianFiltration P ℱ' W') {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ' t] Y₀) {Y : ℝ → Ω → Fin N → Euc d}
    (hY : IsAdditiveSDESolution P ℱ' W' (fun _ => b15c_liftedDriftReg D M) (liftedNoise D) Y₀
      (fun _ => ⊤) Y)
    {T : ℝ} (hT : 0 < T)
    (hfin : b15c_gibbsEntropyGen D.invβ (b15c_potentialReg D M)
      (selectedLaw P (b15c_regProcess Y) 0) < ⊤) :
    ∀ t ∈ Set.Icc 0 T,
      b15c_gibbsEntropyGen D.invβ (b15c_potentialReg D M) (selectedLaw P (b15c_regProcess Y) t)
        + ((ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, b15_fisherInfoGen D.invβ
            (b15c_potentialReg D M) (selectedLaw P (b15c_regProcess Y) r) : ℝ≥0∞) : EReal)
      ≤ b15c_gibbsEntropyGen D.invβ (b15c_potentialReg D M) (selectedLaw P (b15c_regProcess Y) 0) := by
  intro t ht
  have hV2 := b15e_isCk_of_isSmooth hV
  have hVc := b15_continuous_of_isCk hV2
  set U := b15c_potentialReg (N := N) D M with hUdef
  have hUc : Continuous U := b15c_potentialReg_continuous D hVc M
  have hprob : ∀ r : ℝ, IsProbabilityMeasure (selectedLaw P (b15c_regProcess Y) r) := fun r =>
    b15b_selectedLaw_isProb (fun s => b15c_regProcess_measurable hY s) r
  haveI : IsProbabilityMeasure (b15c_gibbsRefGen D.invβ U) := b15e_gibbsRefGen_isProb _ hUc
  -- finiteness of the initial relative entropy
  have hrel0 : relEntropy (selectedLaw P (b15c_regProcess Y) 0) (b15c_gibbsRefGen D.invβ U) < ⊤ := by
    by_contra hcon
    have h' : relEntropy (selectedLaw P (b15c_regProcess Y) 0) (b15c_gibbsRefGen D.invβ U) = ⊤ :=
      not_lt_top_iff.1 hcon
    have : b15c_gibbsEntropyGen D.invβ U (selectedLaw P (b15c_regProcess Y) 0) = ⊤ := by
      unfold b15c_gibbsEntropyGen
      rw [h']
      exact EReal.top_sub_coe _
    exact absurd hfin (by rw [this]; exact lt_irrefl _)
  have hlawEq : ∀ r : ℝ, 0 ≤ r → (d1_lawOf P Y r) = selectedLaw P (b15c_regProcess Y) r :=
    fun r hr => b15e_lawOf_eq_selectedLaw P Y hr
  have hfin' : relEntropy ((d1_lawOf P Y 0).map (d1_configEquiv d N))
      (d1_gibbsMeasure D.invβ (b15d_U D M)) < ⊤ := by
    rw [hlawEq 0 le_rfl]
    have := b15e_relEntropy_map D.invβ U (selectedLaw P (b15c_regProcess Y) 0)
    exact this ▸ hrel0
  have key := b15e_law_entropy hNd D hβ rfl hM hV M hW' hY₀ hY hT hfin' t ht
  -- convert to the configuration language
  have hmapt : ∀ r : ℝ, 0 ≤ r →
      relEntropy ((d1_lawOf P Y r).map (d1_configEquiv d N)) (d1_gibbsMeasure D.invβ (b15d_U D M)) =
        relEntropy (selectedLaw P (b15c_regProcess Y) r) (b15c_gibbsRefGen D.invβ U) := by
    intro r hr
    rw [hlawEq r hr]
    haveI := hprob r
    exact b15e_relEntropy_map D.invβ U _
  have hFish : ∀ r ∈ Set.Icc (0 : ℝ) t, b15_fisherInfoGen D.invβ U (selectedLaw P (b15c_regProcess Y) r) ≤
      d1_fisherInfo D.invβ (b15d_U D M) ((d1_lawOf P Y r).map (d1_configEquiv d N)) := by
    intro r hr
    rw [hlawEq r hr.1]
    exact b15e_fisherInfoGen_le D.invβ U _
  have hI : ∫⁻ r in Set.Icc (0 : ℝ) t, b15_fisherInfoGen D.invβ U (selectedLaw P (b15c_regProcess Y) r) ≤
      ∫⁻ r in Set.Icc (0 : ℝ) t, d1_fisherInfo D.invβ (b15d_U D M)
        ((d1_lawOf P Y r).map (d1_configEquiv d N)) :=
    setLIntegral_mono' measurableSet_Icc hFish
  rw [hmapt t ht.1, hmapt 0 le_rfl] at key
  -- key : R_t + ofReal κ * ∫⁻ I_d1 ≤ R_0 in ENNReal
  have key2 : relEntropy (selectedLaw P (b15c_regProcess Y) t) (b15c_gibbsRefGen D.invβ U) +
      ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, b15_fisherInfoGen D.invβ U
        (selectedLaw P (b15c_regProcess Y) r) ≤
      relEntropy (selectedLaw P (b15c_regProcess Y) 0) (b15c_gibbsRefGen D.invβ U) :=
    le_trans (add_le_add le_rfl (by gcongr)) key
  unfold b15c_gibbsEntropyGen
  set z : ℝ := Real.log (b15c_gibbsPartitionGen D.invβ U).toReal
  have hk2 : (((relEntropy (selectedLaw P (b15c_regProcess Y) t) (b15c_gibbsRefGen D.invβ U) +
      ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, b15_fisherInfoGen D.invβ U
        (selectedLaw P (b15c_regProcess Y) r) : ℝ≥0∞)) : EReal) ≤
      ((relEntropy (selectedLaw P (b15c_regProcess Y) 0) (b15c_gibbsRefGen D.invβ U) : ℝ≥0∞) : EReal) :=
    EReal.coe_ennreal_le_coe_ennreal_iff.mpr key2
  rw [EReal.coe_ennreal_add] at hk2
  have e : ∀ (a J : EReal) (z : ℝ), (a - (z : EReal)) + J = (a + J) - (z : EReal) := by
    intro a J z
    rw [sub_eq_add_neg, sub_eq_add_neg, add_right_comm]
  rw [e, sub_eq_add_neg, sub_eq_add_neg]
  exact add_le_add_left hk2 _

end HRS
