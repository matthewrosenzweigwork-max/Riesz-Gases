import HRS.MH.DualityRdDefs
import HRS.MH.DualityRdA1
import HRS.MH.DualityRdA2
import HRS.MH.DualityRdA3
import HRS.Whole.Q09BAux4

/-!
# DualityRd packet A4: the empirical Itô identity (Lemma 3.6) on `(ℝ^d)^N`

Ports `HRS.empirical_ito_pos` (`HRS/Stochastic/EmpiricalIto.lean:958`) without the covering-space lift: Itô's formula
`ito_formula_additive` (`HRS/Stochastic/Ito.lean:3632`) is applied directly on `E = EucConfig d N`, with `U = Set.univ`,
noise directions `noiseDir D`, drift `particleDriftW D`; the drift identity is packet A2 (`drift_pointwise_rd_proof`), the
Itô integrand is packet A3's `truncGradIntegrand` up to the constant `√(2β⁻¹)/N`, and the `L²` bound is packet A3.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.DualityRd

open HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem da4_euc_decomp (v : Euc d) : ∑ j : Fin d, v j • (EuclideanSpace.single j (1 : ℝ) : Euc d) = v := by
  have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
  simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using h

theorem da4_noise_apply_coord {N : ℕ} (D : WholeDyn d) (k : Fin N × Fin d) (i : Fin N) :
    noiseDir D k i = if i = k.1 then Real.sqrt (2 * D.invβ) • (EuclideanSpace.single k.2 (1 : ℝ) : Euc d) else 0 := by
  simp [noiseDir, Pi.single_apply]

theorem da4_sum_noiseDir_apply {N : ℕ} (D : WholeDyn d) (v : Fin N → Euc d) (i : Fin N) :
    (∑ k : Fin N × Fin d, (v k.1 k.2) • noiseDir D k) i = Real.sqrt (2 * D.invβ) • v i := by
  rw [Finset.sum_apply, Fintype.sum_prod_type]
  simp only [Pi.smul_apply, da4_noise_apply_coord, smul_ite, smul_zero]
  rw [Finset.sum_eq_single i]
  · simp only [if_true, Finset.sum_ite_eq', Finset.mem_univ]
    calc ∑ b : Fin d, v i b • (Real.sqrt (2 * D.invβ) • (EuclideanSpace.single b (1 : ℝ) : Euc d))
        = Real.sqrt (2 * D.invβ) • ∑ b : Fin d, v i b • (EuclideanSpace.single b (1 : ℝ) : Euc d) := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun b _ => smul_comm _ _ _
      _ = Real.sqrt (2 * D.invβ) • v i := by rw [da4_euc_decomp (v i)]
  · intro a _ ha
    simp [Ne.symm ha]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem da4_sum_inner_noiseDir {N : ℕ} (D : WholeDyn d) (g : Fin N → Euc d) (k : Fin N × Fin d) :
    ∑ i, inner ℝ (g i) (noiseDir D k i) = Real.sqrt (2 * D.invβ) * (g k.1) k.2 := by
  have hx : ∀ x, inner ℝ (g x) (noiseDir D k x)
      = if x = k.1 then Real.sqrt (2 * D.invβ) * (g x) k.2 else 0 := by
    intro x
    rw [da4_noise_apply_coord]
    split_ifs with h
    · simp [inner_smul_right, EuclideanSpace.inner_single_right]
    · simp
  simp only [hx, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem da4_integral_apply {N : ℕ} {S : Set ℝ} (g : ℝ → Fin N → Euc d) (i : Fin N)
    (hg : Integrable g (volume.restrict S)) :
    (∫ s in S, g s) i = ∫ s in S, g s i :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).integral_comp_comm hg).symm

theorem da4_fderiv_empirical {N : ℕ} (D : WholeDyn d) {g : Euc d → ℝ} (hg : Differentiable ℝ g)
    (Y : EucConfig d N) (k : Fin N × Fin d) :
    fderiv ℝ (fun Z : EucConfig d N => (N : ℝ)⁻¹ * ∑ i, g (Z i)) Y (noiseDir D k)
      = (N : ℝ)⁻¹ * (Real.sqrt (2 * D.invβ) * gradient g (Y k.1) k.2) := by
  rw [show (fun Z : EucConfig d N => (N : ℝ)⁻¹ * ∑ i, g (Z i)) = HRS.sumLift N g from rfl,
    HRS.fderiv_sumLift_apply hg Y (noiseDir D k)]
  congr 1
  simp only [da2_fderiv_eq_inner]
  exact da4_sum_inner_noiseDir D (fun i => gradient g (Y i)) k

theorem da4_itoDrift_eq {Ω : Type*} {N : ℕ} (hN : 0 < N) (D : WholeDyn d) (hinv : 0 ≤ D.invβ) {t : ℝ}
    (ht0 : 0 < t) {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t)
    (X : ℝ≥0 → Ω → EucConfig d N) (ξ : Ω)
    (hcol : X (Real.toNNReal s) ξ ∉ eucCollisionSet d N ∨ D.M = 0) :
    itoDrift t (fun r (Z : EucConfig d N) => (N : ℝ)⁻¹ * ∑ i, f r (Z i)) (ofNNRealTime X)
        (ofNNRealTime (fun (s : ℝ≥0) (ξ : Ω) => particleDriftW D (X s ξ))) (fun _ _ => noiseDir D) s ξ
      = Whole.pair (Whole.empirical (X (Real.toNNReal s) ξ)) (driftTestRd D f ft s)
        + interactionPairingW D (f s) (Whole.empirical (X (Real.toNNReal s) ξ))
            (Whole.empirical (X (Real.toNNReal s) ξ)) := by
  unfold itoDrift
  simp only [ofNNRealTime_apply]
  exact drift_pointwise_rd_proof hN D hinv ht0 hf hs (X (Real.toNNReal s) ξ) hcol


/-- **Packet A4 = Lemma 3.6 on `ℝ^d`** (L). Statement copied verbatim from `DualityRdSpec.lean`. -/
theorem empirical_ito_rd_proof {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {N : ℕ}
    (D : WholeDyn d) (hinv : 0 ≤ D.invβ) (hVm : Measurable (gradient D.V)) {T : ℝ}
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : IsWholeContactStrongSolution P D T X₀ W X)
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hF : IsWholeFilteredSolution P ℱ W' W X)
    (hocc : D.M = 0 ∨ ∀ᵐ ζ ∂P,
      volume {s : ℝ | s ∈ Set.Icc (0 : ℝ) T ∧ X (Real.toNNReal s) ζ ∈ eucCollisionSet d N} = 0)
    {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T) {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) :
    ∀ᵐ ζ ∂P, ∀ τ ∈ Set.Icc (0 : ℝ) t,
      IntegrableOn (fun r => Whole.pair (Whole.empirical (X (Real.toNNReal r) ζ)) (driftTestRd D f ft r)
        + interactionPairingW D (f r) (Whole.empirical (X (Real.toNNReal r) ζ))
            (Whole.empirical (X (Real.toNNReal r) ζ))) (Set.Icc 0 τ) ∧
      Whole.pair (Whole.empirical (X (Real.toNNReal τ) ζ)) (f τ)
        = Whole.pair (Whole.empirical (X 0 ζ)) (f 0)
          + (∫ r in Set.Icc (0 : ℝ) τ, (Whole.pair (Whole.empirical (X (Real.toNNReal r) ζ)) (driftTestRd D f ft r)
              + interactionPairingW D (f r) (Whole.empirical (X (Real.toNNReal r) ζ))
                  (Whole.empirical (X (Real.toNNReal r) ζ))))
          + (Real.sqrt (2 * D.invβ) / N) * HRS.itoIntegral P ℱ W' (truncGradIntegrand t f X) τ ζ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine Filter.Eventually.of_forall fun ζ τ _ => ?_
    simp [Whole.pair, Whole.empirical, interactionPairingW]
  have htnn : (0 : ℝ) ≤ t := ht0.le
  -- the Itô process in `ℝ^d` (no lift): `X_τ = X_0 + ∫ b + ∑_k (W'_τ - W'_0) σ_k`
  have hZint : ∀ᵐ ζ ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ t →
      X τ ζ = X 0 ζ + (∫ s in Set.Icc (0 : ℝ) τ, particleDriftW D (X (Real.toNNReal s) ζ))
        + ∑ k, (W' τ ζ k - W' 0 ζ k) • noiseDir D k := by
    filter_upwards [hX.eqn, hF.coords] with ζ h1 h2 τ hτ
    obtain ⟨hI, h1⟩ := h1 τ (hτ.trans htT)
    have e : ∀ k : Fin N × Fin d, W' τ ζ k - W' 0 ζ k
        = (fun l => W τ ζ l - W 0 ζ l) k.1 k.2 := by
      intro k
      have h3 := h2 τ k.1 k.2
      have h4 := h2 0 k.1 k.2
      rw [Prod.mk.eta] at h3 h4
      rw [h3, h4]
      simp
    funext i
    have hsum : (∑ k : Fin N × Fin d, (W' τ ζ k - W' 0 ζ k) • noiseDir D k) i
        = Real.sqrt (2 * D.invβ) • (W τ ζ i - W 0 ζ i) := by
      simp only [e]
      exact da4_sum_noiseDir_apply D (fun l => W τ ζ l - W 0 ζ l) i
    have hIi : Integrable (fun s : ℝ => particleDriftW D (X (Real.toNNReal s) ζ)) (volume.restrict (Set.Icc 0 (τ : ℝ))) :=
      integrable_pi_iff.2 hI
    simp only [Pi.add_apply]
    rw [hsum, da4_integral_apply _ i hIi, ← h1 i]
  -- integrability of the drift on `[0,t]`
  have hbint : ∀ᵐ ζ ∂P, IntegrableOn (fun s : ℝ => particleDriftW D (X (Real.toNNReal s) ζ)) (Set.Icc 0 t) := by
    filter_upwards [hX.eqn] with ζ h1
    have htt : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t htnn
    obtain ⟨hI, -⟩ := h1 (Real.toNNReal t) ((le_of_eq htt).trans htT)
    rw [htt] at hI
    exact integrable_pi_iff.2 hI
  -- measurability of `X 0` for every real time
  have hX₀ : ∀ s : ℝ, Measurable[ℱ s] (X 0) := by
    intro s
    rcases le_or_gt 0 s with hs | hs
    · exact (hF.adapted 0).mono (ℱ.mono (by simpa using hs)) le_rfl
    · have h := hF.progressive.adapted s
      have e : ofNNRealTime X s = X 0 := by
        funext ξ
        simp [ofNNRealTime_apply, Real.toNNReal_of_nonpos hs.le]
      rw [e] at h
      exact h
  have hb : MeasureTheory.IsProgressive ℱ
      (ofNNRealTime (fun (s : ℝ≥0) (ξ : Ω) => particleDriftW D (X s ξ))) :=
    fun i => (Q09B.q09b_measurable_driftVec D hVm).comp (hF.progressive i)
  -- Itô's formula on `(ℝ^d)^N`
  have hito := ito_formula_additive (P := P) (ℱ := ℱ) hF.brownian (T := t) htnn
    (fun r (Y : EucConfig d N) => (N : ℝ)⁻¹ * ∑ i, f r (Y i)) (isC12On_empLiftRd_proof ht0 hf)
    (noiseDir D) X hX.adapted hX₀ (fun (s : ℝ≥0) (ξ : Ω) => particleDriftW D (X s ξ)) hb hbint hZint
  -- the Itô integrand is `√(2β⁻¹)/N` times the truncated gradient integrand
  have hΦeq : itoIntegrand t Set.univ (fun r (Y : EucConfig d N) => (N : ℝ)⁻¹ * ∑ i, f r (Y i))
      (ofNNRealTime X) (fun _ _ => noiseDir D)
      = fun s ξ => (Real.sqrt (2 * D.invβ) / (N : ℝ)) • truncGradIntegrand t f X s ξ := by
    funext s ξ k
    simp only [itoIntegrand, truncGradIntegrand, ofNNRealTime_apply, Set.mem_univ, Set.setOf_true,
      Set.indicator_univ, Pi.smul_apply, smul_eq_mul]
    by_cases hs : s ∈ Set.Icc (0 : ℝ) t
    · rw [Set.indicator_of_mem hs, if_pos hs]
      rw [da4_fderiv_empirical D ((hf.c2 s hs).differentiable (by norm_num)) (X (Real.toNNReal s) ξ) k]
      simp only [gradComp]
      ring
    · rw [Set.indicator_of_notMem hs, if_neg hs]
      simp
  have hΦprog : HRS.IsProgressiveL2 P ℱ (truncGradIntegrand t f X) :=
    isProgressiveL2_truncGrad_proof ht0.le hf hF.progressive
  have hΦs : HRS.IsProgressiveL2 P ℱ
      (fun s ξ => (Real.sqrt (2 * D.invβ) / (N : ℝ)) • truncGradIntegrand t f X s ξ) :=
    hΦprog.smul _
  have hloc := HRS.localItoIntegral_eq_itoIntegral hF.brownian hΦs
  have hsm := HRS.itoIntegral_smul hF.brownian hΦprog (Real.sqrt (2 * D.invβ) / (N : ℝ))
  -- collisions: the drift identity holds for a.e. time
  have hcolae : ∀ᵐ ζ ∂P, ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.Icc (0 : ℝ) t →
      (X (Real.toNNReal s) ζ ∉ eucCollisionSet d N ∨ D.M = 0) := by
    rcases hocc with hM | hNull
    · exact Filter.Eventually.of_forall fun ζ => Filter.Eventually.of_forall fun s _ => Or.inr hM
    · filter_upwards [hNull] with ζ hζ
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hζ] with s hs hsI
      exact Or.inl fun hc => hs ⟨⟨hsI.1, hsI.2.trans htT⟩, hc⟩
  filter_upwards [hito, hloc, hsm, hcolae] with ζ hitoζ hlocζ hsmζ hcolζ
  have hptζ : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.Icc (0 : ℝ) t →
      itoDrift t (fun r (Y : EucConfig d N) => (N : ℝ)⁻¹ * ∑ i, f r (Y i)) (ofNNRealTime X)
        (ofNNRealTime (fun (s : ℝ≥0) (ξ : Ω) => particleDriftW D (X s ξ))) (fun _ _ => noiseDir D) s ζ
      = Whole.pair (Whole.empirical (X (Real.toNNReal s) ζ)) (driftTestRd D f ft s)
        + interactionPairingW D (f s) (Whole.empirical (X (Real.toNNReal s) ζ))
            (Whole.empirical (X (Real.toNNReal s) ζ)) :=
    hcolζ.mono fun s hs hsI => da4_itoDrift_eq hN D hinv ht0 hf hsI X ζ (hs hsI)
  obtain ⟨hIdrift, hEq⟩ := hitoζ
  rw [hΦeq] at hEq
  intro τ hτ
  have hτnn : ((Real.toNNReal τ : ℝ≥0) : ℝ) = τ := Real.coe_toNNReal τ hτ.1
  have hE := hEq (Real.toNNReal τ) ((le_of_eq hτnn).trans hτ.2)
  rw [hτnn, hlocζ τ, hsmζ τ] at hE
  have hL : (N : ℝ)⁻¹ * ∑ i, f τ (X (Real.toNNReal τ) ζ i)
      = Whole.pair (Whole.empirical (X (Real.toNNReal τ) ζ)) (f τ) :=
    (Whole.pair_empirical hN _ _).symm
  have hL0 : (N : ℝ)⁻¹ * ∑ i, f 0 (X 0 ζ i) = Whole.pair (Whole.empirical (X 0 ζ)) (f 0) :=
    (Whole.pair_empirical hN _ _).symm
  rw [hL, hL0] at hE
  have hIntEq : (∫ s in Set.Icc (0 : ℝ) τ, itoDrift t (fun r (Y : EucConfig d N) => (N : ℝ)⁻¹ * ∑ i, f r (Y i))
        (ofNNRealTime X) (ofNNRealTime (fun (s : ℝ≥0) (ξ : Ω) => particleDriftW D (X s ξ)))
        (fun _ _ => noiseDir D) s ζ)
      = ∫ r in Set.Icc (0 : ℝ) τ, (Whole.pair (Whole.empirical (X (Real.toNNReal r) ζ)) (driftTestRd D f ft r)
          + interactionPairingW D (f r) (Whole.empirical (X (Real.toNNReal r) ζ))
              (Whole.empirical (X (Real.toNNReal r) ζ))) :=
    setIntegral_congr_ae measurableSet_Icc
      (hptζ.mono fun s h hs => h (Set.Icc_subset_Icc le_rfl hτ.2 hs))
  refine ⟨?_, ?_⟩
  · refine (hIdrift.mono_set (Set.Icc_subset_Icc le_rfl hτ.2)).congr_fun_ae ?_
    filter_upwards [ae_restrict_of_ae hptζ, ae_restrict_mem measurableSet_Icc] with s h1s hs
    exact h1s (Set.Icc_subset_Icc le_rfl hτ.2 hs)
  · linarith [hE, hIntEq]

end HRS.MH.DualityRd
