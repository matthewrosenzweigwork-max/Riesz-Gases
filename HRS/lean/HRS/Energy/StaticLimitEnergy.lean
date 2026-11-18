import HRS.Energy.StaticLimitJoint

/-!
# The modulated energy as a squared feature norm (work package STAT-4.21)

For the spectral kernel `g = specKernel a`, `N F_N(X, μ) = ½ ‖N^{-1/2} ∑_j Z(x_j)‖² - ½ g(0)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.StaticLimitAux

open HRS Torus

variable {d : ℕ} {a : Lattice d → ℝ}

/-- The explicit modulated energy (the formula of `HRS.modulatedEnergy` for `h x y = g (x - y)`). -/
def modE (g : Torus d → ℝ) (N : ℕ) (X : Fin N → Torus d) (μ : Measure (Torus d)) : ℝ :=
  (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j)
    - (1 / (N : ℝ)) * ∑ i, ∫ y, g (X i - y) ∂μ
    + (1 / 2) * ∫ x, ∫ y, g (x - y) ∂μ ∂μ

section Kernel

variable (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]

/-- The mean kernel `G(x) = ∫ g(x - y) dμ(y)`. -/
def Gk (a : Lattice d → ℝ) (μ : Measure (Torus d)) (x : Torus d) : ℝ :=
  ∫ y, specKernel a (x - y) ∂μ

include ha0 has in
theorem hasSum_Gk (x : Torus d) :
    HasSum (fun i : Idx d => feat a i x * mfeat μ a i) (Gk a μ x) := by
  have h := hasSum_kernel_integral ha0 has μ (f := fun _ => (1 : ℝ)) (integrable_const _) x
  simpa [Gk, mfeat] using h

include ha0 has in
theorem hasSum_mfeat_sq :
    HasSum (fun i : Idx d => mfeat μ a i * mfeat μ a i) (∫ x, Gk a μ x ∂μ) := by
  have h := hasSum_integral_tsum_mul ha0 has μ (e := feat a) (fun i => continuous_feat i)
    (B := 1) (fun i y => by simpa using abs_feat_le i y) (c := mfeat μ a) (C := 1)
    (fun i => by simpa using abs_mfeat_le μ (a := a) i) (k := fun _ => (1 : ℝ)) (integrable_const _)
  have e : ∀ x, ∑' i, mfeat μ a i * feat a i x = Gk a μ x := by
    intro x
    rw [← (hasSum_Gk ha0 has μ x).tsum_eq]
    exact tsum_congr fun i => mul_comm _ _
  simp only [mul_one] at h
  simp_rw [e] at h
  simpa [mfeat] using h

include ha0 has in
theorem hasSum_Zfeat_mul (x y : Torus d) :
    HasSum (fun i : Idx d => Zfeat μ a i x * Zfeat μ a i y)
      (specKernel a (x - y) - Gk a μ x - Gk a μ y + ∫ z, Gk a μ z ∂μ) := by
  have h1 := hasSum_feat_mul ha0 has x y
  have h2 := hasSum_Gk ha0 has μ x
  have h3 := hasSum_Gk ha0 has μ y
  have h4 := hasSum_mfeat_sq ha0 has μ
  have h5 := ((h1.sub h2).sub h3).add h4
  convert h5 using 1
  · funext i
    simp only [Zfeat]
    ring

end Kernel


section SsumCoord

theorem FeatSp.coord_smul (c : ℝ) (f : FeatSp d) (i : Idx d) :
    FeatSp.coord (c • f) i = c * FeatSp.coord f i := rfl

theorem FeatSp.coord_sum {ι : Type*} (s : Finset ι) (f : ι → FeatSp d) (i : Idx d) :
    FeatSp.coord (∑ j ∈ s, f j) i = ∑ j ∈ s, FeatSp.coord (f j) i := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (congrArg _ ih).trans rfl

theorem snd_Ssum (m : ℝ) (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (N : ℕ) (X : Fin N → Torus d) :
    (Ssum (Yj m ha0 has μ) N X).snd =
      (Real.sqrt N)⁻¹ • ∑ j, Yf ha0 has μ (X j) := by
  unfold Ssum
  rw [WithLp.smul_snd]
  congr 1
  have := map_sum (WithLp.sndL 2 ℝ (NegSobolev d m) (FeatSp d)) (fun j => Yj m ha0 has μ (X j))
    Finset.univ
  simp only [WithLp.sndL_apply] at this
  exact this

theorem coord_snd_Ssum (m : ℝ) (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (N : ℕ) (X : Fin N → Torus d) (i : Idx d) :
    FeatSp.coord (Ssum (Yj m ha0 has μ) N X).snd i =
      (Real.sqrt N)⁻¹ * ∑ j, Zfeat μ a i (X j) := by
  rw [snd_Ssum m ha0 has μ, FeatSp.coord_smul, FeatSp.coord_sum]
  rfl

end SsumCoord


section Identity

theorem energy_identity (m : ℝ) (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (N : ℕ) (hN : 1 ≤ N) (X : Fin N → Torus d) :
    (N : ℝ) * modE (specKernel a) N X μ =
      (1 / 2) * ‖(Ssum (Yj m ha0 has μ) N X).snd‖ ^ 2 - (1 / 2) * specKernel a 0 := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set g := specKernel a with hg
  set G := Gk a μ with hG
  set Γ0 := ∫ z, Gk a μ z ∂μ with hΓ0
  -- the norm as a sum of squares
  have hs : HasSum (fun i : Idx d => ((Real.sqrt N)⁻¹ * ∑ j, Zfeat μ a i (X j)) ^ 2)
      ((N : ℝ)⁻¹ * ∑ j, ∑ l, (g (X j - X l) - G (X j) - G (X l) + Γ0)) := by
    have hsum : HasSum (fun i : Idx d => ∑ j, ∑ l, Zfeat μ a i (X j) * Zfeat μ a i (X l))
        (∑ j, ∑ l, (g (X j - X l) - G (X j) - G (X l) + Γ0)) :=
      hasSum_sum fun j _ => hasSum_sum fun l _ => hasSum_Zfeat_mul ha0 has μ (X j) (X l)
    have := hsum.mul_left ((N : ℝ)⁻¹)
    convert this using 1
    funext i
    rw [mul_pow, inv_pow, Real.sq_sqrt hNpos.le, sq, Finset.sum_mul_sum]
  have hnorm : ‖(Ssum (Yj m ha0 has μ) N X).snd‖ ^ 2 =
      (N : ℝ)⁻¹ * ∑ j, ∑ l, (g (X j - X l) - G (X j) - G (X l) + Γ0) := by
    rw [FeatSp.norm_sq]
    simp_rw [coord_snd_Ssum m ha0 has μ N X]
    exact hs.tsum_eq
  rw [hnorm]
  -- algebra
  have e1 : ∑ j, ∑ l, g (X j - X l) = ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j) + N * g 0 := by
    have : ∀ j, ∑ l, g (X j - X l) = g 0 + ∑ l ∈ Finset.univ.erase j, g (X j - X l) := by
      intro j
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      simp
    simp_rw [this]
    rw [Finset.sum_add_distrib]
    simp [add_comm]
  have e2 : ∑ j, ∑ l, (g (X j - X l) - G (X j) - G (X l) + Γ0) =
      (∑ j, ∑ l, g (X j - X l)) - N * ∑ j, G (X j) - N * ∑ l, G (X l) + (N : ℝ) ^ 2 * Γ0 := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  rw [e2, e1]
  unfold modE
  have hG1 : ∀ i, ∫ y, g (X i - y) ∂μ = G (X i) := fun i => rfl
  simp_rw [hG1]
  have hΓ : ∫ x, ∫ y, g (x - y) ∂μ ∂μ = Γ0 := rfl
  rw [hΓ]
  field_simp
  ring

end Identity


section GibbsTilt

variable {Ω H E : Type*} [MeasurableSpace Ω] [MeasurableSpace H] [MeasurableSpace E]

theorem gibbs_map_eq (P : Measure Ω) (S : Ω → H) (hS : Measurable S) (T : H → E)
    (hT : Measurable T) (w : H → ℝ) (hw : Measurable w) (hw0 : ∀ v, 0 ≤ w v)
    (Efun : Ω → ℝ) (c0 : ℝ) (hE : ∀ ω, Real.exp (Efun ω) = Real.exp c0 * w (S ω)) :
    ((ENNReal.ofReal (∫ ω, Real.exp (Efun ω) ∂P))⁻¹ •
        P.withDensity (fun ω => ENNReal.ofReal (Real.exp (Efun ω)))).map (fun ω => T (S ω)) =
      (HRS.StaticLimitAux.tiltMeasure w (P.map S)).map T := by
  have hwS : Measurable fun ω => w (S ω) := hw.comp hS
  have hdens : (fun ω => ENNReal.ofReal (Real.exp (Efun ω))) =
      fun ω => ENNReal.ofReal (Real.exp c0) * ENNReal.ofReal (w (S ω)) := by
    funext ω
    rw [hE ω, ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hint : ∫ ω, Real.exp (Efun ω) ∂P = Real.exp c0 * ∫ ω, w (S ω) ∂P := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hE)
  have hint2 : ∫ v, w v ∂(P.map S) = ∫ ω, w (S ω) ∂P := integral_map hS.aemeasurable hw.aestronglyMeasurable
  have hA : 0 ≤ ∫ ω, w (S ω) ∂P := integral_nonneg fun ω => hw0 _
  have hwm : Measurable fun ω => ENNReal.ofReal (w (S ω)) := ENNReal.measurable_ofReal.comp hwS
  have hgm : Measurable fun v => ENNReal.ofReal (w v) := ENNReal.measurable_ofReal.comp hw
  -- the left side
  have he0 : ENNReal.ofReal (Real.exp c0) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hL : (ENNReal.ofReal (∫ ω, Real.exp (Efun ω) ∂P))⁻¹ •
        P.withDensity (fun ω => ENNReal.ofReal (Real.exp (Efun ω))) =
      (ENNReal.ofReal (∫ ω, w (S ω) ∂P))⁻¹ • P.withDensity (fun ω => ENNReal.ofReal (w (S ω))) := by
    rw [hdens]
    have h1 : P.withDensity (fun ω => ENNReal.ofReal (Real.exp c0) * ENNReal.ofReal (w (S ω))) =
        ENNReal.ofReal (Real.exp c0) • P.withDensity (fun ω => ENNReal.ofReal (w (S ω))) :=
      withDensity_smul _ hwm
    rw [h1, smul_smul, hint, ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.mul_inv (Or.inl he0) (Or.inl ENNReal.ofReal_ne_top), mul_comm (ENNReal.ofReal (Real.exp c0))⁻¹,
      mul_assoc, ENNReal.inv_mul_cancel he0 ENNReal.ofReal_ne_top, mul_one]
  rw [hL]
  have hR : HRS.StaticLimitAux.tiltMeasure w (P.map S) =
      (ENNReal.ofReal (∫ ω, w (S ω) ∂P))⁻¹ • (P.withDensity (fun ω => ENNReal.ofReal (w (S ω)))).map S := by
    unfold HRS.StaticLimitAux.tiltMeasure
    rw [hint2]
    congr 1
    exact (HRS.StaticLimitAux.map_withDensity_comp P S hS _ hgm).symm
  rw [hR, Measure.map_smul, Measure.map_smul, Measure.map_map hT hS]
  · rfl
  · exact hT.aemeasurable
  · exact hT.comp hS |>.aemeasurable

end GibbsTilt


section NegCoord

variable {m : ℝ}

theorem NegSobolev.coord_smul' (c : ℝ) (f : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (c • f) k = c * NegSobolev.coord f k := rfl

theorem NegSobolev.coord_sum' {ι : Type*} (s : Finset ι) (f : ι → NegSobolev d m)
    (k : NonzeroLattice d) :
    NegSobolev.coord (∑ j ∈ s, f j) k = ∑ j ∈ s, NegSobolev.coord (f j) k := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (congrArg _ ih).trans rfl

theorem fst_Ssum (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (N : ℕ) (X : Fin N → Torus d) :
    (Ssum (Yj m ha0 has μ) N X).fst = (Real.sqrt N)⁻¹ • ∑ j, Ye m μ (X j) := by
  unfold Ssum
  rw [WithLp.smul_fst]
  congr 1
  have := map_sum (WithLp.fstL 2 ℝ (NegSobolev d m) (FeatSp d)) (fun j => Yj m ha0 has μ (X j))
    Finset.univ
  simp only [WithLp.fstL_apply] at this
  exact this

theorem etaE_eq_aux (hm : (d : ℝ) < 2 * m) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 1 ≤ N) (X : Fin N → Torus d) :
    Real.sqrt N • NegSobolev.ofMeasureDiff m (empirical X) μ =
      (Real.sqrt N)⁻¹ • ∑ j, Ye m μ (X j) := by
  haveI : IsProbabilityMeasure (empirical X) := empirical_isProbabilityMeasure hN X
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine NegSobolev.ext_coord' fun k => ?_
  rw [NegSobolev.coord_smul', NegSobolev.coord_smul', NegSobolev.coord_sum']
  simp only [coord_Ye hm, coord_ofMeasureDiff hm]
  have hint : Torus.measureRealCoeff (empirical X) k = (N : ℝ)⁻¹ * ∑ j, Torus.realMode k (X j) :=
    integral_empirical X (continuous_realMode' k)
  rw [hint, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hs : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  field_simp
  rw [Real.sq_sqrt hNpos.le]
  ring

end NegCoord

end HRS.StaticLimitAux
