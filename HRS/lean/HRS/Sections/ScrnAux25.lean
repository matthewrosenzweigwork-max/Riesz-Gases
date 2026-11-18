import HRS.Sections.ScrnAux24
import HRS.Prob.HilbertMartingale

/-!
# Packet SCRN, part 25: the decomposition `Z = ∑_i N^{-1/2}(f(x_i) - m) + M_T + R` and the vector martingale

For the particle system `X` (strong, filtered, Haar-started), tests `ψ_a` with transported tests `f_a`
(`IsC12Test`, duality identity with `ρ ≡ 1`), the statistic `Z_a = linCoord vol ψ_a (X^{t_a})` decomposes
a.s. as the sum of the Haar initial term, the vector martingale `M_T = √N (∫_0^{t_a} Φ_a dW)_a` and the
remainder `R_a = √N ∫_0^{t_a} flucInteraction(f_a^r, X^r) dr` (`scrn_decomp`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

variable {d : ℕ}

/-- The scaled noise integrand `σ · empiricalNoiseIntegrand`. -/
def scrnPhi {Ω : Type*} {N : ℕ} (D : DynData d) (σ t : ℝ) (f : ℝ → Torus d → ℝ)
    (X : ℝ≥0 → Ω → Config d N) : ℝ → Ω → (Fin N × Fin d) → ℝ :=
  fun r ω k => σ * empiricalNoiseIntegrand D t f X r ω k

lemma scrn_integral_empirical {N : ℕ} (X : Config d N) (f : Torus d → ℝ) :
    ∫ x, f x ∂(empirical X) = (N : ℝ)⁻¹ * ∑ i, f (X i) := by
  unfold empirical
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, Finset.mul_sum]
  · intro i _
    exact integrable_dirac enorm_lt_top

lemma scrn_linCoord_eq {N : ℕ} (hN : 0 < N) (X : Config d N) (ψ : Torus d → ℝ) :
    linCoord (volume : Measure (Torus d)) ψ X = Real.sqrt N * flucPair X (fun _ => (1 : ℝ)) ψ := by
  unfold linCoord flucPair
  rw [pair_empirical hN, scrn_withDensityReal_one, one_div]

section Mart

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℕ} {D : DynData d} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} {ℱ : MeasureTheory.Filtration ℝ mΩ}
  {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}

/-- The vector martingale of the killed integrands and its covariation (Lemma A.27 input). -/
theorem scrn_vector_mart (hF : IsFilteredSolution P ℱ W' W X) {p : ℕ} (ts : Fin p → ℝ)
    (hts : ∀ a, 0 ≤ ts a) {T : ℝ} (hT : ∀ a, ts a ≤ T) (f : Fin p → ℝ → Torus d → ℝ)
    (hC12 : ∀ a, ∃ ft, IsC12Test (ts a) (f a) ft) (σ : ℝ) :
    IsVectorMartingaleWithCovariation P ℱ T
      (vectorItoIntegral P ℱ W' (fun a => killAfter (scrnPhi D σ (ts a) (f a) X) (ts a)))
      (killedCovMatrix (fun a => scrnPhi D σ (ts a) (f a) X) ts) ∧
    ∀ᵐ ω ∂P, ∀ a,
      vectorItoIntegral P ℱ W' (fun a => killAfter (scrnPhi D σ (ts a) (f a) X) (ts a)) T ω a =
        σ * empiricalMartingale P ℱ W' D (ts a) (f a) X ((Real.toNNReal (ts a) : ℝ≥0) : ℝ) ω := by
  have hbase : ∀ a, IsProgressiveL2 P ℱ (empiricalNoiseIntegrand D (ts a) (f a) X) := fun a => by
    obtain ⟨ft, hft⟩ := hC12 a
    exact isProgressiveL2_empiricalNoiseIntegrand (P := P) (ℱ := ℱ) (D := D) hF.progressive
      (hts a) hft
  have hΦ : ∀ a, IsProgressiveL2 P ℱ (scrnPhi D σ (ts a) (f a) X) := fun a =>
    (hbase a).smul σ
  obtain ⟨hmart, hae⟩ := several_times_covariation P hF.brownian
    (fun a => scrnPhi D σ (ts a) (f a) X) hΦ ts hts T hT
  refine ⟨hmart, ?_⟩
  have hsm := fun a => itoIntegral_smul hF.brownian (hbase a) σ
  filter_upwards [hae, ae_all_iff.2 hsm] with ω h1 h2 a
  rw [h1 a]
  have := h2 a (ts a)
  unfold empiricalMartingale
  rw [Real.coe_toNNReal _ (hts a)]
  exact this

end Mart

/-- The `ℝ^p`-valued statistic `Z = (linCoord vol ψ_a (X^{t_a}))_a`. -/
def scrnZ {Ω : Type*} {N p : ℕ} (ψ : Fin p → Torus d → ℝ) (ts : Fin p → ℝ)
    (X : ℝ≥0 → Ω → Config d N) (ω : Ω) : ℝ^p :=
  WithLp.toLp 2 fun a => linCoord (volume : Measure (Torus d)) (ψ a) (X (Real.toNNReal (ts a)) ω)

/-- The transported initial tests `f(y) = (f_a^0(y))_a`. -/
def scrnFvec {p : ℕ} (f : Fin p → ℝ → Torus d → ℝ) (y : Torus d) : ℝ^p :=
  WithLp.toLp 2 fun a => f a 0 y

/-- The remainder vector `R_a = √N ∫_0^{t_a} flucInteraction(f_a^r, X^r) dr`. -/
def scrnRem {Ω : Type*} {N p : ℕ} (D : DynData d) (f : Fin p → ℝ → Torus d → ℝ) (ts : Fin p → ℝ)
    (X : ℝ≥0 → Ω → Config d N) (ω : Ω) : ℝ^p :=
  WithLp.toLp 2 fun a => Real.sqrt N * ∫ r in (0 : ℝ)..(ts a),
    flucInteraction D (f a r) (X (Real.toNNReal r) ω) (fun _ => (1 : ℝ))

lemma scrn_continuous_fvec {p : ℕ} {f : Fin p → ℝ → Torus d → ℝ}
    (hf : ∀ a, Continuous (f a 0)) : Continuous (scrnFvec f) := by
  unfold scrnFvec
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi hf)

lemma scrn_integral_fvec_apply {p : ℕ} {f : Fin p → ℝ → Torus d → ℝ}
    (hf : ∀ a, Continuous (f a 0)) (a : Fin p) :
    (∫ y, scrnFvec f y ∂(volume : Measure (Torus d))) a = ∫ y, f a 0 y ∂(volume : Measure (Torus d)) := by
  have hint : Integrable (scrnFvec f) (volume : Measure (Torus d)) :=
    (scrn_continuous_fvec hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have := (EuclideanSpace.proj a : (ℝ^p) →L[ℝ] ℝ).integral_comp_comm hint
  simpa [scrnFvec] using this.symm

/-- The a.s. decomposition `Z = ∑_i N^{-1/2}(f(x_i) - m) + M_T + R`. -/
theorem scrn_decomp (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} {ℱ : MeasureTheory.Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hF : IsFilteredSolution P ℱ W' W X) {T : ℝ}
    (hsolT : IsStrongSolution P (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) T X₀ W X)
    {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc 0 T) (ψ : Fin p → Torus d → ℝ)
    (hψ2 : ∀ a, Torus.IsCk 2 (ψ a)) (f : Fin p → ℝ → Torus d → ℝ)
    (hf : ∀ a, (ts a = 0 ∧ f a = fun _ => ψ a) ∨ (0 < ts a ∧ IsClassicalAdjointSolution
      (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) (fun _ _ => (1 : ℝ)) (ts a) (ψ a) (f a)))
    (hC12 : ∀ a, ∃ ft, IsC12Test (ts a) (f a) ft) (hfc : ∀ a, Continuous (f a 0)) :
    ∀ᵐ ω ∂P, scrnZ ψ ts X ω =
      (∑ i : Fin N, (Real.sqrt N)⁻¹ • (scrnFvec f (X 0 ω i) -
          ∫ y, scrnFvec f y ∂(volume : Measure (Torus d)))) +
        vectorItoIntegral P ℱ W' (fun a => killAfter
          (scrnPhi (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) (Real.sqrt N) (ts a) (f a) X) (ts a)) T ω +
        scrnRem (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) f ts X ω := by
  set D := PDE.mfData d s hs0 hsd (fun _ => 0) β hβ with hD
  have hN0 : 0 < N := by omega
  obtain ⟨-, hM⟩ := scrn_vector_mart (D := D) hF ts (fun a => (hts a).1) (fun a => (hts a).2) f hC12
    (Real.sqrt N)
  have hdual : ∀ a, ∀ᵐ ω ∂P,
      flucPair (X (Real.toNNReal (ts a)) ω) (fun _ => (1 : ℝ)) (ψ a) =
        flucPair (X 0 ω) (fun _ => (1 : ℝ)) (f a 0) +
        empiricalMartingale P ℱ W' D (ts a) (f a) X ((Real.toNNReal (ts a) : ℝ≥0) : ℝ) ω +
        ∫ r in (0 : ℝ)..(ts a), flucInteraction D (f a r) (X (Real.toNNReal r) ω) (fun _ => (1 : ℝ)) :=
    fun a => scrn_dual_one hd hs0 hsd β hβ hN hF hsolT (hts a) (hψ2 a) (hf a)
  filter_upwards [hM, ae_all_iff.2 hdual] with ω hMω hDω
  ext a
  have hsq : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN0)
  have hsq2 : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by positivity)
  have hmean := scrn_integral_fvec_apply (d := d) hfc a
  have h1 : flucPair (X 0 ω) (fun _ => (1 : ℝ)) (f a 0) =
      (N : ℝ)⁻¹ * ∑ i, f a 0 (X 0 ω i) - ∫ y, f a 0 y ∂(volume : Measure (Torus d)) := by
    unfold flucPair
    rw [pair_empirical hN0, scrn_withDensityReal_one]
    rfl
  have hZ : scrnZ ψ ts X ω a = Real.sqrt N * flucPair (X (Real.toNNReal (ts a)) ω) (fun _ => (1 : ℝ)) (ψ a) := by
    unfold scrnZ
    simp only [PiLp.toLp_apply]
    exact scrn_linCoord_eq hN0 _ _
  rw [hZ, hDω a, h1]
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, WithLp.ofLp_sum, Finset.sum_apply,
    smul_eq_mul]
  rw [hmean]
  simp only [scrnFvec, PiLp.toLp_apply, hMω a, scrnRem]
  have hsumcancel : ∑ i : Fin N, (Real.sqrt N)⁻¹ * (f a 0 (X 0 ω i) -
      ∫ y, f a 0 y ∂(volume : Measure (Torus d))) =
      Real.sqrt N * ((N : ℝ)⁻¹ * ∑ i, f a 0 (X 0 ω i) - ∫ y, f a 0 y ∂(volume : Measure (Torus d))) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hNn : (N : ℝ) ≠ 0 := by positivity
    field_simp
    rw [Real.sq_sqrt (Nat.cast_nonneg N)]
  rw [hsumcancel]
  ring

/-- Law and independence of the coordinates of a Haar-distributed configuration. -/
lemma scrn_coord_indep {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} {Y : Ω → Config d N} (hY : Measurable Y)
    (hlaw : P.map Y = Measure.pi (fun _ : Fin N => (volume : Measure (Torus d)))) :
    iIndepFun (fun (i : Fin N) ω => Y ω i) P ∧
      ∀ i : Fin N, law P (fun ω => Y ω i) = (volume : Measure (Torus d)) := by
  classical
  have hcoord : ∀ i : Fin N, P.map (fun ω => Y ω i) = (volume : Measure (Torus d)) := by
    intro i
    have : (fun ω => Y ω i) = (Function.eval i) ∘ Y := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply i) hY, hlaw, Measure.pi_map_eval]
    simp
  refine ⟨?_, hcoord⟩
  refine (iIndepFun_iff_map_fun_eq_pi_map (f := fun (i : Fin N) ω => Y ω i)
    (fun i => ((measurable_pi_apply i).comp hY).aemeasurable)).2 ?_
  simp only [hcoord]
  exact hlaw

/-- The abstract assembly: the law of `Z` is within `E‖R‖ + Lindeberg + ½ E∫‖Σ-Σ̄‖` (in `d₃`) of the
Gaussian with covariance `Cov_Haar(f) + ∫ Σ̄`. -/
theorem scrn_assembly (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} {ℱ : MeasureTheory.Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hF : IsFilteredSolution P ℱ W' W X) {T : ℝ} (hT : 0 ≤ T)
    (hsolT : IsStrongSolution P (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) T X₀ W X)
    (hlaw : P.map (X 0) = Measure.pi (fun _ : Fin N => (volume : Measure (Torus d))))
    {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc 0 T) (ψ : Fin p → Torus d → ℝ)
    (hψ2 : ∀ a, Torus.IsCk 2 (ψ a)) (f : Fin p → ℝ → Torus d → ℝ)
    (hf : ∀ a, (ts a = 0 ∧ f a = fun _ => ψ a) ∨ (0 < ts a ∧ IsClassicalAdjointSolution
      (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) (fun _ _ => (1 : ℝ)) (ts a) (ψ a) (f a)))
    (hC12 : ∀ a, ∃ ft, IsC12Test (ts a) (f a) ft) (hfc : ∀ a, Continuous (f a 0))
    (hRint : Integrable (scrnRem (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) f ts X) P) :
    d3DistE (law P (scrnZ ψ ts X))
        (multivariateGaussian 0
          ((Matrix.of fun a b => ∫ y, (scrnFvec f y a - (∫ y', scrnFvec f y' ∂(volume : Measure (Torus d))) a) *
              (scrnFvec f y b - (∫ y', scrnFvec f y' ∂(volume : Measure (Torus d))) b)
              ∂(volume : Measure (Torus d))) +
            integratedCov T (scrnSig ts (scrnGc ts f) (2 * (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ).invβ)))) ≤
      ENNReal.ofReal (∫ ω, ‖scrnRem (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) f ts X ω‖ ∂P +
        (1 + Real.sqrt 3) / (6 * Real.sqrt N) * ∫ y, ‖scrnFvec f y -
          ∫ y', scrnFvec f y' ∂(volume : Measure (Torus d))‖ ^ 3 ∂(volume : Measure (Torus d)) +
        (1 / 2) * covDiscrepancyMatrix P T
          (killedCovMatrix (fun a => scrnPhi (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) (Real.sqrt N)
            (ts a) (f a) X) ts)
          (scrnSig ts (scrnGc ts f) (2 * (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ).invβ))) := by
  set D := PDE.mfData d s hs0 hsd (fun _ => 0) β hβ with hD
  have hN1 : 1 ≤ N := by omega
  have hXm : Measurable (X 0) := (hsolT.adapted 0)
  obtain ⟨hmart, -⟩ := scrn_vector_mart (D := D) hF ts (fun a => (hts a).1) (fun a => (hts a).2) f hC12
    (Real.sqrt N)
  -- Σ̄ is a deterministic covariance density
  have hGm : ∀ a, Measurable fun p : ℝ × Torus d => scrnGc ts f a p.1 p.2 := by
    intro a
    obtain ⟨ft, hft⟩ := hC12 a
    have hm := measurable_grad_clamp (hts a).1 hft
    have e : (fun p : ℝ × Torus d => scrnGc ts f a p.1 p.2) = fun p =>
        if p.1 ∈ Set.Icc (0 : ℝ) (ts a) then Torus.grad (f a (clampTI (ts a) p.1)) p.2 else 0 := by
      funext p
      unfold scrnGc
      split_ifs with h
      · rw [clampTI_of_mem h]
      · rfl
    rw [e]
    exact Measurable.ite (measurableSet_Icc.preimage measurable_fst) hm measurable_const
  have hGb : ∀ a r x, ‖scrnGc ts f a r x‖ ≤ ∑ a', |(grad_bound (hts a').1 (hC12 a').choose_spec).choose| := by
    intro a r x
    have hnn : ∀ a', 0 ≤ |(grad_bound (hts a').1 (hC12 a').choose_spec).choose| := fun a' => abs_nonneg _
    refine le_trans ?_ (Finset.single_le_sum (fun a' _ => hnn a') (Finset.mem_univ a))
    unfold scrnGc
    split_ifs with h
    · exact ((grad_bound (hts a).1 (hC12 a).choose_spec).choose_spec r h x).trans (le_abs_self _)
    · simp only [norm_zero]; exact hnn a
  have hc : 0 ≤ 2 * D.invβ := by have := D.hβ; positivity
  have hsb := scrnSig_isDet (ts := ts) (G := scrnGc ts f) (c := 2 * D.invβ) hGm hGb hc T
  -- the initial coordinates
  obtain ⟨hind, hlawi⟩ := scrn_coord_indep hXm hlaw
  have hxmeas : ∀ i : Fin N, Measurable[ℱ 0] (fun ω => X 0 ω i) := fun i =>
    (measurable_pi_apply i).comp (hF.adapted 0)
  have hf3 : MemLp (scrnFvec f) 3 (volume : Measure (Torus d)) :=
    (scrn_continuous_fvec hfc).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have key := iid_initial_sampling P ℱ T hT _ _ hmart _ hsb (volume : Measure (Torus d)) hN1
    (fun i ω => X 0 ω i) hxmeas hind hlawi (scrnFvec f) hf3 (scrnRem D f ts X) hRint
  have hdec := scrn_decomp hd hs0 hsd β hβ hN hF hsolT ts hts ψ hψ2 f hf hC12 hfc
  have hlaweq : law P (scrnZ ψ ts X) = law P (fun ω => ∑ i : Fin N, (Real.sqrt N)⁻¹ •
      (scrnFvec f (X 0 ω i) - ∫ y, scrnFvec f y ∂(volume : Measure (Torus d))) +
      vectorItoIntegral P ℱ W' (fun a => killAfter (scrnPhi D (Real.sqrt N) (ts a) (f a) X) (ts a)) T ω +
      scrnRem D f ts X ω) := Measure.map_congr hdec
  rw [hlaweq]
  exact key

end HRS
