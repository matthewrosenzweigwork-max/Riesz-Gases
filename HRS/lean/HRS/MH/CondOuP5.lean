import HRS.ME.FamVC
import HRS.ME.RetPathLaw
import HRS.Main.HeadlineEquilibrium
import HRS.Sections.Q38bAux4
import HRS.MH.CondOuDefs
import HRS.ME.UIPathTightP3a
import HRS.Main.MeanPartMetricEval

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS.MH.CondOuPackets

open HRS HRS.Main HRS.LZ

variable {d : ℕ}

/-- The shift `t = mk(e_j / (2 k_j))` flips the sign of `cos(2π k·x)` (copy of `HRS.MH.CondOuP.cos_shift`). -/
theorem p_cp5_cos_shift (k : Lattice d) (j : Fin d) (hj : k j ≠ 0) (x : Torus d) :
    Torus.cosMode k (Torus.mk (EuclideanSpace.single j (1 / (2 * (k j : ℝ)))) + x) =
      - Torus.cosMode k x := by
  have hj' : (k j : ℝ) ≠ 0 := by exact_mod_cast hj
  conv_lhs => rw [← Torus.mk_rep x, ← Torus.mk_add, Torus.cosMode_mk]
  conv_rhs => rw [← Torus.mk_rep x, Torus.cosMode_mk]
  rw [Torus.dot_add]
  have : Lattice.dot k (EuclideanSpace.single j (1 / (2 * (k j : ℝ)))) = 1/2 := by
    simp only [Lattice.dot, EuclideanSpace.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    field_simp
  rw [this, mul_add, show 2 * Real.pi * (1/2 : ℝ) = Real.pi by ring, add_comm Real.pi,
    Real.cos_add_pi]

theorem p_cp5_pair_firstMarginal_cos {s : ℝ} (β : ℝ) (k : Lattice d) (hk : k ≠ 0) {N : ℕ} :
    pair (firstMarginal (canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β)) (PDE.cosTest k) = 0 := by
  by_cases hN : 0 < N
  · obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hk (funext h)
    set G := canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β with hG
    set t : Torus d := Torus.mk (EuclideanSpace.single j (1 / (2 * (k j : ℝ)))) with ht
    have hinv : G.map (shiftEquiv t : Config d N ≃ᵐ Config d N) = G :=
      StaticLimitsAux.gibbs_inv (periodicRiesz d s) 0 β t
    have hcont : Continuous (PDE.cosTest k) := by
      unfold PDE.cosTest
      exact continuous_const.mul (Complex.continuous_re.comp (Torus.continuous_mode _))
    have hmeas : Measurable (fun X : Config d N => X ⟨0, hN⟩) := measurable_pi_apply _
    unfold pair firstMarginal
    rw [dif_pos hN, integral_map hmeas.aemeasurable hcont.aestronglyMeasurable]
    have h2 : ∫ X, PDE.cosTest k (X ⟨0, hN⟩) ∂(G.map (shiftEquiv t : Config d N ≃ᵐ Config d N)) =
        ∫ X, PDE.cosTest k ((shiftEquiv t : Config d N ≃ᵐ Config d N) X ⟨0, hN⟩) ∂G :=
      (shiftEquiv t : Config d N ≃ᵐ Config d N).measurableEmbedding.integral_map _
    rw [hinv] at h2
    have h3 : ∀ X : Config d N, PDE.cosTest k ((shiftEquiv t : Config d N ≃ᵐ Config d N) X ⟨0, hN⟩)
        = - PDE.cosTest k (X ⟨0, hN⟩) := by
      intro X
      simp only [PDE.cosTest, shiftEquiv_apply, ht, p_cp5_cos_shift k j hj]
      ring
    simp only [h3, integral_neg] at h2
    linarith
  · have : N = 0 := by omega
    subst this
    unfold firstMarginal
    simp [pair]

theorem p_cp5_eval_zetaE_cosTest (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {m : ℝ} (hm : (d : ℝ) < 2 * m) {N : ℕ} (hN : 1 ≤ N) (k : Lattice d) (hk : k ≠ 0)
    (x : Config d N) :
    NegSobolev.eval (zetaE m (canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β) x)
        (PDE.cosTest k) =
      linCoord (volume : Measure (Torus d)) (PDE.cosTest k) x := by
  haveI : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β) :=
    HRS.MD.EQLawFlow.eqlaw_gibbs_prob hd hs0 hsd (d1_isSmooth_const 0) hβ hN
  haveI := empirical_isProbabilityMeasure (by omega : 0 < N) x
  haveI := isProbabilityMeasure_meanEmpirical
    (canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β) hN
  have hex : IsExchangeable (canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β) :=
    HRS.ME.FamV.canonicalGibbs_isExchangeable _ _ (fun x => periodicRiesz_neg x) β
  unfold zetaE linCoord
  rw [mp_eval_smul, NegSobolev.eval_ofMeasureDiff hm _ _ _ (mp_isCk_top_cosTest k),
    meanEmpirical_eq_firstMarginal _ hex hN, p_cp5_pair_firstMarginal_cos β k hk,
    pair_empirical (by omega : 0 < N)]
  have h0 : pair (volume : Measure (Torus d)) (PDE.cosTest k) = 0 := mp_integral_cosTest k hk
  rw [h0]
  simp

/-- The window `ζ^{0+·}` evaluated by `condouEval2` is a.s. the pair of linear coordinates. -/
theorem p_cp5_pair_ae (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) {N : ℕ} (hN : 2 ≤ N) {m : ℝ} (hm : (d : ℝ) < 2 * m)
    (t : ℝ) (ht : 0 ≤ t) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : IsStationaryGibbsFlow P s hs0 hsd (fun _ => (0 : ℝ)) β hβ (0 + t) X₀ W X) :
    ∀ᵐ ω ∂P, condouEval2 d m t ht k (windowZeta m t 0 P X ω) =
      (WithLp.toLp 2 ![
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X 0 ω),
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X (Real.toNNReal t) ω)] :
        EuclideanSpace ℝ (Fin 2)) := by
  have hV : Torus.IsSmooth (fun _ : Torus d => (0 : ℝ)) := d1_isSmooth_const 0
  obtain ⟨hstat, hmeas, -⟩ := HRS.MD.EQInterp.flow_facts hd hs0 hsd _ hV hβ hN P hX
  have hcont := HRS.MD.EQInterp.windowZeta_cont_ae hd hs0 hsd _ hV hβ hN (le_refl (0 : ℝ)) ht P hX hm
  filter_upwards [hcont] with ω hω
  have key : ∀ τ : Set.Icc (0 : ℝ) t,
      NegSobolev.eval ((windowZeta m t 0 P X ω).at' τ) (PDE.cosTest k) =
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X (Real.toNNReal τ) ω) := by
    intro τ
    rw [HRS.MD.EQInterp.windowZeta_at' P X ω hω τ,
      hstat _ (by rw [Real.coe_toNNReal _ (by linarith [τ.2.1])]; linarith [τ.2.2]),
      p_cp5_eval_zetaE_cosTest hd hs0 hsd hβ hm (by omega) k hk, zero_add]
  rw [condouEval2_apply, key, key]
  have e0 : Real.toNNReal ((HRS.ME.FamV.t0 ht : Set.Icc (0 : ℝ) t) : ℝ) = 0 := by
    simp [HRS.ME.FamV.t0]
  rw [e0]
  rfl

/-- The covariance matrix of the pair of stationary Gaussian coordinates. -/
theorem p_cp5_lagCov (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) (t : ℝ) (ht : 0 ≤ t) :
    PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ)
      (fun _ => (1 : ℝ)) ![0, t] (fun _ => PDE.cosTest k) = condouCov d s β k t := by
  obtain ⟨K, hK1, hK⟩ := mp_cosTest_eq_realMode k hk
  have hφ : (fun _ : Fin 2 => PDE.cosTest k) = fun _ => Torus.realMode K := by
    funext _; exact hK
  have hτ : ∀ a, 0 ≤ (![0, t] : Fin 2 → ℝ) a := by
    intro a; fin_cases a
    · exact le_rfl
    · exact ht
  rw [hφ, q38b_lagCov_eq hd hs0 hsd hβ K ![0, t] hτ]
  have hc : rieszCoeff d s K.1 = rieszCoeff d s k := by
    rcases hK1 with h | h
    · rw [h]
    · rw [h, rieszCoeff_neg]
  have hr : q38b_rate d s β K = PDE.transientRate d s β k := by
    unfold q38b_rate PDE.transientRate
    rcases hK1 with h | h
    · rw [h]
    · rw [h, rieszCoeff_neg, enorm_neg]
  rw [hr, hc]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [condouCov, abs_of_nonneg ht]

theorem p_cp5_gauss_window_ae {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) {m : ℝ} (t : ℝ) (ht : 0 ≤ t)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) m Z) :
    ∀ᵐ ω ∂P', condouEval2 d m t ht k (windowPath m t 0 Z ω) =
      (WithLp.toLp 2 fun a : Fin 2 => NegSobolev.eval (Z (![0, t] a) ω) ((fun _ => PDE.cosTest k) a) :
        EuclideanSpace ℝ (Fin 2)) := by
  filter_upwards [hZ.cont] with ω hω
  rw [condouEval2_apply, HRS.MD.EQInterp.windowPath_at' Z ω hω, HRS.MD.EQInterp.windowPath_at' Z ω hω]
  congr 1
  ext a
  fin_cases a
  · simp [HRS.ME.FamV.t0]
  · simp [endpt]


theorem condou_stationary_joint (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) (t : ℝ) (ht : 0 ≤ t)
    (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X₀ : ∀ n, Ω n → Config d (n + 2)) (W : ∀ n, ℝ≥0 → Ω n → (Fin (n + 2) → Euc d))
    (X : ∀ n, ℝ≥0 → Ω n → Config d (n + 2))
    (hX : ∀ n, IsStationaryGibbsFlow (P n) s hs0 hsd (fun _ => (0 : ℝ)) β hβ t (X₀ n) (W n) (X n)) :
    ConvergesInLaw
      (fun n : ℕ => law (P n) (fun ω => (WithLp.toLp 2 ![
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X n 0 ω),
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X n (Real.toNNReal t) ω)] :
        EuclideanSpace ℝ (Fin 2))))
      (multivariateGaussian 0 (condouCov d s β k t)) := by
  set m : ℝ := (d : ℝ) + 3 with hmdef
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m := by
    rw [hmdef]; refine max_lt ?_ ?_ <;> linarith
  have hmd : (d : ℝ) < 2 * m := by rw [hmdef]; linarith
  have hV : Torus.IsSmooth (fun _ : Torus d => (0 : ℝ)) := d1_isSmooth_const 0
  have hρ := q38b_isThermal hd hs0 hsd β
  obtain ⟨Ω', _, P', _, Z, hZ⟩ := stationaryField_exists hd hs0 hsd hβ _ hV _ hρ m hm
  have hX' : ∀ n, IsStationaryGibbsFlow (P n) s hs0 hsd (fun _ => (0 : ℝ)) β hβ (0 + t) (X₀ n) (W n)
      (X n) := fun n => by rw [zero_add]; exact hX n
  have hconv := HRS.ME.UIPathTight.stationary_windows_converge hd hs0 hsd hβ _ hV _ hρ m hm t ht
    Ω P X₀ W X hX' Ω' P' Z hZ
  set cE := condouEval2 d m t ht k with hcE
  -- the pair as an a.e. image of the window
  have hae : ∀ n, ∀ᵐ ω ∂(P n), cE (windowZeta m t 0 (P n) (X n) ω) =
      (WithLp.toLp 2 ![
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X n 0 ω),
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X n (Real.toNNReal t) ω)] :
        EuclideanSpace ℝ (Fin 2)) := fun n =>
    p_cp5_pair_ae hd hs0 hsd hβ k hk (by omega) hmd t ht (P n) (hX' n)
  have hmeasn : ∀ n, AEMeasurable (fun ω => (WithLp.toLp 2 ![
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X n 0 ω),
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X n (Real.toNNReal t) ω)] :
        EuclideanSpace ℝ (Fin 2))) (P n) := fun n =>
    (cE.continuous.measurable.comp_aemeasurable (hconv.forall_aemeasurable n)).congr (hae n)
  -- Gaussian side
  have hgl := hZ.gaussian 2 ![0, t] (fun _ => PDE.cosTest k)
    (by intro a; fin_cases a; exacts [le_rfl, ht]) (fun _ => mp_isCk_top_cosTest k)
  rw [p_cp5_lagCov hd hs0 hsd hβ k hk t ht] at hgl
  have hgae := p_cp5_gauss_window_ae hs0 hsd hβ k t ht P' Z hZ
  have hlim : AEMeasurable (windowPath m t 0 Z) P' := hconv.aemeasurable_limit
  have hgauss : ∀ f : EuclideanSpace ℝ (Fin 2) →ᵇ ℝ,
      ∫ x, f x ∂(multivariateGaussian 0 (condouCov d s β k t)) = ∫ ω, f (cE (windowPath m t 0 Z ω)) ∂P' := by
    intro f
    rw [← hgl]
    have hmZ : AEMeasurable (fun ω => (WithLp.toLp 2 fun a : Fin 2 =>
        NegSobolev.eval (Z (![0, t] a) ω) ((fun _ => PDE.cosTest k) a) : EuclideanSpace ℝ (Fin 2))) P' :=
      (cE.continuous.measurable.comp_aemeasurable hlim).congr hgae
    rw [law, integral_map hmZ f.continuous.aestronglyMeasurable]
    exact integral_congr_ae (hgae.mono fun ω hω => congrArg f hω.symm)
  intro f
  let fc : PathSpace d m t →ᵇ ℝ := f.compContinuous ⟨cE, cE.continuous⟩
  have h1 := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hconv.forall_aemeasurable
    hconv.aemeasurable_limit).1 hconv fc
  rw [hgauss f]
  have e : ∀ n, ∫ x, f x ∂(law (P n) (fun ω => (WithLp.toLp 2 ![
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X n 0 ω),
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X n (Real.toNNReal t) ω)] :
        EuclideanSpace ℝ (Fin 2)))) = ∫ ω, fc (windowZeta m t 0 (P n) (X n) ω) ∂(P n) := by
    intro n
    rw [law, integral_map (hmeasn n) f.continuous.aestronglyMeasurable]
    exact integral_congr_ae ((hae n).mono fun ω hω => by simp only [fc, BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk, hω])
  simp only [e]
  exact h1

end HRS.MH.CondOuPackets
