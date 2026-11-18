import HRS.ME.FamVC
import HRS.ME.RetPathLaw
import HRS.Main.HeadlineEquilibrium
import HRS.Sections.Q38bAux4
import HRS.MH.CondOuDefs
import HRS.ME.UIPathTightP1
import HRS.Main.MeanPartMetricEval

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS.MH.CondOuPackets

open HRS HRS.Main HRS.LZ

variable {d : ℕ}

/-- shift by `mk (e_j / (2 k_j))` flips the sign of `cos(2π k·x)`. -/
theorem p_cp3_cos_shift (k : Lattice d) (j : Fin d) (hj : k j ≠ 0) (x : Torus d) :
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

/-- first marginal of the homogeneous Gibbs law is orthogonal to `cos_k`. -/
theorem p_cp3_pair_firstMarginal_cosMode {s : ℝ} (β : ℝ) (k : Lattice d) (hk : k ≠ 0) {N : ℕ}
    (hN : 1 ≤ N) :
    pair (firstMarginal (canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β))
      (Torus.cosMode k) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hk (funext h)
  set G := canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β with hG
  have h0 : 0 < N := hN
  have hc : Continuous (Torus.cosMode k) := Complex.continuous_re.comp (Torus.continuous_mode _)
  set t : Torus d := Torus.mk (EuclideanSpace.single j (1 / (2 * (k j : ℝ)))) with ht
  have hmeas : Measurable (fun X : Config d N => X ⟨0, h0⟩) := measurable_pi_apply _
  have h1 : pair (firstMarginal G) (Torus.cosMode k) = ∫ X, Torus.cosMode k (X ⟨0, h0⟩) ∂G := by
    unfold pair firstMarginal
    rw [dif_pos h0, integral_map hmeas.aemeasurable hc.aestronglyMeasurable]
  rw [h1]
  have hinv : G.map (shiftEquiv t : Config d N ≃ᵐ Config d N) = G :=
    HRS.StaticLimitsAux.gibbs_inv _ _ _ _
  have h2 : ∫ X, Torus.cosMode k (X ⟨0, h0⟩) ∂G =
      ∫ X, Torus.cosMode k ((shiftEquiv t : Config d N ≃ᵐ Config d N) X ⟨0, h0⟩) ∂G := by
    conv_lhs => rw [← hinv]
    exact (integral_map_equiv (shiftEquiv t : Config d N ≃ᵐ Config d N)
      (fun X : Config d N => Torus.cosMode k (X ⟨0, h0⟩)))
  have h3 : ∫ X, Torus.cosMode k ((shiftEquiv t : Config d N ≃ᵐ Config d N) X ⟨0, h0⟩) ∂G =
      - ∫ X, Torus.cosMode k (X ⟨0, h0⟩) ∂G := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    show Torus.cosMode k (t + X ⟨0, h0⟩) = _
    exact p_cp3_cos_shift k j hj _
  linarith

/-- (P2b) the `E_m`-evaluation of the centred field against `ψ_k` is the linear coordinate. -/
theorem p_cp3_eval_zetaE_cosTest (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) {m : ℝ} (hm : (d : ℝ) < 2 * m) {N : ℕ} (hN : 1 ≤ N) (k : Lattice d)
    (hk : k ≠ 0) (x : Config d N) :
    NegSobolev.eval (zetaE m (canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β) x)
        (PDE.cosTest k) =
      linCoord (volume : Measure (Torus d)) (PDE.cosTest k) x := by
  haveI := HRS.StaticLimitsAux.gibbs_prob (N := N) hd hs0 hsd 0 β hβ.le
  have hex : IsExchangeable (canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β) :=
    HRS.ME.FamV.canonicalGibbs_isExchangeable _ _ (fun x => periodicRiesz_neg x) β
  have h1 : ∀ F : NegSobolev d m, NegSobolev.eval F (PDE.cosTest k) =
      Real.sqrt 2 * NegSobolev.eval F (Torus.cosMode k) := by
    intro F
    unfold NegSobolev.eval
    rw [← tsum_mul_left]
    refine tsum_congr fun l => ?_
    have : Torus.funRealCoeff (PDE.cosTest k) l = Real.sqrt 2 * Torus.funRealCoeff (Torus.cosMode k) l := by
      unfold Torus.funRealCoeff PDE.cosTest
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [this]; ring
  rw [h1, HRS.ME.FamV.eval_zetaE_cos hm k hN, meanEmpirical_eq_firstMarginal _ hex hN,
    p_cp3_pair_firstMarginal_cosMode β k hk hN, pair_empirical (by omega : 0 < N) x]
  unfold linCoord
  have hp : pair (volume : Measure (Torus d)) (PDE.cosTest k) = 0 := mp_integral_cosTest k hk
  have hs : ∑ i, PDE.cosTest k (x i) = Real.sqrt 2 * ∑ i, Torus.cosMode k (x i) := by
    rw [Finset.mul_sum]; rfl
  rw [hp, hs]
  ring

theorem condou_window_law (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) {N : ℕ} (hN : 2 ≤ N) {m : ℝ} (hm : (d : ℝ) < 2 * m)
    (t : ℝ) (ht : 0 ≤ t) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : IsStationaryGibbsFlow P s hs0 hsd (fun _ => (0 : ℝ)) β hβ t X₀ W X) :
    (law P (windowZeta m t 0 P X)).map (condouEval2 d m t ht k) =
      law P (fun ω => (WithLp.toLp 2 ![
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X 0 ω),
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X (Real.toNNReal t) ω)] :
        EuclideanSpace ℝ (Fin 2))) := by
  have hX' : IsStationaryGibbsFlow P s hs0 hsd (fun _ => (0 : ℝ)) β hβ (0 + t) X₀ W X := by
    rw [zero_add]; exact hX
  have hV : Torus.IsSmooth (fun _ : Torus d => (0 : ℝ)) := d1_isSmooth_const 0
  obtain ⟨hstat, hmeas, -⟩ := HRS.MD.EQInterp.flow_facts hd hs0 hsd _ hV hβ hN P hX'
  have hcont := HRS.MD.EQInterp.windowZeta_cont_ae hd hs0 hsd _ hV hβ hN (le_refl (0 : ℝ)) ht P hX' hm
  have hW : AEMeasurable (windowZeta m t 0 P X) P :=
    HRS.MD.EQInterp.windowZeta_aemeasurable hd hs0 hsd _ hV hβ hN (le_refl (0 : ℝ)) ht P hX' hm
  have hae : (condouEval2 d m t ht k ∘ windowZeta m t 0 P X) =ᵐ[P]
      (fun ω => (WithLp.toLp 2 ![
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X 0 ω),
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X (Real.toNNReal t) ω)] :
        EuclideanSpace ℝ (Fin 2))) := by
    filter_upwards [hcont] with ω hω
    show condouEval2 d m t ht k (windowZeta m t 0 P X ω) = _
    rw [condouEval2_apply, HRS.MD.EQInterp.windowZeta_at' P X ω hω,
      HRS.MD.EQInterp.windowZeta_at' P X ω hω]
    have e0 : Real.toNNReal (0 + ((HRS.ME.FamV.t0 ht : Set.Icc (0 : ℝ) t) : ℝ)) = 0 := by
      simp [HRS.ME.FamV.t0]
    have e1 : Real.toNNReal (0 + ((endpt ht : Set.Icc (0 : ℝ) t) : ℝ)) = Real.toNNReal t := by
      simp [endpt]
    rw [e0, e1, hstat 0 (by simp [ht]), hstat _ (by rw [Real.coe_toNNReal _ ht]; simp),
      p_cp3_eval_zetaE_cosTest hd hs0 hsd hβ hm (by omega) k hk,
      p_cp3_eval_zetaE_cosTest hd hs0 hsd hβ hm (by omega) k hk]
  have hR : Measurable (condouEval2 d m t ht k) := (condouEval2 d m t ht k).continuous.measurable
  calc (law P (windowZeta m t 0 P X)).map (condouEval2 d m t ht k)
      = P.map (condouEval2 d m t ht k ∘ windowZeta m t 0 P X) :=
        AEMeasurable.map_map_of_aemeasurable hR.aemeasurable hW
    _ = _ := Measure.map_congr hae

end HRS.MH.CondOuPackets
