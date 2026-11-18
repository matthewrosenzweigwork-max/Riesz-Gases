import HRS.MC.E213U21a
import HRS.MC.E213U10S
import HRS.MC.E213U12d
import HRS.MC.E213U14b
import HRS.MC.E213U16x
import HRS.MC.E213U15b
import HRS.MC.E213U19b
import HRS.MC.E213U9
import HRS.MC.E213U8
import HRS.MC.E213U7b
import HRS.MC.E213U6
import HRS.MC.E213U5b
import HRS.MC.E213U1a
import HRS.MC.E213U1b
import HRS.MD.EQLawZeta

/-!
# Packet e213u21 (part b): bridging lemmas for the assembly of `core_bound`

* `u21_memCb_mono`: `MemCb 5 → MemCb 3`;
* `u21_windowZeta_aem`: a.e. measurability of `windowZeta` for a prepared realisation;
* `u21_init_particle`: the initial term of the window identity is the integral against the modulated Gibbs measure;
* `u21_integrable_apply`: `ω ↦ u (D³Φ(Z ω))` is integrable;
* `u21_Kproj_apply`: pointwise evaluation of the symmetrised tensor `K_a` on `D³Φ(z)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U21

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

theorem u21_memCb_mono {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {Φ : B → ℝ} (h : MemCb 5 Φ) :
    MemCb 3 Φ :=
  ⟨h.1.of_le (by exact_mod_cast (by norm_num : (3 : ℕ) ≤ 5)), fun j hj => h.2 j (hj.trans (by norm_num))⟩

section Part

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u21_windowZeta_aem (hE : EdgeworthHyp S β₀ m) {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization (regime S β₀ hE).D P
      (modulatedGibbs (periodicRiesz d (regime S β₀ hE).D.s) N (regime S β₀ hE).β₀
        (withDensityReal (regime S β₀ hE).ρ₀)) X₀ W X)
    (T a : ℝ) (hT : 0 < T) (ha : 0 ≤ a) : AEMeasurable (HRS.Main.windowZeta m T a P X) P := by
  have hm : 3 * (d : ℝ) + 8 < m := hE.m_gt
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm2 : (d : ℝ) < 2 * m := by linarith
  have hS := hreal.solution (a + T)
  have hN0 : 0 < N := by omega
  have heq : HRS.Main.windowZeta m T a P X = fun ω => HRS.MD.EQLawPath.eqlaw_pathOf d m T (fun τ : Set.Icc (0 : ℝ) T =>
      zetaE m (P.map (X (Real.toNNReal (a + τ)))) (X (Real.toNNReal (a + τ)) ω)) := by
    funext ω; rfl
  rw [heq]
  refine HRS.MD.EQLawPath.eqlaw_aemeasurable_pathOf P T _ (fun τ => ?_) ?_
  · haveI : IsProbabilityMeasure (P.map (X (Real.toNNReal (a + τ)))) :=
      (Measure.isProbabilityMeasure_map_iff (hS.adapted _).aemeasurable).2 inferInstance
    exact (HRS.MD.EQLawPath.eqlaw_continuous_zetaE hm2 (by omega) _).measurable.comp (hS.adapted _)
  · filter_upwards [hS.cont] with ω hω
    have hζ := HRS.MC.Sec7.S7FCW12.s7fcw12_zetaAt_continuousOn m hm2 P X hS.adapted hS.cont hN0 ω
      (fun i => (hω i).comp continuous_real_toNNReal) (Set.Icc 0 (a + T))
    refine hζ.comp_continuous (continuous_const.add continuous_subtype_val) (fun τ => ?_)
    exact ⟨by linarith [τ.2.1], by linarith [τ.2.2]⟩

theorem u21_init_particle (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization (regime S β₀ hE).D P
      (modulatedGibbs (periodicRiesz d (regime S β₀ hE).D.s) N (regime S β₀ hE).β₀
        (withDensityReal (regime S β₀ hE).ρ₀)) X₀ W X) :
    ∫ ω, Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a (zetaAt (rLvl d) P X 0 ω)) ∂P =
      ∫ x, Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a
          (zetaE (rLvl d) (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) x))
          ∂(modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) := by
  have hH : 0 < a + T := by linarith
  have hS := hreal.solution 0
  set Q : Measure (Config d N) := modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0 with hQdef
  have hQ0 : P.map X₀ = Q := hreal.law_init
  have hX0 : P.map (X 0) = Q := by
    rw [← hQ0]
    exact Measure.map_congr hS.init
  haveI hQp : IsProbabilityMeasure Q := by
    rw [← hX0]
    exact (Measure.isProbabilityMeasure_map_iff (hS.adapted 0).aemeasurable).2 inferInstance
  have hrd : (d : ℝ) < 2 * rLvl d := by
    unfold rLvl
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hU : MemCb 5 (Ucan hE T a ha Φ 0) :=
    (HRS.MC.E213U5.Ucan_regular_proof hE T hT a ha Φ hΦ).1 0 ⟨le_rfl, hH.le⟩
  set g : Config d N → ℝ := fun x => Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a (zetaE (rLvl d) Q x)) with hg
  have hgc : Continuous g :=
    hU.1.continuous.comp ((Iwin S β₀ hE T a).continuous.comp
      (HRS.MD.EQLawPath.eqlaw_continuous_zetaE hrd (by omega) Q))
  have e1 : ∀ ω, Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a (zetaAt (rLvl d) P X 0 ω)) = g (X 0 ω) := by
    intro ω
    show Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a (zetaE (rLvl d) (P.map (X (0 : ℝ).toNNReal)) (X (0 : ℝ).toNNReal ω))) = _
    rw [Real.toNNReal_zero, hX0]
  simp_rw [e1]
  rw [← integral_map (hS.adapted 0).aemeasurable hgc.aestronglyMeasurable, hX0]

theorem u21_integrable_apply {T : ℝ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Z : Ω → PathSpace d m T) (hZ : AEMeasurable Z μ) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ)
    (u : TensorDual (PathSpace d m T) 3) :
    Integrable (fun ω => u (iteratedFDeriv ℝ 3 Φ (Z ω))) μ := by
  have hc : Continuous (iteratedFDeriv ℝ 3 Φ) := hΦ.1.continuous_iteratedFDeriv (by norm_num)
  have hg : Continuous fun z => u (iteratedFDeriv ℝ 3 Φ z) := u.continuous.comp hc
  obtain ⟨C, hC⟩ := hΦ.2 3 (by norm_num)
  refine (integrable_const (‖u‖ * C)).mono' (hg.aestronglyMeasurable.comp_aemeasurable hZ)
    (Filter.Eventually.of_forall fun ω => ?_)
  refine (u.le_opNorm _).trans ?_
  exact mul_le_mul_of_nonneg_left (hC ⟨Z ω, rfl⟩) (norm_nonneg _)

section GD

variable {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u21_Kproj_apply (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ)
    (z : PathSpace d m T) :
    ((gd.Kproj T a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) (iteratedFDeriv ℝ 3 Φ z) =
      (pushforward3 (Iwin S β₀ hE T a) (Kinit0 S β₀)) (iteratedFDeriv ℝ 3 Φ z)
        - 3 * (bochTensor3 gd.P₀ (gd.Dwin T a) (gd.Zwin T a) (gd.Zwin T a)) (iteratedFDeriv ℝ 3 Φ z)
        + 3 * (bochTensor21 gd.P₀ (gd.Jwin T a) (gd.Zwin T a)) (iteratedFDeriv ℝ 3 Φ z) := by
  have hKv : ((gd.Kproj T a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) =
      gd.Kwin T a := by
    classical
    unfold GaussData.Kproj
    rw [max_eq_left ha, dif_pos (HRS.MC.E213U11.Kwin_mem_proof gd T hT a ha)]
  rw [hKv]
  unfold GaussData.Kwin
  rw [symm3_apply]
  have hsym : ∀ σ : Equiv.Perm (Fin 3),
      (iteratedFDeriv ℝ 3 Φ z).domDomCongr σ = iteratedFDeriv ℝ 3 Φ z := fun σ =>
    HRS.MC.E213U1.iteratedFDeriv_three_symm_proof
      ((u21_memCb_mono hΦ).1.contDiffAt) σ
  simp only [hsym, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h6 : (Fintype.card (Equiv.Perm (Fin 3)) : ℝ) = 6 := by
    have : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Fintype.card_perm]; simp [Nat.factorial]
    exact_mod_cast this
  rw [h6]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

end GD

end Part

end HRS.MC.E213U21

end
