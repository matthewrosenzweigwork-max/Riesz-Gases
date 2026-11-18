import HRS.ME.FamVC
import HRS.ME.RetPathLaw
import HRS.Main.HeadlineEquilibrium
import HRS.Sections.Q38bAux4
import HRS.MH.CondOuDefs

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS.MH.CondOuPackets

open HRS HRS.Main HRS.LZ

variable {d : ℕ}

theorem p_cp4_isSmooth_cosTest (k : Lattice d) : Torus.IsSmooth (PDE.cosTest k) := by
  unfold PDE.cosTest Torus.IsSmooth Torus.IsCk
  exact contDiff_const.mul (HRS.d1_isSmooth_cosMode k)

theorem p_cp4_cosTest_eq_realMode (k : Lattice d) (hk : k ≠ 0) :
    ∃ K : NonzeroLattice d, (K.1 = k ∨ K.1 = -k) ∧ PDE.cosTest k = Torus.realMode K := by
  by_cases hp : Lattice.IsPosHalf k
  · refine ⟨⟨k, hk⟩, Or.inl rfl, ?_⟩
    funext x
    simp [Torus.realMode, hp, PDE.cosTest]
  · have hn : Lattice.IsPosHalf (-k) := (Torus.isPosHalf_neg k hk).mpr hp
    refine ⟨⟨-k, neg_ne_zero.mpr hk⟩, Or.inr rfl, ?_⟩
    funext x
    simp [Torus.realMode, hn, PDE.cosTest, Torus.cosMode_neg]

theorem p_cp4_cov (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) (t : ℝ) (ht : 0 ≤ t) :
    PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ)
      (fun _ => (1 : ℝ)) ![0, t] (fun _ => PDE.cosTest k) = condouCov d s β k t := by
  obtain ⟨K, hK1, hK⟩ := p_cp4_cosTest_eq_realMode k hk
  have hτ : ∀ a : Fin 2, 0 ≤ (![0, t] : Fin 2 → ℝ) a := by
    intro a; fin_cases a <;> simp [ht]
  have hrate : q38b_rate d s β K = PDE.transientRate d s β k := by
    unfold q38b_rate PDE.transientRate
    rcases hK1 with h | h <;> rw [h]
    rw [HRS.rieszCoeff_neg, HRS.enorm_neg]
  have hriesz : rieszCoeff d s K.1 = rieszCoeff d s k := by
    rcases hK1 with h | h <;> rw [h]
    rw [HRS.rieszCoeff_neg]
  simp only [hK]
  rw [q38b_lagCov_eq hd hs0 hsd hβ K ![0, t] hτ, hrate, hriesz]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [condouCov, abs_of_nonneg ht, mul_comm]

/-- **P4** statement copied from the spec. -/
theorem condou_gauss_law (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) {m : ℝ} (t : ℝ) (ht : 0 ≤ t)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) m Z) :
    (law P' (windowPath m t 0 Z)).map (condouEval2 d m t ht k) =
      multivariateGaussian 0 (condouCov d s β k t) := by
  have hae : AEMeasurable (windowPath m t 0 Z) P' :=
    (HRS.MD.EQGaussWindow.eqgw_fidi hd hs0 hsd (fun _ => (0 : ℝ)) hβ (fun _ => (1 : ℝ)) m t P' Z hZ 0
      le_rfl).1
  have hR : Measurable (condouEval2 d m t ht k) := (condouEval2 d m t ht k).continuous.measurable
  have h1 : (law P' (windowPath m t 0 Z)).map (condouEval2 d m t ht k) =
      P'.map (condouEval2 d m t ht k ∘ windowPath m t 0 Z) :=
    AEMeasurable.map_map_of_aemeasurable hR.aemeasurable hae
  have h2 : (condouEval2 d m t ht k ∘ windowPath m t 0 Z) =ᵐ[P']
      (fun ω => (WithLp.toLp 2 fun a : Fin 2 => NegSobolev.eval (Z (![0, t] a) ω) (PDE.cosTest k) :
        EuclideanSpace ℝ (Fin 2))) := by
    filter_upwards [hZ.cont] with ω hω
    simp only [Function.comp_apply]
    rw [condouEval2_apply,
      HRS.MD.EQGaussWindow.eqgw_windowPath_at t 0 le_rfl Z ω hω (HRS.ME.FamV.t0 ht),
      HRS.MD.EQGaussWindow.eqgw_windowPath_at t 0 le_rfl Z ω hω (endpt ht)]
    congr 1
    funext a
    fin_cases a <;> simp [HRS.ME.FamV.t0, endpt]
  have h3 := hZ.gaussian 2 ![0, t] (fun _ => PDE.cosTest k)
    (by intro a; fin_cases a <;> simp [ht]) (fun _ => p_cp4_isSmooth_cosTest k)
  rw [h1, Measure.map_congr h2]
  rw [show P'.map _ = _ from h3, p_cp4_cov hd hs0 hsd hβ k hk t ht]

end HRS.MH.CondOuPackets
