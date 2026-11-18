import HRS.MC.E213U18l

/-!
# Packet e213u18 (part m): the initial term `∫ ∏ ℓ_i(I_a ℓ_x) dμ° = ∫ ∏ r_i° dμ°`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U18

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213U10

variable {d : ℕ}

section T0

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}

theorem u18_Iwin_eq (T a : ℝ) (ha : 0 ≤ a) (z : NegSobolev d (rLvl d)) :
    Iwin S β₀ hE T a z = initWinFun (regime S β₀ hE).D (regime S β₀ hE).ρ m (rLvl d) T a z := by
  obtain ⟨C, c, -, -, h⟩ := Classical.choose_spec (exists_Iwin S β₀ hE T)
  exact (h a ha).1 z

theorem u18_Iwin_ell (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {t : ℝ} (ht : t ∈ Set.Icc a (a + T))
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (ℓ' : PathSpace d m T →L[ℝ] ℝ)
    (hℓ : ∀ w, ℓ' w = NegSobolev.eval (pathEval w (t - a)) φ) (z : NegSobolev d (rLvl d)) :
    ℓ' (Iwin S β₀ hE T a z) = NegSobolev.eval z (propagator S.dyn S.ρ 0 t φ) := by
  have hτ : t - a ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hH : 0 < a + T := by linarith
  have ht0 : 0 ≤ t := ha.trans ht.1
  have hc : Continuous fun s : Set.Icc (0 : ℝ) T =>
      Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + (s : ℝ)) 0 (NegSobolev.embed m z) := by
    have h1 := HRS.MC.E213O.vprop_continuousOn_zero S β₀ hE m (a + T) hH.le (NegSobolev.embed m z)
    exact h1.comp_continuous (continuous_const.add continuous_subtype_val)
      (fun s => ⟨by linarith [s.2.1], by linarith [s.2.2]⟩)
  rw [hℓ, u18_pathEval_eq, show pathAt (Iwin S β₀ hE T a z) (t - a) =
    (Iwin S β₀ hE T a z).at' ⟨t - a, hτ⟩ from u10_pathAt_eq _ ⟨t - a, hτ⟩, u18_Iwin_eq T a ha]
  unfold initWinFun
  rw [e213o_pathOf_at' _ hc ⟨t - a, hτ⟩]
  show NegSobolev.eval (Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + (t - a)) 0
    (NegSobolev.embed m z)) φ = _
  rw [add_sub_cancel,
    HRS.MC.Sec7.S7PIS1.s7_PIS_V_eval_proof (regime S β₀ hE) m hE.m_gt (a + T) hH 0 t le_rfl ht0 ht.2 _ φ hφ]
  exact HRS.AdjK.adjka_eval_embed (rLvl_le hE) z _

theorem u18_T0 (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {t : Fin 3 → ℝ} {φ : Fin 3 → Torus d → ℝ}
    (hta : ∀ i, t i ∈ Set.Icc a (a + T)) (hφ : ∀ i, Torus.IsSmooth (φ i))
    (ℓ : Fin 3 → PathSpace d m T →L[ℝ] ℝ)
    (hℓ : ∀ i w, ℓ i w = NegSobolev.eval (pathEval w (t i - a)) (φ i)) :
    ∫ x, ℓ 0 (Iwin S β₀ hE T a (ellVec S β₀ x)) * ℓ 1 (Iwin S β₀ hE T a (ellVec S β₀ x)) *
        ℓ 2 (Iwin S β₀ hE T a (ellVec S β₀ x)) ∂S.μ0 =
      ∫ x, responseInverse (periodicRiesz d S.dyn.s) S.μ0 β₀ (propagator S.dyn S.ρ 0 (t 0) (φ 0)) x *
        responseInverse (periodicRiesz d S.dyn.s) S.μ0 β₀ (propagator S.dyn S.ρ 0 (t 1) (φ 1)) x *
        responseInverse (periodicRiesz d S.dyn.s) S.μ0 β₀ (propagator S.dyn S.ρ 0 (t 2) (φ 2)) x ∂S.μ0 := by
  have hsm : ∀ i, Torus.IsSmooth (propagator S.dyn S.ρ 0 (t i) (φ i)) := fun i =>
    (HRS.MC.L2C0.l2c0_proof (regime S β₀ hE) (φ i) (hφ i) 0 (t i) le_rfl (ha.trans (hta i).1)).1
  have hs : S.s < (d : ℝ) / 2 := hE.s_lt
  have hae : ∀ i, ∀ᵐ x ∂S.μ0, ℓ i (Iwin S β₀ hE T a (ellVec S β₀ x)) =
      responseInverse (periodicRiesz d S.dyn.s) S.μ0 β₀ (propagator S.dyn S.ρ 0 (t i) (φ i)) x := by
    intro i
    have h1 := HRS.MC.Sec7.FCD3B.d3b_rep_ae S.hd S.hs0 hs hE.β₀_nonneg S.hρ0 (hsm i)
    filter_upwards [h1] with x hx
    rw [u18_Iwin_ell T hT a ha (hta i) (hφ i) (ℓ i) (hℓ i)]
    have key := u18_eval_ellPt S.hd S.hs0 hs hE.β₀_nonneg S.hρ0 (r := rLvl d) rfl (hsm i) x
    exact key.trans hx
  refine integral_congr_ae ?_
  filter_upwards [hae 0, hae 1, hae 2] with x h0 h1 h2
  rw [h0, h1, h2]

end T0

end HRS.MC.E213U18

end
