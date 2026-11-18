import HRS.MC.S7UCDefs
import HRS.MC.S7FCH4D
import HRS.MC.S7FCH4E
import HRS.MC.S7FCD5B

/-!
# Packet ucH, H4a/H4b: the finite-rank identities at window `a` (sorry-free; imports no sorried module)

`s7_UC_H4_particle_id_proof`, `s7_UC_H4_gauss_id_proof`: the window-`a` versions of `S7FCH4_particle_id`
(`S7FCH4D.lean:91`) and `S7FCH4_gauss_id` (`S7FCH4E.lean:38`).  Namespace `HRS.MC.Sec7.S7UCH`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7UCH

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCH4

variable {d : ℕ}

theorem S7UCH_windowFluc_eq {Ω : Type} {N : ℕ} (R : Regime d) (r T : ℝ) (X : ℝ≥0 → Ω → Config d N)
    (a : ℝ) (ha : 0 ≤ a) (ω : Ω) :
    HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ ω =
      toPath r T (fun t ω => etaE r (X (a + t).toNNReal ω) (withDensityReal (R.ρ (a + t)))) ω := by
  unfold HRS.Main.windowFluc HRS.flucPath toPath
  refine HRS.MC.Sec7.S7FCF5I.S7FCF5I_dite_congr _ _ ?_
  funext t
  have ht : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  simp only [etaE, flucE, Real.toNNReal_add ha ht]

/-- The Gaussian window `procWin^a` agrees pathwise with `t ↦ η (a + t)` when `η` is continuous on `[a, a+T]`. -/
theorem S7UCH_procWin_val {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (r T a : ℝ)
    (η : ℝ → Ω' → NegSobolev d r) (hc : ∀ᵐ ω ∂P', ContinuousOn (fun t => η t ω) (Set.Icc a (a + T))) :
    ∀ᵐ ω ∂P', ∀ s : Set.Icc (0 : ℝ) T, PathSpace.at' (procWin r T a η ω) s = η (a + (s : ℝ)) ω := by
  filter_upwards [hc] with ω hω
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) T => η (a + (t : ℝ)) ω := by
    have h1 : ContinuousOn (fun t => η (a + t) ω) (Set.Icc 0 T) := by
      refine hω.comp (continuous_const.add continuous_id).continuousOn ?_
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact continuousOn_iff_continuous_restrict.1 h1
  intro s
  exact HRS.MC.Sec7.S7FCD5B.S7FCD5B_toPath_apply r T (fun t ω => η (a + t) ω) ω hcont s

/-- **UC-H4a**, proof. -/
theorem s7_UC_H4_particle_id_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization R.D P
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)
    (a : ℝ) (ha : 0 ≤ a)
    (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) (m : PathSpace d r T)
    (hm : ∀ᵐ ω ∂P, zetaWin r T a P X ω = HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ ω - m)
    (hint : Integrable (fun ω => S7FCH4_Y S K (Real.sqrt N)⁻¹ m (zetaWin r T a P X ω)) P) :
    ∀ᵐ ω ∂P, toL2 r T (fun t => fcPartAt r S K (fun t => withDensityReal (R.ρ t)) P X (a + t) ω) =
      S7FCH4_iota hT.le (S7FCH4_Y S K (Real.sqrt N)⁻¹ m (zetaWin r T a P X ω) -
        ∫ ω', S7FCH4_Y S K (Real.sqrt N)⁻¹ m (zetaWin r T a P X ω') ∂P) := by
  classical
  obtain ⟨hh1, hh2⟩ := HRS.MC.Sec7.S7FCF5G.fcf5_E1_window_cont_proof R r hr T (by omega) P X₀ W X hreal a ha
  have key : ∀ᵐ ω ∂P, ∀ t : Set.Icc (0 : ℝ) T,
      fcPartTilde r S K (withDensityReal (R.ρ (a + t))) (X (a + (t : ℝ)).toNNReal ω) =
        PathSpace.at' (S7FCH4_Y S K (Real.sqrt N)⁻¹ m (zetaWin r T a P X ω)) t -
          S7FCH4_cst r S K (withDensityReal (R.ρ (a + t))) := by
    filter_upwards [hm, hh1, hh2] with ω h1 h2 h3
    intro t
    have := isProb_withDensityReal
      (HRS.MC.Sec7.S7FCD5B.S7FCD5B_hdens R (a + t) (add_nonneg ha t.2.1))
    have hη : PathSpace.at' (zetaWin r T a P X ω) t + PathSpace.at' m t =
        etaE r (X (a + (t : ℝ)).toNNReal ω) (withDensityReal (R.ρ (a + t))) := by
      have hz : PathSpace.at' (zetaWin r T a P X ω) t = zetaAt r P X (a + (t : ℝ)) ω :=
        HRS.MC.Sec7.S7FCD5B.S7FCD5B_toPath_apply r T (fun t ω => zetaAt r P X (a + t) ω) ω h3 t
      rw [h1, S7UCH_windowFluc_eq R r T X a ha, S7FCH4_at_sub,
        HRS.MC.Sec7.S7FCD5B.S7FCD5B_toPath_apply r T _ ω h2 t]
      abel
    rw [S7FCH4_at_Y, hη]
    exact S7FCH4_tilde_eq (by omega) r hr S K _ _
  filter_upwards [key] with ω hω
  refine S7FCH4_toL2_eq_iota hT.le _ _ fun t ht => ?_
  set tt : Set.Icc (0 : ℝ) T := ⟨t, ht⟩ with htt
  have hI : ∫ ω', fcPartTilde r S K (withDensityReal (R.ρ (a + t))) (X (a + t).toNNReal ω') ∂P =
      (∫ ω', PathSpace.at' (S7FCH4_Y S K (Real.sqrt N)⁻¹ m (zetaWin r T a P X ω')) tt ∂P) -
        S7FCH4_cst r S K (withDensityReal (R.ρ (a + t))) := by
    rw [integral_congr_ae (key.mono fun ω' h => h tt),
      integral_sub (S7FCH4_integrable_at hint tt) (integrable_const _), integral_const]
    simp
    rfl
  show fcPartAt r S K (fun t => withDensityReal (R.ρ t)) P X (a + t) ω = _
  unfold fcPartAt
  rw [hω tt, hI, S7FCH4_at_sub, S7FCH4_at_integral hint tt]
  abel

/-- **UC-H4b**, proof. -/
theorem s7_UC_H4_gauss_id_proof {r : ℝ} {T : ℝ} (hT : 0 < T) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (η : ℝ → Ω' → NegSobolev d r) (S : Finset (NonzeroLattice d))
    (K : NonzeroLattice d → FRKernel d) (a : ℝ) (ha : 0 ≤ a) (hmeas : ∀ t, Measurable (η t))
    (hc : ∀ᵐ ω ∂P', ContinuousOn (fun t => η t ω) (Set.Icc a (a + T)))
    (hmom : Integrable (fun ω => ‖procWin r T a η ω‖ ^ 2) P')
    (hint : Integrable (fun ω => S7FCH4_Y S K 0 (0 : PathSpace d r T) (procWin r T a η ω)) P') :
    ∀ᵐ ω ∂P', toL2 r T (fun t => fcGaussAt r S K P' η (a + t) ω) =
      S7FCH4_iota hT.le (S7FCH4_Y S K 0 (0 : PathSpace d r T) (procWin r T a η ω) -
        ∫ ω', S7FCH4_Y S K 0 (0 : PathSpace d r T) (procWin r T a η ω') ∂P') := by
  classical
  have hae := S7UCH_procWin_val P' r T a η hc
  filter_upwards [hae] with ω hω
  refine S7FCH4_toL2_eq_iota hT.le _ _ fun t ht => ?_
  set tt : Set.Icc (0 : ℝ) T := ⟨t, ht⟩ with htt
  have hI : PathSpace.at' (∫ ω', S7FCH4_Y S K 0 (0 : PathSpace d r T) (procWin r T a η ω') ∂P') tt =
      ∫ ω', S7FCH4_gq r S K (η (a + t) ω') ∂P' := by
    rw [S7FCH4_at_integral hint tt]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω' h
    rw [S7FCH4_at_Y, h tt, S7FCH4_at_zero]
    simp [S7FCH4_phi]
    rfl
  have hQ : ∀ k, Integrable (fun ω' => (K k).quad (η (a + t) ω')) P' := by
    intro k
    refine Integrable.mono' (hmom.const_mul (S7FCH4_qC r (K k))) ?_ ?_
    · exact ((HRS.MC.Sec7.S7FCW12.s7fcw12_quad_continuous (m := r) (K k)).measurable.comp
        (hmeas (a + t))).aestronglyMeasurable
    · filter_upwards [hae] with ω' h
      have h1 := S7FCH4_quad_abs_le (K k) (η (a + t) ω')
      have h2 : ‖η (a + t) ω'‖ ≤ ‖procWin r T a η ω'‖ := by
        rw [← h tt]; exact S7FCH4_norm_at_le _ tt
      rw [Real.norm_eq_abs]
      refine h1.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (S7FCH4_qC_nonneg r (K k))
      nlinarith [norm_nonneg (η (a + t) ω')]
  have hG : ∫ ω', S7FCH4_gq r S K (η (a + t) ω') ∂P' =
      ∑ k ∈ S, (∫ ω', (K k).quad (η (a + t) ω') ∂P') • S7FCH4_e r k := by
    unfold S7FCH4_gq
    rw [integral_finsetSum _ (fun k _ => (hQ k).smul_const _)]
    exact Finset.sum_congr rfl fun k _ => integral_smul_const _ _
  show fcGaussAt r S K P' η (a + t) ω = PathSpace.at' (S7FCH4_Y S K 0 (0 : PathSpace d r T) (procWin r T a η ω) -
    ∫ ω', S7FCH4_Y S K 0 (0 : PathSpace d r T) (procWin r T a η ω') ∂P') tt
  rw [S7FCH4_at_sub, hI, hG, S7FCH4_at_Y, hω tt, S7FCH4_at_zero]
  unfold fcGaussAt
  simp only [add_zero]
  rw [S7FCH4_ofSeq_sum]
  simp only [S7FCH4_phi, zero_smul, sub_zero]
  unfold S7FCH4_gq
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => (sub_smul _ _ _)

end HRS.MC.Sec7.S7UCH

end
