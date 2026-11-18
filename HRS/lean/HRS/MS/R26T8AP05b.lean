import HRS.MS.R26T8AP05a
import HRS.MS.R26T8AP03c

/-!
# S8.2 local Newton layer, packet T8A.P05 (part b): derivatives falling on the source
`r26t8a_stageA`: (`C^q` and) `D^q_x int Kk(u) s(x-u) du = int Kk(u) . D^q s(x-u) du` for integrable `Kk` and `C^q` compactly supported `s`.
`r26t8a_stageB`: `D^p_Y int Kk(u) . Psi(Y, z-u) du = int Kk(u) . D^p_Y Psi(Y, z-u) du` for `C^p` compactly supported `Psi`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_conv_jet' {s : Euc d → ℝ} {i : ℕ} (hs : ContDiff ℝ (i : WithTop ℕ∞) s) (c : ℝ) (u x : Euc d) :
    iteratedFDeriv ℝ i (fun x => c * s (x - u)) x = c • iteratedFDeriv ℝ i s (x - u) := by
  have h1 : (fun x => c * s (x - u)) = fun x => c • (fun z => s (z - u)) x := by
    funext x; simp
  have hca : ContDiffAt ℝ (i : WithTop ℕ∞) (fun z => s (z - u)) x :=
    (hs.comp (contDiff_id.sub contDiff_const)).contDiffAt
  rw [h1, iteratedFDeriv_const_smul_apply' hca, iteratedFDeriv_comp_sub]

theorem r26t8a_stageA {Kk s : Euc d → ℝ} (hKk : Integrable Kk) {q : ℕ} (hs : ContDiff ℝ (q : WithTop ℕ∞) s)
    (hsc : HasCompactSupport s) (z : Euc d) :
    ContDiff ℝ (q : WithTop ℕ∞) (fun x => ∫ u, Kk u * s (x - u)) ∧
    iteratedFDeriv ℝ q (fun x => ∫ u, Kk u * s (x - u)) z = ∫ u, Kk u • iteratedFDeriv ℝ q s (z - u) := by
  obtain ⟨B, hB0, hB⟩ := r26t8a_jets_bdd2 hs hsc
  have hint : Integrable (fun u => ‖Kk u‖ * B) := hKk.norm.mul_const B
  have key := HRS.MS.Lc.lc4_iteratedFDeriv_integral (μ := (volume : Measure (Euc d)))
    (fun u x => Kk u * s (x - u)) q
    (fun u => contDiff_const.mul (hs.comp (contDiff_id.sub contDiff_const)))
    (Φ := fun u => ‖Kk u‖ * B) hint
    (fun i hi u x => by
      rw [r26t8a_conv_jet' (hs.of_le (by exact_mod_cast hi)), norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hB i hi _) (abs_nonneg _))
    (fun i hi x => by
      have : (fun u => iteratedFDeriv ℝ i (fun x => Kk u * s (x - u)) x) =
          fun u => Kk u • iteratedFDeriv ℝ i s (x - u) :=
        funext fun u => r26t8a_conv_jet' (hs.of_le (by exact_mod_cast hi)) _ u x
      rw [this]
      exact hKk.aestronglyMeasurable.smul ((((hs.continuous_iteratedFDeriv (by exact_mod_cast hi))).comp
        (continuous_const.sub continuous_id))).aestronglyMeasurable)
  refine ⟨key.1, ?_⟩
  rw [key.2 q le_rfl z]
  exact integral_congr_ae (Eventually.of_forall fun u => r26t8a_conv_jet' hs (Kk u) u z)

theorem r26t8a_stageB {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] {Kk : Euc d → ℝ}
    (hKk : Integrable Kk) {Ψ : Euc d × Euc d → V} {p : ℕ} (hΨ : ContDiff ℝ (p : WithTop ℕ∞) Ψ)
    (hc : HasCompactSupport Ψ) (X z : Euc d) :
    iteratedFDeriv ℝ p (fun Y => ∫ u, Kk u • Ψ (Y, z - u)) X =
      ∫ u, Kk u • iteratedFDeriv ℝ p (fun Y => Ψ (Y, z - u)) X := by
  obtain ⟨B, hB0, hB⟩ := r26t8a_jets_bdd2 hΨ hc
  have hint : Integrable (fun u => ‖Kk u‖ * B) := hKk.norm.mul_const B
  have hsl : ∀ u, ContDiff ℝ (p : WithTop ℕ∞) (fun Y => Ψ (Y, z - u)) := fun u =>
    hΨ.comp (contDiff_id.prodMk contDiff_const)
  have hjet : ∀ (i : ℕ), i ≤ p → ∀ (u Y : Euc d), iteratedFDeriv ℝ i (fun Y => Kk u • Ψ (Y, z - u)) Y =
      Kk u • iteratedFDeriv ℝ i (fun Y => Ψ (Y, z - u)) Y := fun i hi u Y =>
    iteratedFDeriv_const_smul_apply' ((hsl u).of_le (by exact_mod_cast hi)).contDiffAt
  have key := HRS.MS.Lc.lc4_iteratedFDeriv_integral (μ := (volume : Measure (Euc d)))
    (fun u Y => Kk u • Ψ (Y, z - u)) p (fun u => contDiff_const.smul (hsl u))
    (Φ := fun u => ‖Kk u‖ * B) hint
    (fun i hi u Y => by
      rw [hjet i hi, norm_smul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact (r26t8a_slice_jet_norm (hΨ.of_le (by exact_mod_cast hi)) Y (z - u)).trans (hB i hi _))
    (fun i hi x => by
      have hΨi : ContDiff ℝ (i : WithTop ℕ∞) Ψ := hΨ.of_le (by exact_mod_cast hi)
      have e : (fun u => iteratedFDeriv ℝ i (fun Y => Kk u • Ψ (Y, z - u)) x) = fun u =>
          Kk u • (iteratedFDeriv ℝ i Ψ (x, z - u)).compContinuousLinearMap
            (fun _ => ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) :=
        funext fun u => by rw [hjet i hi, r26t8a_slice_jet hΨi]
      rw [e]
      exact hKk.aestronglyMeasurable.smul ((ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin i => ContinuousLinearMap.inl ℝ (Euc d) (Euc d))).continuous.comp
        ((hΨ.continuous_iteratedFDeriv (by exact_mod_cast hi)).comp
          (continuous_const.prodMk (continuous_const.sub continuous_id)))).aestronglyMeasurable)
  rw [key.2 p le_rfl X]
  exact integral_congr_ae (Eventually.of_forall fun u => hjet p le_rfl u X)

end HRS.MS.R26T8A
