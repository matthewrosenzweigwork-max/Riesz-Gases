import HRS.MS.SpecAux48
import HRS.MS.SpecAux40
import HRS.Whole.CriticalNoise

/-!
# S8P: `IsSpectralData` for the critical quadratic model (S8.7, packets b2-b7, assembly)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_exists_spectralData`: for `d ≥ 2`, `a, β > 0` and the thermal density `ρβ` of the
critical model (`s = d/2`), there are `e, om` with `IsSpectralData d β ρβ e om`.  This is the first conjunct of `HRS.Whole.spectral_space`;
the `L⁴` gradient bound and the coupling statement are not part of it.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec HRS.MS.MovLin

local notation "𝓢R" => SchwartzMap (Euc _) ℝ

set_option maxHeartbeats 3200000 in
theorem s8p_exists_spectralData {d : ℕ} (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (ρβ : Euc d → ℝ) (hρ : HRS.Whole.IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) :
    ∃ (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ), HRS.Whole.IsSpectralData d β ρβ e om := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have H : Mov2dTh d ((d : ℝ) / 2) β a ρβ :=
    ⟨hd, by positivity, by linarith, hβ, ha, hρ⟩
  have hs : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  obtain ⟨M, h⟩ := s8p_rho_of_thermal H hs
  obtain ⟨hρ', hE, -⟩ := mov2e_thermal H.hd H.hs0 H.hsd H.hβ H.hq H.hρ
  obtain ⟨ψ0, hψ0⟩ := mov2d_sqrt_schwartz H
  obtain ⟨D⟩ := s8p_eigData H h
  have hmean : ∀ n, ∫ x, Real.sqrt (ρβ x) * D.φ n x = 0 := fun n =>
    s8p_mean_zero H ψ0 hψ0 (D.v n) (D.φ n) (D.hv n)
  have hsd : (d : ℝ) / 2 < d := H.hsd
  refine ⟨fun l => s8p_E d ((d : ℝ) / 2) β ρβ (D.φ l), D.om, ?_⟩
  refine ⟨fun l => s8p_E_smooth hd1 H.hs0 hsd hρ' hE β (D.φ l), fun l => ?_, fun l => D.lam_pos.trans_le (D.lam_le l),
    D.mono, fun l => ?_, fun l => ?_, fun l j => ?_, fun l j => ?_, fun l j => ?_, ?_, ?_⟩
  · exact ⟨s8p_E_memLp hd1 H.hs0 hsd hρ' hE β (D.φ l), s8p_E_mean hd1 H.hs0 hsd hρ' hE β (D.φ l) (hmean l)⟩
  · exact s8p_eigen_eq hd1 H.hs0 hsd hρ' hE β (D.φ l) (D.om l) (D.hS l)
  · exact ⟨_, s8p_response hd1 H.hs0 hsd hρ' hE hβ (D.φ l) (hmean l)⟩
  · -- orth
    have hri := s8p_responseInverse_E hd1 hs hsd hρ' hE (fun x => h.le x) hβ (D.φ j) (hmean j)
    unfold HRS.Whole.l2Inner
    have h1 : ∫ x, s8p_E d ((d : ℝ) / 2) β ρβ (D.φ l) x *
        HRS.Whole.responseInverse (rieszKernel d ((d : ℝ) / 2)) (HRS.Whole.withDensityReal ρβ) β
          (s8p_E d ((d : ℝ) / 2) β ρβ (D.φ j)) x ∂(HRS.Whole.withDensityReal ρβ) =
        β⁻¹ * ∫ x, s8p_E d ((d : ℝ) / 2) β ρβ (D.φ l) x * (D.φ j x / Real.sqrt (ρβ x))
          ∂(HRS.Whole.withDensityReal ρβ) := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hri] with x hx
      rw [hx]; ring
    show β * (∫ x, s8p_E d ((d : ℝ) / 2) β ρβ (D.φ l) x *
        HRS.Whole.responseInverse (rieszKernel d ((d : ℝ) / 2)) (HRS.Whole.withDensityReal ρβ) β
          (s8p_E d ((d : ℝ) / 2) β ρβ (D.φ j)) x ∂(HRS.Whole.withDensityReal ρβ)) = _
    rw [h1, ← mul_assoc, mul_inv_cancel₀ hβ.ne', one_mul,
      s8p_orth_e hd1 H.hs0 hsd hρ' hE β (D.φ l) (D.φ j) (hmean j), D.pair H l j]
  · exact (s8p_grad_pair hd1 H.hs0 hsd hρ' hE β (D.φ l) (D.φ j)).1
  · rw [(s8p_grad_pair hd1 H.hs0 hsd hρ' hE β (D.φ l) (D.φ j)).2]
    have : ∫ x, mov2eW d ((d : ℝ) / 2) β ρβ (D.φ j) x * movS d ((d : ℝ) / 2) β ρβ (D.φ l) x =
        ∫ x, D.om l * (mov2eW d ((d : ℝ) / 2) β ρβ (D.φ j) x * D.φ l x) := by
      refine integral_congr_ae ?_
      filter_upwards [D.hS l] with x hx
      rw [hx]; ring
    rw [this, integral_const_mul, D.pair H j l]
    by_cases hlj : l = j
    · subst hlj; simp
    · simp [hlj, Ne.symm hlj]
  · exact s8p_growth H ψ0 hψ0 D
  · intro f hf hr
    exact s8p_complete_field hd1 hs hsd hρ' hE h hβ D.v D.φ D.hv hmean D.complete f hf hr

end HRS.MS.Spec
