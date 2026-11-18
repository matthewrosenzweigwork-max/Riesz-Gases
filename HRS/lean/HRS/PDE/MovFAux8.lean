import HRS.PDE.MovFAux7

/-!
# MOVF Aux8: joint continuity of the `C²`-jets from continuity in `C²`; transfer of weak solutions
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

/-- `C²`-continuity in `r` (in the `cbNorm 2` of differences) and `C²` in `x` give joint continuity of the jets. -/
theorem movf_joint_cont {T : ℝ} {ρ : ℝ → Torus d → ℝ} (hck : ∀ r ∈ Set.Icc (0 : ℝ) T, Torus.IsCk 2 (ρ r))
    (hrate : ∀ r₀ : Set.Icc (0 : ℝ) T, Tendsto (fun r : Set.Icc (0 : ℝ) T =>
      Torus.cbNorm 2 (fun x => ρ r.1 x - ρ r₀.1 x)) (𝓝 r₀) (𝓝 0)) (j : ℕ) (hj : j ≤ 2) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => iteratedFDeriv ℝ j (Torus.lift (ρ p.1)) p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨r₀, x₀⟩
  have hcx : Continuous fun x : Euc d => iteratedFDeriv ℝ j (Torus.lift (ρ r₀.1)) x := by
    have h2 : ContDiff ℝ 2 (Torus.lift (ρ r₀.1)) := by exact_mod_cast hck r₀.1 r₀.2
    exact h2.continuous_iteratedFDeriv (by exact_mod_cast hj)
  have hbd : ∀ p : Set.Icc (0 : ℝ) T × Euc d,
      ‖iteratedFDeriv ℝ j (Torus.lift (ρ p.1.1)) p.2 - iteratedFDeriv ℝ j (Torus.lift (ρ r₀.1)) p.2‖ ≤
        Torus.cbNorm 2 (fun x => ρ p.1.1 x - ρ r₀.1 x) := by
    intro p
    have h1 : ContDiff ℝ 2 (Torus.lift (ρ p.1.1)) := by exact_mod_cast hck p.1.1 p.1.2
    have h2 : ContDiff ℝ 2 (Torus.lift (ρ r₀.1)) := by exact_mod_cast hck r₀.1 r₀.2
    have hsub : Torus.IsCk 2 (fun x => ρ p.1.1 x - ρ r₀.1 x) := mova_isCk_sub (hck p.1.1 p.1.2) (hck r₀.1 r₀.2)
    have := PDE.ET.norm_iteratedFDeriv_le_cbNorm (k := 2) (j := j) hj hsub p.2
    have e : iteratedFDeriv ℝ j (Torus.lift fun x => ρ p.1.1 x - ρ r₀.1 x) p.2 =
        iteratedFDeriv ℝ j (Torus.lift (ρ p.1.1)) p.2 - iteratedFDeriv ℝ j (Torus.lift (ρ r₀.1)) p.2 := by
      have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := j) (x := p.2)
        (h1.contDiffAt.of_le (by exact_mod_cast hj)) (h2.contDiffAt.of_le (by exact_mod_cast hj))
      exact this
    rwa [e] at this
  have hs : Tendsto (fun p : Set.Icc (0 : ℝ) T × Euc d =>
      Torus.cbNorm 2 (fun x => ρ p.1.1 x - ρ r₀.1 x)) (𝓝 (r₀, x₀)) (𝓝 0) :=
    (hrate r₀).comp (continuous_fst.tendsto (r₀, x₀))
  have h0 : Tendsto (fun p : Set.Icc (0 : ℝ) T × Euc d =>
      iteratedFDeriv ℝ j (Torus.lift (ρ p.1.1)) p.2 - iteratedFDeriv ℝ j (Torus.lift (ρ r₀.1)) p.2)
      (𝓝 (r₀, x₀)) (𝓝 0) := squeeze_zero_norm hbd hs
  have h1 : Tendsto (fun p : Set.Icc (0 : ℝ) T × Euc d =>
      iteratedFDeriv ℝ j (Torus.lift (ρ r₀.1)) p.2) (𝓝 (r₀, x₀))
      (𝓝 (iteratedFDeriv ℝ j (Torus.lift (ρ r₀.1)) x₀)) :=
    (hcx.tendsto x₀).comp (continuous_snd.tendsto (r₀, x₀))
  have := h0.add h1
  simp only [zero_add, sub_add_cancel] at this
  exact this

theorem movf_mf_congr {D : DynData d} {T T' : ℝ} {ρ ρ' : ℝ → Torus d → ℝ} (hTT : T ≤ T')
    (hagree : ∀ t ∈ Set.Icc (0 : ℝ) T, ρ' t = ρ t) (h : IsMeanFieldSolution D T' ρ') :
    IsMeanFieldSolution D T ρ := by
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) T, t ∈ Set.Icc (0 : ℝ) T' := fun t ht => ⟨ht.1, ht.2.trans hTT⟩
  refine ⟨fun t ht => hagree t ht ▸ h.density t (hmem t ht), fun ψ hψ t ht => ?_⟩
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, ht.1.trans ht.2⟩
  have := h.weak ψ hψ t (hmem t ht)
  rw [hagree t ht, hagree 0 h0] at this
  rw [this]
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
  simp only [hagree s hsT]

end HRS

end
