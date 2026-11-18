import HRS.MS.R26T8AF00
import HRS.MS.R26T8AF01b
import HRS.MS.UlTie2
import HRS.MS.FldRemAux4
import HRS.MS.OrbFeatAux2
import HRS.MS.FeatDecAux3

/-!
# S8.2 observed-time layer, packet T8A.F11: four orbits with common all-jet difference quotients

`F j t = propagatorW (critCoeff) 0 t (L^j f)`.  Route: the frozen S5.1 `ul_adjoint_orbit_bounds` (proved as
`Ul.ul_adjoint_orbit_bounds_proof`) at the stationary data `Q = a·I`, `ν = β⁻¹`, `σ = 0`, `c = -∇g*ρ` (`critCoeff = fixedViscosityCoeff`),
identification of the propagator with the UL evolution (`s52b_prop_eq`, uniqueness `s53_uniq`), horizon `T = t + 1`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

/-- the UL data of the critical coefficient: `critCoeff = fixedViscosityCoeff` with `Q = sym(a I)`, `ν = β⁻¹`, `σ = 0`,
the UL orbit hypotheses and uniqueness of classical adjoint solutions -/
theorem r26t8a_f11_setup (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) :
    ∃ (θ : Euc d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (c : Euc d → Euc d),
      IsUlCutoff θ ∧
      critCoeff d a beta rho = fixedViscosityCoeff ((d : ℝ) / 2) (-1) Q beta⁻¹ c rho ∧
      HRS.MS.Ul.UlOrb d ((d : ℝ) / 2) beta⁻¹ rho (fun _ => (0 : Euc d)) c θ ∧
      IsSchwartzDensity rho ∧
      ∀ T : ℝ, HRS.MS.S52B.S52bUniq (fixedViscosityCoeff ((d : ℝ) / 2) (-1) Q beta⁻¹ c rho) T := by
  have hd1 : 1 ≤ d := by omega
  have hs0' : 0 < criticalS d := HRS.MS.S82R.s82r_criticalS_pos hd1
  have hsd' : criticalS d < d := HRS.MS.S82R.s82r_criticalS_lt hd1
  have hcrit : criticalS d = (d : ℝ) / 2 := rfl
  have hs0 : 0 ≤ (d : ℝ) / 2 := by rw [← hcrit]; exact hs0'.le
  have hsd : (d : ℝ) / 2 < d := by rw [← hcrit]; exact hsd'
  have hν : 0 < beta⁻¹ := inv_pos.2 hbeta
  have hρS : IsSchwartzDensity rho := by
    rw [critical_thermal_eq d hd a beta ha hbeta hrho]
    exact HRS.MS.S85.s85_thermal_schwartz hd hs0' hsd' ha hbeta
  obtain ⟨θ, hθ⟩ := HRS.MS.S52B.s52b_exists_ulCutoff d
  set Q : Matrix (Fin d) (Fin d) ℝ := Torus.symPart (a • (1 : Matrix (Fin d) (Fin d) ℝ)) with hQ
  set c : Euc d → Euc d := fun x => (fun _ : Euc d => (0 : Euc d)) x -
    convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) rho x with hc
  refine ⟨θ, Q, c, hθ, (HRS.MS.S85.s85_crit_eq a beta rho).trans (HRS.MS.S53.s53_coeff_eq _ _ _ _),
    ⟨hd, hs0, hsd, hν, hρS.2.elim fun ψ hψ => ⟨ψ, hψ⟩, fun i => ⟨0, by ext x; simp⟩, hc, hθ⟩, hρS, ?_⟩
  intro T
  have := HRS.MS.S53.s53_uniq hd hs0 hsd hν (a • (1 : Matrix (Fin d) (Fin d) ℝ)) hρS T
  rw [HRS.MS.S53.s53_coeff_eq] at this
  exact this

theorem r26t8a_four_orbits (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (f : SchwartzMap (Euc d) ℝ) :
    ∃ F : Fin 4 → ℝ → Euc d → ℝ,
      (∀ j : Fin 4, ∀ t : ℝ, 0 ≤ t →
        F j t = propagatorW (critCoeff d a beta rho) 0 t (r26t8a_LIter a beta rho j f)) ∧
      (∀ j : Fin 4, ∀ t : ℝ, 0 ≤ t → ∃ u,
        IsClassicalAdjointW (critCoeff d a beta rho) t (r26t8a_LIter a beta rho j f) u ∧ F j t = u 0) ∧
      (∀ j : Fin 4, ∀ t : ℝ, 0 ≤ t → ∀ k : ℕ, MemCb k (F j t)) ∧
      (∀ j : Fin 4, ∀ t : ℝ, 0 ≤ t → ContDiff ℝ ∞ (F j t)) ∧
      (∀ (j : Fin 4) (hj : (j : ℕ) < 3), ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t → ∀ eps : ℝ, 0 < eps →
        ∃ delta : ℝ, 0 < delta ∧ ∀ h : ℝ, h ≠ 0 → |h| < delta → 0 ≤ t + h →
          ∀ ell ≤ k, ∀ x, ‖iteratedFDeriv ℝ ell
            (fun y => h⁻¹ * (F j (t + h) y - F j t y) - F ⟨(j : ℕ) + 1, by omega⟩ t y) x‖ ≤ eps) := by
  have hd1 : 1 ≤ d := by omega
  have hs0' : 0 < criticalS d := HRS.MS.S82R.s82r_criticalS_pos hd1
  have hsd' : criticalS d < d := HRS.MS.S82R.s82r_criticalS_lt hd1
  have hcrit : criticalS d = (d : ℝ) / 2 := rfl
  have hs0 : 0 ≤ (d : ℝ) / 2 := by rw [← hcrit]; exact hs0'.le
  have hsd : (d : ℝ) / 2 < d := by rw [← hcrit]; exact hsd'
  have hν : 0 < beta⁻¹ := inv_pos.2 hbeta
  obtain ⟨θ, Q, c, hθ, hC, O, hρS, huniq⟩ := r26t8a_f11_setup d hd a beta ha hbeta rho hrho
  set Cf := fixedViscosityCoeff ((d : ℝ) / 2) (-1) Q beta⁻¹ c rho with hCf
  have hLit : ∀ j : ℕ, r26t8a_LIter a beta rho j f =
      (fun g x => generatorW Cf 0 g x)^[j] ⇑f := by
    intro j; unfold r26t8a_LIter; rw [hC]
  set F : Fin 4 → ℝ → Euc d → ℝ := fun j t =>
    propagatorW Cf 0 t ((fun g x => generatorW Cf 0 g x)^[(j : ℕ)] ⇑f) with hF
  -- the family realises the evolutions at every level and horizon
  have hFev : ∀ (k₁ : ℕ), (4 : ℝ) + (d : ℝ) / 2 < k₁ → ∀ (T : ℝ), 0 ≤ T →
      ∀ a' : Fin 4, ∀ t ∈ Set.Icc (0 : ℝ) T, ∃ u,
        HRS.Whole.IsUlBackwardEvolution θ k₁ Cf t ((fun g x => generatorW Cf 0 g x)^[(a' : ℕ)] ⇑f) u ∧
          F a' t = u 0 := by
    intro k₁ hk₁ T hT a' t ht
    obtain ⟨w, hw, hprop⟩ := HRS.MS.S52B.s52b_prop_eq O Q hk₁ ht.1 (huniq t)
      (HRS.MS.Ul.ul6_closure O Q f (a' : ℕ) k₁)
    refine ⟨w, hw, ?_⟩
    have := hprop 0 t le_rfl ht.1 le_rfl
    simpa [hF] using this
  have horb : ∀ k : ℕ, ∀ T : ℝ, 0 ≤ T → ∃ k₁ : ℕ, (4 : ℝ) + (d : ℝ) / 2 < k₁ ∧
      ((∀ t ∈ Set.Icc (0 : ℝ) T, ∀ a' : Fin 4, MemCb k (F a' t)) ∧
      ∀ (a' : Fin 4) (ha3 : (a' : ℕ) < 3), ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ h : ℝ, h ≠ 0 → |h| < δ → t + h ∈ Set.Icc (0 : ℝ) T →
          ∀ j ≤ k, ∀ x : Euc d, ‖iteratedFDeriv ℝ j
            (fun y => h⁻¹ * (F a' (t + h) y - F a' t y) - F ⟨(a' : ℕ) + 1, by omega⟩ t y) x‖ ≤ ε) := by
    intro k T hT
    obtain ⟨k₀, J, H⟩ := HRS.MS.Ul.ul_adjoint_orbit_bounds_proof hd ((d : ℝ) / 2) hs0 hsd θ hθ k
    set k₁ : ℕ := max k₀ (max (⌊(k : ℝ) + (d : ℝ) / 2⌋₊ + 1) (⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ + 1)) with hk₁
    have hk₁4 : (4 : ℝ) + (d : ℝ) / 2 < k₁ := by
      have h1 : (4 : ℝ) + (d : ℝ) / 2 < ((⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast; exact Nat.lt_floor_add_one _
      exact h1.trans_le (by exact_mod_cast le_trans (le_max_right _ _) (le_max_right _ _))
    have hkk : (k : ℝ) + (d : ℝ) / 2 < k₁ := by
      have h1 : (k : ℝ) + (d : ℝ) / 2 < ((⌊(k : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast; exact Nat.lt_floor_add_one _
      exact h1.trans_le (by exact_mod_cast le_trans (le_max_left _ _) (le_max_right _ _))
    obtain ⟨C, hC'⟩ := H k₁ (le_max_left _ _) hkk T beta⁻¹ Q rho c hT hν hρS
      ⟨_, O.hσ, O.hc⟩
    obtain ⟨-, hall⟩ := hC' f
    exact ⟨k₁, hk₁4, hall F (hFev k₁ hk₁4 T hT) |> fun h => ⟨fun t ht a' => h.1 t ht |>.1 a', h.2⟩⟩
  refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
  · intro j t ht
    rw [hC, hLit]
  · intro j t ht
    obtain ⟨K, hK⟩ : ∃ K : ℕ, (4 : ℝ) + (d : ℝ) / 2 < K := ⟨⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ + 1, by
      push_cast; exact Nat.lt_floor_add_one _⟩
    obtain ⟨u, hu, hFu⟩ := hFev K hK t ht j t ⟨ht, le_rfl⟩
    refine ⟨u, ?_, hFu⟩
    rw [hC, hLit]
    exact hu.classicalSol
  · intro j t ht k
    obtain ⟨k₁, -, hcb, -⟩ := horb k t ht
    exact hcb t ⟨ht, le_rfl⟩ j
  · intro j t ht
    refine contDiff_infty.2 fun k => ?_
    obtain ⟨k₁, -, hcb, -⟩ := horb k t ht
    exact (hcb t ⟨ht, le_rfl⟩ j).1
  · intro j hj k t ht ε hε
    obtain ⟨k₁, -, -, hd'⟩ := horb k (t + 1) (by linarith)
    obtain ⟨δ, hδ, hδ'⟩ := hd' j hj t ⟨ht, by linarith⟩ ε hε
    refine ⟨min δ 1, lt_min hδ one_pos, fun h hh0 hh h0 ℓ hℓ x => ?_⟩
    refine hδ' h hh0 (lt_of_lt_of_le hh (min_le_left _ _)) ⟨h0, ?_⟩ ℓ hℓ x
    have := lt_of_lt_of_le hh (min_le_right _ _)
    have := (abs_lt.1 this).2
    linarith


/-- time homogeneity of the propagator on the UL data `L^j f` -/
theorem r26t8a_prop_shift (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (f : SchwartzMap (Euc d) ℝ) (j : ℕ) (r t : ℝ) (hr : 0 ≤ r) (hrt : r ≤ t) :
    propagatorW (critCoeff d a beta rho) r t (r26t8a_LIter a beta rho j f) =
      propagatorW (critCoeff d a beta rho) 0 (t - r) (r26t8a_LIter a beta rho j f) := by
  obtain ⟨θ, Q, c, hθ, hC, O, hρS, huniq⟩ := r26t8a_f11_setup d hd a beta ha hbeta rho hrho
  have hd1 : 1 ≤ d := by omega
  have hs0' : 0 < criticalS d := HRS.MS.S82R.s82r_criticalS_pos hd1
  have hsd' : criticalS d < d := HRS.MS.S82R.s82r_criticalS_lt hd1
  have hLit : r26t8a_LIter a beta rho j f =
      (fun g x => generatorW (fixedViscosityCoeff ((d : ℝ) / 2) (-1) Q beta⁻¹ c rho) 0 g x)^[j] ⇑f := by
    unfold r26t8a_LIter; rw [hC]
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (4 : ℝ) + (d : ℝ) / 2 < K := ⟨⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ + 1, by
    push_cast; exact Nat.lt_floor_add_one _⟩
  obtain ⟨w, -, hprop⟩ := HRS.MS.S52B.s52b_prop_eq O Q hK (T := t) (hr.trans hrt) (huniq t)
    (HRS.MS.Ul.ul6_closure O Q f j K)
  rw [hC, hLit]
  have h1 := hprop r t hr hrt le_rfl
  have h2 := hprop 0 (t - r) le_rfl (by linarith) (by linarith)
  rw [h1, h2]
  congr 1
  ring

end HRS.MS.R26T8A

end
