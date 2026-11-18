import HRS.MS.S88BDDefs

/-!
# S8.8.A01: actual classical orbit and compact-time `C_b` regularity

`s88_regular_orbit`: for every thermal equilibrium `ρ` and every `m ≥ wholeSpaceIndex d`, the orbit
`t ↦ propagatorW (critCoeff d a β ρ) 0 t (oscTestFun m α)` has classical adjoint witnesses at every
nonnegative horizon, lies in `C_b^2`, is scalarly continuous on compact time intervals and locally bounded.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S88Breakdown

open HRS HRS.Whole HRS.MS.Ul HRS.MS.S52B HRS.MS.S53 HRS.MS.S21

variable {d : ℕ}

theorem s88_coeff_eq (a β : ℝ) (ρ : Euc d → ℝ) :
    critCoeff d a β ρ = fixedViscosityCoeff ((d : ℝ) / 2) (-1)
      (Torus.symPart (a • (1 : Matrix (Fin d) (Fin d) ℝ))) β⁻¹
      (fun x => (fun _ : Euc d => (0 : Euc d)) x -
        convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρ x) ρ := by
  unfold critCoeff
  rw [s21_dyn_eq, s53_coeff_eq]

theorem s88_setup (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (T : ℝ) {ρ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) :
    ∃ θ : Euc d → ℝ, ∃ O : UlOrb d ((d : ℝ) / 2) β⁻¹ ρ (fun _ => (0 : Euc d))
      (fun x => (fun _ : Euc d => (0 : Euc d)) x -
        convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρ x) θ,
      S52bUniq (fixedViscosityCoeff ((d : ℝ) / 2) (-1)
        (Torus.symPart (a • (1 : Matrix (Fin d) (Fin d) ℝ))) β⁻¹
        (fun x => (fun _ : Euc d => (0 : Euc d)) x -
          convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρ x) ρ) T := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hρS : IsSchwartzDensity ρ := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ]; exact s21_schwartz_thermal hd hs0 hsd ha hβ
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  obtain ⟨θ, hθ⟩ := s52b_exists_ulCutoff d
  have hO : UlOrb d ((d : ℝ) / 2) β⁻¹ ρ (fun _ => (0 : Euc d))
      (fun x => (fun _ : Euc d => (0 : Euc d)) x -
        convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρ x) θ :=
    ⟨hd, hs0, hsd, hν, hρS.2.elim fun ψ hψ => ⟨ψ, hψ⟩, fun i => ⟨0, by ext x; simp⟩, rfl, hθ⟩
  have huniq := s53_uniq hd hs0 hsd hν (a • (1 : Matrix (Fin d) (Fin d) ℝ)) hρS T
  rw [s53_coeff_eq] at huniq
  exact ⟨θ, hO, huniq⟩

/-- The stationary orbit data at the requested index `m`, not only at the threshold index. -/
theorem s88_orbit_data (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {m : ℝ}
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) {T : ℝ} (hT : 0 ≤ T) {ρ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) :
    ∃ (b : MultiIndex d → ℝ) (K : ℝ) (G0 G1 G2 G3 : MultiIndex d → ℝ → Euc d → ℝ),
      S21GOrbit (critCoeff d a β ρ) m T K (s21gJ d) b G0 G1 G2 G3 := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  obtain ⟨θ, hO, huniq⟩ := s88_setup hd ha hβ T hρ
  obtain ⟨hK4, hkK⟩ := s21gK0_gt d
  obtain ⟨b, K, G0, G1, G2, G3, Orb⟩ := s21g_orbit_of_uniq hO
    (Torus.symPart (a • (1 : Matrix (Fin d) (Fin d) ℝ))) m hT huniq (s21gJ d) (s21gK0 d) hK4 hkK
    (lt_of_lt_of_le (s21g_index_bound hd _ hs0 hsd) hm)
  rw [← s88_coeff_eq] at Orb
  exact ⟨b, K, G0, G1, G2, G3, Orb⟩

/-- The classical adjoint witness at every nonnegative horizon, at the requested index `m`. -/
theorem s88_classical_exists (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (m : ℝ)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) (α : MultiIndex d)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW (critCoeff d a β ρ) t (oscTestFun m α) f := by
  obtain ⟨θ, hO, huniq⟩ := s88_setup hd ha hβ t hρ
  obtain ⟨hK4, -⟩ := s21gK0_gt d
  obtain ⟨φ, hφ, -⟩ := s52b_phi (d := d) m α
  have hcl := ul6_closure hO (Torus.symPart (a • (1 : Matrix (Fin d) (Fin d) ℝ))) φ 0 (s21gK0 d)
  obtain ⟨w, hw, -⟩ := s52b_prop_eq hO (Torus.symPart (a • (1 : Matrix (Fin d) (Fin d) ℝ))) hK4 ht
    huniq hcl
  refine ⟨w, ?_⟩
  have e0 : (ul6L ((d : ℝ) / 2) (Torus.symPart (a • (1 : Matrix (Fin d) (Fin d) ℝ))) β⁻¹
      (fun x => (fun _ : Euc d => (0 : Euc d)) x -
        convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρ x) ρ φ 0) = oscTestFun m α := by
    rw [← hφ]; rfl
  have := hw.classicalSol
  rw [e0] at this
  rw [s88_coeff_eq]
  exact this

theorem s88_memCb_mono {J : ℕ} {g : Euc d → ℝ} (h : MemCb J g) (hJ : 2 ≤ J) : MemCb 2 g :=
  ⟨h.1.of_le (by exact_mod_cast hJ), fun j hj => h.2 j (hj.trans hJ)⟩

theorem s88_regular_orbit {d : ℕ} (hd : 2 ≤ d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (m : ℝ) (hm : (wholeSpaceIndex d : ℝ) ≤ m)
    (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) :
    S88OrbitRegular (critCoeff d a β ρ) m := by
  have hJ : 2 ≤ s21gJ d := by unfold s21gJ; omega
  refine ⟨fun α t ht => s88_classical_exists hd ha hβ m hρ α ht, ?_, ?_, ?_⟩
  · intro α t ht
    obtain ⟨b, K, G0, G1, G2, G3, Orb⟩ := s88_orbit_data hd ha hβ hm ht hρ
    have h := Orb.mem0 α t ⟨ht, le_rfl⟩
    have e : s88Orbit (critCoeff d a β ρ) m t α = G0 α t := by
      have := Orb.hom α 0 t le_rfl ht le_rfl
      simpa [s88Orbit] using this
    rw [e]
    exact s88_memCb_mono h hJ
  · intro α x T hT
    obtain ⟨b, K, G0, G1, G2, G3, Orb⟩ := s88_orbit_data hd ha hβ hm hT hρ
    have e : ∀ t ∈ Set.Icc (0 : ℝ) T, s88Orbit (critCoeff d a β ρ) m t α x = G0 α t x := by
      intro t ht
      have := Orb.hom α 0 t le_rfl ht.1 ht.2
      simp only [s88Orbit, this, sub_zero]
    refine ContinuousOn.congr (f := fun t : ℝ => G0 α t x) (fun τ hτ => ?_) e
    have := s21g_hasDerivWithin_iter (Orb.mem0 α) (Orb.mem1 α) (Orb.diff0 α)
      (Nat.zero_le (s21gJ d)) x (fun i => (Fin.elim0 i : Euc d)) hτ
    simpa [iteratedFDeriv_zero_apply] using this.continuousWithinAt
  · intro α T hT
    obtain ⟨b, K, G0, G1, G2, G3, Orb⟩ := s88_orbit_data hd ha hβ hm hT hρ
    refine ⟨K * b α, mul_nonneg Orb.hK (Orb.b_nonneg α), fun t ht x => ?_⟩
    have e : s88Orbit (critCoeff d a β ρ) m t α = G0 α t := by
      have := Orb.hom α 0 t le_rfl ht.1 ht.2
      simpa [s88Orbit] using this
    rw [e]
    have h := s21g_abs_iter_le_cb (Orb.mem0 α t ht) (Nat.zero_le (s21gJ d)) x
      (fun i => (Fin.elim0 i : Euc d))
    simp only [iteratedFDeriv_zero_apply, Finset.univ_eq_empty, Finset.prod_empty, mul_one] at h
    exact h.trans (Orb.cb0 α t ht)

end HRS.MS.S88Breakdown
