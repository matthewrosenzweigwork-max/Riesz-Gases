import HRS.MS.FeatDecAux11

/-!
# S8.5 `feature_decay`, part 12 (S85 packet): coefficient forms, uniqueness, existence, `t`-measurability
for the stationary coefficient `C = (⟨s, -1, quadV Q 0, ν⟩).coeff (fun _ => ρ)` with `ρ` a Schwartz density.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.S85

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Adj HRS.MS.S52B HRS.MS.UlW

variable {d : ℕ}

/-- the drift field `c = 0 - ∇g*ρ` -/
def s85c (s : ℝ) (ρ : Euc d → ℝ) : Euc d → Euc d :=
  fun x => (fun _ : Euc d => (0 : Euc d)) x - convGradConvW (rieszKernelGrad d s) ρ x

theorem s85_coeff_fv {s ν : ℝ} (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.IsSymm) (ρ : Euc d → ℝ) :
    (⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ) =
      fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ := by
  rw [ulw_coeff_eq (s := s) (ν := ν) (-1) Q hQ 0 ρ]
  congr 1
  funext x
  simp [s85c, Torus.matVec]

theorem s85_sigma (d : ℕ) : ∀ i : Fin d, ∃ ψ : SchwartzMap (Euc d) ℝ,
    ⇑ψ = fun x => ((fun _ : Euc d => (0 : Euc d)) x) i := fun i => ⟨0, by ext x; simp⟩

theorem s85_uniq (hd : 2 ≤ d) {s ν : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (hν : 0 < ν)
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.IsSymm) {ρ : Euc d → ℝ} (hρ : IsSchwartzDensity ρ)
    (T : ℝ) : S52bUniq (fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ) T := by
  intro t ht φ f₁ f₂ h₁ h₂ r hr
  rw [← s85_coeff_fv Q hQ ρ] at h₁ h₂
  have e1 := ulw_unique hd hs0 hsd (-1) Q hQ 0 hν hρ.1 hρ.2 T ht h₁ r hr
  have e2 := ulw_unique hd hs0 hsd (-1) Q hQ 0 hν hρ.1 hρ.2 T ht h₂ r hr
  rw [← e1, ← e2]

/-- existence of the classical adjoint solutions for `φ_α` and `Lφ_α` -/
theorem s85_exists_adjoint (hd : 2 ≤ d) {s ν : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (hν : 0 < ν)
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.IsSymm) {ρ : Euc d → ℝ} (hρ : IsSchwartzDensity ρ)
    (T : ℝ) (hT : 0 ≤ T) (m : ℝ) (α : MultiIndex d) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∃ f, IsClassicalAdjointW ((⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ)) t
      (oscTestFun m α) f) ∧
    ∃ f, IsClassicalAdjointW ((⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ)) t
      (generatorW ((⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ)) t (oscTestFun m α)) f := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨θ, hθ⟩ := s52b_exists_ulCutoff d
  obtain ⟨K, hK⟩ := s85_witness5 hd s hs0 hsd θ hθ 5 le_rfl T ν Q (-1) 0 ρ hT hν hQ hρ
  set k : ℕ := 5 + 1 + ⌈(d : ℝ) / 2⌉₊ with hk
  obtain ⟨ψ, hψ⟩ := hρ.2
  have hρr : UlRapid ρ := by rw [← hψ]; exact ult_schwartz_rapid ψ
  set σ : Euc d → Euc d := fun _ => 0 with hσdef
  have hσ : ∀ i, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = fun x => σ x i := s85_sigma d
  obtain ⟨f, hf, hfN⟩ := s52b_phi (d := d) m α
  obtain ⟨Cu, hCu0, hCu⟩ := ul6_ul_of_S (d := d) hθ k
  obtain ⟨C1, hC10, hC1⟩ := s52b_schwartz_S (d := d) s (k)
  obtain ⟨Cfin, hCfin0, hCfin⟩ := s52b_orbit_ul1 hd hs0 hsd hθ k ν Q ρ ⟨ψ, hψ⟩ σ hσ (s85c s ρ) rfl
  have hcoeff := s85_coeff_fv (s := s) (ν := ν) Q hQ ρ
  refine ⟨?_, ?_⟩
  · -- the datum `φ_α`
    have hφ : ContDiff ℝ ((5 + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) (oscTestFun m α) := by
      rw [← hf]; exact s85_cdiff_nat (f.smooth _) _
    have hul : ulNormE k θ (oscTestFun m α) < ⊤ := by
      rw [← hf]
      have := hCu (-(s + 1)) (C1 * oscNorm ((s52bIdx d s k : ℕ) : ℝ) f) f (by linarith)
        (f.smooth _) (hC1 f)
      exact lt_of_le_of_lt this ENNReal.ofReal_lt_top
    exact (hK t t ht.1 le_rfl ht.2 _ hφ hul).1
  · set g : Euc d → ℝ := generatorW ((⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ)) t
      (oscTestFun m α) with hg
    have hgeq : g = ul6L s Q ν (s85c s ρ) ρ f 1 := by
      have e : ul6L s Q ν (s85c s ρ) ρ f 1 =
          fun x => generatorW (fixedViscosityCoeff s (-1) Q ν (s85c s ρ) ρ) 0 (⇑f) x := by
        rw [ul6L_succ]; rfl
      rw [e, hg, hcoeff, s52b_gen_const, ← hf]
    have hgcd : ContDiff ℝ ∞ g := by
      rw [hgeq]
      exact (orbitData_decay hd hs0 hsd ν Q ρ ⟨ψ, hψ⟩ σ hσ (s85c s ρ) rfl f 1).1
    have hφ : ContDiff ℝ ((5 + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) g := s85_cdiff_nat hgcd _
    have hul : ulNormE k θ g < ⊤ := by
      rw [hgeq]
      exact lt_of_le_of_lt (hCfin f) ENNReal.ofReal_lt_top
    exact (hK t t ht.1 le_rfl ht.2 _ hφ hul).1

end HRS.MS.S85
