import HRS.MS.FixEqP3Aux18

/-!
# S5.7 `fixed_equation` (worker S57P), part 31: the difference of two families (`C_N` against `C`), sup bound of the feature orbits
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

theorem S57pFeData.mono {s : ℝ} {Q : Matrix (Fin d) (Fin d) ℝ} {ν : ℝ} {c : ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ}
    {T T' : ℝ} (h : S57pFeData s Q ν c ρ T) (hT : T' ≤ T) : S57pFeData s Q ν c ρ T' := by
  refine ⟨h.hd, h.hs0, h.hsd, h.hν, ?_, ?_, h.cont.mono (Set.prod_mono (Set.Icc_subset_Icc_right hT) subset_rfl)⟩
  · obtain ⟨A, hA, hdec, hpt⟩ := h.rho
    exact ⟨A, hA, fun t ht => hdec t ⟨ht.1, ht.2.trans hT⟩, fun y => (hpt y).mono (Set.Icc_subset_Icc_right hT)⟩
  · obtain ⟨Λc, hΛ, hc⟩ := h.drift
    exact ⟨Λc, hΛ, fun t ht => hc t ⟨ht.1, ht.2.trans hT⟩⟩

/-- the closeness of two families of coefficients -/
structure S57pDelta (K' : ℕ) (L' : ℝ) (T : ℝ) (ν νN : ℝ) (c cN : ℝ → Euc d → Euc d) (ρ ρN : ℝ → Euc d → ℝ)
    (Dν Dc Dρ : ℝ) : Prop where
  hν : |ν - νN| ≤ Dν
  hc : ∀ τ ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ K' (c τ) ∧ ContDiff ℝ K' (cN τ) ∧
    cbNormVecE K' (fun x => c τ x - cN τ x) ≤ ENNReal.ofReal Dc
  hρ : ∀ τ ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ K' (ρ τ) ∧ ContDiff ℝ K' (ρN τ) ∧
    weightedSupE K' L' (fun x => ρN τ x - ρ τ x) ≤ ENNReal.ofReal Dρ

variable {θ : Euc d → ℝ} {T : ℝ} {n : ℕ} {K KN : ℝ} {s : ℝ} {M Q : Matrix (Fin d) (Fin d) ℝ} {ν νN : ℝ}
  {c cN : ℝ → Euc d → Euc d} {ρ ρN : ℝ → Euc d → ℝ} {A Λc νbar : ℝ} {m : ℝ} {J : ℕ} {Ca CaN Cd CdN : ℝ}
  {L' Dν Dc Dρ : ℝ}

/-- **sup bound of the difference of the feature orbits** -/
theorem s57p_pair_b (hθ : IsUlCutoff θ) (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (M Q : Matrix (Fin d) (Fin d) ℝ)
    (n : ℕ) (K KN : ℝ) (m : ℝ) (J : ℕ)
    (hJ2 : 3 * ((n + 1 + ⌈(d : ℝ) / 2⌉₊ + 3) + 1 + ⌈(d : ℝ) / 2⌉₊) + 9 ≤ J) (T : ℝ) (hT : 0 ≤ T) :
    ∃ Cp1 : ℝ, 0 ≤ Cp1 ∧ ∀ {ν νN : ℝ} {c cN : ℝ → Euc d → Euc d} {ρ ρN : ℝ → Euc d → ℝ} {A Λc νbar : ℝ} {Ca CaN Cd CdN : ℝ}
      {L' Dν Dc Dρ : ℝ}, S57pFx θ T n K s M Q ν c ρ A Λc νbar → S57pFx θ T n KN s M Q νN cN ρN A Λc νbar →
      UlAdjointInput θ (fixedEqCoeff s M Q ν c ρ) T (n + 1 + ⌈(d : ℝ) / 2⌉₊ + 3) K →
      S57pDelta (n + 1 + ⌈(d : ℝ) / 2⌉₊ + 3) L' T ν νN c cN ρ ρN Dν Dc Dρ → (d : ℝ) + 3 ≤ L' →
      S57pOrbBd (fixedEqCoeff s M Q νN cN ρN) T n m J CaN CdN →
      ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ i ≤ n, ∀ x,
        ‖iteratedFDeriv ℝ i (fun y => propagatorW (fixedEqCoeff s M Q ν c ρ) r t (oscTestFun m α) y -
          propagatorW (fixedEqCoeff s M Q νN cN ρN) r t (oscTestFun m α) y) x‖ ≤
          Cp1 * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) * (max Dν 0 + max Dc 0 + max Dρ 0) := by
  set e := ⌈(d : ℝ) / 2⌉₊ with he
  obtain ⟨Cud, hCud0, hCud⟩ := s57p_diff_bound hθ n
  obtain ⟨Cj2, hCj2, hjets2⟩ := s57p_osc_jets hθ hd m J ((n + 1 + e + 3) + 1 + e) hJ2
  obtain ⟨hCu20, hCu2⟩ := s57pCu_spec hθ (n + 1 + e + 3)
  have hCg0 := s57pCg_nonneg (d := d) hs0 M (n + 1 + e)
  refine ⟨T * (|KN| * (Cud * (s57pCg d s M (n + 1 + e) * (|K| * (s57pCu θ hθ (n + 1 + e + 3) * Cj2))))), ?_, ?_⟩
  · have h1 := abs_nonneg KN
    have h2 : 0 ≤ s57pCg d s M (n + 1 + e) := hCg0
    have h3 : 0 ≤ |K| * (s57pCu θ hθ (n + 1 + e + 3) * Cj2) := mul_nonneg (abs_nonneg _) (mul_nonneg hCu20 hCj2)
    exact mul_nonneg hT (mul_nonneg h1 (mul_nonneg hCud0 (mul_nonneg h2 h3)))
  · intro ν νN c cN ρ ρN A Λc νbar Ca CaN Cd CdN L' Dν Dc Dρ Fx FxN adj2 Δ hL' hbdN α t ht r hr i hi x
    have ht0 : 0 ≤ t := ht.1
    have hn4 := Fx.hn4
    have hsub : ∀ τ ∈ Set.Icc (0 : ℝ) t, τ ∈ Set.Icc (0 : ℝ) T := fun τ hτ => ⟨hτ.1, hτ.2.trans ht.2⟩
    have hB2 : 0 ≤ Cj2 * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) :=
      mul_nonneg hCj2 (Real.rpow_nonneg (oscEigenvalue_pos α).le _)
    have hφ2 : ContDiff ℝ (((n + 1 + e + 3) + 1 + e : ℕ) : WithTop ℕ∞) (oscTestFun m α) :=
      s55_cd_of_inf _ (hjets2 α).1
    obtain ⟨hcl, hO⟩ := hCu2 adj2 hB2 hφ2 (fun l hl y => (hjets2 α).2 l hl y) t ht
    have hdb := hCud (M := M) (Q := Q) (ν := ν) (νN := νN) (c := c) (cN := cN) (ρ := ρ) (ρN := ρN) (s := s) (t := t) ht0 hn4
      (Fx.fe.mono ht.2) (FxN.fe.mono ht.2) (fun t' ht' => FxN.fam.uniq t' ⟨ht'.1, ht'.2.trans ht.2⟩)
      (KN := KN) (FxN.fam.mono ht.2).adj (K' := n + 1 + e + 3) le_rfl hL' Δ.hν
      (fun τ hτ => Δ.hc τ (hsub τ hτ)) (fun τ hτ => Δ.hρ τ (hsub τ hτ)) hcl ((hbdN α).1 t ht).1
      (Bf := |K| * (s57pCu θ hθ (n + 1 + e + 3) * (Cj2 * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)))) (BfN := CaN * oscEigenvalue d α ^ (((J : ℝ) - m) / 2))
      (fun r' hr' => hO r' hr')
      (fun r' hr' => ⟨(((hbdN α).1 t ht).2 r' hr').1.of_le (by exact_mod_cast (by omega : 4 ≤ n + 1)),
        fun j hj y => (((hbdN α).1 t ht).2 r' hr').2 j (by omega) y⟩) r hr i hi x
    refine hdb.trans ?_
    have hΔ : 0 ≤ max Dν 0 + max Dc 0 + max Dρ 0 := by positivity
    have hlam : 0 ≤ oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := Real.rpow_nonneg (oscEigenvalue_pos α).le _
    have hP : 0 ≤ |KN| * (Cud * (s57pCg d s M (n + 1 + e) * (|K| * (s57pCu θ hθ (n + 1 + e + 3) * Cj2)))) :=
      mul_nonneg (abs_nonneg _) (mul_nonneg hCud0 (mul_nonneg hCg0 (mul_nonneg (abs_nonneg _) (mul_nonneg hCu20 hCj2))))
    calc t * (|KN| * (Cud * (s57pCg d s M (n + 1 + e) * (max Dν 0 + max Dc 0 + max Dρ 0) *
          (|K| * (s57pCu θ hθ (n + 1 + e + 3) * (Cj2 * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)))))))
        = t * ((|KN| * (Cud * (s57pCg d s M (n + 1 + e) * (|K| * (s57pCu θ hθ (n + 1 + e + 3) * Cj2))))) *
            oscEigenvalue d α ^ (((J : ℝ) - m) / 2) * (max Dν 0 + max Dc 0 + max Dρ 0)) := by ring
      _ ≤ T * ((|KN| * (Cud * (s57pCg d s M (n + 1 + e) * (|K| * (s57pCu θ hθ (n + 1 + e + 3) * Cj2))))) *
            oscEigenvalue d α ^ (((J : ℝ) - m) / 2) * (max Dν 0 + max Dc 0 + max Dρ 0)) :=
          mul_le_mul_of_nonneg_right ht.2 (mul_nonneg (mul_nonneg hP hlam) hΔ)
      _ = _ := by ring

end HRS.MS.FixEq
