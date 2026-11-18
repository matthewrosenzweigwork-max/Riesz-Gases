import HRS.MS.FldRemAux2
import HRS.MS.OrbFeatAux3

/-!
# S5.3 (`field_remainder`), part 3: the orbit input `S53Orbit` for the fixed-viscosity coefficients

For `Cf = fixedViscosityCoeff s (-1) Q ν c ρ` (standing data `UlOrb`) and the horizon-`T` evolutions `w_a` of the data
`L^a φ_α` (`a ≤ 3`; `ul_evolution_exists` at the level `K0 = ⌊4 + d/2⌋ + 1`), put `G_a α τ = w_a α (T - τ)`.  Then
* `G_a α τ = U_τ L^a φ_α` is the orbit (`ul6_shift`), `propagatorW Cf r t φ_α = G_0 α (t - r)` (uniqueness hypothesis
  `S52bUniq` of S5.2B), the difference quotients are `ul6_main_diff`;
* the `C_b²` bounds use `ul6_cb_bound` and the explicit linear index `s52bIdx d s (K0 + 2)` of S5.2B:
  `‖D² G_a α τ‖ ≤ K · λ_α^{(J - m)/2}`, which is summable for `m - J > 2d`.

Helper names carry the prefix `s53_`, namespace `HRS.MS.S53`.
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S53

open HRS HRS.Whole HRS.MS.Ul HRS.MS.S52B

variable {d : ℕ}

/-- The datum `φ` itself in `H^K_ul` with the linear index (`a = 0` analogue of `s52b_orbit_ul1`). -/
theorem s53_orbit_ul0 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) {θ : Euc d → ℝ}
    (hθ : IsUlCutoff θ) (K : ℕ) (ν : ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ)
    (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ) (σ : Euc d → Euc d)
    (hσ : ∀ i, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = fun x => σ x i) (c : Euc d → Euc d)
    (hc : c = fun x => σ x - convGradConvW (rieszKernelGrad d s) ρ x) :
    ∃ Cfin : ℝ, 0 ≤ Cfin ∧ ∀ f : SchwartzMap (Euc d) ℝ,
      ulNormE K θ (ul6L s Q ν c ρ f 0) ≤
        ENNReal.ofReal (Cfin * oscNorm ((s52bIdx d s (K + 2) : ℕ) : ℝ) f) := by
  obtain ⟨C1, hC10, hC1⟩ := s52b_schwartz_S (d := d) s K
  obtain ⟨ψ, hψ⟩ := hρ
  choose φ hφ using hσ
  obtain ⟨Cu, hCu0, hCu⟩ := ul6_ul_of_S hθ K
  refine ⟨Cu * C1, by positivity, fun f => ?_⟩
  obtain ⟨hcd0, -, -⟩ := orbitData_decay hd hs0 hsd ν Q ρ ⟨ψ, hψ⟩ σ (fun i => ⟨φ i, hφ i⟩) c hc f 0
  have h1 := hCu (-(s + 1)) _ _ (by linarith) hcd0 (hC1 f)
  have e : ul6L s Q ν c ρ f 0 = (⇑f : Euc d → ℝ) := rfl
  rw [e]
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  have hosc : oscNorm ((s52bIdx d s K : ℕ) : ℝ) f ≤ oscNorm ((s52bIdx d s (K + 2) : ℕ) : ℝ) f :=
    ul6_osc_mono (by unfold s52bIdx; omega) f
  have hC1' : 0 ≤ C1 := hC10
  calc Cu * (C1 * oscNorm ((s52bIdx d s K : ℕ) : ℝ) f) ≤ Cu * (C1 * oscNorm ((s52bIdx d s (K + 2) : ℕ) : ℝ) f) := by
        gcongr
    _ = _ := by ring


/-- **The orbit input of S5.3 for a fixed-viscosity coefficient**, conditional on the uniqueness of classical adjoint
solutions (`S52bUniq`, the single hypothesis of S5.2B) and `m - J > 2d` for the linear index
`J = s52bIdx d s (K0 + 2)`, `K0 = ⌊4 + d/2⌋ + 1`. -/
theorem s53_orbit_of_uniq {s ν : ℝ} {ρ : Euc d → ℝ} {σ c : Euc d → Euc d} {θ : Euc d → ℝ}
    (O : UlOrb d s ν ρ σ c θ) (Q : Matrix (Fin d) (Fin d) ℝ) (m : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (huniq : S52bUniq (fixedViscosityCoeff s (-1) Q ν c ρ) T)
    (hJm : ((s52bIdx d s (⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ + 1 + 2) : ℕ) : ℝ) + 2 * d < m) :
    ∃ (b : MultiIndex d → ℝ) (K : ℝ) (G0 G1 G2 : MultiIndex d → ℝ → Euc d → ℝ),
      S53Orbit (fixedViscosityCoeff s (-1) Q ν c ρ) m T K b G0 G1 G2 := by
  set K0 : ℕ := ⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ + 1 with hK0
  have hK4 : (4 : ℝ) + (d : ℝ) / 2 < K0 := by
    rw [hK0]; push_cast; exact Nat.lt_floor_add_one _
  have hkK : ((2 : ℕ) : ℝ) + (d : ℝ) / 2 < K0 := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    push_cast; linarith
  set Cf := fixedViscosityCoeff s (-1) Q ν c ρ with hCf
  set J : ℕ := s52bIdx d s (K0 + 2) with hJ
  obtain ⟨Cf0, hCf00, hCf0⟩ := s53_orbit_ul0 O.hd O.hs0 O.hsd O.hθ K0 ν Q ρ O.hρ σ O.hσ c O.hc
  obtain ⟨Cf1, hCf10, hCf1⟩ := s52b_orbit_ul1 O.hd O.hs0 O.hsd O.hθ K0 ν Q ρ O.hρ σ O.hσ c O.hc
  obtain ⟨Ccb, hCcb0, hCcb⟩ := ul6_cb_bound O Q hK4 hkK T hT
  obtain ⟨Cev, hCev⟩ := ul_evolution_exists O.hs0 O.hsd θ O.hθ K0 hK4 T ν hT O.hν Q (-1) ρ O.hρ c O.smooth
  choose f hf hfN using fun α : MultiIndex d => s52b_phi (d := d) m α
  have hex : ∀ (α : MultiIndex d) (a : Fin 4), ∃ w : ℝ → Euc d → ℝ,
      IsUlBackwardEvolution θ K0 Cf T (ul6L s Q ν c ρ (f α) (a : ℕ)) w := fun α a => by
    obtain ⟨w, hw, -⟩ := hCev T ⟨hT, le_rfl⟩ _ (ul6_closure O Q (f α) (a : ℕ) K0)
    exact ⟨w, hw⟩
  choose w hw using hex
  have hsh : ∀ (α : MultiIndex d) (a : Fin 4), ∀ τ ∈ Icc (0 : ℝ) T,
      IsUlBackwardEvolution θ K0 Cf τ (ul6L s Q ν c ρ (f α) (a : ℕ)) (fun r => w α a (r + (T - τ))) := by
    intro α a τ hτ
    have hδ : T - τ ∈ Icc (0 : ℝ) T := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    have := ul6_shift s (-1) Q ν c ρ hδ (hw α a)
    rwa [show T - (T - τ) = τ by ring] at this
  have hpos : ∀ α : MultiIndex d, 0 ≤ oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := fun α =>
    Real.rpow_nonneg (oscEv_pos α).le _
  -- bounds
  have hbd : ∀ (α : MultiIndex d) (a : Fin 4) (Cfin : ℝ), 0 ≤ Cfin →
      ulNormE K0 θ (ul6L s Q ν c ρ (f α) (a : ℕ)) ≤ ENNReal.ofReal (Cfin * oscNorm (J : ℝ) (f α)) →
      ∀ τ ∈ Icc (0 : ℝ) T, MemCb 2 (w α a (T - τ)) ∧
        (⨆ x, ‖iteratedFDeriv ℝ 2 (w α a (T - τ)) x‖) ≤
          Ccb * Cfin * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) ∧
        cbNorm 2 (w α a (T - τ)) ≤ Ccb * Cfin * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := by
    intro α a Cfin hC hU τ hτ
    obtain ⟨-, hmem, hnb⟩ := hCcb τ hτ _ (ul6_closure O Q (f α) (a : ℕ) K0) K0 le_rfl _ (hsh α a τ hτ)
    simp only [zero_add] at hmem hnb
    refine ⟨hmem, ?_⟩
    have hnn : 0 ≤ Cfin * oscNorm (J : ℝ) (f α) := mul_nonneg hC (Real.sqrt_nonneg _)
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hU
    rw [ENNReal.toReal_ofReal hnn, hfN α J] at h2
    have hsup : (⨆ x, ‖iteratedFDeriv ℝ 2 (w α a (T - τ)) x‖) ≤ cbNorm 2 (w α a (T - τ)) := by
      unfold cbNorm
      exact Finset.single_le_sum (f := fun i => ⨆ z, ‖iteratedFDeriv ℝ i (w α a (T - τ)) z‖)
        (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (by norm_num))
    have hfin : cbNorm 2 (w α a (T - τ)) ≤ Ccb * Cfin * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := by
      refine hnb.trans ?_
      calc Ccb * (ulNormE K0 θ (ul6L s Q ν c ρ (f α) (a : ℕ))).toReal
          ≤ Ccb * (Cfin * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) :=
            mul_le_mul_of_nonneg_left h2 hCcb0
        _ = _ := by ring
    exact ⟨hsup.trans hfin, hfin⟩
  have hmem : ∀ (α : MultiIndex d) (a : Fin 4), ∀ τ ∈ Icc (0 : ℝ) T, MemCb 2 (w α a (T - τ)) := by
    intro α a τ hτ
    obtain ⟨-, hmem, -⟩ := hCcb τ hτ _ (ul6_closure O Q (f α) (a : ℕ) K0) K0 le_rfl _ (hsh α a τ hτ)
    simpa only [zero_add] using hmem
  have hdiff : ∀ (α : MultiIndex d) (a : Fin 4) (ha : (a : ℕ) < 3),
      S53Diff T (fun τ => w α a (T - τ)) (fun τ => w α ⟨(a : ℕ) + 1, by omega⟩ (T - τ)) := by
    intro α a ha τ hτ ε hε
    have hF : ∀ (b' : Fin 4), ∀ t ∈ Icc (0 : ℝ) T, ∃ u,
        IsUlBackwardEvolution θ K0 Cf t (ul6L s Q ν c ρ (f α) (b' : ℕ)) u ∧
          (fun τ => w α b' (T - τ)) t = u 0 := fun b' t ht =>
      ⟨_, hsh α b' t ht, by simp⟩
    exact ul6_main_diff O Q hK4 hkK le_rfl hT (f α) (fun b' τ => w α b' (T - τ)) hF a ha τ hτ ε hε
  have hJm' : (d : ℝ) < (m - J) / 2 := by linarith
  have hsum : Summable fun α : MultiIndex d => oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := by
    have h := (summable_oscEigenvalue_rpow_iff (by have := O.hd; omega : 1 ≤ d) ((m - J) / 2)).2 hJm'
    have e : -((m - (J : ℝ)) / 2) = ((J : ℝ) - m) / 2 := by ring
    rwa [e] at h
  refine ⟨fun α => oscEigenvalue d α ^ (((J : ℝ) - m) / 2), Ccb * max Cf0 Cf1,
    fun α τ => w α 0 (T - τ), fun α τ => w α 1 (T - τ), fun α τ => w α 2 (T - τ), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsum, ?_, ?_⟩
  · -- identification
    intro α r t hr hrt htT
    have hv := hsh α 0 t ⟨hr.trans hrt, htT⟩
    have hprop := s52b_prop_isClassical (C := Cf) ⟨_, hv.classicalSol⟩
    have := huniq t ⟨hr.trans hrt, htT⟩ _ _ _ hprop hv.classicalSol r ⟨hr, hrt⟩
    have e0 : oscTestFun m α = ul6L s Q ν c ρ (f α) ((0 : Fin 4) : ℕ) := by
      rw [← hf α]; rfl
    rw [e0]
    refine this.trans ?_
    show w α 0 (r + (T - t)) = w α 0 (T - (t - r))
    congr 1; ring
  · exact fun α τ hτ => hmem α 0 τ hτ
  · exact fun α τ hτ => hmem α 1 τ hτ
  · exact fun α τ hτ => hmem α 2 τ hτ
  · intro α τ hτ
    refine ((hbd α 0 Cf0 hCf00 (hCf0 (f α)) τ hτ).2.1).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left _ _) hCcb0) (hpos α)
  · intro α τ hτ
    refine ((hbd α 1 Cf1 hCf10 (hCf1 (f α)) τ hτ).2.1).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right _ _) hCcb0) (hpos α)
  · intro α τ hτ
    refine ((hbd α 0 Cf0 hCf00 (hCf0 (f α)) τ hτ).2.2).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left _ _) hCcb0) (hpos α)
  · intro α τ hτ
    refine ((hbd α 1 Cf1 hCf10 (hCf1 (f α)) τ hτ).2.2).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right _ _) hCcb0) (hpos α)
  · exact mul_nonneg hCcb0 (le_max_of_le_left hCf00)
  · exact hpos
  · exact fun α => hdiff α 0 (by norm_num)
  · exact fun α => hdiff α 1 (by norm_num)

end HRS.MS.S53
