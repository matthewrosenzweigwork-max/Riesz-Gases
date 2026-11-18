import HRS.MS.UniqQAux8
import HRS.MS.OrbFeatAux2

/-!
# UNIQ-Q, part 9: `S52bUniq` for the frozen coefficient

The difference of two `IsClassicalAdjointW` solutions with the same terminal datum is a `UqSol` with the source
`S = ⟨c,∇u⟩ - N u` (`ul5_gen_fixed`, linearity of `ulNL`: `ul_nl_sub`); `uniqq_zero` gives `u = 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.UniqQ

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Lc HRS.MS.S52B

variable {d : ℕ}

theorem uniqq_cont_val {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) : Continuous fun p : Icc (0 : ℝ) t × Euc d => f p.1 p.2 := by
  have h := hf.cont_c2 0 (by norm_num)
  have e : (fun p : Icc (0 : ℝ) t × Euc d => f p.1 p.2) = fun p =>
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Euc d) ℝ (fun i => i.elim0))
        (iteratedFDeriv ℝ 0 (f p.1) p.2) := by
    funext p
    simp [iteratedFDeriv_zero_apply]
  rw [e]
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Euc d) ℝ (fun i => i.elim0)).continuous.comp h

theorem uniqq_memCb {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) t) : MemCb 2 (f r) := by
  refine ⟨hf.c2 r hr, fun j hj => ?_⟩
  obtain ⟨B, hB⟩ := hf.bdd j hj
  exact ⟨B, by rintro _ ⟨x, rfl⟩; exact hB r hr x⟩

/-- **uniqueness of classical adjoint solutions for the frozen coefficient** -/
theorem uniqq_S52bUniq {s ν : ℝ} (hν : 0 < ν) (hs0 : 0 ≤ s) (hsd : s < d)
    (Q : Matrix (Fin d) (Fin d) ℝ) {ρ : Euc d → ℝ} (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ)
    {c : Euc d → Euc d} (hc : ∃ Λ : ℝ, ∀ x, ‖c x‖ ≤ Λ) (T : ℝ) :
    S52bUniq (fixedViscosityCoeff s (-1) Q ν c ρ) T := by
  obtain ⟨ψ, rfl⟩ := hρ
  obtain ⟨Λ, hΛ⟩ := hc
  intro t ht φ f1 f2 h1 h2 r hr
  set u : ℝ → Euc d → ℝ := fun r x => f1 r x - f2 r x with hu
  set S : ℝ → Euc d → ℝ := fun r x =>
    inner ℝ (c x) (gradient (u r) x) - ulNL s (-1) ψ (u r) x with hS
  have hsol : UqSol Q ν t u S := by
    refine ⟨fun r hr => (h1.c2 r hr).sub (h2.c2 r hr), ?_, ?_, ?_⟩
    · have key : ∀ j, j ≤ 2 → ∃ B : ℝ, ∀ r ∈ Icc (0 : ℝ) t, ∀ x, ‖iteratedFDeriv ℝ j (u r) x‖ ≤ B := by
        intro j hj
        obtain ⟨B1, hB1⟩ := h1.bdd j hj
        obtain ⟨B2, hB2⟩ := h2.bdd j hj
        refine ⟨B1 + B2, fun r hr x => ?_⟩
        have e : iteratedFDeriv ℝ j (fun y => f1 r y - f2 r y) x =
            iteratedFDeriv ℝ j (f1 r) x - iteratedFDeriv ℝ j (f2 r) x :=
          iteratedFDeriv_sub_apply ((h1.c2 r hr).of_le (by exact_mod_cast hj)).contDiffAt
            ((h2.c2 r hr).of_le (by exact_mod_cast hj)).contDiffAt
        simp only [hu]
        rw [e]
        exact (norm_sub_le _ _).trans (add_le_add (hB1 r hr x) (hB2 r hr x))
      obtain ⟨B0, hB0⟩ := key 0 (by norm_num)
      obtain ⟨B1, hB1⟩ := key 1 (by norm_num)
      obtain ⟨B2, hB2⟩ := key 2 (by norm_num)
      refine ⟨max (max B0 B1) B2, fun j hj r hr x => ?_⟩
      interval_cases j
      · exact (hB0 r hr x).trans ((le_max_left _ _).trans (le_max_left _ _))
      · exact (hB1 r hr x).trans ((le_max_right _ _).trans (le_max_left _ _))
      · exact (hB2 r hr x).trans (le_max_right _ _)
    · exact (uniqq_cont_val h1).sub (uniqq_cont_val h2)
    · intro x r hr
      have hrI : r ∈ Icc (0 : ℝ) t := ⟨hr.1.le, hr.2.le⟩
      have hd := (h1.time_deriv x r hr).sub (h2.time_deriv x r hr)
      refine hd.congr_deriv ?_
      have g1 := ul5_gen_fixed s (-1) Q ν c ψ r (f1 r) x
      have g2 := ul5_gen_fixed s (-1) Q ν c ψ r (f2 r) x
      have hl := uqL0_sub Q ν (h1.c2 r hrI) (h2.c2 r hrI) x
      have hg := lu_grad_sub ((h1.c2 r hrI).differentiable (by norm_num))
        ((h2.c2 r hrI).differentiable (by norm_num)) x
      have hn := ul_nl_sub hs0 hsd (-1) ψ ⟨ψ, rfl⟩ (m := 2) le_rfl (uniqq_memCb h1 hrI)
        (uniqq_memCb h2 hrI) x
      have hS' : S r x = inner ℝ (c x) (gradient (f1 r) x) - inner ℝ (c x) (gradient (f2 r) x) -
          (ulNL s (-1) ψ (f1 r) x - ulNL s (-1) ψ (f2 r) x) := by
        simp only [hS, hu]
        rw [hg, inner_sub_right, hn]
      have e2 : uqL0 Q ν (u r) x = uqL0 Q ν (f1 r) x - uqL0 Q ν (f2 r) x := hl
      unfold ulPert ul5A at g1 g2
      show -generatorW (fixedViscosityCoeff s (-1) Q ν c ψ) r (f1 r) x -
        -generatorW (fixedViscosityCoeff s (-1) Q ν c ψ) r (f2 r) x = -(uqL0 Q ν (u r) x + S r x)
      rw [e2, hS', g1, g2]
      simp only [uqL0]
      ring
  have hz : ∀ y, u t y = 0 := fun y => by
    simp only [hu, h1.terminal, h2.terminal, sub_self]
  have := uniqq_zero hν hs0 hsd (-1) ψ hΛ ht.1 hsol (fun r x => rfl) hz r hr
  funext y
  have := this y
  simp only [hu] at this
  linarith

end HRS.MS.UniqQ
