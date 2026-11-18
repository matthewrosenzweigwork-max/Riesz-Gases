import HRS.Main.ThermLin2Fu8

/-!
# THERMLIN2 Fu9: `tl2fu_main'`, the Fubini identity for a test family `ψ_r` that is only a.e.-measurable in `r`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c HRS.Uniform.Q45 Classical

variable {d : ℕ} {m T' K : ℝ} {Vev Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
  {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
  {G : ℝ → Ω → NegSobolev d m} {Cd : ℝ → NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ}
  {Zs Zw : ℝ → Ω → NegSobolev d m} {t : ℝ} {φ : Torus d → ℝ} {ψ : ℝ → Torus d → ℝ} {B : ℝ}

theorem tl2fu_memSob_zero (m : ℝ) : MemSobolev m (fun _ : Torus d => (0 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · exact MemLp.zero
  · simp [Torus.funRealCoeff]

theorem tl2fu_coord_zero {m : ℝ} (k : NonzeroLattice d) : NegSobolev.coord (0 : NegSobolev d m) k = 0 := rfl

theorem tl2fu_lpFun_zero (m : ℝ) : lpFun m (fun _ : Torus d => (0 : ℝ)) = 0 := by
  refine NegSobolev_ext fun k => ?_
  rw [coord_lpFun (tl2fu_memSob_zero m), tl2fu_coord_zero]
  simp [Torus.funRealCoeff]

/-- The variance computation for a test family whose coordinates are a.e.-measurable in `r`. -/
theorem tl2fu_main' (D : Tl2FuSetup m T' K Vev Wev P ℱ G Cd Zs Zw) (ht : t ∈ Set.Icc (0 : ℝ) T')
    (hφ : MemSobolev m φ) (hB : 0 ≤ B)
    (hψm : ∀ r ∈ Set.Icc (0 : ℝ) t, MemSobolev m (ψ r))
    (hψB : ∀ r ∈ Set.Icc (0 : ℝ) t, ‖lpFun m (ψ r)‖ ≤ B)
    (hψae : ∀ k, AEMeasurable (fun r => NegSobolev.coord (lpFun m (ψ r)) k)
      (volume.restrict (Set.Icc (0 : ℝ) t)))
    (hweak : ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ z : NegSobolev d m,
      NegSobolev.eval (Vev t σ z) φ - NegSobolev.eval (Wev t σ z) φ =
        ∫ r in σ..t, NegSobolev.eval (Wev r σ z) (ψ r)) :
    ∀ᵐ ω ∂P, NegSobolev.eval (Zs t ω) φ - NegSobolev.eval (Zw t ω) φ =
      ∫ r in (0 : ℝ)..t, NegSobolev.eval (Zw r ω) (ψ r) := by
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) t) with hμ
  have hall : ∀ᵐ r ∂μ, ∀ k, NegSobolev.coord (lpFun m (ψ r)) k = (hψae k).mk _ r :=
    ae_all_iff.2 fun k => (hψae k).ae_eq_mk
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null
    (μ := μ) (s := {r | ¬ ∀ k, NegSobolev.coord (lpFun m (ψ r)) k = (hψae k).mk _ r}) (ae_iff.1 hall)
  have hNae : ∀ᵐ r ∂volume, r ∈ Set.Icc (0 : ℝ) t → r ∉ N := by
    exact (ae_restrict_iff' measurableSet_Icc).1 (measure_eq_zero_iff_ae_notMem.1 hN0)
  set ψ' : ℝ → Torus d → ℝ := fun r => if r ∈ N then (fun _ => 0) else ψ r with hψ'
  have hψ'eq : ∀ r, r ∉ N → ψ' r = ψ r := fun r hr => by simp [hψ', hr]
  have hψ'N : ∀ r, r ∈ N → ψ' r = fun _ => 0 := fun r hr => by simp [hψ', hr]
  have hcoord : ∀ k, (fun r => NegSobolev.coord (lpFun m (ψ' r)) k) =
      fun r => if r ∈ N then 0 else (hψae k).mk _ r := by
    intro k; funext r
    by_cases hr : r ∈ N
    · rw [hψ'N r hr, tl2fu_lpFun_zero, tl2fu_coord_zero]; simp [hr]
    · rw [hψ'eq r hr]; simp only [hr, ↓reduceIte]
      by_contra hne
      exact hr (hsub (fun h => hne (h k)))
  have hmeas : Measurable fun r => lpFun m (ψ' r) := by
    refine measurable_of_coord fun k => ?_
    rw [hcoord k]
    exact Measurable.ite hNm measurable_const (hψae k).measurable_mk
  have hψ'm : ∀ r ∈ Set.Icc (0 : ℝ) t, MemSobolev m (ψ' r) := by
    intro r hr
    by_cases hrN : r ∈ N
    · rw [hψ'N r hrN]; exact tl2fu_memSob_zero m
    · rw [hψ'eq r hrN]; exact hψm r hr
  have hψ'B : ∀ r ∈ Set.Icc (0 : ℝ) t, ‖lpFun m (ψ' r)‖ ≤ B := by
    intro r hr
    by_cases hrN : r ∈ N
    · rw [hψ'N r hrN, tl2fu_lpFun_zero, norm_zero]; exact hB
    · rw [hψ'eq r hrN]; exact hψB r hr
  have hcongr : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Set.uIoc 0 t → ψ' r = ψ r := by
    filter_upwards [hNae] with r hr hrI
    rw [Set.uIoc_of_le ht.1] at hrI
    exact hψ'eq r (hr ⟨hrI.1.le, hrI.2⟩)
  have hweak' : ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ z : NegSobolev d m,
      NegSobolev.eval (Vev t σ z) φ - NegSobolev.eval (Wev t σ z) φ =
        ∫ r in σ..t, NegSobolev.eval (Wev r σ z) (ψ' r) := by
    intro σ hσ z
    rw [hweak σ hσ z]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hNae] with r hr hrI
    rw [Set.uIoc_of_le hσ.2] at hrI
    rw [hψ'eq r (hr ⟨hσ.1.trans hrI.1.le, hrI.2⟩)]
  have E : Tl2FuTest Vev Wev t φ ψ' B :=
    ⟨hφ, hψ'm, fun r hr => hψ'B r hr, hmeas, hweak'⟩
  filter_upwards [tl2fu_main D ht E] with ω hω
  rw [hω]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hcongr] with r hr hrI
  rw [hr hrI]

end HRS.ThermLin.Plan2
