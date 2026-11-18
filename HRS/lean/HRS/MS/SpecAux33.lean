import HRS.MS.SpecAux32
import HRS.MS.SpecAux30
import HRS.MS.MovLinAux11

/-!
# S8P: the S6.2 semigroup is symmetric for the inner product `⟨x, A y⟩` (S8.7, gap b1)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_T_symm`: for the semigroup `T = mov2d_T` of `mov_linear_proof` and
`A = s8p_Asub h (MovL2Zero ρ) β⁻¹` (`= νI + P Q`),
`⟨T t x, A y⟩ = ⟨x, A (T t y)⟩` for all `x, y ∈ L²_0`, `t ≥ 0`.

Generator symmetry on the Schwartz core is `s8p_WS_symm` (polarised ground-state identity, `SpecAux31`) through the Fubini
bridge `s8p_polar_eq` (`SpecAux32`); the semigroup step is the abstract `s8p_semigroup_symm` (`SpecAux30`), whose
hypotheses are `mov2d_T_zero/add/cont`, the invariance `mov2d_T_core` and the density `mov2d_dense_core` of the core.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec HRS.MS.MovLin

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_T_symm (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) {M : ℝ} (h : S8pRho d s ρ M)
    (x y : MovL2Zero ρ) {t : ℝ} (ht : 0 ≤ t) :
    ⟪mov2d_T H ψ0 hψ0 t x, s8p_Asub h (MovL2Zero ρ) β⁻¹ y⟫ =
      ⟪x, s8p_Asub h (MovL2Zero ρ) β⁻¹ (mov2d_T H ψ0 hψ0 t y)⟫ := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  obtain ⟨hρ, hE, -⟩ := mov2e_thermal H.hd H.hs0 H.hsd H.hβ H.hq H.hρ
  have hTs := mov2d_isSemigroup H ψ0 hψ0
  refine s8p_semigroup_symm (mov2d_T H ψ0 hψ0) (s8p_Asub h (MovL2Zero ρ) β⁻¹) hTs.zero
    (fun a b ha hb => hTs.add a b ha hb) hTs.cont (s8p_Asub_symm h (MovL2Zero ρ) β⁻¹)
    {v : MovL2Zero ρ | ∃ φ : 𝓢R, ∀ᵐ x ∂(volume : Measure (Euc d)), movFun v x = φ x}
    (mov2d_dense_core H ψ0 hψ0) ?_ ?_ ?_ x y ht
  · rintro σ hσ v ⟨φ, hφ⟩
    exact mov2d_T_core H ψ0 hψ0 φ v hφ hσ
  · rintro v ⟨φ, hφ⟩
    obtain ⟨w, -, hw⟩ := hTs.generator φ v hφ
    exact ⟨w, hw⟩
  · rintro v ⟨φ, hφ⟩ v' ⟨ψ, hψ⟩ w w' hw hw'
    obtain ⟨w0, hw0, hg0⟩ := hTs.generator φ v hφ
    obtain ⟨w0', hw0', hg0'⟩ := hTs.generator ψ v' hψ
    have e1 : w = w0 := s8p_isGen_unique hTs.zero hw hg0
    have e2 : w' = w0' := s8p_isGen_unique hTs.zero hw' hg0'
    subst e1 e2
    have k1 : ⟪w, s8p_Asub h (MovL2Zero ρ) β⁻¹ v'⟫ = β⁻¹ * ⟪v', w⟫ +
        s8p_qf s ρ (v' : Lp ℝ 2 (volume : Measure (Euc d))) (w : Lp ℝ 2 (volume : Measure (Euc d))) := by
      rw [← real_inner_comm w]
      exact s8p_Asub_inner h (MovL2Zero ρ) β⁻¹ v' w
    have k2 : ⟪s8p_Asub h (MovL2Zero ρ) β⁻¹ v, w'⟫ = β⁻¹ * ⟪v, w'⟫ +
        s8p_qf s ρ (v : Lp ℝ 2 (volume : Measure (Euc d))) (w' : Lp ℝ 2 (volume : Measure (Euc d))) :=
      s8p_Asub_inner h (MovL2Zero ρ) β⁻¹ v w'
    have h1 := s8p_polar_eq hd1 H.hs0 H.hsd hρ hE h β φ ψ (v' : Lp ℝ 2 (volume : Measure (Euc d)))
      (w : Lp ℝ 2 (volume : Measure (Euc d))) hψ hw0
    have h2 := s8p_polar_eq hd1 H.hs0 H.hsd hρ hE h β ψ φ (v : Lp ℝ 2 (volume : Measure (Euc d)))
      (w' : Lp ℝ 2 (volume : Measure (Euc d))) hφ hw0'
    rw [k1, k2]
    exact h1.trans ((s8p_WS_symm hd1 H.hs0 H.hsd hρ hE β φ ψ).trans h2.symm)

end HRS.MS.Spec
