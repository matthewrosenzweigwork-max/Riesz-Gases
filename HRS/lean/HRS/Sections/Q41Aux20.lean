import HRS.Sections.Q41Aux19
import HRS.Sections.Q41Aux14
import HRS.Sections.Q41Aux13

/-!
# Packet Q41, helper 20: existence of the stationary Gaussian field

`q41_field_exists`: for `d ≥ 2`, `0 ≤ s < d`, `β > 0`, smooth `V`, any thermal density `ρ_β` and any
`m` with `d + 2 < 2m`, there is a probability space carrying an `E_m`-valued stationary Gaussian
field (`HRS.IsStationaryGaussianField`).  The mode kernel `r t s k l = κ(t,s; e_k, e_l)` is verified
to be symmetric, positive semidefinite (Corollary 5.3, `exists_cov_comparison`), bounded, with
increments `≲ ⟨k⟩² |t - s|`; the abstract Gaussian construction of `q41_smooth_process` applies.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.Q41

open HRS HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear HRS.PDE.MFPair

variable {d : ℕ}

/-- Positive semidefiniteness of the stationary covariance for smooth tests, under the (a priori)
continuity and positivity of the thermal density. -/
theorem q41_lagcov_psd (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {ρβ : Torus d → ℝ}
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Continuous ρβ)
    (hpos : ∀ x, 0 < ρβ x) {p : ℕ} (τ : Fin p → ℝ) (hτ : ∀ a, 0 ≤ τ a)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    (stationaryLagCov d s β (mfData d s hs0 hsd V β hβ) ρβ τ φ).PosSemidef := by
  set K : ℕ := 8 * d + 40 with hKdef
  have hconst : Torus.IsSmooth (fun _ : Torus d => (1 : ℝ)) := by
    unfold Torus.IsSmooth Torus.IsCk
    exact contDiff_const
  have hFR : FiniteRegHyp d s β β K V (fun _ => 1) := by
    refine ⟨hs0, hsd, hβ, le_rfl, ?_, isCk_of_smooth_ps hV (K + 2), ?_,
      MFSemigroup.memSobolev_of_isSmooth hconst _, ⟨1, one_pos, fun x => le_rfl⟩⟩
    · rw [hKdef]; push_cast; nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    · exact ⟨fun _ => zero_le_one, measurable_const, by simp⟩
  obtain ⟨ρc, hρc, -⟩ := MFGlobal.finite_reg_exists_unique (by omega) s β β K V _ hFR β
    ⟨le_rfl, le_rfl⟩
  have hj : (d : ℝ) / 2 + 4 < ((2 * d + 10 : ℕ) : ℝ) := by
    push_cast; nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  exact (exists_cov_comparison (by omega) s β β K V _ hFR (2 * d + 10) ⟨d + 5, by omega⟩ hj
    (by rw [hKdef]; omega) β ⟨le_rfl, le_rfl⟩ ρc hρc ρβ hρβ hρC hpos p τ hτ φ hφ).1

section Kernel

variable {s β c₀ Λ₀ : ℝ} {V ρβ : Torus d → ℝ}
  (H : FrozenHyp d s (2 * mStar d + 4) β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ)

/-- The stationary kernel on the real Fourier modes. -/
def q41_r (t t' : ℝ) (k l : NonzeroLattice d) : ℝ :=
  q41_cov2 H t t' (Torus.realMode k) (Torus.realMode l)

lemma q41_Cv_S0 (hd : 1 ≤ d) {φ ψ : Torus d → ℝ} (hφ : Continuous φ)
    (hψ : Torus.IsSmooth ψ) :
    susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ (Sg H 0 ψ) =
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ ψ := by
  have hC := q41_covProps hd H
  have hψc := q41_cont_of_smooth hψ
  have hψck : Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) ψ := isCk_of_smooth_ps hψ _
  have hψm : MemSobolev ((mStar d : ℝ) + 4) ψ := (sob_of_isCk_ps hψck).2
  have e0 : Sg H 0 ψ = fun x => ψ x + -pair (withDensityReal ρβ) ψ := by
    funext x
    have := congrFun (frozen_zero hd H hψc hψm) x
    simp only [projMean] at this
    rw [this]; ring
  rw [e0]
  exact hC.const2 φ ψ _ hφ hψc

lemma q41_cov2_symm (hd : 1 ≤ d) {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (hψ : Torus.IsSmooth ψ) (t t' : ℝ) :
    q41_cov2 H t t' φ ψ = q41_cov2 H t' t ψ φ := by
  have hC := q41_covProps hd H
  obtain ⟨M, hM0, hM⟩ := q41_S_bound H hd
  have hφc := q41_cont_of_smooth hφ
  have hψc := q41_cont_of_smooth hψ
  have hφck : Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) φ := isCk_of_smooth_ps hφ _
  have hψck : Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) ψ := isCk_of_smooth_ps hψ _
  unfold q41_cov2
  by_cases h1 : t ≤ t'
  · by_cases h2 : t' ≤ t
    · have e : t = t' := le_antisymm h1 h2
      subst e
      simp only [if_pos le_rfl, sub_self]
      rw [q41_Cv_S0 H hd hφc hψ, q41_Cv_S0 H hd hψc hφ]
      exact hC.symm φ ψ hφc hψc
    · simp only [if_pos h1, if_neg h2]
      exact hC.symm _ _ hφc ((hM ψ hψck (t' - t) (by linarith)).1)
  · have h2 : t' ≤ t := by linarith
    simp only [if_neg h1, if_pos h2]
    exact hC.symm _ _ ((hM φ hφck (t - t') (by linarith)).1) hψc

theorem q41_modeKernel (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (hV : Torus.IsSmooth V) (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (hρC : Continuous ρβ) (hpos : ∀ x, 0 < ρβ x) :
    ModeKernel d (q41_r H) := by
  have hd1 : 1 ≤ d := by omega
  have hC := q41_covProps hd1 H
  obtain ⟨M, hM0, hM⟩ := q41_S_bound H hd1
  have hmc := q41_realMode_cont (d := d)
  have hmck := q41_realMode_ck (d := d)
  have hsm := fun k : NonzeroLattice d => HRS.FieldSingAux.isSmooth_realMode k
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t t' k l
    exact q41_cov2_symm H hd1 (hsm k) (hsm l) t t'
  · intro ι _ _ τ k hτ
    classical
    set n := Fintype.card ι with hn
    let eqv : ι ≃ Fin n := Fintype.equivFin ι
    have hP := q41_lagcov_psd hd hs0 hsd hβ hV hρβ hρC hpos
      (fun a : Fin n => τ (eqv.symm a)) (fun a => hτ _)
      (fun a : Fin n => Torus.realMode (k (eqv.symm a))) (fun a => hsm _)
    have hsub := hP.submatrix eqv
    convert hsub using 1
    ext a b
    simp [q41_r, q41_cov2, PDE.stationaryLagCov]
  · obtain ⟨K, hK0, hK⟩ := hC.bound
    refine ⟨K * Real.sqrt 2 * Real.sqrt 2, fun t k ht => ?_⟩
    have e : q41_r H t t k k = susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β
        (Torus.realMode k) (Torus.realMode k) := by
      simp only [q41_r, q41_cov2, if_pos le_rfl, sub_self]
      exact q41_Cv_S0 H hd1 (hmc k) (hsm k)
    rw [e]
    exact (le_abs_self _).trans (hK _ _ _ _ (hmc k) (hmc k) (fun x => Torus.abs_realMode_le k x)
      (fun x => Torus.abs_realMode_le k x))
  · obtain ⟨Cc, hCc⟩ := Torus.cbNorm_realMode_le (d := d) 1
    refine ⟨2 * β⁻¹ * Cc ^ 2, fun t t' k ht ht' => ?_⟩
    have hdiag : ∀ u : ℝ, q41_r H u u k k = susceptibilityCov (periodicRiesz d s)
        (withDensityReal ρβ) β (Torus.realMode k) (Torus.realMode k) := by
      intro u
      simp only [q41_r, q41_cov2, if_pos le_rfl, sub_self]
      exact q41_Cv_S0 H hd1 (hmc k) (hsm k)
    have hcb : Torus.cbNorm 1 (Torus.realMode k) ^ 2 ≤ Cc ^ 2 * Lattice.jp k.1 ^ 2 := by
      have h0 := cbNorm_nonneg_ps (d := d) 1 (Torus.realMode k)
      have := hCc k
      calc Torus.cbNorm 1 (Torus.realMode k) ^ 2 ≤ (Cc * Lattice.jp k.1 ^ 1) ^ 2 :=
            pow_le_pow_left₀ h0 this 2
        _ = Cc ^ 2 * Lattice.jp k.1 ^ 2 := by ring
    have hlip : ∀ u u' : ℝ, 0 ≤ u → u ≤ u' →
        q41_r H u u k k - q41_r H u u' k k ≤ β⁻¹ * (Cc ^ 2 * Lattice.jp k.1 ^ 2) * (u' - u) := by
      intro u u' hu huu'
      have hh : 0 ≤ u' - u := by linarith
      have hinc := q41_inc_bound H hd1 (hsm k) hh
      rw [hdiag u]
      have e2 : q41_r H u u' k k = susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β
          (Torus.realMode k) (Sg H (u' - u) (Torus.realMode k)) := by
        simp only [q41_r, q41_cov2, if_pos huu']
      rw [e2]
      refine hinc.trans ?_
      have hνpos : 0 < β⁻¹ := inv_pos.2 hβ
      have := mul_le_mul_of_nonneg_left hcb hνpos.le
      nlinarith
    have key : ∀ u u' : ℝ, 0 ≤ u → u ≤ u' →
        q41_r H u u k k + q41_r H u' u' k k - 2 * q41_r H u u' k k ≤
          2 * β⁻¹ * Cc ^ 2 * Lattice.jp k.1 ^ 2 * |u - u'| := by
      intro u u' hu huu'
      have := hlip u u' hu huu'
      rw [hdiag u'] at *
      rw [hdiag u] at this ⊢
      rw [abs_of_nonpos (by linarith)]
      nlinarith
    rcases le_total t t' with h | h
    · exact key t t' ht h
    · have := key t' t ht' h
      have hs : q41_r H t t' k k = q41_r H t' t k k :=
        q41_cov2_symm H hd1 (hsm k) (hsm k) t t'
      rw [hs, abs_sub_comm]
      linarith

end Kernel

end HRS.Q41
