import HRS.MS.SpecAux45
import HRS.MS.SpecAux21
import HRS.MS.MovDecAux3

/-!
# S8P: Weyl-type growth `ω_n ≥ c (n+1)^{1/d}` of the eigenvalues (S8.7, packet b6)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  Pieces: `s8p_osc_tsum` (the oscillator form of a Schwartz function in terms of the
Hermite Hilbert basis), `s8p_rayleigh` (on the span of the profiles `w_i = √ρ e_i` the oscillator form is at most `Cr (ω_l + 1) ‖·‖²`)
and the dimension count `s8p_growth_count`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec HRS.MS.MovLin

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_osc_tsum (S : 𝓢R) :
    Summable (fun α : MultiIndex d => oscEigenvalue d α * ⟪hermiteLpD α, SchwartzMap.toLp S 2 volume⟫ ^ 2) ∧
      ∑' α : MultiIndex d, oscEigenvalue d α * ⟪hermiteLpD α, SchwartzMap.toLp S 2 volume⟫ ^ 2 =
        oscNorm 1 S ^ 2 := by
  have hc : ∀ α : MultiIndex d, ⟪hermiteLpD α, SchwartzMap.toLp S 2 volume⟫ = hermiteCoeff (⇑S) α :=
    fun α => OscSpace.inner_hermiteLpD_toLp (⇑S) (S.memLp 2) α
  have hm := memOsc_schwartz (1 : ℝ) S
  have e : ∀ α : MultiIndex d, oscEigenvalue d α * ⟪hermiteLpD α, SchwartzMap.toLp S 2 volume⟫ ^ 2 =
      oscEigenvalue d α ^ (1 : ℝ) * hermiteCoeff (⇑S) α ^ 2 := fun α => by
    rw [hc α, Real.rpow_one]
  simp_rw [e]
  refine ⟨hm.2, ?_⟩
  unfold oscNorm
  rw [Real.sq_sqrt (tsum_nonneg fun α => mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) (sq_nonneg _))]

/-- The spectral data at the level of `L²_0`: `A`-orthonormal, `A`-complete Schwartz eigenvectors of `S`. -/
structure S8pEigData (d : ℕ) (s β : ℝ) (ρ : Euc d → ℝ) {M : ℝ} (h : S8pRho d s ρ M) where
  v : ℕ → MovL2Zero ρ
  φ : ℕ → SchwartzMap (Euc d) ℝ
  om : ℕ → ℝ
  lam : ℝ
  lam_pos : 0 < lam
  lam_le : ∀ n, lam ≤ om n
  mono : Monotone om
  hv : ∀ n, ∀ᵐ x ∂(volume : Measure (Euc d)), movFun (v n) x = φ n x
  hS : ∀ n, ∀ᵐ x ∂(volume : Measure (Euc d)), movS d s β ρ (φ n) x = om n * φ n x
  orth : ∀ n m, ⟪v n, s8p_Asub h (MovL2Zero ρ) β⁻¹ (v m)⟫ = if n = m then 1 else 0
  complete : ∀ f : MovL2Zero ρ, (∀ n, ⟪f, s8p_Asub h (MovL2Zero ρ) β⁻¹ (v n)⟫ = 0) → f = 0

theorem s8p_eigData (H : Mov2dTh d s β q ρ) {M : ℝ} (h : S8pRho d s ρ M) :
    Nonempty (S8pEigData d s β ρ h) := by
  obtain ⟨v, φ, oo, lam, hlam, hle, hmono, hv, hS, horth, hcomp⟩ := s8p_spectral_vectors H h
  exact ⟨⟨v, φ, oo, lam, hlam, hle, hmono, hv, hS, horth, hcomp⟩⟩

variable {M : ℝ} {h : S8pRho d s ρ M}

theorem S8pEigData.pair (D : S8pEigData d s β ρ h) (H : Mov2dTh d s β q ρ) (n m : ℕ) :
    ∫ x, mov2eW d s β ρ (D.φ n) x * D.φ m x = if n = m then 1 else 0 := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  obtain ⟨hρ, hE, -⟩ := mov2e_thermal H.hd H.hs0 H.hsd H.hβ H.hq H.hρ
  rw [← s8p_A_pair hd1 H.hs0 H.hsd hρ hE h (D.φ n) (D.φ m) (D.v n) (D.v m) (D.hv n) (D.hv m) β,
    s8p_Asub_symm h (MovL2Zero ρ) β⁻¹ (D.v n) (D.v m), D.orth n m]

theorem S8pEigData.zz_orth (D : S8pEigData d s β ρ h) (H : Mov2dTh d s β q ρ) (i k : ℕ) :
    ∫ x, ∑ j, mov2eZ d s β ρ (D.φ k) j x * mov2eZ d s β ρ (D.φ i) j x =
      D.om i * (if k = i then 1 else 0) := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  obtain ⟨hρ, hE, -⟩ := mov2e_thermal H.hd H.hs0 H.hsd H.hβ H.hq H.hρ
  rw [← (s8p_WS_integral hd1 H.hs0 H.hsd hρ hE β (D.φ i) (D.φ k)).2]
  have : ∫ x, mov2eW d s β ρ (D.φ k) x * movS d s β ρ (D.φ i) x =
      ∫ x, D.om i * (mov2eW d s β ρ (D.φ k) x * D.φ i x) := by
    refine integral_congr_ae ?_
    filter_upwards [D.hS i] with x hx
    rw [hx]; ring
  rw [this, integral_const_mul, D.pair H k i]

end HRS.MS.Spec
