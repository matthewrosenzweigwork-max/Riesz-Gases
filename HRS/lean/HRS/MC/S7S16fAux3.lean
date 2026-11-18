import HRS.MC.Sec7Vocab
import HRS.MC.S7S16e
import HRS.MC.S7S16fAux2
import HRS.Sections.Q38bAux2

/-!
# Packet `slow_correction` (S16f), part 3: `pi_* G` is a nondegenerate diagonal Gaussian

For `rho = 1`, `responseInverse` of a real mode is the Fourier multiplier `(1 + beta ghat(k))^{-1}`
(`q38b_responseInverse_eq`) and the real modes are orthonormal, so the covariance of
`pi_* G = N(0, C)` (`s7e_law_G`) is `diag((1 + beta ghat(k))^{-1}, (1 + beta ghat(-k))^{-1})`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S16f

open HRS HRS.Sec7 HRS.MC.SEdge HRS.MC.Sec7 HRS.MC.Sec7.S16e

variable {d : ℕ}

theorem s16f_ne_neg (k : NonzeroLattice d) : k ≠ s7_neg k := by
  intro h
  have h1 : k.1 = -k.1 := congrArg Subtype.val h
  apply k.2
  funext i
  have := congrFun h1 i
  simp only [Pi.neg_apply] at this
  simp only [Pi.zero_apply]
  omega

theorem s16f_cov_entry (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (kk ll : NonzeroLattice d) :
    ∫ x : Torus d, Torus.realMode kk x *
        responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β (Torus.realMode ll) x =
      (1 + β * rieszCoeff d s ll.1)⁻¹ * (if kk = ll then 1 else 0) := by
  have h := q38b_responseInverse_eq hd hs0 hsd hβ ll 1
  have hf : (fun x => (1 : ℝ) * Torus.realMode ll x) = Torus.realMode ll := by
    funext x; simp
  rw [hf] at h
  calc ∫ x : Torus d, Torus.realMode kk x *
        responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β (Torus.realMode ll) x
      = ∫ x : Torus d, (1 + β * rieszCoeff d s ll.1)⁻¹ * (Torus.realMode kk x * Torus.realMode ll x) := by
        refine integral_congr_ae ?_
        filter_upwards [h] with x hx
        rw [hx]; ring
    _ = _ := by
        rw [integral_const_mul, Torus.realMode_orthonormal]

theorem s16f_law_diag (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ}
    (hβ : 0 < β) (m : ℝ) (hm : (d : ℝ) / 2 < m) (G : Measure (NegSobolev d m))
    [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov m G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) volume β ψ x ∂volume)
    (k : NonzeroLattice d) (π : NegSobolev d m →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (hπ : ∀ F, π F = s7_modePair m k F) :
    ∃ c : Fin 2 → ℝ, (∀ i, 0 < c i) ∧ G.map π = multivariateGaussian 0 (Matrix.diagonal c) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  have hWa : ∀ (u : NegSobolev d m) (a : Fin 2), π u a = NegSobolev.eval u (s7e_phi k a) :=
    fun u a => by rw [hπ]; exact s7e_modePair_eq_eval k u a
  have hlaw : G.map π = multivariateGaussian 0 (Matrix.of fun a b : Fin 2 =>
      ∫ x : Torus d, s7e_phi k a x * responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β
        (s7e_phi k b) x ∂(volume : Measure (Torus d))) := by
    have := s7e_law_G hd hs0 hs hβ.le G hG (s7e_phi k) (s7e_phi_smooth k) π hWa
    rw [this]
    unfold sed_Cmat
    rw [HRS.MC.SEdge.S16a.s16a_wdr_one]
  let kk : Fin 2 → NonzeroLattice d := fun a => if a = 0 then k else s7_neg k
  have hphi : ∀ a, s7e_phi k a = Torus.realMode (kk a) := by
    intro a; simp only [s7e_phi, kk]; split_ifs <;> rfl
  let c : Fin 2 → ℝ := fun a => (1 + β * rieszCoeff d s (kk a).1)⁻¹
  refine ⟨c, fun a => inv_pos.2 (q42_one_add_pos hd hs0 hsd hβ _), ?_⟩
  rw [hlaw]
  congr 2
  ext a b
  simp only [hphi, Matrix.of_apply, Matrix.diagonal_apply]
  rw [s16f_cov_entry hd hs0 hsd hβ]
  have hkk : ∀ a b : Fin 2, kk a = kk b ↔ a = b := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [kk, s16f_ne_neg k, (s16f_ne_neg k).symm]
  by_cases hab : a = b
  · subst hab; simp [c]
  · simp [hab, (hkk a b).not.2 hab]

theorem s16f_fullSupport (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ}
    (hβ : 0 < β) (m : ℝ) (hm : (d : ℝ) / 2 < m) (G : Measure (NegSobolev d m))
    [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov m G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) volume β ψ x ∂volume)
    (k : NonzeroLattice d) (π : NegSobolev d m →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (hπ : ∀ F, π F = s7_modePair m k F) :
    ProbabilityTheory.IsGaussian (G.map π) ∧
    ∀ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U → U.Nonempty → 0 < (G.map π) U := by
  obtain ⟨c, hc, hlaw⟩ := s16f_law_diag hd hs0 hs hβ m hm G hG k π hπ
  refine ⟨by rw [hlaw]; infer_instance, fun U hU hne => ?_⟩
  rw [hlaw]
  exact s16f_gauss_openPos c hc U hU hne

end HRS.MC.Sec7.S16f

end
