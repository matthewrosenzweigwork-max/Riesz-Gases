import HRS.MC.S7PIDVMain

/-!
# Packet S1 (shared infrastructure), part 1: the matrix action of the propagator on smooth test functions

For `0 ≤ u ≤ t ≤ T` and smooth `φ`, the real coefficients of `U^{u,t} φ` are the (unconditionally convergent) matrix
action `(U^{u,t}φ)^_j = ∑_k φ̂_k T_{jk}`, `T = pieT u t`.  For `t > 0` this follows from the Sobolev boundedness of the
propagator (`pie_level_bound`) and the truncation `φ = c + ∑_{k ∈ K} φ̂_k e_k + r_K` (`‖r_K‖_{H^J} → 0`); for `t = 0` the
propagator is the identity.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIS1

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7.PIE HRS.MC.Sec7.S7PIDV

variable {d : ℕ}

/-- the adjoint data at any level `J ≥ m_*` -/
lemma S7PIS1_hyp (R : Regime d) (T : ℝ) (hT : 0 < T) (J : ℕ) (hJ : PDE.mStar d ≤ J) :
    PIEHyp J R.D R.ρ T := by
  have hd2 : 2 ≤ d := R.hd
  have hd1 : 1 ≤ d := by omega
  have hν : 0 < R.D.invβ := by rw [R.hDβ]; exact inv_pos.2 R.hβ
  have hJ3 := ClassicalPart.three_le_mStar d
  obtain ⟨hprob, hcont⟩ := HRS.MC.L2C0.l2c0_rho_prob_cont R
  have hA := HRS.MC.L2C0.l2c0_adjointData_generic R.D R.hM R.hV hν R.ρ hprob
    (fun j => HRS.MC.RegSet.reg_proof R j) hcont
  obtain ⟨Rg, MB, Λ, VB, ν₀, hAD⟩ := hA J (by omega) T hT
  exact ⟨hd1, hJ, Rg, MB, Λ, VB, ν₀, hAD⟩

/-- the propagator of a constant -/
lemma S7PIS1_prop_const {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {u : ℝ} (hu : u ∈ Set.Icc 0 t) (c : ℝ) :
    propagator D μ u t (fun _ => c) = fun _ => c := by
  obtain ⟨hd, hJ, Rg, MB, Λ, VB, ν₀, hA⟩ := H
  exact prop_const hd D.s D.hs0 D.hsd J hJ Rg MB Λ VB D ν₀ T μ hA ht c hu

/-- the propagator at the degenerate time `(0,0)` is the identity on smooth functions -/
lemma S7PIS1_prop_zero {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) : propagator D μ 0 0 φ = φ := by
  obtain ⟨hd, hJ, Rg, MB, Λ, VB, ν₀, hA⟩ := H
  exact prop_self_zero hd D.s D.hs0 D.hsd J Rg MB Λ VB D ν₀ T μ hA hφ

/-- a coefficient is bounded by the (nonnegative-exponent) Sobolev norm -/
lemma S7PIS1_abs_coeff_le {χ : Torus d → ℝ} {σ : ℝ} (hσ : 0 ≤ σ) (hχ : MemSobolev σ χ)
    (j : NonzeroLattice d) : |Torus.funRealCoeff χ j| ≤ sobolevNorm σ χ := by
  have h1 : Lattice.jp j.1 ^ (2 * σ) * Torus.funRealCoeff χ j ^ 2 ≤
      ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * σ) * Torus.funRealCoeff χ k ^ 2 :=
    hχ.2.le_tsum j fun k _ => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
  have hj1 : 1 ≤ Lattice.jp j.1 ^ (2 * σ) :=
    Real.one_le_rpow (Torus.jp_ge_one j.1) (by linarith)
  have h2 : Torus.funRealCoeff χ j ^ 2 ≤ sobolevNorm σ χ ^ 2 := by
    unfold sobolevNorm
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (tsum_nonneg fun k =>
      mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)))]
    nlinarith [sq_nonneg (Torus.mean χ), sq_nonneg (Torus.funRealCoeff χ j)]
  exact abs_le.2 (abs_le_of_sq_le_sq' h2 (Real.sqrt_nonneg _))

lemma S7PIS1_funRealCoeff_const (c : ℝ) (j : NonzeroLattice d) :
    Torus.funRealCoeff (fun _ : Torus d => c) j = 0 := by
  unfold Torus.funRealCoeff
  rw [integral_mul_const, Torus.integral_realMode]; simp

lemma S7PIS1_mean_const (c : ℝ) : Torus.mean (fun _ : Torus d => c) = c := by
  unfold Torus.mean
  simp

lemma S7PIS1_cont_of_smooth {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) : Continuous φ :=
  (dom_smooth (J := 0) hφ).1

/-- the truncation `ψ_K = c + ∑_{k ∈ K} φ̂_k e_k` and the remainder `r_K = φ - ψ_K` -/
def S7PIS1_psi (φ : Torus d → ℝ) (K : Finset (NonzeroLattice d)) : Torus d → ℝ :=
  fun x => 1 * Torus.mean φ + 1 * pieComb K (fun k => Torus.funRealCoeff φ k) x

def S7PIS1_rem (φ : Torus d → ℝ) (K : Finset (NonzeroLattice d)) : Torus d → ℝ :=
  fun x => 1 * φ x + (-1) * S7PIS1_psi φ K x

lemma S7PIS1_dom_psi (J : ℕ) (φ : Torus d → ℝ) (K : Finset (NonzeroLattice d)) :
    Dom J (S7PIS1_psi φ K) :=
  dom_closed (dom_smooth (a33_isSmooth_const _)) (pieDom_comb J K _) 1 1

lemma S7PIS1_dom_rem {J : ℕ} {φ : Torus d → ℝ} (hφ : Dom J φ) (K : Finset (NonzeroLattice d)) :
    Dom J (S7PIS1_rem φ K) :=
  dom_closed hφ (S7PIS1_dom_psi J φ K) 1 (-1)

lemma S7PIS1_coeff_psi {φ : Torus d → ℝ} (K : Finset (NonzeroLattice d)) (j : NonzeroLattice d) :
    Torus.funRealCoeff (S7PIS1_psi φ K) j = if j ∈ K then Torus.funRealCoeff φ j else 0 := by
  unfold S7PIS1_psi
  rw [pie_funRealCoeff_lin continuous_const (pieComb_continuous _ _), S7PIS1_funRealCoeff_const,
    pieComb_coeff]
  simp

lemma S7PIS1_coeff_rem {φ : Torus d → ℝ} (hφ : Continuous φ) (K : Finset (NonzeroLattice d))
    (j : NonzeroLattice d) :
    Torus.funRealCoeff (S7PIS1_rem φ K) j = if j ∈ K then 0 else Torus.funRealCoeff φ j := by
  have hψ : Continuous (S7PIS1_psi φ K) := (S7PIS1_dom_psi 0 φ K).1
  unfold S7PIS1_rem
  rw [pie_funRealCoeff_lin hφ hψ, S7PIS1_coeff_psi]
  split_ifs <;> ring

lemma S7PIS1_mean_rem {φ : Torus d → ℝ} (hφ : Continuous φ) (K : Finset (NonzeroLattice d)) :
    Torus.mean (S7PIS1_rem φ K) = 0 := by
  have hψ : Continuous (S7PIS1_psi φ K) := (S7PIS1_dom_psi 0 φ K).1
  have hint : ∀ x : Torus d, True := fun _ => trivial
  unfold Torus.mean S7PIS1_rem
  have h1 : Integrable φ := ClassicalAux.integrable_of_continuous hφ
  have h2 : Integrable (S7PIS1_psi φ K) := ClassicalAux.integrable_of_continuous hψ
  have e : (fun x => 1 * φ x + (-1) * S7PIS1_psi φ K x) = fun x => φ x - S7PIS1_psi φ K x := by
    funext x; ring
  rw [e, integral_sub h1 h2]
  have hm : ∫ x, S7PIS1_psi φ K x = Torus.mean φ := by
    unfold S7PIS1_psi
    have hc : Integrable (fun _ : Torus d => Torus.mean φ) := integrable_const _
    have hcm : Integrable (pieComb K (fun k => Torus.funRealCoeff φ k)) :=
      ClassicalAux.integrable_of_continuous (pieComb_continuous _ _)
    have e2 : (fun x => 1 * Torus.mean φ + 1 * pieComb K (fun k => Torus.funRealCoeff φ k) x) =
        fun x => Torus.mean φ + pieComb K (fun k => Torus.funRealCoeff φ k) x := by
      funext x; ring
    rw [e2, integral_add hc hcm]
    have := pieComb_mean K (fun k => Torus.funRealCoeff φ k)
    unfold Torus.mean at this
    rw [this]; simp
  rw [hm]
  unfold Torus.mean
  ring

/-- the propagator of the truncation -/
lemma S7PIS1_coeff_prop_psi {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {u : ℝ} (hu : u ∈ Set.Icc 0 t) (φ : Torus d → ℝ)
    (K : Finset (NonzeroLattice d)) (j : NonzeroLattice d) :
    Torus.funRealCoeff (propagator D μ u t (S7PIS1_psi φ K)) j =
      ∑ k ∈ K, Torus.funRealCoeff φ k * pieT D μ u t j k := by
  have hc : Dom J (fun _ : Torus d => Torus.mean φ) := dom_smooth (a33_isSmooth_const _)
  unfold S7PIS1_psi
  rw [pie_prop_lin H ht hu hc (pieDom_comb J K (fun k => Torus.funRealCoeff φ k)) 1 1,
    S7PIS1_prop_const H ht hu]
  have hcont := pie_prop_continuous H ht hu (pieDom_comb J K (fun k => Torus.funRealCoeff φ k))
  have e : (fun x => 1 * Torus.mean φ + 1 * propagator D μ u t
      (pieComb K (fun k => Torus.funRealCoeff φ k)) x) = fun x => 1 * (fun _ : Torus d => Torus.mean φ) x +
        1 * propagator D μ u t (pieComb K (fun k => Torus.funRealCoeff φ k)) x := rfl
  have e2 := pie_funRealCoeff_lin (continuous_const (y := Torus.mean φ)) hcont 1 1 j
  rw [e, e2, S7PIS1_funRealCoeff_const, pie_coeff_comb H ht hu K]
  ring

end HRS.MC.Sec7.S7PIS1

end
