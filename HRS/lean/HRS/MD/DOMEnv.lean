/-
# HRS.MD.DOMEnv — packet DOM-ENV (generator-domain clause of Prop. 4.16)

The master weight `Pw X = ∏_{i<j} w(x_i,x_j)`; Gibbs density times every power of `Pw` is bounded;
every power of `Pw` is `ℙ_{N,β}`-integrable; envelope of `F_N(ψ)`, `∇_iF`, `Δ_iF` and of the drift by powers of `Pw`
off collisions.
-/
import HRS.Equilibrium.Q84dStationary

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.MD.DOMProof

open HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

/-- The master weight `∏_{i<j} w(x_i, x_j)`. -/
def Pw (s : ℝ) {d N : ℕ} (X : Config d N) : ℝ :=
  ∏ p ∈ pairsN N, wEnv s (X p.1) (X p.2)

theorem domp_wEnv_symm (x y : Torus d) : wEnv s x y = wEnv s y x := by
  unfold wEnv rTrunc
  rw [PairCorrAux.eucDist_symm']

theorem domp_one_le_Pw (X : Config d N) : 1 ≤ Pw s X := by
  unfold Pw
  refine Finset.prod_induction _ (fun t : ℝ => 1 ≤ t) (fun a b ha hb => ?_) le_rfl
    (fun p _ => PairCorrAux.one_le_wEnv s _ _)
  nlinarith

theorem domp_w_le_Pw (X : Config d N) {i j : Fin N} (hij : i ≠ j) :
    wEnv s (X i) (X j) ≤ Pw s X := by
  have hp := ordPair_mem hij
  have h1 : wEnv s (X (ordPair i j).1) (X (ordPair i j).2) = wEnv s (X i) (X j) := by
    unfold ordPair
    split_ifs
    · rfl
    · exact domp_wEnv_symm _ _
  unfold Pw
  rw [← Finset.mul_prod_erase _ _ hp, h1]
  have : 1 ≤ ∏ p ∈ (pairsN N).erase (ordPair i j), wEnv s (X p.1) (X p.2) := by
    refine Finset.prod_induction _ (fun t : ℝ => 1 ≤ t) (fun a b ha hb => ?_) le_rfl
      (fun p _ => PairCorrAux.one_le_wEnv s _ _)
    nlinarith
  have h0 := PairCorrAux.one_le_wEnv s (X i) (X j)
  nlinarith

theorem domp_measurable_wpair (p : Fin N × Fin N) :
    Measurable (fun X : Config d N => wEnv s (X p.1) (X p.2)) := by
  have hpr : Measurable (fun X : Config d N => (X p.1, X p.2)) :=
    (measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2)
  have h := Measurable.comp (q84d_measurable_eucDist_prod d) hpr
  have h2 : Measurable (fun X : Config d N => min 1 (Torus.eucDist (X p.1) (X p.2))) :=
    measurable_const.min h
  have h3 : Measurable (fun X : Config d N => (min 1 (Torus.eucDist (X p.1) (X p.2))) ^ (-s)) :=
    h2.pow_const _
  exact measurable_const.add h3

theorem domp_measurable_Pw : Measurable (Pw s : Config d N → ℝ) := by
  unfold Pw
  exact Finset.measurable_prod _ fun p _ => domp_measurable_wpair p

/-- `w^m e^{-κ g} ≤ C` for every power `m`. -/
theorem domp_w_pow_exp_bound (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {κ : ℝ} (hκ : 0 < κ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : Torus d,
      wEnv s x y ^ m * Real.exp (-κ * periodicRiesz d s (x - y)) ≤ C := by
  set j : ℕ := m + 1 with hj
  have hjpos : (0 : ℝ) < j := by positivity
  obtain ⟨C, hC0, hC⟩ := q84d_w_exp_bound hd hcrit (s := s) (κ := κ / j) (div_pos hκ hjpos)
  refine ⟨C ^ j, by positivity, fun x y => ?_⟩
  have hw1 := PairCorrAux.one_le_wEnv s x y
  have h1 : wEnv s x y ^ m ≤ wEnv s x y ^ (2 * j) :=
    pow_le_pow_right₀ hw1 (by omega)
  have h2 : Real.exp (-κ * periodicRiesz d s (x - y)) =
      Real.exp (-(κ / j) * periodicRiesz d s (x - y)) ^ j := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  calc wEnv s x y ^ m * Real.exp (-κ * periodicRiesz d s (x - y))
      ≤ wEnv s x y ^ (2 * j) * Real.exp (-κ * periodicRiesz d s (x - y)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (wEnv s x y ^ 2 * Real.exp (-(κ / j) * periodicRiesz d s (x - y))) ^ j := by
        rw [h2, mul_pow, ← pow_mul]
    _ ≤ C ^ j := pow_le_pow_left₀ (by positivity) (hC x y).2 j

section Gibbs

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
include hd hcrit

/-- `q · Pw^m ≤ C` (all configurations). -/
theorem domp_q_mul_Pw_pow_le {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (hN : 1 ≤ N) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : Config d N,
      Real.exp (-β * canonicalHamiltonian (periodicRiesz d s) V X) * Pw s X ^ m ≤ C := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨B, hB0, hB⟩ := q84d_exists_lower hd hs0 hsd
  obtain ⟨Vm, hVm⟩ := q84d_exists_bound_smooth hV
  obtain ⟨C, hC0, hC⟩ := domp_w_pow_exp_bound hd hcrit (κ := β / N) (div_pos hβ hNp) m
  refine ⟨Real.exp (β * ((N : ℝ) * Vm + N * B)) * C ^ (pairsN N).card, by positivity, fun X => ?_⟩
  have h := q84d_q_le hB0 hB hVm hN hβ.le (pairsN N) (Finset.Subset.refl _) X
  have hP : Pw s X ^ m = ∏ p ∈ pairsN N, wEnv s (X p.1) (X p.2) ^ m := by
    unfold Pw; rw [Finset.prod_pow]
  have hPnn : 0 ≤ Pw s X ^ m := by
    have := domp_one_le_Pw (s := s) X
    positivity
  calc Real.exp (-β * canonicalHamiltonian (periodicRiesz d s) V X) * Pw s X ^ m
      ≤ (Real.exp (β * ((N : ℝ) * Vm + N * B)) *
        ∏ p ∈ pairsN N, Real.exp (-(β / N) * periodicRiesz d s (X p.1 - X p.2))) * Pw s X ^ m :=
        mul_le_mul_of_nonneg_right h hPnn
    _ = Real.exp (β * ((N : ℝ) * Vm + N * B)) *
        ∏ p ∈ pairsN N, (wEnv s (X p.1) (X p.2) ^ m *
          Real.exp (-(β / N) * periodicRiesz d s (X p.1 - X p.2))) := by
        rw [hP, Finset.prod_mul_distrib]; ring
    _ ≤ Real.exp (β * ((N : ℝ) * Vm + N * B)) * ∏ _p ∈ pairsN N, C := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have hnn : ∀ p ∈ pairsN N, 0 ≤ wEnv s (X p.1) (X p.2) ^ m *
            Real.exp (-(β / N) * periodicRiesz d s (X p.1 - X p.2)) := fun p _ => by
          have := PairCorrAux.one_le_wEnv s (X p.1) (X p.2)
          positivity
        exact Finset.prod_le_prod₀ hnn fun p _ => hC _ _
    _ = _ := by rw [Finset.prod_const]

theorem domp_integrable_Pw_pow {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (hN : 1 ≤ N) (m : ℕ) :
    Integrable (fun X : Config d N => Pw s X ^ m) (canonicalGibbs (periodicRiesz d s) V N β) := by
  obtain ⟨C, hC0, hC⟩ := domp_q_mul_Pw_pow_le hd hcrit hV hβ hN m
  refine q84d_integrable_of_q_bound hd hcrit hV hβ hN
    ((domp_measurable_Pw.pow_const m).aestronglyMeasurable) C (fun X _ => ?_)
  have := domp_one_le_Pw (s := s) X
  rw [abs_of_nonneg (by positivity)]
  exact hC X

end Gibbs


/-! ### Envelope of `F_N(ψ)` and its first two derivatives -/

theorem domp_norm_le_sum_abs (v : Euc d) : ‖v‖ ≤ ∑ k, |v k| := by
  have h : ‖v‖ ^ 2 ≤ (∑ k, |v k|) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    calc ∑ k, v k ^ 2 = ∑ k, |v k| ^ 2 := by simp [sq_abs]
      _ ≤ (∑ k, |v k|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg (fun k _ => abs_nonneg _)
  exact le_of_sq_le_sq h (Finset.sum_nonneg fun k _ => abs_nonneg _)

section Envelope

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
include hd hcrit

theorem domp_F_envelope {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (hN : 1 ≤ N) {ρ : Torus d → ℝ} {f : Torus d → ℝ} {K₁ : ℝ} {ψ : Torus d → Torus d → ℝ}
    (hψ : IsPairCorrector d s V β ρ f K₁ ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : Config d N, X ∉ collisionSet d N →
      |Fstat ψ X| ≤ C * Pw s X ∧
      (∀ i, ‖configGrad (Fstat ψ) X i‖ ≤ C * Pw s X) ∧
      (∀ i, |configLap (Fstat ψ) X i| ≤ C * Pw s X) ∧
      (∀ i, ‖Torus.grad V (X i) + (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
          periodicRieszGrad d s (X i - X j)‖ ≤ C * Pw s X ^ 2) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  have hK₁ := q84d_K_nonneg hd hcrit hψ
  obtain ⟨Vg, hVg⟩ := q84d_exists_grad_bound hV
  have hVg0 : 0 ≤ Vg := (abs_nonneg _).trans (hVg (0 : Torus d) ⟨0, by omega⟩)
  obtain ⟨Cg, hCg0, hCg⟩ := q84d_gradg_le_w_sq hd hcrit (s := s)
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set c : ℝ := (N : ℝ) ^ (-(3 / 2 : ℝ)) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hc1 : c ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  set A : ℝ := 2 * K₁ * N * N + 2 * K₁ * N * d + 2 * K₁ * N * d + d * Vg + Cg with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨A, hA0, fun X hX => ?_⟩
  have hXne : ∀ a b : Fin N, a ≠ b → X a ≠ X b := fun a b hab hXab => hX ⟨a, b, hab, hXab⟩
  have hP1 := domp_one_le_Pw (s := s) X
  have hP0 : 0 ≤ Pw s X := by linarith
  have hwP : ∀ i j : Fin N, i ≠ j → wEnv s (X i) (X j) ≤ Pw s X := fun i j hij => domp_w_le_Pw X hij
  have hwsum : ∀ i : Fin N, ∑ l ∈ Finset.univ.erase i, wEnv s (X i) (X l) ≤ N * Pw s X := fun i =>
    q84d_sum_le_card _ _ hP0 fun l hl => hwP i l (Finset.ne_of_mem_erase hl).symm
  -- the three derivative bounds
  have hAik : ∀ i k, |Aik d ψ i k X| ≤ 2 * K₁ * N * Pw s X := by
    intro i k
    unfold Aik
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ) ^ (-(3 / 2 : ℝ)))]
    rw [← hc]
    calc 2 * c * |∑ j ∈ Finset.univ.erase i, gK ψ k (X i) (X j)|
        ≤ 2 * c * ∑ j ∈ Finset.univ.erase i, K₁ * wEnv s (X i) (X j) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
          exact q84d_gK_bound hψ.size (hXne i j (Finset.ne_of_mem_erase hj).symm) k
      _ = 2 * c * K₁ * ∑ j ∈ Finset.univ.erase i, wEnv s (X i) (X j) := by
          rw [← Finset.mul_sum]; ring
      _ ≤ 2 * 1 * K₁ * (N * Pw s X) := by
          have hS0 : 0 ≤ ∑ j ∈ Finset.univ.erase i, wEnv s (X i) (X j) :=
            Finset.sum_nonneg fun j _ => (zero_le_one.trans (PairCorrAux.one_le_wEnv s _ _))
          have h2c : 2 * c * K₁ ≤ 2 * 1 * K₁ := by nlinarith
          exact mul_le_mul h2c (hwsum i) hS0 (by positivity)
      _ = 2 * K₁ * N * Pw s X := by ring
  have hCik : ∀ i k, |Cik d ψ i k X| ≤ 2 * K₁ * N * Pw s X := by
    intro i k
    unfold Cik
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ) ^ (-(3 / 2 : ℝ)))]
    rw [← hc]
    calc 2 * c * |∑ j ∈ Finset.univ.erase i, hK ψ k (X i) (X j)|
        ≤ 2 * c * ∑ j ∈ Finset.univ.erase i, K₁ * wEnv s (X i) (X j) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
          exact q84d_hK_bound hψ.size (hXne i j (Finset.ne_of_mem_erase hj).symm) k
      _ = 2 * c * K₁ * ∑ j ∈ Finset.univ.erase i, wEnv s (X i) (X j) := by
          rw [← Finset.mul_sum]; ring
      _ ≤ 2 * 1 * K₁ * (N * Pw s X) := by
          have hS0 : 0 ≤ ∑ j ∈ Finset.univ.erase i, wEnv s (X i) (X j) :=
            Finset.sum_nonneg fun j _ => (zero_le_one.trans (PairCorrAux.one_le_wEnv s _ _))
          have h2c : 2 * c * K₁ ≤ 2 * 1 * K₁ := by nlinarith
          exact mul_le_mul h2c (hwsum i) hS0 (by positivity)
      _ = 2 * K₁ * N * Pw s X := by ring
  have hdN : (0 : ℝ) ≤ d := by positivity
  refine ⟨?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · -- F
    unfold Fstat
    rw [abs_mul, abs_of_nonneg hc0]
    have hpair := q84d_pairSum_bound 1 zero_le_one ψ X (M := 2 * K₁ * Pw s X) (by positivity)
      (fun i j hij => by
        rw [one_mul]
        calc |ψ (X i) (X j)| ≤ 2 * K₁ * wEnv s (X i) (X j) :=
              q84d_psi_le_w hs1 hψ.size hK₁ (hXne i j hij)
          _ ≤ 2 * K₁ * Pw s X := mul_le_mul_of_nonneg_left (hwP i j hij) (by positivity))
    rw [one_mul] at hpair
    calc c * |pairSumOrdered ψ X| ≤ 1 * (N * (N * (2 * K₁ * Pw s X))) :=
          mul_le_mul hc1 hpair (abs_nonneg _) zero_le_one
      _ ≤ A * Pw s X := by
          rw [hA]
          have h1 : 0 ≤ 2 * K₁ * N * d * Pw s X := by positivity
          have h2 : 0 ≤ d * Vg * Pw s X := by positivity
          have h3 : 0 ≤ Cg * Pw s X := by positivity
          nlinarith
  · refine (domp_norm_le_sum_abs _).trans ?_
    calc ∑ k, |(configGrad (Fstat ψ) X i) k| = ∑ k, |Aik d ψ i k X| := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [q84d_configGrad_comp hψ.symm hψ.size.smooth X hXne i k]
      _ ≤ ∑ _k : Fin d, 2 * K₁ * N * Pw s X := Finset.sum_le_sum fun k _ => hAik i k
      _ = d * (2 * K₁ * N * Pw s X) := by simp
      _ ≤ A * Pw s X := by
          rw [hA]
          have h1 : 0 ≤ 2 * K₁ * N * N * Pw s X := by positivity
          have h2 : 0 ≤ d * Vg * Pw s X := by positivity
          have h3 : 0 ≤ Cg * Pw s X := by positivity
          have h4 : 0 ≤ 2 * K₁ * N * d * Pw s X := by positivity
          nlinarith
  · rw [q84d_configLap_eq hψ.symm hψ.size.smooth X hXne i]
    calc |∑ k, Cik d ψ i k X| ≤ ∑ k, |Cik d ψ i k X| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin d, 2 * K₁ * N * Pw s X := Finset.sum_le_sum fun k _ => hCik i k
      _ = d * (2 * K₁ * N * Pw s X) := by simp
      _ ≤ A * Pw s X := by
          rw [hA]
          have h1 : 0 ≤ 2 * K₁ * N * N * Pw s X := by positivity
          have h2 : 0 ≤ d * Vg * Pw s X := by positivity
          have h3 : 0 ≤ Cg * Pw s X := by positivity
          have h4 : 0 ≤ 2 * K₁ * N * d * Pw s X := by positivity
          nlinarith
  · have hg1 : ‖Torus.grad V (X i)‖ ≤ d * Vg := by
      refine (domp_norm_le_sum_abs _).trans ?_
      calc ∑ k, |(Torus.grad V (X i)) k| ≤ ∑ _k : Fin d, Vg := Finset.sum_le_sum fun k _ => hVg _ _
        _ = d * Vg := by simp
    have hg2 : ‖∑ j ∈ Finset.univ.erase i, periodicRieszGrad d s (X i - X j)‖ ≤ N * (Cg * Pw s X ^ 2) := by
      refine (norm_sum_le _ _).trans (q84d_sum_le_card _ _ (by positivity) fun j hj => ?_)
      have hij := (Finset.ne_of_mem_erase hj).symm
      calc ‖periodicRieszGrad d s (X i - X j)‖ ≤ Cg * wEnv s (X i) (X j) ^ 2 := hCg _ _ (hXne i j hij)
        _ ≤ Cg * Pw s X ^ 2 := by
            refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans
              (PairCorrAux.one_le_wEnv s _ _)) (hwP i j hij) 2) hCg0
    calc ‖Torus.grad V (X i) + (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
          periodicRieszGrad d s (X i - X j)‖
        ≤ ‖Torus.grad V (X i)‖ + ‖(1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
          periodicRieszGrad d s (X i - X j)‖ := norm_add_le _ _
      _ ≤ d * Vg + (1 / (N : ℝ)) * (N * (Cg * Pw s X ^ 2)) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
          exact add_le_add hg1 (mul_le_mul_of_nonneg_left hg2 (by positivity))
      _ = d * Vg + Cg * Pw s X ^ 2 := by field_simp
      _ ≤ A * Pw s X ^ 2 := by
          have hP2 : 1 ≤ Pw s X ^ 2 := one_le_pow₀ hP1
          rw [hA]
          have h1 : 0 ≤ 2 * K₁ * N * N * Pw s X ^ 2 := by positivity
          have h4 : 0 ≤ 2 * K₁ * N * d * Pw s X ^ 2 := by positivity
          have h5 : 0 ≤ (2 * K₁ * N * d) * (Pw s X ^ 2 - 1) := by
            apply mul_nonneg (by positivity); linarith
          have h6 : 0 ≤ (2 * K₁ * N * N) * (Pw s X ^ 2 - 1) := by
            apply mul_nonneg (by positivity); linarith
          have h7 : 0 ≤ (d * Vg) * (Pw s X ^ 2 - 1) := by
            apply mul_nonneg (by positivity); linarith
          have h8 : 0 ≤ Cg * (Pw s X ^ 2 - 1) := mul_nonneg hCg0 (by linarith)
          nlinarith

end Envelope

end HRS.MD.DOMProof

end
