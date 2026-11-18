import HRS.PDE.MeanFieldAprioriPositive
import HRS.PDE.Toolbox.CoeffL2

/-!
# A priori bounds for the finite-regularity mean-field equation, packet AP4
(uniform upper bound by the Alikakos iteration; package MF-01, plan `MeanFieldAprioriPlan.md`,
amended by `MeanFieldAprioriAmendment.md` §2.5)

The main theorem `exists_sup_bound` is stated for real solutions on `[0,T]` (`MFSolRealOn … T`)
with a constant `Λ` independent of `T`, of `ν ∈ [νm, νp]` and of the solution.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

namespace HRS.PDE.MFApriori

variable {d : ℕ}
open Aux

/-! ### Section 1: Parseval for real continuous functions and for the gradient -/

theorem parseval_real {g : Torus d → ℝ} (hg : Continuous g) :
    hsNormSq 0 (coeffOf g) = ∫ x, g x ^ 2 := by
  have hm : MemLp (fun x => (g x : ℂ)) 2 volume :=
    memLp_two_of_continuous (Complex.continuous_ofReal.comp hg)
  obtain ⟨-, h2⟩ := hsNormSq_zero_coeffOfC _ hm
  rw [coeffOf_eq_coeffOfC, h2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [Complex.norm_real]

theorem grad_parseval {u : Torus d → ℝ} (hu : Torus.IsCk 1 u) :
    hsNormSq 0 (fun k => ((2 * Real.pi * Lattice.enorm k : ℝ) : ℂ) * coeffOf u k) =
      ∫ x, ‖Torus.grad u x‖ ^ 2 := by
  obtain ⟨hmem, -⟩ := memHs_one_coeffOf u hu
  obtain ⟨h0, h1⟩ := (memHs_one_iff _).1 hmem
  have hsj : ∀ j : Fin d, Summable fun k => ‖derivCoeff j (coeffOf u) k‖ ^ 2 :=
    fun j => (memHs_zero_iffC _).1 (h1 j)
  have e1 : ∀ k : Lattice d, ‖((2 * Real.pi * Lattice.enorm k : ℝ) : ℂ) * coeffOf u k‖ ^ 2 =
      ∑ j, ‖derivCoeff j (coeffOf u) k‖ ^ 2 := by
    intro k
    simp_rw [norm_derivCoeff_sq]
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, mul_pow,
      enorm_sq_eq_sumC, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hsNormSq_zero]
  simp_rw [e1]
  rw [Summable.tsum_finsetSum fun j _ => hsj j]
  have hpd : ∀ j, Continuous (Torus.partialDeriv j u) := fun j => continuous_partialDeriv j u hu
  have e2 : ∀ j : Fin d, ∑' k, ‖derivCoeff j (coeffOf u) k‖ ^ 2 =
      ∫ x, (Torus.partialDeriv j u x) ^ 2 := by
    intro j
    rw [← coeffOf_partialDeriv_eq j u hu, ← hsNormSq_zero]
    exact parseval_real (hpd j)
  simp_rw [e2, norm_grad_sq]
  rw [integral_finsetSum]
  intro j _
  exact ((hpd j).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)


/-! ### Section 2: real-power algebra for the logistic inequality -/

/-- Nash's inequality `Y^{d+2} ≤ C B⁴ (a + B²)^d` rewritten as `κ Y^{1+2/d} ≤ a + B²`,
`κ = (C B⁴)^{-1/d}`. -/
theorem nash_logistic_form (hd : 1 ≤ d) {Cn B Y a : ℝ} (hCn : 0 < Cn) (hB : 0 < B) (hY : 0 ≤ Y)
    (ha : 0 ≤ a) (h : Y ^ (d + 2) ≤ Cn * B ^ 4 * (a + B ^ 2) ^ d) :
    (Cn * B ^ 4) ^ (-(1 / (d : ℝ))) * Y ^ (1 + 2 / (d : ℝ)) ≤ a + B ^ 2 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hd0 : d ≠ 0 := by omega
  have hP : 0 < Cn * B ^ 4 := by positivity
  set κ : ℝ := (Cn * B ^ 4) ^ (-(1 / (d : ℝ))) with hκ
  have hκ0 : 0 < κ := Real.rpow_pos_of_pos hP _
  have hκd : κ ^ d = (Cn * B ^ 4)⁻¹ := by
    rw [hκ, ← Real.rpow_natCast, ← Real.rpow_mul hP.le]
    have : -(1 / (d : ℝ)) * (d : ℝ) = -1 := by field_simp
    rw [this, Real.rpow_neg_one]
  have hYd : (Y ^ (1 + 2 / (d : ℝ))) ^ d = Y ^ (d + 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY]
    have : (1 + 2 / (d : ℝ)) * (d : ℝ) = ((d + 2 : ℕ) : ℝ) := by
      push_cast; field_simp
    rw [this, Real.rpow_natCast]
  have hz0 : 0 ≤ κ * Y ^ (1 + 2 / (d : ℝ)) := by positivity
  have hzd : (κ * Y ^ (1 + 2 / (d : ℝ))) ^ d = (Cn * B ^ 4)⁻¹ * Y ^ (d + 2) := by
    rw [mul_pow, hκd, hYd]
  have hle : (κ * Y ^ (1 + 2 / (d : ℝ))) ^ d ≤ (a + B ^ 2) ^ d := by
    rw [hzd]
    rw [inv_mul_le_iff₀ hP]
    linarith
  exact (pow_le_pow_iff_left₀ hz0 (by positivity) hd0).1 hle


theorem rpow_threshold_le_sq {x M : ℝ} (hx : 0 ≤ x) (hM : 0 ≤ M)
    (h : x ^ d ≤ M ^ 2) : x ^ ((d : ℝ) / 2) ≤ M := by
  have hx' : 0 ≤ x ^ ((d : ℝ) / 2) := Real.rpow_nonneg hx _
  have e : (x ^ ((d : ℝ) / 2)) ^ 2 = x ^ d := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_natCast]
    congr 1; push_cast; ring
  exact (pow_le_pow_iff_left₀ hx' hM (by norm_num : (2 : ℕ) ≠ 0)).1 (e ▸ h)

theorem rpow_threshold_le_pow {x M : ℝ} (hx : 0 ≤ x) (hM : 0 ≤ M)
    (h : x ^ d ≤ M ^ (d + 2)) : x ^ ((d : ℝ) / ((d : ℝ) + 2)) ≤ M := by
  have hx' : 0 ≤ x ^ ((d : ℝ) / ((d : ℝ) + 2)) := Real.rpow_nonneg hx _
  have hd2 : (d : ℝ) + 2 ≠ 0 := by positivity
  have e : (x ^ ((d : ℝ) / ((d : ℝ) + 2))) ^ (d + 2) = x ^ d := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_natCast]
    congr 1; push_cast; field_simp
  exact (pow_le_pow_iff_left₀ hx' hM (by omega : d + 2 ≠ 0)).1 (e ▸ h)

/-- `|∇ ρ^q|² = q² ρ^{2q-2} |∇ρ|²`. -/
theorem norm_grad_pow_sq {ρ : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ) (q : ℕ) (hq : 1 ≤ q) (x : Torus d) :
    ‖Torus.grad (fun y => ρ y ^ q) x‖ ^ 2 = (q : ℝ) ^ 2 * ρ x ^ (2 * q - 2) * ‖Torus.grad ρ x‖ ^ 2 := by
  have hΦ : ContDiffOn ℝ 1 (fun r : ℝ => r ^ q) univ := (contDiff_id.pow q).contDiffOn
  have hd : ∀ j, Torus.partialDeriv j (fun y => ρ y ^ q) x =
      (q : ℝ) * ρ x ^ (q - 1) * Torus.partialDeriv j ρ x := by
    intro j
    have := partialDeriv_comp j (fun r : ℝ => r ^ q) univ isOpen_univ hΦ ρ hρ (fun _ => mem_univ _) x
    rw [this]
    simp
  rw [norm_grad_sq, norm_grad_sq]
  simp_rw [hd]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : ρ x ^ (2 * q - 2) = (ρ x ^ (q - 1)) ^ 2 := by
    rw [← pow_mul]; congr 1; omega
  rw [this]; ring

theorem continuous_laplacian_of_isCk {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) :
    Continuous (Torus.laplacian f) := by
  have : Torus.laplacian f = fun x => ∑ j, Torus.partialDeriv j (Torus.partialDeriv j f) x := by
    funext x; exact laplacian_eq_sum _ hf x
  rw [this]
  exact continuous_finsetSum _ fun j _ =>
    continuous_partialDeriv j _ (isCk_one_partialDeriv j _ hf)


/-! ### Section 3: the differential inequality for `∫ ρ^{2q}` at a fixed time -/

/-- The constants of the pairing bound `exists_laplaceRiesz_pairing_bound` (as a hypothesis). -/
def PairingBound (d : ℕ) (s : ℝ) (A : ℝ) : Prop :=
  ∀ f φ : Torus d → ℝ, Continuous f → MemHs 2 (coeffOf f) → (∀ x, 0 ≤ f x) →
    (∫ x, f x) = 1 → Continuous φ → (∀ x, 0 ≤ φ x) →
    (∀ x y, 0 ≤ (φ x - φ y) * (f x - f y)) →
    ∫ x, φ x * toFun (laplaceRieszCoeff d s (coeffOf f)) x ≤ A * ∫ x, φ x

/-- Nash's inequality (as a hypothesis, with the constant `Cn`). -/
def NashBound (d : ℕ) (Cn : ℝ) : Prop :=
  ∀ c : Coeff d, MemHs 1 c → ∀ M : ℝ, 0 ≤ M → (∀ k, ‖c k‖ ≤ M) →
    hsNormSq 0 c ^ (d + 2) ≤ Cn * M ^ 4 *
      (hsNormSq 0 (fun k => ((2 * Real.pi * Lattice.enorm k : ℝ) : ℂ) * c k) + M ^ 2) ^ d

/-- The time-`t` energy inequality: with `p = 2q`, `Y = ∫ρ^p`,
`p ∫ρ^{p-1}(νΔρ + Div(ρ∇W)) ≤ -L κ Y^{1+2/d} + γ Y + L B²`, where `∫ρ^q ≤ B`. -/
theorem pow_energy_ineq (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (hν : 0 < ν) (c : Coeff d) (hc : MemHs (K : ℝ) c) (hreal : IsRealCoeff c)
    (hnn : ∀ x, 0 ≤ toFun c x) (hmass : ∫ x, toFun c x = 1)
    (Cn : ℝ) (hCn : 0 < Cn) (hNash : NashBound d Cn) (A D : ℝ)
    (hpair : PairingBound d s A) (hDV : ∀ x, Torus.laplacian V x ≤ D)
    (q : ℕ) (hq : 1 ≤ q) (B : ℝ) (hB : 1 ≤ B) (hXq : ∫ x, toFun c x ^ q ≤ B) :
    ∫ x, deriv (fun r : ℝ => r ^ (2 * q)) (toFun c x) * toFun (mfRhsCoeff d s V ν c) x ≤
      -((ν * (4 * (((2 * q : ℕ) : ℝ) - 1) / ((2 * q : ℕ) : ℝ))) *
          (Cn * B ^ 4) ^ (-(1 / (d : ℝ)))) *
          (∫ x, toFun c x ^ (2 * q)) ^ (1 + 2 / (d : ℝ)) +
        (((2 * q : ℕ) : ℝ) - 1) * (D + A) * (∫ x, toFun c x ^ (2 * q)) +
        (ν * (4 * (((2 * q : ℕ) : ℝ) - 1) / ((2 * q : ℕ) : ℝ))) * B ^ 2 := by
  have hint : ∀ f : Torus d → ℝ, Continuous f → Integrable f := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hdK : (d : ℝ) / 2 < K := by linarith
  have hsum : Summable fun k => ‖c k‖ := summable_norm_of_memHs (K : ℝ) hdK c hc
  have hV2 : Torus.IsCk 2 V := hV.of_le (by exact_mod_cast (by omega : 2 ≤ K + 2))
  have hVK := memHs_of_isCk_nat K V hV
  obtain ⟨C₂, -, hC₂⟩ := exists_mfPath_isCk (d := d) 2 (K : ℝ) (by simpa using hK)
  have hρ2 : Torus.IsCk 2 (toFun c) := by simpa using (hC₂ c hc hreal).1
  have hρ1 : Torus.IsCk 1 (toFun c) := hρ2.of_le (by norm_num)
  have hρc : Continuous (toFun c) := continuous_of_isCk' hρ1 le_rfl
  set ρ := toFun c with hρdef
  obtain ⟨p, hpq⟩ : ∃ p : ℕ, p = 2 * q := ⟨_, rfl⟩
  rw [← hpq]
  have hp2 : 2 ≤ p := by omega
  have hpR : (p : ℝ) = 2 * q := by rw [hpq]; push_cast; ring
  have hpR2 : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpos : (0 : ℝ) < p := by linarith
  -- the derivative of the power
  have hder : ∀ r : ℝ, deriv (fun r : ℝ => r ^ p) r = p * r ^ (p - 1) := fun r => by simp
  have step1 : ∫ x, deriv (fun r : ℝ => r ^ p) (ρ x) * toFun (mfRhsCoeff d s V ν c) x =
      p * ∫ x, ρ x ^ (p - 1) * toFun (mfRhsCoeff d s V ν c) x := by
    simp_rw [hder, mul_assoc]
    rw [integral_const_mul]
  rw [step1, integral_pow_rhs' hd s hs0 hsd (K : ℝ) hK V hV2 hVK ν c hc hreal p hp2]
  set J : ℝ := ∫ x, ρ x ^ (p - 2) * ‖Torus.grad ρ x‖ ^ 2 with hJ
  set Z : ℝ := ∫ x, ρ x ^ p * Torus.laplacian (Wpot d s V c) x with hZ
  set Y : ℝ := ∫ x, ρ x ^ p with hY
  set κ : ℝ := (Cn * B ^ 4) ^ (-(1 / (d : ℝ))) with hκ
  set L : ℝ := ν * (4 * ((p : ℝ) - 1) / (p : ℝ)) with hL
  have hL0 : 0 ≤ L := by
    have : 0 ≤ 4 * ((p : ℝ) - 1) / (p : ℝ) := by
      apply div_nonneg <;> linarith
    positivity
  have hY0 : 0 ≤ Y := integral_nonneg fun x => pow_nonneg (hnn x) _
  have hρp : Continuous fun x => ρ x ^ p := hρc.pow p
  -- bound for `Z`
  have hW2 := isCk_two_Wpot hd s hs0 hsd (K : ℝ) hK V hV2 c hc hreal
  have hriesz2 : Torus.IsCk 2 (riesz d s c) := (riesz_isCk hd s hs0 hsd 2 (K : ℝ) (by simpa using hK) c hc hreal).1
  have hlapR : ∀ x, Torus.laplacian (riesz d s c) x = toFun (laplaceRieszCoeff d s c) x :=
    (riesz_isCk hd s hs0 hsd 2 (K : ℝ) (by simpa using hK) c hc hreal).2 le_rfl
  have hlapW : ∀ x, Torus.laplacian (Wpot d s V c) x =
      Torus.laplacian V x + toFun (laplaceRieszCoeff d s c) x := by
    intro x
    have := laplacian_add V (riesz d s c) hV2 hriesz2 x
    rw [← hlapR x]
    exact this
  have hcV : Continuous (Torus.laplacian V) := continuous_laplacian_of_isCk hV2
  have hcR : Continuous (toFun (laplaceRieszCoeff d s c)) := by
    have : toFun (laplaceRieszCoeff d s c) = Torus.laplacian (riesz d s c) := funext fun x => (hlapR x).symm
    rw [this]; exact continuous_laplacian_of_isCk hriesz2
  have hZ1 : Z = (∫ x, ρ x ^ p * Torus.laplacian V x) +
      ∫ x, ρ x ^ p * toFun (laplaceRieszCoeff d s c) x := by
    have hi1 : Integrable fun x => ρ x ^ p * Torus.laplacian V x := hint _ (hρp.mul hcV)
    have hi2 : Integrable fun x => ρ x ^ p * toFun (laplaceRieszCoeff d s c) x :=
      hint _ (hρp.mul hcR)
    rw [hZ, ← integral_add hi1 hi2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hlapW x]; ring
  have hZ2 : (∫ x, ρ x ^ p * Torus.laplacian V x) ≤ D * Y := by
    rw [hY, ← integral_const_mul]
    refine integral_mono (hint _ (hρp.mul hcV)) (hint _ (continuous_const.mul hρp)) fun x => ?_
    have := hDV x
    have h0 := pow_nonneg (hnn x) p
    simp only
    nlinarith
  have hZ3 : (∫ x, ρ x ^ p * toFun (laplaceRieszCoeff d s c) x) ≤ A * Y := by
    have hcoef : coeffOf ρ = c := coeffOf_toFun c hreal hsum
    have h := hpair ρ (fun x => ρ x ^ p) hρc (by rw [hcoef]; exact memHs_mono (by linarith) hc) hnn
      hmass hρp (fun x => pow_nonneg (hnn x) _) (fun x y => by
        have hx := hnn x
        have hy := hnn y
        rcases le_total (ρ x) (ρ y) with h | h
        · exact mul_nonneg_of_nonpos_of_nonpos (by linarith [pow_le_pow_left₀ hx h p])
            (by linarith)
        · exact mul_nonneg (by linarith [pow_le_pow_left₀ hy h p]) (by linarith))
    rw [hcoef] at h
    exact h
  have hZle : Z ≤ (D + A) * Y := by rw [hZ1]; nlinarith
  -- the gradient term via Nash
  set u : Torus d → ℝ := fun x => ρ x ^ q with hu
  have hu2 : Torus.IsCk 2 u := isCk_comp (fun r : ℝ => r ^ q) univ (contDiff_id.pow q).contDiffOn ρ
    hρ2 (fun _ => mem_univ _)
  have hu1 : Torus.IsCk 1 u := hu2.of_le (by norm_num)
  have huc : Continuous u := hρc.pow q
  have hJ0 : 0 ≤ J := integral_nonneg fun x => mul_nonneg (pow_nonneg (hnn x) _) (sq_nonneg _)
  have hY' : hsNormSq 0 (coeffOf u) = Y := by
    rw [parseval_real huc, hY]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hu]
    rw [← pow_mul]; congr 1; omega
  have ha : hsNormSq 0 (fun k => ((2 * Real.pi * Lattice.enorm k : ℝ) : ℂ) * coeffOf u k) =
      (q : ℝ) ^ 2 * J := by
    rw [grad_parseval hu1, hJ, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hu]
    rw [norm_grad_pow_sq hρ1 q hq x]
    have : p - 2 = 2 * q - 2 := by omega
    rw [this]; ring
  have hcoefB : ∀ k, ‖coeffOf u k‖ ≤ B := by
    intro k
    refine (norm_coeffOf_le k).trans ?_
    have : ∫ x, |u x| = ∫ x, ρ x ^ q :=
      integral_congr_ae (Eventually.of_forall fun x => abs_of_nonneg (pow_nonneg (hnn x) q))
    rw [this]; exact hXq
  have hmem1 := (memHs_one_coeffOf u hu1).1
  have hN := hNash _ hmem1 B (by linarith) hcoefB
  rw [hY', ha] at hN
  have hlog := nash_logistic_form hd hCn (by linarith) hY0 (by positivity) hN
  have hq' : (q : ℝ) = (p : ℝ) / 2 := by rw [hpR]; ring
  have e1 : (p : ℝ) * (-ν * ((p : ℝ) - 1) * J + (((p : ℝ) - 1) / p) * Z) =
      -(L * ((q : ℝ) ^ 2 * J)) + ((p : ℝ) - 1) * Z := by
    rw [hL, hq']
    field_simp
    ring
  rw [e1]
  have h3 : L * (κ * Y ^ (1 + 2 / (d : ℝ))) ≤ L * ((q : ℝ) ^ 2 * J + B ^ 2) :=
    mul_le_mul_of_nonneg_left hlog hL0
  have h4 : ((p : ℝ) - 1) * Z ≤ ((p : ℝ) - 1) * ((D + A) * Y) :=
    mul_le_mul_of_nonneg_left hZle (by linarith)
  nlinarith


theorem kappa_pow (hd : 1 ≤ d) {P : ℝ} (hP : 0 < P) :
    (P ^ (-(1 / (d : ℝ)))) ^ d = P⁻¹ := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  rw [← Real.rpow_natCast, ← Real.rpow_mul hP.le]
  have : -(1 / (d : ℝ)) * (d : ℝ) = -1 := by field_simp
  rw [this, Real.rpow_neg_one]

/-! ### Section 4: one step of the Alikakos iteration on `[0,T]` -/

/-- From `∫ρ^q ≤ B` on `[0,T]` to `∫ρ^{2q} ≤ max (∫ρ₀^{2q}) M`, for constants `M` large enough. -/
theorem step_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (hν : 0 < ν) (ρc : ℝ → Coeff d) {T : ℝ} (H : MFSolRealOn d s V ν K ρ₀ ρc T)
    (hnn : ∀ t ∈ Set.Icc 0 T, ∀ x, 0 ≤ mfPath ρc t x)
    (hmass : ∀ t ∈ Set.Icc 0 T, ∫ x, mfPath ρc t x = 1)
    (Cn : ℝ) (hCn : 0 < Cn) (hNash : NashBound d Cn) (A D : ℝ) (hA0 : 0 ≤ A) (hD0 : 0 ≤ D)
    (hpair : PairingBound d s A) (hDV : ∀ x, Torus.laplacian V x ≤ D)
    (q : ℕ) (hq : 1 ≤ q) (B : ℝ) (hB : 1 ≤ B)
    (hXq : ∀ t ∈ Set.Icc 0 T, ∫ x, mfPath ρc t x ^ q ≤ B)
    (τ M : ℝ) (hτ : (q : ℝ) * ((D + A) / ν) ≤ τ) (hM0 : 0 ≤ M)
    (hM1 : τ ^ d * Cn * B ^ 4 ≤ M ^ 2) (hM2 : 2 ^ d * Cn * B ^ (2 * d + 4) ≤ M ^ (d + 2)) :
    ∀ t ∈ Set.Icc 0 T, ∫ x, mfPath ρc t x ^ (2 * q) ≤
      max (∫ x, mfPath ρc 0 x ^ (2 * q)) M := by
  intro t₁ ht₁
  obtain ⟨h1, -⟩ := continuousOn_mfPath_prod_on hd s hs0 hsd K hK V ρ₀ hV ν ρc H
  obtain ⟨p, hpq⟩ : ∃ p : ℕ, p = 2 * q := ⟨_, rfl⟩
  have hpR : (p : ℝ) = 2 * q := by rw [hpq]; push_cast; ring
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpR2 : (2 : ℝ) ≤ p := by linarith
  have hpos : (0 : ℝ) < p := by linarith
  set P : ℝ := Cn * B ^ 4 with hP
  have hP0 : 0 < P := by positivity
  set κ : ℝ := P ^ (-(1 / (d : ℝ))) with hκ
  have hκ0 : 0 < κ := Real.rpow_pos_of_pos hP0 _
  have hκd : κ ^ d = P⁻¹ := kappa_pow hd hP0
  set L : ℝ := ν * (4 * ((p : ℝ) - 1) / (p : ℝ)) with hL
  have hL0 : 0 < L := by
    have : 0 < 4 * ((p : ℝ) - 1) / (p : ℝ) := by
      apply div_pos <;> linarith
    positivity
  set X : ℝ → ℝ := fun τ => ∫ x, mfPath ρc τ x ^ p with hX
  have hXc : ContinuousOn X (Icc 0 T) :=
    continuousOn_integral_comp (mfPath ρc) (fun r : ℝ => r ^ p) univ (continuous_pow p).continuousOn
      h1 (fun _ _ _ => mem_univ _)
  have hX0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ X t := fun t ht =>
    integral_nonneg fun x => pow_nonneg (hnn t ht x) _
  have hα : 0 < L * κ := mul_pos hL0 hκ0
  have hγ : 0 ≤ ((p : ℝ) - 1) * (D + A) := mul_nonneg (by linarith) (by linarith)
  have hδ : 0 ≤ L * B ^ 2 := by positivity
  have hder : ∀ t ∈ Ioo (0 : ℝ) T, ∃ X' : ℝ, HasDerivAt X X' t ∧
      X' ≤ -(L * κ) * X t ^ (1 + 2 / (d : ℝ)) + ((p : ℝ) - 1) * (D + A) * X t + L * B ^ 2 := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self ht
    refine ⟨_, hasDerivAt_integral_comp hd s hs0 hsd K hK V ρ₀ hV ν ρc H (fun r : ℝ => r ^ p) univ
      isOpen_univ (contDiff_id.pow p).contDiffOn (a := 0) (b := T) le_rfl (ht.1.trans ht.2) le_rfl
      (fun _ _ _ => mem_univ _) ht, ?_⟩
    have := pow_energy_ineq hd s hs0 hsd K hK V hV ν hν (ρc t) (H.sol.cont.1 t htI)
      (H.real t htI) (hnn t htI) (hmass t htI) Cn hCn hNash A D hpair hDV q hq B hB (hXq t htI)
    rw [← hpq] at this
    exact this
  have hlog := le_of_deriv_le_logistic hd X T (L * κ) (((p : ℝ) - 1) * (D + A)) (L * B ^ 2) hα hγ hδ
    hXc hX0 hder t₁ ht₁
  rw [← hpq]
  refine hlog.trans ?_
  refine max_le_max le_rfl (max_le ?_ ?_)
  · -- first threshold
    have hx : 2 * (((p : ℝ) - 1) * (D + A)) / (L * κ) =
        (2 * (((p : ℝ) - 1) * (D + A)) / L) * κ⁻¹ := by
      field_simp
    have hx2 : 2 * (((p : ℝ) - 1) * (D + A)) / L = (q : ℝ) * ((D + A) / ν) := by
      rw [hL]
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      rw [hpR]
      have h2q : (2 : ℝ) * q - 1 ≠ 0 := by linarith
      field_simp
      ring
    have hx0 : 0 ≤ (q : ℝ) * ((D + A) / ν) := by positivity
    refine rpow_threshold_le_sq (by positivity) hM0 ?_
    rw [hx, hx2, mul_pow, inv_pow, hκd, inv_inv]
    refine le_trans ?_ hM1
    have := pow_le_pow_left₀ hx0 hτ d
    rw [hP]
    nlinarith [mul_le_mul_of_nonneg_right this hP0.le]
  · -- second threshold
    have hx : 2 * (L * B ^ 2) / (L * κ) = 2 * B ^ 2 * κ⁻¹ := by
      field_simp
    refine rpow_threshold_le_pow (by positivity) hM0 ?_
    rw [hx, mul_pow, inv_pow, hκd, inv_inv, mul_pow, ← pow_mul]
    refine le_trans (le_of_eq ?_) hM2
    rw [hP]
    have : B ^ (2 * d + 4) = B ^ (2 * d) * B ^ 4 := pow_add _ _ _
    rw [this]; ring


/-! ### Section 5: constants for the iteration, and `L^{2^j}` bounds give `L^∞` -/

/-- A single constant `ϑ ≥ 1` serving every level of the iteration. -/
theorem exists_theta (Cn e : ℝ) (hCn : 0 < Cn) (he : 0 ≤ e) (d : ℕ) :
    ∃ ϑ : ℝ, 1 ≤ ϑ ∧ ∀ j : ℕ, (((2 : ℝ) ^ j) * e) ^ d * Cn ≤ ϑ ^ (2 * (j + 1)) ∧
      2 ^ d * Cn ≤ ϑ ^ ((j + 1) * (d + 2)) := by
  set Cn' : ℝ := max 1 Cn with hCn'
  set e' : ℝ := max e 1 with he'
  have hC1 : 1 ≤ Cn' := le_max_left _ _
  have hCC : Cn ≤ Cn' := le_max_right _ _
  have he1 : 1 ≤ e' := le_max_right _ _
  set Θ : ℝ := Cn' * (2 * e') ^ d with hΘ
  refine ⟨1 + Θ + 2 ^ d * Cn', ?_, fun j => ?_⟩
  · have : 0 ≤ Θ := by positivity
    have : 0 ≤ 2 ^ d * Cn' := by positivity
    linarith
  set ϑ : ℝ := 1 + Θ + 2 ^ d * Cn' with hϑ
  have hΘ0 : 0 ≤ Θ := by positivity
  have h2C : 0 ≤ 2 ^ d * Cn' := by positivity
  have hϑ1 : 1 ≤ ϑ := by linarith
  have hΘϑ : Θ ≤ ϑ := by linarith
  have hΘ1 : 1 ≤ Θ := by
    have : 1 ≤ (2 * e') ^ d := one_le_pow₀ (by linarith)
    nlinarith
  constructor
  · -- `(2^j e)^d Cn ≤ Θ^{j+1} ≤ (ϑ²)^{j+1}`
    have h1 : (2 : ℝ) ^ j * e ≤ (2 * e') ^ (j + 1) := by
      rw [mul_pow]
      have : e ≤ e' ^ (j + 1) := by
        calc e ≤ e' := le_max_left _ _
          _ = e' ^ 1 := (pow_one _).symm
          _ ≤ e' ^ (j + 1) := pow_le_pow_right₀ he1 (by omega)
      calc (2 : ℝ) ^ j * e ≤ 2 ^ j * e' ^ (j + 1) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ 2 ^ (j + 1) * e' ^ (j + 1) := by
            gcongr; norm_num; omega
    have h2 : ((2 : ℝ) ^ j * e) ^ d ≤ ((2 * e') ^ d) ^ (j + 1) := by
      calc ((2 : ℝ) ^ j * e) ^ d ≤ ((2 * e') ^ (j + 1)) ^ d := pow_le_pow_left₀ (by positivity) h1 d
        _ = ((2 * e') ^ d) ^ (j + 1) := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have h3 : Cn ≤ Cn' ^ (j + 1) :=
      hCC.trans (by
        calc Cn' = Cn' ^ 1 := (pow_one _).symm
          _ ≤ Cn' ^ (j + 1) := pow_le_pow_right₀ hC1 (by omega))
    calc ((2 : ℝ) ^ j * e) ^ d * Cn ≤ ((2 * e') ^ d) ^ (j + 1) * Cn' ^ (j + 1) :=
          mul_le_mul h2 h3 (by linarith) (by positivity)
      _ = Θ ^ (j + 1) := by rw [hΘ, mul_pow]; ring
      _ ≤ (ϑ ^ 2) ^ (j + 1) := by
          refine pow_le_pow_left₀ hΘ0 ?_ _
          nlinarith
      _ = ϑ ^ (2 * (j + 1)) := by rw [← pow_mul]
  · calc (2 : ℝ) ^ d * Cn ≤ 2 ^ d * Cn' := by gcongr
      _ ≤ ϑ := by linarith
      _ = ϑ ^ 1 := (pow_one _).symm
      _ ≤ ϑ ^ ((j + 1) * (d + 2)) := pow_le_pow_right₀ hϑ1 (by nlinarith)

/-- `L^{2^j}` bounds give an `L^∞` bound (subsequence version of `abs_le_of_integral_pow_le`). -/
theorem abs_le_of_integral_two_pow_le {u : Torus d → ℝ} (hu : Continuous u) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (h : ∀ j : ℕ, ∫ x, |u x| ^ (2 ^ j) ≤ Λ ^ (2 ^ j)) : ∀ x, |u x| ≤ Λ := by
  intro x₀
  by_contra hlt
  rw [not_le] at hlt
  set a := (|u x₀| + Λ) / 2 with ha
  have haΛ : Λ < a := by rw [ha]; linarith
  have hax : a < |u x₀| := by rw [ha]; linarith
  have ha0 : 0 < a := lt_of_le_of_lt hΛ haΛ
  set U : Set (Torus d) := {x | a < |u x|} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const hu.abs
  have hUne : U.Nonempty := ⟨x₀, hax⟩
  have hμ : 0 < (volume U).toReal := by
    have h1 : 0 < volume U := hUo.measure_pos volume hUne
    exact ENNReal.toReal_pos h1.ne' (measure_ne_top _ _)
  set μ₀ := (volume U).toReal with hμ₀
  have hlow : ∀ p : ℕ, μ₀ * a ^ p ≤ ∫ x, |u x| ^ p := by
    intro p
    have hint : Integrable (fun x : Torus d => |u x| ^ p) :=
      (hu.abs.pow p).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hind : Integrable (U.indicator fun _ => a ^ p) :=
      (integrable_const _).indicator hUo.measurableSet
    have h1 : ∫ x, U.indicator (fun _ => a ^ p) x ≤ ∫ x, |u x| ^ p := by
      refine integral_mono hind hint fun x => ?_
      by_cases hx : x ∈ U
      · rw [Set.indicator_of_mem hx]
        exact pow_le_pow_left₀ ha0.le (le_of_lt hx) p
      · rw [Set.indicator_of_notMem hx]; positivity
    rw [integral_indicator_const _ hUo.measurableSet] at h1
    simpa [mul_comm, hμ₀, Measure.real] using h1
  rcases hΛ.eq_or_lt with h0 | hΛpos
  · subst h0
    have := (hlow 1).trans (by simpa using h 0)
    have : 0 < μ₀ * a ^ 1 := by positivity
    simp at *
    linarith
  · have hr : 1 < a / Λ := by rw [lt_div_iff₀ hΛpos]; linarith
    have ht := (tendsto_pow_atTop_atTop_of_one_lt hr).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
    have hev : ∀ᶠ j : ℕ in atTop, 1 / μ₀ + 1 ≤ (a / Λ) ^ (2 ^ j) := ht.eventually_ge_atTop _
    obtain ⟨j, hj⟩ := hev.exists
    have h1 := (hlow (2 ^ j)).trans (h j)
    have h2 : μ₀ * (a / Λ) ^ (2 ^ j) * Λ ^ (2 ^ j) ≤ 1 * Λ ^ (2 ^ j) := by
      rw [div_pow, one_mul]
      have : μ₀ * (a ^ (2 ^ j) / Λ ^ (2 ^ j)) * Λ ^ (2 ^ j) = μ₀ * a ^ (2 ^ j) := by
        field_simp
      rw [this]; exact h1
    have h3 : μ₀ * (a / Λ) ^ (2 ^ j) ≤ 1 := le_of_mul_le_mul_right h2 (by positivity)
    have h4 : 1 ≤ μ₀ * (1 / μ₀) := by rw [mul_one_div_cancel hμ.ne']
    nlinarith


/-! ### Section 6: the uniform upper bound -/

/-- Uniform-in-time `L^∞` bound (Alikakos iteration with Nash), uniform in `ν ∈ [ν₋, ν₊]`,
for real solutions on `[0,T]` with a constant independent of `T`
(`MeanFieldAprioriAmendment.md` §2.5). -/
theorem exists_sup_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (νm νp : ℝ)
    (hνm : 0 < νm) (hνν : νm ≤ νp) (ρ₀ : Torus d → ℝ) (hρ₀ : IsProbDensity ρ₀)
    (hρ₀H : MemSobolev K ρ₀) (hpos : ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ ρ₀ x) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ ν ∈ Set.Icc νm νp, ∀ (T : ℝ) (ρc : ℝ → Coeff d),
      MFSolRealOn d s V ν K ρ₀ ρc T →
      ∀ t ∈ Set.Icc 0 T, ∀ x, 0 ≤ mfPath ρc t x ∧ mfPath ρc t x ≤ Λ := by
  have _ := hνν
  obtain ⟨Cn, hCn, hN⟩ := nash_fourier hd
  have hNash : NashBound d Cn := hN
  obtain ⟨A, hA0, -, hA⟩ := exists_laplaceRiesz_pairing_bound hd s hs0 hsd
  have hpair : PairingBound d s A := hA
  have hV2 : Torus.IsCk 2 V := hV.of_le (by exact_mod_cast (by omega : 2 ≤ K + 2))
  obtain ⟨D, hD0, hD⟩ := exists_abs_le_of_continuous _ (continuous_laplacian_of_isCk hV2)
  have hDV : ∀ x, Torus.laplacian V x ≤ D := fun x => (abs_le.1 (hD x)).2
  have hKd : (d : ℝ) / 2 < K := by linarith
  have hmem0 : MemHs (K : ℝ) (coeffOf ρ₀) := (hsNormSq_coeffOf K ρ₀ hρ₀H).1
  have hsum0 := summable_norm_of_memHs (K : ℝ) hKd _ hmem0
  have hg0c : Continuous (toFun (coeffOf ρ₀)) := MFProduct.continuous_toFun _ hsum0
  obtain ⟨R₀, hR₀0, hR₀⟩ := exists_abs_le_of_continuous _ hg0c
  set R : ℝ := max R₀ 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  obtain ⟨ϑ, hϑ1, hϑ⟩ := exists_theta Cn ((D + A) / νm) hCn (by positivity) d
  refine ⟨R * ϑ ^ 2, by positivity, ?_⟩
  intro ν hν T ρc H t ht
  have hνpos : 0 < ν := lt_of_lt_of_le hνm hν.1
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h0T : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  -- positivity and mass
  obtain ⟨δ, hδ, hδ'⟩ := exists_pos_on_Icc hd s hs0 hsd K hK V ρ₀ hV ν hνpos ρc H hρ₀H hpos
  have hnn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 ≤ mfPath ρc t x := fun t ht x =>
    (hδ.trans_le (hδ' t ht x)).le
  have hmass : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ x, mfPath ρc t x = 1 := by
    intro t ht
    have hsum : Summable fun k => ‖ρc t k‖ :=
      summable_norm_of_memHs (K : ℝ) hKd _ (H.sol.cont.1 t ht)
    have h0 : ρc t 0 = 1 := by
      rw [coeff_zero_eq_on hd s V ρ₀ ν K ρc H.sol ht, coeffOf_zero_eq, hρ₀.integral_one]
      simp
    have h1 := coeffOf_toFun (ρc t) (H.real t ht) hsum
    have h2 := congrFun h1 0
    rw [coeffOf_zero_eq, h0] at h2
    exact_mod_cast h2
  have hR0 : ∀ p : ℕ, ∫ x, mfPath ρc 0 x ^ p ≤ R ^ p := by
    intro p
    have h0 : mfPath ρc 0 = toFun (coeffOf ρ₀) := by
      funext x; simp [mfPath, H.sol.init]
    have hc0 : Continuous (mfPath ρc 0) := by rw [h0]; exact hg0c
    calc ∫ x, mfPath ρc 0 x ^ p ≤ ∫ _x : Torus d, R ^ p := by
          refine integral_mono ?_ (integrable_const _) fun x => ?_
          · exact (hc0.pow p).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
          · refine pow_le_pow_left₀ (hnn 0 h0T x) ?_ p
            rw [h0]
            exact ((le_abs_self _).trans (hR₀ x)).trans (le_max_left _ _)
      _ = R ^ p := by simp
  -- the Alikakos iteration
  have hP : ∀ j : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫ x, mfPath ρc t x ^ (2 ^ j) ≤ R ^ (2 ^ j) * ϑ ^ (2 ^ (j + 1) - j - 2) := by
    intro j
    induction j with
    | zero =>
      intro t ht
      norm_num [hmass t ht]
      exact hR1
    | succ j ih =>
      intro t ht
      set a : ℕ := 2 ^ (j + 1) - j - 2 with ha
      set B : ℝ := R ^ (2 ^ j) * ϑ ^ a with hB
      have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR1) (one_le_pow₀ hϑ1)
      obtain ⟨hc1, hc2⟩ := hϑ j
      have hq1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      have hτ : (((2 ^ j : ℕ) : ℝ)) * ((D + A) / ν) ≤ (2 : ℝ) ^ j * ((D + A) / νm) := by
        push_cast
        gcongr
        exact hν.1
      have hM1 : ((2 : ℝ) ^ j * ((D + A) / νm)) ^ d * Cn * B ^ 4 ≤ (ϑ ^ (j + 1) * B ^ 2) ^ 2 := by
        calc ((2 : ℝ) ^ j * ((D + A) / νm)) ^ d * Cn * B ^ 4
            ≤ ϑ ^ (2 * (j + 1)) * B ^ 4 := mul_le_mul_of_nonneg_right hc1 (by positivity)
          _ = (ϑ ^ (j + 1) * B ^ 2) ^ 2 := by ring
      have hM2 : 2 ^ d * Cn * B ^ (2 * d + 4) ≤ (ϑ ^ (j + 1) * B ^ 2) ^ (d + 2) := by
        calc 2 ^ d * Cn * B ^ (2 * d + 4)
            ≤ ϑ ^ ((j + 1) * (d + 2)) * B ^ (2 * d + 4) :=
              mul_le_mul_of_nonneg_right hc2 (by positivity)
          _ = (ϑ ^ (j + 1) * B ^ 2) ^ (d + 2) := by ring
      have key := step_bound hd s hs0 hsd K hK V ρ₀ hV ν hνpos ρc H hnn hmass Cn hCn hNash A D
        hA0 hD0 hpair hDV (2 ^ j) hq1 B hB1 ih _ _ hτ (by positivity) hM1 hM2 t ht
      have e2 : 2 * 2 ^ j = 2 ^ (j + 1) := by ring
      rw [e2] at key
      refine key.trans (max_le ?_ ?_)
      · refine (hR0 _).trans ?_
        exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hϑ1)
      · have hm : j + 2 ≤ 2 ^ (j + 1) := Nat.lt_two_pow_self (n := j + 1)
        have e4 : 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by ring
        have e5 : (j + 1) + a * 2 = 2 ^ (j + 1 + 1) - (j + 1) - 2 := by
          rw [ha, e4]; omega
        refine le_of_eq ?_
        calc ϑ ^ (j + 1) * B ^ 2 = R ^ (2 ^ j * 2) * (ϑ ^ (j + 1) * ϑ ^ (a * 2)) := by
              rw [hB, mul_pow, ← pow_mul, ← pow_mul]; ring
          _ = R ^ (2 ^ (j + 1)) * ϑ ^ (2 ^ (j + 1 + 1) - (j + 1) - 2) := by
              rw [← pow_add, e5, pow_succ 2 j]
  -- conclusion
  have hu : Continuous (mfPath ρc t) := by
    obtain ⟨h1, -⟩ := continuousOn_mfPath_prod_on hd s hs0 hsd K hK V ρ₀ hV ν ρc H
    exact h1.comp_continuous (Continuous.prodMk_right t) (fun x => ⟨ht, mem_univ _⟩)
  have habs := abs_le_of_integral_two_pow_le hu (R * ϑ ^ 2) (by positivity) (fun j => by
    have e1 : ∫ x, |mfPath ρc t x| ^ (2 ^ j) = ∫ x, mfPath ρc t x ^ (2 ^ j) :=
      integral_congr_ae (Eventually.of_forall fun x => by
        simp only [abs_of_nonneg (hnn t ht x)])
    rw [e1]
    refine (hP j t ht).trans ?_
    rw [mul_pow, ← pow_mul]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hϑ1 ?_) (by positivity)
    have : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
    omega)
  intro x
  exact ⟨hnn t ht x, (le_abs_self _).trans (habs x)⟩

end HRS.PDE.MFApriori
