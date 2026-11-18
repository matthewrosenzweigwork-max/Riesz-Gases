import HRS.PDE.MeanFieldAprioriUpper
import HRS.PDE.MeanFieldPairInverse

/-!
# V-uniform sup bound (packet EVA of `docs/MAIN_E_EVU_PLAN.md`)

`exists_sup_bound_unifV` is a copy of `HRS.PDE.MFApriori.exists_sup_bound`
(`HRS/PDE/MeanFieldAprioriUpper.lean:498`) with the constant `Λ` chosen before the potential `V`:
the fixed data are `d s K νm νp ρ₀` and the bound `Bv`; then for every smooth `V` with
`Torus.cbNorm (K+2) V ≤ Bv`, the solution bound holds with the same `Λ`.

The only place where `V` entered through a constant of the original proof is the bound `ΔV ≤ D`
(originally `D` from `exists_abs_le_of_continuous`); here `D := d * |Bv|`, obtained from
`MFPair.abs_laplacian_le` (`|ΔV x| ≤ d * cbNorm (K+2) V ≤ d * Bv`). All other uses of `V`
(`exists_pos_on_Icc`, `step_bound`, `continuousOn_mfPath_prod_on`) are per-`V` qualitative facts,
and `step_bound` takes `D` explicitly.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate
open HRS.PDE HRS.PDE.MFApriori HRS.PDE.MFApriori.Aux

namespace HRS.ME.EVU

variable {d : ℕ}

/-- Uniform-in-time `L^∞` bound with the constant chosen before `V` (copy of
`HRS.PDE.MFApriori.exists_sup_bound`, `V` restricted by `cbNorm (K+2) V ≤ Bv`). -/
theorem exists_sup_bound_unifV (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (νm νp : ℝ)
    (hνm : 0 < νm) (hνν : νm ≤ νp) (ρ₀ : Torus d → ℝ) (hρ₀ : IsProbDensity ρ₀)
    (hρ₀H : MemSobolev K ρ₀) (hpos : ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ ρ₀ x) (Bv : ℝ) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ V : Torus d → ℝ, Torus.IsCk (K + 2) V → Torus.cbNorm (K + 2) V ≤ Bv →
      ∀ ν ∈ Set.Icc νm νp, ∀ (T : ℝ) (ρc : ℝ → Coeff d),
      MFSolRealOn d s V ν K ρ₀ ρc T →
      ∀ t ∈ Set.Icc 0 T, ∀ x, 0 ≤ mfPath ρc t x ∧ mfPath ρc t x ≤ Λ := by
  have _ := hνν
  obtain ⟨Cn, hCn, hN⟩ := nash_fourier hd
  have hNash : NashBound d Cn := hN
  obtain ⟨A, hA0, -, hA⟩ := exists_laplaceRiesz_pairing_bound hd s hs0 hsd
  have hpair : PairingBound d s A := hA
  set D : ℝ := (d : ℝ) * |Bv| with hDdef
  have hD0 : 0 ≤ D := by positivity
  have hKd : (d : ℝ) / 2 < K := by linarith
  have hmem0 : MemHs (K : ℝ) (coeffOf ρ₀) := (hsNormSq_coeffOf K ρ₀ hρ₀H).1
  have hsum0 := summable_norm_of_memHs (K : ℝ) hKd _ hmem0
  have hg0c : Continuous (toFun (coeffOf ρ₀)) := MFProduct.continuous_toFun _ hsum0
  obtain ⟨R₀, hR₀0, hR₀⟩ := exists_abs_le_of_continuous _ hg0c
  set R : ℝ := max R₀ 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  obtain ⟨ϑ, hϑ1, hϑ⟩ := exists_theta Cn ((D + A) / νm) hCn (by positivity) d
  refine ⟨R * ϑ ^ 2, by positivity, ?_⟩
  intro V hV hVB ν hν T ρc H t ht
  have hDV : ∀ x, Torus.laplacian V x ≤ D := by
    intro x
    have h1 := HRS.PDE.MFPair.abs_laplacian_le (L := K + 2) (by omega) hV x
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    calc Torus.laplacian V x ≤ |Torus.laplacian V x| := le_abs_self _
      _ ≤ d * Torus.cbNorm (K + 2) V := h1
      _ ≤ d * Bv := mul_le_mul_of_nonneg_left hVB hd0
      _ ≤ d * |Bv| := mul_le_mul_of_nonneg_left (le_abs_self Bv) hd0
      _ = D := rfl
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

end HRS.ME.EVU
