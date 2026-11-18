import HRS.MS.Ker1Aux6

/-!
# Lemma S.A.34, kernel part (`S:B:lem:expanding-tori`) -- packet MS-KER1

`expanding_tori_kernel_proof` restates `HRS.Whole.AppendixALemmas.expanding_tori_kernel` (frozen in
`HRS/Whole/AppendixALemmas.lean`, statement copied verbatim).

Route: `g₁ = periodicRiesz d s ∘ mk` is the unit-period kernel; `γ_L(x) = L^{-s} g₁(x/L)` satisfies
`IsPeriodicRieszKernel d s L` (`Ker1Aux2`) and every `γ` with this property agrees with `γ_L` off the lattice
`Lℤ^d` (`Ker1Aux3`: Fourier uniqueness on `L¹(𝕋^d)` plus continuity), in particular on `0 < |x| ≤ L/2`.
Near `0`, `g₁ = g_E + q` with `q` smooth (`periodicRiesz_local_singularity'` and its `d = 1` analogues), whence the
bounds (a), (b) (homogeneity of `g_E`, compactness away from `0`) and the convergence (c)
(`γ_L - g_E = L^{-s} q(·/L) (+ log L)`) (`Ker1Aux4`-`Ker1Aux6`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff ComplexConjugate

namespace HRS.MS.Ker1

open HRS HRS.Whole HRS.Whole.AppendixALemmas

variable {d : ℕ}

theorem expanding_tori_kernel_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) :
    (∀ L : ℝ, 1 ≤ L → ∃ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ) ∧
    (∃ C : ℝ, ∀ L : ℝ, 1 ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      (∀ n : ℕ, n ≤ m + 2 → 0 < (n : ℝ) + s → ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ L / 2 →
        ‖iteratedFDeriv ℝ n γ x‖ ≤ C * (‖x‖ ^ (-s - n) + (if 0 < s then L ^ (-s - n) else 0) +
          (if s = 0 then L ^ (-(n : ℝ)) else 0))) ∧
      (s = 0 → ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ L / 2 →
        |γ x - Real.log L| ≤ C * (1 + |Real.log ‖x‖|))) ∧
    ∀ K : Set (Euc d), IsCompact K → (∀ x ∈ K, x ≠ 0) → ∀ n : ℕ, n ≤ m + 2 → ∀ ε : ℝ, 0 < ε →
      ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
        ((0 < (n : ℝ) + s → ∀ x ∈ K,
            ‖iteratedFDeriv ℝ n γ x - iteratedFDeriv ℝ n (rieszKernel d s) x‖ ≤ ε) ∧
          (n = 0 → s = 0 → ∃ c : ℝ, ∀ x ∈ K, |γ x - rieszKernel d s x - c| ≤ ε)) := by
  refine ⟨fun L hL => ⟨ker1_gam d s L, ker1_gam_isKernel hd hs0 hsd (by linarith)⟩, ?_, ?_⟩
  · -- the uniform constant
    have hCn : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (0 < (n : ℝ) + s → ∀ L : ℝ, 0 < L → ∀ x : Euc d, x ≠ 0 →
        ‖x‖ ≤ L / 2 → ‖iteratedFDeriv ℝ n (ker1_gam d s L) x‖ ≤ C * ‖x‖ ^ (-s - n)) := by
      intro n
      by_cases hn : 0 < (n : ℝ) + s
      · obtain ⟨C, hC0, hC⟩ := ker1_gam_bound_a hd hs0 hsd n hn
        exact ⟨C, hC0, fun _ => hC⟩
      · exact ⟨0, le_rfl, fun h => absurd h hn⟩
    choose Cn hCn0 hCn using hCn
    have hClog : ∃ C : ℝ, 0 ≤ C ∧ (s = 0 → ∀ L : ℝ, 0 < L → ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ L / 2 →
        |ker1_gam d s L x - Real.log L| ≤ C + |Real.log ‖x‖|) := by
      by_cases hs : s = 0
      · subst hs
        obtain ⟨C, hC0, hC⟩ := ker1_gam_bound_b hd
        exact ⟨C, hC0, fun _ => hC⟩
      · exact ⟨0, le_rfl, fun h => absurd h hs⟩
    obtain ⟨Cl, hCl0, hCl⟩ := hClog
    refine ⟨1 + ∑ n ∈ Finset.range (m + 3), Cn n + Cl, fun L hL γ hγ => ⟨fun n hn hns x hx0 hx => ?_, fun hs x hx0 hx => ?_⟩⟩
    · have hLp : 0 < L := by linarith
      have hoff := ker1_offLattice_of_half hLp hx0 hx
      have heq := (ker1_eventually_eq_gam hd hs0 hsd hLp hγ hoff).iteratedFDeriv ℝ n
      rw [heq.eq_of_nhds]
      refine (hCn n hns L hLp x hx0 hx).trans ?_
      have hle : Cn n ≤ 1 + ∑ n ∈ Finset.range (m + 3), Cn n + Cl := by
        have : Cn n ≤ ∑ n ∈ Finset.range (m + 3), Cn n :=
          Finset.single_le_sum (f := Cn) (fun i _ => hCn0 i) (Finset.mem_range.2 (by omega))
        linarith
      have h1 : 0 ≤ ‖x‖ ^ (-s - (n : ℝ)) := by positivity
      have h2 : 0 ≤ (if 0 < s then L ^ (-s - (n : ℝ)) else 0) := by
        split_ifs
        · exact Real.rpow_nonneg hLp.le _
        · exact le_rfl
      have h3 : 0 ≤ (if s = 0 then L ^ (-(n : ℝ)) else 0) := by
        split_ifs
        · exact Real.rpow_nonneg hLp.le _
        · exact le_rfl
      have hCn0' := hCn0 n
      nlinarith
    · have hLp : 0 < L := by linarith
      have hoff := ker1_offLattice_of_half hLp hx0 hx
      have heq := (ker1_eventually_eq_gam hd hs0 hsd hLp hγ hoff).self_of_nhds
      rw [heq]
      refine (hCl hs L hLp x hx0 hx).trans ?_
      have h1 : 0 ≤ |Real.log ‖x‖| := abs_nonneg _
      have hS : 0 ≤ ∑ n ∈ Finset.range (m + 3), Cn n := Finset.sum_nonneg fun i _ => hCn0 i
      nlinarith
  · intro K hK hK0 n _ ε hε
    obtain ⟨q, δ, hδ, hq, hloc⟩ := ker1_decomp hd hs0 hsd
    obtain ⟨L₁, hL₁pos, hL₁⟩ := ker1_conv_aux hd hs0 hδ hq hloc hK hK0 n hε
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    refine ⟨max L₁ (2 * max R 1), fun L hL γ hγ => ?_⟩
    have hL1 : L₁ ≤ L := (le_max_left _ _).trans hL
    have hL2 : 2 * max R 1 ≤ L := (le_max_right _ _).trans hL
    have hRpos : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hLp : 0 < L := by linarith
    have hoff : ∀ x ∈ K, ∀ z : Fin d → ℤ, x ≠ L • latticePt z := fun x hx =>
      ker1_offLattice_of_half hLp (hK0 x hx) (by
        have := (hR x hx).trans (le_max_left R 1); linarith)
    refine ⟨fun hns x hx => ?_, fun hn hs => ?_⟩
    · have heq := (ker1_eventually_eq_gam hd hs0 hsd hLp hγ (hoff x hx)).iteratedFDeriv ℝ n
      rw [heq.eq_of_nhds]
      refine (hL₁ L hL1 x hx).1 ?_
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · right
        intro hs0'
        subst h0; subst hs0'; simp at hns
      · left; omega
    · refine ⟨Real.log L + q 0, fun x hx => ?_⟩
      have heq := (ker1_eventually_eq_gam hd hs0 hsd hLp hγ (hoff x hx)).self_of_nhds
      rw [heq]
      exact (hL₁ L hL1 x hx).2 hn hs

example := (@expanding_tori_kernel_proof : type_of% @HRS.Whole.AppendixALemmas.expanding_tori_kernel)

end HRS.MS.Ker1
