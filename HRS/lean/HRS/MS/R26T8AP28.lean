import HRS.MS.R26T8AP27

/-!
# S8.2 local Newton layer, packet T8A.P28: exact bounded linear smooth inverse interface
The norm constant must precede the density: the thermal density is unique (`critical_thermal_eq`) and the weighted semigroup is unique on
`C_M` (`s85_semigroup_unique`), so the constant of P27 for one fixed `(rho0, Ulim)` serves every `(rho, U)`.  Regularity and the equation
come from the merged `s8h2_c5`; linearity of `tensorU` from the weighted semigroup fields on the (weighted-decaying) slices.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

section P28

variable {d : ℕ} {a β : ℝ} {ρβ : Euc d → ℝ} {M : ℝ} {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}

/-- Slices of a weighted-decaying kernel and their `U_t`-images lie in `C_M`. -/
theorem r26t8a_p28_slices
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    (hM : 0 ≤ M) {t : ℝ} (ht : 0 ≤ t) {R : Euc d → Euc d → ℝ}
    (hR : S8hPair M 0 (Function.uncurry R)) :
    (∀ x', MemCM M (R x')) ∧ ∀ y, MemCM M (fun x' => U t (R x') y) := by
  obtain ⟨K0, -, hsec⟩ := s8h2_sec0 hU hM ht
  obtain ⟨hc, hdec, N, -, hN⟩ := s8h2_pair_good hR
  exact ⟨fun x' => s8h2_slice_memCM hc hdec x', (hsec (F := R) (N := N) hc hdec hN t ⟨ht, le_rfl⟩).1⟩

theorem r26t8a_p28_tensor_lin
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    (hM : 0 ≤ M) {t : ℝ} (ht : 0 ≤ t) {R R' : Euc d → Euc d → ℝ}
    (hR : S8hPair M 0 (Function.uncurry R)) (hR' : S8hPair M 0 (Function.uncurry R')) (c : ℝ) (x y : Euc d) :
    tensorU U t (R + c • R') x y = tensorU U t R x y + c * tensorU U t R' x y := by
  obtain ⟨h1, h2⟩ := r26t8a_p28_slices hU hM ht hR
  obtain ⟨h1', h2'⟩ := r26t8a_p28_slices hU hM ht hR'
  have hin : ∀ x' y', U t ((R + c • R') x') y' = U t (R x') y' + c * U t (R' x') y' := by
    intro x' y'
    have e : (R + c • R') x' = R x' + c • R' x' := rfl
    have hm2 : MemCM M (c • R' x') := by
      refine ⟨(h1' x').1.const_smul c, ?_⟩
      have := (h1' x').2.const_mul c
      rw [mul_zero] at this
      exact this.congr fun z => by simp [mul_div_assoc]
    rw [e, hU.add t ht _ _ (h1 x') hm2, hU.smul t ht c _ (h1' x')]
    simp
  unfold tensorU
  have e1 : (fun x' => U t ((R + c • R') x') y) = fun x' => U t (R x') y + c • U t (R' x') y := by
    funext x'; rw [hin]; simp
  have hm2 : MemCM M (c • fun x' => U t (R' x') y) := by
    refine ⟨(h2' y).1.const_smul c, ?_⟩
    have := (h2' y).2.const_mul c
    rw [mul_zero] at this
    exact this.congr fun z => by simp [mul_div_assoc]
  have e2 : (fun x' => U t (R x') y + c • U t (R' x') y) =
      (fun x' => U t (R x') y) + c • fun x' => U t (R' x') y := rfl
  rw [e1, e2, hU.add t ht _ _ (h2 y) hm2, hU.smul t ht c _ (h2' y)]
  simp

end P28

theorem r26t8a_smooth_pair_inverse_bounded
    (d : ℕ) (hd : 2 ≤ d) (a beta M : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 < M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ U, HRS.Whole.IsWeightedSemigroup (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) M U →
      ∀ R : Euc d → Euc d → ℝ,
      HRS.Whole.MemCMpair M 8 R → CanonicalPair (HRS.Whole.withDensityReal rho) R →
      (∃ K : ℝ, K < M ∧ ∃ A : ℝ, ∀ j : ℕ, j ≤ 8 → ∀ x y,
        ‖iteratedFDeriv ℝ j (Function.uncurry R) (x, y)‖ ≤ A * HRS.MS.Phase2S82.pairWeight K x y) →
      CanonicalPair (HRS.Whole.withDensityReal rho) (HRS.Whole.pairInverseW U R) ∧
      ContDiff ℝ 8 (Function.uncurry (HRS.Whole.pairInverseW U R)) ∧
      HRS.Whole.pairNormE M 8 (HRS.Whole.pairInverseW U R) ≤ ENNReal.ofReal C * HRS.Whole.pairNormE M 8 R ∧
      (∀ x y, -pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho)
        (HRS.Whole.pairInverseW U R) x y = R x y) ∧
      (∀ R' : Euc d → Euc d → ℝ, HRS.Whole.MemCMpair M 8 R' →
        CanonicalPair (HRS.Whole.withDensityReal rho) R' →
        (∀ x y, IntegrableOn (fun t => HRS.Whole.tensorU U t R' x y) (Set.Ioi 0)) →
        ∀ c : ℝ, HRS.Whole.pairInverseW U (R + c • R') =
          HRS.Whole.pairInverseW U R + c • HRS.Whole.pairInverseW U R') := by
  by_cases hex : ∃ rho0 : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho0
  · obtain ⟨rho0, hrho0⟩ := hex
    have hrho0' : IsThermalEquilibrium d ((d : ℝ) / 2) a beta rho0 := hrho0
    have hU0 := s85_exists_semigroup hd ha hbeta hrho0' hM
    obtain ⟨C, hC, hP⟩ := r26t8a_pair_inverse_norm d hd a beta M ha hbeta hM rho0 hrho0
      (s85_Ulim a beta rho0 M) hU0
    refine ⟨C, hC, fun rho hrho U hU R hR hcan hgr => ?_⟩
    have hrho' : IsThermalEquilibrium d ((d : ℝ) / 2) a beta rho := hrho
    have hrr : rho = rho0 := (critical_thermal_eq d hd a beta ha hbeta hrho).trans
      (critical_thermal_eq d hd a beta ha hbeta hrho0).symm
    subst hrr
    have hRp0 : S8hPair M 0 (Function.uncurry R) :=
      s8h2_pair_mono (Nat.zero_le 8) (s8h_pair_iff.1 hR)
    have hEq : pairInverseW U R = pairInverseW (s85_Ulim a beta rho M) R := by
      funext x y
      unfold pairInverseW
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      have ht0 : 0 ≤ t := (Set.mem_Ioi.1 ht).le
      obtain ⟨h1, h2⟩ := r26t8a_p28_slices hU hM.le ht0 hRp0
      unfold tensorU
      have e1 : (fun x' => U t (R x') y) = fun x' => s85_Ulim a beta rho M t (R x') y :=
        funext fun x' => by rw [s85_semigroup_unique hd ha hbeta hrho' hM hU ht0 (h1 x')]
      have e2 : U t (fun x' => U t (R x') y) x = s85_Ulim a beta rho M t (fun x' => U t (R x') y) x :=
        congrFun (s85_semigroup_unique hd ha hbeta hrho' hM hU ht0 (h2 y)) x
      rw [e2, e1]
    obtain ⟨hcanΨ, hnorm⟩ := hP R hR hcan
    rw [← hEq] at hcanΨ hnorm
    obtain ⟨K, hK, A, hA⟩ := hgr
    have hC5 := s8h2_c5 hd ha hbeta hrho' hM hU 8 (by norm_num) R (by exact_mod_cast hR.1) hcan.2.2
      ⟨K, hK, fun k hk => ⟨A, fun x y => by
        have := hA k hk x y
        unfold HRS.MS.Phase2S82.pairWeight at this
        simpa [mul_assoc] using this⟩⟩
    obtain ⟨hint, hcd, -, heq⟩ := hC5
    refine ⟨hcanΨ, by exact_mod_cast hcd, hnorm, fun x y => ?_, ?_⟩
    · unfold pairA
      exact heq x y
    · intro R' hR' hcan' hint' c
      have hR'p0 : S8hPair M 0 (Function.uncurry R') :=
        s8h2_pair_mono (Nat.zero_le 8) (s8h_pair_iff.1 hR')
      funext x y
      show ∫ t in Set.Ioi (0 : ℝ), tensorU U t (R + c • R') x y =
        (∫ t in Set.Ioi (0 : ℝ), tensorU U t R x y) + c * ∫ t in Set.Ioi (0 : ℝ), tensorU U t R' x y
      rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht =>
        r26t8a_p28_tensor_lin hU hM.le (Set.mem_Ioi.1 ht).le hRp0 hR'p0 c x y)]
      rw [integral_add (hint x y) ((hint' x y).const_mul c), integral_const_mul]
  · exact ⟨0, le_rfl, fun rho hrho => absurd ⟨rho, hrho⟩ hex⟩

end HRS.MS.R26T8A
