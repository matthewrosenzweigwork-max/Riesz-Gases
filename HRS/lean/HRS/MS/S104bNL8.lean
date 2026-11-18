import HRS.MS.S104bNL7

/-!
# S10.5 (nonlinear), packet S104b-NL8: `S21mData` along a resulting solution

`s104b_data`: for a resulting solution `ρ` of the class, the orbit regularity `S104nOrbit` of the adjoint orbits of the oscillator test functions on every horizon, the gradient
orbit bounds `R2OrbitGrad` of S10.3, the regularity `IsRegularMFRd` and the class bounds, the moving window data `S21mData d s a β T b ρ` holds for every window start `b ≥ 0`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S104b

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.S53 HRS.MS.R2WinErr HRS.MS.R2GenInit HRS.MS.S21m HRS.MH.DualityRd

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
theorem s104b_data (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) {εstar c₁ C₁ ε : ℝ} {ψ : Euc d → ℝ}
    {ρ : ℝ → Euc d → ℝ} (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ)
    (horb : ∀ α : MultiIndex d, ∀ T0 : ℝ, 0 ≤ T0 →
      S104nOrbit ((quadraticGradientDyn d s a β).coeff ρ) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) T0)
    (Cs0 cdec : ℝ) (hcdec : 0 < cdec) (hsum : Summable (s104_b d))
    (hgrad : ∀ α : MultiIndex d,
      (∀ t : ℝ, 0 ≤ t → R2OrbitGrad ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) (Cs0 * s104_b d α) cdec) ∧
      (∀ t : ℝ, 0 ≤ t → R2OrbitGrad ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
        (generatorW ((quadraticGradientDyn d s a β).coeff ρ) t (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))
        (Cs0 * s104_b d α) cdec))
    (hreg : ∀ T0 : ℝ, 0 ≤ T0 → ∃ Λ : ℝ, IsRegularMFRd s 3 Λ T0 ρ)
    (hjm : ∀ T' : ℝ, 0 ≤ T' → Measurable fun p : ℝ × Euc d => ρ (max 0 (min p.1 T')) p.2)
    (hρ2 : Integrable (fun x : Euc d => ‖x‖ ^ 2 * ρ 0 x)) {T : ℝ} (hT : 0 < T) {b : ℝ} (hb : 0 ≤ b) :
    S21mData d s a β T b ρ := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cphi, hCphi0, hphi'⟩ := s104_hphi hd1
  set Cs : ℝ := max Cs0 Cphi with hCs
  have hCs0 : 0 ≤ Cphi := hCphi0
  have hCsn : 0 ≤ Cs := hCs0.trans (le_max_right _ _)
  set k : ℕ := 4 * d + 42 with hk
  set C : WholeCoeff d := (quadraticGradientDyn d s a β).coeff ρ with hCdef
  set m : ℝ := ((wholeSpaceIndex d : ℕ) : ℝ) with hm
  have hτ : 0 ≤ b + T := by linarith
  have horb' : ∀ α : MultiIndex d,
      (∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (oscTestFun m α) (Cs * s104_b d α) cdec) ∧
      (∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (generatorW C t (oscTestFun m α)) (Cs * s104_b d α) cdec) := by
    intro α
    have hle : Cs0 * s104_b d α ≤ Cs * s104_b d α :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (s104_b_nonneg α)
    exact ⟨fun t ht => s104_R2OrbitGrad_mono _ ((hgrad α).1 t ht) hle,
      fun t ht => s104_R2OrbitGrad_mono _ ((hgrad α).2 t ht) hle⟩
  have hφ : ∀ α a', ContDiff ℝ k (fun x => gradComp a' (oscTestFun m α) x) ∧
      ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun x => gradComp a' (oscTestFun m α) x) x‖ ≤ Cs * s104_b d α :=
    fun α a' => ⟨(hphi' α a').1, fun j hj x => ((hphi' α a').2 j hj x).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (s104_b_nonneg α))⟩
  have hex : ∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t →
      (∃ f, IsClassicalAdjointW C t (oscTestFun m α) f) ∧
      (∃ f, IsClassicalAdjointW C t (generatorW C t (oscTestFun m α)) f) :=
    fun α t ht => ⟨(horb α t ht).ex0 t ⟨ht, le_rfl⟩, (horb α t ht).ex1 t ⟨ht, le_rfl⟩⟩
  have hmeasU : ∀ r : ℝ, 0 ≤ r → ∀ (a' : Fin d) α x, AEStronglyMeasurable (fun u => if r < b + u then
      gradComp a' (propagatorW C r (b + u) (generatorW C (b + u) (oscTestFun m α))) x else 0)
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    fun r hr a' α x => s104n_hobs (horb α (b + T) hτ) hT.le hb le_rfl hr a' x
  have hF := s105_win_feat hd1 C k m T b cdec Cs hb hT.le hcdec.le hCsn hsum
    (fun α => (horb' α).1) (fun α => (horb' α).2) hφ (fun α t ht => (hex α t ht).1)
    (fun α t ht => (hex α t ht).2) hmeasU
  have hC : OscAdjointInput C m (b + T) := by
    refine ⟨fun r t hr hrt htT α a' x => s104b_duhamel (horb α (b + T) hτ) hr hrt htT a' x, ?_⟩
    intro a' r hr x
    have hmeas0 : ∀ α x, AEStronglyMeasurable (fun u => if r < 0 + u then gradComp a' (propagatorW C r (0 + u)
        (generatorW C (0 + u) (oscTestFun m α))) x else 0) (volume.restrict (Set.Icc (0 : ℝ) (b + T))) :=
      fun α x => s104n_hobs (horb α (b + T) hτ) hτ le_rfl (by linarith) hr.1 a' x
    obtain ⟨-, -, h3, h4⟩ := s105_winK C k m (b + T) cdec Cs hcdec.le hCsn hsum (fun α => (horb' α).1)
      (fun α => (horb' α).2) hφ le_rfl hr.1 a' hmeas0 x
    refine ⟨s105_memℓp_of_bound (K := Cs) (fun α => ?_) hsum, fun t ht => ?_, ?_⟩
    · have := (hφ α a').2 0 (Nat.zero_le _) x
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    · have := h3 t ⟨by linarith [hr.1, ht.1], ht.2⟩ (by simpa using ht.1)
      simpa only [zero_add] using this
    · simpa only [zero_add] using h4
  have hK : ∀ (a' : Fin d) (r : ℝ), r ∈ Set.Icc (0 : ℝ) (b + T) → ∀ x, S105WinK C m T b a' r x :=
    fun a' r hr x => s105_winK C k m T cdec Cs hcdec.le hCsn hsum (fun α => (horb' α).1)
      (fun α => (horb' α).2) hφ hb hr.1 a' (hmeasU r hr.1 a') x
  have hcl : ∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t → IsClassicalAdjointW C t (oscTestFun m α)
      (fun r => propagatorW C r t (oscTestFun m α)) :=
    fun α t ht => HRS.MS.Fcau.propagatorW_isClassical (hex α t ht).1
  have hM : ∃ Λ ΛV G₀ : ℝ, MFData s Λ (b + T) ΛV G₀ (quadraticGradientDyn d s a β) ρ := by
    obtain ⟨Λ, hΛ⟩ := hreg (b + T) hτ
    obtain ⟨ΛV, G₀, h⟩ := s104b_mfData hs0 hsd hβ ha hres hΛ
    exact ⟨Λ, ΛV, G₀, h⟩
  have hpos : ∀ x, 0 < ρβ x := fun x => HRS.Whole.u4_thermal_pos hρβ x
  exact ⟨hC, hK, hF, hcl, hM, hρ2, hjm (b + T) hτ, fun ψ' hψ hbd =>
    (s21p_rho_weak_cont hρβ.2.1 hpos hres ψ' hψ hbd).mono (fun r hr => hr.1)⟩

end HRS.MS.S104b
