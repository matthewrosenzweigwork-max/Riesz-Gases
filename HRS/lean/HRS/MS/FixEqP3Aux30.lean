import HRS.MS.FixEqP3Aux29

/-!
# S5.7 `fixed_equation` (worker S57P), part 42: the maximal inequality for `X^N - X`
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau HRS.MS.U10

variable {d : ℕ} {θ : Euc d → ℝ} {T : ℝ} {n : ℕ} {K KN : ℝ} {s : ℝ} {M Q : Matrix (Fin d) (Fin d) ℝ} {ν νN : ℝ}
  {c cN : ℝ → Euc d → Euc d} {ρ ρN : ℝ → Euc d → ℝ} {A Λc νbar : ℝ} {m : ℝ} {J : ℕ}
  {Ca CaN Cd CdN Cp1 Cp2 Dt : ℝ}

theorem S57pPairBd.kdiff_hs (P : S57pPairBd θ T n K KN s M Q ν νN c cN ρ ρN A Λc νbar m J Ca CaN Cd CdN Cp1 Cp2 Dt)
    (hT : 0 ≤ T) {q qN τ : ℝ} (hq : 0 ≤ q) (hqN : 0 ≤ qN) (hτ0 : 0 ≤ τ)
    (hτ : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ x : Euc d, ENNReal.ofReal |ρN r x - ρ r x| ≤ ENNReal.ofReal τ)
    (hsum : Summable fun α : MultiIndex d => oscEigenvalue d α ^ ((J : ℝ) - m))
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Set.Icc (0 : ℝ) T) (ht₂ : t₂ ∈ Set.Icc (0 : ℝ) T) :
    ∑' α : MultiIndex d, ‖(s57pκ (fixedEqCoeff s M Q νN cN ρN) T qN ρN t₂ (oscTestFun m α) -
        s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t₂ (oscTestFun m α)) -
      (s57pκ (fixedEqCoeff s M Q νN cN ρN) T qN ρN t₁ (oscTestFun m α) -
        s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t₁ (oscTestFun m α))‖ ^ 2 ≤
      (3 * s57pCz T q qN τ CaN CdN Cp1 Cp2 Dt * ∑' α : MultiIndex d, oscEigenvalue d α ^ ((J : ℝ) - m)) * |t₂ - t₁| := by
  have hs2 : Summable fun α : MultiIndex d => (3 * s57pCz T q qN τ CaN CdN Cp1 Cp2 Dt) * oscEigenvalue d α ^ ((J : ℝ) - m) *
      |t₂ - t₁| := (hsum.mul_left _).mul_right _
  have hk : ∀ α : MultiIndex d, ‖(s57pκ (fixedEqCoeff s M Q νN cN ρN) T qN ρN t₂ (oscTestFun m α) -
        s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t₂ (oscTestFun m α)) -
      (s57pκ (fixedEqCoeff s M Q νN cN ρN) T qN ρN t₁ (oscTestFun m α) -
        s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t₁ (oscTestFun m α))‖ ^ 2 ≤
      (3 * s57pCz T q qN τ CaN CdN Cp1 Cp2 Dt) * oscEigenvalue d α ^ ((J : ℝ) - m) * |t₂ - t₁| := by
    intro α
    rcases le_total t₁ t₂ with h | h
    · rw [abs_of_nonneg (sub_nonneg.2 h)]
      have := P.kdiff_holder hT hq hqN hτ0 hτ α ht₁.1 h ht₂.2
      linarith
    · rw [abs_of_nonpos (sub_nonpos.2 h), neg_sub, ← norm_neg, neg_sub]
      have := P.kdiff_holder hT hq hqN hτ0 hτ α ht₂.1 h ht₁.2
      linarith
  refine (Summable.tsum_le_tsum hk (Summable.of_nonneg_of_le (fun α => sq_nonneg _) hk hs2) hs2).trans (le_of_eq ?_)
  rw [tsum_mul_right, tsum_mul_left]

theorem S57pPairBd.noise_sup (P : S57pPairBd θ T n K KN s M Q ν νN c cN ρ ρN A Λc νbar m J Ca CaN Cd CdN Cp1 Cp2 Dt)
    (hT : 0 < T) {q qN τ : ℝ} (hq : 0 ≤ q) (hqN : 0 ≤ qN) (hτ0 : 0 ≤ τ)
    (hτ : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ x : Euc d, ENNReal.ofReal |ρN r x - ρ r x| ≤ ENNReal.ofReal τ)
    (hsum : Summable fun α : MultiIndex d => oscEigenvalue d α ^ ((J : ℝ) - m))
    {Ω₀ : Type} [MeasurableSpace Ω₀] {Qm : Measure Ω₀} [IsProbabilityMeasure Qm]
    {W : Lp (Euc d) 2 (s57pμ d T) → Ω₀ → ℝ} (hI : Sb7Iso Qm W)
    (hlaw : ∀ g, Qm.map (W g) = gaussianReal 0 (Real.toNNReal (‖g‖ ^ 2)))
    {Mg : ℝ} (hM0 : 0 ≤ Mg)
    (hM : ∀ v : ℝ, 0 ≤ v → ∫⁻ y, ‖y‖ₑ ^ 4 ∂(gaussianReal 0 v.toNNReal) ≤ ENNReal.ofReal (Mg * v ^ 2))
    {X1 X2 : ℝ → Ω₀ → OscDual d m} (hX1m : ∀ t, Measurable (X1 t)) (hX2m : ∀ t, Measurable (X2 t))
    (hX1c : ∀ w, ContinuousOn (fun t => X1 t w) (Set.Icc 0 T)) (hX2c : ∀ w, ContinuousOn (fun t => X2 t w) (Set.Icc 0 T))
    (hX1a : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α, ∀ᵐ w ∂Qm, OscDual.coord (X1 t w) α =
      W (s57pκ (fixedEqCoeff s M Q νN cN ρN) T qN ρN t (oscTestFun m α)) w)
    (hX2a : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α, ∀ᵐ w ∂Qm, OscDual.coord (X2 t w) α =
      W (s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t (oscTestFun m α)) w) :
    ∫⁻ w, (⨆ t : Set.Icc (0 : ℝ) T, ‖X1 t w - X2 t w‖ₑ) ^ 4 ∂Qm ≤
      ENNReal.ofReal (s57pC0 T * (Mg * ((3 * s57pCz T q qN τ CaN CdN Cp1 Cp2 Dt *
        ∑' α : MultiIndex d, oscEigenvalue d α ^ ((J : ℝ) - m)) ^ 2))) := by
  have hT0 : 0 ≤ T := hT.le
  set Kz : ℝ := 3 * s57pCz T q qN τ CaN CdN Cp1 Cp2 Dt * ∑' α : MultiIndex d, oscEigenvalue d α ^ ((J : ℝ) - m) with hKz
  have h00 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT0⟩
  have hs1 := (s57p_kappa_hs P.FxN P.hbdN P.hCaN P.hCdN hqN hsum).1
  have hs2 := (s57p_kappa_hs P.Fx P.hbd P.hCa P.hCd hq hsum).1
  have hKz0 : 0 ≤ Kz := by
    have := P.hCaN; have := P.hCdN; have := P.hCp1; have := P.hCp2; have := P.hDt
    have hS0 : 0 ≤ ∑' α : MultiIndex d, oscEigenvalue d α ^ ((J : ℝ) - m) :=
      tsum_nonneg fun α => (Real.rpow_pos_of_pos (oscEv_pos α) _).le
    rw [hKz]; unfold s57pCz; positivity
  have hmom : ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ w, ‖(X1 t w - X2 t w) - (X1 s' w - X2 s' w)‖ₑ ^ 4 ∂Qm ≤
      ENNReal.ofReal ((Mg * Kz ^ 2) * |t - s'| ^ 2) := by
    intro s' hs' t ht
    refine (s57p_diff_moment hI hlaw hM0 hM hX1a hX2a hs1 hs2 hs' ht).trans (ENNReal.ofReal_le_ofReal ?_)
    have h := P.kdiff_hs hT0 hq hqN hτ0 hτ hsum hs' ht
    have h0 : 0 ≤ ∑' α : MultiIndex d, ‖(s57pκ (fixedEqCoeff s M Q νN cN ρN) T qN ρN t (oscTestFun m α) -
        s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t (oscTestFun m α)) -
      (s57pκ (fixedEqCoeff s M Q νN cN ρN) T qN ρN s' (oscTestFun m α) -
        s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ s' (oscTestFun m α))‖ ^ 2 := tsum_nonneg fun α => sq_nonneg _
    have h2 := pow_le_pow_left₀ h0 h 2
    calc Mg * (∑' α : MultiIndex d, ‖(s57pκ (fixedEqCoeff s M Q νN cN ρN) T qN ρN t (oscTestFun m α) -
        s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t (oscTestFun m α)) -
      (s57pκ (fixedEqCoeff s M Q νN cN ρN) T qN ρN s' (oscTestFun m α) -
        s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ s' (oscTestFun m α))‖ ^ 2) ^ 2
        ≤ Mg * (Kz * |t - s'|) ^ 2 := mul_le_mul_of_nonneg_left h2 hM0
      _ = (Mg * Kz ^ 2) * |t - s'| ^ 2 := by ring
  have hsup := s57p_sup_moment Qm (Z := fun t w => X1 t w - X2 t w) hT (A := Mg * Kz ^ 2) (by positivity)
    (fun t => (hX1m t).sub (hX2m t)) (fun w => (hX1c w).sub (hX2c w)) hmom
  have z1 := s57p_noise_zero hI h00 hX1a (fun α => by unfold s57pκ; exact s57p_el_zero _ _)
  have z2 := s57p_noise_zero hI h00 hX2a (fun α => by unfold s57pκ; exact s57p_el_zero _ _)
  refine le_trans (le_of_eq (lintegral_congr_ae ?_)) hsup
  filter_upwards [z1, z2] with w a b
  simp only [a, b, sub_zero]

end HRS.MS.FixEq
