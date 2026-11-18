import HRS.MS.WsPrepM2

/-!
# S21S packet M3: the mild identity of the moving window and the window remainder

Moving analogues of `s105_mild_coord`, `s105_R_cont`, `s105_R_coord`, `s105_R_bound_dense` (R2GenInitAux26/29/40).  For a moving mean-field trajectory `ρ`
(`S21mData`, in particular `MFData` for the quadratic dynamics), the duality identity `s56_duality_core` with the test `f_r = U^{r,b+u} φ_α` gives, at the
window time `b+u`, the Duhamel identity

`coord_α σ(μ_N^{b+u} - ρ_{b+u}) = σ(μ_N^0 - ρ_0)(U^{0,b+u}φ_α) + coord_α (𝒯M)(u) + σ ∫_0^{b+u} flucInteractionRd (U^{r,b+u}φ_α) (X_r) (ρ_r) dr`.

`s21mR` is the window remainder `Ξ - A(k₀) - 𝒯M`; `s21m_R_coord` computes its coordinates, `s21m_R_bound_dense` bounds it by the moving-reference forcing
`-(σ/2) ∫_0^{b+u} r2CommForcingMov` along a dense sequence of window times.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S21m

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.GenPath HRS.MS.S52 HRS.MP.RdRem HRS.MH.DualityRd HRS.MS.R2GenInit
  HRS.Uniform.Q54c HRS.GF

variable {d : ℕ}

/-- The fluctuation field `Ξ_t = σ(μ_N^t - ρ_t dx) ∈ B_m` about the moving reference. -/
def s21mXi (m σ : ℝ) (ρ : ℝ → Euc d → ℝ) {N : ℕ} {Ω : Type*} (X : ℝ≥0 → Ω → EucConfig d N) (t : ℝ) (ζ : Ω) :
    OscDual d m :=
  σ • OscDual.ofMeasureDiff m (HRS.Whole.empirical (X (Real.toNNReal t) ζ)) (HRS.Whole.withDensityReal (ρ t))

/-- The window remainder. -/
def s21mR (C : WholeCoeff d) (m T b σ : ℝ) (ρ : ℝ → Euc d → ℝ) {N : ℕ} {Ω : Type*}
    (X : ℝ≥0 → Ω → EucConfig d N) (M : ℝ → Ω → KSpace d m T) (u : ℝ) (ζ : Ω) : OscDual d m :=
  s21mXi m σ ρ X (b + u) ζ - (s105K0 C m T b σ (ρ 0) X ζ).evalA u -
    reconstructPath m T (fun τ ζ => M (b + τ) ζ) ζ u

theorem s21m_fluc_eq {m σ : ℝ} {T b : ℝ} {N : ℕ} {Ω : Type*} (X : ℝ≥0 → Ω → EucConfig d N)
    (ρ : ℝ → Euc d → ℝ) (ζ : Ω) :
    flucPathW m T b σ X ρ ζ = windowPathOf m T 0 (fun u => s21mXi m σ ρ X (b + u) ζ) := by
  unfold flucPathW windowPathOf s21mXi
  exact HRS.GF.dite_continuousMap_congr _ _ (funext fun t => by simp)

theorem s21m_mild_coord (hd : 2 ≤ d) {s : ℝ} {a β : ℝ} (hβ : 0 < β)
    {T b : ℝ} (hb : 0 ≤ b) (hT : 0 < T) {ρ : ℝ → Euc d → ℝ} (hS : S21mData d s a β T b ρ) {N : ℕ} (hN : 1 ≤ N)
    (C : WholeCoeff d) (hCdef : C = (quadraticGradientDyn d s a β).coeff ρ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P (quadraticGradientDyn d s a β) (b + T) X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (Mm : ℝ → Ω → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T)
    (hΦ : ∀ T' : ℝ, IsHSIntegrand P ℱ T' (s105Phi (fun a' r x => r2WindowFeature C
      ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b r x) (b + T) β⁻¹ X))
    (hM : IsHilbertItoIntegral P ℱ W' (s105Phi (fun a' r x => r2WindowFeature C
      ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b r x) (b + T) β⁻¹ X) Mm)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) (α : MultiIndex d) :
    ∀ᵐ ζ ∂P,
      OscDual.coord (Real.sqrt N • OscDual.ofMeasureDiff ((wholeSpaceIndex d : ℕ) : ℝ)
          (HRS.Whole.empirical (X (Real.toNNReal (b + u)) ζ)) (HRS.Whole.withDensityReal (ρ (b + u)))) α =
        Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical (X 0 ζ))
            (propagatorW C 0 (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) -
          HRS.Whole.pair (HRS.Whole.withDensityReal (ρ 0))
            (propagatorW C 0 (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) +
        OscDual.coord (reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => Mm (b + τ) ζ) ζ u) α +
        Real.sqrt N * ∫ r in Set.Icc (0 : ℝ) (b + u), HRS.Whole.AppendixA.flucInteractionRd
          (quadraticGradientDyn d s a β)
          (propagatorW C r (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) (X (Real.toNNReal r) ζ) (ρ r) := by
  subst hCdef
  have hm : (d : ℝ) < ((wholeSpaceIndex d : ℕ) : ℝ) := by
    unfold wholeSpaceIndex; push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have ht0 : 0 ≤ b + u := by linarith [hu.1]
  have htτ : b + u ≤ b + T := by linarith [hu.2]
  have hτ : 0 < b + T := by linarith
  have ht : b + u ∈ Set.Icc (0 : ℝ) (b + T) := ⟨ht0, htτ⟩
  have hcl_t := hS.hcl α (b + u) ht0
  obtain ⟨Λ, ΛV, G₀, hMF⟩ := hS.hM
  have hdual := s56_duality_core s Λ (b + T) ΛV G₀ (quadraticGradientDyn d s a β) hMF.hs hMF.hs0 hMF.hsd
    hMF.hinv hMF.hV ρ hMF.hρ hMF.hreg P X₀ W X hX ℱ W' hF (b + u) ht _ _ hcl_t
  have hW : IsCylindricalBrownian P ℱ W' := HRS.GF.gfb3_isCylindricalBrownian_of_filtration hF.brownian
  have hid := s105_ident ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T b β⁻¹ N P ℱ W' X Mm hN hb hT.le hW hΦ hM
    hS.hC hS.hK u hu α
  have hprog := HRS.MH.DualityRd.isProgressiveL2_truncGrad_proof (P := P) ht0 hcl_t.isC12TestRd hF.progressive
  have hsm := HRS.itoIntegral_smul hF.brownian hprog (Real.sqrt (2 * β⁻¹ / N))
  have hψ : (fun (r : ℝ) (ζ' : Ω) (ia : Fin N × Fin d) => if r ∈ Set.Icc (0 : ℝ) (b + u) then
      Real.sqrt (2 * β⁻¹ / N) * gradComp ia.2 (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r (b + u)
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) (X (Real.toNNReal r) ζ' ia.1) else 0) =
      fun t' z => Real.sqrt (2 * β⁻¹ / N) • HRS.MH.DualityRd.truncGradIntegrand (b + u)
        (fun r => propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) X t' z := by
    funext r ζ' ia
    by_cases hr : r ∈ Set.Icc (0 : ℝ) (b + u) <;> simp [HRS.MH.DualityRd.truncGradIntegrand, hr]
  filter_upwards [hdual, hid, hsm] with ζ hd' hi hs'
  obtain ⟨-, heq⟩ := hd' (b + u) ⟨ht0, le_rfl⟩
  rw [hψ] at hi
  rw [hi, hs' (b + u)]
  have hterm : propagatorW ((quadraticGradientDyn d s a β).coeff ρ) (b + u) (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) =
      oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α := hcl_t.terminal
  haveI : IsProbabilityMeasure (HRS.Whole.empirical (X (Real.toNNReal (b + u)) ζ)) :=
    HRS.Whole.empirical_isProbabilityMeasure (by omega) _
  haveI := HRS.MS.Thm.cb_withDensityReal_isProb (hS.hprob ht)
  rw [OscDual.coord_smul, s56_coord_ofMeasureDiff hm]
  have heq' : HRS.Whole.pair (HRS.Whole.empirical (X (Real.toNNReal (b + u)) ζ))
        (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) (b + u) (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) -
      HRS.Whole.pair (HRS.Whole.withDensityReal (ρ (b + u)))
        (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) (b + u) (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) =
      (HRS.Whole.pair (HRS.Whole.empirical (X 0 ζ))
          (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) -
        HRS.Whole.pair (HRS.Whole.withDensityReal (ρ 0))
          (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))) +
      (Real.sqrt (2 * β⁻¹) / N) * itoIntegral P ℱ W' (fun r ζ' (ia : Fin N × Fin d) =>
        if r ∈ Set.Icc (0 : ℝ) (b + u) then gradComp ia.2
          (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))
          (X (Real.toNNReal r) ζ' ia.1) else 0) (b + u) ζ +
      ∫ r in Set.Icc (0 : ℝ) (b + u), HRS.Whole.AppendixA.flucInteractionRd (quadraticGradientDyn d s a β)
        (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))
        (X (Real.toNNReal r) ζ) (ρ r) := heq
  rw [hterm] at heq'
  have e1 : ∫ x, oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α x ∂(HRS.Whole.empirical (X (Real.toNNReal (b + u)) ζ)) =
      HRS.Whole.pair (HRS.Whole.empirical (X (Real.toNNReal (b + u)) ζ)) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) := rfl
  have e2 : ∫ x, oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α x ∂(HRS.Whole.withDensityReal (ρ (b + u))) =
      HRS.Whole.pair (HRS.Whole.withDensityReal (ρ (b + u))) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) := rfl
  rw [e1, e2, s105_sqrt_q (by omega : 0 < N) (inv_nonneg.2 hβ.le)]
  have := congrArg (fun z => Real.sqrt N * z) heq'
  have hT' : itoIntegral P ℱ W' (HRS.MH.DualityRd.truncGradIntegrand (b + u)
      (fun r => propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) X) (b + u) ζ =
      itoIntegral P ℱ W' (fun r ζ' (ia : Fin N × Fin d) => if r ∈ Set.Icc (0 : ℝ) (b + u) then
        gradComp ia.2 (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r (b + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α))
          (X (Real.toNNReal r) ζ' ia.1) else 0) (b + u) ζ := rfl
  rw [hT']
  linear_combination this

theorem s21m_R_cont (hd1 : 1 ≤ d) {s a β T b : ℝ} (hT : 0 ≤ T) (hb : 0 ≤ b) {ρ : ℝ → Euc d → ℝ}
    (hS : S21mData d s a β T b ρ) {N : ℕ} (hN : 1 ≤ N) (σ : ℝ)
    (hm : (d : ℝ) < ((wholeSpaceIndex d : ℕ) : ℝ)) {Ω : Type*} (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω)
    (hXc : ∀ i, Continuous fun t : ℝ≥0 => X t ζ i)
    (M : ℝ → Ω → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T)
    (hMc : ContinuousOn (fun t => M t ζ) (Set.Icc 0 (b + T))) :
    ContinuousOn (fun u => s21mR ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) T b σ ρ X M u ζ) (Set.Icc (0 : ℝ) T) := by
  unfold s21mR s21mXi
  have hxi : ContinuousOn (fun t => σ • OscDual.ofMeasureDiff ((wholeSpaceIndex d : ℕ) : ℝ)
      (HRS.Whole.empirical (X (Real.toNNReal t) ζ)) (HRS.Whole.withDensityReal (ρ t))) (Set.Icc (0 : ℝ) (b + T)) :=
    s56_xi_cont_time hd1 hm σ (by omega : 0 < N) (T := b + T) ρ (fun t ht => hS.hprob ht) hS.hcont
      (fun t => X (Real.toNNReal t) ζ) (fun i => (hXc i).comp continuous_real_toNNReal)
  have hxi' : ContinuousOn (fun u => σ • OscDual.ofMeasureDiff ((wholeSpaceIndex d : ℕ) : ℝ)
      (HRS.Whole.empirical (X (Real.toNNReal (b + u)) ζ)) (HRS.Whole.withDensityReal (ρ (b + u)))) (Set.Icc (0 : ℝ) T) :=
    hxi.comp (by fun_prop) (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  have hshift : ContinuousOn (fun τ => M (b + τ) ζ) (Set.Icc 0 T) :=
    hMc.comp (by fun_prop) (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  exact (hxi'.sub (HRS.MS.U9.u9_continuousOn_evalA hT _)).sub
    (continuousOn_iff_continuous_restrict.2 (HRS.MS.U9.u9_continuous_recon hT (fun τ ζ => M (b + τ) ζ) ζ hshift))

theorem s21m_R_coord (hd : 2 ≤ d) {s a β : ℝ} (hβ : 0 < β) {T b : ℝ} (hb : 0 ≤ b) (hT : 0 < T)
    {ρ : ℝ → Euc d → ℝ} (hS : S21mData d s a β T b ρ) {N : ℕ} (hN : 1 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P (quadraticGradientDyn d s a β) (b + T) X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (Mm : ℝ → Ω → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T)
    (hΦ : ∀ T' : ℝ, IsHSIntegrand P ℱ T' (s105Phi (fun a' r x => r2WindowFeature
      ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b r x)
      (b + T) β⁻¹ X))
    (hM : IsHilbertItoIntegral P ℱ W' (s105Phi (fun a' r x => r2WindowFeature
      ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b r x)
      (b + T) β⁻¹ X) Mm)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) (α : MultiIndex d) :
    ∀ᵐ ζ ∂P, OscDual.coord (s21mR ((quadraticGradientDyn d s a β).coeff ρ)
        ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm u ζ) α =
      Real.sqrt N * ∫ r in Set.Icc (0 : ℝ) (b + u), flucInteractionRd (quadraticGradientDyn d s a β)
        (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r (b + u)
          (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) (X (Real.toNNReal r) ζ) (ρ r) := by
  have hτ : 0 ≤ b + T := by linarith
  filter_upwards [s21m_mild_coord hd hβ hb hT hS hN _ rfl P X₀ W X hX ℱ W' hF Mm hΦ hM hu α] with ζ h
  unfold s21mR s21mXi s105K0
  rw [s56_coord_sub, s56_coord_sub, s105_k0_eval _ hb rfl hS.hC (Real.sqrt N) (hS.hprob ⟨le_rfl, hτ⟩) hS.hρ2 hN
    (X 0 ζ) hu α hS.hF (fun a' z => hS.hK a' 0 ⟨le_rfl, by linarith [hu.1, hu.2]⟩ z)
    (hS.hcl α (b + u) (by linarith [hu.1]))]
  linarith

theorem s21m_R_bound_dense (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (hβ : 0 < β)
    {T b : ℝ} (hb : 0 ≤ b) (hT : 0 < T) {ρ : ℝ → Euc d → ℝ} (hS : S21mData d s a β T b ρ) {N : ℕ} (hN : 1 ≤ N)
    (hm : (d : ℝ) < ((wholeSpaceIndex d : ℕ) : ℝ))
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P (quadraticGradientDyn d s a β) (b + T) X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (Mm : ℝ → Ω → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T)
    (hΦ : ∀ T' : ℝ, IsHSIntegrand P ℱ T' (s105Phi (fun a' r x => r2WindowFeature
      ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b r x)
      (b + T) β⁻¹ X))
    (hM : IsHilbertItoIntegral P ℱ W' (s105Phi (fun a' r x => r2WindowFeature
      ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b r x)
      (b + T) β⁻¹ X) Mm)
    (s' : ℕ → Set.Icc (0 : ℝ) T) (hs' : DenseRange s') :
    ∀ᵐ ζ ∂P, ∀ u ∈ Set.Icc (0 : ℝ) T, ‖s21mR ((quadraticGradientDyn d s a β).coeff ρ)
        ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm u ζ‖ₑ ≤
      ⨆ n : ℕ, l2NormE (fun α : MultiIndex d =>
        -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + (s' n)), r2CommForcingMov
          ((quadraticGradientDyn d s a β).coeff ρ) s ((wholeSpaceIndex d : ℕ) : ℝ) ρ X α
          (b + (s' n)) r ζ) := by
  have hd1 : 1 ≤ d := by omega
  have hq : ∀ᵐ ζ ∂P, ∀ n : ℕ, ∀ α : MultiIndex d, OscDual.coord (s21mR ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm (s' n) ζ) α =
      -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + (s' n)), r2CommForcingMov
          ((quadraticGradientDyn d s a β).coeff ρ) s ((wholeSpaceIndex d : ℕ) : ℝ) ρ X α
          (b + (s' n)) r ζ := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro α
    filter_upwards [s21m_R_coord hd hβ hb hT hS hN P X₀ W X hX ℱ W' hF Mm hΦ hM (s' n).2 α] with ζ h
    rw [h]
    have hcl := hS.hcl α (b + s' n) (by linarith [(s' n).2.1])
    have hmem : ∀ r ∈ Set.Icc (0 : ℝ) (b + s' n), MemCb 2 (propagatorW
        ((quadraticGradientDyn d s a β).coeff ρ) r (b + s' n)
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) := fun r hr =>
      s105_memCb_at hcl hr
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    have hrT : r ∈ Set.Icc (0 : ℝ) (b + T) := ⟨hr.1, hr.2.trans (by linarith [(s' n).2.2])⟩
    rw [s105_fluc_eq_forcing hd1 hs0 hsd a β (hS.regSlice hrT) (hmem r hr) (X (Real.toNNReal r) ζ)]
    unfold r2CommForcingMov
    ring
  filter_upwards [hq, hX.cont] with ζ hq1 hXc
  set L : ℝ≥0∞ := ⨆ n : ℕ, l2NormE (fun α : MultiIndex d =>
        -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + (s' n)), r2CommForcingMov
          ((quadraticGradientDyn d s a β).coeff ρ) s ((wholeSpaceIndex d : ℕ) : ℝ) ρ X α
          (b + (s' n)) r ζ) with hL
  have hRc := s21m_R_cont hd1 hT.le hb hS hN (Real.sqrt N) hm X ζ hXc Mm (hM.cont ζ).continuousOn
  have hcont : Continuous fun u : Set.Icc (0 : ℝ) T => s21mR ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm u ζ :=
    continuousOn_iff_continuous_domRestrict.1 hRc
  have hclosed : IsClosed {u : Set.Icc (0 : ℝ) T | ‖s21mR ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm u ζ‖ₑ ≤ L} :=
    isClosed_le (continuous_enorm.comp hcont) continuous_const
  have key : ∀ t0 : Set.Icc (0 : ℝ) T, ‖s21mR ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm t0 ζ‖ₑ ≤ L := fun t0 =>
    hs'.induction_on t0 hclosed (fun n => by
      show ‖s21mR ((quadraticGradientDyn d s a β).coeff ρ)
        ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm (s' n) ζ‖ₑ ≤ L
      rw [s56_enorm_eq_l2NormE]
      have : (fun α => OscDual.coord (s21mR ((quadraticGradientDyn d s a β).coeff ρ)
        ((wholeSpaceIndex d : ℕ) : ℝ) T b (Real.sqrt N) ρ X Mm (s' n) ζ) α) = _ := funext (hq1 n)
      rw [this]
      exact le_iSup (fun n : ℕ => l2NormE (fun α : MultiIndex d =>
        -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (b + (s' n)), r2CommForcingMov
          ((quadraticGradientDyn d s a β).coeff ρ) s ((wholeSpaceIndex d : ℕ) : ℝ) ρ X α
          (b + (s' n)) r ζ)) n)
  intro u hu
  exact key ⟨u, hu⟩

end HRS.MS.S21m
