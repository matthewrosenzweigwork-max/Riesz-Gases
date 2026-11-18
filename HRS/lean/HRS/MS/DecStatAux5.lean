import HRS.MS.DecStatAux4

/-!
# SA4, packet 5: the covariance cost with the test bound `Sa4Test` (copies of `sa2_cov_pt`, `sa2_cov_cost_gen`, `sa2_cov_cost`,
`sa2_covH` of the S.A.2 engine; the hypotheses `cbNorm 2`, `ulocNormE 2` on the orbit are replaced by `cbNorm m_*` only)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF HRS.Whole.AppendixALemmas HRS.MS.MainRdStat
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.DecStat

variable {d : ℕ}

section CovCost

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ}
  {𝔈 : ℕ → ℝ}

theorem sa4_cov_pt (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N)
    {χ : Euc d → ℝ} {C₀c Ct : ℝ} (hTest : Sa4Test d S.s χ C₀c Ct) (hCt : 0 ≤ Ct) {q : ℕ}
    (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Euc d → ℝ) {B : Fin q → ℝ}
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb (mStar d) (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm (mStar d) (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a)
    (w : (R N).Ω) (a b : Fin q) {rr : ℝ} (hrr : 0 ≤ rr ∧ rr < min (ts a) (ts b))
    (hinj : Function.Injective ((R N).X (Real.toNNReal rr) w)) (R₁ : ℝ) (hR₁ : 1 ≤ R₁) :
    |(sa2Sg S R N ts φ rr w - sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N) rr) a b| ≤
      2 * S.qN N * (Ct * B a * B b) * (R₁ ^ ((d : ℝ) / 2) * (smearScale d N (max Λ 1) +
        Real.sqrt (sa2En S R N C₀c Λ w rr)) + sa2M2 S R N w rr / R₁ ^ 2) := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < N := by omega
  have h1 : rr ∈ Set.Icc (0 : ℝ) (ts a) := ⟨hrr.1, (hrr.2.trans_le (min_le_left _ _)).le⟩
  have h2 : rr ∈ Set.Icc (0 : ℝ) (ts b) := ⟨hrr.1, (hrr.2.trans_le (min_le_right _ _)).le⟩
  have hrT : rr ∈ Set.Icc (0 : ℝ) S.T := ⟨hrr.1, (h1.2.trans (hts a).2)⟩
  have hq := sa2_q_nonneg S N
  have hclamp : HRS.MP.RdRem.mrrClamp S.T rr = rr := HRS.MP.RdRem.mrrClamp_of_mem hrT
  set h : Euc d → ℝ := fun x => ∑ j, sa2U S N ts φ a j rr x * sa2U S N ts φ b j rr x with hh
  have hheq : h = sa2h (propagatorW (S.coeff N) rr (ts a) (φ a)) (propagatorW (S.coeff N) rr (ts b) (φ b)) := by
    funext x
    simp only [hh, sa2U, if_pos h1, if_pos h2, sa2h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [HRS.MP.RdMart.mrm_grad_component, HRS.MP.RdMart.mrm_grad_component]
  have hsb : sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N) rr a b =
      2 * S.qN N * HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N rr)) h := by
    unfold sa2SigBar
    simp only [Matrix.of_apply, if_pos hrr]
    congr 1
    unfold HRS.Whole.pair
    have hprob := (hS.mean_field.solution N hN1).density rr hrT
    rw [HRS.MP.RdRem.mrr_integral_withDensityReal _ hprob.measurable hprob.nonneg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [sa2Rho, hclamp, hh]
    ring
  have hdiff : (sa2Sg S R N ts φ rr w - sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N) rr) a b =
      2 * S.qN N * (HRS.Whole.pair (HRS.Whole.empirical ((R N).X (Real.toNNReal rr) w)) h -
        HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N rr)) h) := by
    rw [Matrix.sub_apply, sa2_Sg_entry hN0 ts φ w a b hrr, hsb]
    ring
  rw [hdiff, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * S.qN N), hheq]
  have hprob := (hS.mean_field.solution N hN1).density rr hrT
  have hρΛ : ∀ x, S.ρ N rr x ≤ max Λ 1 := fun x => (sa2_rho_le hS hN1 hrT x).trans (le_max_left _ _)
  have hBa : 0 ≤ B a := (sa2_cbNorm_nonneg (mStar d) _).trans (hB a rr h1).2
  have hBb : 0 ≤ B b := (sa2_cbNorm_nonneg (mStar d) _).trans (hB b rr h2).2
  have key := hTest (max Λ 1) (le_max_right _ _) N hN (S.ρ N rr) hprob hρΛ
    ((hS.mean_field.solution N hN1).second_moment rr hrT) ((R N).X (Real.toNNReal rr) w) hinj _ _
    (hB a rr h1).1 (hB b rr h2).1 (B a) (B b) hBa hBb (hB a rr h1).2 (hB b rr h2).2 R₁ hR₁
  have hen : sa2En S R N C₀c Λ w rr = rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal rr) w)
      (HRS.Whole.withDensityReal (S.ρ N rr)) + oNΛ d S.s C₀c (max Λ 1) N := by
    simp only [sa2En, hclamp]
  have hm2 : sa2M2 S R N w rr = secondMomentOf (HRS.Whole.empirical ((R N).X (Real.toNNReal rr) w)) +
      secondMomentOf (HRS.Whole.withDensityReal (S.ρ N rr)) := by
    simp only [sa2M2, hclamp]
  rw [hen, hm2]
  calc 2 * S.qN N * |HRS.Whole.pair (HRS.Whole.empirical ((R N).X (Real.toNNReal rr) w))
        (sa2h (propagatorW (S.coeff N) rr (ts a) (φ a)) (propagatorW (S.coeff N) rr (ts b) (φ b))) -
        HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N rr))
          (sa2h (propagatorW (S.coeff N) rr (ts a) (φ a)) (propagatorW (S.coeff N) rr (ts b) (φ b)))|
      ≤ 2 * S.qN N * (Ct * B a * B b * (R₁ ^ ((d : ℝ) / 2) * (smearScale d N (max Λ 1) +
          Real.sqrt (rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal rr) w)
            (HRS.Whole.withDensityReal (S.ρ N rr)) + oNΛ d S.s C₀c (max Λ 1) N)) +
          (secondMomentOf (HRS.Whole.empirical ((R N).X (Real.toNNReal rr) w)) +
            secondMomentOf (HRS.Whole.withDensityReal (S.ρ N rr))) / R₁ ^ 2)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring


theorem sa4_cov_cost_gen (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} (hprog : IsProgressive ℱ (ofNNRealTime (R N).X))
    {χ : Euc d → ℝ} {C₀c Ct : ℝ} (hTest : Sa4Test d S.s χ C₀c Ct) (hCt : 0 ≤ Ct) (hC₀c : 0 ≤ C₀c)
    (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T)
    (φ : Fin q → Euc d → ℝ) {B : Fin q → ℝ} (hB0 : ∀ a, 0 ≤ B a)
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb (mStar d) (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm (mStar d) (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a)
    (hinj : ∀ᵐ w ∂(R N).P, ∀ᵐ rr ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal rr) w))
    {m₂ : ℝ} (hm₂ : 0 ≤ m₂) (hmom : PropagatedSecondMoment S R m₂)
    (F : ℝ → (R N).Ω → ℝ) (hF0 : ∀ σ w, 0 ≤ F σ w)
    (hFle : ∀ σ w, F σ w ≤ ∑ a, ∑ b, |(sa2Sg S R N ts φ σ w -
      sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N) σ) a b|) :
    ∫ w, (∫ σ in Set.Icc (0 : ℝ) S.T, F σ w) ∂(R N).P ≤
      2 * S.qN N * Ct * (∑ a, B a) ^ 2 * S.T * wN d N (𝔈 N) m₂ := by
  have hN1 : 1 ≤ N := by omega
  have hT0 : 0 ≤ S.T := S.hT.le
  have h𝔈 : 0 ≤ 𝔈 N := (hS.energy.pos N hN1).le
  have hq := sa2_q_nonneg S N
  set K0 : ℝ := 2 * S.qN N * Ct * (∑ a, B a) ^ 2 with hK0def
  have hK0 : 0 ≤ K0 := by
    have : 0 ≤ ∑ a, B a := Finset.sum_nonneg fun a _ => hB0 a
    positivity
  -- the energy and second-moment slices
  obtain ⟨hs1, hI1, hE1⟩ := sa2_E1 hS hd hN hprog hC₀c hC₀
  obtain ⟨hs2, hI2, hE2⟩ := sa2_E2 hS hN hprog hm₂ hmom
  have hF10 : ∀ w σ, 0 ≤ sa2F1 S R N C₀c Λ w σ := fun w σ => Real.sqrt_nonneg _
  have hF20 : ∀ w σ, 0 ≤ sa2M2 S R N w σ := fun w σ =>
    add_nonneg (HRS.Whole.Q09A.secondMomentOf_nonneg _) (HRS.Whole.Q09A.secondMomentOf_nonneg _)
  set lam : ℝ := smearScale d N (max Λ 1) with hlam
  have hΛ1 : 1 ≤ max Λ 1 := le_max_right _ _
  have hN0r : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam0 : 0 ≤ lam := by
    rw [hlam]; unfold smearScale
    exact Real.rpow_nonneg (by positivity) _
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hlam1 : lam ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := by
    rw [hlam]; unfold smearScale
    refine Real.rpow_le_rpow_of_nonpos hN0r ?_ (by
      have : (0 : ℝ) ≤ 1 / d := by positivity
      have e : -(1 : ℝ) / d = -(1 / d) := by ring
      rw [e]; linarith)
    nlinarith
  -- the bound for each `R₁ ≥ 1`
  have main : ∀ R₁ : ℝ, 1 ≤ R₁ → ∫ w, (∫ σ in Set.Icc (0 : ℝ) S.T, F σ w) ∂(R N).P ≤
      K0 * S.T * (R₁ ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 : ℝ) / d) + (𝔈 N) ^ ((1 : ℝ) / 2)) + m₂ / R₁ ^ 2) := by
    intro R₁ hR₁
    have hR0 : 0 < R₁ := by linarith
    have hP0 : 0 ≤ R₁ ^ ((d : ℝ) / 2) := Real.rpow_nonneg hR0.le _
    set Pt : (R N).Ω → ℝ → ℝ := fun w σ => K0 * (R₁ ^ ((d : ℝ) / 2) * (lam + sa2F1 S R N C₀c Λ w σ) + sa2M2 S R N w σ / R₁ ^ 2) with hPt
    have hPt0 : ∀ w σ, 0 ≤ Pt w σ := fun w σ => by
      have := hF10 w σ; have := hF20 w σ
      simp only [hPt]; positivity
    -- pointwise domination
    have hdom : ∀ᵐ w ∂(R N).P, ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
        F σ w ≤ Pt w σ := by
      filter_upwards [hinj] with w hw
      filter_upwards [hw] with σ hσ
      refine (hFle σ w).trans ?_
      have hterm : 0 ≤ R₁ ^ ((d : ℝ) / 2) * (lam + sa2F1 S R N C₀c Λ w σ) + sa2M2 S R N w σ / R₁ ^ 2 := by
        have := hF10 w σ; have := hF20 w σ; positivity
      calc ∑ a, ∑ b, |(sa2Sg S R N ts φ σ w -
            sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N) σ) a b|
          ≤ ∑ a, ∑ b, 2 * S.qN N * (Ct * B a * B b) *
              (R₁ ^ ((d : ℝ) / 2) * (lam + sa2F1 S R N C₀c Λ w σ) + sa2M2 S R N w σ / R₁ ^ 2) := by
            refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
            by_cases hab : 0 ≤ σ ∧ σ < min (ts a) (ts b)
            · exact sa4_cov_pt hS hd hN hTest hCt ts hts φ hB w a b hab hσ R₁ hR₁
            · have h0 : (sa2Sg S R N ts φ σ w -
                  sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N) σ) a b = 0 := by
                rw [Matrix.sub_apply, sa2_Sg_entry_zero ts φ w a b hab]
                simp only [sa2SigBar, Matrix.of_apply, if_neg hab, sub_self]
              rw [h0, abs_zero]
              have := hB0 a; have := hB0 b
              positivity
        _ = Pt w σ := by
            have hsum : ∑ a, ∑ b, 2 * S.qN N * (Ct * B a * B b) = 2 * S.qN N * Ct * (∑ a, B a) ^ 2 := by
              rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun b _ => ?_
              ring
            simp_rw [← Finset.sum_mul]
            rw [hsum]
    -- integrability of the slices of the bound
    have hc : IntegrableOn (fun _ : ℝ => lam) (Set.Icc (0 : ℝ) S.T) := integrableOn_const (by simp)
    have hPtI : ∀ᵐ w ∂(R N).P, IntegrableOn (Pt w) (Set.Icc (0 : ℝ) S.T) := by
      filter_upwards [hs1, hs2] with w h1 h2
      have hA : IntegrableOn (fun σ => lam + sa2F1 S R N C₀c Λ w σ) (Set.Icc (0 : ℝ) S.T) := hc.add h1
      have hB : IntegrableOn (fun σ => R₁ ^ ((d : ℝ) / 2) * (lam + sa2F1 S R N C₀c Λ w σ)) (Set.Icc (0 : ℝ) S.T) :=
        hA.const_mul _
      have hC : IntegrableOn (fun σ => sa2M2 S R N w σ / R₁ ^ 2) (Set.Icc (0 : ℝ) S.T) := h2.div_const _
      have hD : IntegrableOn (fun σ => R₁ ^ ((d : ℝ) / 2) * (lam + sa2F1 S R N C₀c Λ w σ) + sa2M2 S R N w σ / R₁ ^ 2)
          (Set.Icc (0 : ℝ) S.T) := hB.add hC
      exact hD.const_mul K0
    have hPtEq : ∀ᵐ w ∂(R N).P, ∫ σ in Set.Icc (0 : ℝ) S.T, Pt w σ =
        K0 * (R₁ ^ ((d : ℝ) / 2) * (lam * S.T + ∫ σ in Set.Icc (0 : ℝ) S.T, sa2F1 S R N C₀c Λ w σ) +
          (∫ σ in Set.Icc (0 : ℝ) S.T, sa2M2 S R N w σ) / R₁ ^ 2) := by
      filter_upwards [hs1, hs2] with w h1 h2
      have hA : IntegrableOn (fun σ => lam + sa2F1 S R N C₀c Λ w σ) (Set.Icc (0 : ℝ) S.T) := hc.add h1
      have hB : IntegrableOn (fun σ => R₁ ^ ((d : ℝ) / 2) * (lam + sa2F1 S R N C₀c Λ w σ)) (Set.Icc (0 : ℝ) S.T) :=
        hA.const_mul _
      have hC : IntegrableOn (fun σ => sa2M2 S R N w σ / R₁ ^ 2) (Set.Icc (0 : ℝ) S.T) := h2.div_const _
      have e1 : ∫ σ in Set.Icc (0 : ℝ) S.T, Pt w σ = K0 * ∫ σ in Set.Icc (0 : ℝ) S.T,
          (R₁ ^ ((d : ℝ) / 2) * (lam + sa2F1 S R N C₀c Λ w σ) + sa2M2 S R N w σ / R₁ ^ 2) := integral_const_mul _ _
      have e2 : ∫ σ in Set.Icc (0 : ℝ) S.T, (R₁ ^ ((d : ℝ) / 2) * (lam + sa2F1 S R N C₀c Λ w σ) + sa2M2 S R N w σ / R₁ ^ 2) =
          (∫ σ in Set.Icc (0 : ℝ) S.T, R₁ ^ ((d : ℝ) / 2) * (lam + sa2F1 S R N C₀c Λ w σ)) +
            ∫ σ in Set.Icc (0 : ℝ) S.T, sa2M2 S R N w σ / R₁ ^ 2 := integral_add hB hC
      have e3 : ∫ σ in Set.Icc (0 : ℝ) S.T, R₁ ^ ((d : ℝ) / 2) * (lam + sa2F1 S R N C₀c Λ w σ) =
          R₁ ^ ((d : ℝ) / 2) * (lam * S.T + ∫ σ in Set.Icc (0 : ℝ) S.T, sa2F1 S R N C₀c Λ w σ) := by
        rw [integral_const_mul]
        congr 1
        have : ∫ σ in Set.Icc (0 : ℝ) S.T, (lam + sa2F1 S R N C₀c Λ w σ) =
            (∫ σ in Set.Icc (0 : ℝ) S.T, lam) + ∫ σ in Set.Icc (0 : ℝ) S.T, sa2F1 S R N C₀c Λ w σ := integral_add hc h1
        rw [this]
        simp [Measure.real, Real.volume_Icc, hT0, mul_comm]
      have e4 : ∫ σ in Set.Icc (0 : ℝ) S.T, sa2M2 S R N w σ / R₁ ^ 2 =
          (∫ σ in Set.Icc (0 : ℝ) S.T, sa2M2 S R N w σ) / R₁ ^ 2 := integral_div _ _
      rw [e1, e2, e3, e4]
    -- the double integral
    have hJ1 : Integrable (fun w => lam * S.T + ∫ σ in Set.Icc (0 : ℝ) S.T, sa2F1 S R N C₀c Λ w σ) (R N).P :=
      (integrable_const _).add hI1
    have hJ2 : Integrable (fun w => R₁ ^ ((d : ℝ) / 2) * (lam * S.T + ∫ σ in Set.Icc (0 : ℝ) S.T, sa2F1 S R N C₀c Λ w σ))
        (R N).P := hJ1.const_mul _
    have hJ3 : Integrable (fun w => (∫ σ in Set.Icc (0 : ℝ) S.T, sa2M2 S R N w σ) / R₁ ^ 2) (R N).P :=
      hI2.div_const _
    have hJ4 : Integrable (fun w => R₁ ^ ((d : ℝ) / 2) * (lam * S.T + ∫ σ in Set.Icc (0 : ℝ) S.T, sa2F1 S R N C₀c Λ w σ) +
        (∫ σ in Set.Icc (0 : ℝ) S.T, sa2M2 S R N w σ) / R₁ ^ 2) (R N).P := hJ2.add hJ3
    have hg : Integrable (fun w => K0 * (R₁ ^ ((d : ℝ) / 2) * (lam * S.T + ∫ σ in Set.Icc (0 : ℝ) S.T, sa2F1 S R N C₀c Λ w σ) +
          (∫ σ in Set.Icc (0 : ℝ) S.T, sa2M2 S R N w σ) / R₁ ^ 2)) (R N).P := hJ4.const_mul K0
    have hint : ∫ w, K0 * (R₁ ^ ((d : ℝ) / 2) * (lam * S.T + ∫ σ in Set.Icc (0 : ℝ) S.T, sa2F1 S R N C₀c Λ w σ) +
          (∫ σ in Set.Icc (0 : ℝ) S.T, sa2M2 S R N w σ) / R₁ ^ 2) ∂(R N).P =
        K0 * (R₁ ^ ((d : ℝ) / 2) * (lam * S.T + ∫ w, (∫ σ in Set.Icc (0 : ℝ) S.T, sa2F1 S R N C₀c Λ w σ) ∂(R N).P) +
          (∫ w, (∫ σ in Set.Icc (0 : ℝ) S.T, sa2M2 S R N w σ) ∂(R N).P) / R₁ ^ 2) := by
      rw [integral_const_mul, integral_add hJ2 hJ3, integral_const_mul, integral_add (integrable_const _) hI1,
        integral_div]
      simp
    calc ∫ w, (∫ σ in Set.Icc (0 : ℝ) S.T, F σ w) ∂(R N).P
        ≤ ∫ w, K0 * (R₁ ^ ((d : ℝ) / 2) * (lam * S.T + ∫ σ in Set.Icc (0 : ℝ) S.T, sa2F1 S R N C₀c Λ w σ) +
            (∫ σ in Set.Icc (0 : ℝ) S.T, sa2M2 S R N w σ) / R₁ ^ 2) ∂(R N).P := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w =>
            setIntegral_nonneg measurableSet_Icc fun σ _ => hF0 σ w) hg ?_
          filter_upwards [hdom, hPtI, hPtEq] with w h1 h2 h3
          rw [← h3]
          exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun σ => hF0 σ w) h2 h1
      _ = K0 * (R₁ ^ ((d : ℝ) / 2) * (lam * S.T + ∫ w, (∫ σ in Set.Icc (0 : ℝ) S.T, sa2F1 S R N C₀c Λ w σ) ∂(R N).P) +
            (∫ w, (∫ σ in Set.Icc (0 : ℝ) S.T, sa2M2 S R N w σ) ∂(R N).P) / R₁ ^ 2) := hint
      _ ≤ K0 * (R₁ ^ ((d : ℝ) / 2) * (lam * S.T + S.T * Real.sqrt (𝔈 N)) + (S.T * m₂) / R₁ ^ 2) := by
          gcongr
      _ ≤ K0 * S.T * (R₁ ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 : ℝ) / d) + (𝔈 N) ^ ((1 : ℝ) / 2)) + m₂ / R₁ ^ 2) := by
          rw [Real.sqrt_eq_rpow]
          have h1 : lam * S.T ≤ (N : ℝ) ^ (-(1 : ℝ) / d) * S.T := mul_le_mul_of_nonneg_right hlam1 hT0
          have h2 : R₁ ^ ((d : ℝ) / 2) * (lam * S.T + S.T * (𝔈 N) ^ ((1 : ℝ) / 2)) ≤
              R₁ ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 : ℝ) / d) * S.T + S.T * (𝔈 N) ^ ((1 : ℝ) / 2)) := by
            gcongr
          calc K0 * (R₁ ^ ((d : ℝ) / 2) * (lam * S.T + S.T * (𝔈 N) ^ ((1 : ℝ) / 2)) + S.T * m₂ / R₁ ^ 2)
              ≤ K0 * (R₁ ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 : ℝ) / d) * S.T + S.T * (𝔈 N) ^ ((1 : ℝ) / 2)) +
                S.T * m₂ / R₁ ^ 2) := by gcongr
            _ = _ := by ring
  -- the infimum over `R₁`
  have hKT : 0 ≤ K0 * S.T := mul_nonneg hK0 hT0
  rcases hKT.eq_or_lt with h0 | hpos
  · have := main 1 le_rfl
    rw [← h0, zero_mul] at this ⊢
    exact this
  · have hle : (∫ w, (∫ σ in Set.Icc (0 : ℝ) S.T, F σ w) ∂(R N).P) / (K0 * S.T) ≤ wN d N (𝔈 N) m₂ := by
      unfold wN
      refine le_ciInf fun R₁ => ?_
      rw [div_le_iff₀ hpos]
      calc _ ≤ K0 * S.T * (R₁.1 ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 : ℝ) / d) + (𝔈 N) ^ ((1 : ℝ) / 2)) +
            m₂ / R₁.1 ^ 2) := main R₁.1 R₁.2
        _ = _ := by ring
    have := (div_le_iff₀ hpos).1 hle
    calc _ ≤ wN d N (𝔈 N) m₂ * (K0 * S.T) := this
      _ = 2 * S.qN N * Ct * (∑ a, B a) ^ 2 * S.T * wN d N (𝔈 N) m₂ := by rw [hK0def]; ring

theorem sa4_cov_cost (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} (hprog : IsProgressive ℱ (ofNNRealTime (R N).X))
    {χ : Euc d → ℝ} {C₀c Ct : ℝ} (hTest : Sa4Test d S.s χ C₀c Ct) (hCt : 0 ≤ Ct) (hC₀c : 0 ≤ C₀c)
    (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T)
    (φ : Fin q → Euc d → ℝ) {B : Fin q → ℝ} (hB0 : ∀ a, 0 ≤ B a)
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb (mStar d) (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm (mStar d) (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a)
    (hinj : ∀ᵐ w ∂(R N).P, ∀ᵐ rr ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal rr) w))
    {m₂ : ℝ} (hm₂ : 0 ≤ m₂) (hmom : PropagatedSecondMoment S R m₂) :
    covDiscrepancyMatrix (R N).P S.T (sa2Sg S R N ts φ)
        (sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N)) ≤
      2 * S.qN N * Ct * (∑ a, B a) ^ 2 * S.T * wN d N (𝔈 N) m₂ := by
  unfold covDiscrepancyMatrix
  exact sa4_cov_cost_gen hS hd hN hprog hTest hCt hC₀c hC₀ ts hts φ hB0 hB hinj hm₂ hmom
    (fun σ w => s1Norm (sa2Sg S R N ts φ σ w -
      sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N) σ))
    (fun σ w => traceNormMatrix_nonneg _)
    (fun σ w => (HRS.Main.A8P.a8p_s1Norm_le_sum _).trans (le_of_eq (by simp only [Matrix.sub_apply])))


/-- the covariance cost in the Hilbert-Schmidt form -/
theorem sa4_covH (hS : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈)
    (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) {ℱ : Filtration ℝ (R N).mΩ}
    (hprog : IsProgressive ℱ (ofNNRealTime (R N).X))
    {χ : Euc d → ℝ} {C₀c Ct : ℝ} (hTest : Sa4Test d S.s χ C₀c Ct) (hCt : 0 ≤ Ct) (hC₀c : 0 ≤ C₀c)
    (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) {q : ℕ} (ts : Fin q → ℝ)
    (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Euc d → ℝ) {B : Fin q → ℝ}
    (hB0 : ∀ a, 0 ≤ B a)
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb (mStar d) (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm (mStar d) (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a)
    (hinj : ∀ᵐ ζ ∂(R N).P, ∀ᵐ rr ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal rr) ζ))
    {m₂ : ℝ} (hm₂ : 0 ≤ m₂) (hmom : PropagatedSecondMoment S R m₂) :
    covDiscrepancy (R N).P S.T (fun rr ζ => hsCovForm (sa2PhiH S R N ts φ rr ζ))
        (fun rr => HRS.Main.A8P.a8pForm (sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N) rr)) ≤
      2 * S.qN N * Ct * (∑ a, B a) ^ 2 * S.T * wN d N (𝔈 N) m₂ := by
  unfold covDiscrepancy
  simp only [sa2_hsCov_eq]
  refine sa4_cov_cost_gen hS hd hN hprog hTest hCt hC₀c hC₀ ts hts φ hB0 hB hinj hm₂ hmom
    (fun rr ζ => traceNormForm (HRS.Main.A8P.a8pForm (sa2Sg S R N ts φ rr ζ) -
      HRS.Main.A8P.a8pForm (sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N) rr)))
    (fun rr ζ => traceNormForm_nonneg _) (fun rr ζ => ?_)
  rw [← HRS.Main.A8P.a8pForm_sub]
  refine (HRS.Main.A8P.a8p_traceNormForm_le _).trans (le_of_eq ?_)
  simp only [Matrix.sub_apply]

end CovCost

end HRS.MS.DecStat
