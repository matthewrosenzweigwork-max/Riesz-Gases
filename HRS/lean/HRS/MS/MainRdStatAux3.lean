import HRS.MS.MainRdStatAux2

/-!
# SA2, packet 3: the Itô decomposition `Z = I_emp + M + R` of the statistics vector

For a finite family `(t_a, φ_a)`, `ψ_a = U_N^{0,t_a}φ_a`, `c_N = σ_N √(2β_N⁻¹)/N`:
* `sa2Phi`: the killed scaled noise integrand `c_N ∇U^{r,t_a}φ_a(x_i^r)` (zero outside `[0,t_a]`);
* `sa2_decomp`: a.s. `Z = I_emp + (vectorItoIntegral of the killed integrands)(T) + R` (`duality_identity_rd` at `τ = t_a`);
* `sa2_vecmart`: the vector martingale with covariation `killedCovMatrix`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ}

/-- The scaled noise integrand of the `a`-th statistic. -/
def sa2Phi (S : WholeMainData d) {Ω : Type*} {N : ℕ} (t : ℝ) (φ : Euc d → ℝ)
    (X : ℝ≥0 → Ω → EucConfig d N) : ℝ → Ω → Fin N × Fin d → ℝ :=
  fun r ζ => (S.sigma N * (Real.sqrt (2 * S.invβ N) / N)) •
    HRS.MH.DualityRd.truncGradIntegrand t (fun r => propagatorW (S.coeff N) r t φ) X r ζ

theorem sa2_grad_coord_le {f : Euc d → ℝ} (hf : MemCb 2 f) (x : Euc d) (j : Fin d) :
    |gradient f x j| ≤ cbNorm 2 f := by
  have h1 : gradient f x j = fderiv ℝ f x (EuclideanSpace.single j 1) :=
    HRS.MP.RdMart.mrm_grad_component f x j
  have h2 : ‖fderiv ℝ f x‖ ≤ cbNorm 2 f := by
    have := sa2_norm_iter_le_cbNorm (k := 2) (j := 1) (by norm_num) hf x
    rwa [norm_iteratedFDeriv_one] at this
  rw [h1, ← Real.norm_eq_abs]
  refine ((fderiv ℝ f x).le_opNorm _).trans ?_
  simpa using h2

theorem sa2_trunc_prog {Ω : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ} {ℱ : Filtration ℝ mΩ}
    (C : WholeCoeff d) (t : ℝ) (φ : Euc d → ℝ) {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : IsProgressive ℱ (ofNNRealTime X)) :
    IsProgressive ℱ (HRS.MH.DualityRd.truncGradIntegrand t (fun r => propagatorW C r t φ) X) := by
  intro i
  letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  refine measurable_pi_iff.2 fun ia => ?_
  have hXi : IsProgressive ℱ (fun r ζ => ofNNRealTime X r ζ ia.1) := fun i =>
    (measurable_pi_apply ia.1).comp (hX i)
  have hg := isProgressive_comp_measurable' (fun r ζ => ofNNRealTime X r ζ ia.1) hXi
    (fun r (x : Euc d) => if r ∈ Set.Icc (0 : ℝ) t then gradient (propagatorW C r t φ) x ia.2 else 0)
    (HRS.MP.RdMart.mrm_meas_grad C t φ ia.2)
  exact hg i

theorem sa2_trunc_bound {Ω : Type*} {N : ℕ} {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {B : ℝ}
    (hB : ∀ r ∈ Set.Icc (0 : ℝ) t, MemCb 2 (propagatorW C r t φ) ∧ cbNorm 2 (propagatorW C r t φ) ≤ B)
    (hB0 : 0 ≤ B) (X : ℝ≥0 → Ω → EucConfig d N) (r : ℝ) (ζ : Ω) (ia : Fin N × Fin d) :
    |HRS.MH.DualityRd.truncGradIntegrand t (fun r => propagatorW C r t φ) X r ζ ia| ≤ B := by
  unfold HRS.MH.DualityRd.truncGradIntegrand
  by_cases hr : r ∈ Set.Icc (0 : ℝ) t
  · rw [if_pos hr]
    obtain ⟨hm, hb⟩ := hB r hr
    exact (sa2_grad_coord_le hm _ _).trans hb
  · rw [if_neg hr]; simpa using hB0

theorem sa2_phi_L2 {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} (S : WholeMainData d) {N : ℕ} {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {B : ℝ}
    (hB : ∀ r ∈ Set.Icc (0 : ℝ) t, MemCb 2 (propagatorW C r t φ) ∧ cbNorm 2 (propagatorW C r t φ) ≤ B)
    (hB0 : 0 ≤ B) {X : ℝ≥0 → Ω → EucConfig d N} (hX : IsProgressive ℱ (ofNNRealTime X))
    (hC : C = S.coeff N) :
    IsProgressiveL2 P ℱ (sa2Phi S t φ X) := by
  subst hC
  have h1 : IsProgressiveL2 P ℱ
      (HRS.MH.DualityRd.truncGradIntegrand t (fun r => propagatorW (S.coeff N) r t φ) X) :=
    IsProgressiveL2.of_bounded P (sa2_trunc_prog _ t φ hX) B (fun s z k => sa2_trunc_bound hB hB0 X s z k)
  exact h1.smul _

section Decomp

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ}
  {𝔈 : ℕ → ℝ}

/-- The scaled initial statistics `σ(⟨ψ_a, μ_N^0⟩ - ⟨ψ_a, μ_{β_N}^0⟩)`. -/
def sa2Iemp (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (N : ℕ) {q : ℕ} (ts : Fin q → ℝ)
    (φ : Fin q → Euc d → ℝ) (ζ : (R N).Ω) : EuclideanSpace ℝ (Fin q) :=
  WithLp.toLp 2 fun a => S.sigma N *
    (HRS.Whole.pair (HRS.Whole.empirical ((R N).X 0 ζ)) (propagatorW (S.coeff N) 0 (ts a) (φ a)) -
      HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N 0)) (propagatorW (S.coeff N) 0 (ts a) (φ a)))

/-- The surrogate initial statistics `A_N η(ψ_a)`. -/
def sa2Itil (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (N : ℕ) {q : ℕ} (ts : Fin q → ℝ)
    (φ : Fin q → Euc d → ℝ) (ζ : (R N).Ω) : EuclideanSpace ℝ (Fin q) :=
  WithLp.toLp 2 fun a => S.AN N * (R N).η ζ (propagatorW (S.coeff N) 0 (ts a) (φ a))

/-- The scaled remainders. -/
def sa2Rem (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (N : ℕ) {q : ℕ} (ts : Fin q → ℝ)
    (φ : Fin q → Euc d → ℝ) (ζ : (R N).Ω) : EuclideanSpace ℝ (Fin q) :=
  WithLp.toLp 2 fun a => S.sigma N * ∫ r in Set.Icc (0 : ℝ) (ts a),
    flucInteractionRd (S.dyn N) (propagatorW (S.coeff N) r (ts a) (φ a))
      ((R N).X (Real.toNNReal r) ζ) (S.ρ N r)

theorem sa2_vecmart {N : ℕ} {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Euc d → ℝ) {B : Fin q → ℝ}
    (hB : ∀ a, ∀ r ∈ Set.Icc (0 : ℝ) (ts a), MemCb 2 (propagatorW (S.coeff N) r (ts a) (φ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) r (ts a) (φ a)) ≤ B a) (hB0 : ∀ a, 0 ≤ B a) :
    IsVectorMartingaleWithCovariation (R N).P ℱ S.T
      (vectorItoIntegral (R N).P ℱ W' (fun a => killAfter (sa2Phi S (ts a) (φ a) (R N).X) (ts a)))
      (killedCovMatrix (fun a => sa2Phi S (ts a) (φ a) (R N).X) ts) ∧
    ∀ᵐ ζ ∂(R N).P, ∀ a,
      vectorItoIntegral (R N).P ℱ W' (fun a => killAfter (sa2Phi S (ts a) (φ a) (R N).X) (ts a)) S.T ζ a =
        itoIntegral (R N).P ℱ W' (sa2Phi S (ts a) (φ a) (R N).X) (ts a) ζ := by
  have hΦ : ∀ a, IsProgressiveL2 (R N).P ℱ (sa2Phi S (ts a) (φ a) (R N).X) := fun a =>
    sa2_phi_L2 S (hB a) (hB0 a) hF.progressive rfl
  exact several_times_covariation (R N).P hF.brownian (fun a => sa2Phi S (ts a) (φ a) (R N).X) hΦ ts
    (fun a => (hts a).1) S.T (fun a => (hts a).2)

/-- The decomposition `Z = I_emp + M + R`. -/
theorem sa2_decomp (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hr3 : 3 ≤ r) (hmV : 2 ≤ mV)
    {N : ℕ} (hN : 1 ≤ N) {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Euc d → ℝ)
    {B : Fin q → ℝ}
    (hB : ∀ a, ∀ r ∈ Set.Icc (0 : ℝ) (ts a), MemCb 2 (propagatorW (S.coeff N) r (ts a) (φ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) r (ts a) (φ a)) ≤ B a) (hB0 : ∀ a, 0 ≤ B a)
    (hcl : ∀ a, IsClassicalAdjointW (S.coeff N) (ts a) (φ a)
      (fun r => propagatorW (S.coeff N) r (ts a) (φ a))) :
    ∀ᵐ ζ ∂(R N).P, fluctStatRd (S.sigma N) (R N).X (S.ρ N) ts φ ζ =
      sa2Iemp S R N ts φ ζ +
        vectorItoIntegral (R N).P ℱ W'
          (fun a => killAfter (sa2Phi S (ts a) (φ a) (R N).X) (ts a)) S.T ζ + sa2Rem S R N ts φ ζ := by
  obtain ⟨-, hmid⟩ := sa2_vecmart hF ts hts φ hB hB0
  have hdual : ∀ a, DualityIdentityRd (R N).P ℱ W' (S.dyn N) (S.ρ N) (R N).X (ts a)
      (fun r => propagatorW (S.coeff N) r (ts a) (φ a)) := fun a =>
    HRS.MH.DualityRd.duality_identity_rd_proof S.s Λ S.T ΛV G₀ (S.dyn N) rfl S.hs0 S.hsd (S.hinvβ N)
      (sa2_vhyp_mono hS.potential hmV) (S.ρ N) (hS.mean_field.solution N hN)
      (sa2_regular_mono (hS.mean_field.regular N hN) hr3 le_rfl) (R N).P (R N).X₀ (R N).W (R N).X
      (hS.flow N hN) ℱ W' hF (ts a) (hts a) (φ a) _ (hcl a)
  have hΦ : ∀ a, IsProgressiveL2 (R N).P ℱ
      (HRS.MH.DualityRd.truncGradIntegrand (ts a) (fun r => propagatorW (S.coeff N) r (ts a) (φ a)) (R N).X) :=
    fun a => IsProgressiveL2.of_bounded (R N).P (sa2_trunc_prog _ (ts a) (φ a) hF.progressive) (B a)
      (fun s z k => sa2_trunc_bound (hB a) (hB0 a) (R N).X s z k)
  have hsm := fun a => itoIntegral_smul hF.brownian (hΦ a) (S.sigma N * (Real.sqrt (2 * S.invβ N) / N))
  filter_upwards [ae_all_iff.2 hdual, hmid, ae_all_iff.2 hsm] with ζ hD hM hS'
  ext a
  have h1 := (hD a (ts a) ⟨(hts a).1, le_rfl⟩).2
  have h2 := hM a
  have h3 := hS' a (ts a)
  have hterm : (fun r => propagatorW (S.coeff N) r (ts a) (φ a)) (ts a) = φ a := (hcl a).terminal
  simp only [hterm] at h1
  simp only [fluctStatRd, sa2Iemp, sa2Rem, PiLp.add_apply, PiLp.toLp_apply]
  have e : itoIntegral (R N).P ℱ W' (sa2Phi S (ts a) (φ a) (R N).X) (ts a) ζ =
      (S.sigma N * (Real.sqrt (2 * S.invβ N) / N)) * itoIntegral (R N).P ℱ W'
        (HRS.MH.DualityRd.truncGradIntegrand (ts a)
          (fun r => propagatorW (S.coeff N) r (ts a) (φ a)) (R N).X) (ts a) ζ := h3
  have hdyn : (S.dyn N).invβ = S.invβ N := rfl
  rw [hdyn] at h1
  unfold HRS.MH.DualityRd.truncGradIntegrand at e
  rw [h2, e]
  linear_combination (S.sigma N) * h1

end Decomp

end HRS.MS.MainRdStat
