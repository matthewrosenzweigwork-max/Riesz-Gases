import HRS.Sections.Q40bAux12
import HRS.Sections.Q40bAux13

/-!
# Packet Q40b, part 14: ingredients of `criterion_stationary`

* `q40b_cov_uniform`: `exists_cov_comparison` with constants uniform in the lags `τ`;
* `q40b_noiseCov_eq`: `noiseCovMatrix` of the trajectory is the covariance `Mcov` of `PDE.MFLinear`;
* `q40b_zetaStat_eval`: `⟨ψ, ζ_N^0⟩` is the evaluation of `ζ_N^∘ ∈ E_j` at `ψ`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section
namespace HRS.Q40b

open PDE PDE.MFLinear

variable {d : ℕ}

theorem q40b_cov_uniform (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) (j : ℕ) (hjeven : Even j) (hj : (d : ℝ) / 2 + 4 < j)
    (hK : 2 * j + 4 * d + 20 ≤ K) (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρc : ℝ → Coeff d)
    (hρc : IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Continuous ρβ)
    (hpos : ∀ x, 0 < ρβ x) (p : ℕ) (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ τ : Fin p → ℝ, (∀ a, 0 ≤ τ a) →
      (stationaryLagCov d s β (mfD H hβ) ρβ τ φ).PosSemidef ∧
      ∀ u : ℝ, 0 ≤ u →
        (Mcov (mfD H hβ) ρc τ φ u).PosSemidef ∧
        ∀ a b, |Mcov (mfD H hβ) ρc τ φ u a b -
          stationaryLagCov d s β (mfD H hβ) ρβ τ φ a b| ≤ C * Real.exp (-c * u) := by
  obtain ⟨m, Cρ, c₀, Λ₀, hF, Hz⟩ :=
    loss_facts hd s βm βp K V ρ₀ H j hjeven hj hK β hβ ρc hρc ρβ hρβ hρC hpos
  have hm := hF.m_pos
  have hν : 0 < β⁻¹ := inv_pos.2 (lt_of_lt_of_le H.hβm hβ.1)
  choose CA hCA0 hA2 hAS hAUS hAU using fun a => hF.grad (φ a) (hφ a)
  set Cab : Fin p → Fin p → ℝ := fun a b =>
    2 * β⁻¹ * ((2 / m) * (CA a * CA b * (2 + Cρ)) + CA a * CA b / m) with hCab
  have hCab0 : ∀ a b, 0 ≤ Cab a b := by
    intro a b
    have := hCA0 a; have := hCA0 b; have := hF.Cρ_nonneg
    simp only [hCab]
    positivity
  set C : ℝ := 1 + ∑ a, ∑ b, Cab a b with hC
  have hCpos : 0 < C := by
    have : 0 ≤ ∑ a, ∑ b, Cab a b := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      hCab0 a b
    rw [hC]; linarith
  have hCle : ∀ a b, Cab a b ≤ C := by
    intro a b
    have h1 : Cab a b ≤ ∑ b', Cab a b' :=
      Finset.single_le_sum (f := fun b' => Cab a b') (fun b' _ => hCab0 a b') (Finset.mem_univ b)
    have h2 : ∑ b', Cab a b' ≤ ∑ a', ∑ b', Cab a' b' :=
      Finset.single_le_sum (f := fun a' => ∑ b', Cab a' b')
        (fun a' _ => Finset.sum_nonneg fun b' _ => hCab0 a' b') (Finset.mem_univ a)
    rw [hC]; linarith
  refine ⟨C, m / 2, hCpos, by linarith, fun τ hτ => ?_⟩
  have hent := fun u (hu : 0 ≤ u) a b =>
    Mcov_entry hd Hz hF τ hτ φ hφ CA hCA0 hA2 hAS hAUS hAU u hu a b
  have hbound : ∀ u, 0 ≤ u → ∀ a b, |Mcov (mfD H hβ) ρc τ φ u a b -
      stationaryLagCov d s β (mfD H hβ) ρβ τ φ a b| ≤ C * Real.exp (-(m / 2) * u) := by
    intro u hu a b
    refine (hent u hu a b).trans ?_
    exact mul_le_mul_of_nonneg_right (hCle a b) (Real.exp_pos _).le
  have hMpsd : ∀ u, 0 ≤ u → (Mcov (mfD H hβ) ρc τ φ u).PosSemidef := fun u hu =>
    Mcov_posSemidef hF (by exact hν.le) τ hτ φ hφ u hu
  exact ⟨posSemidef_of_approx _ (fun u => Mcov (mfD H hβ) ρc τ φ u) hMpsd C (m / 2)
    (by linarith) hbound, fun u hu => ⟨hMpsd u hu, hbound u hu⟩⟩

theorem q40b_noiseCov_eq {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {ρc : ℝ → Coeff d}
    (hρ : ∀ t, 0 ≤ t → mfPath ρc t = ρ t) {p : ℕ} (t : Fin p → ℝ) (ht : ∀ a, 0 ≤ t a)
    (φ : Fin p → Torus d → ℝ) :
    noiseCovMatrix htr.dyn ρ β⁻¹ t φ =
      Matrix.of fun a b => 2 * htr.dyn.invβ *
        ∫ r in Set.Icc 0 (min (t a) (t b)), Eint htr.dyn ρc (φ a) (φ b) (t a) (t b) r := by
  ext a b
  simp only [noiseCovMatrix, Matrix.of_apply]
  have hinv : htr.dyn.invβ = β⁻¹ := rfl
  rw [hinv]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
  have hr0 : 0 ≤ r := hr.1
  have hcga : ∀ r' ∈ Set.Icc (0 : ℝ) (t a), ρ r' = mfPath ρc r' := fun r' h => (hρ r' h.1).symm
  have hcgb : ∀ r' ∈ Set.Icc (0 : ℝ) (t b), ρ r' = mfPath ρc r' := fun r' h => (hρ r' h.1).symm
  unfold Eint
  rw [q40b_propagator_congr hcga r (φ a), q40b_propagator_congr hcgb r (φ b), hρ r hr0]


theorem q40b_eval_smul {m : ℝ} (c : ℝ) (F : NegSobolev d m) (ψ : Torus d → ℝ) :
    NegSobolev.eval (c • F) ψ = c * NegSobolev.eval F ψ := by
  unfold NegSobolev.eval
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have : NegSobolev.fourierCoeff (c • F) k = c * NegSobolev.fourierCoeff F k := by
    unfold NegSobolev.fourierCoeff NegSobolev.coord
    show Lattice.jp k.1 ^ m * ((c • (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F)) k) = _
    rw [lp.coeFn_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [this]
  ring

theorem q40b_zetaStat_eval {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (hN : 1 ≤ N) (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → Config d N) {j : ℝ} (hj : (d : ℝ) < 2 * j)
    {ψ : Torus d → ℝ} (hc : Continuous ψ)
    (hs : Summable fun k : Lattice d => ‖Torus.fcoef ψ k‖) (ω : Ω) :
    zetaStat P X 0 ψ ω = NegSobolev.eval (zetaE j (P.map (X 0)) (X 0 ω)) ψ := by
  unfold zetaStat zetaE
  simp only [Real.toNNReal_zero]
  rw [q40b_eval_smul]
  congr 1
  haveI := empirical_isProbabilityMeasure (by omega : 0 < N) (X 0 ω)
  haveI : IsProbabilityMeasure (P.map (X 0)) := inferInstance
  haveI := isProbabilityMeasure_meanEmpirical (P.map (X 0)) hN
  rw [NegSobolev.eval_ofMeasureDiff_of_summable hj _ _ ψ hc hs,
    pair_empirical (by omega : 0 < N)]
  ring

theorem q40b_summable_fcoef {j : ℕ} (hj : (d : ℝ) / 2 < j) {ψ : Torus d → ℝ} {c : ℝ}
    (hmem : MemSobolev (j : ℝ) (fun x => ψ x - c)) :
    Summable fun k : Lattice d => ‖Torus.fcoef ψ k‖ := by
  have hL2 : MemLp ψ 2 volume := by
    have := hmem.1.add (memLp_const (c : ℝ) : MemLp (fun _ : Torus d => c) 2 volume)
    have e : ((fun x => ψ x - c) + fun _ : Torus d => c) = ψ := by
      funext x; simp
    rwa [e] at this
  have hψ : MemSobolev (j : ℝ) ψ := ⟨hL2, summable_of_memSobolev_sub_const hmem⟩
  have h1 := (hsNormSq_coeffOf (j : ℝ) ψ hψ).1
  have h2 := summable_norm_of_memHs (j : ℝ) hj (coeffOf ψ) h1
  simpa only [coeffOf_eq_fcoef] using h2

end HRS.Q40b
