import HRS.MS.MainRdStatAux17
import HRS.Main.A8PAux39

/-!
# SA2, packet 9a: relabelling of the index set (statistics indexed by `Fin (n+1) × Bool`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

theorem sa2_fluct_reindex {Ω : Type*} {N : ℕ} (e : ι ≃ Fin q) (σ : ℝ) (X : ℝ≥0 → Ω → EucConfig d N)
    (ρ : ℝ → Euc d → ℝ) (ts : ι → ℝ) (φ : ι → Euc d → ℝ) (ζ : Ω) :
    fluctStatRd σ X ρ ts φ ζ =
      HRS.Main.A8P.a8pV e (fluctStatRd σ X ρ (fun j => ts (e.symm j)) (fun j => φ (e.symm j)) ζ) := by
  ext i
  simp [fluctStatRd, HRS.Main.A8P.a8pV_apply]

theorem sa2_stat_law_reindex {Ω : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ} (e : ι ≃ Fin q)
    (P : Measure Ω) (σ : ℝ) (X : ℝ≥0 → Ω → EucConfig d N) (ρ : ℝ → Euc d → ℝ) (ts : ι → ℝ)
    (φ : ι → Euc d → ℝ)
    (hmeas : Measurable (fluctStatRd σ X ρ (fun j => ts (e.symm j)) (fun j => φ (e.symm j)))) :
    fluctStatLawRd P σ X ρ ts φ =
      (fluctStatLawRd P σ X ρ (fun j => ts (e.symm j)) (fun j => φ (e.symm j))).map
        (HRS.Main.A8P.a8pV e) := by
  unfold fluctStatLawRd law
  rw [Measure.map_map (HRS.Main.A8P.a8pV e).continuous.measurable hmeas]
  congr 1
  funext ζ
  exact sa2_fluct_reindex e σ X ρ ts φ ζ

theorem sa2_surr_law_reindex {Ω : Type*} {mΩ : MeasurableSpace Ω} (e : ι ≃ Fin q)
    (P : Measure Ω) [IsProbabilityMeasure P] (C : WholeCoeff d) (A qq : ℝ) (ts : ι → ℝ)
    (φ : ι → Euc d → ℝ) (η : Ω → (Euc d → ℝ) → ℝ) (hη : ∀ ψ : Euc d → ℝ, Measurable fun ζ => η ζ ψ)
    (hpsd : (Matrix.of fun a b : Fin q => noiseCovW C qq (ts (e.symm a)) (ts (e.symm b))
      (φ (e.symm a)) (φ (e.symm b))).PosSemidef) :
    surrogateStatLawRd C A qq ts φ P η =
      (surrogateStatLawRd C A qq (fun j => ts (e.symm j)) (fun j => φ (e.symm j)) P η).map
        (HRS.Main.A8P.a8pV e) := by
  unfold surrogateStatLawRd
  have hm : Measurable (fun ζ => (WithLp.toLp 2 fun a : Fin q => A * η ζ
      (propagatorW C 0 (ts (e.symm a)) (φ (e.symm a))) : EuclideanSpace ℝ (Fin q))) :=
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun a => measurable_const.mul (hη _))
  have hV : Measurable (HRS.Main.A8P.a8pV e) := (HRS.Main.A8P.a8pV e).continuous.measurable
  haveI : IsProbabilityMeasure (law P (fun ζ => (WithLp.toLp 2 fun a : Fin q => A * η ζ
      (propagatorW C 0 (ts (e.symm a)) (φ (e.symm a))) : EuclideanSpace ℝ (Fin q)))) :=
    inferInstanceAs (IsProbabilityMeasure (P.map _))
  have hconv := Measure.map_conv_addMonoidHom
    (μ := law P (fun ζ => (WithLp.toLp 2 fun a : Fin q => A * η ζ
      (propagatorW C 0 (ts (e.symm a)) (φ (e.symm a))) : EuclideanSpace ℝ (Fin q))))
    (ν := multivariateGaussian 0 (Matrix.of fun a b : Fin q => noiseCovW C qq (ts (e.symm a))
      (ts (e.symm b)) (φ (e.symm a)) (φ (e.symm b))))
    (HRS.Main.A8P.a8pV e).toLinearMap.toAddMonoidHom hV
  have h1 : law P (fun ζ => (WithLp.toLp 2 fun a : ι => A * η ζ (propagatorW C 0 (ts a) (φ a)) :
      EuclideanSpace ℝ ι)) = (law P (fun ζ => (WithLp.toLp 2 fun a : Fin q => A * η ζ
      (propagatorW C 0 (ts (e.symm a)) (φ (e.symm a))) : EuclideanSpace ℝ (Fin q)))).map
        (HRS.Main.A8P.a8pV e) := by
    unfold law
    rw [Measure.map_map hV hm]
    congr 1
    funext ζ
    ext i
    simp [HRS.Main.A8P.a8pV_apply]
  have hmat : (Matrix.of fun a b : ι => noiseCovW C qq (ts a) (ts b) (φ a) (φ b)) =
      (Matrix.of fun a b : Fin q => noiseCovW C qq (ts (e.symm a)) (ts (e.symm b))
        (φ (e.symm a)) (φ (e.symm b))).submatrix e e := by
    ext a b
    simp
  rw [hmat, HRS.Main.A8P.a8p_gauss_reindex e _ hpsd, h1]
  exact hconv.symm

section Basics

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}

/-- measurability of the statistics vector and positivity of the surrogate covariance -/
theorem sa2_iota_basics (hS : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈)
    {N : ℕ} (hN : 1 ≤ N) (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T)
    (φ : Fin q → Euc d → ℝ) (hφc : ∀ a, Continuous (φ a)) {B : Fin q → ℝ} (hB0 : ∀ a, 0 ≤ B a)
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a) :
    Measurable (fluctStatRd (S.sigma N) (R N).X (S.ρ N) ts φ) ∧
    (Matrix.of fun a b : Fin q => noiseCovW (S.coeff N) (S.qN N) (ts a) (ts b) (φ a) (φ b)).PosSemidef := by
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N
  have hXm : ∀ t : ℝ≥0, Measurable ((R N).X t) := fun t => (hF.adapted t).mono (ℱ.le _) le_rfl
  refine ⟨HRS.MS.PathFidi.sa26_fluct_meas (by omega) _ hXm _ ts φ hφc, ?_⟩
  have hsb := sa2_sb_isDet hS hN ts φ hB0 hB
  rw [sa2_sigma_eq hS ts hts φ]
  exact integratedCov_psd hsb

end Basics

end HRS.MS.MainRdStat
