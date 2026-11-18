import HRS.MS.ProClosureS111PhysicalI19
import HRS.MS.ProClosureS111ThermalResponse
import HRS.MS.ProClosureS111LpFTCRepresentatives

/-!
The physical screened terminal FTC as actual scalar random paths.
There is no assumed window-orbit input. Each derivative section represents
the prescribed response at every time, including zero and the terminal
endpoint, and the entire family has a common almost-sure scalar FTC.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6C

variable {d : ℕ}
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

theorem projMean_sub_const (mu : Measure (Euc d)) [IsProbabilityMeasure mu]
    (f : Euc d → ℝ) (hf : Integrable f mu) (c : ℝ) :
    HRS.Whole.projMean mu (fun x => f x - c) = HRS.Whole.projMean mu f := by
  have hi : HRS.Whole.pair mu (fun x => f x - c) = HRS.Whole.pair mu f - c := by
    simp [HRS.Whole.pair, integral_sub hf (integrable_const c)]
  funext x
  simp only [HRS.Whole.projMean, hi]
  ring

/-- Exact equality of the frozen choices: their defining predicates coincide. -/
theorem responseInverse_sub_const (mu : Measure (Euc d)) [IsProbabilityMeasure mu]
    (kernel : Euc d → ℝ) (gamma : ℝ)
    (f : Euc d → ℝ) (hf : Integrable f mu) (c : ℝ) :
    HRS.Whole.responseInverse kernel mu gamma (fun x => f x - c) =
      HRS.Whole.responseInverse kernel mu gamma f := by
  have hproj := projMean_sub_const mu f hf c
  have hpred : (fun h => HRS.Whole.IsResponse kernel mu gamma (fun x => f x - c) h) =
      (fun h => HRS.Whole.IsResponse kernel mu gamma f h) := by
    funext h
    unfold HRS.Whole.IsResponse
    apply propext
    constructor
    · rintro ⟨hm, hh⟩
      refine ⟨hm, ?_⟩
      simpa only [HRS.Whole.IsResponse, hproj] using hh
    · rintro ⟨hm, hh⟩
      refine ⟨hm, ?_⟩
      simpa only [HRS.Whole.IsResponse, hproj] using hh
  unfold HRS.Whole.responseInverse
  exact congrArg (fun P : (Euc d → ℝ) → Prop =>
    if h : ∃ h, P h then h.choose else 0) hpred

theorem screened_center_rep (mu : Measure (Euc d)) [IsProbabilityMeasure mu]
    (kernel : Euc d → ℝ) (gamma : ℝ)
    (R : Lp ℝ 3 mu →L[ℝ] Lp ℝ 3 mu)
    (hR : ∀ f : Euc d → ℝ, ∀ hf : MemLp f 3 mu,
      (R (hf.toLp f) : Euc d → ℝ) =ᵐ[mu] HRS.Whole.responseInverse kernel mu gamma f)
    (f : Euc d → ℝ) (hf : MemLp (fun x => f x - f 0) 3 mu) :
    (R (r26t6c_toLp3 mu (fun x => f x - f 0)) : Euc d → ℝ) =ᵐ[mu]
      HRS.Whole.responseInverse kernel mu gamma f := by
  have hf3 : MemLp f 3 mu := by
    convert hf.add (memLp_const (f 0)) using 1
    funext x
    simp
  have h := hR (fun x => f x - f 0) hf
  rw [responseInverse_sub_const mu kernel gamma f (hf3.integrable (by norm_num)) (f 0)] at h
  simpa only [r26t6c_toLp3, dif_pos hf] using h

/-- An actual physical producer of the screened scalar FTC, with no `hW`.
The response preparation may be zero. -/
theorem physical_screened_terminal_FTC (hd : 2 ≤ d)
    (s a beta gamma T u : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hgamma : 0 ≤ gamma)
    (hT : 0 < T) (hu : 0 ≤ u)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d s a beta rho) :
    let mu := HRS.Whole.withDensityReal rho
    let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
    let phi := fun alpha : MultiIndex d => oscTestFun (wholeSpaceIndex d) alpha
    ∃ f g : MultiIndex d → ℝ → Euc d → ℝ,
      (∀ alpha, StronglyMeasurable (fun z : ℝ × Euc d => g alpha z.1 z.2)) ∧
      (∀ alpha t, t ∈ Icc (0 : ℝ) T →
        MemLp (f alpha t) 3 mu ∧
        f alpha t =ᵐ[mu] HRS.Whole.responseInverse (rieszKernel d s) mu gamma
          (propagatorW C 0 (u + t) (phi alpha)) ∧
        MemLp (g alpha t) 3 mu ∧
        g alpha t =ᵐ[mu] HRS.Whole.responseInverse (rieszKernel d s) mu gamma
          (propagatorW C 0 (u + t) (generatorW C (u + t) (phi alpha)))) ∧
      ∀ᵐ x ∂mu, ∀ alpha,
        IntegrableOn (fun v => g alpha v x) (Icc (0 : ℝ) T) ∧
        ∀ t ∈ Icc (0 : ℝ) T, f alpha t x =
          f alpha 0 x + ∫ v in Icc (0 : ℝ) t, g alpha v x := by
  let mu := HRS.Whole.withDensityReal rho
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  let phi := fun alpha : MultiIndex d => oscTestFun (wholeSpaceIndex d) alpha
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.2.1
  have hsd : s < (d : ℝ) := by
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ (d : ℝ))]
  obtain ⟨Cresp, hCresp, hresponse⟩ :=
    physical_response_L3_CLM_uniform hd s a beta hs0 hs ha hbeta
  obtain ⟨R, hRnorm, hR⟩ := hresponse rho hrho gamma hgamma
  have hex : ∀ alpha : MultiIndex d, ∃ f g : ℝ → Euc d → ℝ,
      StronglyMeasurable (fun z : ℝ × Euc d => g z.1 z.2) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        MemLp (f t) 3 mu ∧
        f t =ᵐ[mu] HRS.Whole.responseInverse (rieszKernel d s) mu gamma
          (propagatorW C 0 (u + t) (phi alpha)) ∧
        MemLp (g t) 3 mu ∧
        g t =ᵐ[mu] HRS.Whole.responseInverse (rieszKernel d s) mu gamma
          (propagatorW C 0 (u + t) (generatorW C (u + t) (phi alpha)))) ∧
      ∀ᵐ x ∂mu, IntegrableOn (fun v => g v x) (Icc (0 : ℝ) T) ∧
        ∀ t ∈ Icc (0 : ℝ) T, f t x = f 0 x + ∫ v in Icc (0 : ℝ) t, g v x := by
    intro alpha
    let q := fun t => propagatorW C 0 (u + t) (phi alpha)
    let qp := fun t => propagatorW C 0 (u + t) (generatorW C (u + t) (phi alpha))
    let Q := fun t => r26t6c_toLp3 mu (fun x => q t x - q t 0)
    let D := fun t => r26t6c_toLp3 mu (fun x => qp t x - qp t 0)
    obtain ⟨hLp, hDm, hDi, hFTC⟩ :=
      physical_centered_terminal_L3_FTC hd s a beta T u hs0 hsd ha hbeta hT hu rho hrho alpha
    change (∀ t ∈ Icc (0 : ℝ) T, MemLp (fun x => q t x - q t 0) 3 mu ∧
      MemLp (fun x => qp t x - qp t 0) 3 mu) at hLp
    change StronglyMeasurable (fun t : Icc (0 : ℝ) T => D t) at hDm
    change IntegrableOn D (Icc (0 : ℝ) T) at hDi
    change ∀ t ∈ Icc (0 : ℝ) T, Q t = Q 0 + ∫ v in Icc (0 : ℝ) t, D v at hFTC
    let F := fun t => R (Q t)
    let G := fun t => R (D t)
    have hGm : StronglyMeasurable (fun t : Icc (0 : ℝ) T => G t) :=
      R.continuous.comp_stronglyMeasurable hDm
    have hGi : IntegrableOn G (Icc (0 : ℝ) T) := R.integrable_comp hDi
    have hFG : ∀ t ∈ Icc (0 : ℝ) T, F t = F 0 + ∫ v in Icc (0 : ℝ) t, G v := by
      intro t ht
      have hDt : IntegrableOn D (Icc (0 : ℝ) t) :=
        hDi.mono_set (fun v hv => ⟨hv.1, hv.2.trans ht.2⟩)
      dsimp only [F, G]
      rw [hFTC t ht, map_add, ← R.integral_comp_comm hDt]
    obtain ⟨f, g, hgm, hrep, hpath⟩ := L3_FTC_representatives mu T hT.le F G hGm hGi hFG
    refine ⟨f, g, hgm, fun t ht => ?_, hpath⟩
    obtain ⟨hf3, hf, hg3, hg⟩ := hrep t ht
    exact ⟨hf3, hf.trans (screened_center_rep mu (rieszKernel d s) gamma R hR
      (q t) (hLp t ht).1), hg3,
      hg.trans (screened_center_rep mu (rieszKernel d s) gamma R hR
        (qp t) (hLp t ht).2)⟩
  choose f g hgm hrep hpath using hex
  exact ⟨f, g, hgm, hrep, ae_all_iff.2 hpath⟩

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.physical_screened_terminal_FTC
