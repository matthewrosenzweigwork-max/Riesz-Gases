import HRS.MS.R2GenInitAux29
import HRS.MS.GenPathAux46

/-!
# S10.5 window comparison, packet D1: the Gaussian `𝒦_T`-martingale of the window and its finite-dimensional laws

For a Gaussian martingale `G` with deterministic covariation density `s105Db` on `[0,b+T]`:
`s105_Db_dir_zero` (the increments of `y1(u,α) - y2(α)` after `b+u` have zero variance), `s105_recon_coord_eq`
(`coord_α (𝒯 G)(u) = ⟨G_{b+u}, y1(u,α)⟩` a.s.), `s105_noiseCov_eq` (the covariance of the pairings is `noiseCovW`) and
`s105_Gb_fdd` (the vector `(⟨G_{b+u_a}, y1(u_a,α_a)⟩)_a` is a centered Gaussian with covariance `noiseCovW`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.GenPath HRS.MS.S52 HRS.MP.RdRem HRS.MH.DualityRd HRS.Uniform.Q54c HRS.GF

variable {d : ℕ}

theorem s105_pair_all {s a β T b : ℝ} {ρ : Euc d → ℝ} (hS : S105Stat d s a β T b ρ) (hb : 0 ≤ b) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) T) (a' : Fin d) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) (b + T)) (x : Euc d)
    (α : MultiIndex d) :
    inner ℝ (r2WindowFeature ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T
        (gradComp a') b r x) (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T u α) =
      (if r ≤ b + u then gradComp a' (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r (b + u)
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) x else gradComp a' (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) x) ∧
    inner ℝ (r2WindowFeature ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T
        (gradComp a') b r x) (s52y2 ((wholeSpaceIndex d : ℕ) : ℝ) T α) =
      (if b ≤ r then gradComp a' (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) x else 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := hS.hK a' r hr x
  exact ⟨s105_pair_y1 _ hS.hC hb hr.1 hr.2 hu a' x h1 h3 h4 α, s105_pair_y2 _ _ T b r a' x h1 h2 h4 α⟩

theorem s105_Db_dir_zero {s a β T b : ℝ} {ρ : Euc d → ℝ} (hS : S105Stat d s a β T b ρ) (hb : 0 ≤ b)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) (α : MultiIndex d) (q : ℝ) (hq : 0 ≤ q)
    [IsFiniteMeasure (HRS.Whole.withDensityReal ρ)] :
    ∀ σ ∈ Set.Ioc (b + u) (b + T), s105Db _ hS.hF (HRS.Whole.withDensityReal ρ) q hq σ
      (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T u α - s52y2 ((wholeSpaceIndex d : ℕ) : ℝ) T α)
      (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T u α - s52y2 ((wholeSpaceIndex d : ℕ) : ℝ) T α) = 0 := by
  intro σ hσ
  have hσ' : σ ∈ Set.Icc (0 : ℝ) (b + T) := ⟨by linarith [hu.1, hσ.1], hσ.2⟩
  rw [(s105Db_spec _ hS.hF _ q hq hσ').1]
  unfold featureForm
  have hz : ∀ (a' : Fin d) (x : Euc d), inner ℝ (r2WindowFeature
      ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b σ x)
      (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T u α - s52y2 ((wholeSpaceIndex d : ℕ) : ℝ) T α) = 0 := by
    intro a' x
    obtain ⟨e1, e2⟩ := s105_pair_all hS hb hu a' hσ' x α
    rw [inner_sub_right, e1, e2, if_neg (not_le.2 hσ.1), if_pos (by linarith [hu.1, hσ.1]), sub_self]
  simp [hz]

theorem s105_recon_coord_eq {s a β T b : ℝ} {ρ : Euc d → ℝ} (hS : S105Stat d s a β T b ρ) (hb : 0 ≤ b)
    (q : ℝ) (hq : 0 ≤ q) [IsFiniteMeasure (HRS.Whole.withDensityReal ρ)] {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {G : ℝ → Ω → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T}
    (hG : IsHilbertMartingaleWithCovariation P ℱ (b + T) G (fun r _ =>
      s105Db _ hS.hF (HRS.Whole.withDensityReal ρ) q hq r))
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) (α : MultiIndex d) :
    ∀ᵐ ζ ∂P, OscDual.coord (reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => G (b + τ) ζ) ζ u) α =
      inner ℝ (G (b + u) ζ) (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T u α) := by
  have h := s56_incr_zero hG (t := b + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T u α - s52y2 ((wholeSpaceIndex d : ℕ) : ℝ) T α)
    (s105_Db_dir_zero hS hb hu α q hq)
  filter_upwards [h] with ζ hζ
  rw [s52_coord_recon hu.1 hu.2 (fun τ ζ => G (b + τ) ζ) ζ α]
  simp only [inner_sub_right] at hζ
  linarith

theorem s105_noiseCov_eq {s a β T b : ℝ} {ρ : Euc d → ℝ} (hS : S105Stat d s a β T b ρ) (hb : 0 ≤ b)
    (q : ℝ) (hq : 0 ≤ q) {ua uc : ℝ} (hua : ua ∈ Set.Icc (0 : ℝ) T) (huc : uc ∈ Set.Icc (0 : ℝ) T)
    (αa αc : MultiIndex d) :
    haveI := HRS.MS.Thm.cb_withDensityReal_isProb hS.hprob
    ∫ σ in Set.Icc (0 : ℝ) (min (b + ua) (b + uc)), s105Db _ hS.hF (HRS.Whole.withDensityReal ρ) q hq σ
      (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T ua αa) (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T uc αc) =
      noiseCovW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) q (b + ua) (b + uc)
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αa) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αc) := by
  haveI := HRS.MS.Thm.cb_withDensityReal_isProb hS.hprob
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hCdef
  have hρC : ∀ r x, C.ρ r x = ρ x := fun r x => rfl
  unfold noiseCovW
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
  have hta : b + ua ∈ Set.Icc (0 : ℝ) (b + T) := ⟨by linarith [hua.1], by linarith [hua.2]⟩
  have htb : b + uc ∈ Set.Icc (0 : ℝ) (b + T) := ⟨by linarith [huc.1], by linarith [huc.2]⟩
  have hσa : σ ≤ b + ua := hσ.2.trans (min_le_left _ _)
  have hσb : σ ≤ b + uc := hσ.2.trans (min_le_right _ _)
  have hσT : σ ∈ Set.Icc (0 : ℝ) (b + T) := ⟨hσ.1, hσa.trans hta.2⟩
  have hcla := hS.hcl αa (b + ua) hta.1
  have hclb := hS.hcl αc (b + uc) htb.1
  obtain ⟨Ba, hBa⟩ := s56_gradComp_bdd hcla
  obtain ⟨Bb, hBb⟩ := s56_gradComp_bdd hclb
  have hρ := hS.hprob
  rw [(s105Db_spec _ hS.hF _ q hq hσT).1]
  unfold featureForm
  beta_reduce
  have hpair : ∀ (c : Fin d) (x : Euc d), inner ℝ (r2WindowFeature C ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp c) b σ x) (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T ua αa) *
      inner ℝ (r2WindowFeature C ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp c) b σ x) (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T uc αc) =
      gradComp c (propagatorW C σ (b + ua) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αa)) x *
        gradComp c (propagatorW C σ (b + uc) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αc)) x := by
    intro c x
    rw [(s105_pair_all hS hb hua c hσT x αa).1, (s105_pair_all hS hb huc c hσT x αc).1, if_pos hσa, if_pos hσb]
  simp only [← hCdef]
  simp_rw [hpair]
  have hint : ∀ c : Fin d, Integrable (fun x => ρ x *
      (gradComp c (propagatorW C σ (b + ua) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αa)) x *
        gradComp c (propagatorW C σ (b + uc) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αc)) x)) volume := by
    intro c
    refine Integrable.mono' (g := fun x => (|Ba| * |Bb|) * |ρ x|) ?_ ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((s56_integrable_of_prob hρ).abs).const_mul _
    · have hca := s56_gradComp_cont ((hcla.c2 σ ⟨hσ.1, hσa⟩).of_le (by norm_num)) c
      have hcb := s56_gradComp_cont ((hclb.c2 σ ⟨hσ.1, hσb⟩).of_le (by norm_num)) c
      exact (hρ.measurable.mul (hca.mul hcb).measurable).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 := hBa σ ⟨hσ.1, hσa⟩ c x
      have h2 := hBb σ ⟨hσ.1, hσb⟩ c x
      have h3 : |gradComp c (propagatorW C σ (b + ua) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αa)) x| ≤ |Ba| := h1.trans (le_abs_self _)
      have h4 : |gradComp c (propagatorW C σ (b + uc) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αc)) x| ≤ |Bb| := h2.trans (le_abs_self _)
      calc |ρ x| * (|gradComp c (propagatorW C σ (b + ua) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αa)) x| *
            |gradComp c (propagatorW C σ (b + uc) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αc)) x|)
          ≤ |ρ x| * (|Ba| * |Bb|) := by gcongr
        _ = _ := by ring
  congr 1
  simp_rw [mrr_integral_withDensityReal _ hρ.measurable hρ.nonneg]
  rw [← integral_finsetSum _ (fun c _ => hint c)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ∑ c : Fin d, ρ x * (gradComp c (propagatorW C σ (b + ua) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αa)) x *
      gradComp c (propagatorW C σ (b + uc) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αc)) x) =
    inner ℝ (gradient (propagatorW C σ (b + ua) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αa)) x)
      (gradient (propagatorW C σ (b + uc) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αc)) x) * ρ x
  rw [PiLp.inner_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [gradComp, RCLike.inner_apply, conj_trivial]
  ring

end HRS.MS.R2GenInit
