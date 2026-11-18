import HRS.MS.WsPrepM1

/-!
# S21S packet M2: the Gaussian martingale of the moving window and its finite-dimensional laws

Moving analogues of `s105_Db_dir_zero`, `s105_recon_coord_eq`, `s105_noiseCov_eq`, `s105_Gb_fdd` (R2GenInitAux30/31): for a Gaussian martingale `G` with covariation density
`s21mDb` on `[0,b+T]`, `coord_α (𝒯 G)(u) = ⟨G_{b+u}, y1(u,α)⟩` a.s., and the vector `(⟨G_{b+u_a}, y1(u_a,α_a)⟩)_a` is a centered Gaussian with
covariance `noiseCovW C q (b+u_a) (b+u_c)`; `s21m_noiseCov_psd`: that matrix is positive semidefinite.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S21m

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.GenPath HRS.MS.S52 HRS.MP.RdRem HRS.MH.DualityRd HRS.MS.R2GenInit
  HRS.Uniform.Q54c HRS.GF

variable {d : ℕ}

theorem S21mData.hpAll {s a β T b : ℝ} {ρ : ℝ → Euc d → ℝ} (h : S21mData d s a β T b ρ) :
    ∀ r ∈ Set.Icc (0 : ℝ) (b + T), HRS.Whole.IsProbDensity (ρ r) := fun _ hr => h.hprob hr

theorem s21m_pair_all {s a β T b : ℝ} {ρ : ℝ → Euc d → ℝ} (hS : S21mData d s a β T b ρ) (hb : 0 ≤ b) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) T) (a' : Fin d) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) (b + T)) (x : Euc d)
    (α : MultiIndex d) :
    inner ℝ (r2WindowFeature ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T
        (gradComp a') b r x) (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T u α) =
      (if r ≤ b + u then gradComp a' (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r (b + u)
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)) x else gradComp a' (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) x) ∧
    inner ℝ (r2WindowFeature ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T
        (gradComp a') b r x) (s52y2 ((wholeSpaceIndex d : ℕ) : ℝ) T α) =
      (if b ≤ r then gradComp a' (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) x else 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := hS.hK a' r hr x
  exact ⟨s105_pair_y1 _ hS.hC hb hr.1 hr.2 hu a' x h1 h3 h4 α, s105_pair_y2 _ _ T b r a' x h1 h2 h4 α⟩

theorem s21m_Db_dir_zero {s a β T b : ℝ} {ρ : ℝ → Euc d → ℝ} (hS : S21mData d s a β T b ρ) (hb : 0 ≤ b)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) (α : MultiIndex d) (q : ℝ) (hq : 0 ≤ q) :
    ∀ σ ∈ Set.Ioc (b + u) (b + T), s21mDb _ hS.hF hS.hpAll q hq σ
      (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T u α - s52y2 ((wholeSpaceIndex d : ℕ) : ℝ) T α)
      (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T u α - s52y2 ((wholeSpaceIndex d : ℕ) : ℝ) T α) = 0 := by
  intro σ hσ
  have hσ' : σ ∈ Set.Icc (0 : ℝ) (b + T) := ⟨by linarith [hu.1, hσ.1], hσ.2⟩
  rw [(s21mDb_spec _ hS.hF hS.hpAll q hq hσ').1]
  unfold featureForm
  have hz : ∀ (a' : Fin d) (x : Euc d), inner ℝ (r2WindowFeature
      ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp a') b σ x)
      (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T u α - s52y2 ((wholeSpaceIndex d : ℕ) : ℝ) T α) = 0 := by
    intro a' x
    obtain ⟨e1, e2⟩ := s21m_pair_all hS hb hu a' hσ' x α
    rw [inner_sub_right, e1, e2, if_neg (not_le.2 hσ.1), if_pos (by linarith [hu.1, hσ.1]), sub_self]
  simp [hz]

theorem s21m_recon_coord_eq {s a β T b : ℝ} {ρ : ℝ → Euc d → ℝ} (hS : S21mData d s a β T b ρ) (hb : 0 ≤ b)
    (q : ℝ) (hq : 0 ≤ q) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {G : ℝ → Ω → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T}
    (hG : IsHilbertMartingaleWithCovariation P ℱ (b + T) G (fun r _ =>
      s21mDb _ hS.hF hS.hpAll q hq r))
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) (α : MultiIndex d) :
    ∀ᵐ ζ ∂P, OscDual.coord (reconstructPath ((wholeSpaceIndex d : ℕ) : ℝ) T (fun τ ζ => G (b + τ) ζ) ζ u) α =
      inner ℝ (G (b + u) ζ) (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T u α) := by
  have h := s56_incr_zero hG (t := b + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T u α - s52y2 ((wholeSpaceIndex d : ℕ) : ℝ) T α)
    (s21m_Db_dir_zero hS hb hu α q hq)
  filter_upwards [h] with ζ hζ
  rw [s52_coord_recon hu.1 hu.2 (fun τ ζ => G (b + τ) ζ) ζ α]
  simp only [inner_sub_right] at hζ
  linarith

theorem s21m_noiseCov_eq {s a β T b : ℝ} {ρ : ℝ → Euc d → ℝ} (hS : S21mData d s a β T b ρ) (hb : 0 ≤ b)
    (q : ℝ) (hq : 0 ≤ q) {ua uc : ℝ} (hua : ua ∈ Set.Icc (0 : ℝ) T) (huc : uc ∈ Set.Icc (0 : ℝ) T)
    (αa αc : MultiIndex d) :
    ∫ σ in Set.Icc (0 : ℝ) (min (b + ua) (b + uc)), s21mDb _ hS.hF hS.hpAll q hq σ
      (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T ua αa) (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T uc αc) =
      noiseCovW ((quadraticGradientDyn d s a β).coeff ρ) q (b + ua) (b + uc)
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αa) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αc) := by
  set C := (quadraticGradientDyn d s a β).coeff ρ with hCdef
  have hρC : ∀ r x, C.ρ r x = ρ r x := fun r x => rfl
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
  have hρ := hS.hprob hσT
  haveI := HRS.MS.Thm.cb_withDensityReal_isProb hρ
  rw [(s21mDb_spec _ hS.hF hS.hpAll q hq hσT).1]
  unfold featureForm
  beta_reduce
  have hpair : ∀ (c : Fin d) (x : Euc d), inner ℝ (r2WindowFeature C ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp c) b σ x) (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T ua αa) *
      inner ℝ (r2WindowFeature C ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp c) b σ x) (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T uc αc) =
      gradComp c (propagatorW C σ (b + ua) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αa)) x *
        gradComp c (propagatorW C σ (b + uc) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αc)) x := by
    intro c x
    rw [(s21m_pair_all hS hb hua c hσT x αa).1, (s21m_pair_all hS hb huc c hσT x αc).1, if_pos hσa, if_pos hσb]
  simp only [← hCdef]
  simp_rw [hpair]
  have hint : ∀ c : Fin d, Integrable (fun x => ρ σ x *
      (gradComp c (propagatorW C σ (b + ua) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αa)) x *
        gradComp c (propagatorW C σ (b + uc) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αc)) x)) volume := by
    intro c
    refine Integrable.mono' (g := fun x => (|Ba| * |Bb|) * |ρ σ x|) ?_ ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((s56_integrable_of_prob hρ).abs).const_mul _
    · have hca := s56_gradComp_cont ((hcla.c2 σ ⟨hσ.1, hσa⟩).of_le (by norm_num)) c
      have hcb := s56_gradComp_cont ((hclb.c2 σ ⟨hσ.1, hσb⟩).of_le (by norm_num)) c
      exact (hρ.measurable.mul (hca.mul hcb).measurable).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 := hBa σ ⟨hσ.1, hσa⟩ c x
      have h2 := hBb σ ⟨hσ.1, hσb⟩ c x
      have h3 : |gradComp c (propagatorW C σ (b + ua) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αa)) x| ≤ |Ba| := h1.trans (le_abs_self _)
      have h4 : |gradComp c (propagatorW C σ (b + uc) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αc)) x| ≤ |Bb| := h2.trans (le_abs_self _)
      calc |ρ σ x| * (|gradComp c (propagatorW C σ (b + ua) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αa)) x| *
            |gradComp c (propagatorW C σ (b + uc) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αc)) x|)
          ≤ |ρ σ x| * (|Ba| * |Bb|) := by gcongr
        _ = _ := by ring
  congr 1
  simp_rw [mrr_integral_withDensityReal _ hρ.measurable hρ.nonneg]
  rw [← integral_finsetSum _ (fun c _ => hint c)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ∑ c : Fin d, ρ σ x * (gradComp c (propagatorW C σ (b + ua) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αa)) x *
      gradComp c (propagatorW C σ (b + uc) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αc)) x) =
    inner ℝ (gradient (propagatorW C σ (b + ua) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αa)) x)
      (gradient (propagatorW C σ (b + uc) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) αc)) x) * ρ σ x
  rw [PiLp.inner_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [gradComp, RCLike.inner_apply, conj_trivial]
  ring

theorem s21m_Gb_fdd {s a β T b : ℝ} {ρ : ℝ → Euc d → ℝ} (hS : S21mData d s a β T b ρ) (hb : 0 ≤ b) (hT : 0 < T)
    (q : ℝ) (hq : 0 ≤ q)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {G : ℝ → Ω → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T}
    (hG : IsHilbertMartingaleWithCovariation P ℱ (b + T) G (fun r _ =>
      s21mDb _ hS.hF hS.hpAll q hq r))
    (hGc : ∀ ζ, Continuous fun t => G t ζ) (hGz : ∀ ζ, G 0 ζ = 0) (hGm : ∀ t, Measurable (G t))
    {p : ℕ} (us : Fin p → ℝ) (hus : ∀ a, us a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d) :
    P.map (fun ζ => (WithLp.toLp 2 fun a => inner ℝ (G (b + us a) ζ)
        (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a)) : EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (Matrix.of fun i j => noiseCovW ((quadraticGradientDyn d s a β).coeff ρ) q
        (b + us i) (b + us j) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs i))
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j))) := by
  have hτ : 0 < b + T := by linarith
  have hts : ∀ a, b + us a ∈ Set.Icc (0 : ℝ) (b + T) := fun a =>
    ⟨by linarith [(hus a).1], by linarith [(hus a).2]⟩
  set ys : Fin p → ℝ → KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T := fun a _ =>
    s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a) with hys
  set B : ℝ := ∑ a, ‖s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a)‖ with hB
  have hXm : Measurable fun ζ => (WithLp.toLp 2 fun a => inner ℝ (G (b + us a) ζ)
      (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a)) : EuclideanSpace ℝ (Fin p)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => (hGm _).inner measurable_const)
  have h := gfb4_vec_gaussian hG hGc hGz hτ (fun a => b + us a) hts ys (B := B)
    (fun a σ _ => by
      show ‖s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a)‖ ≤ B
      exact Finset.single_le_sum (f := fun a => ‖s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a)‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ a))
    (fun a x => (continuousOn_const : ContinuousOn (fun _ : ℝ =>
      inner ℝ (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a)) x) (Set.Icc 0 (b + us a)))) _ hXm
    (fun a => by
      have : ∀ N' ζ, ‖(WithLp.toLp 2 fun a => inner ℝ (G (b + us a) ζ)
          (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a)) : EuclideanSpace ℝ (Fin p)) a -
          isum (fun σ => G σ ζ) (ys a) (b + T) (b + us a) N'‖ₑ ^ 2 = 0 := by
        intro N' ζ
        have e := s56_isum_const (fun σ => G σ ζ) (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a)) (hts a) N'
        have e2 : isum (fun σ => G σ ζ) (ys a) (b + T) (b + us a) N' =
            inner ℝ (G (b + us a) ζ) (s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a)) := by
          rw [show ys a = fun _ => s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us a) (αs a) from rfl, e, hGz]; simp
        rw [e2]
        simp
      simp_rw [this]
      simp)
  rw [h]
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  have := s21m_noiseCov_eq hS hb q hq (hus i) (hus j) (αs i) (αs j)
  simpa [min_def, ys] using this


theorem s21m_noiseCov_psd {s a β T b : ℝ} {ρ : ℝ → Euc d → ℝ} (hS : S21mData d s a β T b ρ) (hb : 0 ≤ b)
    (hT : 0 < T) (q : ℝ) (hq : 0 ≤ q) {p : ℕ} (us : Fin p → ℝ) (hus : ∀ a, us a ∈ Set.Icc (0 : ℝ) T)
    (αs : Fin p → MultiIndex d) :
    (Matrix.of fun i j => noiseCovW ((quadraticGradientDyn d s a β).coeff ρ) q
        (b + us i) (b + us j) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs i))
        (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j))).PosSemidef := by
  have hτ : 0 ≤ b + T := by linarith
  have hDet := s21mDb_isDet hτ _ hS.hF hS.hpAll hS.hρm q hq
  exact s21m_psd_of_entries hDet (fun i => b + us i)
    (fun i => ⟨by linarith [(hus i).1], by linarith [(hus i).2]⟩)
    (fun i => s52y1 ((wholeSpaceIndex d : ℕ) : ℝ) T (us i) (αs i)) _
    (fun i j => (s21m_noiseCov_eq hS hb q hq (hus i) (hus j) (αs i) (αs j)).symm)

end HRS.MS.S21m
