import HRS.MS.FinNoiseAux33
import HRS.MS.FinNoiseAux34
import HRS.Whole.Adjoint

/-!
# S8.6 `finite_noise`: the localised Fourier synthesis of one chart (Pro FR05) (S86b)

`s86_localized`: for a chart `F(u) = xc + A u` (`A` injective, `‖A‖ ≤ C_A`), a smooth cutoff `χ` with
`tsupport χ ⊆ F(int Q)` whose pull-back `χ ∘ F` has derivatives bounded by `Cχ l`, and a `C^r` function `Γ : ℝ^d → K` with
`⟨x⟩^p ‖D^l Γ(x)‖ ≤ C_Γ` (`l ≤ r`, `r > d`), there is a bounded `R : ℓ²(ℤ^d) → K` with
`R (chartFeature r (mk u)) = χ(F u) Γ(F u)` on the closed cube `Q = [-1/2,1/2]^d` and
`‖R‖² ≤ C₀ ⟨xc⟩^{-2p}`, `C₀ = s86_locC …` depending only on `d, r, p, C_A, C_Γ, Cχ`.
Route: Leibniz and chain-rule bounds, `⟨xc⟩ ≤ (1 + C_A d)⟨F u⟩` on the cube, zero-collar periodisation (Aux34), synthesis (Aux33).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

namespace HRS.MS.FinNoise

open HRS HRS.Torus HRS.Uniform HRS.Whole

variable {d : ℕ}

theorem s86_jb_le (x y : Euc d) : jbracket x ≤ jbracket (x + y) + ‖y‖ := by
  unfold jbracket
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 : ‖x‖ ≤ ‖x + y‖ + ‖y‖ := by
    have := norm_sub_le (x + y) y
    simpa using this
  have h2 : ‖x + y‖ ≤ Real.sqrt (1 + ‖x + y‖ ^ 2) := by
    calc ‖x + y‖ = Real.sqrt (‖x + y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖x + y‖])
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + ‖x + y‖ ^ 2 by positivity)
  have h4 : ‖x‖ ^ 2 ≤ (‖x + y‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [mul_nonneg (norm_nonneg y) (norm_nonneg (x + y)), norm_nonneg y,
    mul_le_mul_of_nonneg_left h2 (norm_nonneg y)]

theorem s86_jb_ge_one (x : Euc d) : 1 ≤ jbracket x := by
  unfold jbracket
  calc (1 : ℝ) = Real.sqrt 1 := by simp
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖x‖])

theorem s86_cube_norm_le {u : Euc d} (hu : ∀ i, |u i| ≤ 1 / 2) : ‖u‖ ≤ (d : ℝ) := by
  have h1 : ∀ i, ‖u i‖ ^ 2 ≤ 1 / 4 := by
    intro i
    have := hu i
    rw [Real.norm_eq_abs, sq_abs]
    nlinarith [abs_nonneg (u i), sq_abs (u i)]
  have h2 : ‖u‖ ^ 2 ≤ (d : ℝ) / 4 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖u i‖ ^ 2 ≤ ∑ _i : Fin d, (1 / 4 : ℝ) := Finset.sum_le_sum (fun i _ => h1 i)
      _ = (d : ℝ) / 4 := by simp [div_eq_inv_mul]; ring
  have h3 : (d : ℝ) / 4 ≤ (d : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos d with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ d := by exact_mod_cast h
      nlinarith
  exact le_of_sq_le_sq (h2.trans h3) (Nat.cast_nonneg d)

theorem s86_interior_cube {u : Euc d}
    (hu : u ∈ interior {u : Euc d | ∀ i, |u i| ≤ 1 / 2}) : ∀ i, |u i| < 1 / 2 := by
  classical
  intro i
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hu)
  set v : Euc d := EuclideanSpace.single i (ε / 2) with hv
  have hvn : ‖v‖ = ε / 2 := by
    rw [hv, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h1 : u + v ∈ Metric.ball u ε := by
    rw [mem_ball_iff_norm]; simp only [add_sub_cancel_left]; rw [hvn]; linarith
  have h2 : u - v ∈ Metric.ball u ε := by
    rw [mem_ball_iff_norm]; simp only [sub_sub_cancel_left, norm_neg]; rw [hvn]; linarith
  have e1 := hball h1 i
  have e2 := hball h2 i
  have hvi : v i = ε / 2 := by simp [hv]
  simp only [PiLp.add_apply, PiLp.sub_apply, hvi] at e1 e2
  rw [abs_le] at e1 e2
  rw [abs_lt]
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]

/-- The explicit bound for the `l`-th derivative of the localised feature (without the weight). -/
def s86_locM (CA CΓ P : ℝ) (Cχ : ℕ → ℝ) (l : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * Cχ i * CA ^ (l - i)) * (CΓ * P)

/-- The constant of the squared operator norm. -/
def s86_locC (d r : ℕ) (CA CΓ P : ℝ) (Cχ : ℕ → ℝ) : ℝ :=
  ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ) * (d : ℝ) ^ l * (s86_locM CA CΓ P Cχ l) ^ 2

theorem s86_localized (r : ℕ) (hr : d < r) (p : ℝ) (hp : 0 ≤ p) {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] [CompleteSpace K] {ι : Type*} (b : HilbertBasis ι ℝ K)
    (Γ : Euc d → K) (hΓd : ContDiff ℝ r Γ) (CΓ : ℝ)
    (hΓb : ∀ l ≤ r, ∀ x, jbracket x ^ p * ‖iteratedFDeriv ℝ l Γ x‖ ≤ CΓ)
    (CA : ℝ) (Cχ : ℕ → ℝ) (xc : Euc d) (A : Euc d →L[ℝ] Euc d) (hAinj : Function.Injective A)
    (hA : ‖A‖ ≤ CA) (χ : Euc d → ℝ) (hχ : ContDiff ℝ r χ)
    (hχs : tsupport χ ⊆ (fun u => xc + A u) '' interior {u : Euc d | ∀ i, |u i| ≤ 1 / 2})
    (hχd : ∀ l ≤ r, ∀ u, ‖iteratedFDeriv ℝ l (fun u' => χ (xc + A u')) u‖ ≤ Cχ l) :
    ∃ R : FeatureSpace d →L[ℝ] K,
      (∀ u : Euc d, (∀ i, |u i| ≤ 1 / 2) →
        R (chartFeature (d := d) r (Torus.mk u)) = χ (xc + A u) • Γ (xc + A u)) ∧
      ‖R‖ ^ 2 ≤ s86_locC d r CA ((CΓ)) ((1 + CA * d) ^ p) Cχ * jbracket xc ^ (-(2 * p)) := by
  classical
  have hCA0 : 0 ≤ CA := (norm_nonneg _).trans hA
  have hCΓ0 : 0 ≤ CΓ := by
    have := hΓb 0 (Nat.zero_le _) 0
    exact (mul_nonneg (Real.rpow_nonneg (by linarith [s86_jb_ge_one (0 : Euc d)]) _)
      (norm_nonneg _)).trans this
  have hCχ0 : ∀ l ≤ r, 0 ≤ Cχ l := fun l hl => (norm_nonneg _).trans (hχd l hl 0)
  set P : ℝ := (1 + CA * d) ^ p with hP
  have hP0 : 0 ≤ P := by positivity
  set F : Euc d → Euc d := fun u => xc + A u with hF
  have hFd : ContDiff ℝ r F := contDiff_const.add A.contDiff
  set g : Euc d → K := fun u => χ (F u) • Γ (F u) with hg
  have hgd : ContDiff ℝ r g := (hχ.comp hFd).smul (hΓd.comp hFd)
  -- support
  have hts : tsupport g ⊆ interior {u : Euc d | ∀ i, |u i| ≤ 1 / 2} := by
    have h1 : tsupport g ⊆ F ⁻¹' tsupport χ := by
      refine closure_minimal ?_ ((isClosed_tsupport χ).preimage hFd.continuous)
      intro u hu
      have : χ (F u) ≠ 0 := by
        intro h; exact hu (by simp [hg, h])
      exact subset_tsupport _ this
    intro u hu
    obtain ⟨u', hu', hu'e⟩ := hχs (h1 hu)
    have : u' = u := hAinj (add_left_cancel hu'e)
    rwa [← this]
  have hcube : ∀ u ∈ tsupport g, ∀ i, |u i| < 1 / 2 := fun u hu => s86_interior_cube (hts hu)
  have hcomp : HasCompactSupport g := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Euc d) (d : ℝ)) (isClosed_tsupport g) ?_
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right]
    exact s86_cube_norm_le fun i => (hcube u hu i).le
  -- derivative bound
  have hbound : ∀ l ≤ r, ∀ u, ‖iteratedFDeriv ℝ l g u‖ ≤ s86_locM CA CΓ P Cχ l * jbracket xc ^ (-p) := by
    intro l hl u
    by_cases hu : u ∈ tsupport g
    swap
    · have : u ∉ Function.support (iteratedFDeriv ℝ l g) := fun h => hu (support_iteratedFDeriv_subset l h)
      have h0 : iteratedFDeriv ℝ l g u = 0 := by simpa using this
      rw [h0, norm_zero]
      have : 0 ≤ s86_locM CA CΓ P Cχ l := by
        unfold s86_locM
        refine mul_nonneg (Finset.sum_nonneg fun i hi => ?_) (mul_nonneg hCΓ0 hP0)
        have : i ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCχ0 i (this.trans hl))) (pow_nonneg hCA0 _)
      exact mul_nonneg this (Real.rpow_nonneg (by linarith [s86_jb_ge_one xc]) _)
    have hun : ‖u‖ ≤ (d : ℝ) := s86_cube_norm_le fun i => (hcube u hu i).le
    -- Peetre
    have hpeet : jbracket (F u) ^ (-p) ≤ P * jbracket xc ^ (-p) := by
      have h1 : jbracket xc ≤ (1 + CA * d) * jbracket (F u) := by
        have := s86_jb_le xc (A u)
        have h2 : ‖A u‖ ≤ CA * d := by
          calc ‖A u‖ ≤ ‖A‖ * ‖u‖ := A.le_opNorm u
            _ ≤ CA * d := mul_le_mul hA hun (norm_nonneg _) hCA0
        have h3 := s86_jb_ge_one (F u)
        have h4 : jbracket xc ≤ jbracket (F u) + ‖A u‖ := this
        nlinarith [mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ CA * d by positivity)]
      have hc : 0 < 1 + CA * d := by positivity
      have hjx : 0 < jbracket xc := by linarith [s86_jb_ge_one xc]
      have hjF : 0 < jbracket (F u) := by linarith [s86_jb_ge_one (F u)]
      -- (1+CA d)^{-1} jb xc ≤ jb (F u)
      have h5 : jbracket xc / (1 + CA * d) ≤ jbracket (F u) := by
        rw [div_le_iff₀ hc]; linarith
      calc jbracket (F u) ^ (-p) ≤ (jbracket xc / (1 + CA * d)) ^ (-p) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) h5 (by linarith)
        _ = P * jbracket xc ^ (-p) := by
            rw [Real.div_rpow hjx.le hc.le, Real.rpow_neg hc.le, Real.rpow_neg hjx.le, hP]
            field_simp
    -- Leibniz
    have hχF : ContDiff ℝ r (fun u' => χ (xc + A u')) := hχ.comp hFd
    have hΓF : ContDiff ℝ r (fun u' => Γ (xc + A u')) := hΓd.comp hFd
    have hgB : g = fun y => (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] K →L[ℝ] K)
        (χ (xc + A y)) (Γ (xc + A y)) := by
      funext y; simp [hg, hF]
    have hLeib := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] K →L[ℝ] K).norm_iteratedFDeriv_le_of_bilinear
      hχF hΓF u (n := l) (by exact_mod_cast hl)
    rw [← hgB] at hLeib
    have hls : ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] K →L[ℝ] K)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_lsmul_le
    -- the chain rule for Γ
    have hchain : ∀ j ≤ r, ‖iteratedFDeriv ℝ j (fun u' => Γ (xc + A u')) u‖ ≤
        CA ^ j * (CΓ * P * jbracket xc ^ (-p)) := by
      intro j hj
      have e1 : (fun u' => Γ (xc + A u')) = (fun z => Γ (xc + z)) ∘ (A : Euc d → Euc d) := rfl
      have hf : ContDiff ℝ r (fun z => Γ (xc + z)) := hΓd.comp (contDiff_const.add contDiff_id)
      have e2 := A.iteratedFDeriv_comp_right hf u (i := j) (by exact_mod_cast hj)
      rw [e1, e2]
      have e3 : iteratedFDeriv ℝ j (fun z => Γ (xc + z)) (A u) = iteratedFDeriv ℝ j Γ (xc + A u) :=
        iteratedFDeriv_comp_add_left j xc (A u)
      rw [e3]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      have e4 : ∏ _i : Fin j, ‖A‖ = ‖A‖ ^ j := by simp
      rw [e4]
      have h1 : ‖iteratedFDeriv ℝ j Γ (F u)‖ ≤ CΓ * jbracket (F u) ^ (-p) := by
        have := hΓb j hj (F u)
        have hjF : 0 < jbracket (F u) := by linarith [s86_jb_ge_one (F u)]
        rw [Real.rpow_neg hjF.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hjF _)]
        linarith
      calc ‖iteratedFDeriv ℝ j Γ (F u)‖ * ‖A‖ ^ j
          ≤ (CΓ * jbracket (F u) ^ (-p)) * CA ^ j :=
            mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) hA j) (pow_nonneg (norm_nonneg _) _)
              (mul_nonneg hCΓ0 (Real.rpow_nonneg (by linarith [s86_jb_ge_one (F u)]) _))
        _ ≤ (CΓ * (P * jbracket xc ^ (-p))) * CA ^ j := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpeet hCΓ0) (pow_nonneg hCA0 _)
        _ = CA ^ j * (CΓ * P * jbracket xc ^ (-p)) := by ring
    refine hLeib.trans ?_
    have hterm : ∀ i ∈ Finset.range (l + 1),
        (l.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun u' => χ (xc + A u')) u‖ *
          ‖iteratedFDeriv ℝ (l - i) (fun u' => Γ (xc + A u')) u‖ ≤
        (l.choose i : ℝ) * Cχ i * (CA ^ (l - i) * (CΓ * P * jbracket xc ^ (-p))) := by
      intro i hi
      have hil : i ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have a1 := hχd i (hil.trans hl) u
      have a2 := hchain (l - i) ((Nat.sub_le l i).trans hl)
      have hch : (0 : ℝ) ≤ (l.choose i : ℝ) := Nat.cast_nonneg _
      exact mul_le_mul (mul_le_mul_of_nonneg_left a1 hch) a2 (norm_nonneg _)
        (mul_nonneg hch (hCχ0 i (hil.trans hl)))
    have hsum := Finset.sum_le_sum hterm
    have heq : ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * Cχ i *
        (CA ^ (l - i) * (CΓ * P * jbracket xc ^ (-p))) =
        s86_locM CA CΓ P Cχ l * jbracket xc ^ (-p) := by
      unfold s86_locM
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hmul := mul_le_mul hls hsum (Finset.sum_nonneg fun i _ => by positivity) zero_le_one
    rw [one_mul, heq] at hmul
    exact hmul
  -- periodise and synthesise
  obtain ⟨G, hGper, hGd, hGeq, hGb⟩ := s86_periodize g r hgd hcomp (fun u hu => hcube u hu)
  have hjxpos : 0 < jbracket xc := by linarith [s86_jb_ge_one xc]
  have hMnn : ∀ l ≤ r, 0 ≤ s86_locM CA CΓ P Cχ l * jbracket xc ^ (-p) := by
    intro l hl
    have : 0 ≤ s86_locM CA CΓ P Cχ l := by
      unfold s86_locM
      refine mul_nonneg (Finset.sum_nonneg fun i hi => ?_) (mul_nonneg hCΓ0 hP0)
      have : i ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCχ0 i (this.trans hl))) (pow_nonneg hCA0 _)
    exact mul_nonneg this (Real.rpow_nonneg hjxpos.le _)
  have hGB : ∀ l ≤ r, ∀ y, ‖iteratedFDeriv ℝ l G y‖ ≤ s86_locM CA CΓ P Cχ l * jbracket xc ^ (-p) :=
    fun l hl y => hGb l hl _ (hMnn l hl) (hbound l hl) y
  obtain ⟨R, hR, hRn⟩ := s86_synthesis r hr b G hGper hGd (fun l => s86_locM CA CΓ P Cχ l * jbracket xc ^ (-p)) hGB
  refine ⟨R, fun u hu => ?_, ?_⟩
  · rw [hR u, hGeq u hu]
  · refine hRn.trans (le_of_eq ?_)
    unfold s86_locC
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    have : (jbracket xc ^ (-p)) ^ 2 = jbracket xc ^ (-(2 * p)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hjxpos.le]
      congr 1; push_cast; ring
    rw [mul_pow, this]; ring

end HRS.MS.FinNoise
