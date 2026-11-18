import HRS.MS.WadAux170

/-!
# S8.3, packet S8H-2: cutoffs, mollification and discretization on a finite dimensional space

Generic (`E` finite dimensional, arbitrary positive weight `w`) versions of the S8F cutoff lemmas (`s8h_cutoff`, `s8h_cutoff_error`), the
convolution `s8h_Conv f g z = ∫ f(u) g(z-u) du` with its derivative (`s8h_Conv_hasFDerivAt`), the mollification error (`s8h_Conv_err`) and the
discretization error of a convolution by a finite sum of translates of the kernel (`s8h_disc_err`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff Convolution

namespace HRS.MS.Wad

open HRS HRS.Whole

section Mollify

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem s8h_cutoff (k : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 1 ≤ R → ∃ χ : E → ℝ,
    ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ (∀ x, ‖x‖ < 2 * R → χ x = 1) ∧
    (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B) := by
  let ψ : ContDiffBump (0 : E) := ⟨2, 3, by norm_num, by norm_num⟩
  have hb : ∀ i : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ i (⇑ψ) x‖ ≤ C := fun i =>
    (ψ.contDiff.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (ψ.hasCompactSupport.iteratedFDeriv i)
  choose C hC using hb
  refine ⟨∑ i ∈ Finset.range (k + 1), |C i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun R hR => ?_⟩
  have hR0 : 0 < R := by linarith
  have hRi : 0 < R⁻¹ := inv_pos.2 hR0
  refine ⟨fun x => ψ (R⁻¹ • x), ψ.contDiff.comp (contDiff_const_smul _), ?_, fun x hx => ?_,
    fun x => ⟨ψ.nonneg, ψ.le_one⟩, fun i hi x => ?_⟩
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : E) (3 * R)) fun x hx => ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    refine ψ.zero_of_le_dist ?_
    show (3 : ℝ) ≤ dist (R⁻¹ • x) 0
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hRi]
    rw [inv_mul_eq_div, le_div_iff₀ hR0]
    linarith
  · refine ψ.one_of_mem_closedBall ?_
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hRi]
    show R⁻¹ * ‖x‖ ≤ 2
    rw [inv_mul_eq_div, div_le_iff₀ hR0]
    linarith
  · rw [iteratedFDeriv_comp_const_smul R⁻¹ (ψ.contDiff (n := i)), norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hRi i)]
    have h1 : R⁻¹ ^ i ≤ 1 := pow_le_one₀ hRi.le (inv_le_one_of_one_le₀ hR)
    have h2 : ‖iteratedFDeriv ℝ i (⇑ψ) (R⁻¹ • x)‖ ≤ ∑ j ∈ Finset.range (k + 1), |C j| :=
      (hC i _).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun j => |C j|)
        (fun j _ => abs_nonneg _) (Finset.mem_range.2 (by omega))))
    calc R⁻¹ ^ i * ‖iteratedFDeriv ℝ i (⇑ψ) (R⁻¹ • x)‖ ≤ 1 * ∑ j ∈ Finset.range (k + 1), |C j| :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _

theorem s8h_cutoff_error {w : E → ℝ} (hwp : ∀ x, 0 < w x) {k : ℕ} {f : E → ℝ} (hf : ContDiff ℝ k f)
    (hdec : ∀ i ≤ k, Tendsto (fun x => ‖iteratedFDeriv ℝ i f x‖ / w x) (cocompact (E)) (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i (fun y => χ y * f y - f y) x‖ ≤ ε * w x := by
  obtain ⟨B, hB0, hχ⟩ := s8h_cutoff (E := E) k
  set Cχ : ℝ := (B + 1) * 2 ^ k with hCχ
  have hCχ0 : 0 < Cχ := by positivity
  set ε' : ℝ := ε / Cχ with hε'
  have hε'0 : 0 < ε' := by positivity
  -- the tail
  have hev : ∀ᶠ z in cocompact (E), ∀ m ∈ Finset.range (k + 1),
      ‖iteratedFDeriv ℝ m f z‖ / w z < ε' := by
    rw [Filter.eventually_all_finset]
    intro m hm
    exact (hdec m (by simpa [Nat.lt_succ_iff] using hm)).eventually (gt_mem_nhds hε'0)
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.1 hev
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall (0 : E)
  set R : ℝ := max R₀ 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  have hR0 : 0 < R := by linarith
  have hfar : ∀ m ≤ k, ∀ z : E, R < ‖z‖ → ‖iteratedFDeriv ℝ m f z‖ ≤ ε' * w z := by
    intro m hm z hz
    have hzK : z ∉ K := fun h => by
      have := hR₀ h
      rw [Metric.mem_closedBall, dist_zero_right] at this
      have := le_max_left R₀ 1
      linarith
    have := hKs hzK m (Finset.mem_range.2 (by omega))
    have hp : 0 < w z := hwp z
    rw [div_lt_iff₀ hp] at this
    exact this.le
  obtain ⟨χ, hχd, hχc, hχ1, hχb, hχD⟩ := hχ R hR1
  refine ⟨χ, hχd, hχc, fun i hi x => ?_⟩
  by_cases hx : ‖x‖ ≤ R
  · -- near `x` the cutoff is `1`
    have hnhds : {y : E | ‖y‖ < 2 * R} ∈ 𝓝 x := by
      refine IsOpen.mem_nhds (isOpen_lt continuous_norm continuous_const) ?_
      show ‖x‖ < 2 * R
      linarith
    have heq : (fun y => χ y * f y - f y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hnhds] with y hy
      rw [hχ1 y hy]; ring
    have := (Filter.EventuallyEq.iteratedFDeriv ℝ heq i).eq_of_nhds
    rw [this]
    have h0 : iteratedFDeriv ℝ i (fun _ : E => (0 : ℝ)) x = 0 := by
      by_cases hi0 : i = 0
      · subst hi0
        simp [iteratedFDeriv_zero_eq_comp]
      · rw [iteratedFDeriv_const_of_ne hi0]; rfl
    rw [h0, norm_zero]
    have := (hwp x).le
    positivity
  · push Not at hx
    have hcd : ContDiff ℝ (k : WithTop ℕ∞) (fun y => χ y - 1) :=
      ((hχd.of_le (by exact_mod_cast le_top)).sub contDiff_const)
    have hfk : ContDiff ℝ (k : WithTop ℕ∞) f := hf
    have e : (fun y => χ y * f y - f y) = fun y => (χ y - 1) * f y := by funext y; ring
    rw [e]
    have hLeib := norm_iteratedFDeriv_mul_le hcd hfk x (n := i) (by exact_mod_cast hi)
    refine hLeib.trans ?_
    have hbl : ∀ l ≤ i, ‖iteratedFDeriv ℝ l (fun y => χ y - 1) x‖ ≤ B + 1 := by
      intro l hl
      by_cases hl0 : l = 0
      · subst hl0
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hχb x |>.1, hχb x |>.2]
      · have hcl : ContDiff ℝ l χ := hχd.of_le (by exact_mod_cast le_top)
        have e2 : iteratedFDeriv ℝ l (fun y => χ y - 1) x = iteratedFDeriv ℝ l χ x := by
          have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := x) (i := l) (f := χ) (g := fun _ => (1 : ℝ))
            hcl.contDiffAt contDiff_const.contDiffAt
          simp only [Pi.sub_def] at this ⊢
          rw [this, iteratedFDeriv_const_of_ne hl0]
          simp
        rw [e2]
        exact (hχD l (hl.trans hi) x).trans (by linarith)
    calc ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fun y => χ y - 1) x‖ *
          ‖iteratedFDeriv ℝ (i - l) f x‖
        ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * ((B + 1) * (ε' * w x)) := by
          refine Finset.sum_le_sum fun l hl => ?_
          have hl' : l ≤ i := by simpa [Nat.lt_succ_iff] using hl
          have h1 := hbl l hl'
          have h2 := hfar (i - l) (by omega) x hx
          have h3 : 0 ≤ (i.choose l : ℝ) := Nat.cast_nonneg _
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) (by linarith)) h3
      _ = 2 ^ i * ((B + 1) * (ε' * w x)) := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose i
      _ ≤ 2 ^ k * ((B + 1) * (ε' * w x)) := by
          have hj := (hwp x).le
          have : 0 ≤ (B + 1) * (ε' * w x) := by positivity
          exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) this
      _ = ε * w x := by
          rw [hε', hCχ]; field_simp


theorem s8h_norm_iter_sub {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) (g : E → F) (x y : E) :
    ‖iteratedFDeriv ℝ k (fderiv ℝ g) x - iteratedFDeriv ℝ k (fderiv ℝ g) y‖ =
      ‖iteratedFDeriv ℝ (k + 1) g x - iteratedFDeriv ℝ (k + 1) g y‖ := by
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply]
  rw [← dist_eq_norm, ← dist_eq_norm, LinearIsometryEquiv.dist_map]

theorem s8h_norm_iter0_pts {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F) (x y : E) :
    ‖iteratedFDeriv ℝ 0 g x - iteratedFDeriv ℝ 0 g y‖ = ‖g x - g y‖ := by
  rw [iteratedFDeriv_zero_eq_comp]
  simp only [Function.comp_apply]
  rw [← dist_eq_norm, ← dist_eq_norm, LinearIsometryEquiv.dist_map]

end Mollify

section ConvZ

variable {d : ℕ}

instance s8h_inst_haar (d : ℕ) : (volume : Measure (Euc d × Euc d)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; infer_instance

instance s8h_inst_neg (d : ℕ) : (volume : Measure (Euc d × Euc d)).IsNegInvariant := by
  refine ⟨?_⟩
  have h := Measure.map_addHaar_smul (volume : Measure (Euc d × Euc d)) (r := (-1 : ℝ)) (by norm_num)
  have e : (fun x : Euc d × Euc d => (-1 : ℝ) • x) = fun x => -x := by funext x; simp
  rw [e] at h
  simp at h
  exact h

/-- Convolution `∫ f(u) g(z-u) du` on the pair space. -/
def s8h_Conv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Euc d × Euc d → ℝ)
    (g : Euc d × Euc d → F) : Euc d × Euc d → F :=
  fun z => ∫ u, f u • g (z - u)

theorem s8h_Conv_eq {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Euc d × Euc d → ℝ)
    (g : Euc d × Euc d → F) :
    s8h_Conv f g = (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g : Euc d × Euc d → F) := rfl

theorem s8h_Conv_hasFDerivAt {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Euc d × Euc d → ℝ}
    (hf : Continuous f) {g : Euc d × Euc d → F} (hc : HasCompactSupport g) (hg : ContDiff ℝ 1 g)
    (x : Euc d × Euc d) : HasFDerivAt (s8h_Conv f g) (s8h_Conv f (fderiv ℝ g) x) x := by
  have hli : LocallyIntegrable f (volume : Measure (Euc d × Euc d)) := hf.locallyIntegrable
  have := hc.hasFDerivAt_convolution_right (μ := (volume : Measure (Euc d × Euc d)))
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F) hli hg x
  refine this.congr_fderiv ?_
  unfold s8h_Conv
  simp only [convolution_def, ContinuousLinearMap.precompR_apply]
  congr 1

theorem s8h_Conv_err {κ : Euc d × Euc d → ℝ} (hκc : Continuous κ) (hκcs : HasCompactSupport κ)
    (hκ0 : ∀ u, 0 ≤ κ u) (hκ1 : ∫ u, κ u = 1) {r : ℝ} (hκs : ∀ u, κ u ≠ 0 → ‖u‖ < r) :
    ∀ (i : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (g : Euc d × Euc d → F), HasCompactSupport g → ContDiff ℝ i g → ∀ {ε : ℝ},
      (∀ x y, dist x y < r → ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ ≤ ε) → ∀ y,
      ‖iteratedFDeriv ℝ i (s8h_Conv κ g) y - iteratedFDeriv ℝ i g y‖ ≤ ε := by
  intro i
  induction i with
  | zero =>
    intro F _ _ _ g hc hg ε hmod y
    rw [s8h_norm_iter0_sub]
    have hgc : Continuous g := hg.continuous
    have hint : Integrable (fun u => κ u • g (y - u)) volume := by
      refine Continuous.integrable_of_hasCompactSupport (hκc.smul (hgc.comp (continuous_const.sub continuous_id))) ?_
      exact hκcs.smul_right
    have hκi : Integrable κ volume := hκc.integrable_of_hasCompactSupport hκcs
    have e1 : g y = ∫ u, κ u • g y := by
      rw [integral_smul_const, hκ1, one_smul]
    have e2 : s8h_Conv κ g y - g y = ∫ u, κ u • (g (y - u) - g y) := by
      unfold s8h_Conv
      conv_lhs => rw [e1]
      rw [← integral_sub hint (hκi.smul_const _)]
      congr 1; funext u; rw [smul_sub]
    rw [e2]
    have hb : ∀ u, ‖κ u • (g (y - u) - g y)‖ ≤ κ u * ε := by
      intro u
      by_cases hu : κ u = 0
      · simp [hu]
      · rw [norm_smul, Real.norm_of_nonneg (hκ0 u)]
        refine mul_le_mul_of_nonneg_left ?_ (hκ0 u)
        have := hmod (y - u) y (by rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hκs u hu)
        rwa [s8h_norm_iter0_pts] at this
    refine (norm_integral_le_of_norm_le (hκi.mul_const ε) (Filter.Eventually.of_forall hb)).trans ?_
    rw [integral_mul_const, hκ1, one_mul]
  | succ i ih =>
    intro F _ _ _ g hc hg ε hmod y
    have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_cast; omega)
    have hDg : ContDiff ℝ i (fderiv ℝ g) := hg.fderiv_right (by norm_cast)
    have hfd : fderiv ℝ (s8h_Conv κ g) = s8h_Conv κ (fderiv ℝ g) :=
      funext fun x => (s8h_Conv_hasFDerivAt hκc hc hg1 x).fderiv
    rw [← s8h_norm_iter_sub', hfd]
    refine ih (F := Euc d × Euc d →L[ℝ] F) (fderiv ℝ g) (hc.fderiv ℝ) hDg (fun x x' hxx => ?_) y
    rw [s8h_norm_iter_sub]
    exact hmod x x' hxx

theorem s8h_Conv_comm (f g : Euc d × Euc d → ℝ) (z : Euc d × Euc d) : s8h_Conv f g z = s8h_Conv g f z := by
  unfold s8h_Conv
  have := integral_sub_left_eq_self (fun u : Euc d × Euc d => f u • g (z - u)) (volume : Measure (Euc d × Euc d)) z
  simp only [sub_sub_cancel, smul_eq_mul] at this ⊢
  rw [← this]
  congr 1; funext u; ring

/-- A finite continuous partition of unity along `tsupport f`, subordinate to balls of radius `h`. -/
structure S8hPart (f : Euc d × Euc d → ℝ) (h : ℝ) {ι : Type} [Fintype ι] (θ : ι → Euc d × Euc d → ℝ)
    (zs : ι → Euc d × Euc d) : Prop where
  cont : ∀ l, Continuous (θ l)
  nonneg : ∀ l z, 0 ≤ θ l z
  le_one : ∀ z, ∑ l, θ l z ≤ 1
  eq_one : ∀ z, f z ≠ 0 → ∑ l, θ l z = 1
  small : ∀ l z, θ l z ≠ 0 → ‖z - zs l‖ < h

theorem s8h_part_exists {f : Euc d × Euc d → ℝ} (hfc : HasCompactSupport f) {h : ℝ} (hh : 0 < h) :
    ∃ (ι : Type) (_ : Fintype ι) (θ : ι → Euc d × Euc d → ℝ) (zs : ι → Euc d × Euc d), S8hPart f h θ zs := by
  classical
  have hK : IsCompact (tsupport f) := hfc
  obtain ⟨t, htK, htfin, hcov⟩ := finite_cover_balls_of_compact hK hh
  set t' : Finset (Euc d × Euc d) := htfin.toFinset with ht'
  obtain ⟨g, hg⟩ := PartitionOfUnity.exists_isSubordinate (ι := t') (X := Euc d × Euc d) (isClosed_tsupport f)
    (fun i : t' => Metric.ball (i : Euc d × Euc d) h) (fun i => Metric.isOpen_ball) (by
      intro x hx
      have := hcov hx
      simp only [Set.mem_iUnion] at this ⊢
      obtain ⟨y, hy, hxy⟩ := this
      exact ⟨⟨y, htfin.mem_toFinset.2 hy⟩, hxy⟩)
  refine ⟨t', inferInstance, fun i z => g i z, fun i => (i : Euc d × Euc d), ?_⟩
  refine ⟨fun l => (g l).continuous, fun l z => g.nonneg l z, fun z => ?_, fun z hz => ?_, fun l z hz => ?_⟩
  · have := g.sum_le_one z
    rwa [finsum_eq_sum_of_fintype] at this
  · have := g.sum_eq_one (subset_tsupport f (Function.mem_support.2 hz))
    rwa [finsum_eq_sum_of_fintype] at this
  · have := hg l (subset_tsupport _ (Function.mem_support.2 hz))
    rw [mem_ball, dist_eq_norm] at this
    exact this

/-- Translates of a kernel with the given weights. -/
def s8h_Disc {ι : Type} [Fintype ι] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (c : ι → ℝ)
    (zs : ι → Euc d × Euc d) (H : Euc d × Euc d → F) : Euc d × Euc d → F :=
  fun z => ∑ l, c l • H (z - zs l)

theorem s8h_Disc_hasFDerivAt {ι : Type} [Fintype ι] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : ι → ℝ) (zs : ι → Euc d × Euc d) {H : Euc d × Euc d → F} (hH : ContDiff ℝ 1 H) (z : Euc d × Euc d) :
    HasFDerivAt (s8h_Disc c zs H) (s8h_Disc c zs (fderiv ℝ H) z) z := by
  unfold s8h_Disc
  have : HasFDerivAt (fun z => ∑ l, c l • H (z - zs l)) (∑ l, c l • fderiv ℝ H (z - zs l)) z := by
    refine HasFDerivAt.fun_sum fun l _ => ?_
    have h1 : HasFDerivAt (fun z : Euc d × Euc d => z - zs l) (ContinuousLinearMap.id ℝ _) z :=
      (hasFDerivAt_id z).sub_const _
    have h2 : HasFDerivAt H (fderiv ℝ H (z - zs l)) (z - zs l) :=
      ((hH.differentiable one_ne_zero) _).hasFDerivAt
    have := (h2.comp z h1).const_smul (c l)
    refine this.congr_fderiv ?_
    simp
  exact this

theorem s8h_disc_err {f : Euc d × Euc d → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {h : ℝ}
    {ι : Type} [Fintype ι] {θ : ι → Euc d × Euc d → ℝ} {zs : ι → Euc d × Euc d} (hp : S8hPart f h θ zs) :
    ∀ (i : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (H : Euc d × Euc d → F),
      HasCompactSupport H → ContDiff ℝ i H → ∀ {ε : ℝ}, 0 ≤ ε →
      (∀ a b, ‖a - b‖ < h → ‖iteratedFDeriv ℝ i H a - iteratedFDeriv ℝ i H b‖ ≤ ε) → ∀ z,
      ‖iteratedFDeriv ℝ i (fun z => s8h_Disc (fun l => ∫ u, θ l u * f u) zs H z - s8h_Conv f H z) z‖ ≤
        ε * ∫ u, ‖f u‖ := by
  intro i
  induction i with
  | zero =>
    intro F _ _ _ H hHc hH ε hε hmod z
    rw [norm_iteratedFDeriv_zero]
    have hHcont : Continuous H := hH.continuous
    have hK : IsCompact (tsupport f) := hfc
    have hsupp : ∀ φ : Euc d × Euc d → ℝ, Continuous φ → (∀ u, f u = 0 → φ u = 0) → Integrable φ volume := by
      intro φ hφ hz
      refine hφ.integrable_of_hasCompactSupport (HasCompactSupport.intro hK fun u hu => hz u ?_)
      exact image_eq_zero_of_notMem_tsupport hu
    have hfi : Integrable f volume := hf.integrable_of_hasCompactSupport hfc
    have hint1 : ∀ l, Integrable (fun u => (θ l u * f u) • H (z - zs l)) volume := fun l =>
      (hsupp (fun u => θ l u * f u) ((hp.cont l).mul hf) (fun u hu => by simp [hu])).smul_const _
    have hint2 : ∀ l, Integrable (fun u => (θ l u * f u) • H (z - u)) volume := by
      intro l
      refine Continuous.integrable_of_hasCompactSupport (((hp.cont l).mul hf).smul
        (hHcont.comp (continuous_const.sub continuous_id))) (HasCompactSupport.intro hK fun u hu => ?_)
      simp [image_eq_zero_of_notMem_tsupport hu]
    have hcoef : s8h_Disc (fun l => ∫ u, θ l u * f u) zs H z =
        ∫ u, ∑ l, (θ l u * f u) • H (z - zs l) := by
      unfold s8h_Disc
      rw [integral_finset_sum _ (fun l _ => hint1 l)]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [integral_smul_const]
    have hsum : ∀ u, ∑ l, (θ l u * f u) • H (z - u) = f u • H (z - u) := by
      intro u
      rw [← Finset.sum_smul, ← Finset.sum_mul]
      by_cases hu : f u = 0
      · simp [hu]
      · rw [hp.eq_one u hu, one_mul]
    have hconv : s8h_Conv f H z = ∫ u, ∑ l, (θ l u * f u) • H (z - u) := by
      unfold s8h_Conv
      congr 1; funext u; rw [hsum]
    have hdiff : s8h_Disc (fun l => ∫ u, θ l u * f u) zs H z - s8h_Conv f H z =
        ∫ u, ∑ l, (θ l u * f u) • (H (z - zs l) - H (z - u)) := by
      rw [hcoef, hconv, ← integral_sub (integrable_finset_sum _ fun l _ => hint1 l)
        (integrable_finset_sum _ fun l _ => hint2 l)]
      congr 1; funext u
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_sub]
    show ‖s8h_Disc (fun l => ∫ u, θ l u * f u) zs H z - s8h_Conv f H z‖ ≤ _
    rw [hdiff]
    have hb : ∀ u, ‖∑ l, (θ l u * f u) • (H (z - zs l) - H (z - u))‖ ≤ ε * ‖f u‖ := by
      intro u
      refine (norm_sum_le _ _).trans ?_
      calc ∑ l, ‖(θ l u * f u) • (H (z - zs l) - H (z - u))‖ ≤ ∑ l, θ l u * (ε * ‖f u‖) := by
            refine Finset.sum_le_sum fun l _ => ?_
            rw [norm_smul, norm_mul, Real.norm_of_nonneg (hp.nonneg l u)]
            by_cases hl : θ l u = 0
            · simp [hl]
            · have := hmod (z - zs l) (z - u) (by
                rw [sub_sub_sub_cancel_left]; exact hp.small l u hl)
              rw [s8h_norm_iter0_pts] at this
              have h0 : 0 ≤ θ l u * ‖f u‖ := mul_nonneg (hp.nonneg l u) (norm_nonneg _)
              calc θ l u * ‖f u‖ * ‖H (z - zs l) - H (z - u)‖ ≤ θ l u * ‖f u‖ * ε :=
                    mul_le_mul_of_nonneg_left this h0
                _ = θ l u * (ε * ‖f u‖) := by ring
        _ = (∑ l, θ l u) * (ε * ‖f u‖) := by rw [Finset.sum_mul]
        _ ≤ 1 * (ε * ‖f u‖) :=
            mul_le_mul_of_nonneg_right (hp.le_one u) (mul_nonneg hε (norm_nonneg _))
        _ = ε * ‖f u‖ := one_mul _
    refine (norm_integral_le_of_norm_le (hfi.norm.const_mul ε) (Filter.Eventually.of_forall hb)).trans ?_
    rw [integral_const_mul]
  | succ i ih =>
    intro F _ _ _ H hHc hH ε hε hmod z
    have hH1 : ContDiff ℝ 1 H := hH.of_le (by norm_cast; omega)
    have hDH : ContDiff ℝ i (fderiv ℝ H) := hH.fderiv_right (by norm_cast)
    have hfd : fderiv ℝ (fun z => s8h_Disc (fun l => ∫ u, θ l u * f u) zs H z - s8h_Conv f H z) =
        fun z => s8h_Disc (fun l => ∫ u, θ l u * f u) zs (fderiv ℝ H) z - s8h_Conv f (fderiv ℝ H) z := by
      funext x
      exact ((s8h_Disc_hasFDerivAt _ zs hH1 x).sub (s8h_Conv_hasFDerivAt hf hHc hH1 x)).fderiv
    rw [← norm_iteratedFDeriv_fderiv, hfd]
    refine ih (F := Euc d × Euc d →L[ℝ] F) (fderiv ℝ H) (hHc.fderiv ℝ) hDH hε (fun a b hab => ?_) z
    rw [s8h_norm_iter_sub]
    exact hmod a b hab

end ConvZ

end HRS.MS.Wad
