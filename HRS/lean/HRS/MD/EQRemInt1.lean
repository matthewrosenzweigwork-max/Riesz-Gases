import HRS.MD.EQRemStatic

/-!
# EQ-REM (b), part 1: Fourier expansion of a bounded linear functional on `C²`

For a (pointwise) linear functional `ℓ` on `C²(𝕋^d)` with `|ℓ φ| ≤ b ‖φ‖_{C²}`, `ℓ(const) = 0`, and `φ ∈ C² ∩ H^M`
(`M > d/2 + 2`): `ℓ φ = lim_F ∑_{k ∈ F} φ̂_k ℓ(e_k)` along finite sets `F`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQRem

open HRS HRS.MD.EQ29

variable {d : ℕ}

/-- The trigonometric partial sum `∑_{k ∈ F} c_k e_k`. -/
def eqremTrig (F : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) : Torus d → ℝ :=
  fun x => ∑ k ∈ F, c k * Torus.realMode k x

theorem eqrem_isCk_sub {φ ψ : Torus d → ℝ} {n : WithTop ℕ∞} (hφ : Torus.IsCk n φ) (hψ : Torus.IsCk n ψ) :
    Torus.IsCk n (fun x => φ x - ψ x) := hφ.sub hψ

theorem eqrem_isCk_add {φ ψ : Torus d → ℝ} {n : WithTop ℕ∞} (hφ : Torus.IsCk n φ) (hψ : Torus.IsCk n ψ) :
    Torus.IsCk n (fun x => φ x + ψ x) := hφ.add hψ

theorem eqrem_isCk_const (n : WithTop ℕ∞) (c : ℝ) : Torus.IsCk n (fun _ : Torus d => c) :=
  contDiff_const

theorem eqrem_isCk_smul {φ : Torus d → ℝ} {n : WithTop ℕ∞} (c : ℝ) (hφ : Torus.IsCk n φ) :
    Torus.IsCk n (fun x => c * φ x) := hφ.const_smul c

theorem eqrem_isCk_trig (F : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) :
    Torus.IsCk 2 (eqremTrig F c) := by
  unfold eqremTrig Torus.IsCk
  have : Torus.lift (fun x => ∑ k ∈ F, c k * Torus.realMode k x) =
      fun y => ∑ k ∈ F, c k * Torus.lift (Torus.realMode k) y := rfl
  rw [this]
  refine ContDiff.sum fun k _ => ?_
  have hk : Torus.IsCk 2 (Torus.realMode k : Torus d → ℝ) := by
    have := Uniform.Q54c.isCk_realMode k 2
    exact_mod_cast this
  exact hk.const_smul (c k)

theorem eqrem_continuous_of_isCk {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) : Continuous φ :=
  Torus.continuous_of_continuous_lift hφ.continuous


theorem eqrem_integrable_of_continuous {φ : Torus d → ℝ} (hφ : Continuous φ) : Integrable φ :=
  hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem eqrem_integrable_realMode (k : NonzeroLattice d) {φ : Torus d → ℝ} (hφ : Continuous φ) :
    Integrable (fun x => Torus.realMode k x * φ x) :=
  eqrem_integrable_of_continuous ((Torus.continuous_realMode k).mul hφ)

/-- Coefficients of `φ - mean φ - S_F φ`. -/
theorem eqrem_coeff_remainder {φ : Torus d → ℝ} (hφ : Continuous φ) (F : Finset (NonzeroLattice d))
    (c : NonzeroLattice d → ℝ) (k : NonzeroLattice d) :
    Torus.funRealCoeff (fun x => φ x - Torus.mean φ - eqremTrig F c x) k =
      Torus.funRealCoeff φ k - (if k ∈ F then c k else 0) := by
  unfold Torus.funRealCoeff
  have h1 : ∀ x, Torus.realMode k x * (φ x - Torus.mean φ - eqremTrig F c x) =
      Torus.realMode k x * φ x - Torus.mean φ * Torus.realMode k x -
        ∑ j ∈ F, c j * (Torus.realMode k x * Torus.realMode j x) := by
    intro x
    unfold eqremTrig
    rw [mul_sub, mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [h1]
  have i1 : Integrable (fun x => Torus.realMode k x * φ x) := eqrem_integrable_realMode k hφ
  have i2 : Integrable (fun x => Torus.mean φ * Torus.realMode k x) :=
    ((Torus.continuous_realMode k).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _
  have i3 : Integrable (fun x => ∑ j ∈ F, c j * (Torus.realMode k x * Torus.realMode j x)) :=
    integrable_finsetSum _ fun j _ =>
      (eqrem_integrable_realMode k (Torus.continuous_realMode j)).const_mul _
  have e1 := integral_sub (μ := (volume : Measure (Torus d)))
    (f := fun x => Torus.realMode k x * φ x - Torus.mean φ * Torus.realMode k x)
    (g := fun x => ∑ j ∈ F, c j * (Torus.realMode k x * Torus.realMode j x)) (i1.sub i2) i3
  have e2 := integral_sub (μ := (volume : Measure (Torus d)))
    (f := fun x => Torus.realMode k x * φ x) (g := fun x => Torus.mean φ * Torus.realMode k x) i1 i2
  rw [e1, e2, integral_const_mul, Torus.integral_realMode,
    integral_finsetSum _ fun j _ => (eqrem_integrable_realMode k (Torus.continuous_realMode j)).const_mul _]
  simp_rw [integral_const_mul, Torus.realMode_orthonormal k]
  simp [Finset.sum_ite_eq]

/-- The mean of `φ - mean φ - S_F φ` vanishes. -/
theorem eqrem_mean_remainder {φ : Torus d → ℝ} (hφ : Continuous φ) (F : Finset (NonzeroLattice d))
    (c : NonzeroLattice d → ℝ) :
    Torus.mean (fun x => φ x - Torus.mean φ - eqremTrig F c x) = 0 := by
  have i1 : Integrable φ := eqrem_integrable_of_continuous hφ
  have i3 : Integrable (eqremTrig F c) :=
    eqrem_integrable_of_continuous (eqrem_continuous_of_isCk (eqrem_isCk_trig F c))
  have e1 := integral_sub (μ := (volume : Measure (Torus d)))
    (f := fun x => φ x - Torus.mean φ) (g := eqremTrig F c) (i1.sub (integrable_const _)) i3
  have e2 := integral_sub (μ := (volume : Measure (Torus d)))
    (f := φ) (g := fun _ => Torus.mean φ) i1 (integrable_const _)
  have h2 : ∫ x : Torus d, eqremTrig F c x = 0 := by
    unfold eqremTrig
    rw [integral_finsetSum _ fun j _ => ((Torus.continuous_realMode j).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _]
    simp [integral_const_mul, Torus.integral_realMode]
  have hm : Torus.mean φ = ∫ x : Torus d, φ x := rfl
  have hmm : Torus.mean (fun x => φ x - Torus.mean φ - eqremTrig F c x) =
      ∫ x : Torus d, (φ x - Torus.mean φ - eqremTrig F c x) := rfl
  rw [hmm, e1, e2, h2, ← hm]
  simp


/-- Tail of a nonnegative summable family tends to zero along finite sets. -/
theorem eqrem_tail_tendsto {ι : Type*} [DecidableEq ι] (w : ι → ℝ) (hw : Summable w) :
    Tendsto (fun F : Finset ι => ∑' k, (if k ∈ F then 0 else w k)) atTop (𝓝 0) := by
  have e : ∀ F : Finset ι, ∑' k, (if k ∈ F then 0 else w k) = (∑' k, w k) - ∑ k ∈ F, w k := by
    intro F
    have hF : Summable (fun k => if k ∈ F then w k else 0) :=
      summable_of_ne_finset_zero (s := F) fun k hk => by simp [hk]
    have h1 : (fun k => if k ∈ F then (0 : ℝ) else w k) = fun k => w k - (if k ∈ F then w k else 0) := by
      funext k; by_cases hk : k ∈ F <;> simp [hk]
    rw [h1, hw.tsum_sub hF]
    congr 1
    rw [tsum_eq_sum (s := F) (fun k hk => by simp [hk])]
    exact Finset.sum_congr rfl fun k hk => by simp [hk]
  simp_rw [e]
  have := hw.hasSum
  have h2 : Tendsto (fun F : Finset ι => ∑ k ∈ F, w k) atTop (𝓝 (∑' k, w k)) := this
  simpa using (tendsto_const_nhds (x := ∑' k, w k)).sub h2

/-- The Fourier partial sums converge in `C²` for `φ ∈ C² ∩ H^M`, `M > d/2 + 2`. -/
theorem eqrem_trig_cb_tendsto {M : ℝ} (hM : (d : ℝ) / 2 + 2 < M) {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ)
    (hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * M) * Torus.funRealCoeff φ k ^ 2) :
    Tendsto (fun F : Finset (NonzeroLattice d) => Torus.cbNorm 2
      (fun x => φ x - Torus.mean φ - eqremTrig F (Torus.funRealCoeff φ) x)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := cbNorm_le_sobolevNorm (d := d) 2 M (by exact_mod_cast hM)
  have hφc : Continuous φ := eqrem_continuous_of_isCk hφ
  set w : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (2 * M) * Torus.funRealCoeff φ k ^ 2 with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k =>
    mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
  have hT := eqrem_tail_tendsto w hs
  have hψ : ∀ F : Finset (NonzeroLattice d), Torus.IsCk 2
      (fun x => φ x - Torus.mean φ - eqremTrig F (Torus.funRealCoeff φ) x) := fun F =>
    eqrem_isCk_sub (eqrem_isCk_sub hφ (eqrem_isCk_const 2 _)) (eqrem_isCk_trig F _)
  have hcoef : ∀ (F : Finset (NonzeroLattice d)) (k : NonzeroLattice d),
      Lattice.jp k.1 ^ (2 * M) * Torus.funRealCoeff
        (fun x => φ x - Torus.mean φ - eqremTrig F (Torus.funRealCoeff φ) x) k ^ 2 =
        if k ∈ F then 0 else w k := by
    intro F k
    rw [eqrem_coeff_remainder hφc F]
    by_cases hk : k ∈ F <;> simp [hk, hw]
  have hmem : ∀ F : Finset (NonzeroLattice d), MemSobolev M
      (fun x => φ x - Torus.mean φ - eqremTrig F (Torus.funRealCoeff φ) x) := by
    intro F
    refine ⟨(eqrem_continuous_of_isCk (hψ F)).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _), ?_⟩
    simp_rw [hcoef F]
    exact hs.of_nonneg_of_le (fun k => by split_ifs <;> simp [hw0]) (fun k => by
      split_ifs
      · exact hw0 k
      · exact le_rfl)
  have hsob : ∀ F : Finset (NonzeroLattice d), sobolevNorm M
      (fun x => φ x - Torus.mean φ - eqremTrig F (Torus.funRealCoeff φ) x) =
      Real.sqrt (∑' k, (if k ∈ F then 0 else w k)) := by
    intro F
    unfold sobolevNorm
    rw [eqrem_mean_remainder hφc F]
    simp_rw [hcoef F]
    simp
  have hbound : ∀ F : Finset (NonzeroLattice d), Torus.cbNorm 2
      (fun x => φ x - Torus.mean φ - eqremTrig F (Torus.funRealCoeff φ) x) ≤
      |C| * Real.sqrt (∑' k, (if k ∈ F then 0 else w k)) := by
    intro F
    refine (hC _ (hmem F) (hψ F)).trans ?_
    rw [hsob F]
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
  have hlim : Tendsto (fun F : Finset (NonzeroLattice d) => |C| * Real.sqrt (∑' k, (if k ∈ F then 0 else w k)))
      atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hT
    simpa using this.const_mul |C|
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun F => PDE.cbNorm_nonneg' 2 _) hbound


/-- Abstract Fourier expansion of a bounded pointwise-linear functional on `C²`. -/
theorem eqrem_expansion {M : ℝ} (hM : (d : ℝ) / 2 + 2 < M) (ℓ : (Torus d → ℝ) → ℝ) (b : ℝ)
    (hadd : ∀ φ ψ : Torus d → ℝ, Torus.IsCk 2 φ → Torus.IsCk 2 ψ →
      ℓ (fun x => φ x + ψ x) = ℓ φ + ℓ ψ)
    (hsmul : ∀ (c : ℝ) (φ : Torus d → ℝ), Torus.IsCk 2 φ → ℓ (fun x => c * φ x) = c * ℓ φ)
    (hconst : ∀ c : ℝ, ℓ (fun _ => c) = 0)
    (hbd : ∀ φ : Torus d → ℝ, Torus.IsCk 2 φ → |ℓ φ| ≤ b * Torus.cbNorm 2 φ)
    {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ)
    (hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * M) * Torus.funRealCoeff φ k ^ 2) :
    Tendsto (fun F : Finset (NonzeroLattice d) => ∑ k ∈ F, Torus.funRealCoeff φ k * ℓ (Torus.realMode k))
      atTop (𝓝 (ℓ φ)) := by
  classical
  have hek : ∀ k : NonzeroLattice d, Torus.IsCk 2 (Torus.realMode k : Torus d → ℝ) := fun k => by
    have := Uniform.Q54c.isCk_realMode k 2
    exact_mod_cast this
  have hS : ∀ (c : NonzeroLattice d → ℝ) (F : Finset (NonzeroLattice d)),
      ℓ (eqremTrig F c) = ∑ k ∈ F, c k * ℓ (Torus.realMode k) := by
    intro c F
    induction F using Finset.induction_on with
    | empty =>
      have : eqremTrig (∅ : Finset (NonzeroLattice d)) c = fun _ => (0 : ℝ) := by
        funext x; simp [eqremTrig]
      rw [this, hconst]; simp
    | insert a F ha ih =>
      have : eqremTrig (insert a F) c = fun x => c a * Torus.realMode a x + eqremTrig F c x := by
        funext x; simp [eqremTrig, Finset.sum_insert ha]
      rw [this, hadd _ _ (eqrem_isCk_smul (c a) (hek a)) (eqrem_isCk_trig F c),
        hsmul _ _ (hek a), ih, Finset.sum_insert ha]
  have hlim := eqrem_trig_cb_tendsto hM hφ hs
  have hψ : ∀ F : Finset (NonzeroLattice d), Torus.IsCk 2
      (fun x => φ x - Torus.mean φ - eqremTrig F (Torus.funRealCoeff φ) x) := fun F =>
    eqrem_isCk_sub (eqrem_isCk_sub hφ (eqrem_isCk_const 2 _)) (eqrem_isCk_trig F _)
  have hdec : ∀ F : Finset (NonzeroLattice d),
      ℓ φ = ℓ (fun x => φ x - Torus.mean φ - eqremTrig F (Torus.funRealCoeff φ) x) +
        ∑ k ∈ F, Torus.funRealCoeff φ k * ℓ (Torus.realMode k) := by
    intro F
    set ψ : Torus d → ℝ := fun x => φ x - Torus.mean φ - eqremTrig F (Torus.funRealCoeff φ) x with hψdef
    have e1 : φ = fun x => (ψ x + eqremTrig F (Torus.funRealCoeff φ) x) + Torus.mean φ := by
      funext x; simp only [hψdef]; ring
    have h1 : ℓ φ = ℓ (fun x => ψ x + eqremTrig F (Torus.funRealCoeff φ) x) + ℓ (fun _ => Torus.mean φ) := by
      conv_lhs => rw [e1]
      exact hadd _ _ (eqrem_isCk_add (hψ F) (eqrem_isCk_trig F _)) (eqrem_isCk_const 2 _)
    rw [h1, hadd _ _ (hψ F) (eqrem_isCk_trig F _), hconst, hS]
    ring
  have hupper : Tendsto (fun F : Finset (NonzeroLattice d) => |b| * Torus.cbNorm 2
      (fun x => φ x - Torus.mean φ - eqremTrig F (Torus.funRealCoeff φ) x)) atTop (𝓝 0) := by
    simpa using hlim.const_mul |b|
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun F => dist_nonneg) (fun F => ?_) hupper
  rw [Real.dist_eq]
  have := hdec F
  have h2 : ∑ k ∈ F, Torus.funRealCoeff φ k * ℓ (Torus.realMode k) - ℓ φ =
      -ℓ (fun x => φ x - Torus.mean φ - eqremTrig F (Torus.funRealCoeff φ) x) := by linarith
  rw [h2, abs_neg]
  exact (hbd _ (hψ F)).trans (mul_le_mul_of_nonneg_right (le_abs_self b) (PDE.cbNorm_nonneg' 2 _))

end HRS.MD.EQRem

end
