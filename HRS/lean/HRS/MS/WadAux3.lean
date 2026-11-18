import HRS.MS.WadAux2

/-!
# S8.3, packet D2 (part 1): the Gaussian average commutes with derivatives

For `f` of class `C^k` all of whose derivatives `D^i f`, `i ≤ k`, belong to `C_M` (continuous, `‖D^i f‖ ⟨x⟩^{-M}
→ 0`), `|c| ≤ 1`, `0 < c`:

* `s83_G_hasFDerivAt`: `D (G_{c,σ} f) = c G_{c,σ} (D f)` (differentiation under the Gaussian integral).
* `s83_G_iter`: `G_{c,σ} f ∈ C^k`, `D^i (G f) ∈ C_M`, and `‖D^i (G f)‖_M ≤ 2^M mom |c|^i ‖D^i f‖_M`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

universe u

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

section Deriv

/-- Differentiation under the Gaussian integral. -/
theorem s83_G_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : Euc d → E} (hf : ContDiff ℝ 1 f) {M C C' : ℝ} (hM : 0 ≤ M) (hw : Wt M C f)
    (hw' : Wt M C' (fderiv ℝ f)) {c σ σ₀ : ℝ} (hc : |c| ≤ 1) (hσ : |σ| ≤ σ₀) (x₀ : Euc d) :
    HasFDerivAt (s83_G c σ f) (c • s83_G c σ (fderiv ℝ f) x₀) x₀ := by
  have hfc : Continuous f := hf.continuous
  have hf'c : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hC' := hw'.nonneg
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := stdGaussian (Euc d)) (F := fun (x : Euc d) (z : Euc d) => f (c • x + σ • z))
    (F' := fun (x : Euc d) (z : Euc d) => c • fderiv ℝ f (c • x + σ • z)) (x₀ := x₀)
    (bound := fun z : Euc d => |c| * (C' * 2 ^ M * (3 * jbracket x₀) ^ M) * jbracket (σ • z) ^ M)
    (Metric.ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · have e : ∫ z, c • fderiv ℝ f (c • x₀ + σ • z) ∂(stdGaussian (Euc d)) =
        c • s83_G c σ (fderiv ℝ f) x₀ := integral_smul c _
    rw [e] at key
    exact key
  · exact Eventually.of_forall fun x => (s83_cont_shift hfc c σ x).aestronglyMeasurable
  · exact s83_int_shift hfc hM hw hσ x₀
  · have hcont : Continuous fun z : Euc d => c • fderiv ℝ f (c • x₀ + σ • z) :=
      (hf'c.comp (continuous_const.add (continuous_const_smul σ))).const_smul c
    exact hcont.aestronglyMeasurable
  · refine Eventually.of_forall fun z x hx => ?_
    rw [mem_ball_iff_norm] at hx
    rw [norm_smul, Real.norm_eq_abs]
    have h1 := s83_jb_add_rpow hM (c • x) (σ • z)
    have h2 : jbracket (c • x) ^ M ≤ (3 * jbracket x₀) ^ M :=
      (s83_jb_smul_le_rpow hM hc x).trans
        (Real.rpow_le_rpow (s83_jb_pos _).le (s83_jb_le_three hx) hM)
    have h3 : 0 ≤ jbracket (σ • z) ^ M := Real.rpow_nonneg (s83_jb_pos _).le _
    have hb : ‖fderiv ℝ f (c • x + σ • z)‖ ≤
        (C' * 2 ^ M * (3 * jbracket x₀) ^ M) * jbracket (σ • z) ^ M := by
      refine (hw' _).trans ?_
      calc C' * jbracket (c • x + σ • z) ^ M
          ≤ C' * (2 ^ M * (jbracket (c • x) ^ M * jbracket (σ • z) ^ M)) :=
            mul_le_mul_of_nonneg_left h1 hC'
        _ = C' * 2 ^ M * jbracket (c • x) ^ M * jbracket (σ • z) ^ M := by ring
        _ ≤ C' * 2 ^ M * (3 * jbracket x₀) ^ M * jbracket (σ • z) ^ M := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) h3
    calc |c| * ‖fderiv ℝ f (c • x + σ • z)‖
        ≤ |c| * ((C' * 2 ^ M * (3 * jbracket x₀) ^ M) * jbracket (σ • z) ^ M) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg c)
      _ = |c| * (C' * 2 ^ M * (3 * jbracket x₀) ^ M) * jbracket (σ • z) ^ M := by ring
  · exact ((s83_int_jb_smul (M := M) hM hσ).const_mul _)
  · refine Eventually.of_forall fun z x _ => ?_
    have h1 : HasFDerivAt (fun x : Euc d => c • x + σ • z) (c • ContinuousLinearMap.id ℝ (Euc d)) x :=
      ((hasFDerivAt_id x).const_smul c).add_const (σ • z)
    have h2 := (hf.differentiable one_ne_zero (c • x + σ • z)).hasFDerivAt.comp x h1
    have e : (fderiv ℝ f (c • x + σ • z)).comp (c • ContinuousLinearMap.id ℝ (Euc d)) =
        c • fderiv ℝ f (c • x + σ • z) := by
      ext v; simp
    rw [e] at h2
    exact h2

/-- `CMs` transfers along pointwise equal norms (continuity of the target assumed). -/
theorem s83_cms_of_norm_eq {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂] {M : ℝ}
    {g : Euc d → E₁} {h : Euc d → E₂} (hh : Continuous h) (e : ∀ x, ‖g x‖ = ‖h x‖)
    (hg : CMs M g) : CMs M h := by
  refine ⟨hh, ?_⟩
  have := hg.2
  simpa [e] using this

theorem s83_cms_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : ℝ} {g : Euc d → E}
    (hg : ContDiff ℝ 0 g) : CMs M (iteratedFDeriv ℝ 0 g) ↔ CMs M g := by
  constructor
  · exact s83_cms_of_norm_eq hg.continuous (fun x => norm_iteratedFDeriv_zero)
  · exact s83_cms_of_norm_eq (hg.continuous_iteratedFDeriv' (m := 0)) (fun x => (norm_iteratedFDeriv_zero).symm)

theorem s83_wt_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M C : ℝ} {g : Euc d → E} :
    Wt M C (iteratedFDeriv ℝ 0 g) ↔ Wt M C g := by
  unfold Wt
  simp only [norm_iteratedFDeriv_zero]

/-- **Derivatives of Gaussian averages.**  If `f ∈ C^k` and every `D^i f` (`i ≤ k`) is in `C_M`, then
`G_{c,σ} f ∈ C^k`, every `D^i (G f)` is in `C_M`, and `‖D^i (G f)‖_M ≤ 2^M mom c^i ‖D^i f‖_M`. -/
theorem s83_G_iter {M : ℝ} (hM : 0 ≤ M) {c σ σ₀ : ℝ} (hc0 : 0 < c) (hc : c ≤ 1) (hσ : |σ| ≤ σ₀) :
    ∀ (k : ℕ) {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (f : Euc d → E), ContDiff ℝ k f → (∀ i ≤ k, CMs M (iteratedFDeriv ℝ i f)) →
      ContDiff ℝ k (s83_G c σ f) ∧ (∀ i ≤ k, CMs M (iteratedFDeriv ℝ i (s83_G c σ f))) ∧
      ∀ i ≤ k, ∀ C, Wt M C (iteratedFDeriv ℝ i f) →
        Wt M (2 ^ M * mom d M σ₀ * c ^ i * C) (iteratedFDeriv ℝ i (s83_G c σ f)) := by
  have hc' : |c| ≤ 1 := by rw [abs_of_pos hc0]; exact hc
  intro k
  induction k with
  | zero =>
    intro E _ _ _ f hf hcm
    have hf0 : Continuous f := hf.continuous
    have hcmf : CMs M f := (s83_cms_zero hf).1 (hcm 0 le_rfl)
    obtain ⟨C0, hw0⟩ := s83_cm_wt hcmf
    have hGcm := s83_G_cm hcmf hM hc0 hc hσ
    have hGd : ContDiff ℝ 0 (s83_G c σ f) := contDiff_zero.2 hGcm.1
    refine ⟨hGd, fun i hi => ?_, fun i hi C hC => ?_⟩
    · have : i = 0 := by omega
      subst this
      exact (s83_cms_zero hGd).2 hGcm
    · have : i = 0 := by omega
      subst this
      rw [s83_wt_zero] at hC ⊢
      have := s83_G_wt hf0 hM hC hc' hσ
      refine this.mono (le_of_eq ?_)
      ring
  | succ k ih =>
    intro E _ _ _ f hf hcm
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.succ_pos k)
    have hf' : ContDiff ℝ k (fderiv ℝ f) := by
      have := (contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := (k : WithTop ℕ∞)) (f := f)).1
        (by exact_mod_cast hf)
      exact this.2.2
    have hcm' : ∀ i ≤ k, CMs M (iteratedFDeriv ℝ i (fderiv ℝ f)) := fun i hi =>
      s83_cms_of_norm_eq (hf'.continuous_iteratedFDeriv (by exact_mod_cast hi))
        (fun x => (norm_iteratedFDeriv_fderiv (n := i) (f := f) (x := x)).symm)
        (hcm (i + 1) (by omega))
    obtain ⟨hG1, hG2, hG3⟩ := ih (fderiv ℝ f) hf' hcm'
    have hcm0 : CMs M f := (s83_cms_zero (hf.of_le (by exact_mod_cast Nat.zero_le _))).1 (hcm 0 (Nat.zero_le _))
    have hcm1 : CMs M (fderiv ℝ f) :=
      (s83_cms_zero (hf'.of_le (by exact_mod_cast Nat.zero_le _))).1 (hcm' 0 (Nat.zero_le _))
    obtain ⟨C, hw⟩ := s83_cm_wt hcm0
    obtain ⟨C', hw'⟩ := s83_cm_wt hcm1
    have hD : ∀ x, HasFDerivAt (s83_G c σ f) (c • s83_G c σ (fderiv ℝ f) x) x := fun x =>
      s83_G_hasFDerivAt hf1 hM hw hw' hc' hσ x
    have hfd : fderiv ℝ (s83_G c σ f) = c • s83_G c σ (fderiv ℝ f) :=
      funext fun x => (hD x).fderiv
    have hGC : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (s83_G c σ f) := by
      have : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [this, contDiff_succ_iff_fderiv]
      refine ⟨fun x => (hD x).differentiableAt, by simp, ?_⟩
      rw [hfd]
      exact hG1.const_smul c
    -- iterated derivative of `G f` through `fderiv`
    have hit : ∀ j : ℕ, j ≤ k → ∀ x, ‖iteratedFDeriv ℝ (j + 1) (s83_G c σ f) x‖ =
        c * ‖iteratedFDeriv ℝ j (s83_G c σ (fderiv ℝ f)) x‖ := by
      intro j hj x
      rw [← norm_iteratedFDeriv_fderiv, hfd]
      have := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (a := c) (i := j) (x := x)
        (f := s83_G c σ (fderiv ℝ f)) ((hG1.of_le (by exact_mod_cast hj)).contDiffAt)
      have this' : iteratedFDeriv ℝ j (fun y => c • s83_G c σ (fderiv ℝ f) y) x =
          c • iteratedFDeriv ℝ j (s83_G c σ (fderiv ℝ f)) x := this
      change ‖iteratedFDeriv ℝ j (fun y => c • s83_G c σ (fderiv ℝ f) y) x‖ = _
      rw [this', norm_smul, Real.norm_of_nonneg hc0.le]
    refine ⟨hGC, fun i hi => ?_, fun i hi C₁ hC₁ => ?_⟩
    · rcases i with _ | j
      · exact (s83_cms_zero (hGC.of_le (by exact_mod_cast Nat.zero_le _))).2
          (s83_G_cm hcm0 hM hc0 hc hσ)
      · refine ⟨hGC.continuous_iteratedFDeriv (by exact_mod_cast hi), ?_⟩
        have h2 := (hG2 j (by omega)).2
        have h3 := h2.const_mul c
        rw [mul_zero] at h3
        refine h3.congr fun x => ?_
        rw [hit j (by omega) x]
        ring
    · rcases i with _ | j
      · rw [s83_wt_zero] at hC₁ ⊢
        have := s83_G_wt hf.continuous hM hC₁ hc' hσ
        refine this.mono (le_of_eq ?_)
        ring
      · intro x
        rw [hit j (by omega) x]
        have hCj : Wt M C₁ (iteratedFDeriv ℝ j (fderiv ℝ f)) := fun y => by
          rw [norm_iteratedFDeriv_fderiv]; exact hC₁ y
        have := hG3 j (by omega) C₁ hCj x
        calc c * ‖iteratedFDeriv ℝ j (s83_G c σ (fderiv ℝ f)) x‖
            ≤ c * (2 ^ M * mom d M σ₀ * c ^ j * C₁ * jbracket x ^ M) :=
              mul_le_mul_of_nonneg_left this hc0.le
          _ = 2 ^ M * mom d M σ₀ * c ^ (j + 1) * C₁ * jbracket x ^ M := by ring

end Deriv

end HRS.MS.Wad
