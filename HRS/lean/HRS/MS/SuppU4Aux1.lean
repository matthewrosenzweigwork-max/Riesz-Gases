import HRS.Whole.Basic

/-!
# Worker U4, auxiliary lemmas (helper file for `HRS.MS.SuppU4`)

Smooth compactly supported functions on `Euc d`: membership in `C_b^k` (`MemCb`), in `Σ^m`
(`MemOsc`), triangle inequalities for `cbNorm` and `oscNorm`, and the finite-sum bound used for the
smallness estimate.  All statements are proved from `memOsc_schwartz`, `norm_ofFun`,
`oscNorm_const_mul`, `cbNorm_const_mul` and standard Mathlib lemmas, with no unproved placeholder.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

/-- Smooth functions with compact support (the class `C_c^∞`). -/
def U4CS (g : Euc d → ℝ) : Prop := ContDiff ℝ ∞ g ∧ HasCompactSupport g

lemma u4_cs_add {f g : Euc d → ℝ} (hf : U4CS f) (hg : U4CS g) : U4CS (fun x => f x + g x) :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

lemma u4_cs_const_mul (c : ℝ) {f : Euc d → ℝ} (hf : U4CS f) : U4CS (fun x => c * f x) := by
  refine ⟨contDiff_const.mul hf.1, ?_⟩
  have h : HasCompactSupport ((fun _ : Euc d => c) * f) := hf.2.mul_left
  exact h

lemma u4_cs_mul {s : Euc d → ℝ} (hs : ContDiff ℝ ∞ s) {f : Euc d → ℝ} (hf : U4CS f) :
    U4CS (fun x => s x * f x) := by
  refine ⟨hs.mul hf.1, ?_⟩
  have h : HasCompactSupport (s * f) := hf.2.mul_left
  exact h

lemma u4_bdd (j : ℕ) {f : Euc d → ℝ} (hf : U4CS f) :
    BddAbove (Set.range fun z => ‖iteratedFDeriv ℝ j f z‖) := by
  have hc : Continuous (iteratedFDeriv ℝ j f) :=
    hf.1.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support (hf.2.iteratedFDeriv j)
  exact ⟨C, by rintro _ ⟨z, rfl⟩; exact hC z⟩

lemma u4_memCb (k : ℕ) {f : Euc d → ℝ} (hf : U4CS f) : MemCb k f :=
  ⟨hf.1.of_le (by exact_mod_cast le_top), fun j _ => u4_bdd j hf⟩

lemma u4_memOsc (m : ℝ) {f : Euc d → ℝ} (hf : U4CS f) : MemOsc m f := by
  have hS : HasCompactSupport f := hf.2
  obtain ⟨S, hSf⟩ : ∃ S : SchwartzMap (Euc d) ℝ, ⇑S = f := ⟨hS.toSchwartzMap hf.1, rfl⟩
  have h := memOsc_schwartz m S
  rw [hSf] at h
  exact h

lemma u4_cbNorm_nonneg (k : ℕ) (f : Euc d → ℝ) : 0 ≤ cbNorm k f := by
  unfold cbNorm
  refine Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun z => norm_nonneg _

lemma u4_oscNorm_nonneg (m : ℝ) (f : Euc d → ℝ) : 0 ≤ oscNorm m f := by
  unfold oscNorm
  exact Real.sqrt_nonneg _

lemma u4_cbNorm_zero (k : ℕ) : cbNorm k (fun _ : Euc d => (0 : ℝ)) = 0 := by
  unfold cbNorm
  have h : ∀ j : ℕ, iteratedFDeriv ℝ j (fun _ : Euc d => (0 : ℝ)) = 0 := fun j =>
    iteratedFDeriv_fun_zero
  simp [h]

lemma u4_oscNorm_zero (m : ℝ) : oscNorm m (fun _ : Euc d => (0 : ℝ)) = 0 := by
  unfold oscNorm hermiteCoeff
  simp

/-- The triangle inequality for `cbNorm` on smooth compactly supported functions. -/
lemma u4_cbNorm_add_le (k : ℕ) {f g : Euc d → ℝ} (hf : U4CS f) (hg : U4CS g) :
    cbNorm k (fun x => f x + g x) ≤ cbNorm k f + cbNorm k g := by
  unfold cbNorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have hsum : ∀ z, ‖iteratedFDeriv ℝ j (fun x => f x + g x) z‖ ≤
      ‖iteratedFDeriv ℝ j f z‖ + ‖iteratedFDeriv ℝ j g z‖ := by
    intro z
    have h : iteratedFDeriv ℝ j (fun x => f x + g x) z =
        iteratedFDeriv ℝ j f z + iteratedFDeriv ℝ j g z :=
      iteratedFDeriv_add_apply (hf.1.contDiffAt.of_le (by exact_mod_cast le_top))
        (hg.1.contDiffAt.of_le (by exact_mod_cast le_top))
    rw [h]
    exact norm_add_le _ _
  apply ciSup_le
  intro z
  calc ‖iteratedFDeriv ℝ j (fun x => f x + g x) z‖
      ≤ ‖iteratedFDeriv ℝ j f z‖ + ‖iteratedFDeriv ℝ j g z‖ := hsum z
    _ ≤ (⨆ z, ‖iteratedFDeriv ℝ j f z‖) + ⨆ z, ‖iteratedFDeriv ℝ j g z‖ :=
        add_le_add (le_ciSup (u4_bdd j hf) z) (le_ciSup (u4_bdd j hg) z)

/-- Hermite coefficients are additive on smooth compactly supported functions. -/
lemma u4_hc_add (α : MultiIndex d) {f g : Euc d → ℝ} (hf : U4CS f) (hg : U4CS g) :
    hermiteCoeff (fun x => f x + g x) α = hermiteCoeff f α + hermiteCoeff g α := by
  unfold hermiteCoeff
  have hh : Continuous (hermiteFunD α) := (contDiff_hermiteFunD α).continuous
  have hfi : Integrable (fun x => f x * hermiteFunD α x) := by
    have hc : Continuous (fun x => f x * hermiteFunD α x) := hf.1.continuous.mul hh
    refine hc.integrable_of_hasCompactSupport ?_
    have h : HasCompactSupport (f * hermiteFunD α) := hf.2.mul_right
    exact h
  have hgi : Integrable (fun x => g x * hermiteFunD α x) := by
    have hc : Continuous (fun x => g x * hermiteFunD α x) := hg.1.continuous.mul hh
    refine hc.integrable_of_hasCompactSupport ?_
    have h : HasCompactSupport (g * hermiteFunD α) := hg.2.mul_right
    exact h
  simp only [add_mul]
  exact integral_add hfi hgi

/-- `ofFun` is additive on smooth compactly supported functions. -/
lemma u4_ofFun_add (m : ℝ) {f g : Euc d → ℝ} (hf : U4CS f) (hg : U4CS g) :
    OscSpace.ofFun m (fun x => f x + g x) = OscSpace.ofFun m f + OscSpace.ofFun m g := by
  have hfm := u4_memOsc m hf
  have hgm := u4_memOsc m hg
  have hfgm := u4_memOsc m (u4_cs_add hf hg)
  rw [OscSpace.ofFun_eq hfgm, OscSpace.ofFun_eq hfm, OscSpace.ofFun_eq hgm]
  apply lp.ext
  funext α
  change oscEigenvalue d α ^ (m / 2) * hermiteCoeff (fun x => f x + g x) α =
    oscEigenvalue d α ^ (m / 2) * hermiteCoeff f α + oscEigenvalue d α ^ (m / 2) * hermiteCoeff g α
  rw [u4_hc_add α hf hg]
  ring

/-- The triangle inequality for `oscNorm` on smooth compactly supported functions. -/
lemma u4_oscNorm_add_le (m : ℝ) {f g : Euc d → ℝ} (hf : U4CS f) (hg : U4CS g) :
    oscNorm m (fun x => f x + g x) ≤ oscNorm m f + oscNorm m g := by
  have hfm := u4_memOsc m hf
  have hgm := u4_memOsc m hg
  have hfgm := u4_memOsc m (u4_cs_add hf hg)
  have hlin := u4_ofFun_add m hf hg
  calc oscNorm m (fun x => f x + g x)
      = ‖OscSpace.ofFun m (fun x => f x + g x)‖ := (OscSpace.norm_ofFun _ hfgm).symm
    _ = ‖OscSpace.ofFun m f + OscSpace.ofFun m g‖ := by rw [hlin]
    _ ≤ ‖OscSpace.ofFun m f‖ + ‖OscSpace.ofFun m g‖ := norm_add_le _ _
    _ = oscNorm m f + oscNorm m g := by
        rw [OscSpace.norm_ofFun _ hfm, OscSpace.norm_ofFun _ hgm]

/-- Finite linear combinations: a generic bound for a seminorm-like functional `P`. -/
lemma u4_sum_bound {n : ℕ} (P : (Euc d → ℝ) → ℝ) (hP0 : P (fun _ => 0) ≤ 0)
    (hadd : ∀ f g : Euc d → ℝ, U4CS f → U4CS g → P (fun x => f x + g x) ≤ P f + P g)
    (hmul : ∀ (a : ℝ) (f : Euc d → ℝ), U4CS f → P (fun x => a * f x) = |a| * P f)
    (c : Fin n → ℝ) (ψ : Fin n → Euc d → ℝ) (hψ : ∀ i, U4CS (ψ i)) (s : Finset (Fin n)) :
    U4CS (fun x => ∑ i ∈ s, c i * ψ i x) ∧
      P (fun x => ∑ i ∈ s, c i * ψ i x) ≤ ∑ i ∈ s, |c i| * P (ψ i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨⟨contDiff_const, HasCompactSupport.zero⟩, hP0⟩
  | insert a s ha ih =>
    obtain ⟨hcs, hle⟩ := ih
    have hA : U4CS (fun x => c a * ψ a x) := u4_cs_const_mul (c a) (hψ a)
    have hsum_eq : (fun x => ∑ i ∈ insert a s, c i * ψ i x) =
        fun x => c a * ψ a x + ∑ i ∈ s, c i * ψ i x := by
      funext x
      rw [Finset.sum_insert ha]
    rw [hsum_eq, Finset.sum_insert ha]
    refine ⟨u4_cs_add hA hcs, ?_⟩
    have h1 := hadd (fun x => c a * ψ a x) (fun x => ∑ i ∈ s, c i * ψ i x) hA hcs
    have h2 := hmul (c a) (ψ a) (hψ a)
    rw [h2] at h1
    linarith

end HRS.Whole
