import HRS.MS.MainRdStatAux1
import HRS.MS.GoFeatAux2
import HRS.MS.UlNormAux1

/-!
# SA2, packet 2: consequences of the adjoint input `AdjointInputRd (ulocClass m_*) (ulocClass m_*) 2 C T Kad`

* `sa2_c2_of_mem`: a continuous test of finite `H^{m_*}_uloc` norm is `C²` (`uloc_embedding_cb`, continuous representatives agree).
* `Sa2Orbit`: the classical solution `f = (r ↦ U^{r,t}φ)`, its `C_b^2` and uloc bounds on `[0,t]` (all in terms of `n = ‖φ‖_{H^{m_*}_uloc}`).
* `sa2_y0`: `Y0Class` and `y0Norm m₀ χ ψ ≤ Cy X` for `ψ` with `ulocNormE m_* χ ψ ≤ X`, `cbNorm 2 ψ ≤ X`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ}

/-! ### Elementary bounds from `cbNorm` -/

theorem sa2_norm_iter_le_cbNorm {k j : ℕ} (hj : j ≤ k) {f : Euc d → ℝ} (hf : MemCb k f) (x : Euc d) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ cbNorm k f := by
  have h0 : ‖iteratedFDeriv ℝ j f x‖ ≤ ⨆ z : Euc d, ‖iteratedFDeriv ℝ j f z‖ := le_ciSup (hf.2 j hj) x
  refine h0.trans ?_
  unfold cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j f z‖)
    (fun _ _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

theorem sa2_cbNorm_nonneg (k : ℕ) (f : Euc d → ℝ) : 0 ≤ cbNorm k f :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem sa2_lip_of_memCb {f : Euc d → ℝ} (hf : MemCb 2 f) (x y : Euc d) :
    |f x - f y| ≤ cbNorm 2 f * ‖x - y‖ := by
  have hdiff : ∀ z, DifferentiableAt ℝ f z := fun z =>
    (hf.1.differentiable (by norm_num)) z
  have hb : ∀ z ∈ (Set.univ : Set (Euc d)), ‖fderiv ℝ f z‖ ≤ cbNorm 2 f := by
    intro z _
    have := sa2_norm_iter_le_cbNorm (k := 2) (j := 1) (by norm_num) hf z
    rwa [norm_iteratedFDeriv_one] at this
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z) hb convex_univ
    (Set.mem_univ y) (Set.mem_univ x)
  rw [← Real.norm_eq_abs]
  simpa [norm_sub_rev] using this

theorem sa2_c01_le {f : Euc d → ℝ} (hf : MemCb 2 f) : HRS.PDE.ToolboxRd.c01Norm f ≤ 2 * cbNorm 2 f := by
  have h0 := sa2_cbNorm_nonneg 2 f
  unfold HRS.PDE.ToolboxRd.c01Norm
  have h1 : (⨆ x, |f x|) ≤ cbNorm 2 f :=
    Real.iSup_le (fun x => by
      have := HRS.MP.RdRem.mrr_abs_le_cbNorm hf x
      exact this) h0
  have h2 : (⨆ p : {p : Euc d × Euc d // p.1 ≠ p.2}, |f p.1.1 - f p.1.2| / ‖p.1.1 - p.1.2‖) ≤ cbNorm 2 f :=
    Real.iSup_le (fun p => by
      have hp : 0 < ‖p.1.1 - p.1.2‖ := norm_pos_iff.2 (sub_ne_zero.2 p.2)
      rw [div_le_iff₀ hp]
      exact sa2_lip_of_memCb hf _ _) h0
  linarith

/-! ### Monotonicity of the uloc norm in the index -/

theorem sa2_ulocNormE_mono {m m' : ℕ} (h : m ≤ m') (χ u : Euc d → ℝ) :
    ulocNormE m χ u ≤ ulocNormE m' χ u := by
  unfold ulocNormE
  refine iSup_mono fun z => ?_
  exact HRS.MS.Ul.ul0_sobE_mono (by exact_mod_cast h) _

/-! ### `C²` of tests of the class -/

theorem sa2_c2_of_mem {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {φ : Euc d → ℝ}
    (hφ : (ulocClass (mStar d) χ).mem φ) : ContDiff ℝ 2 φ := by
  have hlt : ((2 : ℕ) : ℝ) + (d : ℝ) / 2 < ((mStar d : ℕ) : ℝ) := by
    unfold mStar
    have : (d : ℝ) < 2 * ((d / 2 : ℕ) : ℝ) + 2 := by
      have h : d < 2 * (d / 2) + 2 := by omega
      exact_mod_cast h
    push_cast
    linarith
  obtain ⟨C, hC⟩ := HRS.MS.UlocCb.uloc_embedding_cb_proof (mStar d) 2 hlt χ hχ
  obtain ⟨v, hv, hvcb, -⟩ := hC φ hφ.2
  have hvc : Continuous v := hvcb.1.continuous
  have : v = φ := (Continuous.ae_eq_iff_eq (volume : Measure (Euc d)) hvc hφ.1).1 hv
  rw [← this]
  exact hvcb.1

/-! ### The orbit package -/

theorem sa2_isClassical_prop {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ}
    (h : ∃ f, IsClassicalAdjointW C t φ f) :
    IsClassicalAdjointW C t φ (fun r => propagatorW C r t φ) := by
  have e : (fun r => propagatorW C r t φ) = h.choose := by
    funext r; unfold propagatorW; rw [dif_pos h]
  rw [e]; exact h.choose_spec

/-- The consequences of the adjoint input for one test `φ` and one time `t`. -/
structure Sa2Orbit (C : WholeCoeff d) (χ : Euc d → ℝ) (Kp : ℝ) (t : ℝ) (φ : Euc d → ℝ) : Prop where
  cl : IsClassicalAdjointW C t φ (fun r => propagatorW C r t φ)
  c2 : ContDiff ℝ 2 φ
  cb : ∀ r ∈ Set.Icc (0 : ℝ) t, MemCb 2 (propagatorW C r t φ) ∧
    cbNorm 2 (propagatorW C r t φ) ≤ Kp * (ulocNormE (mStar d) χ φ).toReal
  ul : ∀ r ∈ Set.Icc (0 : ℝ) t, ulocNormE (mStar d) χ (propagatorW C r t φ) ≤
    ENNReal.ofReal (Kp * (ulocNormE (mStar d) χ φ).toReal)

theorem sa2_orbit {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {C : WholeCoeff d} {T Kad : ℝ}
    (hA : AdjointInputRd (ulocClass (mStar d) χ) (ulocClass (mStar d) χ) 2 C T Kad)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {φ : Euc d → ℝ} (hφ : (ulocClass (mStar d) χ).mem φ) :
    Sa2Orbit C χ (max Kad 0) t φ := by
  have hc2 := sa2_c2_of_mem hχ hφ
  have hn0 : 0 ≤ (ulocNormE (mStar d) χ φ).toReal := ENNReal.toReal_nonneg
  have hall : ∀ r ∈ Set.Icc (0 : ℝ) t, (∃ f, IsClassicalAdjointW C t φ f) ∧
      (ulocClass (mStar d) χ).mem (propagatorW C r t φ) ∧
      (ulocClass (mStar d) χ).norm (propagatorW C r t φ) ≤ Kad * (ulocClass (mStar d) χ).norm φ ∧
      MemCb 2 (propagatorW C r t φ) ∧ cbNorm 2 (propagatorW C r t φ) ≤ Kad * (ulocClass (mStar d) χ).norm φ :=
    fun r hr => hA r t hr.1 hr.2 ht.2 φ hc2 hφ
  have hex : ∃ f, IsClassicalAdjointW C t φ f := (hall 0 ⟨le_rfl, ht.1⟩).1
  have hKn : Kad * (ulocClass (mStar d) χ).norm φ ≤ max Kad 0 * (ulocNormE (mStar d) χ φ).toReal :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hn0
  refine ⟨sa2_isClassical_prop hex, hc2, fun r hr => ⟨(hall r hr).2.2.2.1, ?_⟩, fun r hr => ?_⟩
  · exact (hall r hr).2.2.2.2.trans hKn
  · obtain ⟨-, hmem, hnorm, -, -⟩ := hall r hr
    have hfin : ulocNormE (mStar d) χ (propagatorW C r t φ) ≠ ⊤ := hmem.2.ne
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal (hnorm.trans hKn)

/-! ### `Y₀` data of the orbit at time `0` -/

theorem sa2_varpi_const {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (M : ℕ) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ m₀ ≤ M, ∀ u : Euc d → ℝ,
      varpiNormE m₀ χ u ≤ ENNReal.ofReal Cv * ulocNormE m₀ χ u := by
  have h : ∀ m₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Euc d → ℝ,
      varpiNormE m₀ χ u ≤ ENNReal.ofReal C * ulocNormE m₀ χ u := fun m₀ => by
    obtain ⟨-, -, C, hC⟩ := HRS.MS.UlocWeighted.uloc_embedding_weighted_proof m₀ χ hχ
    refine ⟨max C 0, le_max_right _ _, fun u => (hC u).trans ?_⟩
    gcongr
    exact le_max_left _ _
  choose Cf hCf0 hCf using h
  refine ⟨∑ m₀ ∈ Finset.range (M + 1), Cf m₀, Finset.sum_nonneg fun m _ => hCf0 m, fun m₀ hm u => ?_⟩
  refine (hCf m₀ u).trans ?_
  gcongr
  exact Finset.single_le_sum (f := Cf) (fun m _ => hCf0 m) (Finset.mem_range.2 (Nat.lt_succ_of_le hm))

theorem sa2_y0 {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) :
    ∃ Cy : ℝ, 0 ≤ Cy ∧ ∀ m₀ : ℕ, m₀ ≤ mStar d → ∀ (ψ : Euc d → ℝ) (X : ℝ), 0 ≤ X →
      MemCb 2 ψ → cbNorm 2 ψ ≤ X → ulocNormE (mStar d) χ ψ ≤ ENNReal.ofReal X →
      Y0Class m₀ χ ψ ∧ y0Norm m₀ χ ψ ≤ Cy * X := by
  obtain ⟨Cv, hCv0, hCv⟩ := sa2_varpi_const (d := d) hχ (mStar d)
  refine ⟨Cv + 2, by positivity, fun m₀ hm ψ X hX hcb hcbX hul => ?_⟩
  have hu0 : ulocNormE m₀ χ ψ ≤ ENNReal.ofReal X := (sa2_ulocNormE_mono hm χ ψ).trans hul
  have hY : Y0Class m₀ χ ψ := by
    refine ⟨lt_of_le_of_lt hu0 ENNReal.ofReal_lt_top, ⟨cbNorm 2 ψ, fun x => ?_⟩,
      ⟨cbNorm 2 ψ, fun x y => ?_⟩⟩
    · exact HRS.MP.RdRem.mrr_abs_le_cbNorm hcb x
    · exact sa2_lip_of_memCb hcb x y
  refine ⟨hY, ?_⟩
  unfold y0Norm
  have h1 : varpiNormE m₀ χ ψ ≤ ENNReal.ofReal (Cv * X) := by
    refine (hCv m₀ hm ψ).trans ?_
    rw [ENNReal.ofReal_mul hCv0]
    gcongr
  have h2 : (varpiNormE m₀ χ ψ).toReal ≤ Cv * X :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) h1
  have h3 := sa2_c01_le hcb
  have hX2 : 2 * cbNorm 2 ψ ≤ 2 * X := by linarith
  nlinarith

end HRS.MS.MainRdStat
