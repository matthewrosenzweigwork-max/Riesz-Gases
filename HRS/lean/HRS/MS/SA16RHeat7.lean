import HRS.MS.SA16RHeat6

/-!
# S.A.16 (SA16R) Heat7: the gain operator `Γ_a : WmpSpace d k p →L WmpSpace d (k+1) p`

`sa16r_Gam`: continuous linear extension of `φ ↦ g_a ⋆ φ`, with `‖Γ_a‖ ≤ 1 + d (4/3)^{d/2} a^{-1/2}`, and
`wrep (Γ_a (jet φ)) = g_a ⋆ φ` for `φ ∈ C_c^∞` (`sa16r_Gam_cc`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution

section Heat7
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the constant `‖K_a‖₁` bound -/
def sa16r_cG (d : ℕ) (a : ℝ) : ℝ := 1 + d * (a ^ (-(1 / 2 : ℝ)) * (4 / 3 : ℝ) ^ ((d : ℝ) / 2))

lemma sa16r_cG_nonneg (d : ℕ) {a : ℝ} (ha : 0 < a) : 0 ≤ sa16r_cG d a := by
  unfold sa16r_cG
  have : 0 ≤ a ^ (-(1 / 2 : ℝ)) * (4 / 3 : ℝ) ^ ((d : ℝ) / 2) := by positivity
  positivity

lemma sa16r_heat_norm {a : ℝ} (ha : 0 < a) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (k : ℕ) :
    eLpNorm (wJet (k + 1) (sa16r_cv (sa16r_g d a) φ)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (sa16r_cG d a) * eLpNorm (wJet k φ) (ENNReal.ofReal p) volume := by
  have hp : (1 : ℝ) ≤ p := by have := (Fact.out : 2 ≤ p); linarith
  have hmc : Continuous (fun y => ‖wJet k φ y‖) := (sa16j_jet_cont hφ.1 k).norm
  have h1 : eLpNorm (wJet (k + 1) (sa16r_cv (sa16r_g d a) φ)) (ENNReal.ofReal p) volume ≤
      eLpNorm (sa16r_cv (sa16r_K d a) (fun y => ‖wJet k φ y‖)) (ENNReal.ofReal p) volume := by
    refine eLpNorm_mono (sa16j_jet_cont (sa16r_cv_contDiff ha hφ) (k + 1)).aestronglyMeasurable fun x => ?_
    refine (sa16r_jet_heat_pointwise ha hφ k x).trans ?_
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  refine h1.trans ((sa16r_young (sa16r_K_cont (d := d) a).measurable hmc hp).trans ?_)
  rw [eLpNorm_norm _ (sa16j_jet_cont hφ.1 k).aestronglyMeasurable]
  gcongr
  -- `∫⁻ ‖K‖ₑ ≤ ofReal (cG)`
  have hK : ∫⁻ z, ‖sa16r_K d a z‖ₑ = ENNReal.ofReal (∫ z, sa16r_K d a z) := by
    rw [ofReal_integral_eq_lintegral_ofReal (sa16r_K_int ha) (Eventually.of_forall (sa16r_K_nonneg ha))]
    refine lintegral_congr fun z => ?_
    rw [Real.enorm_eq_ofReal (sa16r_K_nonneg ha z)]
  rw [hK]
  exact ENNReal.ofReal_le_ofReal (sa16r_K_integral_le ha)

/-- the linear map `φ ↦ g_a ⋆ φ` from `C_c^∞` to `sa16r_S d (k+1) p` -/
def sa16r_heatL (d : ℕ) (p : ℝ) [Fact (2 ≤ p)] {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ccSub d →ₗ[ℝ] sa16r_S d (k + 1) p where
  toFun φ := ⟨sa16r_cv (sa16r_g d a) φ.1, sa16r_heat_mem ha φ.2 k⟩
  map_add' φ ψ := by
    apply Subtype.ext
    exact sa16r_cv_add (sa16r_g_int ha) φ.2 ψ.2
  map_smul' c φ := by
    apply Subtype.ext
    exact sa16r_cv_smul (sa16r_g d a) c φ.1

lemma sa16r_heatL_apply {a : ℝ} (ha : 0 < a) (k : ℕ) (φ : ccSub d) :
    ((sa16r_heatL d p ha k φ : sa16r_S d (k + 1) p) : Euc d → ℝ) = sa16r_cv (sa16r_g d a) φ.1 := rfl

lemma sa16r_heatL_bound {a : ℝ} (ha : 0 < a) (k : ℕ) (φ : ccSub d) :
    ‖sa16r_J d (k + 1) p (sa16r_heatL d p ha k φ)‖ ≤ sa16r_cG d a * ‖sa16r_Jcc d k p φ‖ := by
  have hS : MemLp (sa16j_S d (k + 1) (sa16r_heatL d p ha k φ).1) (ENNReal.ofReal p) volume :=
    sa16r_heat_S_memLp ha φ.2 k
  rw [sa16r_J_norm (f := sa16r_heatL d p ha k φ) (k + 1) hS, sa16r_Jcc_norm]
  have h := sa16r_heat_norm (p := p) ha φ.2 k
  have hfin : eLpNorm (wJet k φ.1) (ENNReal.ofReal p) volume ≠ ⊤ :=
    (sa16r_jet_memLp_cc φ.2 k).eLpNorm_lt_top.ne
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sa16r_cG_nonneg d ha)] at this
  exact this

/-- the gain operator -/
theorem sa16r_Gam_exists {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ∃ T : WmpSpace d k p →L[ℝ] WmpSpace d (k + 1) p, ‖T‖ ≤ sa16r_cG d a ∧
      ∀ φ, T (sa16r_Jcc d k p φ) = sa16r_J d (k + 1) p (sa16r_heatL d p ha k φ) := by
  obtain ⟨T, h1, h2, -⟩ := sa16r_extend_cc d k (k + 1) p (sa16r_heatL d p ha k) (sa16r_cG_nonneg d ha)
    (sa16r_heatL_bound ha k)
  exact ⟨T, h1, h2⟩

open Classical in
/-- `Γ_a`, zero for `a ≤ 0` -/
def sa16r_Gam (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] (a : ℝ) : WmpSpace d k p →L[ℝ] WmpSpace d (k + 1) p :=
  if h : 0 < a then Classical.choose (sa16r_Gam_exists (d := d) (p := p) h k) else 0

lemma sa16r_Gam_norm {a : ℝ} (ha : 0 < a) (k : ℕ) : ‖sa16r_Gam d k p a‖ ≤ sa16r_cG d a := by
  unfold sa16r_Gam
  rw [dif_pos ha]
  exact (Classical.choose_spec (sa16r_Gam_exists (d := d) (p := p) ha k)).1

lemma sa16r_Gam_jet {a : ℝ} (ha : 0 < a) (k : ℕ) (φ : ccSub d) :
    sa16r_Gam d k p a (sa16r_Jcc d k p φ) = sa16r_J d (k + 1) p (sa16r_heatL d p ha k φ) := by
  unfold sa16r_Gam
  rw [dif_pos ha]
  exact (Classical.choose_spec (sa16r_Gam_exists (d := d) (p := p) ha k)).2 φ

/-- zeroth component of `Γ_a` on jets of `C_c^∞` -/
lemma sa16r_Gam_cc {a : ℝ} (ha : 0 < a) (k : ℕ) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) :
    wrep d (k + 1) p (sa16r_Gam d k p a (sa16r_cc_elt hφ k)) =ᵐ[volume] sa16r_cv (sa16r_g d a) φ := by
  have h := sa16r_Gam_jet (p := p) ha k ⟨φ, hφ⟩
  rw [sa16r_Jcc_eq] at h
  rw [show sa16r_cc_elt hφ k = sa16r_cc_elt (⟨φ, hφ⟩ : ccSub d).2 k from rfl, h]
  exact sa16r_J_spec d (k + 1) p _

end Heat7

end HRS.Whole.AppendixA.Phase2SA16R
