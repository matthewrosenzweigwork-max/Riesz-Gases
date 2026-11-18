import HRS.MS.SA16RExt2
import HRS.MS.SA16JetSchwartz

/-!
# S.A.16 (SA16R) Ext3: extension from `C_c^∞`

`ccSub d`: the submodule `C_c^∞`; `sa16r_Jcc`: the jet class of `φ ∈ C_c^∞` in `WmpSpace d k p` (dense range);
`sa16r_extend_cc`: a linear map `𝓛 : C_c^∞ → sa16r_S d l p` with `‖J_l (𝓛 φ)‖ ≤ c ‖J_k φ‖` extends uniquely.
`sa16r_Jcc_norm`, `sa16r_J_norm`: norms are `L^p` norms of jets.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Ext3
variable (d k l : ℕ) (p : ℝ) [Fact (2 ≤ p)]

/-- `C_c^∞(ℝ^d)` as a submodule -/
def ccSub : Submodule ℝ (Euc d → ℝ) where
  carrier := {φ | IsCcInfty φ}
  add_mem' := fun ha hb => ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  smul_mem' := fun c _ hf => ⟨hf.1.const_smul c, hf.2.smul_left⟩

variable {d p}

lemma sa16r_jet_memLp_cc {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (k : ℕ) :
    MemLp (wJet k φ) (ENNReal.ofReal p) volume :=
  (sa16j_jet_cont hφ.1 k).memLp_of_hasCompactSupport (sa16j_jet_support hφ.2 k)

/-- the jet class of a `C_c^∞` function as an element of `WmpSpace` -/
def sa16r_cc_elt {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (k : ℕ) : WmpSpace d k p :=
  ⟨(sa16r_jet_memLp_cc (p := p) hφ k).toLp (wJet k φ), by
    unfold WmpSpace
    refine Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨φ, hφ, ?_⟩)
    exact (sa16r_jet_memLp_cc (p := p) hφ k).coeFn_toLp⟩

lemma sa16r_cc_elt_coe {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (k : ℕ) :
    (((sa16r_cc_elt (p := p) hφ k : WmpSpace d k p) : WLp d k p) : Euc d → (WIndex d k → ℝ))
      =ᵐ[volume] wJet k φ :=
  (sa16r_jet_memLp_cc (p := p) hφ k).coeFn_toLp

lemma sa16r_cc_elt_wrep {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (k : ℕ) :
    wrep d k p (sa16r_cc_elt hφ k) =ᵐ[volume] φ := by
  filter_upwards [sa16r_cc_elt_coe (p := p) hφ k] with x hx
  show ((((sa16r_cc_elt (p := p) hφ k : WmpSpace d k p) : WLp d k p) : Euc d → _) x) (wZero d k) = φ x
  rw [hx]
  simp only [wJet, wZero, partialDeriv]
  exact iteratedFDeriv_zero_apply _

lemma ccSub_le_S (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] : ccSub d ≤ sa16r_S d k p :=
  fun φ hφ => ⟨hφ.1, sa16r_cc_elt hφ k, sa16r_cc_elt_wrep hφ k⟩

/-- the jet class of `φ ∈ C_c^∞` -/
def sa16r_Jcc (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] : ccSub d →ₗ[ℝ] WmpSpace d k p :=
  (sa16r_J d k p).comp (Submodule.inclusion (ccSub_le_S d k p))

lemma sa16r_Jcc_eq (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] (φ : ccSub d) :
    sa16r_Jcc d k p φ = sa16r_cc_elt φ.2 k := by
  refine sa16r_wrep_inj d k p _ _ ?_
  filter_upwards [sa16r_J_spec d k p (Submodule.inclusion (ccSub_le_S d k p) φ),
    sa16r_cc_elt_wrep (p := p) φ.2 k] with x h1 h2
  rw [h2]
  exact h1

lemma sa16r_Jcc_dense (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] : DenseRange (sa16r_Jcc d k p) := by
  intro G
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  show (G : WLp d k p) ∈ closure (Subtype.val '' Set.range (sa16r_Jcc d k p))
  set N : Submodule ℝ (WLp d k p) :=
    (LinearMap.range (sa16r_Jcc d k p)).map (WmpSpace d k p).subtype with hN
  have hspan : Submodule.span ℝ {F : WLp d k p | ∃ φ : Euc d → ℝ, IsCcInfty φ ∧
      (F : Euc d → (WIndex d k → ℝ)) =ᵐ[volume] wJet k φ} ≤ N := by
    rw [Submodule.span_le]
    rintro F ⟨φ, hφ, hF⟩
    have hFmem : F ∈ WmpSpace d k p := by
      unfold WmpSpace
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨φ, hφ, hF⟩)
    refine ⟨sa16r_Jcc d k p ⟨φ, hφ⟩, ⟨⟨φ, hφ⟩, rfl⟩, ?_⟩
    rw [sa16r_Jcc_eq]
    refine Lp.ext ?_
    filter_upwards [sa16r_cc_elt_coe (p := p) hφ k, hF] with x h1 h2
    exact h1.trans h2.symm
  have h1 : (G : WLp d k p) ∈ (Submodule.span ℝ {F : WLp d k p | ∃ φ : Euc d → ℝ, IsCcInfty φ ∧
      (F : Euc d → (WIndex d k → ℝ)) =ᵐ[volume] wJet k φ}).topologicalClosure := G.2
  have h2 := Submodule.topologicalClosure_mono hspan h1
  have h3 : ((N : Set (WLp d k p))) = Subtype.val '' Set.range (sa16r_Jcc d k p) := by
    rw [hN, Submodule.map_coe, LinearMap.coe_range]
    rfl
  have h2' : (G : WLp d k p) ∈ closure ((N : Set (WLp d k p))) := h2
  rw [← h3]
  exact h2'

/-- **Extension principle from `C_c^∞`.** -/
theorem sa16r_extend_cc (d k l : ℕ) (p : ℝ) [Fact (2 ≤ p)] (𝓛 : ccSub d →ₗ[ℝ] sa16r_S d l p)
    {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ φ, ‖sa16r_J d l p (𝓛 φ)‖ ≤ c * ‖sa16r_Jcc d k p φ‖) :
    ∃ T : WmpSpace d k p →L[ℝ] WmpSpace d l p, ‖T‖ ≤ c ∧
      (∀ φ, T (sa16r_Jcc d k p φ) = sa16r_J d l p (𝓛 φ)) ∧
      ∀ T' : WmpSpace d k p →L[ℝ] WmpSpace d l p,
        (∀ φ, T' (sa16r_Jcc d k p φ) = sa16r_J d l p (𝓛 φ)) → T' = T :=
  sa16r_ext_abstract (sa16r_Jcc d k p) (sa16r_Jcc_dense d k p) ((sa16r_J d l p).comp 𝓛) hc hb

/-- the norm of the jet class of `φ ∈ C_c^∞` -/
lemma sa16r_Jcc_norm (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] (φ : ccSub d) :
    ‖sa16r_Jcc d k p φ‖ = (eLpNorm (wJet k φ.1) (ENNReal.ofReal p) volume).toReal := by
  rw [sa16r_Jcc_eq]
  show ‖(((sa16r_cc_elt (p := p) φ.2 k : WmpSpace d k p) : WLp d k p))‖ = _
  rw [Lp.norm_def, eLpNorm_congr_ae (sa16r_cc_elt_coe (p := p) φ.2 k)]

/-- a smooth function with `L^p` derivatives is in `sa16r_S` -/
lemma sa16r_mem_S {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hS : MemLp (sa16j_S d l f) (ENNReal.ofReal p) volume) : f ∈ sa16r_S d l p := by
  obtain ⟨G, hG⟩ := sa16j_jet_mem d l p hf hS
  refine ⟨hf, G, ?_⟩
  filter_upwards [hG] with x hx
  simp only [wrep]
  rw [hx]
  simp only [wJet, wZero, partialDeriv]
  exact iteratedFDeriv_zero_apply _

/-- the norm of `J f` for smooth `f` with `L^p` derivatives -/
lemma sa16r_J_norm {f : sa16r_S d l p} (hS : MemLp (sa16j_S d l f.1) (ENNReal.ofReal p) volume) :
    ‖sa16r_J d l p f‖ = (eLpNorm (wJet l f.1) (ENNReal.ofReal p) volume).toReal := by
  have h1 := sa16j_wNormE_eq d l p f.2.1 hS
  have h2 := wNormE_eq_lift_norm d l p (sa16r_J d l p f) f.1 (sa16r_J_spec d l p f)
  rw [h1] at h2
  have h3 : ENNReal.ofReal ‖sa16r_J d l p f‖ = eLpNorm (wJet l f.1) (ENNReal.ofReal p) volume := h2.symm
  have hfin : eLpNorm (wJet l f.1) (ENNReal.ofReal p) volume ≠ ⊤ := by rw [← h3]; exact ENNReal.ofReal_ne_top
  rw [← h3, ENNReal.toReal_ofReal (norm_nonneg _)]

end Ext3

end HRS.Whole.AppendixA.Phase2SA16R
