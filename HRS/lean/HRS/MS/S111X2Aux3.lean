import HRS.Whole.Q34Aux18
import HRS.MS.R2ScrAux1

/-!
# S11.1 X2, packet E01 (abstract part): the response form of a bounded positive operator

`KRep g ν K Mg`: `K` is a bounded symmetric nonnegative operator on `L²(ν)` with range in the centered classes that
represents `HRS.Whole.Kop g ν` on centered classes.  For `0 ≤ θ ≤ Γ` the choice-defined `HRS.Whole.responseInverse` is then a.e. the
resolvent `(I + θK)⁻¹` of the centered class of `P_ν f`, and `HRS.Whole.susceptibilityCov g ν θ` is the resolvent form, which is
linear, symmetric, coercive with constant `(1 + Γ Mg)⁻¹` and bounded by `‖P f‖ ‖P h‖`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MS.S111X2

open HRS.Whole HRS.Whole.Q34
open HRS (Euc)

/-! ### Hilbert space part -/

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A bounded symmetric nonnegative operator. -/
structure PosOp (K : H →L[ℝ] H) (Mg : ℝ) : Prop where
  symm : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y)
  pos : ∀ x, 0 ≤ inner ℝ (K x) x
  nonneg : 0 ≤ Mg
  bound : ∀ x, ‖K x‖ ≤ Mg * ‖x‖

theorem s111x2_resolvent {K : H →L[ℝ] H} {Mg : ℝ} (hK : PosOp K Mg) {θ : ℝ} (hθ : 0 ≤ θ) (f : H) :
    ∃ h : H, h + θ • K h = f ∧ (∀ h', h' + θ • K h' = f → h' = h) ∧
      ‖f‖ ^ 2 / (1 + θ * Mg) ≤ inner ℝ f h ∧ inner ℝ f h ≤ ‖f‖ ^ 2 ∧ ‖h‖ ≤ ‖f‖ := by
  rcases hθ.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨f, by simp, fun h' hh => by simpa using hh, ?_, ?_, le_rfl⟩
    · simp [real_inner_self_eq_norm_sq]
    · simp [real_inner_self_eq_norm_sq]
  · exact resolvent_exists K hK.symm hK.pos hK.nonneg hK.bound hpos f

/-- The resolvent `(I + θK)⁻¹`. -/
def s111x2_Res {K : H →L[ℝ] H} {Mg : ℝ} (hK : PosOp K Mg) {θ : ℝ} (hθ : 0 ≤ θ) (f : H) : H :=
  Classical.choose (s111x2_resolvent hK hθ f)

variable {K : H →L[ℝ] H} {Mg : ℝ} (hK : PosOp K Mg) {θ : ℝ} (hθ : 0 ≤ θ)
include hK hθ

theorem s111x2_Res_spec (f : H) : s111x2_Res hK hθ f + θ • K (s111x2_Res hK hθ f) = f :=
  (Classical.choose_spec (s111x2_resolvent hK hθ f)).1

theorem s111x2_Res_unique {f h : H} (hh : h + θ • K h = f) : h = s111x2_Res hK hθ f :=
  (Classical.choose_spec (s111x2_resolvent hK hθ f)).2.1 h hh

theorem s111x2_Res_add (f g : H) :
    s111x2_Res hK hθ (f + g) = s111x2_Res hK hθ f + s111x2_Res hK hθ g := by
  symm
  apply s111x2_Res_unique hK hθ
  have h1 := s111x2_Res_spec hK hθ f
  have h2 := s111x2_Res_spec hK hθ g
  rw [map_add, smul_add]
  calc _ = (s111x2_Res hK hθ f + θ • K (s111x2_Res hK hθ f)) +
        (s111x2_Res hK hθ g + θ • K (s111x2_Res hK hθ g)) := by abel
    _ = f + g := by rw [h1, h2]

theorem s111x2_Res_smul (c : ℝ) (f : H) :
    s111x2_Res hK hθ (c • f) = c • s111x2_Res hK hθ f := by
  symm
  apply s111x2_Res_unique hK hθ
  have h1 := s111x2_Res_spec hK hθ f
  rw [map_smul, smul_comm θ c, ← smul_add, h1]

theorem s111x2_Res_symm (f g : H) :
    inner ℝ (s111x2_Res hK hθ f) g = inner ℝ f (s111x2_Res hK hθ g) := by
  set a := s111x2_Res hK hθ f
  set b := s111x2_Res hK hθ g
  have hf := s111x2_Res_spec hK hθ f
  have hg := s111x2_Res_spec hK hθ g
  have e1 : inner ℝ a g = inner ℝ a b + θ * inner ℝ a (K b) := by
    conv_lhs => rw [← hg]
    rw [inner_add_right, inner_smul_right]
  have e2 : inner ℝ f b = inner ℝ a b + θ * inner ℝ (K a) b := by
    conv_lhs => rw [← hf]
    rw [inner_add_left, inner_smul_left]
    simp
    rfl
  rw [e1, e2, hK.symm a b]

theorem s111x2_Res_bounds (f : H) :
    ‖f‖ ^ 2 / (1 + θ * Mg) ≤ inner ℝ f (s111x2_Res hK hθ f) ∧
      inner ℝ f (s111x2_Res hK hθ f) ≤ ‖f‖ ^ 2 ∧ ‖s111x2_Res hK hθ f‖ ≤ ‖f‖ := by
  obtain ⟨h, hs, hu, h1, h2, h3⟩ := s111x2_resolvent hK hθ f
  have : h = s111x2_Res hK hθ f := s111x2_Res_unique hK hθ hs
  rw [← this]; exact ⟨h1, h2, h3⟩

end Hilbert

/-! ### Measure part -/

section MeasurePart

variable {d : ℕ} {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {g : Euc d → ℝ}

/-- `K` represents `HRS.Whole.Kop g ν` on the centered classes. -/
structure KRep (g : Euc d → ℝ) (ν : Measure (Euc d)) [IsProbabilityMeasure ν]
    (K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (Mg : ℝ) : Prop where
  symm : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y)
  pos : ∀ x, 0 ≤ inner ℝ (K x) x
  nonneg : 0 ≤ Mg
  bound : ∀ x, ‖K x‖ ≤ Mg * ‖x‖
  pc : ∀ U, Pc ν (K U) = K U
  kop : ∀ U : Lp ℝ 2 ν, Pc ν U = U → HRS.Whole.Kop g ν (U : Euc d → ℝ) =ᵐ[ν] (K U : Euc d → ℝ)

theorem KRep.posOp {K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν} {Mg : ℝ} (h : KRep g ν K Mg) : PosOp K Mg :=
  ⟨h.symm, h.pos, h.nonneg, h.bound⟩

/-- `∫ (P f)² dν`, the squared norm of the centered part. -/
def s111x2_centeredSquare (ν : Measure (Euc d)) (f : Euc d → ℝ) : ℝ := ∫ x, (HRS.Whole.projMean ν f x) ^ 2 ∂ν

theorem s111x2_memL2Zero_projMean {f : Euc d → ℝ} (hf : MemLp f 2 ν) : HRS.Whole.MemL2Zero ν (HRS.Whole.projMean ν f) := by
  refine ⟨hf.sub (memLp_const _), ?_⟩
  have h1 : Integrable f ν := hf.integrable (by norm_num)
  simp only [HRS.Whole.projMean, HRS.Whole.pair]
  rw [integral_sub h1 (integrable_const _), integral_const]
  simp

/-- The centered class of `P_ν f`. -/
def s111x2_cl {f : Euc d → ℝ} (hf : MemLp f 2 ν) : Lp ℝ 2 ν :=
  (exists_class (s111x2_memL2Zero_projMean hf)).choose

theorem s111x2_cl_ae {f : Euc d → ℝ} (hf : MemLp f 2 ν) :
    HRS.Whole.projMean ν f =ᵐ[ν] (s111x2_cl hf : Euc d → ℝ) :=
  (exists_class (s111x2_memL2Zero_projMean hf)).choose_spec.1

theorem s111x2_cl_pc {f : Euc d → ℝ} (hf : MemLp f 2 ν) : Pc ν (s111x2_cl hf) = s111x2_cl hf :=
  (exists_class (s111x2_memL2Zero_projMean hf)).choose_spec.2

theorem s111x2_cl_norm_sq {f : Euc d → ℝ} (hf : MemLp f 2 ν) :
    ‖s111x2_cl hf‖ ^ 2 = s111x2_centeredSquare ν f :=
  (integral_sq_eq (s111x2_cl_ae hf)).symm

variable {K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν} {Mg : ℝ} (hK : KRep g ν K Mg) {θ : ℝ} (hθ : 0 ≤ θ)
include hK hθ

/-- Existence of the response. -/
theorem s111x2_resp_exists {ψ : Euc d → ℝ} (hψ : MemLp ψ 2 ν) :
    HRS.Whole.IsResponse g ν θ ψ ((s111x2_Res hK.posOp hθ (s111x2_cl hψ) : Lp ℝ 2 ν) : Euc d → ℝ) := by
  set F := s111x2_cl hψ with hF
  set H := s111x2_Res hK.posOp hθ F with hH
  have hsol : H + θ • K H = F := s111x2_Res_spec hK.posOp hθ F
  have hPH : Pc ν H = H := by
    have h1 := congrArg (Pc ν) hsol
    rw [map_add, map_smul, hK.pc, s111x2_cl_pc hψ] at h1
    have h2 : Pc ν H + θ • K H = H + θ • K H := h1.trans hsol.symm
    exact add_right_cancel h2
  refine ⟨⟨Lp.memLp H, ?_⟩, ?_⟩
  · rw [← inner_one2]
    calc inner ℝ (one2 ν) H = inner ℝ (one2 ν) (Pc ν H) := by rw [hPH]
      _ = 0 := inner_one2_Pc H
  · have hsol' : ((H + θ • K H : Lp ℝ 2 ν) : Euc d → ℝ) = (F : Euc d → ℝ) := by rw [hsol]
    filter_upwards [Lp.coeFn_add H (θ • K H), Lp.coeFn_smul θ (K H), hK.kop H hPH,
      s111x2_cl_ae hψ] with x h1 h2 h3 h4
    have e1 := congrFun hsol' x
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, ← h3] at e1
    rw [h4]; exact e1

/-- Uniqueness of the response. -/
theorem s111x2_resp_unique {ψ h : Euc d → ℝ} (hψ : MemLp ψ 2 ν) (hr : HRS.Whole.IsResponse g ν θ ψ h) :
    h =ᵐ[ν] ((s111x2_Res hK.posOp hθ (s111x2_cl hψ) : Lp ℝ 2 ν) : Euc d → ℝ) := by
  obtain ⟨U, hU, hPU⟩ := exists_class hr.1
  have e : U + θ • K U = s111x2_cl hψ := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add U (θ • K U), Lp.coeFn_smul θ (K U), hK.kop U hPU, hU, hr.2,
      s111x2_cl_ae hψ] with x h1 h2 h3 h4 h6 h7
    have hkc : HRS.Whole.Kop g ν h x = HRS.Whole.Kop g ν (U : Euc d → ℝ) x := congrFun (HRS.MS.S98.s98_kop_congr_ae hU) x
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, ← h3, ← hkc, ← h4, h6, ← h7]
  have hUe := s111x2_Res_unique hK.posOp hθ e
  rw [hUe] at hU
  exact hU

/-- `HRS.Whole.responseInverse` is a.e. the resolvent of the centered class. -/
theorem s111x2_responseInverse_ae {ψ : Euc d → ℝ} (hψ : MemLp ψ 2 ν) :
    HRS.Whole.responseInverse g ν θ ψ =ᵐ[ν] ((s111x2_Res hK.posOp hθ (s111x2_cl hψ) : Lp ℝ 2 ν) : Euc d → ℝ) := by
  have hex : ∃ h, HRS.Whole.IsResponse g ν θ ψ h := ⟨_, s111x2_resp_exists hK hθ hψ⟩
  have hr : HRS.Whole.IsResponse g ν θ ψ (HRS.Whole.responseInverse g ν θ ψ) := by
    unfold HRS.Whole.responseInverse
    rw [dif_pos hex]
    exact hex.choose_spec
  exact s111x2_resp_unique hK hθ hψ hr

theorem s111x2_susc_eq {φ ψ : Euc d → ℝ} (hφ : MemLp φ 2 ν) (hψ : MemLp ψ 2 ν) :
    HRS.Whole.susceptibilityCov g ν θ φ ψ =
      inner ℝ (s111x2_cl hφ) (s111x2_Res hK.posOp hθ (s111x2_cl hψ)) := by
  unfold HRS.Whole.susceptibilityCov
  exact l2Inner_eq (s111x2_cl_ae hφ) (s111x2_responseInverse_ae hK hθ hψ)

end MeasurePart

end HRS.MS.S111X2
