import HRS.MS.ZeroTempAux5

/-!
# SA11, packet B2: the transposed propagator `T`, the transported field `Z`, the particle field `Ξ`

* `Sa11TransportData`: the hypotheses at one `(C, t)`: the adjoint input `AdjointInputRd (wClass m p) (wWeakClass m p) j C T K`
  and the linearity of `φ ↦ U^{0,t}φ` on `C_c^∞` (`sa11_propagatorW_lin`).
* `sa11_Phi`, `sa11_Top`: the bounded operator `T : W^{m,p} → W^{m,p}` with `T (J φ) =` the weak jet of `U^{0,t}φ`.
* `sa11_Z`: `Z ζ = η(ζ) ∘ T`; `IsTransportedWRepr` holds for every `ζ`.
* `sa11_Xi`: the particle field `Ξ ζ = σ (μ_N^t - ρ_N^t)` as an element of the dual, continuous in the particle configuration.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal ContDiff

namespace HRS.MS.ZeroTemp

variable {d : ℕ} {m : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa11_isClosed : IsClosed (WmpSpace d m p : Set (WLp d m p)) := Submodule.isClosed_topologicalClosure _

instance sa11_complete : CompleteSpace (WmpSpace d m p) := (sa11_isClosed (d := d) (m := m) (p := p)).completeSpace_coe

theorem sa11_cd2 {φ : Euc d → ℝ} (hφ : IsCcInfty φ) : ContDiff ℝ 2 φ :=
  hφ.1.of_le (by simp)

theorem sa11_zeroth_add (F G : WmpSpace d m p) :
    (fun x => (((F + G : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m)) =ᵐ[volume]
      fun x => ((F : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) +
        ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) := by
  filter_upwards [Lp.coeFn_add (F : WLp d m p) (G : WLp d m p)] with x hx
  exact congrFun hx (wZero d m)

theorem sa11_zeroth_smul (c : ℝ) (F : WmpSpace d m p) :
    (fun x => (((c • F : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m)) =ᵐ[volume]
      fun x => c * ((F : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) := by
  filter_upwards [Lp.coeFn_smul c (F : WLp d m p)] with x hx
  exact congrFun hx (wZero d m)

/-- an element of `W^{-m,p'}` as a continuous linear functional on `W^{m,p}` -/
abbrev sa11_dual (ξ : WNeg d m p) : WmpSpace d m p →L[ℝ] ℝ := ξ

/-! ### The transposed propagator -/

section Transport

/-- Hypotheses at one coefficient `C` and one time `t ∈ [0,T]`. -/
structure Sa11TransportData (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (C : WholeCoeff d) (T K : ℝ) (j : ℕ) (t : ℝ) : Prop where
  ht : t ∈ Set.Icc (0 : ℝ) T
  adj : AdjointInputRd (wClass m p) (wWeakClass m p) j C T K
  lin : ∀ (φ ψ : Euc d → ℝ) (c : ℝ), IsCcInfty φ → IsCcInfty ψ →
    propagatorW C 0 t (fun x => φ x + c * ψ x) = fun x => propagatorW C 0 t φ x + c * propagatorW C 0 t ψ x

variable {C : WholeCoeff d} {T K : ℝ} {j : ℕ} {t : ℝ}

theorem sa11_U_mem (h : Sa11TransportData m p C T K j t) (φ : sa11_V d) :
    (wWeakClass (d := d) m p).mem (propagatorW C 0 t φ.1) :=
  (h.adj 0 t le_rfl h.ht.1 h.ht.2 φ.1 (sa11_cd2 φ.2) (sa11_wClass_mem φ)).2.1

/-- the weak jet of `U^{0,t}φ` -/
def sa11_Phi0 (h : Sa11TransportData m p C T K j t) (φ : sa11_V d) : WmpSpace d m p :=
  Classical.choose (sa11_exists_weakJet (sa11_U_mem h φ))

theorem sa11_Phi0_spec (h : Sa11TransportData m p C T K j t) (φ : sa11_V d) :
    ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((sa11_Phi0 h φ : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = propagatorW C 0 t φ.1 x :=
  Classical.choose_spec (sa11_exists_weakJet (sa11_U_mem h φ))

theorem sa11_Phi0_norm (h : Sa11TransportData m p C T K j t) (φ : sa11_V d) :
    ‖sa11_Phi0 h φ‖ ≤ max K 0 * sa11_cJ d m * ‖sa11_J (m := m) (p := p) φ‖ := by
  have h1 : ‖sa11_Phi0 h φ‖ = (wWeakClass (d := d) m p).norm (propagatorW C 0 t φ.1) :=
    (sa11_wWeak_norm_eq (sa11_Phi0_spec h φ)).symm
  have h2 := (h.adj 0 t le_rfl h.ht.1 h.ht.2 φ.1 (sa11_cd2 φ.2) (sa11_wClass_mem φ)).2.2.1
  have h3 := sa11_wClass_norm_le (m := m) (p := p) φ
  have h4 : 0 ≤ (wClass (d := d) m p).norm φ.1 := ENNReal.toReal_nonneg
  rw [h1]
  calc (wWeakClass (d := d) m p).norm (propagatorW C 0 t φ.1) ≤ K * (wClass (d := d) m p).norm φ.1 := h2
    _ ≤ max K 0 * (wClass (d := d) m p).norm φ.1 := mul_le_mul_of_nonneg_right (le_max_left _ _) h4
    _ ≤ max K 0 * (sa11_cJ d m * ‖sa11_J (m := m) (p := p) φ‖) :=
        mul_le_mul_of_nonneg_left h3 (le_max_right _ _)
    _ = _ := by ring

theorem sa11_U_zero (h : Sa11TransportData m p C T K j t) : propagatorW C 0 t (fun _ : Euc d => (0 : ℝ)) = fun _ => 0 := by
  have h0 : IsCcInfty (fun _ : Euc d => (0 : ℝ)) := ⟨contDiff_const, HasCompactSupport.zero⟩
  have := h.lin _ _ 1 h0 h0
  have e : (fun x : Euc d => (0 : ℝ) + 1 * 0) = fun _ => 0 := by funext x; ring
  rw [e] at this
  funext x
  have hx := congrFun this x
  simp only at hx
  linarith

/-- the weak-jet map `C_c^∞ → W^{m,p}` is linear -/
def sa11_Phi (h : Sa11TransportData m p C T K j t) : sa11_V d →ₗ[ℝ] WmpSpace d m p where
  toFun := sa11_Phi0 h
  map_add' a b := by
    apply sa11_eq_of_zeroth
    have h1 := sa11_Phi0_spec h (a + b)
    have h2 := sa11_Phi0_spec h a
    have h3 := sa11_Phi0_spec h b
    have h4 := sa11_zeroth_add (sa11_Phi0 h a) (sa11_Phi0 h b)
    have hl := congrFun (h.lin a.1 b.1 1 a.2 b.2)
    filter_upwards [h1, h2, h3, h4] with x e1 e2 e3 e4
    have e5 : propagatorW C 0 t (a + b).1 x = propagatorW C 0 t a.1 x + propagatorW C 0 t b.1 x := by
      have := hl x
      simp only [one_mul] at this
      exact this
    rw [e1, e4, e2, e3, e5]
  map_smul' c a := by
    apply sa11_eq_of_zeroth
    have h1 := sa11_Phi0_spec h (c • a)
    have h2 := sa11_Phi0_spec h a
    have h4 := sa11_zeroth_smul c (sa11_Phi0 h a)
    have hl := congrFun (h.lin (fun _ => 0) a.1 c ⟨contDiff_const, HasCompactSupport.zero⟩ a.2)
    have hz := sa11_U_zero h
    filter_upwards [h1, h2, h4] with x e1 e2 e4
    have e5 : propagatorW C 0 t (c • a).1 x = c * propagatorW C 0 t a.1 x := by
      have := hl x
      have e : (fun y : Euc d => (0 : ℝ) + c * a.1 y) = (c • a).1 := by funext y; simp
      rw [e, congrFun hz x] at this
      simpa using this
    simp only [RingHom.id_apply]
    rw [e4, e1, e2, e5]

theorem sa11_Phi_apply (h : Sa11TransportData m p C T K j t) (φ : sa11_V d) : sa11_Phi h φ = sa11_Phi0 h φ := rfl

/-- The transposed propagator `T : W^{m,p} → W^{m,p}`. -/
def sa11_Top (h : Sa11TransportData m p C T K j t) : WmpSpace d m p →L[ℝ] WmpSpace d m p :=
  sa11_ext (m := m) (p := p) (sa11_Phi h)

theorem sa11_Top_apply (h : Sa11TransportData m p C T K j t) (φ : sa11_V d) :
    sa11_Top h (sa11_J (m := m) (p := p) φ) = sa11_Phi0 h φ :=
  sa11_ext_apply (m := m) (p := p) (sa11_Phi h) (C := max K 0 * sa11_cJ d m)
    (fun φ => sa11_Phi0_norm h φ) φ

theorem sa11_Top_norm (h : Sa11TransportData m p C T K j t) : ‖sa11_Top h‖ ≤ max K 0 * sa11_cJ d m :=
  sa11_ext_norm_le (m := m) (p := p) (sa11_Phi h) (mul_nonneg (le_max_right _ _) (sa11_cJ_nonneg d m))
    (fun φ => sa11_Phi0_norm h φ)

end Transport

/-! ### The transported field `Z` -/

/-- precomposition with `T` on the dual -/
def sa11_precomp (T : WmpSpace d m p →L[ℝ] WmpSpace d m p) :
    (WmpSpace d m p →L[ℝ] ℝ) →L[ℝ] (WmpSpace d m p →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ (WmpSpace d m p) (WmpSpace d m p) ℝ).flip T

theorem sa11_precomp_apply (T : WmpSpace d m p →L[ℝ] WmpSpace d m p) (L : WmpSpace d m p →L[ℝ] ℝ)
    (F : WmpSpace d m p) : sa11_precomp T L F = L (T F) := rfl

theorem sa11_precomp_norm_le (T : WmpSpace d m p →L[ℝ] WmpSpace d m p) (L : WmpSpace d m p →L[ℝ] ℝ) :
    ‖sa11_precomp T L‖ ≤ ‖T‖ * ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun F => ?_
  rw [sa11_precomp_apply]
  calc ‖L (T F)‖ ≤ ‖L‖ * ‖T F‖ := L.le_opNorm _
    _ ≤ ‖L‖ * (‖T‖ * ‖F‖) := mul_le_mul_of_nonneg_left (T.le_opNorm F) (ContinuousLinearMap.opNorm_nonneg L)
    _ = ‖T‖ * ‖L‖ * ‖F‖ := by ring

section ZRepr

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {N : ℕ} {C : WholeCoeff d} {T K : ℝ} {j : ℕ} {t : ℝ}

/-- `Z = η ∘ T` represents the transported linear approximation (for every `ζ`). -/
theorem sa11_isTransported (hAN : S.AN N = 1) (h : Sa11TransportData m p (S.coeff N) S.T K j t)
    (ηW : (R N).Ω → WNeg d m p) :
    IsTransportedWRepr S R N m p t ηW
      (fun ζ => (sa11_precomp (sa11_Top h) (sa11_dual (ηW ζ)) : WNeg d m p)) := by
  intro φ hφ F G hF hG
  refine Filter.Eventually.of_forall fun ζ => ?_
  have hFJ : F = sa11_J (m := m) (p := p) ⟨φ, hφ⟩ := sa11_eq_J (φ := ⟨φ, hφ⟩) hF
  have hGP : G = sa11_Phi0 h ⟨φ, hφ⟩ :=
    sa11_eq_of_zeroth (hG.mp ((sa11_Phi0_spec h ⟨φ, hφ⟩).mono fun x h1 h2 => h2.trans h1.symm))
  rw [hAN, one_mul]
  show sa11_precomp (sa11_Top h) (sa11_dual (ηW ζ)) F = (sa11_dual (ηW ζ)) G
  rw [sa11_precomp_apply, hFJ, sa11_Top_apply, hGP]

theorem sa11_Z_measurable (T' : WmpSpace d m p →L[ℝ] WmpSpace d m p) (ηW : (R N).Ω → WNeg d m p)
    (hη : Measurable ηW) :
    Measurable (fun ζ => (sa11_precomp T' (sa11_dual (ηW ζ)) : WNeg d m p)) := by
  have hc : Continuous (fun L : WNeg d m p => (sa11_precomp T' (L : WmpSpace d m p →L[ℝ] ℝ) : WNeg d m p)) :=
    (sa11_precomp T').continuous
  exact hc.measurable.comp hη

end ZRepr

/-! ### The particle field `Ξ` -/

section XiRepr

variable (hd : 1 ≤ d) (hm : mStar d + ⌊(d : ℝ) / p⌋₊ + 1 ≤ m)

/-- `φ ↦ N⁻¹ ∑ φ(x_i)` on `C_c^∞` -/
def sa11_empL {N : ℕ} (X : EucConfig d N) : sa11_V d →ₗ[ℝ] ℝ where
  toFun φ := (N : ℝ)⁻¹ * ∑ i, φ.1 (X i)
  map_add' a b := by
    simp only [Submodule.coe_add, Pi.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' c a := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

/-- `φ ↦ σ (N⁻¹ ∑ φ(x_i) - ∫ φ ρ)` on `C_c^∞` -/
def sa11_xiL {N : ℕ} (σ : ℝ) (X : EucConfig d N) (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity ρ) :
    sa11_V d →ₗ[ℝ] ℝ :=
  haveI := sa11_isProb hρ
  σ • (sa11_empL X - sa11_intL (HRS.Whole.withDensityReal ρ))

include hd hm

theorem sa11_empL_bound {N : ℕ} (X : EucConfig d N) (φ : sa11_V d) :
    ‖sa11_empL X φ‖ ≤ sa11_Cemb (m := m) (p := p) hd hm * ‖sa11_J (m := m) (p := p) φ‖ := by
  have hb : ∀ x, ‖φ.1 x‖ ≤ sa11_Cemb (m := m) (p := p) hd hm * ‖sa11_J (m := m) (p := p) φ‖ := fun x => by
    have := sa11_Cemb_spec (m := m) (p := p) hd hm φ 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this
  show ‖(N : ℝ)⁻¹ * ∑ i, φ.1 (X i)‖ ≤ _
  rw [norm_mul]
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    have := mul_nonneg (sa11_Cemb_nonneg (m := m) (p := p) hd hm) (norm_nonneg (sa11_J (m := m) (p := p) φ))
    simpa using this
  · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : ‖∑ i, φ.1 (X i)‖ ≤ N * (sa11_Cemb (m := m) (p := p) hd hm * ‖sa11_J (m := m) (p := p) φ‖) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i, ‖φ.1 (X i)‖ ≤ ∑ _i : Fin N, (sa11_Cemb (m := m) (p := p) hd hm * ‖sa11_J (m := m) (p := p) φ‖) :=
            Finset.sum_le_sum fun i _ => hb _
        _ = _ := by simp
    rw [norm_inv, Real.norm_natCast]
    calc (N : ℝ)⁻¹ * ‖∑ i, φ.1 (X i)‖ ≤ (N : ℝ)⁻¹ * (N * (sa11_Cemb (m := m) (p := p) hd hm * ‖sa11_J (m := m) (p := p) φ‖)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by field_simp

theorem sa11_empL_lip_bound {N : ℕ} (X Y : EucConfig d N) (φ : sa11_V d) :
    ‖(sa11_empL X - sa11_empL Y) φ‖ ≤
      (sa11_Cemb (m := m) (p := p) hd hm * dist X Y) * ‖sa11_J (m := m) (p := p) φ‖ := by
  have hdc : ∀ x y : Euc d, ‖φ.1 x - φ.1 y‖ ≤ sa11_Cemb (m := m) (p := p) hd hm * ‖sa11_J (m := m) (p := p) φ‖ * ‖x - y‖ := by
    intro x y
    have hder : ∀ z ∈ (Set.univ : Set (Euc d)),
        ‖fderiv ℝ φ.1 z‖ ≤ sa11_Cemb (m := m) (p := p) hd hm * ‖sa11_J (m := m) (p := p) φ‖ := by
      intro z _
      have h1 := sa11_Cemb_spec (m := m) (p := p) hd hm φ 1 (by unfold mStar; omega) z
      rwa [norm_iteratedFDeriv_one] at h1
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := φ.1) (s := Set.univ)
      (fun z _ => (φ.2.1.differentiable (by simp)) z) hder convex_univ (Set.mem_univ y) (Set.mem_univ x)
  have hC0 := sa11_Cemb_nonneg (m := m) (p := p) hd hm
  show ‖(N : ℝ)⁻¹ * ∑ i, φ.1 (X i) - (N : ℝ)⁻¹ * ∑ i, φ.1 (Y i)‖ ≤ _
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0; simp; exact mul_nonneg (mul_nonneg hC0 dist_nonneg) (norm_nonneg _)
  · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul]
    have h1 : ‖∑ i, (φ.1 (X i) - φ.1 (Y i))‖ ≤
        N * (sa11_Cemb (m := m) (p := p) hd hm * ‖sa11_J (m := m) (p := p) φ‖ * dist X Y) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i, ‖φ.1 (X i) - φ.1 (Y i)‖
          ≤ ∑ _i : Fin N, (sa11_Cemb (m := m) (p := p) hd hm * ‖sa11_J (m := m) (p := p) φ‖ * dist X Y) := by
            refine Finset.sum_le_sum fun i _ => ?_
            refine (hdc _ _).trans ?_
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 (norm_nonneg _))
            rw [← dist_eq_norm]
            exact dist_le_pi_dist X Y i
        _ = _ := by simp
    rw [norm_inv, Real.norm_natCast]
    calc (N : ℝ)⁻¹ * ‖∑ i, (φ.1 (X i) - φ.1 (Y i))‖
        ≤ (N : ℝ)⁻¹ * (N * (sa11_Cemb (m := m) (p := p) hd hm * ‖sa11_J (m := m) (p := p) φ‖ * dist X Y)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by field_simp

omit hd hm in
/-- `σ (μ_N - ρ)` as a functional on `W^{m,p}`. -/
def sa11_Xi {N : ℕ} (σ : ℝ) (X : EucConfig d N) (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity ρ) :
    WmpSpace d m p →L[ℝ] ℝ :=
  sa11_ext (m := m) (p := p) (sa11_xiL σ X ρ hρ)

theorem sa11_Xi_apply {N : ℕ} (σ : ℝ) (X : EucConfig d N) (ρ : Euc d → ℝ)
    (hρ : HRS.Whole.IsProbDensity ρ) (φ : sa11_V d) :
    sa11_Xi (m := m) (p := p) σ X ρ hρ (sa11_J (m := m) (p := p) φ) =
      σ * ((N : ℝ)⁻¹ * ∑ i, φ.1 (X i) - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) φ.1) := by
  haveI := sa11_isProb hρ
  have hb : ∀ φ : sa11_V d, ‖sa11_xiL σ X ρ hρ φ‖ ≤ (|σ| * (2 * sa11_Cemb (m := m) (p := p) hd hm)) *
      ‖sa11_J (m := m) (p := p) φ‖ := by
    intro φ
    show ‖σ * ((sa11_empL X) φ - (sa11_intL (HRS.Whole.withDensityReal ρ)) φ)‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs]
    have h1 := sa11_empL_bound (m := m) (p := p) hd hm X φ
    have h2 := sa11_intL_bound (m := m) (p := p) hm (sa11_Cemb_spec (m := m) (p := p) hd hm)
      (HRS.Whole.withDensityReal ρ) φ
    calc |σ| * ‖(sa11_empL X) φ - (sa11_intL (HRS.Whole.withDensityReal ρ)) φ‖
        ≤ |σ| * (sa11_Cemb (m := m) (p := p) hd hm * ‖sa11_J (m := m) (p := p) φ‖ +
          sa11_Cemb (m := m) (p := p) hd hm * ‖sa11_J (m := m) (p := p) φ‖) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add h1 h2)) (abs_nonneg _)
      _ = _ := by ring
  unfold sa11_Xi
  rw [sa11_ext_apply _ hb]
  rfl

theorem sa11_Xi_lip {N : ℕ} (σ : ℝ) (X Y : EucConfig d N) (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity ρ) :
    ‖sa11_Xi (m := m) (p := p) σ X ρ hρ - sa11_Xi (m := m) (p := p) σ Y ρ hρ‖ ≤
      (|σ| * sa11_Cemb (m := m) (p := p) hd hm) * dist X Y := by
  haveI := sa11_isProb hρ
  set ℓ : sa11_V d →ₗ[ℝ] ℝ := σ • (sa11_empL X - sa11_empL Y) with hℓ
  have hbℓ : ∀ φ : sa11_V d, ‖ℓ φ‖ ≤ ((|σ| * sa11_Cemb (m := m) (p := p) hd hm) * dist X Y) *
      ‖sa11_J (m := m) (p := p) φ‖ := by
    intro φ
    show ‖σ * ((sa11_empL X - sa11_empL Y) φ)‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs]
    calc |σ| * ‖(sa11_empL X - sa11_empL Y) φ‖
        ≤ |σ| * ((sa11_Cemb (m := m) (p := p) hd hm * dist X Y) * ‖sa11_J (m := m) (p := p) φ‖) :=
          mul_le_mul_of_nonneg_left (sa11_empL_lip_bound (m := m) (p := p) hd hm X Y φ) (abs_nonneg _)
      _ = _ := by ring
  have hbX : ∀ φ : sa11_V d, ‖sa11_xiL σ X ρ hρ φ‖ ≤ (|σ| * (2 * sa11_Cemb (m := m) (p := p) hd hm)) *
      ‖sa11_J (m := m) (p := p) φ‖ := by
    intro φ
    show ‖σ * ((sa11_empL X) φ - (sa11_intL (HRS.Whole.withDensityReal ρ)) φ)‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs]
    have h1 := sa11_empL_bound (m := m) (p := p) hd hm X φ
    have h2 := sa11_intL_bound (m := m) (p := p) hm (sa11_Cemb_spec (m := m) (p := p) hd hm)
      (HRS.Whole.withDensityReal ρ) φ
    calc |σ| * ‖(sa11_empL X) φ - (sa11_intL (HRS.Whole.withDensityReal ρ)) φ‖
        ≤ |σ| * (sa11_Cemb (m := m) (p := p) hd hm * ‖sa11_J (m := m) (p := p) φ‖ +
          sa11_Cemb (m := m) (p := p) hd hm * ‖sa11_J (m := m) (p := p) φ‖) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add h1 h2)) (abs_nonneg _)
      _ = _ := by ring
  have hbY : ∀ φ : sa11_V d, ‖sa11_xiL σ Y ρ hρ φ‖ ≤ (|σ| * (2 * sa11_Cemb (m := m) (p := p) hd hm)) *
      ‖sa11_J (m := m) (p := p) φ‖ := by
    intro φ
    show ‖σ * ((sa11_empL Y) φ - (sa11_intL (HRS.Whole.withDensityReal ρ)) φ)‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs]
    have h1 := sa11_empL_bound (m := m) (p := p) hd hm Y φ
    have h2 := sa11_intL_bound (m := m) (p := p) hm (sa11_Cemb_spec (m := m) (p := p) hd hm)
      (HRS.Whole.withDensityReal ρ) φ
    calc |σ| * ‖(sa11_empL Y) φ - (sa11_intL (HRS.Whole.withDensityReal ρ)) φ‖
        ≤ |σ| * (sa11_Cemb (m := m) (p := p) hd hm * ‖sa11_J (m := m) (p := p) φ‖ +
          sa11_Cemb (m := m) (p := p) hd hm * ‖sa11_J (m := m) (p := p) φ‖) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add h1 h2)) (abs_nonneg _)
      _ = _ := by ring
  have hEq : sa11_Xi (m := m) (p := p) σ X ρ hρ - sa11_Xi (m := m) (p := p) σ Y ρ hρ =
      sa11_ext (m := m) (p := p) ℓ := by
    refine sa11_ext_unique ℓ hbℓ _ fun φ => ?_
    rw [ContinuousLinearMap.sub_apply, sa11_Xi_apply hd hm, sa11_Xi_apply hd hm]
    show _ = σ * (((N : ℝ)⁻¹ * ∑ i, φ.1 (X i)) - ((N : ℝ)⁻¹ * ∑ i, φ.1 (Y i)))
    ring
  rw [hEq]
  exact sa11_ext_norm_le ℓ (mul_nonneg (mul_nonneg (abs_nonneg _) (sa11_Cemb_nonneg hd hm)) dist_nonneg) hbℓ

theorem sa11_Xi_continuous {N : ℕ} (σ : ℝ) (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity ρ) :
    Continuous (fun X : EucConfig d N => sa11_Xi (m := m) (p := p) σ X ρ hρ) := by
  have hlip : LipschitzWith ⟨|σ| * sa11_Cemb (m := m) (p := p) hd hm,
      mul_nonneg (abs_nonneg _) (sa11_Cemb_nonneg hd hm)⟩
      (fun X : EucConfig d N => sa11_Xi (m := m) (p := p) σ X ρ hρ) :=
    LipschitzWith.of_dist_le_mul fun X Y => by
      rw [dist_eq_norm]
      exact sa11_Xi_lip hd hm σ X Y ρ hρ
  exact hlip.continuous

theorem sa11_Xi_measurable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (σ : ℝ) (ρ : Euc d → ℝ)
    (hρ : HRS.Whole.IsProbDensity ρ) (Xt : Ω → EucConfig d N) (hX : Measurable Xt) :
    Measurable (fun ζ => (sa11_Xi (m := m) (p := p) σ (Xt ζ) ρ hρ : WNeg d m p)) := by
  have hc : Continuous (fun X : EucConfig d N => (sa11_Xi (m := m) (p := p) σ X ρ hρ : WNeg d m p)) :=
    sa11_Xi_continuous (m := m) (p := p) hd hm σ ρ hρ
  exact hc.measurable.comp hX

omit hd hm in
theorem sa11_isFluct_of_apply {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {N : ℕ} {t : ℝ}
    (Ξ : (R N).Ω → WNeg d m p)
    (h : ∀ φ : sa11_V d, ∀ ζ, (sa11_dual (Ξ ζ)) (sa11_J (m := m) (p := p) φ) =
      S.sigma N * (HRS.Whole.pair (HRS.Whole.empirical ((R N).X (Real.toNNReal t) ζ)) φ.1 -
        HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N t)) φ.1)) :
    IsFluctWRepr S R N m p t Ξ := by
  intro φ hφ F hF
  refine Filter.Eventually.of_forall fun ζ => ?_
  have hFJ : F = sa11_J (m := m) (p := p) ⟨φ, hφ⟩ := sa11_eq_J (φ := ⟨φ, hφ⟩) hF
  show (sa11_dual (Ξ ζ)) F = _
  rw [hFJ]
  exact h ⟨φ, hφ⟩ ζ

end XiRepr

end HRS.MS.ZeroTemp
