import HRS.MP.RdPropIncr
import HRS.MP.HNegInfra

/-!
# Packet MPRPROP, part 2: the kernel bound `KernelBoundRd` (S.A.22 kernel part on `ℝ^d`)

* `rpk_exists_rep`: a bounded linear functional on the smooth `H^Γ` tests is the pairing with a unique
  element of `H^{-Γ}` (Riesz via the isometric embedding `J : φ ↦ (1+4π²|ξ|²)^Γ φ̂` of the tests into `HNeg`,
  Hahn-Banach and Riesz on the Hilbert space `HNeg`);
* `rpk_kernel`: `KernelBoundRd` from the increment bound and the adjoint input.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff ComplexConjugate

namespace HRS.MP.RdProp
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.HNegInfra
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-! ### The tests as a vector space -/

lemma rpk_memSobolev_comb {Γ : ℝ} {u v : Euc d → ℝ} (hu : HRS.PDE.ToolboxRd.MemSobolev Γ u) (hv : HRS.PDE.ToolboxRd.MemSobolev Γ v) (c : ℝ) :
    HRS.PDE.ToolboxRd.MemSobolev Γ (fun x => c * u x + v x) := by
  have hcu : MemLp (fun x => c * u x) 2 volume := hu.1.const_mul c
  have hw : MemLp (fun x => c * u x + v x) 2 volume := hcu.add hv.1
  refine ⟨hw, ?_⟩
  have h1 := fourierL2_add hcu hv.1
  have h2 := fourierL2_smul hu.1 c
  have hmeas : AEStronglyMeasurable (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ Γ *
      ‖fourierL2 (fun x => c * u x + v x) ξ‖ ^ 2) volume := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (mhn_continuous_rho_inv (d := d) (Γ := Γ)).aestronglyMeasurable
    · exact (aestronglyMeasurable_fourierL2 hw).norm.pow 2
  have hI : Integrable (fun ξ : Euc d => 2 * (c ^ 2 * ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ Γ * ‖fourierL2 u ξ‖ ^ 2) +
      (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ Γ * ‖fourierL2 v ξ‖ ^ 2)) volume :=
    ((hu.2.const_mul (c ^ 2)).add hv.2).const_mul 2
  refine hI.mono' hmeas ?_
  filter_upwards [h1, h2] with ξ e1 e2
  have hpos : 0 ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ Γ :=
    Real.rpow_nonneg (by positivity) _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), e1]
  simp only [e2]
  have hn : ‖(c : ℂ) * fourierL2 u ξ + fourierL2 v ξ‖ ^ 2 ≤
      2 * (c ^ 2 * ‖fourierL2 u ξ‖ ^ 2 + ‖fourierL2 v ξ‖ ^ 2) := by
    have h3 := norm_add_le ((c : ℂ) * fourierL2 u ξ) (fourierL2 v ξ)
    have h4 : ‖(c : ℂ) * fourierL2 u ξ‖ = |c| * ‖fourierL2 u ξ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [h4] at h3
    have h5 : 0 ≤ ‖(c : ℂ) * fourierL2 u ξ + fourierL2 v ξ‖ := norm_nonneg _
    nlinarith [sq_abs c, norm_nonneg (fourierL2 u ξ), norm_nonneg (fourierL2 v ξ), abs_nonneg c,
      mul_nonneg (abs_nonneg c) (norm_nonneg (fourierL2 u ξ)),
      sq_nonneg (|c| * ‖fourierL2 u ξ‖ - ‖fourierL2 v ξ‖)]
  calc (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ Γ * ‖(c : ℂ) * fourierL2 u ξ + fourierL2 v ξ‖ ^ 2
      ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ Γ * (2 * (c ^ 2 * ‖fourierL2 u ξ‖ ^ 2 + ‖fourierL2 v ξ‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hn hpos
    _ = _ := by ring

lemma rpk_memSobolev_zero {Γ : ℝ} : HRS.PDE.ToolboxRd.MemSobolev Γ (fun _ : Euc d => (0 : ℝ)) := by
  refine ⟨MemLp.zero, ?_⟩
  have h := fourierL2_sub (d := d) (u := fun _ => (0 : ℝ)) (v := fun _ => (0 : ℝ)) MemLp.zero MemLp.zero
  simp only [sub_self] at h
  refine (integrable_zero _ _ _).congr ?_
  filter_upwards [h] with ξ hξ
  rw [hξ]; simp

/-- The smooth `H^Γ` tests as a real vector space. -/
def rpk_Tst (d : ℕ) (Γ : ℝ) : Submodule ℝ (Euc d → ℝ) where
  carrier := {φ | IsSobolevTest Γ φ}
  add_mem' := by
    intro a b ha hb
    refine ⟨ha.1.add hb.1, ?_⟩
    have := rpk_memSobolev_comb ha.2 hb.2 1
    simp only [one_mul] at this
    exact this
  zero_mem' := ⟨contDiff_const, rpk_memSobolev_zero⟩
  smul_mem' := by
    intro c a ha
    refine ⟨ha.1.const_smul c, ?_⟩
    have := rpk_memSobolev_comb ha.2 (rpk_memSobolev_zero (d := d) (Γ := Γ)) c
    simp only [add_zero] at this
    exact this

lemma rpk_Tst_mem {Γ : ℝ} {φ : Euc d → ℝ} : φ ∈ rpk_Tst d Γ ↔ IsSobolevTest Γ φ := Iff.rfl

/-! ### The embedding of the tests into `HNeg` -/

lemma rpk_psiLp_mem {Γ : ℝ} {φ : Euc d → ℝ} (hφ : HRS.PDE.ToolboxRd.MemSobolev Γ φ) :
    mhn_psiLp hφ ∈ HNegSubmodule d Γ := by
  apply mhn_mem_of_conj
  rw [mhn_ae_mu_iff]
  have h1 := (Measure.measurePreserving_neg (volume : Measure (Euc d))).quasiMeasurePreserving.ae
    (mhn_psiLp_ae hφ)
  filter_upwards [mhn_psiLp_ae hφ, h1, fourierL2_neg hφ.1] with ξ a b c
  rw [b, a]
  simp only [mhn_psi, norm_neg, c, map_mul, Complex.conj_ofReal]

def rpk_J (Γ : ℝ) : rpk_Tst d Γ →ₗ[ℝ] HNeg d Γ where
  toFun φ := (⟨mhn_psiLp φ.2.2, rpk_psiLp_mem φ.2.2⟩ : HNegSubmodule d Γ)
  map_add' a b := by
    apply Subtype.ext
    apply Lp.ext
    show (mhn_psiLp (a + b).2.2 : Euc d → ℂ) =ᵐ[sobolevMeasure d Γ]
      ((mhn_psiLp a.2.2 + mhn_psiLp b.2.2 : Lp ℂ 2 (sobolevMeasure d Γ)) : Euc d → ℂ)
    rw [Filter.EventuallyEq, mhn_ae_mu_iff]
    filter_upwards [mhn_psiLp_ae (a + b).2.2, mhn_psiLp_ae a.2.2, mhn_psiLp_ae b.2.2,
      (mhn_ae_mu_iff _).1 (Lp.coeFn_add (mhn_psiLp a.2.2) (mhn_psiLp b.2.2)),
      fourierL2_add a.2.2.1 b.2.2.1] with ξ h1 h2 h3 h4 h5
    rw [h4, Pi.add_apply, h1, h2, h3]
    simp only [mhn_psi]
    have : fourierL2 ((a + b : rpk_Tst d Γ) : Euc d → ℝ) ξ = fourierL2 (fun x => a.1 x + b.1 x) ξ := rfl
    rw [this, h5]
    ring
  map_smul' c a := by
    apply Subtype.ext
    apply Lp.ext
    show (mhn_psiLp (c • a).2.2 : Euc d → ℂ) =ᵐ[sobolevMeasure d Γ]
      ((c • mhn_psiLp a.2.2 : Lp ℂ 2 (sobolevMeasure d Γ)) : Euc d → ℂ)
    rw [Filter.EventuallyEq, mhn_ae_mu_iff]
    filter_upwards [mhn_psiLp_ae (c • a).2.2, mhn_psiLp_ae a.2.2,
      (mhn_ae_mu_iff _).1 (Lp.coeFn_smul c (mhn_psiLp a.2.2)),
      fourierL2_smul a.2.2.1 c] with ξ h1 h2 h4 h5
    rw [h4, Pi.smul_apply, h1, h2]
    simp only [mhn_psi]
    have : fourierL2 ((c • a : rpk_Tst d Γ) : Euc d → ℝ) ξ = fourierL2 (fun x => c * a.1 x) ξ := rfl
    rw [this, h5]
    simp [Complex.real_smul]
    ring

lemma rpk_J_inner {Γ : ℝ} (φ : rpk_Tst d Γ) (F : HNeg d Γ) :
    inner ℝ (rpk_J Γ φ) F = HNeg.pairing φ.1 F := by
  rw [mhn_pairing_eq φ.2.2 F, mhn_inner_eq]
  rfl

lemma rpk_J_norm {Γ : ℝ} (φ : rpk_Tst d Γ) : ‖rpk_J Γ φ‖ = HRS.Whole.sobolevNorm Γ φ.1 := by
  rw [mhn_norm_eq]
  exact mhn_norm_psiLp φ.2.2

/-! ### Riesz representation on the tests -/

theorem rpk_exists_rep {Γ : ℝ} (L : (Euc d → ℝ) → ℝ) (B : ℝ)
    (hlin : ∀ φ φ' : Euc d → ℝ, ∀ c : ℝ, IsSobolevTest Γ φ → IsSobolevTest Γ φ' →
      L (c • φ + φ') = c * L φ + L φ')
    (hbd : ∀ φ : Euc d → ℝ, IsSobolevTest Γ φ → |L φ| ≤ B * HRS.Whole.sobolevNorm Γ φ) :
    ∃ k : HNeg d Γ, ∀ φ : Euc d → ℝ, IsSobolevTest Γ φ → HNeg.pairing φ k = L φ := by
  have hL0 : L 0 = 0 := by
    have h := hlin 0 0 1 ⟨contDiff_const, rpk_memSobolev_zero⟩ ⟨contDiff_const, rpk_memSobolev_zero⟩
    simp only [smul_zero, add_zero] at h
    linarith
  let Lt : rpk_Tst d Γ →ₗ[ℝ] ℝ :=
    { toFun := fun φ => L φ.1
      map_add' := fun a b => by
        have h := hlin a.1 b.1 1 a.2 b.2
        simpa using h
      map_smul' := fun c a => by
        have h := hlin a.1 0 c a.2 ⟨contDiff_const, rpk_memSobolev_zero⟩
        simp only [add_zero] at h
        simpa [hL0] using h }
  have hker : LinearMap.ker (rpk_J Γ : rpk_Tst d Γ →ₗ[ℝ] HNeg d Γ) ≤ LinearMap.ker Lt := by
    intro φ hφ
    rw [LinearMap.mem_ker] at hφ ⊢
    have h0 : HRS.Whole.sobolevNorm Γ φ.1 = 0 := by rw [← rpk_J_norm, hφ, norm_zero]
    have := hbd φ.1 φ.2
    rw [h0, mul_zero] at this
    exact abs_nonpos_iff.1 this
  let l0 : LinearMap.range (rpk_J Γ : rpk_Tst d Γ →ₗ[ℝ] HNeg d Γ) →ₗ[ℝ] ℝ :=
    (Submodule.liftQ _ Lt hker).comp (LinearMap.quotKerEquivRange (rpk_J Γ : rpk_Tst d Γ →ₗ[ℝ] HNeg d Γ)).symm.toLinearMap
  have hl0 : ∀ (φ : rpk_Tst d Γ) (h : rpk_J Γ φ ∈ LinearMap.range (rpk_J Γ : rpk_Tst d Γ →ₗ[ℝ] HNeg d Γ)),
      l0 ⟨rpk_J Γ φ, h⟩ = L φ.1 := by
    intro φ h
    simp only [l0, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image _ φ h]
    simp [Lt]
  have hl0b : ∀ y, ‖l0 y‖ ≤ max B 0 * ‖y‖ := by
    intro y
    obtain ⟨φ, hφ⟩ := y.2
    have hy : y = ⟨rpk_J Γ φ, ⟨φ, rfl⟩⟩ := Subtype.ext hφ.symm
    rw [hy, hl0 φ ⟨φ, rfl⟩, Real.norm_eq_abs]
    show |L φ.1| ≤ max B 0 * ‖rpk_J Γ φ‖
    rw [rpk_J_norm]
    exact (hbd φ.1 φ.2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  let l1 : LinearMap.range (rpk_J Γ : rpk_Tst d Γ →ₗ[ℝ] HNeg d Γ) →L[ℝ] ℝ :=
    LinearMap.mkContinuous l0 (max B 0) hl0b
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range (rpk_J Γ : rpk_Tst d Γ →ₗ[ℝ] HNeg d Γ)) l1
  refine ⟨(InnerProductSpace.toDual ℝ (HNeg d Γ)).symm g, fun φ hφ => ?_⟩
  set k := (InnerProductSpace.toDual ℝ (HNeg d Γ)).symm g with hk
  have h1 := rpk_J_inner (⟨φ, hφ⟩ : rpk_Tst d Γ) k
  have h2 : inner ℝ k (rpk_J Γ ⟨φ, hφ⟩) = g (rpk_J Γ ⟨φ, hφ⟩) :=
    InnerProductSpace.toDual_symm_apply
  have h3 := hg ⟨rpk_J Γ ⟨φ, hφ⟩, ⟨⟨φ, hφ⟩, rfl⟩⟩
  have h4 : l1 ⟨rpk_J Γ ⟨φ, hφ⟩, ⟨⟨φ, hφ⟩, rfl⟩⟩ = L φ := hl0 ⟨φ, hφ⟩ _
  rw [← h1, real_inner_comm, h2]
  exact h3.trans h4

/-! ### The kernel bound -/

lemma rpk_gradient_partial (F : Euc d → ℝ) (x : Euc d) (j : Fin d) :
    gradient F x j = partialDeriv (fun _ : Fin 1 => j) F x := by
  rw [movtr_gradient_apply]
  unfold partialDeriv
  rw [iteratedFDeriv_one_apply]

lemma rpk_gradient_comb {f g : Euc d → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (c : ℝ)
    (x : Euc d) (j : Fin d) :
    gradient (c • f + g) x j = c * gradient f x j + gradient g x j := by
  rw [movtr_gradient_apply, movtr_gradient_apply, movtr_gradient_apply,
    fderiv_add (hf.const_smul c).differentiableAt hg.differentiableAt, fderiv_const_smul hf.differentiableAt]
  simp

lemma rpk_gradient_sub {f g : Euc d → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (x : Euc d) (j : Fin d) :
    gradient (fun y => f y - g y) x j = gradient f x j - gradient g x j := by
  rw [movtr_gradient_apply, movtr_gradient_apply, movtr_gradient_apply]
  have e : (fun y => f y - g y) = f - g := rfl
  rw [e, fderiv_sub hf.differentiableAt hg.differentiableAt]
  simp

/-- **Kernel bound** (`B:eq:path-kernel-increment` and the uniform kernel bound) on `ℝ^d` for one coefficient,
from the adjoint input `AdjointInputOneD` (which contains the linearity on tests, the uniform bound of the first
derivative, and the existence of classical adjoint solutions) and the increment bound `IncrementBoundRd`.  The
constant is `max (max Kadj C₁) 0`. -/
theorem rpk_kernel (Γ m₀ : ℕ) (Cf : WholeCoeff d) (T Kadj C₁ : ℝ)
    (hadj : AdjointInputOneD (((Γ + 2 : ℕ) : ℝ)) (m₀ + 1) Cf T Kadj)
    (hinc : IncrementBoundRd Cf T (Γ + 2) m₀ C₁) :
    KernelBoundRd Cf T (Γ + 2) (max (max Kadj C₁) 0) := by
  set Cm : ℝ := max (max Kadj C₁) 0 with hCm
  have hCm0 : 0 ≤ Cm := le_max_right _ _
  have hKad : Kadj ≤ Cm := (le_max_left _ _).trans (le_max_left _ _)
  have hC1 : C₁ ≤ Cm := (le_max_right _ _).trans (le_max_left _ _)
  -- consequences of the adjoint input
  have hdiff : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Euc d → ℝ, IsSobolevTest (((Γ + 2 : ℕ) : ℝ)) φ →
      Differentiable ℝ (propagatorW Cf r t φ) := fun r t hr hrt htT φ hφ =>
    ((hadj r t hr hrt htT φ hφ).2.1).differentiable (by exact_mod_cast Nat.succ_ne_zero m₀)
  have hlinP : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ φ' : Euc d → ℝ, ∀ c : ℝ,
      IsSobolevTest (((Γ + 2 : ℕ) : ℝ)) φ → IsSobolevTest (((Γ + 2 : ℕ) : ℝ)) φ' →
      propagatorW Cf r t (c • φ + φ') = c • propagatorW Cf r t φ + propagatorW Cf r t φ' := by
    intro r t hr hrt htT φ φ' c hφ hφ'
    have h := (hadj r t hr hrt htT φ' hφ').2.2.1 φ hφ c
    rw [add_comm (c • φ) φ', h, add_comm]
  have hbdP : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Euc d → ℝ, IsSobolevTest (((Γ + 2 : ℕ) : ℝ)) φ →
      ∀ (j : Fin d) (x : Euc d), |gradient (propagatorW Cf r t φ) x j| ≤
        Kadj * HRS.Whole.sobolevNorm (((Γ + 2 : ℕ) : ℝ)) φ := by
    intro r t hr hrt htT φ hφ j x
    rw [rpk_gradient_partial]
    exact (hadj r t hr hrt htT φ hφ).2.2.2 1 (by omega) (fun _ => j) x
  refine ⟨?_, ?_⟩
  · intro j r t hr hrt htT x
    obtain ⟨k, hk⟩ := rpk_exists_rep (d := d) (Γ := (((Γ + 2 : ℕ) : ℝ)))
      (fun φ => gradient (propagatorW Cf r t φ) x j) (max Kadj 0)
      (fun φ φ' c hφ hφ' => by
        show gradient (propagatorW Cf r t (c • φ + φ')) x j = _
        rw [hlinP r t hr hrt htT φ φ' c hφ hφ']
        rw [rpk_gradient_comb (hdiff r t hr hrt htT φ hφ) (hdiff r t hr hrt htT φ' hφ')])
      (fun φ hφ => (hbdP r t hr hrt htT φ hφ j x).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)))
    refine ⟨k, hk, fun k' hk' => ?_⟩
    have h0 : k' - k = 0 := hneg_eq_zero_of_pairing_zero _ (fun φ hφ => by
      rw [mhn_pairing_sub hφ, hk φ hφ, hk' φ hφ, sub_self])
    exact sub_eq_zero.1 h0
  · intro Kern hKern j r s' t hr hrs hst htT x
    have hrt : r ≤ t := hrs.trans hst
    have hs'T : s' ≤ T := hst.trans htT
    refine ⟨?_, ?_⟩
    · refine hneg_norm_le_of_pairing _ (Cm * |t - s'| * (1 + ‖x‖)) (by positivity) (fun φ hφ => ?_)
      rw [mhn_pairing_sub hφ, hKern j r t hr hrt htT x φ hφ, hKern j r s' hr hrs hs'T x φ hφ,
        ← rpk_gradient_sub (hdiff r t hr hrt htT φ hφ) (hdiff r s' hr hrs hs'T φ hφ), rpk_gradient_partial]
      refine (hinc r s' t hr hrs hst htT φ hφ 1 (by omega) (fun _ => j) x).trans ?_
      have hj := rpi_jb_le x
      have hn : 0 ≤ HRS.Whole.sobolevNorm (((Γ + 2 : ℕ) : ℝ)) φ := Real.sqrt_nonneg _
      have h1 : C₁ * |t - s'| * jbracket x ≤ Cm * |t - s'| * (1 + ‖x‖) := by
        have := abs_nonneg (t - s')
        have h2 : C₁ * |t - s'| ≤ Cm * |t - s'| := mul_le_mul_of_nonneg_right hC1 this
        calc C₁ * |t - s'| * jbracket x ≤ Cm * |t - s'| * jbracket x :=
              mul_le_mul_of_nonneg_right h2 (rpi_jb_pos x).le
          _ ≤ Cm * |t - s'| * (1 + ‖x‖) := mul_le_mul_of_nonneg_left hj (by positivity)
      exact mul_le_mul_of_nonneg_right h1 hn
    · refine hneg_norm_le_of_pairing _ Cm hCm0 (fun φ hφ => ?_)
      rw [hKern j r t hr hrt htT x φ hφ]
      exact (hbdP r t hr hrt htT φ hφ j x).trans (mul_le_mul_of_nonneg_right hKad (Real.sqrt_nonneg _))

end HRS.MP.RdProp
