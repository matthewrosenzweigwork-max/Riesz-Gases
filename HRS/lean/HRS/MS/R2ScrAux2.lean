import HRS.MS.R2ScrAux1
import HRS.MS.MovThermAux1
import HRS.MS.ThCorr
import HRS.MS.PoisKolmAux2

/-!
# S9.8 `r2_screened`, part 2: the vector field `v = γ⁻¹ ∇χ`

Namespace `HRS.MS.S98`; helper lemmas carry the prefix `s98_`.  No existing file is edited.

* `s98_neg_div`: `-div(ρ (c ∇χ)) = c ρ (-Δχ - b·∇χ)` when `∇ρ = ρ b`, `χ ∈ C²`;
* `s98_gL`, `s98_gL_contDiff`, `s98_gL_norm`: `v = c ∇χ` is `C^k` with `‖D^j v‖ ≤ |c| ‖D^{j+1} χ‖` (`j ≤ k`);
* `s98_core`: generic assembly (resolvent hypothesis `hres` as in `tc6_core`; `ρ = thermalDensity` by `mv0_rho_eq`,
  Poisson solve `L χ = r` with `r = γ a_φ` by `tc1_poisson_thermal`, `v = γ⁻¹ ∇χ`);
* `r2_screened_proof : type_of% @HRS.Whole.r2_screened` (`C_b^J` and `H^J` instances of `s98_core`).
No statement was adjusted; the frozen statement is true and non-vacuous as it stands (`responseRepW` is identified
with `γ⁻¹ r` pointwise by continuity, see `R2ScrAux1`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace HRS.MS.S98

open HRS.Whole

variable {d : ℕ}

theorem s98_gradient_coord (χ : Euc d → ℝ) (y : Euc d) (i : Fin d) :
    (gradient χ y) i = fderiv ℝ χ y (EuclideanSpace.single i 1) := by
  have h := HRS.MS.PoisKolm.kl_inner_gradient χ y (EuclideanSpace.single i 1)
  rw [← h, EuclideanSpace.inner_single_left]
  simp

/-- The Riesz map `w ↦ ∇` as a real continuous linear map on covectors. -/
def s98_gL0 (d : ℕ) : (Euc d →L[ℝ] ℝ) →L[ℝ] Euc d :=
  LinearMap.mkContinuous
    { toFun := fun w => (InnerProductSpace.toDual ℝ (Euc d)).symm w
      map_add' := fun w w' => map_add _ w w'
      map_smul' := fun c w => by simp [map_smulₛₗ] } 1 (fun w => by simp)

/-- The linear map `w ↦ c • ∇` (`w` a covector). -/
def s98_gL (d : ℕ) (c : ℝ) : (Euc d →L[ℝ] ℝ) →L[ℝ] Euc d := c • s98_gL0 d

theorem s98_gL_fderiv (c : ℝ) (χ : Euc d → ℝ) (y : Euc d) :
    s98_gL d c (fderiv ℝ χ y) = c • gradient χ y := rfl

theorem s98_gL_norm (c : ℝ) : ‖s98_gL d c‖ ≤ |c| := by
  unfold s98_gL
  have h0 : ‖s98_gL0 d‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  calc ‖c • s98_gL0 d‖ ≤ ‖c‖ * ‖s98_gL0 d‖ := ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖c‖ * 1 := mul_le_mul_of_nonneg_left h0 (norm_nonneg _)
    _ = |c| := by rw [mul_one, Real.norm_eq_abs]

/-- `c ∇χ ∈ C^k` for `χ ∈ C^{k+1}`. -/
theorem s98_gL_contDiff {k : ℕ} {χ : Euc d → ℝ} (hχ : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) χ) (c : ℝ) :
    ContDiff ℝ (k : WithTop ℕ∞) (fun y => c • gradient χ y) := by
  have hfd : ContDiff ℝ (k : WithTop ℕ∞) (fderiv ℝ χ) := hχ.fderiv_right (m := k) (by rw [Nat.cast_succ])
  exact (s98_gL d c).contDiff.comp hfd

/-- `‖D^j (c ∇χ)(x)‖ ≤ |c| ‖D^{j+1} χ(x)‖` for `j ≤ k`. -/
theorem s98_gL_iter {k : ℕ} {χ : Euc d → ℝ} (hχ : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) χ) (c : ℝ)
    {j : ℕ} (hj : j ≤ k) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (fun y => c • gradient χ y) x‖ ≤ |c| * ‖iteratedFDeriv ℝ (j + 1) χ x‖ := by
  have hfd : ContDiff ℝ (k : WithTop ℕ∞) (fderiv ℝ χ) := hχ.fderiv_right (m := k) (by rw [Nat.cast_succ])
  have := (s98_gL d c).norm_iteratedFDeriv_comp_left (f := fderiv ℝ χ) (x := x) (N := (k : WithTop ℕ∞))
    (n := j) hfd.contDiffAt (by exact_mod_cast hj)
  rw [norm_iteratedFDeriv_fderiv] at this
  calc ‖iteratedFDeriv ℝ j (fun y => c • gradient χ y) x‖
      = ‖iteratedFDeriv ℝ j (s98_gL d c ∘ fderiv ℝ χ) x‖ := rfl
    _ ≤ ‖s98_gL d c‖ * ‖iteratedFDeriv ℝ (j + 1) χ x‖ := this
    _ ≤ |c| * ‖iteratedFDeriv ℝ (j + 1) χ x‖ := mul_le_mul_of_nonneg_right (s98_gL_norm c) (norm_nonneg _)

/-- `div ∇χ = Δχ` for `χ ∈ C²`. -/
theorem s98_movDiv_gradient {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ) (x : Euc d) :
    movDiv (fun y => gradient χ y) x = Laplacian.laplacian χ x := by
  have hg : ContDiff ℝ 1 (fun y => gradient χ y) := by
    have := s98_gL_contDiff (k := 1) (χ := χ) (by simpa using hχ) 1
    simpa using this
  have hgd : DifferentiableAt ℝ (fun y => gradient χ y) x := (hg.differentiable (by norm_num)) x
  rw [HRS.MS.MovForce.mv1_laplacian_eq hχ]
  unfold movDiv
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : HasFDerivAt (fun y => (gradient χ y) i) ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp
      (fderiv ℝ (fun y => gradient χ y) x)) x :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp x hgd.hasFDerivAt
  have e : (fun y => (gradient χ y) i) = fun y => fderiv ℝ χ y (EuclideanSpace.single i 1) :=
    funext fun y => s98_gradient_coord χ y i
  rw [e] at h1
  rw [h1.fderiv]
  simp

/-- `-div(ρ (c ∇χ)) = c ρ (-Δχ - b·∇χ)` when `∇ρ = ρ b`. -/
theorem s98_neg_div {ρ : Euc d → ℝ} {b : Euc d → Euc d} {χ : Euc d → ℝ} (hρ : Differentiable ℝ ρ)
    (hgrad : ∀ x, gradient ρ x = ρ x • b x) (hχ : ContDiff ℝ 2 χ) (c : ℝ) (x : Euc d) :
    -movDiv (fun y => ρ y • (c • gradient χ y)) x = c * ρ x * poissonOp b χ x := by
  have hg : ContDiff ℝ 1 (fun y => gradient χ y) := by
    have := s98_gL_contDiff (k := 1) (χ := χ) (by simpa using hχ) 1
    simpa using this
  have hgd : DifferentiableAt ℝ (fun y => gradient χ y) x := (hg.differentiable (by norm_num)) x
  have hF : DifferentiableAt ℝ (fun y => c • gradient χ y) x := hgd.const_smul c
  rw [HRS.MS.MovForce.mv1_movDiv_smul (hρ x) hF]
  have h1 : movDiv (fun y => c • gradient χ y) x = c * movDiv (fun y => gradient χ y) x := by
    unfold movDiv
    have e : fderiv ℝ (fun y => c • gradient χ y) x = c • fderiv ℝ (fun y => gradient χ y) x :=
      fderiv_const_smul hgd c
    rw [e]
    simp [Finset.mul_sum]
  rw [h1, s98_movDiv_gradient hχ]
  have h2 : ∑ i, fderiv ℝ ρ x (EuclideanSpace.single i 1) * (c • gradient χ x) i =
      c * ρ x * inner ℝ (b x) (gradient χ x) := by
    have e : ∀ i : Fin d, fderiv ℝ ρ x (EuclideanSpace.single i 1) * (c • gradient χ x) i =
        c * ρ x * (inner ℝ (EuclideanSpace.single i (1 : ℝ)) (b x) *
          inner ℝ (EuclideanSpace.single i (1 : ℝ)) (gradient χ x)) := by
      intro i
      rw [← HRS.MS.PoisKolm.kl_inner_gradient ρ x (EuclideanSpace.single i 1), hgrad x]
      have e2 : (gradient χ x) i = inner ℝ (EuclideanSpace.single i (1 : ℝ)) (gradient χ x) := by
        rw [EuclideanSpace.inner_single_left]
        simp
      simp only [PiLp.smul_apply, smul_eq_mul, inner_smul_right, e2]
      ring
    rw [Finset.sum_congr rfl fun i _ => e i, ← Finset.mul_sum, HRS.MS.Gap.gap1_sum_inner]
  rw [h2]
  unfold poissonOp
  ring

/-- The `C_b^k` energy of `c ∇χ` in `ℝ≥0∞`. -/
theorem s98_vec_bound {k : ℕ} {χ : Euc d → ℝ} (hχ : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) χ) {c : ℝ}
    (hc : 0 ≤ c) {T : ℝ} (hT : ∀ (x : Euc d), ∀ j ≤ k, ‖iteratedFDeriv ℝ (j + 1) χ x‖ ≤ T) :
    cbNormVecE k (fun y => c • gradient χ y) ≤ ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * (c * T)) := by
  have hT0 : 0 ≤ c * T := by
    have := (norm_nonneg (iteratedFDeriv ℝ 1 χ 0)).trans (hT 0 0 (Nat.zero_le _))
    positivity
  unfold cbNormVecE
  calc ∑ j ∈ Finset.range (k + 1), ⨆ x : Euc d,
        ENNReal.ofReal ‖iteratedFDeriv ℝ j (fun y => c • gradient χ y) x‖
      ≤ ∑ _j ∈ Finset.range (k + 1), ENNReal.ofReal (c * T) := by
        refine Finset.sum_le_sum fun j hj => iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
        have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        refine (s98_gL_iter hχ c hjk x).trans ?_
        rw [abs_of_nonneg hc]
        exact mul_le_mul_of_nonneg_left (hT x j hjk) hc
    _ = ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * (c * T)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

/-- **Generic assembly of S9.8** (data class `P φ`, norm `nf φ`; the hypothesis `hres` is the one of `tc6_core`). -/
theorem s98_core (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ) (hk : 1 ≤ k)
    (a β γ : ℝ) (ha : 0 < a) (hβ : 0 < β) (hγ : 0 < γ) (P : (Euc d → ℝ) → Prop)
    (nf : (Euc d → ℝ) → ℝ) (hnf : ∀ φ, P φ → 0 ≤ nf φ) (hPc : ∀ φ, P φ → Continuous φ)
    (hres : ∃ N0 : ℕ, ∀ M₀ c S : ℝ, 0 < c → ∃ C5 : ℝ, 0 ≤ C5 ∧
      ∀ ρ : Euc d → ℝ, HRS.MS.TcDefs.TcRef d ρ M₀ c S N0 → ∀ γ' : ℝ, 0 < γ' → γ' ≤ γ →
        ∀ φ : Euc d → ℝ, P φ →
          ∃ r₀ r : Euc d → ℝ, MemL2Zero (HRS.Whole.withDensityReal ρ) r₀ ∧
            (∀ᵐ x ∂(HRS.Whole.withDensityReal ρ),
              r₀ x + γ' * HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) r₀ x =
                γ' * HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) φ x) ∧
            HRS.MemCb (k + 1) r ∧ HRS.cbNorm (k + 1) r ≤ C5 * nf φ ∧
            r =ᵐ[HRS.Whole.withDensityReal ρ] r₀) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ → ∀ φ : Euc d → ℝ, P φ →
      ∃ v : Euc d → Euc d,
        HRS.Whole.IsResponse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ φ
            (responseRepW (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ φ) ∧
          HRS.MemCb k (responseRepW (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ φ) ∧ ContDiff ℝ k v ∧
          Differentiable ℝ (fun y => ρ y • v y) ∧
          (∀ x, -movDiv (fun y => ρ y • v y) x =
            ρ x * responseRepW (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ φ x) ∧
          ENNReal.ofReal (HRS.cbNorm k (responseRepW (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ φ)) +
              cbNormVecE k v ≤ ENNReal.ofReal (C * nf φ) := by
  obtain ⟨N0, hN0⟩ := hres
  obtain ⟨c, M₀, m₂, hc, hM₀, hS, hMb⟩ := HRS.MS.Tc6.tc6_unif hd hs0 hsd (am := a) (ap := a)
    (βm := β) (βp := β) ha hβ le_rfl le_rfl
  obtain ⟨S, hS0, hSρ⟩ := hS N0
  obtain ⟨Mb, hMb0, hMbρ⟩ := hMb (k + 1)
  obtain ⟨C5, hC5, hC5ρ⟩ := hN0 M₀ c S hc
  have hqm : 0 < a * β := mul_pos ha hβ
  obtain ⟨C1, Cm, hP⟩ := HRS.MS.Tc1.tc1_poisson_thermal hd (a * β) (a * β) Mb m₂ hqm (k + 1)
    (by omega)
  refine ⟨γ⁻¹ * (1 + ((k + 1 : ℕ) : ℝ) * |Cm|) * C5, fun ρ hρeq φ hφ => ?_⟩
  have hρ := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρeq
  subst hρ
  have hTc := hSρ a β le_rfl le_rfl le_rfl le_rfl
  have hdr := hMbρ a β le_rfl le_rfl le_rfl le_rfl
  obtain ⟨r₀, r, hr₀, hae, hr, hbd, hrr⟩ := hC5ρ _ hTc γ hγ le_rfl φ hφ
  have hprob : IsProbabilityMeasure (HRS.Whole.withDensityReal (thermalDensity d s a β)) :=
    HRS.MS.TcF.tc4_isProb hTc.prob
  have hri : Integrable r (HRS.Whole.withDensityReal (thermalDensity d s a β)) :=
    (HRS.MS.Tc5.tc5_memLp_of_cb hr).integrable one_le_two
  have hr0 : ∫ x, r x ∂(HRS.Whole.withDensityReal (thermalDensity d s a β)) = 0 :=
    (integral_congr_ae hrr).trans hr₀.2
  obtain ⟨χ, hχc, -, -, hgen, -, -, hder⟩ :=
    hP s a β hs0 hsd ha hβ le_rfl le_rfl hdr r hr hri hr0
  obtain ⟨B, hBeq, hGap, -⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd ha hβ hρeq
  set ρ := thermalDensity d s a β with hρdef
  have hρd : Differentiable ℝ ρ := hGap.smooth.differentiable (by simp)
  have hgrad : ∀ x, gradient ρ x = ρ x • (-(β * a) • x + B x) := hGap.grad
  have hpois : ∀ x, poissonOp (fun x => -(β * a) • x + B x) χ x = r x := by
    intro x
    have h1 := HRS.MS.Tc1.tc1_gen_eq_thermal hd hs0 hsd ha hβ χ x
    have e : (fun x => -(a * β) • x + (-β) • gradient
        (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x) =
        fun x => -(β * a) • x + B x := by
      funext y
      rw [hBeq, mul_comm a β]
    rw [e] at h1
    rw [← h1]
    exact hgen x
  -- the continuous representative
  have hrc : Continuous r := hr.1.continuous
  have hX0 : 0 ≤ HRS.cbNorm (k + 1) r := HRS.MS.Tc5.tc5_cb_nonneg _ r
  obtain ⟨hrep, hrespW⟩ := HRS.MS.S98.s98_resp_rep (d := d) (by omega) hs0 hsd hc hTc hγ (hPc φ hφ) hrc
    (B := HRS.cbNorm (k + 1) r) (fun x => by
      have := HRS.MS.Tc5.tc5_cb_sup_le hr x
      rwa [Real.norm_eq_abs] at this) hr₀ hae hrr
  have hrepf : responseRepW (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ φ = fun x => γ⁻¹ * r x := funext hrep
  have hχ2 : ContDiff ℝ 2 χ := hχc.of_le (by exact_mod_cast (by omega : 2 ≤ k + 1))
  refine ⟨fun y => γ⁻¹ • gradient χ y, hrespW, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrepf]
    exact (HRS.MS.Tc5.tc5_cb_smul γ⁻¹ (HRS.MS.Tc5.tc5_cb_mono (Nat.le_succ k) hr).1).1
  · exact s98_gL_contDiff hχc γ⁻¹
  · exact hρd.smul ((s98_gL_contDiff hχc γ⁻¹).differentiable (by exact_mod_cast (by omega : k ≠ 0)))
  · intro x
    rw [s98_neg_div hρd hgrad hχ2 γ⁻¹ x, hpois x, hrep x]
    ring
  · -- the bound
    have hT : ∀ (x : Euc d), ∀ j ≤ k, ‖iteratedFDeriv ℝ (j + 1) χ x‖ ≤ |Cm| * HRS.cbNorm (k + 1) r := by
      intro x j hj
      have h1 : ‖iteratedFDeriv ℝ (j + 1) χ x‖ ≤ ∑ i : Fin (k + 1), ‖iteratedFDeriv ℝ ((i : ℕ) + 1) χ x‖ :=
        Finset.single_le_sum (f := fun i : Fin (k + 1) => ‖iteratedFDeriv ℝ ((i : ℕ) + 1) χ x‖)
          (fun i _ => norm_nonneg _) (Finset.mem_univ (⟨j, by omega⟩ : Fin (k + 1)))
      exact h1.trans ((hder fun _ => x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hX0))
    have hv := s98_vec_bound hχc (inv_nonneg.2 hγ.le) hT
    rw [hrepf]
    have hcb : HRS.cbNorm k (fun x => γ⁻¹ * r x) ≤ γ⁻¹ * HRS.cbNorm (k + 1) r := by
      have := (HRS.MS.Tc5.tc5_cb_smul γ⁻¹ (HRS.MS.Tc5.tc5_cb_mono (Nat.le_succ k) hr).1).2
      rw [abs_of_nonneg (inv_nonneg.2 hγ.le)] at this
      exact this.trans (mul_le_mul_of_nonneg_left (HRS.MS.Tc5.tc5_cb_mono (Nat.le_succ k) hr).2
        (inv_nonneg.2 hγ.le))
    have hnf := hnf φ hφ
    have hXn : HRS.cbNorm (k + 1) r ≤ C5 * nf φ := hbd
    have hsum : γ⁻¹ * HRS.cbNorm (k + 1) r + ((k + 1 : ℕ) : ℝ) * (γ⁻¹ * (|Cm| * HRS.cbNorm (k + 1) r)) ≤
        γ⁻¹ * (1 + ((k + 1 : ℕ) : ℝ) * |Cm|) * C5 * nf φ := by
      have e : γ⁻¹ * HRS.cbNorm (k + 1) r + ((k + 1 : ℕ) : ℝ) * (γ⁻¹ * (|Cm| * HRS.cbNorm (k + 1) r)) =
          γ⁻¹ * (1 + ((k + 1 : ℕ) : ℝ) * |Cm|) * HRS.cbNorm (k + 1) r := by ring
      rw [e]
      calc γ⁻¹ * (1 + ((k + 1 : ℕ) : ℝ) * |Cm|) * HRS.cbNorm (k + 1) r
          ≤ γ⁻¹ * (1 + ((k + 1 : ℕ) : ℝ) * |Cm|) * (C5 * nf φ) :=
            mul_le_mul_of_nonneg_left hXn (by positivity)
        _ = γ⁻¹ * (1 + ((k + 1 : ℕ) : ℝ) * |Cm|) * C5 * nf φ := by ring
    calc ENNReal.ofReal (HRS.cbNorm k fun x => γ⁻¹ * r x) + cbNormVecE k (fun y => γ⁻¹ • gradient χ y)
        ≤ ENNReal.ofReal (γ⁻¹ * HRS.cbNorm (k + 1) r) +
            ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * (γ⁻¹ * (|Cm| * HRS.cbNorm (k + 1) r))) :=
          add_le_add (ENNReal.ofReal_le_ofReal hcb) hv
      _ = ENNReal.ofReal (γ⁻¹ * HRS.cbNorm (k + 1) r +
            ((k + 1 : ℕ) : ℝ) * (γ⁻¹ * (|Cm| * HRS.cbNorm (k + 1) r))) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hsum

/-- **S9.8** `r2_screened`: the proof; it has exactly the type of the frozen statement `HRS.Whole.r2_screened`
(tie in `R2ScrTie.lean`). -/
theorem r2_screened_proof : type_of% @HRS.Whole.r2_screened := by
  intro d s hd hs0 hs a β γ ha hβ hγ k J hk hJ
  have hd2 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : s < d := by linarith
  have hα : 0 < (d : ℝ) - s := by linarith
  set m : ℕ := k + 1 with hm
  have hmJ : m ≤ J := by
    have : ((m : ℕ) : ℝ) ≤ J := by
      rw [hm]; push_cast; linarith
    exact_mod_cast this
  set M : ℕ := ⌈((m : ℝ) + d / 2) / ((d : ℝ) - s)⌉₊ + 1 with hM
  have hMs : (m : ℝ) + d / 2 < M * ((d : ℝ) - s) := HRS.MS.Tc5.tc5_M_spec hsd m
  -- the `C_b^J` data class
  have hcb : ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ → ∀ φ : Euc d → ℝ, HRS.MemCb J φ →
      ∃ v : Euc d → Euc d,
        HRS.Whole.IsResponse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ φ
            (responseRepW (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ φ) ∧
          HRS.MemCb k (responseRepW (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ φ) ∧ ContDiff ℝ k v ∧
          Differentiable ℝ (fun y => ρ y • v y) ∧
          (∀ x, -movDiv (fun y => ρ y • v y) x =
            ρ x * responseRepW (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ φ x) ∧
          ENNReal.ofReal (HRS.cbNorm k (responseRepW (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ φ)) +
              cbNormVecE k v ≤ ENNReal.ofReal (C * HRS.cbNorm J φ) := by
    set N0 : ℕ := m + ⌈(M : ℝ) * ((d : ℝ) - s) + d⌉₊ + 1 with hN0
    have hmN : m ≤ N0 := by omega
    have hN : (M : ℝ) * ((d : ℝ) - s) + d < N0 := by
      have h1 := Nat.le_ceil ((M : ℝ) * ((d : ℝ) - s) + d)
      have : ((⌈(M : ℝ) * ((d : ℝ) - s) + d⌉₊ : ℕ) : ℝ) + 1 ≤ N0 := by
        rw [hN0]; push_cast; have : (0 : ℝ) ≤ m := by positivity
        linarith
      linarith
    exact s98_core hd hs0 hsd k hk a β γ ha hβ hγ (HRS.MemCb J) (HRS.cbNorm J)
      (fun φ _ => HRS.MS.Tc5.tc5_cb_nonneg J φ) (fun φ hφ => hφ.1.continuous)
      ⟨N0, fun M₀ c S hc => HRS.MS.Tc5.tc5_resolvent_rep (d := d) hs0 hsd m J M hmJ hMs γ M₀ c S hc N0 hmN hN
        |>.imp fun C hC => hC⟩
  -- the `H^J` data class
  have hsob : ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ → ∀ φ : Euc d → ℝ, MemHSmooth J φ →
      ∃ v : Euc d → Euc d,
        HRS.Whole.IsResponse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ φ
            (responseRepW (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ φ) ∧
          HRS.MemCb k (responseRepW (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ φ) ∧ ContDiff ℝ k v ∧
          Differentiable ℝ (fun y => ρ y • v y) ∧
          (∀ x, -movDiv (fun y => ρ y • v y) x =
            ρ x * responseRepW (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ φ x) ∧
          ENNReal.ofReal (HRS.cbNorm k (responseRepW (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ φ)) +
              cbNormVecE k v ≤ ENNReal.ofReal (C * sobolevWNorm J 2 φ) := by
    have hJm : (m : ℝ) + d / 2 < J := by rw [hm]; push_cast; exact hJ
    set N0 : ℕ := J + ⌈(M : ℝ) * ((d : ℝ) - s) + d⌉₊ + 1 with hN0
    have hN : (J : ℝ) + M * ((d : ℝ) - s) + d < N0 := by
      have h1 := Nat.le_ceil ((M : ℝ) * ((d : ℝ) - s) + d)
      have : ((⌈(M : ℝ) * ((d : ℝ) - s) + d⌉₊ : ℕ) : ℝ) + 1 + J ≤ N0 := by
        rw [hN0]; push_cast; linarith
      linarith
    obtain ⟨Cs, hCs0, hCs⟩ := HRS.MS.TcS.tcs_sobolevNorm_le_hsmooth d J
    obtain ⟨C1, hC10, hC1⟩ := HRS.MS.TcS.tcs_sobolev_of_hsmooth d J
    have hW : ∀ φ : Euc d → ℝ, 0 ≤ sobolevWNorm J 2 φ := fun φ => by
      unfold sobolevWNorm
      exact Finset.sum_nonneg fun n _ => Real.rpow_nonneg (integral_nonneg fun x => by positivity) _
    refine s98_core hd hs0 hsd k hk a β γ ha hβ hγ (MemHSmooth J) (sobolevWNorm J 2) (fun φ _ => hW φ)
      (fun φ hφ => hφ.1.continuous) ⟨N0, fun M₀ c S hc => ?_⟩
    obtain ⟨C, hC0, hCρ⟩ := HRS.MS.Tc5.tc5_resolvent_rep_sob (d := d) hs0 hsd m J M hJm hMs γ M₀ c S hc N0 hN
    refine ⟨C * Cs, mul_nonneg hC0 hCs0, fun ρ hρ γ' hγ' hγp φ hφ => ?_⟩
    obtain ⟨r₀, r, h1, h2, h3, h4, h5⟩ := hCρ ρ hρ γ' hγ' hγp φ (hC1 φ hφ).1
    refine ⟨r₀, r, h1, h2, h3, ?_, h5⟩
    have hs' : Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (J : ℝ) φ) ≤ Cs * sobolevWNorm J 2 φ :=
      hCs φ hφ
    calc HRS.cbNorm m r ≤ C * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (J : ℝ) φ) := h4
      _ ≤ C * (Cs * sobolevWNorm J 2 φ) := mul_le_mul_of_nonneg_left hs' hC0
      _ = C * Cs * sobolevWNorm J 2 φ := by ring
  obtain ⟨C1, hC1⟩ := hcb
  obtain ⟨C2, hC2⟩ := hsob
  have hW : ∀ φ : Euc d → ℝ, 0 ≤ sobolevWNorm J 2 φ := fun φ => by
    unfold sobolevWNorm
    exact Finset.sum_nonneg fun n _ => Real.rpow_nonneg (integral_nonneg fun x => by positivity) _
  refine ⟨max C1 C2, fun ρ hρ => ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩⟩
  · obtain ⟨v, a1, a2, a3, a4, a5, a6⟩ := hC1 ρ hρ φ hφ
    exact ⟨v, a1, a2, a3, a4, a5, a6.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (HRS.MS.Tc5.tc5_cb_nonneg J φ)))⟩
  · obtain ⟨v, a1, a2, a3, a4, a5, a6⟩ := hC2 ρ hρ φ hφ
    exact ⟨v, a1, a2, a3, a4, a5, a6.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (hW φ)))⟩

end HRS.MS.S98

end
