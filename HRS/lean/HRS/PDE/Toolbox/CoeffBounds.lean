import HRS.PDE.ForwardEq
import HRS.PDE.KernelInputsD1
import HRS.Analysis.Category

/-!
# Appendix C helper lemmas: coefficient bounds (Lemma C.1)

Auxiliary results for `HRS/PDE/Toolbox.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-! ### Generic `C^k` norm calculus for vector-valued periodic functions -/

section Generic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Vector-valued analogue of `Torus.bddAbove_norm_iteratedFDeriv_lift`. -/
theorem bddAbove_iteratedFDeriv_lift (j : ℕ) (φ : Torus d → E) (h : ContDiff ℝ j (Torus.lift φ)) :
    BddAbove (Set.range fun x : Euc d => ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖) := by
  have hc : Continuous fun x : Euc d => ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖ :=
    (h.continuous_iteratedFDeriv le_rfl).norm
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Euc d) d).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨‖M‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  set m : Lattice d := fun i => ⌊x i⌋ with hm
  set y : Euc d := x + Lattice.toEuc (-m) with hy
  have hg : ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖ = ‖iteratedFDeriv ℝ j (Torus.lift φ) y‖ := by
    rw [hy, Torus.iteratedFDeriv_lift_periodic]
  have hyc : ∀ i, 0 ≤ y i ∧ y i < 1 := by
    intro i
    have := Int.floor_le (x i)
    have h2 := Int.lt_floor_add_one (x i)
    simp only [hy, hm, Lattice.toEuc, PiLp.add_apply, Pi.neg_apply, Int.cast_neg]
    constructor <;> linarith
  have hyb : y ∈ Metric.closedBall (0 : Euc d) d := by
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_iff.mpr
    refine ⟨Nat.cast_nonneg d, ?_⟩
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          rw [Real.norm_eq_abs, sq_abs]
          have := hyc i
          nlinarith
      _ = d := by simp
      _ ≤ (d : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos d with h0 | h0
          · simp [h0]
          · have : (1 : ℝ) ≤ d := by exact_mod_cast h0
            nlinarith
  show ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖ ≤ ‖M‖
  rw [hg]
  have := hM y hyb
  rw [norm_norm] at this
  exact this.trans (Real.le_norm_self M)

theorem cbNorm_nonneg'C (k : ℕ) (φ : Torus d → E) : 0 ≤ Torus.cbNorm k φ :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem cbNorm_mono' {k l : ℕ} (hkl : k ≤ l) (φ : Torus d → E) :
    Torus.cbNorm k φ ≤ Torus.cbNorm l φ := by
  unfold Torus.cbNorm
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun _ _ _ => Real.iSup_nonneg fun _ => norm_nonneg _)

/-- `‖T ∘ ψ‖_{C^k} ≤ ‖T‖ ‖ψ‖_{C^k}` for a continuous linear map `T`. -/
theorem cbNorm_clm_comp_le (T : E →L[ℝ] F) (k : ℕ) (ψ : Torus d → E) (hψ : Torus.IsCk k ψ) :
    Torus.cbNorm k (fun x => T (ψ x)) ≤ ‖T‖ * Torus.cbNorm k ψ := by
  unfold Torus.cbNorm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hψ' : ContDiff ℝ j (Torus.lift ψ) := hψ.of_le (by exact_mod_cast hjk)
  have hb := bddAbove_iteratedFDeriv_lift j ψ hψ'
  refine ciSup_le fun x => ?_
  have e : Torus.lift (fun x => T (ψ x)) = T ∘ Torus.lift ψ := rfl
  rw [e]
  calc _ ≤ ‖T‖ * ‖iteratedFDeriv ℝ j (Torus.lift ψ) x‖ :=
        T.norm_iteratedFDeriv_comp_left hψ'.contDiffAt le_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_ciSup hb x) (norm_nonneg _)

/-- Triangle inequality for `cbNorm` on vector-valued functions. -/
theorem cbNorm_sub_le' (k : ℕ) (φ ψ : Torus d → E) (hφ : Torus.IsCk k φ) (hψ : Torus.IsCk k ψ) :
    Torus.cbNorm k (φ - ψ) ≤ Torus.cbNorm k φ + Torus.cbNorm k ψ := by
  unfold Torus.cbNorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hφ' : ContDiff ℝ j (Torus.lift φ) := hφ.of_le (by exact_mod_cast hjk)
  have hψ' : ContDiff ℝ j (Torus.lift ψ) := hψ.of_le (by exact_mod_cast hjk)
  have b1 := bddAbove_iteratedFDeriv_lift j φ hφ'
  have b2 := bddAbove_iteratedFDeriv_lift j ψ hψ'
  refine ciSup_le fun x => ?_
  have : Torus.lift (φ - ψ) = Torus.lift φ - Torus.lift ψ := rfl
  rw [this, iteratedFDeriv_sub_apply hφ'.contDiffAt hψ'.contDiffAt]
  exact (norm_sub_le _ _).trans (add_le_add (le_ciSup b1 x) (le_ciSup b2 x))

end Generic

/-! ### The gradient on the torus -/

/-- The inverse Riesz map `(ℝ^d)* → ℝ^d` as a continuous `ℝ`-linear map of norm `≤ 1`. -/
def dualToVec (d : ℕ) : (Euc d →L[ℝ] ℝ) →L[ℝ] Euc d :=
  LinearMap.mkContinuous
    { toFun := fun l => (InnerProductSpace.toDual ℝ (Euc d)).symm l
      map_add' := fun a b => map_add _ a b
      map_smul' := fun c l => by simp }
    1 (fun l => by simp)

theorem norm_dualToVec_le : ‖dualToVec d‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem lift_grad (φ : Torus d → ℝ) :
    Torus.lift (Torus.grad φ) = fun y => dualToVec d (fderiv ℝ (Torus.lift φ) y) := by
  funext y
  obtain ⟨n, hn⟩ := Torus.rep_mk y
  show gradient (Torus.lift φ) (Torus.rep (Torus.mk y)) = _
  rw [hn]
  have h1 : (fun z => Torus.lift φ (z + Lattice.toEuc n)) = Torus.lift φ :=
    funext fun z => Torus.lift_periodic φ z n
  have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := Torus.lift φ) (Lattice.toEuc n) (x := y)
  rw [h1] at h2
  show (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ (Torus.lift φ) (y + Lattice.toEuc n)) = _
  rw [← h2]
  rfl

theorem isCk_grad (n : ℕ) (φ : Torus d → ℝ) (hφ : Torus.IsCk ((n + 1 : ℕ) : WithTop ℕ∞) φ) :
    Torus.IsCk (n : WithTop ℕ∞) (Torus.grad φ) := by
  unfold Torus.IsCk at *
  rw [lift_grad]
  exact (dualToVec d).contDiff.comp (hφ.fderiv_right (by exact_mod_cast le_rfl))

theorem cbNorm_grad_le (k : ℕ) (φ : Torus d → ℝ) (hφ : Torus.IsCk ((k + 1 : ℕ) : WithTop ℕ∞) φ) :
    Torus.cbNorm k (Torus.grad φ) ≤ Torus.cbNorm (k + 1) φ := by
  have hφ' : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (Torus.lift φ) := hφ
  unfold Torus.cbNorm
  rw [Finset.sum_range_succ' _ (k + 1)]
  have hnn : 0 ≤ ⨆ x : Euc d, ‖iteratedFDeriv ℝ 0 (Torus.lift φ) x‖ :=
    Real.iSup_nonneg fun _ => norm_nonneg _
  refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun j hj => ?_) hnn
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hb := bddAbove_iteratedFDeriv_lift (j + 1) φ (hφ'.of_le (by exact_mod_cast Nat.succ_le_succ hjk))
  refine ciSup_le fun x => ?_
  rw [lift_grad]
  have hfd : ContDiff ℝ (j : WithTop ℕ∞) (fderiv ℝ (Torus.lift φ)) :=
    hφ'.fderiv_right (by exact_mod_cast Nat.succ_le_succ hjk)
  have e : (fun y => dualToVec d (fderiv ℝ (Torus.lift φ) y)) =
      (dualToVec d) ∘ (fderiv ℝ (Torus.lift φ)) := rfl
  rw [e]
  calc _ ≤ ‖dualToVec d‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ (Torus.lift φ)) x‖ :=
        (dualToVec d).norm_iteratedFDeriv_comp_left hfd.contDiffAt le_rfl
    _ ≤ 1 * ‖iteratedFDeriv ℝ (j + 1) (Torus.lift φ) x‖ := by
        rw [norm_iteratedFDeriv_fderiv]
        exact mul_le_mul_of_nonneg_right norm_dualToVec_le (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact le_ciSup hb x

/-! ### Matrices acting on `ℝ^d` -/

/-- `Torus.matVec M` as a continuous linear map. -/
def matCLM (M : Matrix (Fin d) (Fin d) ℝ) : Euc d →L[ℝ] Euc d :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)

theorem matCLM_apply (M : Matrix (Fin d) (Fin d) ℝ) (v : Euc d) : matCLM M v = Torus.matVec M v := rfl

theorem norm_matCLM_le (MB : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (hM : MatBound MB M) :
    ‖matCLM M‖ ≤ (d : ℝ) ^ 2 * |MB| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  set B : ℝ := d * |MB| * ‖v‖ with hB
  have hB0 : 0 ≤ B := by positivity
  have hcomp : ∀ i, ‖(matCLM M v) i‖ ≤ B := by
    intro i
    have : (matCLM M v) i = ∑ j, M i j * v j := by
      simp [matCLM_apply, Torus.matVec, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
    rw [this, Real.norm_eq_abs]
    calc |∑ j, M i j * v j| ≤ ∑ j, |M i j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin d, |MB| * ‖v‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul ((hM i j).trans (le_abs_self _)) (by simpa using PiLp.norm_apply_le v j)
            (abs_nonneg _) (abs_nonneg _)
      _ = B := by simp [hB]; ring
  have hnorm : ‖matCLM M v‖ ≤ d * B := by
    rw [EuclideanSpace.norm_eq]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc ∑ i, ‖(matCLM M v) i‖ ^ 2 ≤ ∑ _i : Fin d, B ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hcomp i) 2
      _ = d * B ^ 2 := by simp
      _ ≤ (d * B) ^ 2 := by
          rcases Nat.eq_zero_or_pos d with h0 | h0
          · simp [h0]
          · have : (1 : ℝ) ≤ d := by exact_mod_cast h0
            nlinarith [sq_nonneg B]
  calc ‖matCLM M v‖ ≤ d * B := hnorm
    _ = (d : ℝ) ^ 2 * |MB| * ‖v‖ := by rw [hB]; ring

/-! ### Lemma C.1 -/

theorem coefficient_bounds_aux (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ VB : ℝ) :
    ∃ C : ℝ, ∀ (M : Matrix (Fin d) (Fin d) ℝ) (_ : MatBound MB M) (V : Torus d → ℝ)
      (_ : VHyp m VB V) (μ : Torus d → ℝ) (_ : IsProbDensity μ) (_ : Torus.IsCk (m + 3) μ)
      (_ : Torus.cbNorm (m + 3) μ ≤ Λ),
      Torus.IsCk (m + 1) (fun x => Torus.matVec M (convGradConv (periodicRieszGrad d s) μ x) - Torus.grad V x) ∧
      Torus.cbNorm (m + 1) (fun x => Torus.matVec M (convGradConv (periodicRieszGrad d s) μ x) - Torus.grad V x) +
        (⨆ q : {q : Euc d // ‖q‖ = 1}, Torus.cbNorm (m + 1) (fun x => inner ℝ q.1 (Torus.grad μ x))) +
        Torus.cbNorm (m + 3) μ ≤ C := by
  obtain ⟨C1, hC1⟩ := convGradConv_cbNorm_of_one_le hd hs0 hsd (m + 1)
  refine ⟨(d : ℝ) ^ 2 * |MB| * max C1 0 * |Λ| + |VB| + |Λ| + |Λ|, ?_⟩
  intro M hM V hV μ _ hCk hΛ
  obtain ⟨hVk, hVB⟩ := hV
  -- regularity bookkeeping
  have hμ2 : Torus.IsCk (((m + 1 : ℕ) : WithTop ℕ∞) + 1) μ := by
    unfold Torus.IsCk at *
    refine hCk.of_le ?_
    norm_cast
    omega
  have hμ2' : Torus.IsCk ((m + 2 : ℕ) : WithTop ℕ∞) μ := by
    unfold Torus.IsCk at *
    refine hCk.of_le ?_
    norm_cast
    omega
  have hVk' : Torus.IsCk ((m + 2 : ℕ) : WithTop ℕ∞) V := by
    unfold Torus.IsCk at *
    refine hVk.of_le ?_
    norm_cast
    omega
  obtain ⟨hBk, hBn⟩ := hC1 μ hμ2
  set B := convGradConv (periodicRieszGrad d s) μ with hBdef
  have hgV : Torus.IsCk ((m + 1 : ℕ) : WithTop ℕ∞) (Torus.grad V) := isCk_grad (m + 1) V hVk'
  have hLB : Torus.IsCk ((m + 1 : ℕ) : WithTop ℕ∞) (fun x => matCLM M (B x)) := by
    unfold Torus.IsCk at *
    exact (matCLM M).contDiff.comp hBk
  have hb : Torus.IsCk ((m + 1 : ℕ) : WithTop ℕ∞)
      (fun x => Torus.matVec M (B x) - Torus.grad V x) := by
    have : (fun x => Torus.matVec M (B x) - Torus.grad V x) =
        (fun x => matCLM M (B x)) - Torus.grad V := rfl
    rw [this]
    unfold Torus.IsCk at *
    exact hLB.sub hgV
  -- numerical bounds
  have hμn : Torus.cbNorm (m + 2) μ ≤ |Λ| :=
    (cbNorm_mono' (by omega) μ).trans (hΛ.trans (le_abs_self _))
  have hμn3 : Torus.cbNorm (m + 3) μ ≤ |Λ| := hΛ.trans (le_abs_self _)
  have hK : 0 ≤ (d : ℝ) ^ 2 * |MB| := by positivity
  -- the drift
  have hLBn : Torus.cbNorm (m + 1) (fun x => matCLM M (B x)) ≤
      (d : ℝ) ^ 2 * |MB| * max C1 0 * |Λ| := by
    refine (cbNorm_clm_comp_le (matCLM M) (m + 1) B hBk).trans ?_
    calc ‖matCLM M‖ * Torus.cbNorm (m + 1) B ≤ ((d : ℝ) ^ 2 * |MB|) * (max C1 0 * |Λ|) := by
          refine mul_le_mul (norm_matCLM_le MB M hM) ?_ (cbNorm_nonneg'C _ _) hK
          calc Torus.cbNorm (m + 1) B ≤ C1 * Torus.cbNorm (m + 1 + 1) μ := hBn
            _ ≤ max C1 0 * Torus.cbNorm (m + 1 + 1) μ :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (cbNorm_nonneg'C _ _)
            _ ≤ max C1 0 * |Λ| := mul_le_mul_of_nonneg_left hμn (le_max_right _ _)
      _ = _ := by ring
  have hgVn : Torus.cbNorm (m + 1) (Torus.grad V) ≤ |VB| :=
    (cbNorm_grad_le (m + 1) V hVk').trans
      ((cbNorm_mono' (by omega) V).trans (hVB.trans (le_abs_self _)))
  have hbn : Torus.cbNorm (m + 1) (fun x => Torus.matVec M (B x) - Torus.grad V x) ≤
      (d : ℝ) ^ 2 * |MB| * max C1 0 * |Λ| + |VB| := by
    have : (fun x => Torus.matVec M (B x) - Torus.grad V x) =
        (fun x => matCLM M (B x)) - Torus.grad V := rfl
    rw [this]
    exact (cbNorm_sub_le' (m + 1) _ _ hLB hgV).trans (add_le_add hLBn hgVn)
  -- the directional derivatives
  have hgμ : Torus.IsCk ((m + 1 : ℕ) : WithTop ℕ∞) (Torus.grad μ) := isCk_grad (m + 1) μ hμ2'
  have hq : (⨆ q : {q : Euc d // ‖q‖ = 1},
      Torus.cbNorm (m + 1) (fun x => inner ℝ q.1 (Torus.grad μ x))) ≤ |Λ| := by
    have : Nonempty {q : Euc d // ‖q‖ = 1} :=
      ⟨⟨EuclideanSpace.single ⟨0, by omega⟩ 1, by simp⟩⟩
    refine ciSup_le fun q => ?_
    have h1 := cbNorm_clm_comp_le (innerSL ℝ q.1) (m + 1) (Torus.grad μ) hgμ
    have h2 : ‖innerSL ℝ q.1‖ ≤ 1 := by
      refine (innerSL ℝ q.1).opNorm_le_bound zero_le_one fun v => ?_
      calc ‖innerSL ℝ q.1 v‖ ≤ ‖q.1‖ * ‖v‖ := by
            simpa using norm_inner_le_norm (𝕜 := ℝ) q.1 v
        _ = 1 * ‖v‖ := by rw [q.2]
    refine (le_of_eq_of_le (by rfl) h1).trans ?_
    calc ‖innerSL ℝ q.1‖ * Torus.cbNorm (m + 1) (Torus.grad μ) ≤ 1 * Torus.cbNorm (m + 1) (Torus.grad μ) :=
          mul_le_mul_of_nonneg_right h2 (cbNorm_nonneg'C _ _)
      _ = Torus.cbNorm (m + 1) (Torus.grad μ) := one_mul _
      _ ≤ Torus.cbNorm (m + 1 + 1) μ := cbNorm_grad_le (m + 1) μ hμ2'
      _ ≤ |Λ| := hμn
  refine ⟨hb, ?_⟩
  linarith

theorem coefficient_bounds_diff_aux (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (Λ : ℝ) :
    ∃ C : ℝ, ∀ (μ₁ μ₂ : Torus d → ℝ) (_ : IsProbDensity μ₁) (_ : IsProbDensity μ₂)
      (_ : Torus.IsCk (m + 3) μ₁) (_ : Torus.IsCk (m + 3) μ₂)
      (_ : Torus.cbNorm (m + 3) μ₁ ≤ Λ) (_ : Torus.cbNorm (m + 3) μ₂ ≤ Λ),
      Torus.IsCk (m + 1) (convGradConv (periodicRieszGrad d s) (μ₁ - μ₂)) ∧
      Torus.cbNorm (m + 1) (convGradConv (periodicRieszGrad d s) (μ₁ - μ₂)) ≤
        C * Torus.cbNorm (m + 2) (μ₁ - μ₂) := by
  obtain ⟨C1, hC1⟩ := convGradConv_cbNorm_of_one_le hd hs0 hsd (m + 1)
  refine ⟨C1, fun μ₁ μ₂ _ _ h₁ h₂ _ _ => ?_⟩
  have h : Torus.IsCk (((m + 1 : ℕ) : WithTop ℕ∞) + 1) (μ₁ - μ₂) := by
    have : Torus.lift (μ₁ - μ₂) = Torus.lift μ₁ - Torus.lift μ₂ := rfl
    unfold Torus.IsCk at *
    rw [this]
    refine (h₁.sub h₂).of_le ?_
    norm_cast
    omega
  exact hC1 _ h

end HRS.PDE
