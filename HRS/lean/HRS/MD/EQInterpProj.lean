import HRS.MD.EQInterpHolder

/-!
# EQ-INTERP packet, part 4: the Fourier cut-off `P_R` (TeX L4149-4153)

* `projCLM R`: the bounded operator `E_{m₁} → E_m` keeping the modes `⟨k⟩ ≤ R` (norm `≤ R^{m₁-m}`), `projPath` on `𝒳_{·,T}`;
* `cutoff R = projPath ∘ epath`: the frequency cut-off `P_R` of `𝒳_{m,T}`, `coord (P_R F) k = 1[⟨k⟩ ≤ R] coord F k`;
* `sq_norm_sub_cutoff_le`: `‖w - P_R w‖²_{𝒳_m} ≤ R^{-2(m-q)} qSq q w` (tails).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQInterp

variable {d : ℕ}

/-- The multiplier `1[⟨k⟩ ≤ R] ⟨k⟩^{m₁-m}`. -/
def maskW (R m m₁ : ℝ) (k : NonzeroLattice d) : ℝ :=
  if Lattice.jp k.1 ≤ R then Lattice.jp k.1 ^ (m₁ - m) else 0

theorem maskW_abs_le {R m m₁ : ℝ} (hR : 1 ≤ R) (hmm : m ≤ m₁) (k : NonzeroLattice d) :
    |maskW R m m₁ k| ≤ R ^ (m₁ - m) := by
  unfold maskW
  split_ifs with h
  · rw [abs_of_nonneg (Real.rpow_nonneg (Torus.jp_pos k.1).le _)]
    exact Real.rpow_le_rpow (Torus.jp_pos k.1).le h (by linarith)
  · simp only [abs_zero]; exact Real.rpow_nonneg (by linarith) _

theorem memℓp_mask {R m m₁ : ℝ} (hR : 1 ≤ R) (hmm : m ≤ m₁) (G : NegSobolev d m₁) :
    Memℓp (fun k => maskW R m m₁ k * NegSobolev.coord G k) 2 := by
  rw [Torus.memℓp_two_iff]
  obtain ⟨h1, -⟩ := NegSobolev.coord_sq G
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
    (h1.mul_left ((R ^ (m₁ - m)) ^ 2))
  rw [mul_pow]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact sq_le_sq' (by linarith [abs_le.1 (maskW_abs_le hR hmm k), abs_nonneg (maskW R m m₁ k)])
    (abs_le.1 (maskW_abs_le hR hmm k)).2

/-- The (unbundled) cut-off operator `E_{m₁} → E_m`: coordinates `1[⟨k⟩ ≤ R] ⟨k⟩^{m₁-m} coord G k`. -/
def projFun (R m m₁ : ℝ) (hR : 1 ≤ R) (hmm : m ≤ m₁) (G : NegSobolev d m₁) : NegSobolev d m :=
  (⟨fun k => maskW R m m₁ k * NegSobolev.coord G k, memℓp_mask hR hmm G⟩ :
    lp (fun _ : NonzeroLattice d => ℝ) 2)

theorem coord_projFun {R m m₁ : ℝ} (hR : 1 ≤ R) (hmm : m ≤ m₁) (G : NegSobolev d m₁)
    (k : NonzeroLattice d) :
    NegSobolev.coord (projFun R m m₁ hR hmm G) k = maskW R m m₁ k * NegSobolev.coord G k := rfl

theorem norm_projFun_le {R m m₁ : ℝ} (hR : 1 ≤ R) (hmm : m ≤ m₁) (G : NegSobolev d m₁) :
    ‖projFun R m m₁ hR hmm G‖ ≤ R ^ (m₁ - m) * ‖G‖ := by
  have hΛ : 0 ≤ R ^ (m₁ - m) := Real.rpow_nonneg (by linarith) _
  obtain ⟨h1, h2⟩ := NegSobolev.coord_sq (projFun R m m₁ hR hmm G)
  obtain ⟨h3, h4⟩ := NegSobolev.coord_sq G
  have hsq : ‖projFun R m m₁ hR hmm G‖ ^ 2 ≤ (R ^ (m₁ - m) * ‖G‖) ^ 2 := by
    rw [h2, mul_pow, h4, ← tsum_mul_left]
    refine h1.tsum_le_tsum (fun k => ?_) (h3.mul_left _)
    rw [coord_projFun, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact sq_le_sq' (by linarith [abs_le.1 (maskW_abs_le hR hmm k)])
      (abs_le.1 (maskW_abs_le hR hmm k)).2
  exact abs_le_of_sq_le_sq' hsq (by positivity) |>.2

def projCLM (R m m₁ : ℝ) (hR : 1 ≤ R) (hmm : m ≤ m₁) : NegSobolev d m₁ →L[ℝ] NegSobolev d m :=
  LinearMap.mkContinuous
    { toFun := projFun R m m₁ hR hmm
      map_add' := fun F G => by
        refine EQGaussLift.eqgl_ext fun k => ?_
        have hs : ∀ (A B : NegSobolev d m), NegSobolev.coord (A + B) k =
            NegSobolev.coord A k + NegSobolev.coord B k := fun A B => rfl
        have hs' : ∀ (A B : NegSobolev d m₁), NegSobolev.coord (A + B) k =
            NegSobolev.coord A k + NegSobolev.coord B k := fun A B => rfl
        rw [hs, coord_projFun, coord_projFun, coord_projFun, hs']; ring
      map_smul' := fun c F => by
        refine EQGaussLift.eqgl_ext fun k => ?_
        have hs : ∀ (A : NegSobolev d m), NegSobolev.coord (c • A) k = c * NegSobolev.coord A k :=
          fun A => rfl
        have hs' : ∀ (A : NegSobolev d m₁), NegSobolev.coord (c • A) k = c * NegSobolev.coord A k :=
          fun A => rfl
        simp only [RingHom.id_apply]
        rw [hs, coord_projFun, coord_projFun, hs']; ring } (R ^ (m₁ - m))
    (fun G => norm_projFun_le hR hmm G)

theorem projCLM_apply {R m m₁ : ℝ} (hR : 1 ≤ R) (hmm : m ≤ m₁) (G : NegSobolev d m₁) :
    projCLM R m m₁ hR hmm G = projFun R m m₁ hR hmm G := rfl

theorem norm_projCLM_le {R m m₁ : ℝ} (hR : 1 ≤ R) (hmm : m ≤ m₁) :
    ‖(projCLM R m m₁ hR hmm : NegSobolev d m₁ →L[ℝ] NegSobolev d m)‖ ≤ R ^ (m₁ - m) :=
  LinearMap.mkContinuous_norm_le _ (Real.rpow_nonneg (by linarith) _) _

/-- `projCLM` on paths. -/
def projPath (R m m₁ : ℝ) (hR : 1 ≤ R) (hmm : m ≤ m₁) (T : ℝ) :
    PathSpace d m₁ T →L[ℝ] PathSpace d m T :=
  ContinuousLinearMap.compLeftContinuous ℝ (Set.Icc (0 : ℝ) T) (projCLM R m m₁ hR hmm)

theorem projPath_at' {R m m₁ : ℝ} (hR : 1 ≤ R) (hmm : m ≤ m₁) (T : ℝ) (w : PathSpace d m₁ T)
    (t : Set.Icc (0 : ℝ) T) :
    (projPath R m m₁ hR hmm T w).at' t = projFun R m m₁ hR hmm (w.at' t) := rfl

theorem norm_projPath_le {R m m₁ : ℝ} (hR : 1 ≤ R) (hmm : m ≤ m₁) (T : ℝ) :
    ‖(projPath R m m₁ hR hmm T : PathSpace d m₁ T →L[ℝ] PathSpace d m T)‖ ≤ R ^ (m₁ - m) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg (by linarith) _) fun w => ?_
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun t => ?_
  have h1 : ‖(projPath R m m₁ hR hmm T w).at' t‖ ≤ R ^ (m₁ - m) * ‖w.at' t‖ := by
    rw [projPath_at']; exact norm_projFun_le hR hmm _
  have h2 : ‖w.at' t‖ ≤ ‖w‖ :=
    ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0 : ℝ) T, NegSobolev d m₁) from w) t
  calc _ ≤ R ^ (m₁ - m) * ‖w.at' t‖ := h1
    _ ≤ R ^ (m₁ - m) * ‖w‖ := by gcongr

/-- The frequency cut-off `P_R : 𝒳_{m,T} → 𝒳_{m,T}`. -/
def cutoff (R m m₁ : ℝ) (hR : 1 ≤ R) (hmm : m ≤ m₁) (T : ℝ) : PathSpace d m T →L[ℝ] PathSpace d m T :=
  (projPath R m m₁ hR hmm T).comp (epath hmm T)

theorem coord_cutoff {R m m₁ : ℝ} (hR : 1 ≤ R) (hmm : m ≤ m₁) (T : ℝ) (w : PathSpace d m T)
    (t : Set.Icc (0 : ℝ) T) (k : NonzeroLattice d) :
    NegSobolev.coord ((cutoff R m m₁ hR hmm T w).at' t) k =
      if Lattice.jp k.1 ≤ R then NegSobolev.coord (w.at' t) k else 0 := by
  show NegSobolev.coord (projFun R m m₁ hR hmm (NegSobolev.embed m₁ (w.at' t))) k = _
  rw [coord_projFun, EQGaussLift.eqgl_coord_embed hmm]
  unfold maskW
  split_ifs with h
  · have hj := Torus.jp_pos k.1
    simp only [NegSobolev.fourierCoeff]
    rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add hj, ← Real.rpow_add hj,
      show m₁ - m + -m₁ + m = 0 by ring]
    simp
  · simp

end HRS.MD.EQInterp
