import HRS.MC.S7FCH4A

/-!
# S7FCH4B: the path-level maps of the finite-rank pair (H4, part B)

On `PathSpace d r T = C([0,T];E_r)` (second countable and complete, by local instances): the composition operator
`pmap φ`, the maps `Y_{s,m}(u)(t) = φ_s(u(t) + m(t))` with `φ_s = g - s h` (`s = N^{-1/2}`, `m = m_N` on the particle
side, `s = 0, m = 0` on the Gaussian side) with the key pointwise estimate `Y_sub_le`, and the continuous linear inclusion
`ι : C([0,T];E_r) → L²([0,T];E_r)` (`iota`), `‖ι w‖ ≤ √T ‖w‖`.
-/
open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.FCPlan
open scoped ENNReal NNReal
noncomputable section
namespace HRS.MC.Sec7.S7FCH4
variable {d : ℕ} {r T : ℝ}

instance S7FCH4_pathSC : SecondCountableTopology (PathSpace d r T) :=
  inferInstanceAs (SecondCountableTopology C(Set.Icc (0:ℝ) T, NegSobolev d r))
instance S7FCH4_pathComplete : CompleteSpace (PathSpace d r T) :=
  inferInstanceAs (CompleteSpace C(Set.Icc (0:ℝ) T, NegSobolev d r))

theorem S7FCH4_at_sub (w w' : PathSpace d r T) (t : Set.Icc (0:ℝ) T) :
    PathSpace.at' (w - w') t = PathSpace.at' w t - PathSpace.at' w' t := rfl
theorem S7FCH4_at_add (w w' : PathSpace d r T) (t : Set.Icc (0:ℝ) T) :
    PathSpace.at' (w + w') t = PathSpace.at' w t + PathSpace.at' w' t := rfl
theorem S7FCH4_at_smul (c : ℝ) (w : PathSpace d r T) (t : Set.Icc (0:ℝ) T) :
    PathSpace.at' (c • w) t = c • PathSpace.at' w t := rfl
theorem S7FCH4_at_zero (t : Set.Icc (0:ℝ) T) : PathSpace.at' (0 : PathSpace d r T) t = 0 := rfl

theorem S7FCH4_norm_at_le (w : PathSpace d r T) (t : Set.Icc (0:ℝ) T) : ‖PathSpace.at' w t‖ ≤ ‖w‖ :=
  ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0:ℝ) T, NegSobolev d r) from w) t

theorem S7FCH4_norm_le_of (w : PathSpace d r T) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ t, ‖PathSpace.at' w t‖ ≤ C) : ‖w‖ ≤ C :=
  (ContinuousMap.norm_le (show C(Set.Icc (0:ℝ) T, NegSobolev d r) from w) hC).2 h

def S7FCH4_pmap (φ : NegSobolev d r → NegSobolev d r) (hφ : Continuous φ) (w : PathSpace d r T) :
    PathSpace d r T :=
  (⟨fun t => φ (PathSpace.at' w t), hφ.comp (show C(Set.Icc (0:ℝ) T, NegSobolev d r) from w).continuous⟩ :
    C(Set.Icc (0:ℝ) T, NegSobolev d r))

theorem S7FCH4_at_pmap (φ : NegSobolev d r → NegSobolev d r) (hφ : Continuous φ) (w : PathSpace d r T)
    (t : Set.Icc (0:ℝ) T) : PathSpace.at' (S7FCH4_pmap φ hφ w) t = φ (PathSpace.at' w t) := rfl

theorem S7FCH4_pmap_continuous (φ : NegSobolev d r → NegSobolev d r) (hφ : Continuous φ) :
    Continuous (S7FCH4_pmap (T := T) φ hφ) :=
  ContinuousMap.continuous_postcomp (X := Set.Icc (0:ℝ) T) ⟨φ, hφ⟩

/-! ### The inclusion `C([0,T];E_r) → L²([0,T];E_r)` -/

def S7FCH4_pext (hT : 0 ≤ T) (w : PathSpace d r T) : ℝ → NegSobolev d r :=
  fun t => PathSpace.at' w (Set.projIcc 0 T hT t)

theorem S7FCH4_pext_continuous (hT : 0 ≤ T) (w : PathSpace d r T) : Continuous (S7FCH4_pext hT w) :=
  (show C(Set.Icc (0:ℝ) T, NegSobolev d r) from w).continuous.comp continuous_projIcc

theorem S7FCH4_pext_memLp (hT : 0 ≤ T) (w : PathSpace d r T) :
    MemLp (S7FCH4_pext hT w) 2 (volume.restrict (Set.Icc (0:ℝ) T)) := by
  refine MemLp.of_bound (C := ‖w‖) (S7FCH4_pext_continuous hT w).aestronglyMeasurable ?_
  exact ae_of_all _ (fun t => S7FCH4_norm_at_le w _)

/-- The inclusion of continuous paths into `L²`. -/
def S7FCH4_iota (hT : 0 ≤ T) (w : PathSpace d r T) : L2Path d r T :=
  toL2 r T (S7FCH4_pext hT w)

theorem S7FCH4_iota_eq (hT : 0 ≤ T) (w : PathSpace d r T) :
    S7FCH4_iota hT w = (S7FCH4_pext_memLp hT w).toLp (S7FCH4_pext hT w) := by
  unfold S7FCH4_iota toL2
  rw [dif_pos (S7FCH4_pext_memLp hT w)]

theorem S7FCH4_iota_sub (hT : 0 ≤ T) (w w' : PathSpace d r T) :
    S7FCH4_iota hT (w - w') = S7FCH4_iota hT w - S7FCH4_iota hT w' := by
  rw [S7FCH4_iota_eq, S7FCH4_iota_eq, S7FCH4_iota_eq]
  have : S7FCH4_pext hT (w - w') = S7FCH4_pext hT w - S7FCH4_pext hT w' := by
    funext t; rfl
  simp only [this]
  exact MemLp.toLp_sub (S7FCH4_pext_memLp hT w) (S7FCH4_pext_memLp hT w')

theorem S7FCH4_norm_iota_le (hT : 0 ≤ T) (w : PathSpace d r T) :
    ‖S7FCH4_iota hT w‖ ≤ Real.sqrt T * ‖w‖ := by
  rw [S7FCH4_iota_eq, Lp.norm_toLp]
  have h := eLpNorm_le_of_ae_bound (μ := volume.restrict (Set.Icc (0:ℝ) T)) (p := 2)
    (f := S7FCH4_pext hT w) (C := ‖w‖) (S7FCH4_pext_continuous hT w).aestronglyMeasurable
    (ae_of_all _ (fun t => S7FCH4_norm_at_le w (Set.projIcc 0 T hT t)))
  have hμ : (volume.restrict (Set.Icc (0:ℝ) T)) Set.univ = ENNReal.ofReal T := by
    simp
  rw [hμ] at h
  have h2 : ENNReal.toReal (eLpNorm (S7FCH4_pext hT w) 2 (volume.restrict (Set.Icc (0:ℝ) T))) ≤
      ENNReal.toReal (ENNReal.ofReal T ^ ((2 : ℝ≥0∞).toReal)⁻¹ * ENNReal.ofReal ‖w‖) :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top) h
  refine h2.trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hT, ENNReal.toReal_ofReal (norm_nonneg _)]
  congr 1
  rw [Real.sqrt_eq_rpow]
  norm_num

theorem S7FCH4_iota_lipschitz (hT : 0 ≤ T) :
    LipschitzWith (Real.sqrt T).toNNReal (S7FCH4_iota (d := d) (r := r) hT) := by
  refine LipschitzWith.of_dist_le_mul fun w w' => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Real.sqrt_nonneg _), ← S7FCH4_iota_sub]
  exact S7FCH4_norm_iota_le hT _

theorem S7FCH4_iota_continuous (hT : 0 ≤ T) : Continuous (S7FCH4_iota (d := d) (r := r) hT) :=
  (S7FCH4_iota_lipschitz hT).continuous

/-- `toL2` of a function agreeing with a continuous path on `[0,T]` is `ι` of that path. -/
theorem S7FCH4_toL2_eq_iota (hT : 0 ≤ T) (w : PathSpace d r T) (Y : ℝ → NegSobolev d r)
    (h : ∀ t (ht : t ∈ Set.Icc (0:ℝ) T), Y t = PathSpace.at' w ⟨t, ht⟩) :
    toL2 r T Y = S7FCH4_iota hT w := by
  unfold S7FCH4_iota
  refine HRS.MC.Sec7.S7FCW12.s7fcw12_toL2_congr r T Y _ fun t ht => ?_
  rw [h t ht]
  unfold S7FCH4_pext
  rw [Set.projIcc_of_mem _ ht]


/-! ### The path maps `Y_{s,m}` -/

/-- `φ_s(F) = g(F) - s h(F)`; `s = N^{-1/2}` on the particle side, `s = 0` on the Gaussian side. -/
def S7FCH4_phi (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) (s : ℝ)
    (F : NegSobolev d r) : NegSobolev d r :=
  S7FCH4_gq r S K F - s • S7FCH4_hq r S K F

theorem S7FCH4_phi_continuous (r : ℝ) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d)
    (s : ℝ) : Continuous (S7FCH4_phi r S K s) :=
  (S7FCH4_gq_continuous r S K).sub ((S7FCH4_hq_continuous r S K).const_smul s)

/-- `Y_{s,m}(u)(t) = φ_s(u(t) + m(t))`. -/
def S7FCH4_Y (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) (s : ℝ)
    (m u : PathSpace d r T) : PathSpace d r T :=
  S7FCH4_pmap (S7FCH4_phi r S K s) (S7FCH4_phi_continuous r S K s) (u + m)

theorem S7FCH4_at_Y (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) (s : ℝ)
    (m u : PathSpace d r T) (t : Set.Icc (0:ℝ) T) :
    PathSpace.at' (S7FCH4_Y S K s m u) t =
      S7FCH4_phi r S K s (PathSpace.at' u t + PathSpace.at' m t) := rfl

theorem S7FCH4_Y_continuous (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) (s : ℝ)
    (m : PathSpace d r T) : Continuous (S7FCH4_Y S K s m) :=
  (S7FCH4_pmap_continuous _ _).comp (continuous_id.add continuous_const)

theorem S7FCH4_Y_zero (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) :
    S7FCH4_Y S K 0 (0 : PathSpace d r T) 0 = 0 := by
  apply ContinuousMap.ext
  intro t
  show S7FCH4_phi r S K 0 (PathSpace.at' (0 : PathSpace d r T) t + PathSpace.at' (0 : PathSpace d r T) t) = 0
  simp [S7FCH4_phi, S7FCH4_at_zero, S7FCH4_gq_zero]

/-- The key pointwise estimate between the particle map `Y_{s,m}` and the Gaussian map `Y_{0,0}`. -/
theorem S7FCH4_Y_sub_le (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) {s : ℝ}
    (hs : 0 ≤ s) {m : PathSpace d r T} (hm : ‖m‖ ≤ 1) (u v : PathSpace d r T) :
    ‖S7FCH4_Y S K s m u - S7FCH4_Y S K 0 0 v‖ ≤
      (S7FCH4_Lg r S K + S7FCH4_Lh r S K) * ((1 + ‖u‖ + ‖v‖) * (‖u - v‖ + (‖m‖ + s))) := by
  have hLg := S7FCH4_Lg_nonneg r S K
  have hLh := S7FCH4_Lh_nonneg r S K
  have hu := norm_nonneg u
  have hv := norm_nonneg v
  have hm0 := norm_nonneg m
  have huv := norm_nonneg (u - v)
  refine S7FCH4_norm_le_of _ (by positivity) fun t => ?_
  rw [S7FCH4_at_sub, S7FCH4_at_Y, S7FCH4_at_Y]
  set F := PathSpace.at' u t + PathSpace.at' m t with hF
  set G := PathSpace.at' v t + PathSpace.at' (0 : PathSpace d r T) t with hG
  have hFn : ‖F‖ ≤ ‖u‖ + 1 :=
    (norm_add_le _ _).trans (add_le_add (S7FCH4_norm_at_le u t) ((S7FCH4_norm_at_le m t).trans hm))
  have hGn : ‖G‖ ≤ ‖v‖ := by
    rw [hG, S7FCH4_at_zero, add_zero]; exact S7FCH4_norm_at_le v t
  have hFG : ‖F - G‖ ≤ ‖u - v‖ + ‖m‖ := by
    have : F - G = PathSpace.at' (u - v) t + PathSpace.at' m t := by
      rw [hF, hG, S7FCH4_at_zero, add_zero, S7FCH4_at_sub]; abel
    rw [this]
    exact (norm_add_le _ _).trans (add_le_add (S7FCH4_norm_at_le (u - v) t) (S7FCH4_norm_at_le m t))
  have h1 := S7FCH4_gq_sub_le r S K F G
  have h2 := S7FCH4_hq_sub_le r S K F 0
  rw [S7FCH4_hq_zero, sub_zero, sub_zero] at h2
  have hsplit : S7FCH4_phi r S K s F - S7FCH4_phi r S K 0 G =
      (S7FCH4_gq r S K F - S7FCH4_gq r S K G) - s • S7FCH4_hq r S K F := by
    simp only [S7FCH4_phi, zero_smul, sub_zero]; abel
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  have hA : (‖F‖ + ‖G‖) * ‖F - G‖ ≤ (1 + ‖u‖ + ‖v‖) * (‖u - v‖ + (‖m‖ + s)) := by
    apply mul_le_mul (by linarith) (by linarith) (norm_nonneg _) (by positivity)
  have hB : s * ‖S7FCH4_hq r S K F‖ ≤ S7FCH4_Lh r S K * ((1 + ‖u‖ + ‖v‖) * (‖u - v‖ + (‖m‖ + s))) := by
    calc s * ‖S7FCH4_hq r S K F‖ ≤ s * (S7FCH4_Lh r S K * ‖F‖) :=
          mul_le_mul_of_nonneg_left h2 hs
      _ ≤ s * (S7FCH4_Lh r S K * (1 + ‖u‖ + ‖v‖)) := by
          apply mul_le_mul_of_nonneg_left _ hs
          apply mul_le_mul_of_nonneg_left _ hLh
          linarith
      _ ≤ S7FCH4_Lh r S K * ((1 + ‖u‖ + ‖v‖) * (‖u - v‖ + (‖m‖ + s))) := by
          have : s ≤ ‖u - v‖ + (‖m‖ + s) := by linarith
          nlinarith [mul_nonneg hLh (by positivity : (0:ℝ) ≤ 1 + ‖u‖ + ‖v‖)]
  calc ‖S7FCH4_gq r S K F - S7FCH4_gq r S K G‖ + s * ‖S7FCH4_hq r S K F‖
      ≤ S7FCH4_Lg r S K * ((‖F‖ + ‖G‖) * ‖F - G‖) + S7FCH4_Lh r S K * ((1 + ‖u‖ + ‖v‖) * (‖u - v‖ + (‖m‖ + s))) :=
        add_le_add h1 hB
    _ ≤ S7FCH4_Lg r S K * ((1 + ‖u‖ + ‖v‖) * (‖u - v‖ + (‖m‖ + s))) +
        S7FCH4_Lh r S K * ((1 + ‖u‖ + ‖v‖) * (‖u - v‖ + (‖m‖ + s))) := by
        gcongr
    _ = _ := by ring

theorem S7FCH4_Y_norm_le (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) {s : ℝ}
    (hs : 0 ≤ s) {m : PathSpace d r T} (hm : ‖m‖ ≤ 1) (u : PathSpace d r T) :
    ‖S7FCH4_Y S K s m u‖ ≤
      (S7FCH4_Lg r S K + S7FCH4_Lh r S K) * ((1 + ‖u‖) * (‖u‖ + (‖m‖ + s))) := by
  have := S7FCH4_Y_sub_le S K hs hm u 0
  rw [S7FCH4_Y_zero, sub_zero, norm_zero, add_zero, sub_zero] at this
  exact this

end HRS.MC.Sec7.S7FCH4
