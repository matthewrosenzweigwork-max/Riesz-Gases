import HRS.MS.Fp81S21MovingOrbitCont
import HRS.MS.R2InterpAux130
import HRS.MS.Fp81S21MovingItoRep6

/-! Moving prediction: target and deterministic path-space continuity. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.FixEq HRS.MS.CovMeas

/-- The exact 19a-ii target. `H` is the full physical horizon. -/
def fp81s21_moving_prediction_statement
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hH : 0 < H) {N : ℕ} (A : Particle R N) : Prop :=
  ∃ Yh : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d) H,
    (∀ v, Measurable (fun ω => Yh ω v)) ∧
    (∀ᵐ ω ∂A.P, ∀ v ∈ Icc (0 : ℝ) H,
      Yh ω v = s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d) H A.P A.X ω v) ∧
    (∀ᵐ ω ∂A.P, ContinuousOn (Yh ω) (Icc (0 : ℝ) H))

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ}
  {c : MultiIndex d → ℝ} {Pw : ℝ}

theorem fp81s21_moving_Y_continuousOn (hD : S101Data C m T r c)
    (hcls : ∀ (α : MultiIndex d) (t : ℝ), t ∈ Icc (0 : ℝ) T →
      ∃ f, IsClassicalAdjointW C t (oscTestFun m α) f) (hP : (d : ℝ) < 2 * Pw) (hlin : S102Lin C m T)
    (hT : 0 < T) (hd : 1 ≤ d) (hP0 : 0 ≤ Pw) (hr : (d : ℝ) / 2 < r) (hm : (d : ℝ) < m) {N : ℕ} (hN : 0 < N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → EucConfig d N)
    (hXm : ∀ t, Measurable (X t))
    (hmom : ∀ u ∈ Icc (0 : ℝ) T, Integrable (fun x : Euc d => jbracket x ^ Pw)
      (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))))
    (ζ : Ω) (hcz : Continuous fun u : ℝ => zetaB m (P.map (X u.toNNReal)) (X u.toNNReal ζ)) {M : ℝ}
    (hM : ∀ u ∈ Icc (0 : ℝ) T, ∀ f : Euc d → ℝ, IsR2WeightedTest r Pw f →
      |s102_zf P X ζ u f| ≤ M * (weightedSobolevE r Pw f).toReal)
    (hsl : ∀ q ∈ s102_Qset T, ∀ α : MultiIndex d,
      ContinuousOn (fun u => s102_zf P X ζ u (propagatorW C u q (oscTestFun m α))) (Icc 0 q)) :
    ContinuousOn (s102_Y C m T P X ζ) (Icc 0 T) := by
  classical
  set w : OscPath d m T := zetaPathW m T 0 P X ζ with hw
  have hZ : ∀ u ∈ Icc (0 : ℝ) T, S102Z r Pw (s102_zf P X ζ u) := fun u hu =>
    s102_Z_zf hd hP0 hr hN P X u (hmom u hu) ζ
  have hwat : ∀ t ∈ Icc (0 : ℝ) T, r2PathAt w t = zetaB m (P.map (X t.toNNReal)) (X t.toNNReal ζ) := by
    intro t ht
    exact s102_windowPathOf_at (f := fun t : ℝ => zetaB m (P.map (X t.toNNReal)) (X t.toNNReal ζ))
      hcz.continuousOn ht
  have hterm : ∀ t ∈ Icc (0 : ℝ) T, ∀ α : MultiIndex d, propagatorW C t t (oscTestFun m α) = oscTestFun m α :=
    fun t ht α => (s102_propagator_classical (hcls α t ht)).terminal
  have hmatch : ∀ u ∈ Icc (0 : ℝ) T, r2Vprop C m u u (s102_zf P X ζ u) = r2PathAt w u := by
    intro u hu
    apply s102_ext
    intro α
    rw [s102_Vprop_coord hP hD (hZ u hu) hlin hu ⟨le_rfl, hu.2⟩ α, hterm u hu α, hwat u hu,
      s102_coord_zetaB hm hN P X hXm u ζ α]
  -- Lipschitz bound in `t`, uniform in `u`
  have hlip : ∀ u t t' : ℝ, 0 ≤ u → u ≤ t' → t' ≤ t → t ≤ T →
      ‖r2Vprop C m t u (s102_zf P X ζ u) - r2Vprop C m t' u (s102_zf P X ζ u)‖ ≤
        (|M| * s102_KV d r Pw c) * (t - t') := by
    intro u t t' hu hut' ht't htT
    have huT : u ∈ Icc (0 : ℝ) T := ⟨hu, hut'.trans (ht't.trans htT)⟩
    exact s102_Vprop_lip_M hP hD (hZ u huT) hlin (hM u huT) huT ⟨hut', ht't.trans htT⟩
      ⟨hut'.trans ht't, htT⟩ ht't
  -- density of the grid
  have hQd : ∀ t : ℝ, 0 ≤ t → t < T → ∀ δ > 0, ∃ q ∈ s102_Qset T, t < q ∧ q < t + δ ∧ q ≤ T := by
    intro t ht0 htT δ hδ
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min htT (by linarith : t < t + δ))
    have hq3 : (q : ℝ) < T := hq2.trans_le (min_le_left _ _)
    have hq4 : (q : ℝ) < t + δ := hq2.trans_le (min_le_right _ _)
    exact ⟨q, Or.inl ⟨⟨ht0.trans hq1.le, hq3.le⟩, q, rfl⟩, hq1, hq4, hq3.le⟩
  have hslice : ∀ q ∈ s102_Qset T, ContinuousOn (fun u => r2Vprop C m q u (s102_zf P X ζ u)) (Icc 0 q) := fun q hq =>
    s102_V_slice_cont hP hD hlin hZ hM (s102_Qset_sub hT.le hq) (hsl q hq)
  have hjoint := s102_joint_cont (T := T) (K := |M| * s102_KV d r Pw c)
    (mul_nonneg (abs_nonneg M) (s102_KV_nonneg d r Pw c)) (fun u t => r2Vprop C m t u (s102_zf P X ζ u))
    (s102_Qset T) (Or.inr rfl) hQd hlip hslice
  -- the glued function on the square
  have hg2 : Continuous fun p : Icc (0 : ℝ) T × Icc (0 : ℝ) T => r2Vprop C m (max (p.2 : ℝ) p.1) p.1 (s102_zf P X ζ p.1) := by
    refine hjoint.comp_continuous (f := fun p : Icc (0 : ℝ) T × Icc (0 : ℝ) T => ((p.1 : ℝ), max (p.2 : ℝ) (p.1 : ℝ)))
      ((continuous_subtype_val.comp continuous_fst).prodMk
        ((continuous_subtype_val.comp continuous_snd).max (continuous_subtype_val.comp continuous_fst)))
      (fun p => ⟨p.1.2.1, le_max_right _ _, max_le p.2.2.2 p.1.2.2⟩)
  have hg1 : Continuous fun p : Icc (0 : ℝ) T × Icc (0 : ℝ) T => OscPath.at' w p.2 := by
    have : Continuous fun s : Icc (0 : ℝ) T => OscPath.at' w s := by
      show Continuous fun s : Icc (0 : ℝ) T => (show C(Icc (0 : ℝ) T, OscDual d m) from w) s
      exact (show C(Icc (0 : ℝ) T, OscDual d m) from w).continuous
    exact this.comp continuous_snd
  have hg : Continuous fun p : Icc (0 : ℝ) T × Icc (0 : ℝ) T => if (p.2 : ℝ) ≤ p.1 then OscPath.at' w p.2
      else r2Vprop C m (max (p.2 : ℝ) p.1) p.1 (s102_zf P X ζ p.1) :=
    Continuous.if_le hg1 hg2 (continuous_subtype_val.comp continuous_snd) (continuous_subtype_val.comp continuous_fst)
      (fun p hp => by
        have hpe : (p.2 : ℝ) = p.1 := hp
        have e1 : OscPath.at' w p.2 = OscPath.at' w ⟨p.1, p.1.2⟩ := by
          congr 1; exact Subtype.ext hpe
        rw [e1, ← s102_r2PathAt_of_mem w p.1.2, ← hmatch p.1 p.1.2, hpe, max_self])
  set g0 : C(Icc (0 : ℝ) T × Icc (0 : ℝ) T, OscDual d m) := ⟨_, hg⟩ with hg0
  have hpt : ∀ u : ℝ, ∀ hu : u ∈ Icc (0 : ℝ) T, ∀ t : Icc (0 : ℝ) T,
      (fun t' : ℝ => if t' ≤ u then r2PathAt w t' else r2Vprop C m t' u (s102_zf P X ζ u)) (0 + (t : ℝ)) =
        g0 (⟨u, hu⟩, t) := by
    intro u hu t
    simp only [zero_add]
    show (if (t : ℝ) ≤ u then r2PathAt w t else r2Vprop C m t u (s102_zf P X ζ u)) =
      if (t : ℝ) ≤ u then OscPath.at' w t else r2Vprop C m (max (t : ℝ) u) u (s102_zf P X ζ u)
    by_cases h : (t : ℝ) ≤ u
    · simp only [h, if_true]
      exact s102_r2PathAt_of_mem w t.2
    · simp only [h, if_false, max_eq_left (not_le.1 h).le]
  have hY : ∀ u : ℝ, ∀ hu : u ∈ Icc (0 : ℝ) T, s102_Y C m T P X ζ u =
      (show OscPath d m T from ContinuousMap.curry g0 ⟨u, hu⟩) := by
    intro u hu
    unfold s102_Y r2Predicted
    exact s102_windowPathOf_eq _ _ (hpt u hu)
  rw [continuousOn_iff_continuous_restrict]
  have hcurry : Continuous (ContinuousMap.curry g0) := (ContinuousMap.curry g0).continuous
  have : Set.domRestrict (Icc (0 : ℝ) T) (s102_Y C m T P X ζ) =
      fun u : Icc (0 : ℝ) T => (show OscPath d m T from ContinuousMap.curry g0 u) := by
    funext u
    exact hY u u.2
  rw [this]
  exact hcurry

#print axioms HRS.Fp81.S21.fp81s21_moving_prediction_statement
#print axioms HRS.Fp81.S21.fp81s21_moving_Y_continuousOn
end HRS.Fp81.S21
end
