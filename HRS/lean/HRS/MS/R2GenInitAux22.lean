import HRS.MS.R2GenInitAux21

/-!
# S10.5 window comparison, packet B8: the window feature family satisfies `S105Feat`

`s105_win_feat`: from the orbit data of S10.3 (bounds `R2OrbitGrad`, classical adjoint solutions, `u`-measurability of the orbit slot) the
family `Γ_a(r,x) = r2WindowFeature C m T (gradComp a) b r x`, `r ∈ [0,b+T]`, is bounded (uniformly in `b`), continuous in `x`, and `r ↦ ⟨e,Γ_a(clamp r,x)⟩` is
measurable.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.MP.RdRem HRS.MS.Go HRS.MS.R2WinErr HRS.MS.GenPath

variable {d : ℕ}

theorem s105_win_feat (hd1 : 1 ≤ d) (C : WholeCoeff d) (k : ℕ) (m T b cdec Cs : ℝ) (hb : 0 ≤ b) (hT : 0 ≤ T)
    (hcd : 0 ≤ cdec) (hCs : 0 ≤ Cs) (hbS : Summable (s104_b d))
    (hG : ∀ α, ∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (oscTestFun m α) (Cs * s104_b d α) cdec)
    (hG' : ∀ α, ∀ t : ℝ, 0 ≤ t → R2OrbitGrad C k t (generatorW C t (oscTestFun m α)) (Cs * s104_b d α) cdec)
    (hφ : ∀ α a, ContDiff ℝ k (fun x => gradComp a (oscTestFun m α) x) ∧ ∀ j ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ j (fun x => gradComp a (oscTestFun m α) x) x‖ ≤ Cs * s104_b d α)
    (hex0 : ∀ α, ∀ t : ℝ, 0 ≤ t → ∃ f, IsClassicalAdjointW C t (oscTestFun m α) f)
    (hex1 : ∀ α, ∀ t : ℝ, 0 ≤ t → ∃ f, IsClassicalAdjointW C t (generatorW C t (oscTestFun m α)) f)
    (hmeasU : ∀ r : ℝ, 0 ≤ r → ∀ (a : Fin d) α x, AEStronglyMeasurable (fun u => if r < b + u then
      gradComp a (propagatorW C r (b + u) (generatorW C (b + u) (oscTestFun m α))) x else 0)
      (volume.restrict (Set.Icc (0 : ℝ) T))) :
    S105Feat d m T (b + T) (fun a r x => r2WindowFeature C m T (gradComp a) b r x) := by
  have hτ : 0 ≤ b + T := by linarith
  have hts : 0 ≤ ∑' α : MultiIndex d, s104_b d α := tsum_nonneg fun α => s104_b_nonneg α
  have hK0 : 0 ≤ (2 + (d : ℝ) ^ k * Real.sqrt T) * (Cs * ∑' α, s104_b d α) := by positivity
  have hfeat : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∀ a : Fin d,
      ContDiff ℝ k (fun x => r2WindowFeature C m T (gradComp a) b r x) ∧ ∀ j ≤ k, ∀ x,
        ‖iteratedFDeriv ℝ j (fun x => r2WindowFeature C m T (gradComp a) b r x) x‖ ≤
          (2 + (d : ℝ) ^ k * Real.sqrt T) * (Cs * ∑' α, s104_b d α) * s104_theta cdec b r := fun r hr a =>
    s104_window_feature hd1 C k m T cdec Cs hT hcd hCs (s104_b d) (fun α => s104_b_nonneg α) hbS hG hG' hφ hb hr.1 a
      (hmeasU r hr.1 a)
  refine ⟨⟨(2 + (d : ℝ) ^ k * Real.sqrt T) * (Cs * ∑' α, s104_b d α), hK0, ?_⟩, ?_, ?_⟩
  · intro a r hr x
    have h0 := (hfeat r hr a).2 0 (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero] at h0
    exact h0.trans (mul_le_of_le_one_right hK0 (s104_theta_le_one hcd b r))
  · intro a r hr
    exact (hfeat r hr a).1.continuous
  · intro a x e
    have hmemall : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), _ := fun r hr =>
      s105_winK C k m T cdec Cs hcd hCs hbS hG hG' hφ hb hr.1 a (hmeasU r hr.1 a) x
    have hCsb : ∀ α, 0 ≤ Cs * s104_b d α := fun α => mul_nonneg hCs (s104_b_nonneg α)
    set A0f : ℝ → ℝ := fun r => inner ℝ e.A₀ (ellVec (d := d) m
      (fun α => gradComp a (propagatorW C r (max b r) (oscTestFun m α)) x)) with hA0f
    set Mf : ℝ → ℝ := fun r => ∫ u in Set.Icc (0 : ℝ) T, inner ℝ ((e.A' : L2Path d m T) u) (if r < b + u then
      ellVec (d := d) m (fun α => gradComp a (propagatorW C r (b + u) (generatorW C (b + u) (oscTestFun m α))) x)
      else 0) with hMf
    set Bf : ℝ → ℝ := fun r => if b ≤ r then inner ℝ e.B (ellVec (d := d) m
      (fun α => gradComp a (oscTestFun m α) x)) else 0 with hBf
    have hsplit : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), inner ℝ e (r2WindowFeature C m T (gradComp a) b r x) =
        A0f r + Mf r + Bf r := by
      intro r hr
      obtain ⟨h1, h2, h3, h4⟩ := hmemall r hr
      rw [s105_win_eq C m T b r a x h1 h4, s105_win_inner e _ _ _ h4]
      congr 1
      simp only [hBf]
      split_ifs with h
      · rfl
      · rw [s55f_ellVec_zero m, inner_zero_right]
    have hA0c : ContinuousOn A0f (Set.Icc (0 : ℝ) (b + T)) :=
      s105_win_A0_cont C m hb Cs a x hbS hex0
        (fun α r hr => s105_coord_le C (hCsb α) hcd (hG α (max b r) (by positivity)) ⟨hr.1, le_max_right _ _⟩ a x)
        e.A₀
    have hMc : ContinuousOn Mf (Set.Icc (0 : ℝ) (b + T)) :=
      s105_win_mid_cont C k m T b cdec Cs hb hT hcd hCs hbS hG' hex1 a x (e.A' : L2Path d m T)
        (fun r hr => (hmemall r hr).2.2.2) (fun r hr => (hmemall r hr).2.2.1)
    have hfun : (fun r => inner ℝ e (r2WindowFeature C m T (gradComp a) b (mrrClamp (b + T) r) x)) =
        fun r => A0f (mrrClamp (b + T) r) + Mf (mrrClamp (b + T) r) + Bf (mrrClamp (b + T) r) :=
      funext fun r => hsplit _ (mrrClamp_mem hτ r)
    rw [hfun]
    refine ((hA0c.comp_continuous (continuous_mrrClamp (b + T)) (fun r => mrrClamp_mem hτ r)).measurable.add
      (hMc.comp_continuous (continuous_mrrClamp (b + T)) (fun r => mrrClamp_mem hτ r)).measurable).add ?_
    exact Measurable.ite (measurableSet_le measurable_const (continuous_mrrClamp (b + T)).measurable)
      measurable_const measurable_const

end HRS.MS.R2GenInit
