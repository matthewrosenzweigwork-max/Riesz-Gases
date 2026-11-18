import HRS.MC.S7PICPoly
import HRS.Sections.Sec7Setting

/-!
# PI-C (uniqueness of the covariance tensor `J`), part 4: the three time regimes and the main theorem

`T > 0`: `projection_strong_proof` (dyadic polygonal projections).  `T = 0`: the pointwise projection `w ↦ Π_L ∘ w`
(of rank `≤ |box|` since `[0,0]` is a point).  `T < 0`: the path space is the zero space.
-/

noncomputable section

open Filter Topology

namespace HRS.MC.Sec7.S7PIC

open HRS HRS.Sec7

set_option maxSynthPendingDepth 3

variable {d : ℕ} {m : ℝ}

/-- `Π_L` as a continuous linear operator on `E_m`. -/
def S7PIC_Pi (m : ℝ) (L : ℕ) : NegSobolev d m →L[ℝ] NegSobolev d m :=
  LinearMap.mkContinuous
    { toFun := fourierProj m L
      map_add' := q17_fourierProj_add L
      map_smul' := fun c F => q17_fourierProj_smul L c F } 1 (fun F => by
      rw [one_mul]; exact q17_norm_fourierProj_le L F)

theorem S7PIC_Pi_apply (L : ℕ) (F : NegSobolev d m) : S7PIC_Pi m L F = fourierProj m L F := rfl

/-- The pointwise projection `w ↦ Π_L ∘ w` on the path space. -/
def S7PIC_Pz (m T : ℝ) (L : ℕ) : PathSpace d m T →L[ℝ] PathSpace d m T :=
  LinearMap.mkContinuous
    { toFun := fun w => (show PathSpace d m T from
        (⟨fun t => S7PIC_Pi m L (PathSpace.at' w t),
          (S7PIC_Pi m L).continuous.comp (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w).continuous⟩ :
          C(Set.Icc (0 : ℝ) T, NegSobolev d m)))
      map_add' := fun w₁ w₂ => by
        apply S7PIC_path_ext; intro t
        show S7PIC_Pi m L (PathSpace.at' (w₁ + w₂) t) = _ + _
        rw [q17_at_add, map_add]; rfl
      map_smul' := fun c w => by
        apply S7PIC_path_ext; intro t
        show S7PIC_Pi m L (PathSpace.at' (c • w) t) = c • _
        rw [q17_at_smul, map_smul]; rfl } 1 (fun w => by
      rw [one_mul]
      refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 (fun t => ?_)
      show ‖S7PIC_Pi m L (PathSpace.at' w t)‖ ≤ _
      rw [S7PIC_Pi_apply]
      exact (q17_norm_fourierProj_le L _).trans
        (ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w) t))

theorem S7PIC_at_Pz {T : ℝ} (L : ℕ) (w : PathSpace d m T) (t : Set.Icc (0 : ℝ) T) :
    PathSpace.at' (S7PIC_Pz m T L w) t = fourierProj m L (PathSpace.at' w t) := rfl

theorem S7PIC_Pz_norm_le {T : ℝ} (L : ℕ) : ‖S7PIC_Pz (d := d) m T L‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem S7PIC_Pz_tendsto {T : ℝ} (w : PathSpace d m T) :
    Tendsto (fun L : ℕ => S7PIC_Pz m T L w) atTop (𝓝 w) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hK : IsCompact (Set.range (q17_wf w)) := isCompact_range (q17_wf w).continuous
  obtain ⟨L₀, hL₀⟩ := q17_unif_proj hK (ε / 2) (by positivity)
  filter_upwards [eventually_ge_atTop L₀] with L hL
  rw [dist_eq_norm]
  have : ‖S7PIC_Pz m T L w - w‖ ≤ ε / 2 := by
    refine (ContinuousMap.norm_le _ (by positivity)).2 (fun t => ?_)
    exact (hL₀ L hL _ ⟨t, rfl⟩).le
  linarith

/-- The constant path `t ↦ E_k`. -/
def S7PIC_cpath (m : ℝ) (k : NonzeroLattice d) : PathSpace d m 0 :=
  (show PathSpace d m 0 from (⟨fun _ => S7PIC_E m k, continuous_const⟩ :
    C(Set.Icc (0 : ℝ) 0, NegSobolev d m)))

theorem S7PIC_at_cpath (k : NonzeroLattice d) (t : Set.Icc (0 : ℝ) 0) :
    PathSpace.at' (S7PIC_cpath (d := d) m k) t = S7PIC_E m k := rfl

/-- For `T = 0` the projection `Π_L ∘ w` has finite rank. -/
theorem S7PIC_Pz_eq_sum (L : ℕ) (w : PathSpace d m 0) :
    S7PIC_Pz m 0 L w = ∑ k : ↥(S7PIC_box d L),
      S7PIC_lf m 0 ⟨0, le_rfl, le_rfl⟩ k w •
        S7PIC_cpath m k := by
  apply S7PIC_path_ext; intro t
  rw [S7PIC_at_sum, S7PIC_at_Pz]
  have ht : t = ⟨0, le_rfl, le_rfl⟩ := Subtype.ext (le_antisymm t.2.2 t.2.1)
  subst ht
  rw [S7PIC_fourierProj_eq_sum, ← Finset.sum_coe_sort (S7PIC_box d L)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [q17_at_smul, S7PIC_at_cpath, S7PIC_lf_apply]

theorem S7PIC_unique_T0 (D : DynData d) (ρ : ℝ → Torus d → ℝ) (z : ℝ → NegSobolev d m) (I : Set ℝ)
    (J₁ J₂ : TensorDual (PathSpace d m 0) 2) (h₁ : IsJValue D ρ m 0 z I J₁)
    (h₂ : IsJValue D ρ m 0 z I J₂) : J₁ = J₂ := by
  refine S7PIC_eq_of_proj (S7PIC_Pz m 0) J₁ J₂
    (q17_tensorPow_tendsto _ S7PIC_Pz_norm_le S7PIC_Pz_tendsto 2 J₁ h₁.1)
    (q17_tensorPow_tendsto _ S7PIC_Pz_norm_le S7PIC_Pz_tendsto 2 J₂ h₂.1) (fun L => ?_)
  exact S7PIC_tensorPow_eq (S7PIC_Pz m 0 L)
    (fun k : ↥(S7PIC_box d L) => S7PIC_lf m 0 ⟨0, le_rfl, le_rfl⟩ k)
    (fun k => S7PIC_cpath m k) (fun w => by rw [S7PIC_Pz_eq_sum]) J₁ J₂
    (fun a b => S7PIC_agree D ρ z I J₁ J₂ h₁ h₂ _ _ _ _)

theorem S7PIC_unique_Tpos (D : DynData d) (ρ : ℝ → Torus d → ℝ) (z : ℝ → NegSobolev d m) (I : Set ℝ)
    {T : ℝ} (hT : 0 < T)
    (J₁ J₂ : TensorDual (PathSpace d m T) 2) (h₁ : IsJValue D ρ m T z I J₁)
    (h₂ : IsJValue D ρ m T z I J₂) : J₁ = J₂ := by
  obtain ⟨Pj, hPj, -, -, hten⟩ := projection_strong_proof (d := d) m T hT
  exact S7PIC_eq_of_proj Pj J₁ J₂ (hten 2 J₁ h₁.1) (hten 2 J₂ h₂.1)
    (fun L => S7PIC_tensorPow_projPoly D ρ z I J₁ J₂ h₁ h₂ hT.le L (Pj L) (hPj L))

theorem S7PIC_unique_Tneg {T : ℝ} (hT : T < 0) (J₁ J₂ : TensorDual (PathSpace d m T) 2) : J₁ = J₂ := by
  have hE : IsEmpty (Set.Icc (0 : ℝ) T) := ⟨fun t => by linarith [t.2.1, t.2.2]⟩
  have hsub : Subsingleton (PathSpace d m T) :=
    inferInstanceAs (Subsingleton C(Set.Icc (0 : ℝ) T, NegSobolev d m))
  have hM : ∀ M : PathSpace d m T [×2]→L[ℝ] ℝ, M = 0 := by
    intro M
    ext v
    have : v = 0 := funext fun i => Subsingleton.elim _ _
    subst this
    simp
  ext M
  rw [hM M]
  simp

theorem S7PIC_J_unique (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ) (z : ℝ → NegSobolev d m)
    (I : Set ℝ) (J₁ J₂ : TensorDual (PathSpace d m T) 2) (h₁ : IsJValue D ρ m T z I J₁)
    (h₂ : IsJValue D ρ m T z I J₂) : J₁ = J₂ := by
  rcases lt_trichotomy T 0 with hT | rfl | hT
  · exact S7PIC_unique_Tneg hT J₁ J₂
  · exact S7PIC_unique_T0 D ρ z I J₁ J₂ h₁ h₂
  · exact S7PIC_unique_Tpos D ρ z I hT J₁ J₂ h₁ h₂

theorem s7_PI_C_J_unique_proof (R : Regime d) (m T : ℝ) (z : ℝ → NegSobolev d m) (I : Set ℝ)
    (J₁ J₂ : TensorDual (PathSpace d m T) 2) (h₁ : IsJValue R.D R.ρ m T z I J₁)
    (h₂ : IsJValue R.D R.ρ m T z I J₂) : J₁ = J₂ :=
  S7PIC_J_unique R.D R.ρ m T z I J₁ J₂ h₁ h₂

end HRS.MC.Sec7.S7PIC
