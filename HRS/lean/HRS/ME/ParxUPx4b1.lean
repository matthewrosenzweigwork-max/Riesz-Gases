import HRS.ME.ParxUNewton2
import HRS.ME.ParxUConormal2
import HRS.Equilibrium.Parametrix.PX1AuxChart
import HRS.Equilibrium.Parametrix.PX1AuxMul
import HRS.Equilibrium.Parametrix.PX2AuxE
import HRS.Equilibrium.Parametrix.PX3aAuxS
import HRS.Equilibrium.Parametrix.PX4bAuxB
import HRS.Equilibrium.Parametrix.PX4bAuxH
import HRS.Equilibrium.Parametrix.PX4bAuxJ
import HRS.Equilibrium.Parametrix.PX4bAuxK

/-!
# Packet P3a (part 1): uniform `px4b_N_class`, `px4b_G_class`, `px4b_aa_class`

Uniform versions (constants chosen before `β, V, ρ`, through the bundle `ParxU`) of the
`HRS.Parx.px4b_*_class` lemmas of `Packets.lean`.  The proofs use only the uniform leaves
`newton_map_general_unif`, `newton_ofChart_general_unif`, `conormal_row_smooth_aux_unif`, and the
ρ-free calculus of `PX1`–`PX4b`.

The file also contains small helpers copied from the packet proofs (monotonicity of the classes,
the `C^k` bound of `cbNorm2` of a function of one variable, the smoothness of `∂ⱼρ/ρ`), so that
the uniform files do not import `Packets.lean`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-! ### Helpers -/

/-- Monotonicity of the classes in `σ`, `b`, `m`, `B` (copy of the packet proof `ConormalL.mono`). -/
theorem px4bU_mono {σ σ' : ℝ} {b b' : ℕ → ℕ} {m m' : ℕ} {B B' : ℝ}
    {F : Torus d → Torus d → ℝ} (h : ConormalL σ b m B F) (hB0 : 0 ≤ B) (hσ : σ ≤ σ')
    (hb : ∀ c, b c ≤ b' c) (hm : m' ≤ m) (hB : B ≤ B') : ConormalL σ' b' m' B' F where
  smooth := h.smooth.of_le (by exact_mod_cast hm)
  near := by
    intro a c hac X z hz hzr
    refine (h.near a c (hac.trans hm) X z hz hzr).trans ?_
    have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hr1 : ‖z‖ ≤ 1 := by unfold r0 at hzr; linarith
    have h1 : ‖z‖ ^ (-(σ + c)) ≤ ‖z‖ ^ (-(σ' + c)) :=
      Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
    have h2 : (1 + |Real.log ‖z‖|) ^ b c ≤ (1 + |Real.log ‖z‖|) ^ b' c :=
      pow_le_pow_right₀ (by linarith [abs_nonneg (Real.log ‖z‖)]) (hb c)
    have hw : 0 ≤ 1 + ‖z‖ ^ (-(σ + c)) * (1 + |Real.log ‖z‖|) ^ b c := by positivity
    calc B * (1 + ‖z‖ ^ (-(σ + c)) * (1 + |Real.log ‖z‖|) ^ b c)
        ≤ B' * (1 + ‖z‖ ^ (-(σ + c)) * (1 + |Real.log ‖z‖|) ^ b c) :=
          mul_le_mul_of_nonneg_right hB hw
      _ ≤ B' * (1 + ‖z‖ ^ (-(σ' + c)) * (1 + |Real.log ‖z‖|) ^ b' c) := by
          refine mul_le_mul_of_nonneg_left ?_ (hB0.trans hB)
          have h3 : 0 ≤ ‖z‖ ^ (-(σ + c)) := by positivity
          have h4 : 0 ≤ (1 + |Real.log ‖z‖|) ^ b c := by positivity
          have h5 := mul_le_mul h1 h2 h4 (by positivity)
          linarith
  far := fun k hk p hp hr => (h.far k (hk.trans hm) p hp hr).trans hB

/-- The sum of two classes of the same order and log index (`ConormalAdd` of the packet file). -/
theorem px4bU_hAdd : ConormalAdd d := fun _ _ _ _ _ _ _ hF hG => conormalL_add hF hG

/-- `cbNorm2` of a function of the first variable is bounded by its `C^k` norm. -/
theorem px4bU_cbNorm2_fst_le {k : ℕ} {g : Torus d → ℝ} (hg : Torus.IsCk (k : WithTop ℕ∞) g) :
    PDE.cbNorm2 k (fun x _ => g x) ≤ Torus.cbNorm k g := by
  have hgs : ContDiff ℝ (k : WithTop ℕ∞) (Torus.lift g) := hg
  unfold PDE.cbNorm2 Torus.cbNorm
  refine Finset.sum_le_sum fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hbdd : BddAbove (Set.range fun x : Euc d => ‖iteratedFDeriv ℝ j (Torus.lift g) x‖) :=
    ⟨Torus.cbNorm k g, by rintro _ ⟨x, rfl⟩; exact HRS.PDE.MFPair.norm_iter_le_cb_ps hg hjk x⟩
  refine ciSup_le fun p => ?_
  have e : PDE.lift2 (fun x _ => g x) = fun q : Euc d × Euc d => Torus.lift g q.1 := rfl
  rw [e]
  exact (HRS.PDE.MFPair.norm_iter_comp_fst_ps hgs hjk p).trans (le_ciSup hbdd p.1)

/-- `cbNorm2` of a function of the second variable is bounded by its `C^k` norm. -/
theorem px4bU_cbNorm2_snd_le {k : ℕ} {g : Torus d → ℝ} (hg : Torus.IsCk (k : WithTop ℕ∞) g) :
    PDE.cbNorm2 k (fun _ y => g y) ≤ Torus.cbNorm k g := by
  have hgs : ContDiff ℝ (k : WithTop ℕ∞) (Torus.lift g) := hg
  unfold PDE.cbNorm2 Torus.cbNorm
  refine Finset.sum_le_sum fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hbdd : BddAbove (Set.range fun x : Euc d => ‖iteratedFDeriv ℝ j (Torus.lift g) x‖) :=
    ⟨Torus.cbNorm k g, by rintro _ ⟨x, rfl⟩; exact HRS.PDE.MFPair.norm_iter_le_cb_ps hg hjk x⟩
  refine ciSup_le fun p => ?_
  have e : PDE.lift2 (fun _ y => g y) = fun q : Euc d × Euc d => Torus.lift g q.2 := rfl
  rw [e]
  exact (HRS.PDE.MFPair.norm_iter_comp_snd_ps hgs hjk p).trans (le_ciSup hbdd p.2)

/-- Smoothness of `x ↦ ∂ⱼρ(x) / ρ(x)` (copy of the packet proof `px4b_q_smooth`). -/
theorem px4bU_q_smooth {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (j : Fin d) :
    Torus.IsSmooth (fun u => Torus.partialDeriv j ρ u / ρ u) := by
  have hρs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ρ) := hρ.smooth
  have e : Torus.lift (fun u => Torus.partialDeriv j ρ u / ρ u) =
      fun v => (fderiv ℝ (Torus.lift ρ) v (EuclideanSpace.single j 1)) / Torus.lift ρ v := by
    funext v
    have h := px4b_lift_partialDeriv ρ j v
    show Torus.partialDeriv j ρ (Torus.mk v) / ρ (Torus.mk v) = _ / Torus.lift ρ v
    rw [← h]
    rfl
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift fun u => Torus.partialDeriv j ρ u / ρ u)
  rw [e]
  refine ContDiff.div ?_ hρs (fun v => (hρ.pos _).ne')
  exact (hρs.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by exact_mod_cast le_rfl)).clm_apply contDiff_const

/-! ### Uniform versions -/

/-- **Uniform version of `px4b_N_class`.** The constant depends only on `(d, s, N, νm, νp, c₀, Λ₀)`
and `(σ, b, m)`; it is chosen before `β, V, ρ`. -/
theorem px4b_N_class_unif (hd : 2 ≤ d) (hsd : s < d) {σ : ℝ} (hσ : σ ≤ s) (b m : ℕ) (hN : m ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      ConormalL (σ - 2) (fun _ => b + 1) m (C * B) (newtonOp d β ρ F) := by
  obtain ⟨C, hC0, hC⟩ := newton_map_general_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd (lt_of_le_of_lt hσ hsd) b m hN
  refine ⟨C, hC0, fun β V ρ U B F hB hF => ?_⟩
  exact conormalL_mono_b (mul_nonneg hC0 hB) (fun c => by split_ifs <;> omega)
    (hC β V ρ U B F hB hF)

/-- **Uniform version of `px4b_G_class`.** The constant depends only on `(d, s, N, νm, νp, c₀, Λ₀)`
and `(σ, b, m)`; the chart is `newtonChart d β⁻¹`, with `β` chosen after the constant. -/
theorem px4b_G_class_unif (hd : 2 ≤ d) (hsd : s < d) {σ : ℝ} (hσ : σ ≤ s) (b m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      ConormalL (σ - 2) (fun _ => b + 1) m (C * B)
        (ofChart (newtonChart d β⁻¹ (toChart F))) := by
  obtain ⟨C, hC0, hC⟩ := newton_ofChart_general_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd (lt_of_le_of_lt hσ hsd) b m
  refine ⟨C, hC0, fun β V ρ U B F hB hF => ?_⟩
  exact conormalL_mono_b (mul_nonneg hC0 hB) (fun c => by split_ifs <;> omega)
    (hC β V ρ U B F hB hF)

/-- **Uniform version of `px4b_aa_class`.** The row means of `G` are `C^m` with norms `≲ B`; the
constant depends only on `(d, s, N, νm, νp, c₀, Λ₀)` and `(σ, b, m)`. -/
theorem px4b_aa_class_unif (hd : 2 ≤ d) (hsd : s < d) {σ : ℝ} (hσ : σ ≤ s) (b m : ℕ) (hN : m ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      Torus.IsCk (m : WithTop ℕ∞) (fun x => ∫ y, ofChart (newtonChart d β⁻¹ (toChart F)) x y
          ∂(withDensityReal ρ)) ∧
      Torus.cbNorm m (fun x => ∫ y, ofChart (newtonChart d β⁻¹ (toChart F)) x y
          ∂(withDensityReal ρ)) ≤ C * B ∧
      Torus.IsCk (m : WithTop ℕ∞) (fun x => ∫ y, ofChart (newtonChart d β⁻¹ (toChart F)) y x
          ∂(withDensityReal ρ)) ∧
      Torus.cbNorm m (fun x => ∫ y, ofChart (newtonChart d β⁻¹ (toChart F)) y x
          ∂(withDensityReal ρ)) ≤ C * B := by
  obtain ⟨CG, hCG0, hCG⟩ := px4b_G_class_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hsd hσ b m
  have hσ2 : σ - 2 < d := by linarith
  obtain ⟨Cr, hCr0, hCr⟩ := conormal_row_smooth_aux_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hσ2 (b + 1) m hN
  refine ⟨Cr * CG, mul_nonneg hCr0 hCG0, fun β V ρ U B F hB hF => ?_⟩
  have hG := hCG β V ρ U B F hB hF
  have hGB : 0 ≤ CG * B := mul_nonneg hCG0 hB
  have h1 := hCr β V ρ U (CG * B) _ hGB hG
  have h2 := hCr β V ρ U (CG * B) _ hGB (conormalL_swap hG)
  refine ⟨h1.1, ?_, h2.1, ?_⟩
  · calc _ ≤ Cr * (CG * B) := h1.2
      _ = _ := by ring
  · calc _ ≤ Cr * (CG * B) := h2.2
      _ = _ := by ring

end HRS.ME.ParxU

end
