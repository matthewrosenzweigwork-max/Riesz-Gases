import HRS.Equilibrium.Parametrix.Packets
import HRS.Equilibrium.Parametrix.PX5AuxB
import HRS.Equilibrium.Parametrix.PX2AuxE
import HRS.Equilibrium.Parametrix.PX3aAuxW

/-!
# Prop 4.13 parametrix, packet PX5: structure of `ψ^loc` and `R_L`

Uniform conormal classes of `𝒩R_j` (`j < L`), of `ψ^loc_L`; measurability, symmetry, canonicity,
the telescoping identity, additivity with smooth kernels and the remainder.
-/

open MeasureTheory Filter Topology
noncomputable section

namespace HRS.Parx

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

theorem px5_cont_slice2 {R : Torus d → Torus d → ℝ} {m : ℕ} (hR : PDE.IsCk2 m R) (x : Torus d) :
    Continuous (fun y => R x y) :=
  Torus.continuous_of_continuous_lift (PDE.MFPair.isCk_slice2 m R hR x).continuous

/-- `diagExt` does not change double centring. -/
theorem px5_dc_diagExt (hd : 0 < d) {F : Torus d → Torus d → ℝ}
    (hF : PDE.DoublyCentered (withDensityReal ρ) F) :
    PDE.DoublyCentered (withDensityReal ρ) (diagExt F) := by
  have hae : ∀ y : Torus d, ∀ᵐ w ∂(withDensityReal ρ), w ≠ y := by
    intro y
    have h0 : (withDensityReal ρ) {y} = 0 :=
      withDensity_absolutelyContinuous _ _ (volume_singleton_torus hd y)
    have := (measure_eq_zero_iff_ae_notMem (μ := withDensityReal ρ) (s := {y})).1 h0
    filter_upwards [this] with w hw using hw
  refine ⟨fun y => ?_, fun x => ?_⟩
  · have := hF.1 y
    unfold pair at this ⊢
    rw [← this]
    refine integral_congr_ae ?_
    filter_upwards [hae y] with w hw
    simp [diagExt, hw]
  · have := hF.2 x
    unfold pair at this ⊢
    rw [← this]
    refine integral_congr_ae ?_
    filter_upwards [hae x] with w hw
    simp [diagExt, Ne.symm hw]

/-- number of conormal derivatives used: `m = (J+1) + 2L`. -/
def px5m (d J : ℕ) : ℕ := (J + 1) + 2 * parxL d J

theorem px5_conormalAdd : ConormalAdd d := fun _ _ _ _ _ _ _ hF hG => ConormalL.add hF hG

theorem px5_crit_lt (H : ParxHyp d s V β ρ) : s - 2 + 2 < d := by
  have := H.s_lt; linarith

theorem px5_s_pos (H : ParxHyp d s V β ρ) : 0 < s := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast H.two_le
  rw [H.crit]; linarith

/-- uniform class of `𝒩R_j`, `j < L`. -/
theorem px5_N_class (H : ParxHyp d s V β ρ) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Torus d → ℝ, Torus.IsSmooth f → ∀ j < parxL d J,
      Conormal (s - 2) 1 (J + 3) (C * posSeminorm (px5m d J + 2) f)
        (newtonOp d β ρ (parxR d s V β ρ f j)) := by
  have h : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (j < parxL d J → ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      Conormal (s - 2) 1 (J + 3) (C * posSeminorm (px5m d J + 2) f)
        (newtonOp d β ρ (parxR d s V β ρ f j))) := by
    intro j
    by_cases hj : j < parxL d J
    · obtain ⟨C, hC0, hC⟩ := parxN_conormal H (px5m d J) j (by unfold px5m; omega)
      refine ⟨C, hC0, fun _ f hf => ?_⟩
      have hB0 : 0 ≤ C * posSeminorm (px5m d J + 2) f := mul_nonneg hC0 (posSeminorm_nonneg' _ _)
      refine ConormalL.mono (hC f hf) hB0 ?_ (fun c => ?_) ?_ le_rfl
      · have : (0 : ℝ) ≤ (j : ℝ) / 2 := by positivity
        linarith
      · split_ifs <;> simp
      · unfold px5m; omega
    · exact ⟨0, le_rfl, fun h => absurd h hj⟩
  choose C hC0 hC using h
  refine ⟨∑ j ∈ Finset.range (parxL d J), C j, Finset.sum_nonneg fun j _ => hC0 j, ?_⟩
  intro f hf j hj
  have hB0 : 0 ≤ C j * posSeminorm (px5m d J + 2) f := mul_nonneg (hC0 j) (posSeminorm_nonneg' _ _)
  refine ConormalL.mono (hC j hj f hf) hB0 le_rfl (fun c => le_rfl) le_rfl ?_
  refine mul_le_mul_of_nonneg_right ?_ (posSeminorm_nonneg' _ _)
  exact Finset.single_le_sum (f := C) (fun i _ => hC0 i) (Finset.mem_range.mpr hj)

/-- class of `ψ^loc_L`. -/
theorem px5_psi_class (H : ParxHyp d s V β ρ) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      Conormal (s - 2) 1 (J + 3) (C * posSeminorm (px5m d J + 2) f)
        (parxPsi d s V β ρ f (parxL d J)) := by
  obtain ⟨C, hC0, hC⟩ := px5_N_class H J
  refine ⟨(parxL d J : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC0, fun f hf => ?_⟩
  have h := conormal_finset_sum (d := d) px5_conormalAdd (s - 2) (fun _ => 1) (J + 3)
    (Finset.range (parxL d J)) (fun j => newtonOp d β ρ (parxR d s V β ρ f j))
    (fun _ => C * posSeminorm (px5m d J + 2) f)
    (fun j hj => hC f hf j (Finset.mem_range.mp hj))
  have e : (∑ _j ∈ Finset.range (parxL d J), C * posSeminorm (px5m d J + 2) f) =
      (parxL d J : ℝ) * C * posSeminorm (px5m d J + 2) f := by
    simp; ring
  rw [e] at h
  exact h

theorem px5_newtonOp_diag (F : Torus d → Torus d → ℝ) (x : Torus d) : newtonOp d β ρ F x x = 0 := by
  simp [newtonOp]

theorem px5_psi_diag (f : Torus d → ℝ) (n : ℕ) (x : Torus d) : parxPsi d s V β ρ f n x x = 0 := by
  simp [parxPsi, px5_newtonOp_diag]

theorem px5_measurable (H : ParxHyp d s V β ρ) (J : ℕ) (f : Torus d → ℝ) (hf : Torus.IsSmooth f) :
    Measurable (Function.uncurry (parxPsi d s V β ρ f (parxL d J))) := by
  obtain ⟨C, hC0, hC⟩ := px5_psi_class H J
  have h := conormal_measurable (hC f hf)
  have e : offZero (parxPsi d s V β ρ f (parxL d J)) = parxPsi d s V β ρ f (parxL d J) := by
    funext x y
    by_cases hxy : x = y
    · subst hxy; simp [offZero, px5_psi_diag]
    · simp [offZero, hxy]
  rwa [e] at h

theorem px5_symm (H : ParxHyp d s V β ρ) (J : ℕ) (f : Torus d → ℝ) (hf : Torus.IsSmooth f) :
    IsSymmPair (parxPsi d s V β ρ f (parxL d J)) := by
  intro x y
  unfold parxPsi
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨C, hC0, hC⟩ := parxR_conormal H (px5m d J) j (by
    have := Finset.mem_range.mp hj; unfold px5m; omega)
  exact newton_symm _ (hC f hf).2.1 x y

/-- rows of `ψ^loc_L` are integrable, with total integral zero. -/
theorem px5_canonical (H : ParxHyp d s V β ρ) (J : ℕ) (f : Torus d → ℝ) (hf : Torus.IsSmooth f) :
    IsCanonicalPair (withDensityReal ρ) (parxPsi d s V β ρ f (parxL d J)) := by
  have hd := H.two_le
  obtain ⟨K, hK0, hK⟩ := conormal_row_int hd H.rho_smooth (σ := s - 2) (by have := H.s_lt; linarith) 1
  obtain ⟨C, hC0, hC⟩ := px5_N_class H J
  intro x
  have hint : ∀ j ∈ Finset.range (parxL d J),
      Integrable (fun y => newtonOp d β ρ (parxR d s V β ρ f j) x y) (withDensityReal ρ) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hcl := hC f hf j hj'
    have hB0 : 0 ≤ C * posSeminorm (px5m d J + 2) f := mul_nonneg hC0 (posSeminorm_nonneg' _ _)
    have h0 : Conormal (s - 2) 1 0 (C * posSeminorm (px5m d J + 2) f)
        (newtonOp d β ρ (parxR d s V β ρ f j)) :=
      ConormalL.mono hcl hB0 le_rfl (fun c => le_rfl) (Nat.zero_le _) le_rfl
    exact (hK _ _ hB0 h0 (fun x => px5_newtonOp_diag _ x) x).1
  refine ⟨?_, ?_⟩
  · have := integrable_finset_sum _ hint
    exact this
  · have e : (fun y => parxPsi d s V β ρ f (parxL d J) x y) =
        fun y => ∑ j ∈ Finset.range (parxL d J), newtonOp d β ρ (parxR d s V β ρ f j) x y := rfl
    rw [e, integral_finsetSum _ hint]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    obtain ⟨C', hC'0, hC'⟩ := parxR_conormal H (px5m d J) j (by unfold px5m; omega)
    obtain ⟨hc, -, hdc⟩ := hC' f hf
    have hσ : s - (j : ℝ) / 2 < d := by
      have : (0 : ℝ) ≤ (j : ℝ) / 2 := by positivity
      linarith [H.s_lt]
    exact (newton_doublyCentered H hσ hc).2 x


theorem px5_parxK (d J : ℕ) : parxK d J = px5m d J + 2 := by
  unfold parxK px5m parxL; omega

theorem px5_remainder (H : ParxHyp d s V β ρ) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      PDE.IsCk2 J (diagExt (parxR d s V β ρ f (parxL d J))) ∧
      PDE.DoublyCentered (withDensityReal ρ) (diagExt (parxR d s V β ρ f (parxL d J))) ∧
      PDE.cbNorm2 J (diagExt (parxR d s V β ρ f (parxL d J))) ≤ C * posSeminorm (parxK d J) f ∧
      (∀ x y, diagExt (parxR d s V β ρ f (parxL d J)) x y =
        diagExt (parxR d s V β ρ f (parxL d J)) y x) := by
  have hL : 2 * parxL d J ≤ px5m d J := by unfold px5m; omega
  obtain ⟨C, hC0, hC⟩ := parxR_conormal H (px5m d J) (parxL d J) hL
  have e : px5m d J - 2 * parxL d J = J + 1 := by unfold px5m; omega
  have hσ : s - (parxL d J : ℝ) / 2 + ((J : ℝ) + 1) < 0 := by
    have hc : (parxL d J : ℝ) = 2 * J + d + 6 := by unfold parxL; push_cast; ring
    rw [hc, H.crit]; linarith
  obtain ⟨Ce, hCe0, hCe⟩ := conormal_extend H.two_le J (s - (parxL d J : ℝ) / 2) 0 hσ
  refine ⟨Ce * C, mul_nonneg hCe0 hC0, fun f hf => ?_⟩
  obtain ⟨hcl, hsym, hdc⟩ := hC f hf
  rw [e] at hcl
  have hB0 : 0 ≤ C * posSeminorm (px5m d J + 2) f := mul_nonneg hC0 (posSeminorm_nonneg' _ _)
  obtain ⟨h1, h2, h3⟩ := hCe _ _ hB0 hcl
  refine ⟨h1, px5_dc_diagExt (by have := H.two_le; omega) hdc, ?_, ?_⟩
  · rw [px5_parxK]
    calc _ ≤ Ce * (C * posSeminorm (px5m d J + 2) f) := h2
      _ = _ := by ring
  · intro x y
    by_cases hxy : x = y
    · subst hxy; rfl
    · have hyx : y ≠ x := Ne.symm hxy
      rw [h3 x y hxy, h3 y x hyx]
      exact hsym x y

/-- the defect step off the diagonal -/
theorem px5_defect_step (f : Torus d → ℝ) (j : ℕ) (x y : Torus d) (hxy : x ≠ y) :
    parxR d s V β ρ f (j + 1) x y = parxR d s V β ρ f j x y +
      genFst d s V β ρ (newtonOp d β ρ (parxR d s V β ρ f j)) x y +
      genSnd d s V β ρ (newtonOp d β ρ (parxR d s V β ρ f j)) x y := by
  simp [parxR, defectOp, hxy]

theorem px5_telescope_aux (f : Torus d → ℝ) (x y : Torus d) (hxy : x ≠ y) (n : ℕ) :
    parxR d s V β ρ f n x y = parxR d s V β ρ f 0 x y +
      (∑ j ∈ Finset.range n, genFst d s V β ρ (newtonOp d β ρ (parxR d s V β ρ f j)) x y +
        ∑ j ∈ Finset.range n, genSnd d s V β ρ (newtonOp d β ρ (parxR d s V β ρ f j)) x y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [px5_defect_step f n x y hxy, ih, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

theorem px5_telescope (H : ParxHyp d s V β ρ) (J : ℕ) (f : Torus d → ℝ) (hf : Torus.IsSmooth f)
    (x y : Torus d) (hxy : x ≠ y) :
    parxR d s V β ρ f (parxL d J) x y =
      Hsource d s ρ f x y + genFst d s V β ρ (parxPsi d s V β ρ f (parxL d J)) x y +
        genSnd d s V β ρ (parxPsi d s V β ρ f (parxL d J)) x y := by
  obtain ⟨C, hC0, hC⟩ := px5_N_class H J
  have hgs := gen_sum H (px5_crit_lt H) (b := 1) (m := J + 3) (by omega) (parxL d J)
    (fun j => newtonOp d β ρ (parxR d s V β ρ f j))
    (fun j hj => ⟨_, hC f hf j hj⟩) x y hxy
  have e : parxPsi d s V β ρ f (parxL d J) =
      fun x y => ∑ j ∈ Finset.range (parxL d J), newtonOp d β ρ (parxR d s V β ρ f j) x y := rfl
  rw [e, hgs.1, hgs.2, px5_telescope_aux f x y hxy]
  have h0 : parxR d s V β ρ f 0 x y = Hsource d s ρ f x y := by simp [parxR, offZero, hxy]
  rw [h0]; ring

theorem px5_add_smooth (H : ParxHyp d s V β ρ) (J : ℕ) (f : Torus d → ℝ) (hf : Torus.IsSmooth f)
    (Ψ : Torus d → Torus d → ℝ) (hΨ : PDE.IsCk2 2 Ψ) (x y : Torus d) (hxy : x ≠ y) :
    genFst d s V β ρ (fun x y => parxPsi d s V β ρ f (parxL d J) x y + Ψ x y) x y =
        genFst d s V β ρ (parxPsi d s V β ρ f (parxL d J)) x y + genFst d s V β ρ Ψ x y ∧
      genSnd d s V β ρ (fun x y => parxPsi d s V β ρ f (parxL d J) x y + Ψ x y) x y =
        genSnd d s V β ρ (parxPsi d s V β ρ f (parxL d J)) x y + genSnd d s V β ρ Ψ x y ∧
      Jpair d s ρ (fun x y => parxPsi d s V β ρ f (parxL d J) x y + Ψ x y) x y =
        Jpair d s ρ (parxPsi d s V β ρ f (parxL d J)) x y + Jpair d s ρ Ψ x y := by
  obtain ⟨C, hC0, hC⟩ := px5_psi_class H J
  exact gen_add_smooth H (px5_crit_lt H) (b := 1) (m := J + 3) (by omega) (hC f hf) hΨ x y hxy

end HRS.Parx

end
