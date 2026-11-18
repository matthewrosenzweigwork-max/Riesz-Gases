import HRS.Equilibrium.Parametrix.PX4bAuxH

/-!
# Packet PX4b auxiliaries I: the row integral of `𝒜_x F` over the second variable
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

open HRS.PDE HRS.PDE.MFAux

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- A conormal kernel of order `< d` (set to `0` on the diagonal) is integrable on `μ ⊗ μ`. -/
theorem px4b_prod_int (hd : 2 ≤ d) (hρ : SmoothPosDensity ρ) {σ : ℝ} (hσ : σ < d) {b : ℕ → ℕ}
    {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ} (hF : ConormalL σ b m B F) :
    Integrable (fun p : Torus d × Torus d => offZero F p.1 p.2)
      ((withDensityReal ρ).prod (withDensityReal ρ)) := by
  have hB := conormalL_B_nonneg hd hF
  have hc := px4b_conormal_zero_const (conormalL_mono_m (Nat.zero_le m) hF)
  have hH : Conormal σ (b 0) 0 B (offZero F) :=
    conormalL_congr_offDiag (fun x y hxy => by simp [offZero, hxy]) hc
  exact conormal_prod_int hd hρ hσ (b 0) hB hH (fun x => by simp [offZero])


/-- Mean zero of `y ↦ 𝒜_x F(x, y)` (the `genFst` half of `gen_integral_comm`); the joint
integrability of the nonlocal kernel is taken as a hypothesis (it is `jop_general`). -/
theorem px4b_genFst_row (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ + 2 < d) {b : ℕ → ℕ} {m : ℕ}
    {B : ℝ} {F : Torus d → Torus d → ℝ} (hm : 2 ≤ m) (hF : ConormalL σ b m B F)
    (hrow : ∀ x, ∫ y, F x y ∂(withDensityReal ρ) = 0)
    (hJ : Integrable (fun p : Torus d × Torus d =>
      offZero (fun u y => Jop d s ρ (fun z => F z y) u) p.1 p.2)
      ((withDensityReal ρ).prod (withDensityReal ρ))) (x : Torus d) :
    Integrable (fun y => genFst d s V β ρ F x y) (withDensityReal ρ) ∧
      ∫ y, genFst d s V β ρ F x y ∂(withDensityReal ρ) = 0 := by
  have hd := H.two_le
  have hρ := H.rho_smooth
  set μ := withDensityReal ρ with hμ
  haveI : IsProbabilityMeasure μ := isProb_withDensityReal hρ.density
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1
  have hρc : Continuous ρ := continuous_of_isSmooth hρ.smooth
  have hK1 := fun i => px4b_K1_conormal (σ := σ) (b := b) (m := m) (B := B) (F := F) (by omega) hF i
  have hK2 := fun i => px4b_K2_conormal (σ := σ) (b := b) (m := m) (B := B) (F := F) hm hF i
  -- the explicit kernel
  obtain ⟨Kexp, hKexp⟩ : ∃ Kexp : Torus d × Torus d → ℝ, ∀ p, Kexp p =
      (β⁻¹ * ∑ i : Fin d, offZero (px4b_K2 i F) p.1 p.2 +
        β⁻¹ * ∑ j : Fin d, (Torus.partialDeriv j ρ p.1 / ρ p.1) * offZero (px4b_K1 j F) p.1 p.2) +
      offZero (fun u y => Jop d s ρ (fun z => F z y) u) p.1 p.2 := ⟨_, fun _ => rfl⟩
  have hq : ∀ j, Continuous (fun u => Torus.partialDeriv j ρ u / ρ u) := fun j =>
    (PDE.continuous_partialDeriv j ρ hρ1).div hρc (fun u => (hρ.pos u).ne')
  have hP2 : ∀ i, Integrable (fun p : Torus d × Torus d => offZero (px4b_K2 i F) p.1 p.2) (μ.prod μ) :=
    fun i => px4b_prod_int hd hρ (σ := σ + 1 + 1) (by linarith) (hK2 i)
  have hP1 : ∀ j, Integrable (fun p : Torus d × Torus d =>
      (Torus.partialDeriv j ρ p.1 / ρ p.1) * offZero (px4b_K1 j F) p.1 p.2) (μ.prod μ) := by
    intro j
    obtain ⟨C, hC⟩ := PDE.MFSchauder.exists_bound_of_cont (hq j)
    have hmeas : AEStronglyMeasurable (fun p : Torus d × Torus d => Torus.partialDeriv j ρ p.1 / ρ p.1)
        (μ.prod μ) := ((hq j).measurable.comp measurable_fst).aestronglyMeasurable
    exact (px4b_prod_int hd hρ (σ := σ + 1) (by linarith) (hK1 j)).bdd_mul (c := C) hmeas
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hC _)
  have hKint : Integrable Kexp (μ.prod μ) := by
    have e : Kexp = fun p => (β⁻¹ * ∑ i : Fin d, offZero (px4b_K2 i F) p.1 p.2 +
        β⁻¹ * ∑ j : Fin d, (Torus.partialDeriv j ρ p.1 / ρ p.1) * offZero (px4b_K1 j F) p.1 p.2) +
      offZero (fun u y => Jop d s ρ (fun z => F z y) u) p.1 p.2 := funext hKexp
    rw [e]
    refine Integrable.add ?_ hJ
    exact ((integrable_finsetSum Finset.univ fun i _ => hP2 i).const_mul β⁻¹).add
      ((integrable_finsetSum Finset.univ fun j _ => hP1 j).const_mul β⁻¹)
  -- pointwise identification off the diagonal
  have hpt : ∀ y u : Torus d, u ≠ y →
      Bop d s V β ρ (fun z => F z y) u + Jop d s ρ (fun z => F z y) u = Kexp (u, y) := by
    intro y u hu
    have hc2 : ContDiffAt ℝ 2 (Torus.lift (fun z => F z y)) (Torus.rep u) :=
      px4b_slice_c2 hm hF y _ (by rw [Torus.mk_rep]; exact hu)
    rw [hKexp, px4b_Bop_eq H hc2]
    simp only [offZero, if_neg hu]
    rfl
  have hne : ∀ y : Torus d, ∀ᵐ u ∂μ, u ≠ y := fun y => px4b_ae_ne_mu (by omega) ρ y
  -- the row integrals of `Kexp`
  have hrowK : ∀ u : Torus d, Integrable (fun y => Kexp (u, y)) μ ∧ ∫ y, Kexp (u, y) ∂μ = 0 := by
    intro u
    have hB := px4b_B_row H hσ hm hF hrow u
    have hJr := px4b_J_row H hσ hm hF hrow u
    have hae : (fun y => Kexp (u, y)) =ᵐ[μ] fun y => Bop d s V β ρ (fun z => F z y) u +
        Jop d s ρ (fun z => F z y) u := by
      filter_upwards [hne u] with y hy
      exact (hpt y u (Ne.symm hy)).symm
    refine ⟨(hB.1.add hJr.1).congr hae.symm, ?_⟩
    rw [integral_congr_ae hae, integral_add hB.1 hJr.1, hB.2, hJr.2, add_zero]
  have hswap := integral_integral_swap (f := fun (u : Torus d) (y : Torus d) => Kexp (u, y)) hKint
  have hcint : Integrable (fun y => ∫ u, Kexp (u, y) ∂μ) μ := hKint.integral_prod_right
  have hc0 : ∫ y, ∫ u, Kexp (u, y) ∂μ ∂μ = 0 := by
    rw [← hswap]
    simp [fun u => (hrowK u).2]
  -- `genFst` as a difference
  have hgen : ∀ y, genFst d s V β ρ F x y =
      (Bop d s V β ρ (fun z => F z y) x + Jop d s ρ (fun z => F z y) x) - ∫ u, Kexp (u, y) ∂μ := by
    intro y
    unfold genFst projGen projMean pair
    beta_reduce
    congr 1
    exact integral_congr_ae ((hne y).mono fun u hu => hpt y u hu)
  have hBx := px4b_B_row H hσ hm hF hrow x
  have hJx := px4b_J_row H hσ hm hF hrow x
  have hKx : Integrable (fun y => Bop d s V β ρ (fun z => F z y) x + Jop d s ρ (fun z => F z y) x) μ :=
    hBx.1.add hJx.1
  have heq : (fun y => genFst d s V β ρ F x y) = fun y =>
      (Bop d s V β ρ (fun z => F z y) x + Jop d s ρ (fun z => F z y) x) - ∫ u, Kexp (u, y) ∂μ :=
    funext hgen
  rw [heq]
  refine ⟨hKx.sub hcint, ?_⟩
  rw [integral_sub hKx hcint, integral_add hBx.1 hJx.1, hBx.2, hJx.2, hc0]
  simp

end HRS.Parx
end
