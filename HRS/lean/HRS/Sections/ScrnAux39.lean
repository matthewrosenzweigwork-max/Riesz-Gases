import HRS.Sections.ScrnAux38

/-!
# Packet SCRN, part 39: the data `ScrnTr` of the transported tests and the remainder bound

* `scrnLamS d s bp ℓ = min (c, 1/b₊) ℓ^{max(q-2,0)}`: the spectral gap lower bound; `1/λ_* = c₁⁻¹ ℓ^{-e}`.
* `ScrnTr`: the transported tests `f_a` (constant datum / classical adjoint solution, Fourier formula,
  `ScrnGB` bounds with the time profile `θ_a(r)`).
* `scrn_rem_final`: `E‖R‖ ≤ p · (C_q C/(2c₁)) · √N o_N ℓ^{-d/2-2-e}`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS

open HRS.Main.A8P PDE

variable {d : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

/-- The lower bound `λ_* = min(c, 1/b₊) ℓ^{max(q-2,0)}` of the nonzero spectral multipliers. -/
def scrnLamS (d : ℕ) (s bp ℓ : ℝ) : ℝ :=
  min (rieszConst d s) bp⁻¹ * ℓ ^ (max ((d : ℝ) - s - 2) 0)

lemma scrnLamS_pos (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {bp ℓ : ℝ} (hbp : 0 < bp)
    (hℓ : 0 < ℓ) : 0 < scrnLamS d s bp ℓ := by
  have hcr : 0 < rieszConst d s := rieszConst_pos hd hs0 hsd
  unfold scrnLamS
  have : 0 < min (rieszConst d s) bp⁻¹ := lt_min hcr (inv_pos.2 hbp)
  positivity

/-- `ℓ^x / λ_* = c₁⁻¹ ℓ^{x - e}`. -/
lemma scrnLamS_inv (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {bp ℓ : ℝ} (hbp : 0 < bp)
    (hℓ : 0 < ℓ) (x : ℝ) :
    ℓ ^ x / scrnLamS d s bp ℓ =
      (min (rieszConst d s) bp⁻¹)⁻¹ * ℓ ^ (x - max ((d : ℝ) - s - 2) 0) := by
  have hcr : 0 < rieszConst d s := rieszConst_pos hd hs0 hsd
  have h1 : 0 < min (rieszConst d s) bp⁻¹ := lt_min hcr (inv_pos.2 hbp)
  unfold scrnLamS
  rw [Real.rpow_sub hℓ]
  have : 0 < ℓ ^ (max ((d : ℝ) - s - 2) 0) := Real.rpow_pos_of_pos hℓ _
  field_simp

lemma scrn_K_int {lam T C : ℝ} (hlam : 0 < lam) (hT : 0 ≤ T) (hC : 0 ≤ C) :
    ∫ r in Icc 0 T, scrnTheta lam T r * C ≤ C / lam := by
  rw [integral_mul_const]
  calc (∫ r in Icc 0 T, scrnTheta lam T r) * C ≤ (1 / lam) * C :=
        mul_le_mul_of_nonneg_right (scrn_theta_int hlam hT) hC
    _ = C / lam := by ring

lemma scrn_LH_int {lam Ta Tb C : ℝ} (hlam : 0 < lam) (ha : 0 ≤ Ta) (hb : 0 ≤ Tb) (hC : 0 ≤ C) :
    ∫ r in Ico 0 (min Ta Tb), C * (scrnTheta lam Ta r * scrnTheta lam Tb r) ≤ C / lam := by
  rw [integral_const_mul]
  calc C * (∫ r in Ico 0 (min Ta Tb), scrnTheta lam Ta r * scrnTheta lam Tb r) ≤ C * (1 / lam) :=
        mul_le_mul_of_nonneg_left (scrn_theta_pair_int hlam ha hb) hC
    _ = C / lam := by ring

/-- The transported tests of a family of decayed copies. -/
structure ScrnTr (d : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) {p : ℕ}
    (ℓ lamS CG : ℝ) (ts : Fin p → ℝ) (ψ : Fin p → Torus d → ℝ)
    (f : Fin p → ℝ → Torus d → ℝ) : Prop where
  ts0 : ∀ a, 0 ≤ ts a
  ck2 : ∀ a, Torus.IsCk 2 (ψ a)
  cases : ∀ a, (ts a = 0 ∧ f a = fun _ => ψ a) ∨ (0 < ts a ∧ IsClassicalAdjointSolution
    (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) (fun _ _ => (1 : ℝ)) (ts a) (ψ a) (f a))
  coeff : ∀ a, ∀ r ∈ Set.Icc 0 (ts a), ∀ k : Lattice d,
    coeffOf (f a r) k = ((Real.exp (-(ts a - r) * scrnLam d s β⁻¹ k) : ℝ) : ℂ) * coeffOf (ψ a) k
  gb : ∀ a, ∀ r ∈ Set.Icc 0 (ts a), ScrnGB d s ℓ (scrnTheta lamS (ts a) r) (f a r) CG

section Tr

variable {s : ℝ} {hs0 : 0 ≤ s} {hsd : s < d} {β : ℝ} {hβ : 0 < β} {p : ℕ} {ℓ lamS CG : ℝ}
  {ts : Fin p → ℝ} {ψ : Fin p → Torus d → ℝ} {f : Fin p → ℝ → Torus d → ℝ}

theorem ScrnTr.f2 (h : ScrnTr d hs0 hsd hβ ℓ lamS CG ts ψ f) :
    ∀ a, ∀ r ∈ Set.Icc 0 (ts a), Torus.IsCk 2 (f a r) := fun a r hr => (h.gb a r hr).ck2

theorem ScrnTr.fcont (h : ScrnTr d hs0 hsd hβ ℓ lamS CG ts ψ f) : ∀ a, Continuous (f a 0) :=
  fun a => scrn_cont_of_ck2 (h.f2 a 0 ⟨le_rfl, h.ts0 a⟩)

theorem ScrnTr.c12 (h : ScrnTr d hs0 hsd hβ ℓ lamS CG ts ψ f) :
    ∀ a, ∃ ft, IsC12Test (ts a) (f a) ft := by
  intro a
  rcases h.cases a with ⟨h0, hfe⟩ | ⟨hpos, hcl⟩
  · rw [hfe, h0]
    exact ⟨_, scrn_isC12Test_zero (h.ck2 a)⟩
  · exact ⟨_, hcl.isC12Test⟩

end Tr

end HRS
