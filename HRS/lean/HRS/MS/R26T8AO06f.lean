import HRS.MS.R26T8AO06e

/-!
# S8.2 T8A O06 (part f): the literal propagator versus the projected age objects
`propagatorW r b φ = propagatorW 0 (b-r) φ = (projected orbit) + constant`; the corrected `Q`, `D`, the scalar forcing and
the projected generator do not see additive constants, so they equal the age objects `QAge`, `DAge`, `ageTest`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_o06_tb_add_const {k : ℕ} {A : ℝ} {g : Euc d → ℝ} (hg : TestBound k A g) (c : ℝ) :
    TestBound k A (fun x => g x + c) := by
  refine ⟨hg.1.add contDiff_const, fun j hj1 hjk x => ?_⟩
  have hgj : ContDiff ℝ (j : WithTop ℕ∞) g := hg.1.of_le (by exact_mod_cast le_top)
  have : iteratedFDeriv ℝ j (fun x => g x + c) x = iteratedFDeriv ℝ j g x := by
    rw [show (fun x => g x + c) = g + fun _ : Euc d => c from rfl]
    have h1 : iteratedFDeriv ℝ j (g + fun _ : Euc d => c) x =
        iteratedFDeriv ℝ j g x + iteratedFDeriv ℝ j (fun _ : Euc d => c) x :=
      iteratedFDeriv_add_apply hgj.contDiffAt contDiff_const.contDiffAt
    rw [iteratedFDeriv_const_of_ne (by omega : j ≠ 0)] at h1
    simpa using h1
  rw [this]
  exact hg.2 j hj1 hjk x

theorem r26t8a_o06_grad_add_const (g : Euc d → ℝ) (c : ℝ) :
    gradient (fun x => g x + c) = gradient g := by
  funext x
  unfold gradient
  rw [fderiv_add_const]

theorem r26t8a_o06_hSource_const (g : Euc d → ℝ) (c : ℝ) : hSource (fun x => g x + c) = hSource g := by
  unfold hSource
  rw [r26t8a_o06_grad_add_const]

theorem r26t8a_o06_aSource_const (mu : Measure (Euc d)) (g : Euc d → ℝ) (c : ℝ) :
    aSource mu (fun x => g x + c) = aSource mu g := by
  unfold aSource
  rw [r26t8a_o06_hSource_const]

theorem r26t8a_o06_SF_const {N : ℕ} (a beta : ℝ) (rho : Euc d → ℝ) (g : Euc d → ℝ) (c : ℝ) :
    scalarForcing (N := N) a beta rho (fun x => g x + c) = scalarForcing a beta rho g := by
  funext X
  unfold scalarForcing
  rw [r26t8a_o06_hSource_const]

theorem r26t8a_o06_D_const {N : ℕ} {a beta M C : ℝ} {rho : Euc d → ℝ}
    {Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ} (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi) {A : ℝ}
    {g : Euc d → ℝ} (hg : TestBound (testOrder d) A g) (c : ℝ) :
    r26t8a_correctedD (N := N) a beta rho Psi (fun x => g x + c) = r26t8a_correctedD a beta rho Psi g := by
  unfold r26t8a_correctedD Phase2S82.correctedD
  rw [r26t8a_o06_psi_const hPsi hg c, r26t8a_o06_aSource_const]

theorem r26t8a_o06_projGen_const (C : WholeCoeff d) (mu : Measure (Euc d)) {g : Euc d → ℝ}
    (hg : ContDiff ℝ ∞ g) (c : ℝ) :
    HRS.Whole.projGeneratorW C mu 0 (fun x => g x + c) = HRS.Whole.projGeneratorW C mu 0 g := by
  have hgen : generatorW C 0 (fun x => g x + c) = generatorW C 0 g := by
    funext x
    have hl : Laplacian.laplacian (fun x => g x + c) x = Laplacian.laplacian g x := by
      have := ContDiffAt.laplacian_add (f₁ := g) (f₂ := fun _ : Euc d => c) (x := x)
        (hg.of_le (by simp)).contDiffAt contDiff_const.contDiffAt
      have e : (fun x => g x + c) = g + fun _ : Euc d => c := rfl
      rw [e, this]; simp
    unfold generatorW
    rw [hl, r26t8a_o06_grad_add_const]
  unfold HRS.Whole.projGeneratorW
  rw [hgen]

end HRS.MS.R26T8A

end
