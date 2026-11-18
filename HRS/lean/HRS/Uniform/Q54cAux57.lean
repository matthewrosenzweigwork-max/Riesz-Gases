import HRS.Uniform.Q54cAux51
import HRS.Uniform.Q54cAux56

/-!
# Q54c, part 57: the PDE setup attached to a bound `b`, and admissible dynamics data
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.Uniform.Q54c

open HRS HRS.PDE HRS.Uniform

variable {d : ℕ}

open Classical in
/-- the regime used for the bound `b` -/
def bR (b : GeneralBounds d) : Regime :=
  if b.s ≤ (d : ℝ) - 2 then Regime.R1 else Regime.R2b b.c

theorem bR_lambdaM (b : GeneralBounds d) : ∀ C ν₀ θ, (bR b).lambdaM C ν₀ θ = C := by
  intro C ν₀ θ
  unfold bR
  split_ifs <;> rfl

theorem mStar_le_aux (d : ℕ) : mStar d ≤ d + 3 := by
  unfold mStar
  have : ⌊(d : ℝ) / 2⌋₊ ≤ d := Nat.floor_le_of_le (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  omega

structure SetupHyp (b : GeneralBounds d) : Prop where
  hd : 1 ≤ d
  hs0 : 0 ≤ b.s
  hsd : b.s < d
  hγ : 2 * d + 10 < b.γ

theorem SetupHyp.hn {b : GeneralBounds d} (h : SetupHyp b) : mStar d ≤ (b.γ - 2) + 4 := by
  have := mStar_le_aux d
  have := h.hγ
  omega

theorem SetupHyp.hnd {b : GeneralBounds d} (h : SetupHyp b) : (d : ℝ) / 2 < ((b.γ - 2 : ℕ) : ℝ) := by
  have : (d : ℝ) < ((b.γ - 2 : ℕ) : ℝ) := by
    have := h.hγ
    exact_mod_cast (by omega : d < b.γ - 2)
  linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

theorem SetupHyp.hn2 {b : GeneralBounds d} (h : SetupHyp b) : (d : ℝ) / 2 + 2 < ((b.γ - 2 : ℕ) : ℝ) := by
  have : (d : ℝ) + 2 < ((b.γ - 2 : ℕ) : ℝ) := by
    have := h.hγ
    exact_mod_cast (by omega : d + 2 < b.γ - 2)
  linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

/-- the PDE setup of the bound `b` -/
def mkSetup (b : GeneralBounds d) (h : SetupHyp b) : PdeSetup d where
  hd := h.hd
  s := b.s
  hs0 := h.hs0
  hsd := h.hsd
  n := b.γ - 2
  hn := h.hn
  hnd := h.hnd
  R := bR b
  hR := bR_lambdaM b
  MB := 1
  Λ := b.Λ
  VB := Torus.cbNorm (b.γ - 2 + 4 + 3) b.V
  T := b.T
  Bν := b.Bβ
  c := (exists_pdeConst h.hd b.s h.hs0 h.hsd (b.γ - 2) h.hn (bR b) (bR_lambdaM b) 1 b.Λ
    (Torus.cbNorm (b.γ - 2 + 4 + 3) b.V) b.T b.Bβ).some

theorem matBound_neg_one : MatBound (d := d) 1 (-1) := by
  intro i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem symNonpos_neg_one : Torus.SymNonpos (d := d) (-1) := by
  unfold Torus.SymNonpos Torus.symPart
  have : (1 / 2 : ℝ) • ((-1 : Matrix (Fin d) (Fin d) ℝ) + (-1 : Matrix (Fin d) (Fin d) ℝ).transpose) = -1 := by
    rw [Matrix.transpose_neg, Matrix.transpose_one, ← two_smul ℝ (-1 : Matrix (Fin d) (Fin d) ℝ), smul_smul]
    norm_num
  rw [this, neg_neg]
  exact Matrix.PosSemidef.one

theorem mkData (b : GeneralBounds d) (h : SetupHyp b) (hT : 0 < b.T) (D : DynData d) (μ : ℝ → Torus d → ℝ)
    (hs : D.s = b.s) (hM : D.M = -1) (hVD : D.V = b.V) (hVreg : Torus.IsCk (b.γ - 2 + 4 + 3) b.V)
    (hν : D.invβ ≤ b.Bβ) (hprob : ∀ t ∈ Icc 0 b.T, IsProbDensity (μ t))
    (hreg : IsRegularMF (b.γ + 2 * d + 12) b.Λ b.T μ)
    (hcont : ∀ ψ : Torus d → ℝ, Continuous ψ → ContinuousOn (fun r => ∫ x, ψ x * μ r x) (Icc 0 b.T))
    (hlow : ¬ b.s ≤ (d : ℝ) - 2 → 0 < b.c ∧ ∀ t ∈ Icc 0 b.T, ∀ x, b.c ≤ μ t x) :
    (mkSetup b h).Data D 0 μ := by
  refine ⟨⟨hs, ?_, ?_, ?_, hT, ?_⟩, hν⟩
  · rw [hM]; exact matBound_neg_one
  · exact ⟨by rw [hVD]; exact hVreg, by rw [hVD]; exact le_refl _⟩
  · refine ⟨hprob, fun r hr => ?_, fun r hr => ?_, hcont⟩
    · exact ContDiff.of_le (hreg r hr).1 (by exact_mod_cast (by have := h.hγ; omega : b.γ - 2 + 4 + 3 ≤ b.γ + 2 * d + 12))
    · exact (cbNorm_mono' (by have := h.hγ; omega : b.γ - 2 + 4 + 3 ≤ b.γ + 2 * d + 12) (μ r)).trans (hreg r hr).2
  · show (bR b).Holds d b.s D.M D.invβ 0 b.T μ
    unfold bR
    by_cases hc : b.s ≤ (d : ℝ) - 2
    · simp only [hc, if_true]; exact hc
    · simp only [hc, if_false]
      obtain ⟨hc0, hcl⟩ := hlow hc
      exact ⟨by linarith, by rw [hM]; exact symNonpos_neg_one, hc0, hcl⟩

end HRS.Uniform.Q54c
