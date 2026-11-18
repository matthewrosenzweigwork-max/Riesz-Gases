import HRS.MS.GenPathAux54

/-!
# S5.6 packet P8h: the coordinate array of `𝒯G` is the coordinate array of a continuous path; law of the Gaussian part
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.MS.S52 HRS.Uniform.Q54c

variable {d : ℕ}

/-- The array `(n,α) ↦ ⟨G_{s n}, y1(s n, α)⟩`. -/
def s56FArr (b : WholeBounds d) {Ω : Type*} (s : ℕ → Set.Icc (0 : ℝ) b.T)
    (G : ℝ → Ω → KSpace d b.m b.T) (ζ : Ω) : ℕ × MultiIndex d → ℝ :=
  fun i => inner ℝ (G (s i.1) ζ) (s52y1 b.m b.T (s i.1) i.2)

theorem s56_pathCoords_sub {m T : ℝ} (s : ℕ → Set.Icc (0 : ℝ) T) (w w' : OscPath d m T) :
    s56PathCoords (d := d) m T s (w - w') = s56PathCoords m T s w - s56PathCoords m T s w' := by
  funext i
  simp only [s56PathCoords, Pi.sub_apply]
  have : OscPath.at' (w - w') (s i.1) = OscPath.at' w (s i.1) - OscPath.at' w' (s i.1) := rfl
  rw [this]
  exact s56_coord_sub _ _ _

theorem s56_FArr_range (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) {Ctr Cmax : ℝ}
    (hOM : OrbitMaximalConclusion b.m b.T
      (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax)
    (hS : ∀ r ∈ Set.Icc (0 : ℝ) b.T, IsFiniteMeasure (HRS.Whole.withDensityReal (S.ρ N r)))
    (q : ℝ) (hq : 0 ≤ q) {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {G : ℝ → Ω → KSpace d b.m b.T}
    (hG : IsHilbertMartingaleWithCovariation P ℱ b.T G (fun r _ => s56Db b S N hOM hS q hq r))
    (s : ℕ → Set.Icc (0 : ℝ) b.T) :
    ∀ᵐ ζ ∂P, s56FArr b s G ζ = fun i => OscDual.coord (reconstructPath b.m b.T G ζ (s i.1)) i.2 := by
  have : ∀ i : ℕ × MultiIndex d, ∀ᵐ ζ ∂P, OscDual.coord (reconstructPath b.m b.T G ζ (s i.1)) i.2 =
      inner ℝ (G (s i.1) ζ) (s52y1 b.m b.T (s i.1) i.2) := fun i =>
    s56_recon_coord_eq b hbv S N hC hOM hS q hq hG (s i.1).2 i.2
  filter_upwards [ae_all_iff.2 this] with ζ hζ
  funext i
  exact (hζ i).symm

end HRS.MS.GenPath
