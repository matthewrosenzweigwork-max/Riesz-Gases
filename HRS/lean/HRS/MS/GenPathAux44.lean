import HRS.MS.GenPathAux43

/-!
# S5.6 packet P8c: coordinates of `𝒯G` for a Gaussian `𝒦`-martingale `G` with covariation density `Db`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.MS.S52 HRS.MP.RdRem

variable {d : ℕ}

theorem s56Db_dir_zero (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) {Ctr Cmax : ℝ}
    (hOM : OrbitMaximalConclusion b.m b.T
      (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax)
    (hS : ∀ r ∈ Set.Icc (0 : ℝ) b.T, IsFiniteMeasure (HRS.Whole.withDensityReal (S.ρ N r)))
    (q : ℝ) (hq : 0 ≤ q) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b.T) (α : MultiIndex d) :
    ∀ σ ∈ Set.Ioc t b.T, s56Db b S N hOM hS q hq σ (s52y1 b.m b.T t α - s52y2 b.m b.T α)
      (s52y1 b.m b.T t α - s52y2 b.m b.T α) = 0 := by
  intro σ hσ
  have hσ' : σ ∈ Set.Icc (0 : ℝ) b.T := ⟨ht.1.trans hσ.1.le, hσ.2⟩
  rw [(s56Db_spec b S N hOM hS q hq hσ').1]
  unfold featureForm
  have hz : ∀ (a : Fin d) (x : Euc d), inner ℝ (gradFeature (S.coeff N) b.m b.T a σ x)
      (s52y1 b.m b.T t α - s52y2 b.m b.T α) = 0 := by
    intro a x
    rw [inner_sub_right, s52_pair_grad_y1 hC ht.2 a hσ' x α, if_neg (not_le.2 hσ.1),
      s52_pair_grad_y2 hC hbv.hT.le a σ x α, sub_self]
  simp [hz]

theorem s56_recon_coord_eq (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) {Ctr Cmax : ℝ}
    (hOM : OrbitMaximalConclusion b.m b.T
      (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax)
    (hS : ∀ r ∈ Set.Icc (0 : ℝ) b.T, IsFiniteMeasure (HRS.Whole.withDensityReal (S.ρ N r)))
    (q : ℝ) (hq : 0 ≤ q) {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {G : ℝ → Ω → KSpace d b.m b.T}
    (hG : IsHilbertMartingaleWithCovariation P ℱ b.T G (fun r _ => s56Db b S N hOM hS q hq r))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b.T) (α : MultiIndex d) :
    ∀ᵐ ζ ∂P, OscDual.coord (reconstructPath b.m b.T G ζ t) α = inner ℝ (G t ζ) (s52y1 b.m b.T t α) := by
  have h := s56_incr_zero hG ht (s52y1 b.m b.T t α - s52y2 b.m b.T α)
    (s56Db_dir_zero b hbv S N hC hOM hS q hq ht α)
  filter_upwards [h] with ζ hζ
  rw [s52_coord_recon ht.1 ht.2]
  simp only [inner_sub_right] at hζ
  linarith

end HRS.MS.GenPath
