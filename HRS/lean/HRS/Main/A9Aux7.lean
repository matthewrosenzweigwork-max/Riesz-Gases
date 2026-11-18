import HRS.Main.A9Aux6

/-!
# Packet A9, part 7: the field objects `Z, 𝕀 ∈ E_γ` and their coordinates; coordinates of embedded vectors
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open HRS HRS.A33 HRS.PDE HRS.Main.A8P

variable {d : ℕ}

/-- The scaled particle field `Z = σ_N (μ_N^t - ρ^t dx) ∈ E_γ`. -/
def a9Z (S : MainData d) (R : ∀ N, Realization d N) (N : ℕ) (t : ℝ) (ω : (R N).Ω) :
    NegSobolev d (gammaIdx d : ℝ) :=
  S.sigma N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical ((R N).X (Real.toNNReal t) ω))
    (withDensityReal (S.ρ N t))

/-- The scaled initial field `κ_N (μ_N^0 - μ°) ∈ E_γ`. -/
def a9F0 (S : MainData d) (R : ∀ N, Realization d N) (N : ℕ) (ω : (R N).Ω) :
    NegSobolev d (gammaIdx d : ℝ) :=
  S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical ((R N).X 0 ω)) S.μ0

/-- The transported initial field `𝕀 = A_N V^{t,0} (κ_N Ξ_N^0)`. -/
def a9I (S : MainData d) (R : ∀ N, Realization d N) (N : ℕ) (t : ℝ) (ω : (R N).Ω) :
    NegSobolev d (gammaIdx d : ℝ) :=
  S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) (a9F0 S R N ω)

/-- The surrogate initial field `Ĩ = A_N V^{t,0} η°`. -/
def a9Itil (S : MainData d) (R : ∀ N, Realization d N) (N : ℕ) (t : ℝ)
    (ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ)) (ω : (R N).Ω) :
    NegSobolev d (gammaIdx d : ℝ) :=
  S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) (ηF N ω)

theorem a9_gamma_gt : (d : ℝ) < 2 * (gammaIdx d : ℝ) := by
  have h : (d : ℝ) ≤ gammaIdx d := by unfold gammaIdx; push_cast; linarith [(Nat.cast_nonneg (PDE.mStar d) : (0:ℝ) ≤ _)]
  have h1 : (0 : ℝ) < gammaIdx d := by
    have : (1 : ℝ) ≤ gammaIdx d := by
      have := PDE.ClassicalPart.three_le_mStar d
      unfold gammaIdx; exact_mod_cast (by omega : 1 ≤ PDE.mStar d + d + 3)
    linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

theorem a9_pair_phi (μ : Measure (Torus d)) (k : NonzeroLattice d) :
    pair μ (a9phi d k) = a9wt d k * pair μ (Torus.realMode k) := by
  unfold pair a9phi
  rw [integral_const_mul]

theorem a9_flucPair_phi {N : ℕ} (x : Fin N → Torus d) (ρ : Torus d → ℝ) (k : NonzeroLattice d) :
    flucPair x ρ (a9phi d k) = a9wt d k * flucPair x ρ (Torus.realMode k) := by
  unfold flucPair
  rw [a9_pair_phi, a9_pair_phi]; ring

section Coord

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ}

theorem a9_Z_coord (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) (ω : (R N).Ω) (k : NonzeroLattice d) :
    NegSobolev.coord (a9Z S R N t ω) k =
      S.sigma N * flucPair ((R N).X (Real.toNNReal t) ω) (S.ρ N t) (a9phi d k) := by
  have hρ := (hS.mean_field.solution N hN).density t ht
  haveI : IsProbabilityMeasure (withDensityReal (S.ρ N t)) := HRS.isProb_withDensityReal hρ
  haveI : IsProbabilityMeasure (empirical ((R N).X (Real.toNNReal t) ω)) :=
    empirical_isProbabilityMeasure hN _
  unfold a9Z
  rw [HRS.A34.a34_coord_smul, coord_ofMeasureDiff a9_gamma_gt, a9_flucPair_phi]
  unfold flucPair a9wt
  simp only [Torus.measureRealCoeff, pair]

theorem a9_U_phi (hd : 1 ≤ d) (Rg : Regime) (MB Λ VB ν₀ T : ℝ) (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (hA : AdjointData D.s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (k : NonzeroLattice d) :
    propagator D ρ 0 t (a9phi d k) = fun x => a9wt d k * propagator D ρ 0 t (Torus.realMode k) x := by
  let hSu := a9Setup hd Rg MB Λ VB ν₀ D T ρ hA
  have ht' : t ∈ Set.Icc (0 : ℝ) hSu.T := ht
  have hs := HRS.FieldSingAux.isSmooth_realMode (d := d) k
  have e : a9phi d k = fun x => a9wt d k * Torus.realMode k x + 0 * Torus.realMode k x := by
    funext x; simp [a9phi]
  have := hSu.U_lin ht' hs hs (a9wt d k) 0
  rw [e]
  funext x
  have h2 := congrFun this x
  simp only [A33Setup.U, hSu, a9Setup] at h2
  simpa using h2

theorem a9_I_coord (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) (ω : (R N).Ω) (k : NonzeroLattice d) :
    NegSobolev.coord (a9I S R N t ω) k =
      S.sigma N * flucPair ((R N).X 0 ω) (S.ρ N 0)
        (propagator (S.dyn N) (S.ρ N) 0 t (a9phi d k)) := by
  have hA := a9_adjointData a9_mStar_le_gamma hS hN
  have hd := S.hd
  obtain ⟨hm, hc⟩ := a9_U_mem hd Rg MB Λ VB ν₀ S.T (S.dyn N) (S.ρ N) hA ht k
  haveI : IsProbabilityMeasure (empirical ((R N).X 0 ω)) := empirical_isProbabilityMeasure hN _
  haveI := S.hμ0
  unfold a9I a9F0
  rw [HRS.A34.a34_coord_smul, HRS.A34.a34_coord_tf hd Rg MB Λ VB ν₀ S.T (S.dyn N) (S.ρ N) hA ht,
    a9_eval_smul, a9_eval_ofMeasureDiff a9_gamma_gt _ _ hm hc, a9_U_phi hd Rg MB Λ VB ν₀ S.T (S.dyn N)
      (S.ρ N) hA ht k]
  have hdat := hS.mean_field.datum N hN
  have hAk := a8p_A_mul_kappa S N
  unfold flucPair pair
  rw [hdat]
  simp only [integral_const_mul, a9wt]
  rw [← hAk]
  ring

end Coord

section Embed

variable {m : ℝ}

theorem a9unit_coord (k j : NonzeroLattice d) :
    NegSobolev.coord (a9unit m k) j = if j = k then 1 else 0 := by
  classical
  show (lp.single 2 k (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2) j = _
  rw [lp.single_apply]
  by_cases h : j = k
  · subst h; simp
  · simp [h]

theorem a9_coord_embed {q : ℕ} {k : Fin q → NonzeroLattice d}
    (y : ℝ^q) (j : NonzeroLattice d) :
    NegSobolev.coord (embedCLM (fun a => a9unit m (k a)) y) j = ∑ a, if j = k a then y a else 0 := by
  rw [← a9unit_inner, embedCLM_apply, inner_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [real_inner_smul_right, a9unit_inner, a9unit_coord]
  split_ifs <;> simp

end Embed

end HRS.Main.A9
