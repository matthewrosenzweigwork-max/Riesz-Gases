import HRS.Main.A9Aux4

/-!
# Packet A9, part 5: the field objects `Z, 𝕀, Ĩ ∈ E_γ`, their coordinates and measurability
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

open HRS HRS.A33 HRS.PDE

variable {d : ℕ}

/-- The `A33Setup` at the level `γ = gammaIdx d`. -/
def a9Setup (hd : 1 ≤ d) (Rg : Regime) (MB Λ VB ν₀ : ℝ) (D : DynData d) (T : ℝ)
    (ρ : ℝ → Torus d → ℝ) (hA : AdjointData D.s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ) : A33Setup d :=
  ⟨gammaIdx d, a9_mStar_le_gamma, by unfold gammaIdx; omega, hd, Rg, MB, Λ, VB, ν₀, D, T, ρ, hA⟩

section Eval

/-- `F(φ_k) = coord F k`. -/
theorem a9_eval_phi (F : NegSobolev d (gammaIdx d : ℝ)) (k : NonzeroLattice d) :
    NegSobolev.eval F (a9phi d k) = NegSobolev.coord F k := by
  have hs := HRS.FieldSingAux.isSmooth_realMode (d := d) k
  have e : a9phi d k = fun x => a9wt d k * Torus.realMode k x + 0 * Torus.realMode k x := by
    funext x; simp [a9phi]
  rw [e, a33_eval_lin F (a33_cont hs) (a33_cont hs) (a33_ws_of_memSobolev (a33_memSob _ hs))
    (a33_ws_of_memSobolev (a33_memSob _ hs)), a33_eval_realMode]
  unfold NegSobolev.fourierCoeff a9wt
  simp only [zero_mul, add_zero]
  rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
  simp

theorem a9_eval_smul {m : ℝ} (c : ℝ) (F : NegSobolev d m) (ψ : Torus d → ℝ) :
    NegSobolev.eval (c • F) ψ = c * NegSobolev.eval F ψ := by
  unfold NegSobolev.eval
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  unfold NegSobolev.fourierCoeff
  rw [HRS.A34.a34_coord_smul]
  ring

theorem a9_eval_neg {m : ℝ} (F : NegSobolev d m) (ψ : Torus d → ℝ) :
    NegSobolev.eval (-F) ψ = -NegSobolev.eval F ψ := by
  have := a9_eval_smul (-1 : ℝ) F ψ
  simpa using this

theorem a9_eval_sub {m : ℝ} (F G : NegSobolev d m) {ψ : Torus d → ℝ} (hψ : A33WS m ψ) :
    NegSobolev.eval (F - G) ψ = NegSobolev.eval F ψ - NegSobolev.eval G ψ := by
  rw [sub_eq_add_neg, a33_eval_add_left F (-G) hψ, a9_eval_neg]; ring

/-- `eval` of an embedded measure difference against an `H^m` continuous test (`d < 2m`). -/
theorem a9_eval_ofMeasureDiff {m : ℝ} (hm : (d : ℝ) < 2 * m) (μ ν : Measure (Torus d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {ψ : Torus d → ℝ} (hψ : MemSobolev m ψ)
    (hc : Continuous ψ) :
    NegSobolev.eval (NegSobolev.ofMeasureDiff m μ ν) ψ = pair μ ψ - pair ν ψ := by
  obtain ⟨hL2, hs⟩ := hψ
  have hint : Integrable ψ := hL2.integrable one_le_two
  have hmi : (d : ℝ) / 2 + ((0 : ℕ) : ℝ) < m := by
    push_cast; linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  obtain ⟨hsum, -⟩ := Torus.sobolev_coeff_bound hmi hint hs
  have hsum' : Summable fun k : Lattice d => ‖Torus.fcoef ψ k‖ := by simpa using hsum
  exact NegSobolev.eval_ofMeasureDiff_of_summable hm μ ν ψ hc hsum'

end Eval

section Transport

theorem a9_coord_sub {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (F - G) k = NegSobolev.coord F k - NegSobolev.coord G k := by
  unfold NegSobolev.coord
  exact lp.coeFn_sub (F : lp (fun _ : NonzeroLattice d => ℝ) 2) (G : lp (fun _ : NonzeroLattice d => ℝ) 2) ▸ rfl

/-- the propagated mode `U^{0,t} e_k` is an `H^γ` continuous test. -/
theorem a9_U_mem (hd : 1 ≤ d) (Rg : Regime) (MB Λ VB ν₀ T : ℝ) (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (hA : AdjointData D.s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (k : NonzeroLattice d) :
    MemSobolev (gammaIdx d : ℝ) (propagator D ρ 0 t (Torus.realMode k)) ∧
      Continuous (propagator D ρ 0 t (Torus.realMode k)) := by
  let hSu := a9Setup hd Rg MB Λ VB ν₀ D T ρ hA
  obtain ⟨K, -, hK⟩ := hSu.U_bound
  have hs := HRS.FieldSingAux.isSmooth_realMode (d := d) k
  have ht' : t ∈ Set.Icc (0 : ℝ) hSu.T := ht
  exact ⟨(hK (t := t) ht' hs).1, hSu.U_cont ht' hs⟩

/-- the transported field is linear (difference form). -/
theorem a9_transport_sub (hd : 1 ≤ d) (Rg : Regime) (MB Λ VB ν₀ T : ℝ) (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (hA : AdjointData D.s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (F G : NegSobolev d (gammaIdx d : ℝ)) :
    transportField D ρ t (gammaIdx d : ℝ) F - transportField D ρ t (gammaIdx d : ℝ) G =
      transportField D ρ t (gammaIdx d : ℝ) (F - G) := by
  refine HRS.A34.a34_ext fun k => ?_
  rw [a9_coord_sub, HRS.A34.a34_coord_tf hd Rg MB Λ VB ν₀ T D ρ hA ht,
    HRS.A34.a34_coord_tf hd Rg MB Λ VB ν₀ T D ρ hA ht,
    HRS.A34.a34_coord_tf hd Rg MB Λ VB ν₀ T D ρ hA ht,
    a9_eval_sub F G (a33_ws_of_memSobolev (a9_U_mem hd Rg MB Λ VB ν₀ T D ρ hA ht k).1)]
  ring

/-- the transported field is measurable in the field. -/
theorem a9_transport_meas (hd : 1 ≤ d) (Rg : Regime) (MB Λ VB ν₀ T : ℝ) (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (hA : AdjointData D.s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Measurable fun F : NegSobolev d (gammaIdx d : ℝ) => transportField D ρ t (gammaIdx d : ℝ) F := by
  obtain ⟨e⟩ := a33_exists_equiv hd
  refine HRS.Uniform.Q54c.measurable_of_coord fun k => ?_
  have : (fun F : NegSobolev d (gammaIdx d : ℝ) =>
      NegSobolev.coord (transportField D ρ t (gammaIdx d : ℝ) F) k) = fun F =>
      Lattice.jp k.1 ^ (-(gammaIdx d : ℝ)) *
        NegSobolev.eval F (propagator D ρ 0 t (Torus.realMode k)) := by
    funext F
    exact HRS.A34.a34_coord_tf hd Rg MB Λ VB ν₀ T D ρ hA ht F k
  rw [this]
  exact (a33_eval_measurable e (a33_ws_of_memSobolev
    (a9_U_mem hd Rg MB Λ VB ν₀ T D ρ hA ht k).1)).const_mul _

end Transport

end HRS.Main.A9
