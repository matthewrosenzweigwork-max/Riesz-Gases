import HRS.Main.Det16B2
import HRS.Main.Det22Aux2
import HRS.Uniform.Q54cAux43

/-!
# det16d L10: identification of the deterministic limit (Example A.16)

For a solution `Y'` of the linearized equation at noise level `q = 0` with deterministic datum
`embed ηin`, a.s. `Y'^t = embed_{γ+2}(V_∞^{t,0} ηin)` for all `t ∈ [0,T]` simultaneously, and
`t ↦ embed_{γ+2}(V_∞^{t,0} ηin)` is continuous; consequently `law (toPath Y') = δ_{ξ_∞}`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Main.Det16

open HRS HRS.PDE HRS.A33 HRS.A34 HRS.Main HRS.Uniform HRS.Uniform.Q54c

variable {d : ℕ}

/-- At noise level `0` the Gaussian part vanishes: a.s. `Y^t(φ) = Y⁰(U^{0,t}φ)`. -/
theorem det16d_ae_eval {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ) (y₀ : NegSobolev d m)
    (Y : ℝ → Ω → NegSobolev d m) (hY : IsLinearFluctuationSolution P D ρ m 0 T (fun _ => y₀) Y)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (hmem : MemSobolev m φ) :
    ∀ᵐ ω ∂P, NegSobolev.eval (Y t ω) φ = NegSobolev.eval y₀ (propagator D ρ 0 t φ) := by
  obtain ⟨-, hlaw⟩ := hY.gaussian_part 1 (fun _ => t) (fun _ => φ) (fun _ => ht) (fun _ => hφ)
  have hM : (Matrix.of fun a b : Fin 1 => 2 * (0 : ℝ) * ∫ r in Set.Icc 0 t, ∫ x,
      inner ℝ (Torus.grad (propagator D ρ r t φ) x)
        (Torus.grad (propagator D ρ r t φ) x) * ρ r x) = 0 := by
    ext a b; simp
  simp only [min_self] at hlaw
  rw [hM, HRS.Det22.det22_mvGaussian_zero] at hlaw
  set G : Ω → EuclideanSpace ℝ (Fin 1) := fun ω => WithLp.toLp 2 fun a =>
      NegSobolev.eval (Y t ω) φ - NegSobolev.eval y₀ (propagator D ρ 0 t φ) with hG
  have hae : AEMeasurable G P := by
    refine (measurable_toLp_eval fun a => ?_).aemeasurable
    exact ((continuous_eval_const hmem).measurable.comp (hY.meas t)).sub measurable_const
  have hm0 : MeasurableSet {x : EuclideanSpace ℝ (Fin 1) | x ≠ 0} :=
    (measurableSet_singleton (0 : EuclideanSpace ℝ (Fin 1))).compl
  have hnull : P {ω | G ω ≠ 0} = 0 := by
    have h1 : (Measure.map G P) {x | x ≠ 0} = 0 := by
      have e : (Measure.map G P) = Measure.dirac 0 := hlaw
      rw [e, Measure.dirac_apply' _ hm0]
      simp
    rw [Measure.map_apply_of_aemeasurable hae hm0] at h1
    exact h1
  have : ∀ᵐ ω ∂P, G ω = 0 := by
    rw [ae_iff]; simpa using hnull
  filter_upwards [this] with ω hω
  have := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) hω
  simp only [hG] at this
  simpa [sub_eq_zero] using this

/-- the limit path `ξ_∞^t = embed_{γ'}(V_∞^{t,0} η°)` -/
def det16d_xi (D : DynData d) (ρ : ℝ → Torus d → ℝ) (γ' : ℝ) (η : NegSobolev d (gammaIdx d : ℝ))
    (t : ℝ) : NegSobolev d γ' :=
  NegSobolev.embed γ' (transportField D ρ t (gammaIdx d : ℝ) η)

/-- fixed time, modes: a.s. `Y^t = ξ_∞^t`. -/
theorem det16d_ae_fixed (hd : 1 ≤ d) {s : ℝ} (Rg : PDE.Regime) (MB Λ VB ν₀ T : ℝ) (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (hA : AdjointData s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {γ' : ℝ} (hγ : (gammaIdx d : ℝ) ≤ γ') (η : NegSobolev d (gammaIdx d : ℝ))
    (Y : ℝ → Ω → NegSobolev d γ')
    (hY : IsLinearFluctuationSolution P D ρ γ' 0 T (fun _ => NegSobolev.embed γ' η) Y)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, Y t ω = det16d_xi D ρ γ' η t := by
  have hall : ∀ᵐ ω ∂P, ∀ k : NonzeroLattice d, NegSobolev.eval (Y t ω) (Torus.realMode k) =
      NegSobolev.eval η (propagator D ρ 0 t (Torus.realMode k)) := by
    rw [ae_all_iff]
    intro k
    filter_upwards [det16d_ae_eval P D ρ γ' T _ Y hY ht (HRS.FieldSingAux.isSmooth_realMode (d := d) k)
      (HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (HRS.FieldSingAux.isSmooth_realMode (d := d) k) γ')]
      with ω hω
    rw [hω, eval_embed hγ]
  filter_upwards [hall] with ω hω
  refine a34_ext fun k => ?_
  have hjp := Torus.jp_pos k.1
  rw [coord_eq_eval, hω k, det16d_xi, a34_coord_embed hγ, NegSobolev.fourierCoeff,
    a34_coord_tf hd Rg MB Λ VB ν₀ T D ρ hA ht η k]
  have h1 : Lattice.jp k.1 ^ (gammaIdx d : ℝ) * Lattice.jp k.1 ^ (-(gammaIdx d : ℝ)) = 1 := by
    rw [← Real.rpow_add hjp]; simp
  rw [← mul_assoc (Lattice.jp k.1 ^ (gammaIdx d : ℝ)), h1, one_mul]

/-- a.s. continuous paths that equal a deterministic function a.s. at each fixed time equal it a.s. at all times
simultaneously, and the function is continuous. -/
theorem det16d_ae_forall_of_dense {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [T2Space E]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : ℝ} (hT : 0 ≤ T) (Y : ℝ → Ω → E) (ξ : ℝ → E)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T))
    (hfix : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, Y t ω = ξ t) :
    (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y t ω = ξ t) ∧ ContinuousOn ξ (Set.Icc 0 T) := by
  have : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  set D : ℕ → Set.Icc (0 : ℝ) T := TopologicalSpace.denseSeq _ with hDdef
  have hD : DenseRange D := TopologicalSpace.denseRange_denseSeq _
  have hG : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T) ∧ ∀ n, Y (D n) ω = ξ (D n) := by
    filter_upwards [hc, (ae_all_iff.2 fun n => hfix (D n) (D n).2)] with ω h1 h2 using ⟨h1, h2⟩
  obtain ⟨ω0, h0c, h0f⟩ := hG.exists
  have hcs : ∀ ω, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T) →
      Continuous fun t : Set.Icc (0 : ℝ) T => Y t ω := fun ω h => continuousOn_iff_continuous_domRestrict.1 h
  have key : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y t ω = Y t ω0 := by
    filter_upwards [hG] with ω ⟨h1, h2⟩ t ht
    have := hD.equalizer (hcs ω h1) (hcs ω0 h0c) (funext fun n => (h2 n).trans (h0f n).symm)
    exact congrFun this ⟨t, ht⟩
  have hξ : ∀ t ∈ Set.Icc (0 : ℝ) T, ξ t = Y t ω0 := by
    intro t ht
    obtain ⟨ω1, h1, h2⟩ := ((hfix t ht).and (key.mono fun ω h => h t ht)).exists
    exact h1.symm.trans h2
  refine ⟨?_, h0c.congr fun t ht => hξ t ht⟩
  filter_upwards [key] with ω h t ht
  rw [h t ht, hξ t ht]

/-- **L10** (identification of the limit).  If `Y'` solves the linearized equation at noise level `0`
with deterministic datum `embed_{γ+2} η°` (limit coefficients `L`), then a.s. `Y'^t = embed_{γ+2}(V_∞^{t,0} η°)`
for all `t ∈ [0,T]` simultaneously, and `t ↦ embed_{γ+2}(V_∞^{t,0} η°)` is continuous on `[0,T]`. -/
theorem det16d_limit_ident (s : ℝ) (Rg : PDE.Regime) (ν₀ MB Λ T VB : ℝ) (S : MainData d)
    (hs : S.s = s) (hT : S.T = T) (L : LimitCoeffs d)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d))
    (η : NegSobolev d (gammaIdx d : ℝ))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y' : ℝ → Ω' → NegSobolev d ((gammaIdx d + 2 : ℕ) : ℝ))
    (hY : IsLinearFluctuationSolution P' (L.dyn S) L.ρ ((gammaIdx d + 2 : ℕ) : ℝ) 0 T
      (fun _ => NegSobolev.embed ((gammaIdx d + 2 : ℕ) : ℝ) η) Y') :
    (∀ᵐ ω ∂P', ∀ t ∈ Set.Icc (0 : ℝ) T,
        Y' t ω = det16d_xi (L.dyn S) L.ρ ((gammaIdx d + 2 : ℕ) : ℝ) η t) ∧
      ContinuousOn (det16d_xi (L.dyn S) L.ρ ((gammaIdx d + 2 : ℕ) : ℝ) η) (Set.Icc 0 T) := by
  subst hs hT
  have hd := S.hd
  have hmonoL : AdjointData S.s (gammaIdx d) Rg MB Λ VB (L.dyn S) ν₀ S.T L.ρ :=
    HRS.PDE.StabAux.adjointData_mono (by omega) hcoef.limit_adjoint
  have hγ : (gammaIdx d : ℝ) ≤ ((gammaIdx d + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right _ 2
  refine det16d_ae_forall_of_dense P' S.hT.le Y' _ hY.cont fun t ht => ?_
  exact det16d_ae_fixed (by omega) Rg MB Λ VB ν₀ S.T (L.dyn S) L.ρ hmonoL P' hγ η Y' hY ht

/-- the limit path as an element of `𝒳_{γ',T}`, given its continuity -/
def det16d_xiPath (D : DynData d) (ρ : ℝ → Torus d → ℝ) (γ' T : ℝ) (η : NegSobolev d (gammaIdx d : ℝ))
    (hcont : Continuous fun t : Set.Icc (0 : ℝ) T => det16d_xi D ρ γ' η t) : PathSpace d γ' T :=
  ⟨fun t => det16d_xi D ρ γ' η t, hcont⟩

/-- **L10, law form.**  `law P' (toPath Y') = δ_{ξ_∞}` for the continuous path `ξ_∞^t = embed_{γ+2}(V_∞^{t,0} η°)`. -/
theorem det16d_limit_law (s : ℝ) (Rg : PDE.Regime) (ν₀ MB Λ T VB : ℝ) (S : MainData d)
    (hs : S.s = s) (hT : S.T = T) (L : LimitCoeffs d)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d))
    (η : NegSobolev d (gammaIdx d : ℝ))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y' : ℝ → Ω' → NegSobolev d ((gammaIdx d + 2 : ℕ) : ℝ))
    (hY : IsLinearFluctuationSolution P' (L.dyn S) L.ρ ((gammaIdx d + 2 : ℕ) : ℝ) 0 T
      (fun _ => NegSobolev.embed ((gammaIdx d + 2 : ℕ) : ℝ) η) Y') :
    ∃ hcont : Continuous fun t : Set.Icc (0 : ℝ) T =>
        det16d_xi (L.dyn S) L.ρ ((gammaIdx d + 2 : ℕ) : ℝ) η t,
      law P' (toPath ((gammaIdx d + 2 : ℕ) : ℝ) T Y') =
        Measure.dirac (det16d_xiPath (L.dyn S) L.ρ ((gammaIdx d + 2 : ℕ) : ℝ) T η hcont) := by
  obtain ⟨hae, hco⟩ := det16d_limit_ident s Rg ν₀ MB Λ T VB S hs hT L hcoef η P' Y' hY
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) T =>
      det16d_xi (L.dyn S) L.ρ ((gammaIdx d + 2 : ℕ) : ℝ) η t :=
    continuousOn_iff_continuous_domRestrict.1 hco
  refine ⟨hcont, ?_⟩
  have hpath : toPath ((gammaIdx d + 2 : ℕ) : ℝ) T Y' =ᵐ[P']
      fun _ => det16d_xiPath (L.dyn S) L.ρ ((gammaIdx d + 2 : ℕ) : ℝ) T η hcont := by
    filter_upwards [hae] with ω hω
    have hc : Continuous fun t : Set.Icc (0 : ℝ) T => Y' t ω := by
      have : (fun t : Set.Icc (0 : ℝ) T => Y' t ω) =
          fun t : Set.Icc (0 : ℝ) T => det16d_xi (L.dyn S) L.ρ ((gammaIdx d + 2 : ℕ) : ℝ) η t :=
        funext fun t => hω t t.2
      rw [this]; exact hcont
    unfold toPath
    simp only [hc, ↓reduceDIte]
    refine ContinuousMap.ext fun t => ?_
    exact hω t t.2
  show Measure.map _ P' = _
  rw [Measure.map_congr hpath, Measure.map_const]
  simp

end HRS.Main.Det16
