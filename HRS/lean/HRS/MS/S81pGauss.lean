import HRS.MS.S81w2Cov
import HRS.MS.ShiftFldAux29
import HRS.MS.GenPathAux47

/-!
# S8.1 (worker S81P), item (a): identification of a sum of independent Gaussian blocks with the stationary Gaussian field

Namespace `HRS.Whole.S81P`, prefix `s81p_`.

* `s81p_gaussian_add`: if `A, B` are independent centered Gaussian vectors with positive semidefinite covariances `S₁, S₂`, then `A + B`
  is centered Gaussian with covariance `S₁ + S₂` (characteristic functions; the positive semidefiniteness is an explicit hypothesis, since
  `multivariateGaussian 0 S` is `dirac 0` for non-PSD `S`).
* `s81p_gaussian_add3`: the same for three jointly independent vectors.
* `s81p_triple_fdd`: three jointly independent `B_m`-valued processes with Gaussian finite-dimensional laws whose covariance matrices add up
  to the profile `Q` have a sum with Gaussian finite-dimensional laws of covariance `Q`.
* `s81p_window_law_of_profile`: a measurable a.s.-continuous process whose finite-dimensional laws are centered Gaussian with the
  covariance profile `Q_{αα'}(|t-t'|)` of the stationary Gaussian field (`s81w2_Q`) has, on `[0,T]`, the path law of EVERY frozen
  `IsStationaryGaussianField` realization (`s56_path_law_eq` and `s81w2_cov_stationary`).
* `s81p_telescope`: the exact initial/old/recent covariance telescope.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
open HRS HRS.Whole HRS.MS.GenPath HRS.Whole.S81W2

namespace HRS.Whole.S81P

section Vectors

variable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}

theorem s81p_gaussian_add (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Ω → EuclideanSpace ℝ (Fin k)) (hA : AEMeasurable A P) (hB : AEMeasurable B P)
    (hind : IndepFun A B P) {S₁ S₂ : Matrix (Fin k) (Fin k) ℝ} (hS₁ : S₁.PosSemidef)
    (hS₂ : S₂.PosSemidef) (h₁ : P.map A = multivariateGaussian 0 S₁)
    (h₂ : P.map B = multivariateGaussian 0 S₂) :
    P.map (fun z => A z + B z) = multivariateGaussian 0 (S₁ + S₂) := by
  have hS : (S₁ + S₂).PosSemidef := hS₁.add hS₂
  refine Measure.ext_of_charFun ?_
  have h := hind.charFun_map_fun_add_eq_mul hA hB
  rw [h, h₁, h₂]
  funext x
  simp only [Pi.mul_apply]
  rw [charFun_multivariateGaussian hS₁, charFun_multivariateGaussian hS₂,
    charFun_multivariateGaussian hS, ← Complex.exp_add]
  congr 1
  simp only [Matrix.add_mulVec, dotProduct_add, inner_zero_right, Complex.ofReal_zero, zero_mul,
    Complex.ofReal_add]
  ring

theorem s81p_gaussian_add3 (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Fin 3 → Ω → EuclideanSpace ℝ (Fin k)) (hV : ∀ i, AEMeasurable (V i) P)
    (hind : iIndepFun V P) (S : Fin 3 → Matrix (Fin k) (Fin k) ℝ) (hS : ∀ i, (S i).PosSemidef)
    (hlaw : ∀ i, P.map (V i) = multivariateGaussian 0 (S i)) :
    P.map (fun z => V 0 z + V 1 z + V 2 z) = multivariateGaussian 0 (S 0 + S 1 + S 2) := by
  have h01 := s81p_gaussian_add P (V 0) (V 1) (hV 0) (hV 1)
    (hind.indepFun (by decide : (0 : Fin 3) ≠ 1)) (hS 0) (hS 1) (hlaw 0) (hlaw 1)
  have hsum : IndepFun (∑ j ∈ ({0, 1} : Finset (Fin 3)), V j) (V 2) P :=
    hind.indepFun_finsetSum_of_notMem₀ hV (by decide : (2 : Fin 3) ∉ ({0, 1} : Finset (Fin 3)))
  have e : (∑ j ∈ ({0, 1} : Finset (Fin 3)), V j) = fun z => V 0 z + V 1 z := by
    funext z
    simp [Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1)]
  rw [e] at hsum
  exact s81p_gaussian_add P (fun z => V 0 z + V 1 z) (V 2) ((hV 0).add (hV 1)) (hV 2) hsum
    ((hS 0).add (hS 1)) (hS 2) h01 (hlaw 2)

end Vectors

section Process

variable {d : ℕ} {m : ℝ} {Ω : Type*} [MeasurableSpace Ω]

/-- The coordinate vector of a `B_m`-valued process at finitely many times and multi-indices. -/
def s81p_vec {p : ℕ} (Y : ℝ → Ω → OscDual d m) (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d)
    (ζ : Ω) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 fun a => OscDual.coord (Y (ts a) ζ) (αs a)

theorem s81p_vec_meas {p : ℕ} {Y : ℝ → Ω → OscDual d m} (hY : ∀ t, Measurable (Y t))
    (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d) : Measurable (s81p_vec Y ts αs) := by
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun a => ?_)
  exact (s56_continuous_coord m (αs a)).measurable.comp (hY _)

/-- Three jointly independent processes with Gaussian finite-dimensional laws whose covariances add up to `Qp` have a sum with the
Gaussian finite-dimensional laws of covariance `Qp`. -/
theorem s81p_triple_fdd (P : Measure Ω) [IsProbabilityMeasure P] {T : ℝ}
    (G : Fin 3 → ℝ → Ω → OscDual d m) (hGm : ∀ i t, Measurable (G i t))
    (hind : iIndepFun (fun (i : Fin 3) (ζ : Ω) (t : ℝ) => G i t ζ) P)
    (S : Fin 3 → ∀ (p : ℕ), (Fin p → ℝ) → (Fin p → MultiIndex d) → Matrix (Fin p) (Fin p) ℝ)
    (Qp : ∀ (p : ℕ), (Fin p → ℝ) → (Fin p → MultiIndex d) → Matrix (Fin p) (Fin p) ℝ)
    (hpsd : ∀ i p ts αs, (∀ a, ts a ∈ Icc (0 : ℝ) T) → (S i p ts αs).PosSemidef)
    (hlaw : ∀ i p ts αs, (∀ a, ts a ∈ Icc (0 : ℝ) T) →
      P.map (s81p_vec (G i) ts αs) = multivariateGaussian 0 (S i p ts αs))
    (hsum : ∀ p ts αs, (∀ a, ts a ∈ Icc (0 : ℝ) T) → S 0 p ts αs + S 1 p ts αs + S 2 p ts αs = Qp p ts αs)
    {p : ℕ} (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d) (hts : ∀ a, ts a ∈ Icc (0 : ℝ) T) :
    P.map (s81p_vec (fun t ζ => G 0 t ζ + G 1 t ζ + G 2 t ζ) ts αs) =
      multivariateGaussian 0 (Qp p ts αs) := by
  have hmeas : ∀ i, Measurable (s81p_vec (G i) ts αs) := fun i => s81p_vec_meas (hGm i) ts αs
  have hΨ : Measurable (fun (f : ℝ → OscDual d m) => (WithLp.toLp 2 fun a => OscDual.coord (f (ts a)) (αs a) :
      EuclideanSpace ℝ (Fin p))) :=
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun a =>
      (s56_continuous_coord m (αs a)).measurable.comp (measurable_pi_apply (ts a)))
  have hind' : iIndepFun (fun i => s81p_vec (G i) ts αs) P :=
    hind.comp (fun _ f => (WithLp.toLp 2 fun a => OscDual.coord (f (ts a)) (αs a) :
      EuclideanSpace ℝ (Fin p))) (fun _ => hΨ)
  have e : s81p_vec (fun t ζ => G 0 t ζ + G 1 t ζ + G 2 t ζ) ts αs =
      fun ζ => s81p_vec (G 0) ts αs ζ + s81p_vec (G 1) ts αs ζ + s81p_vec (G 2) ts αs ζ := by
    funext ζ
    ext a
    simp [s81p_vec, OscDual.coord_add]
  rw [e, ← hsum p ts αs hts]
  exact s81p_gaussian_add3 P (fun i => s81p_vec (G i) ts αs) (fun i => (hmeas i).aemeasurable) hind'
    (fun i => S i p ts αs) (fun i => hpsd i p ts αs hts) (fun i => hlaw i p ts αs hts)

end Process

section Identify

variable {d : ℕ} {a β : ℝ} {ρ : Euc d → ℝ} {e : ℕ → Euc d → ℝ} {om : ℕ → ℝ} {m : ℝ}

/-- The covariance matrix of the stationary Gaussian field at times `ts` and multi-indices `αs`. -/
def s81p_Qmat (d : ℕ) (β : ℝ) (ρ : Euc d → ℝ) (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ) (m : ℝ) {p : ℕ}
    (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun a c => s81w2_Q d β ρ e om m (αs a) (αs c) |ts a - ts c|

/-- **Identification with every frozen stationary Gaussian field.**  A measurable, a.s. continuous (on `[0,T]`) `B_m`-valued process
whose finite-dimensional laws on `[0,T]` are centered Gaussian with covariance matrices `s81p_Qmat` has the window law of every
`IsStationaryGaussianField` realization. -/
theorem s81p_window_law_of_profile (hd : 2 ≤ d) (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) (hm : (wholeSpaceIndex d : ℝ) ≤ m)
    (hdata : IsSpectralData d β ρ e om) (hcoef : S81W2Coef d a β ρ e om m) {T : ℝ} (hT : 0 < T)
    {Ω : Type*} {Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] (Z : ℝ → Ω' → OscDual d m)
    (hZ : IsStationaryGaussianField d ((d : ℝ) / 2) a β m ρ P' Z)
    (Y : ℝ → Ω → OscDual d m) (hYm : ∀ t, Measurable (Y t))
    (hYc : ∀ᵐ ζ ∂P, ContinuousOn (fun t => Y t ζ) (Icc 0 T))
    (hY : ∀ (p : ℕ) (ts : Fin p → ℝ) (αs : Fin p → MultiIndex d), (∀ a, ts a ∈ Icc (0 : ℝ) T) →
      P.map (s81p_vec Y ts αs) = multivariateGaussian 0 (s81p_Qmat d β ρ e om m ts αs)) :
    law P (processWindow m T 0 Y) = law P' (processWindow m T 0 Z) := by
  classical
  have hZT := hZ T
  haveI : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT.le⟩⟩
  set sq : ℕ → Icc (0 : ℝ) T := TopologicalSpace.denseSeq (Icc (0 : ℝ) T) with hsq
  have hdense : DenseRange sq := TopologicalSpace.denseRange_denseSeq _
  have hmΨ : Measurable (fun ζ (i : ℕ × MultiIndex d) => OscDual.coord (Y (sq i.1) ζ) i.2) :=
    measurable_pi_iff.2 fun i => (s56_continuous_coord m i.2).measurable.comp (hYm _)
  have hmΨ' : Measurable (fun ζ (i : ℕ × MultiIndex d) => OscDual.coord (Z (sq i.1) ζ) i.2) :=
    measurable_pi_iff.2 fun i => (s56_continuous_coord m i.2).measurable.comp (hZT.meas _)
  have hlaw : P.map (fun ζ (i : ℕ × MultiIndex d) => OscDual.coord (Y (sq i.1) ζ) i.2) =
      P'.map (fun ζ (i : ℕ × MultiIndex d) => OscDual.coord (Z (sq i.1) ζ) i.2) := by
    refine s56_seq_law_eq P P' _ _ hmΨ.aemeasurable hmΨ'.aemeasurable fun p f _ => ?_
    have hts : ∀ c, ((sq (f c).1 : Icc (0 : ℝ) T) : ℝ) ∈ Icc (0 : ℝ) T := fun c => (sq (f c).1).2
    have e1 := hY p (fun c => ((sq (f c).1 : Icc (0 : ℝ) T) : ℝ)) (fun c => (f c).2) hts
    have e2 := HRS.MS.S79G.s79g_fdd P' hZT (fun c => ((sq (f c).1 : Icc (0 : ℝ) T) : ℝ)) hts
      (fun c => (f c).2)
    refine e1.trans (Eq.trans ?_ e2.symm)
    congr 1
    ext c c'
    simp only [s81p_Qmat, Matrix.of_apply]
    exact (s81w2_cov_stationary hd ha hβ hρ hm hdata hcoef (f c).2 (f c').2
      (sq (f c).1).2.1 (sq (f c').1).2.1).symm
  exact s56_path_law_eq hT.le P P' Y Z hYm hZT.meas hYc hZT.cont sq hdense hlaw

end Identify

/-- The exact initial/old/recent covariance telescope (the three block covariances add up to the stationary profile). -/
theorem s81p_telescope (Q : ℝ → ℝ) (h b t t' : ℝ) :
    Q (2 * (h + b) + t + t') + (Q (2 * b + t + t') - Q (2 * (h + b) + t + t')) +
      (Q |t - t'| - Q (2 * b + t + t')) = Q |t - t'| := by
  ring

end HRS.Whole.S81P
