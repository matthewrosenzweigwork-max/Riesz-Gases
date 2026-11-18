import HRS.MC.Q714GW
import HRS.MC.S7UCU

/-!
# Packet e213q, GS-3a: path-level Gaussianity of a window from finite-dimensional Gaussianity

`gaussian_window_of_fdd`: let `Z : ℝ → Ω → E_m` have measurable time slices and a.s. continuous paths on `[0,a+T]`, and suppose that
for every finite family of times in `[0,a+T]` and every finite set of Fourier modes the vector of Fourier coordinates is a centred
Gaussian vector (`FddGaussian`).  Then the window `procWin m T a Z` is a.e. measurable into `𝒳_{m,T}` and its law is a centred
Gaussian measure.  This is the proof of `HRS.MC.Q714.GW.gaussian_window_proof` with the homogeneous input `gw_comb_gaussian`
replaced by `FddGaussian` (and with continuity only on `[0,a+T]`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213Q

open HRS HRS.Sec7 HRS.Qch HRS.MC.Q714.GW

variable {d : ℕ}

/-- Finite-dimensional Gaussianity of the Fourier coordinates at times in `I`: for every finite family of times `τ_i ∈ I` and every
finite set `J` of modes, `(Ẑ^{τ_i}(j))_{i, j ∈ J}` is a Gaussian vector with mean zero. -/
def FddGaussian {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {m : ℝ} (Z : ℝ → Ω → NegSobolev d m)
    (I : Set ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (τ : ι → ℝ), (∀ i, τ i ∈ I) → ∀ J : Finset (NonzeroLattice d),
    HasGaussianLaw (fun ω (p : ι × J) => NegSobolev.fourierCoeff (Z (τ p.1) ω) p.2) P ∧
    ∀ p : ι × J, ∫ ω, NegSobolev.fourierCoeff (Z (τ p.1) ω) p.2 ∂P = 0

section Aux

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {m : ℝ} {Z : ℝ → Ω → NegSobolev d m}

/-- Finite combinations of Fourier coordinates are centred Gaussian. -/
theorem e213q_comb_gaussian {I : Set ℝ} (h : FddGaussian P Z I) {ι : Type} [Fintype ι] (τ : ι → ℝ)
    (hτ : ∀ i, τ i ∈ I) (c : ι → NonzeroLattice d → ℝ) (S : Finset (NonzeroLattice d)) :
    HasGaussianLaw (fun ω => ∑ k, ∑ j ∈ S, c k j * NegSobolev.fourierCoeff (Z (τ k) ω) j) P ∧
    ∫ ω, ∑ k, ∑ j ∈ S, c k j * NegSobolev.fourierCoeff (Z (τ k) ω) j ∂P = 0 := by
  classical
  obtain ⟨hG, h0⟩ := h ι τ hτ S
  have e : (fun ω => ∑ k, ∑ j ∈ S, c k j * NegSobolev.fourierCoeff (Z (τ k) ω) j) =
      fun ω => (∑ p : ι × S, c p.1 p.2.1 • (ContinuousLinearMap.proj p :
          (ι × S → ℝ) →L[ℝ] ℝ))
        (fun p : ι × S => NegSobolev.fourierCoeff (Z (τ p.1) ω) p.2) := by
    funext ω
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (Finset.sum_coe_sort S (fun j => c k j * NegSobolev.fourierCoeff (Z (τ k) ω) j)).symm
  rw [e]
  refine ⟨hG.map_fun _, ?_⟩
  have hint : ∀ p : ι × S, Integrable (fun ω => NegSobolev.fourierCoeff (Z (τ p.1) ω) p.2) P :=
    fun p => (hG.eval p).integrable
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [integral_finsetSum _ (fun p _ => (hint p).const_mul _)]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [integral_const_mul, h0 p, mul_zero]

/-- A continuous linear functional of finitely many time slices is a centred real Gaussian. -/
theorem e213q_lin_gaussian [IsProbabilityMeasure P] {I : Set ℝ} (h : FddGaussian P Z I) {ι : Type} [Fintype ι]
    (τ : ι → ℝ) (hτ : ∀ i, τ i ∈ I) (L : ι → StrongDual ℝ (NegSobolev d m)) (W : Ω → ℝ)
    (hW : AEMeasurable W P) (hWeq : ∀ᵐ ω ∂P, W ω = ∑ k, L k (Z (τ k) ω)) :
    ∃ v : ℝ≥0, P.map W = gaussianReal 0 v := by
  classical
  obtain ⟨S, hS⟩ := (Filter.atTop : Filter (Finset (NonzeroLattice d))).exists_seq_tendsto
  set c : ι → NonzeroLattice d → ℝ := fun k j => L k (gwE m j) * (Lattice.jp j.1 ^ m)⁻¹ with hc
  set U : ℕ → Ω → ℝ := fun N ω => ∑ k, ∑ j ∈ S N, c k j * NegSobolev.fourierCoeff (Z (τ k) ω) j with hU
  have hG : ∀ N, HasGaussianLaw (U N) P ∧ ∫ ω, U N ω ∂P = 0 :=
    fun N => e213q_comb_gaussian h τ hτ c (S N)
  have hmap : ∀ N, P.map (U N) = gaussianReal 0 (Var[U N; P]).toNNReal := by
    intro N
    rw [(hG N).1.map_eq_gaussianReal]
    congr 2
    exact (hG N).2
  refine gw_gauss_limit P hmap ?_ hW (fun N => (hG N).1.aemeasurable)
  filter_upwards [hWeq] with ω hω
  rw [hω]
  refine tendsto_finsetSum _ fun k _ => ?_
  have h1 := (gw_dual_hasSum (L k) (Z (τ k) ω))
  have h2 : Tendsto (fun N => ∑ j ∈ S N, NegSobolev.coord (Z (τ k) ω) j * L k (gwE m j)) atTop
      (𝓝 (L k (Z (τ k) ω))) := h1.comp hS
  refine h2.congr fun N => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have hp : Lattice.jp j.1 ^ m ≠ 0 := (Real.rpow_pos_of_pos (Torus.jp_pos _) _).ne'
  simp only [hc, NegSobolev.fourierCoeff]
  field_simp

/-- On a trajectory continuous on `[0,a+T]` the window path is the honest path. -/
theorem e213q_procWin_at (T a : ℝ) (ha : 0 ≤ a) (ω : Ω)
    (hc : ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T))) (t : Set.Icc (0 : ℝ) T) :
    (procWin m T a Z ω).at' t = Z (a + t) ω := by
  classical
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) T => Z (a + (t : ℝ)) ω := by
    refine hc.comp_continuous (by fun_prop) (fun t => ?_)
    exact ⟨add_nonneg ha t.2.1, by linarith [t.2.2]⟩
  have h : procWin m T a Z ω = (⟨fun t : Set.Icc (0 : ℝ) T => Z (a + (t : ℝ)) ω, hcont⟩ :
      C(Set.Icc (0 : ℝ) T, NegSobolev d m)) := by
    unfold procWin toPath
    exact dif_pos hcont
  rw [h]
  rfl

end Aux

/-- Linear functionals of the window are centred Gaussian. -/
theorem e213q_functional_gaussian {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m : ℝ} (T : ℝ) (hT : 0 < T) (Z : ℝ → Ω → NegSobolev d m) (a : ℝ) (ha : 0 ≤ a)
    (hmeas : AEMeasurable (procWin m T a Z) P)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T)))
    (hfdd : FddGaussian P Z (Set.Icc 0 (a + T))) (ℓ : StrongDual ℝ (PathSpace d m T)) :
    ∃ v : ℝ≥0, P.map (fun ω => ℓ (procWin m T a Z ω)) = gaussianReal 0 v := by
  have hVn : ∀ n : ℕ, ∃ v : ℝ≥0,
      P.map (fun ω => ℓ (bInterp hT n (procWin m T a Z ω))) = gaussianReal 0 v := by
    intro n
    refine e213q_lin_gaussian hfdd (fun k : Fin (n + 1) => a + (bnode hT n k : ℝ))
      (fun k => ⟨add_nonneg ha (bnode hT n k).2.1, by linarith [(bnode hT n k).2.2]⟩)
      (fun k => ℓ.comp (bemb hT n k)) _ ?_ ?_
    · exact (ℓ.continuous.comp (gw_bInterp_continuous hT n)).measurable.comp_aemeasurable hmeas
    · filter_upwards [hcont] with ω hω
      have hbi : ℓ (bInterp hT n (procWin m T a Z ω)) =
          ∑ k : Fin (n + 1), ℓ (bemb hT n k ((procWin m T a Z ω).at' (bnode hT n k))) := by
        unfold bInterp
        rw [map_sum]
      rw [hbi]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [e213q_procWin_at T a ha ω hω]
      simp only [ContinuousLinearMap.comp_apply]
  choose v hv using hVn
  have hWm : AEMeasurable (fun ω => ℓ (procWin m T a Z ω)) P :=
    ℓ.continuous.measurable.comp_aemeasurable hmeas
  refine gw_gauss_limit P hv ?_ hWm (fun n =>
    (ℓ.continuous.comp (gw_bInterp_continuous hT n)).measurable.comp_aemeasurable hmeas)
  exact Eventually.of_forall fun ω =>
    (ℓ.continuous.tendsto _).comp (bInterp_tendsto hT (procWin m T a Z ω))

/-- **GS-3a.**  Path-level Gaussianity of the window from finite-dimensional Gaussianity of the Fourier coordinates. -/
theorem gaussian_window_of_fdd {m : ℝ} (T : ℝ) (hT : 0 < T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Ω → NegSobolev d m) (a : ℝ) (ha : 0 ≤ a)
    (hmeas : ∀ t, Measurable (Z t))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T)))
    (hfdd : ∀ (ι : Type) [Fintype ι] (τ : ι → ℝ), (∀ i, τ i ∈ Set.Icc 0 (a + T)) →
      ∀ J : Finset (NonzeroLattice d),
        HasGaussianLaw (fun ω (p : ι × J) => NegSobolev.fourierCoeff (Z (τ p.1) ω) p.2) P ∧
        ∀ p : ι × J, ∫ ω, NegSobolev.fourierCoeff (Z (τ p.1) ω) p.2 ∂P = 0) :
    AEMeasurable (procWin m T a Z) P ∧ IsCenteredGaussian (law P (procWin m T a Z)) := by
  have hmeasW : AEMeasurable (procWin m T a Z) P :=
    HRS.MC.Sec7.S7UCU.S7UCU_procWin_aemeasurable P m T hT Z a ha hmeas hcont
  refine ⟨hmeasW, ?_⟩
  have key := e213q_functional_gaussian P T hT Z a ha hmeasW hcont hfdd
  have hmap : ∀ L : StrongDual ℝ (PathSpace d m T), (law P (procWin m T a Z)).map L =
      P.map (fun ω => L (procWin m T a Z ω)) := fun L =>
    AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hmeasW
  refine ⟨isGaussian_of_map_eq_gaussianReal fun L => ?_, fun L => ?_⟩
  · obtain ⟨v, hv⟩ := key L
    exact ⟨0, v, (hmap L).trans hv⟩
  · obtain ⟨v, hv⟩ := key L
    have h1 : ∫ z, L z ∂(law P (procWin m T a Z)) = ∫ x, x ∂((law P (procWin m T a Z)).map L) := by
      rw [integral_map L.continuous.measurable.aemeasurable
        (by exact aestronglyMeasurable_id)]
    rw [h1, hmap L, hv, integral_id_gaussianReal]

end HRS.MC.E213Q
