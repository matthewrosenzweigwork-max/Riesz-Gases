import HRS.Uniform.Q54cAux11
import HRS.Uniform.Q54cAux1

/-!
# Q54c, part 12: initial value, measurability, and the Gaussian part of `Ŷ`
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.Uniform.Q54c

open HRS HRS.Uniform.Q07c HRS.HilbertCLTAux HRS.Uniform.Q48b

variable {d : ℕ} {a : ℝ}

section Init

variable {P : PathData d a} {T K : ℝ} (hP : P.Spec T K) {G : ℝ → NegSobolev d a}

include hP

theorem Yelt_coord {M : ℝ} (hG : ContinuousOn G (Set.Icc 0 T)) (hM : ∀ σ ∈ Set.Icc 0 T, ‖G σ‖ ≤ M)
    (A : ℝ) (η : NegSobolev d (a + 2)) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (k : NonzeroLattice d) :
    NegSobolev.coord (P.Yelt A η G t) k =
      Lattice.jp k.1 ^ (-(a + 4)) * P.lam A η G t (Torus.realMode k) :=
  rieszElt_coord (lam_rieszHyp hP hG hM A η ht) k

theorem Ypath_zero (hG : ContinuousOn G (Set.Icc 0 T)) (hG0 : G 0 = 0) (A : ℝ)
    (η : NegSobolev d (a + 2)) :
    P.Ypath T A η G 0 = A • NegSobolev.embed (a + 4) η := by
  have hT := hP.hT
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hG
  have h0 : max 0 (min (0 : ℝ) T) = 0 := by simp [hT]
  have h0m : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  refine Subtype.ext (funext fun k => ?_)
  show NegSobolev.coord (P.Ypath T A η G 0) k = NegSobolev.coord (A • NegSobolev.embed (a + 4) η) k
  unfold PathData.Ypath
  rw [h0, Yelt_coord hP hG hM A η h0m k]
  have hl : P.lam A η G 0 (Torus.realMode k) = A * NegSobolev.fourierCoeff η k := by
    unfold PathData.lam PathData.noiseF PathData.initF
    rw [hP.w_zero _ (q48b_isSmooth_realMode k), hG0, eval_realMode]
    simp
  rw [hl]
  have : NegSobolev.coord (A • NegSobolev.embed (a + 4) η) k =
      A * NegSobolev.coord (NegSobolev.embed (a + 4) η) k := rfl
  rw [this, coord_embed (by linarith) η k]
  ring

end Init


section Proc

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℝ mΩ}
variable {PD : PathData d a} {T K : ℝ}
variable {G : ℝ → Ω → NegSobolev d a} {C : ℝ → NegSobolev d a →L[ℝ] NegSobolev d a →L[ℝ] ℝ}

/-- the process `Ŷ_t(ω)` (time clamped) -/
def PathData.Yproc (PD : PathData d a) (T A : ℝ) (η : Ω → NegSobolev d (a + 2))
    (G : ℝ → Ω → NegSobolev d a) (t : ℝ) (ω : Ω) : NegSobolev d (a + 4) :=
  PD.Ypath T A (η ω) (fun σ => G σ ω) t

theorem noiseF_tendsto (hP : PD.Spec T K) {g : ℝ → NegSobolev d a} (hg : ContinuousOn g (Set.Icc 0 T))
    (hg0 : g 0 = 0) {t : ℝ} (ht : t ∈ Set.Icc 0 T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Tendsto (fun N => isum g (PD.y t φ) T t N) atTop (𝓝 (PD.noiseF g t φ)) :=
  isum_tendsto hP.hT ht hg hg0 (hP.deriv t ht φ hφ) (hP.cont_y' t ht φ hφ)

theorem noiseF_measurable' (hP : PD.Spec T K) {m : MeasurableSpace Ω}
    (hGm : ∀ τ ∈ Set.Icc 0 T, Measurable[m] (G τ)) (hGc : ∀ ω, Continuous fun s => G s ω)
    (hGz : ∀ ω, G 0 ω = 0) {t : ℝ} (ht : t ∈ Set.Icc 0 T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Measurable[m] (fun ω => PD.noiseF (fun σ => G σ ω) t φ) := by
  letI : MeasurableSpace Ω := m
  refine measurable_of_tendsto_metrizable (fun N => measurable_isum' hGm hP.hT ht (PD.y t φ) N)
    (tendsto_pi_nhds.2 fun ω => ?_)
  exact noiseF_tendsto hP ((hGc ω).continuousOn) (hGz ω) ht hφ

theorem lam_eq (hP : PD.Spec T K) (hG : ∀ ω, ContinuousOn (fun s => G s ω) (Set.Icc 0 T))
    (A : ℝ) (η : Ω → NegSobolev d (a + 2)) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (ω : Ω) :
    NegSobolev.eval (PD.Yproc T A η G t ω) φ =
      PD.noiseF (fun σ => G σ ω) t φ + A * PD.initF (η ω) t φ := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn (hG ω)
  unfold PathData.Yproc PathData.Ypath
  rw [clamp01_of_mem ht]
  exact Yelt_eval hP (hG ω) hM A (η ω) ht hφ

theorem Yproc_coord (hP : PD.Spec T K) (hG : ∀ ω, ContinuousOn (fun s => G s ω) (Set.Icc 0 T))
    (A : ℝ) (η : Ω → NegSobolev d (a + 2)) (t : ℝ) (k : NonzeroLattice d) (ω : Ω) :
    NegSobolev.coord (PD.Yproc T A η G t ω) k =
      Lattice.jp k.1 ^ (-(a + 4)) * (PD.noiseF (fun σ => G σ ω) (max 0 (min t T)) (Torus.realMode k) +
        A * PD.initF (η ω) (max 0 (min t T)) (Torus.realMode k)) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn (hG ω)
  unfold PathData.Yproc PathData.Ypath
  exact Yelt_coord hP (hG ω) hM A (η ω) (clamp01_mem hP.hT t) k

theorem Yproc_measurable (hP : PD.Spec T K) (hGm : ∀ τ, Measurable (G τ))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0) (A : ℝ)
    {η : Ω → NegSobolev d (a + 2)} (hη : Measurable η) (t : ℝ) :
    Measurable (PD.Yproc T A η G t) := by
  refine measurable_of_coord fun k => ?_
  have hc : ∀ ω, ContinuousOn (fun s => G s ω) (Set.Icc 0 T) := fun ω => (hGc ω).continuousOn
  simp_rw [Yproc_coord hP hc]
  refine Measurable.const_mul ?_ _
  refine Measurable.add ?_ ?_
  · exact noiseF_measurable' hP (fun τ _ => hGm τ) hGc hGz (clamp01_mem hP.hT t)
      (q48b_isSmooth_realMode k)
  · refine Measurable.const_mul ?_ _
    unfold PathData.initF
    exact hη.inner_const

/-- the Gaussian part vector of `Ŷ`: `Ŷ_{t_i}(φ_i) - A ⟨η, U^{0,t_i}φ_i⟩` -/
def procVec (PD : PathData d a) (T A : ℝ) (η : Ω → NegSobolev d (a + 2)) (G : ℝ → Ω → NegSobolev d a)
    (Uf : ℝ → (Torus d → ℝ) → Torus d → ℝ) {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ)
    (ω : Ω) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 fun i => NegSobolev.eval (PD.Yproc T A η G (ts i) ω) (φ i) -
    NegSobolev.eval (A • NegSobolev.embed (a + 4) (η ω)) (Uf (ts i) (φ i))

theorem procVec_eq (hP : PD.Spec T K) (hGc : ∀ ω, Continuous fun s => G s ω)
    (A : ℝ) (η : Ω → NegSobolev d (a + 2)) (Uf : ℝ → (Torus d → ℝ) → Torus d → ℝ)
    (hw : ∀ t ∈ Set.Icc 0 T, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ z : NegSobolev d (a + 2),
      inner ℝ z (PD.w t φ) = NegSobolev.eval z (Uf t φ))
    {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ i, ts i ∈ Set.Icc 0 T) (φ : Fin p → Torus d → ℝ)
    (hφ : ∀ i, Torus.IsSmooth (φ i)) (ω : Ω) :
    procVec PD T A η G Uf ts φ ω =
      noiseVec G ts (fun i => PD.y (ts i) (φ i)) (fun i => PD.y' (ts i) (φ i)) ω := by
  have hc : ∀ ω, ContinuousOn (fun s => G s ω) (Set.Icc 0 T) := fun ω => (hGc ω).continuousOn
  unfold procVec noiseVec
  congr 1
  funext i
  rw [lam_eq hP hc A η (hts i) (hφ i) ω, eval_smul, eval_embed (by linarith), ← hw (ts i) (hts i) (φ i) (hφ i)]
  unfold PathData.initF PathData.noiseF
  ring

theorem Yproc_gaussian_part (hP : PD.Spec T K)
    (hG : IsHilbertMartingaleWithCovariation μ ℱ T G (fun r _ => C r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0) (hT : 0 < T) (A : ℝ)
    {η : Ω → NegSobolev d (a + 2)} (hη : Measurable η)
    (hind : Indep (MeasurableSpace.comap η inferInstance)
      (⨆ τ ∈ {τ : ℝ | 0 ≤ τ ∧ τ ≤ T}, MeasurableSpace.comap (G τ) inferInstance) μ)
    (Uf : ℝ → (Torus d → ℝ) → Torus d → ℝ)
    (hw : ∀ t ∈ Set.Icc 0 T, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ z : NegSobolev d (a + 2),
      inner ℝ z (PD.w t φ) = NegSobolev.eval z (Uf t φ))
    {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ i, ts i ∈ Set.Icc 0 T) (φ : Fin p → Torus d → ℝ)
    (hφ : ∀ i, Torus.IsSmooth (φ i)) :
    IndepFun (procVec PD T A η G Uf ts φ) (fun ω => A • NegSobolev.embed (a + 4) (η ω)) μ ∧
      μ.map (procVec PD T A η G Uf ts φ) =
        multivariateGaussian 0 (Matrix.of fun i j =>
          ∫ σ in Set.Icc 0 (min (ts i) (ts j)), C σ (PD.y (ts i) (φ i) σ) (PD.y (ts j) (φ j) σ)) := by
  have hvec : procVec PD T A η G Uf ts φ =
      noiseVec G ts (fun i => PD.y (ts i) (φ i)) (fun i => PD.y' (ts i) (φ i)) :=
    funext fun ω => procVec_eq hP hGc A η Uf hw ts hts φ hφ ω
  constructor
  · -- independence
    set Minf : MeasurableSpace Ω :=
      ⨆ τ ∈ {τ : ℝ | 0 ≤ τ ∧ τ ≤ T}, MeasurableSpace.comap (G τ) inferInstance with hMinf
    have hGm : ∀ τ ∈ Set.Icc 0 T, Measurable[Minf] (G τ) := fun τ hτ =>
      Measurable.of_comap_le (le_iSup₂_of_le τ (show τ ∈ {τ : ℝ | 0 ≤ τ ∧ τ ≤ T} from hτ) le_rfl)
    have hXm : Measurable[Minf] (procVec PD T A η G Uf ts φ) := by
      rw [hvec]
      letI : MeasurableSpace Ω := Minf
      refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp ?_
      refine measurable_pi_iff.2 fun i => ?_
      exact noiseF_measurable' hP hGm hGc hGz (hts i) (hφ i)
    have hY : Measurable (fun z : NegSobolev d (a + 2) => A • NegSobolev.embed (a + 4) z) := by
      refine measurable_of_coord fun k => ?_
      have : (fun z : NegSobolev d (a + 2) => NegSobolev.coord (A • NegSobolev.embed (a + 4) z) k) =
          fun z => A * (Lattice.jp k.1 ^ (-(a + 4)) *
            (Lattice.jp k.1 ^ (a + 2) * NegSobolev.coord z k)) := by
        funext z
        have e1 : NegSobolev.coord (A • NegSobolev.embed (a + 4) z) k =
            A * NegSobolev.coord (NegSobolev.embed (a + 4) z) k := rfl
        rw [e1, coord_embed (by linarith) z k]
        rfl
      rw [this]
      exact (((continuous_coord (a + 2) k).measurable.const_mul _).const_mul _).const_mul _
    have hcomap : MeasurableSpace.comap (fun ω => A • NegSobolev.embed (a + 4) (η ω)) inferInstance ≤
        MeasurableSpace.comap η inferInstance := by
      have : (fun ω => A • NegSobolev.embed (a + 4) (η ω)) =
          (fun z : NegSobolev d (a + 2) => A • NegSobolev.embed (a + 4) z) ∘ η := rfl
      rw [this, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hY.comap_le
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind.symm hXm.comap_le) hcomap
  · rw [hvec]
    exact noise_gaussian hG hGc hGz hT ts hts _ _ (fun i => hP.deriv _ (hts i) _ (hφ i))
      (fun i => hP.cont_y' _ (hts i) _ (hφ i))

end Proc


end HRS.Uniform.Q54c
