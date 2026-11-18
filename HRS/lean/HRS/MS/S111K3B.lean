import HRS.MS.CovMeasTie
import HRS.MS.GenPathAux10
import HRS.MS.OrbIdTie

/-!
# S11.1 continuation (S11K3), B03 part B: the abstract covariance measure at horizon `2T` and the shifted reconstruction

The shifted reconstruction `𝒯' : C([0,2T];𝒦_T) → C([0,T];ℓ²)`,
`(𝒯' w)(t) = A_{2T}(t) - B_{2T} + B_{T+t}` (norm `≤ 3 + √T`, independent of any forcing horizon), the properties
`K3Jprops` of the abstract covariance measure `HRS.Uniform.covariance_measure_proof` for the identity evolution on `𝒦_T` at
horizon `2T` (constant `C0` depending only on `T`), the localization `J(1_I D) = J(D)(I ∩ ·)` (by `obs_separate`), the
per-interval bound `‖𝒥_D(I)‖ ≤ C0 ∫_{I∩[0,2T]} ‖D‖₁`, and the value of the push-forward on two observations.
-/

set_option autoImplicit false
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S111K3

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.GenPath HRS.MS.U9 HRS.MS.CovMeas HRS.MS.S52

variable {d : ℕ} {m T : ℝ}

abbrev K3Bil (d : ℕ) (m T : ℝ) : Type := KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ

/-- The terminal point `2T` of `[0,2T]`. -/
def k3pt (hT : 0 ≤ T) : Icc (0 : ℝ) (2 * T) := ⟨2 * T, by linarith, le_rfl⟩

/-- The shifted observation point `T + t`. -/
def k3sh (hT : 0 ≤ T) (t : Icc (0 : ℝ) T) : Icc (0 : ℝ) (2 * T) :=
  ⟨T + t, by linarith [t.2.1], by linarith [t.2.2]⟩

lemma k3sh_continuous (hT : 0 ≤ T) : Continuous (k3sh hT) :=
  Continuous.subtype_mk (continuous_const.add continuous_subtype_val) _

/-- The shifted reconstruction as a continuous map. -/
def k3reconFun (hT : 0 ≤ T) (w : PathSp (2 * T) (KSpace d m T)) : C(Icc (0 : ℝ) T, OscDual d m) :=
  ⟨fun t => (pcm w (k3pt hT)).evalA t - (pcm w (k3pt hT)).B + (pcm w (k3sh hT t)).B, by
    have h1 : Continuous fun t : Icc (0 : ℝ) T => (pcm w (k3pt hT)).evalA t :=
      continuousOn_iff_continuous_restrict.1 (u9_continuousOn_evalA hT _)
    exact (h1.sub continuous_const).add (u9_continuous_B.comp ((pcm w).continuous.comp (k3sh_continuous hT)))⟩

lemma k3reconFun_apply (hT : 0 ≤ T) (w : PathSp (2 * T) (KSpace d m T)) (t : Icc (0 : ℝ) T) :
    k3reconFun hT w t = (pcm w (k3pt hT)).evalA t - (pcm w (k3pt hT)).B + (pcm w (k3sh hT t)).B := rfl

def k3reconLin (hT : 0 ≤ T) : PathSp (2 * T) (KSpace d m T) →ₗ[ℝ] OscPath d m T where
  toFun w := k3reconFun hT w
  map_add' w w' := by
    refine ContinuousMap.ext fun t => ?_
    show k3reconFun hT (w + w') t = k3reconFun hT w t + k3reconFun hT w' t
    rw [k3reconFun_apply, k3reconFun_apply, k3reconFun_apply, pcm_add, pcm_add,
      s56_evalA_add, s56_B_add, s56_B_add]
    abel
  map_smul' c w := by
    refine ContinuousMap.ext fun t => ?_
    show k3reconFun hT (c • w) t = c • k3reconFun hT w t
    rw [k3reconFun_apply, k3reconFun_apply, pcm_smul, pcm_smul, s56_evalA_smul,
      s56_B_smul, s56_B_smul]
    simp only [smul_sub, smul_add, RingHom.id_apply]

/-- `𝒯'` as a bounded linear map, `‖𝒯'‖ ≤ 3 + √T`. -/
def k3reconCLM (hT : 0 ≤ T) : PathSp (2 * T) (KSpace d m T) →L[ℝ] OscPath d m T :=
  (k3reconLin hT).mkContinuous (3 + Real.sqrt T) fun w => by
    have hs : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun t => ?_
    show ‖k3reconFun hT w t‖ ≤ (3 + Real.sqrt T) * ‖w‖
    rw [k3reconFun_apply]
    refine (u9_recon_norm_le hT _ _ _).trans ?_
    have h1 := norm_pcm_apply_le w (k3pt hT)
    have h2 := norm_pcm_apply_le w (k3sh hT t)
    have h3 : (2 + Real.sqrt T) * ‖pcm w (k3pt hT)‖ ≤ (2 + Real.sqrt T) * ‖w‖ :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith

lemma k3reconCLM_apply (hT : 0 ≤ T) (w : PathSp (2 * T) (KSpace d m T)) (t : Icc (0 : ℝ) T) :
    (show C(Icc (0 : ℝ) T, OscDual d m) from k3reconCLM hT w) t =
      (pcm w (k3pt hT)).evalA t - (pcm w (k3pt hT)).B + (pcm w (k3sh hT t)).B := rfl

lemma k3reconCLM_norm_le (hT : 0 ≤ T) :
    ‖(k3reconCLM hT : PathSp (2 * T) (KSpace d m T) →L[ℝ] OscPath d m T)‖ ≤ 3 + Real.sqrt T :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- Coordinates of the shifted reconstruction. -/
theorem k3_recon_coord (hT : 0 ≤ T) (w : PathSp (2 * T) (KSpace d m T)) (t : Icc (0 : ℝ) T)
    (α : MultiIndex d) :
    OscDual.coord (OscPath.at' (k3reconCLM hT w : OscPath d m T) t) α =
      inner ℝ (pcm w (k3pt hT)) (s52y1 m T t α) - inner ℝ (pcm w (k3pt hT)) (s52y2 m T α) +
        inner ℝ (pcm w (k3sh hT t)) (s52y2 m T α) := by
  have e : OscPath.at' (k3reconCLM hT w : OscPath d m T) t =
      (pcm w (k3pt hT)).evalA t - (pcm w (k3pt hT)).B + (pcm w (k3sh hT t)).B := rfl
  rw [e, s52_coord_add, s52_coord_sub, s52_coord_evalA t.2.1 t.2.2, s52_coord_B, s52_coord_B]

/-! ### The push-forward -/

/-- The push-forward of an element of `𝒴 ⊗̂ 𝒴` (`𝒴 = C([0,2T];𝒦)`) to `OscPath`. -/
def k3Psi (hT : 0 ≤ T) (τ : ProjTensor2 (PathSp (2 * T) (KSpace d m T))) : TensorDual (OscPath d m T) 2 :=
  s101Bri (tensorMap (k3reconCLM hT) τ)

lemma k3Psi_add (hT : 0 ≤ T) (τ τ' : ProjTensor2 (PathSp (2 * T) (KSpace d m T))) :
    k3Psi hT (τ + τ') = k3Psi hT τ + k3Psi hT τ' := by
  unfold k3Psi; rw [map_add, s101Bri_add]

lemma k3Psi_smul (hT : 0 ≤ T) (a : ℝ) (τ : ProjTensor2 (PathSp (2 * T) (KSpace d m T))) :
    k3Psi hT (a • τ) = a • k3Psi hT τ := by
  unfold k3Psi; rw [map_smul, s101Bri_smul]

lemma k3Psi_zero (hT : 0 ≤ T) : k3Psi hT (0 : ProjTensor2 (PathSp (2 * T) (KSpace d m T))) = 0 := by
  have := k3Psi_smul (d := d) (m := m) hT 0 0
  simpa using this

lemma k3Psi_sub (hT : 0 ≤ T) (τ τ' : ProjTensor2 (PathSp (2 * T) (KSpace d m T))) :
    k3Psi hT (τ - τ') = k3Psi hT τ - k3Psi hT τ' := by
  unfold k3Psi; rw [map_sub, s101Bri_sub]

lemma norm_k3Psi_le (hT : 0 ≤ T) (τ : ProjTensor2 (PathSp (2 * T) (KSpace d m T))) :
    ‖k3Psi hT τ‖ ≤ ‖(k3reconCLM hT : PathSp (2 * T) (KSpace d m T) →L[ℝ] OscPath d m T)‖ ^ 2 * ‖τ‖ :=
  (norm_s101Bri_le _).trans (norm_tensorMap_le _ _)

lemma k3Psi_mem (hT : 0 ≤ T) (τ : ProjTensor2 (PathSp (2 * T) (KSpace d m T))) :
    k3Psi hT τ ∈ projTensor (OscPath d m T) 2 := s101Bri_mem _

lemma lipschitz_k3Psi (hT : 0 ≤ T) :
    LipschitzWith (⟨‖(k3reconCLM hT : PathSp (2 * T) (KSpace d m T) →L[ℝ] OscPath d m T)‖ ^ 2, by positivity⟩ : ℝ≥0)
      (k3Psi (d := d) (m := m) hT) := by
  refine LipschitzWith.of_dist_le_mul fun τ τ' => ?_
  rw [dist_eq_norm, dist_eq_norm, ← k3Psi_sub]
  exact norm_k3Psi_le hT _

/-! ### Properties of the abstract covariance measure at horizon `2T` -/

/-- The clauses of `covariance_measure_proof` for the identity evolution on `𝒦_T` at horizon `2T`. -/
structure K3Jprops (T C0 : ℝ)
    (J : (ℝ → K3Bil d m T) → VectorMeasure ℝ (ProjTensor2 (PathSp (2 * T) (KSpace d m T)))) : Prop where
  supp : ∀ D, IsTraceDensityL1 (2 * T) D → ∀ I, MeasurableSet I → J D I = J D (I ∩ Icc 0 (2 * T))
  tv : ∀ D, IsTraceDensityL1 (2 * T) D →
    (J D).variation (Icc 0 (2 * T)) ≤
      ENNReal.ofReal C0 * ∫⁻ r in Icc (0 : ℝ) (2 * T), ENNReal.ofReal (traceNormForm (D r))
  obs : ∀ D, IsTraceDensityL1 (2 * T) D → ∀ (t₁ t₂ : Icc (0 : ℝ) (2 * T)) (ℓ₁ ℓ₂ : KSpace d m T →L[ℝ] ℝ)
    (I : Set ℝ), MeasurableSet I → tensorPairing (obsForm t₁ t₂ ℓ₁ ℓ₂) (J D I) =
      ∫ r in I ∩ Icc 0 (min (t₁ : ℝ) t₂), D r (pullbackVec (s56_idEvol (KSpace d m T)) t₁ r ℓ₁)
        (pullbackVec (s56_idEvol (KSpace d m T)) t₂ r ℓ₂)
  cont : ∀ D, IsTraceDensityL1 (2 * T) D → ContinuousOn (fun t => J D (Icc 0 t)) (Icc 0 (2 * T))
  lin : ∀ D D', IsTraceDensityL1 (2 * T) D → IsTraceDensityL1 (2 * T) D' → ∀ a b : ℝ, ∀ I, MeasurableSet I →
    J (fun r => a • D r + b • D' r) I = a • J D I + b • J D' I

theorem k3_J_exists (hT : 0 < T) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∃ J : (ℝ → K3Bil d m T) → VectorMeasure ℝ (ProjTensor2 (PathSp (2 * T) (KSpace d m T))),
      K3Jprops T C0 J := by
  have hT2 : 0 ≤ 2 * T := by linarith
  obtain ⟨C0, hC0, hCm⟩ := HRS.Uniform.covariance_measure_proof (2 * T) 1 hT2
  obtain ⟨J, hJ1, hJ2⟩ := hCm (KSpace d m T) (KSpace d m T) (s56_idEvol (KSpace d m T)) (s56_idEvol_maxHyp (2 * T))
  exact ⟨C0, hC0, J, ⟨fun D hD => (hJ1 D hD).1, fun D hD => (hJ1 D hD).2.2.1, fun D hD => (hJ1 D hD).2.2.2.1,
    fun D hD => (hJ1 D hD).2.2.2.2, hJ2⟩⟩

end HRS.MS.S111K3
