import HRS.Sections.QuenchAux4

/-!
# Packet QUENCH (Q27), part 5: independence of the mode processes

The processes `t ↦ Z^t(ψ_k)`, `t ↦ Z^t(χ_k)` (all `k ∈ ℤ^d_+`) form a Gaussian process (sum of the
noise vector and the linear image of the Gaussian initial datum, independent), and distinct ones are
uncorrelated; hence they are independent (Mathlib `IsGaussianProcess.iIndepFun_of_covariance_eq_zero`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

open HRS.Sec7

variable {d : ℕ}

section Indep

variable {s β β₀ m : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Z : ℝ → Ω → NegSobolev d m} {Y : Ω → NegSobolev d m}

/-- The real coordinate process of the mode `ψ_k` / `χ_k`. -/
def Xmode (Z : ℝ → Ω → NegSobolev d m) (kb : PosHalf d × Bool) (t : ℝ≥0) (ω : Ω) : ℝ :=
  NegSobolev.eval (Z t ω) (modeFn kb.1.1 kb.2)

lemma Xmode_eq (Z : ℝ → Ω → NegSobolev d m) (kb : PosHalf d × Bool) (t : ℝ≥0) (ω : Ω) :
    Xmode Z kb t ω = sgn kb.2 * NegSobolev.fourierCoeff (Z t ω) (idx kb.1 kb.2) := by
  unfold Xmode
  rw [modeFn_eq, eval_mode]

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)

include hd hs0 hsd hβ in
theorem isGaussianProcess_Xmode (mf : ModeField d s β β₀ m P Z Y) :
    IsGaussianProcess (fun (p : (_ : PosHalf d × Bool) × ℝ≥0) ω => Xmode Z p.1 p.2 ω) P := by
  classical
  refine ⟨fun I => ?_⟩
  set n := I.card with hn
  let ι : I ≃ Fin n := I.equivFin
  -- the noise vector
  let js : Fin n → NonzeroLattice d := fun a => idx (ι.symm a).1.1.1 (ι.symm a).1.1.2
  let ts : Fin n → ℝ := fun a => ((ι.symm a).1.2 : ℝ)
  have hts : ∀ a, 0 ≤ ts a := fun a => (ι.symm a).1.2.2
  obtain ⟨hindep, hlaw⟩ := mf.gp n js ts hts
  haveI : IsGaussian (Measure.map (fun ω => (WithLp.toLp 2 (fun a => ncoord s β Y Z (js a) (ts a) ω) :
      EuclideanSpace ℝ (Fin n))) P) := by rw [hlaw]; infer_instance
  have hH := IsGaussian.hasGaussianLaw (aemeas_Gvec mf js ts)
  -- the linear maps
  let K : EuclideanSpace ℝ (Fin n) →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi fun p => sgn p.1.1.2 • (EuclideanSpace.proj (ι p) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
  let L : NegSobolev d m →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi fun p => (sgn p.1.1.2 * Real.exp (-(lamMode d s β (idx p.1.1.1 p.1.1.2).1) *
      ((p.1.2 : ℝ≥0) : ℝ))) • HRS.FieldSingAux.coordCLM m (idx p.1.1.1 p.1.1.2)
  have hY : HasGaussianLaw Y P := by
    haveI : IsGaussian (P.map Y) := mf.cenY.1
    exact IsGaussian.hasGaussianLaw mf.measY
  have hA : HasGaussianLaw (K ∘ fun ω => (WithLp.toLp 2 (fun a => ncoord s β Y Z (js a) (ts a) ω) :
      EuclideanSpace ℝ (Fin n))) P := hH.map K
  have hB : HasGaussianLaw (L ∘ Y) P := hY.map L
  have hind : IndepFun (K ∘ fun ω => (WithLp.toLp 2 (fun a => ncoord s β Y Z (js a) (ts a) ω) :
      EuclideanSpace ℝ (Fin n))) (L ∘ Y) P :=
    hindep.comp K.continuous.measurable L.continuous.measurable
  have hsum := iIndepFun.hasGaussianLaw_add hA hB hind
  refine hsum.congr (Eventually.of_forall fun ω => ?_)
  funext p
  simp only [Pi.add_apply, Function.comp_apply, K, L, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.smul_apply, HRS.FieldSingAux.coordCLM_apply, smul_eq_mul]
  rw [Finset.restrict_def]
  have hproj : ∀ (i : Fin n) (f : Fin n → ℝ),
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (WithLp.toLp 2 f) = f i :=
    fun i f => rfl
  simp only [Xmode_eq, ι, js, ts, ncoord, hproj, Equiv.symm_apply_apply]
  ring

lemma idx_injective {p q : PosHalf d × Bool} (h : idx p.1 p.2 = idx q.1 q.2) : p = q :=
  (equiv d).injective h

include hd hs0 hsd hβ in
lemma mean_fcZ (mf : ModeField d s β β₀ m P Z Y) (j : NonzeroLattice d) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, NegSobolev.fourierCoeff (Z t ω) j ∂P = 0 := by
  have e : (fun ω => NegSobolev.fourierCoeff (Z t ω) j) = fun ω => ncoord s β Y Z j t ω +
      Real.exp (-(lamMode d s β j.1) * t) * NegSobolev.fourierCoeff (Y ω) j := by
    funext ω; simp only [ncoord]; ring
  rw [e, integral_add ((memLp2_ncoord hd hs0 hsd hβ mf j ht).integrable one_le_two)
    (((memLp2_fcY mf j).integrable one_le_two).const_mul _), integral_const_mul,
    noise_mean hd hs0 hsd hβ mf j ht, mean_fcY mf j]
  simp

include hd hs0 hsd hβ in
lemma memLp2_fcZ (mf : ModeField d s β β₀ m P Z Y) (j : NonzeroLattice d) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (fun ω => NegSobolev.fourierCoeff (Z t ω) j) 2 P := by
  have e : (fun ω => NegSobolev.fourierCoeff (Z t ω) j) = fun ω => ncoord s β Y Z j t ω +
      Real.exp (-(lamMode d s β j.1) * t) * NegSobolev.fourierCoeff (Y ω) j := by
    funext ω; simp only [ncoord]; ring
  rw [e]
  exact (memLp2_ncoord hd hs0 hsd hβ mf j ht).add ((memLp2_fcY mf j).const_mul _)

include hd hs0 hsd hβ in
theorem indep_modes (mf : ModeField d s β β₀ m P Z Y) :
    iIndepFun (fun (kb : PosHalf d × Bool) ω => fun t : ℝ≥0 => Xmode Z kb t ω) P := by
  refine IsGaussianProcess.iIndepFun_of_covariance_eq_zero (S := fun _ => ℝ≥0)
    (X := fun kb t => Xmode Z kb t) (isGaussianProcess_Xmode hd hs0 hsd hβ mf) ?_ ?_
  · intro kb t
    have : Xmode Z kb t = fun ω => sgn kb.2 * NegSobolev.fourierCoeff (Z t ω) (idx kb.1 kb.2) := by
      funext ω; exact Xmode_eq Z kb t ω
    rw [this]
    exact ((meas_fcZ mf _ _).const_mul _).aemeasurable
  · intro kb₁ kb₂ hne t r
    have hne' : idx kb₁.1 kb₁.2 ≠ idx kb₂.1 kb₂.2 := fun h => hne (idx_injective h)
    have h1 : MemLp (Xmode Z kb₁ t) 2 P := by
      have : Xmode Z kb₁ t = fun ω => sgn kb₁.2 * NegSobolev.fourierCoeff (Z t ω) (idx kb₁.1 kb₁.2) := by
        funext ω; exact Xmode_eq Z kb₁ t ω
      rw [this]; exact (memLp2_fcZ hd hs0 hsd hβ mf _ (NNReal.coe_nonneg t)).const_mul _
    have h2 : MemLp (Xmode Z kb₂ r) 2 P := by
      have : Xmode Z kb₂ r = fun ω => sgn kb₂.2 * NegSobolev.fourierCoeff (Z r ω) (idx kb₂.1 kb₂.2) := by
        funext ω; exact Xmode_eq Z kb₂ r ω
      rw [this]; exact (memLp2_fcZ hd hs0 hsd hβ mf _ (NNReal.coe_nonneg r)).const_mul _
    rw [covariance_eq_sub h1 h2]
    have m1 : ∫ ω, Xmode Z kb₁ t ω ∂P = 0 := by
      simp only [Xmode_eq]
      rw [integral_const_mul, mean_fcZ hd hs0 hsd hβ mf _ (NNReal.coe_nonneg t), mul_zero]
    have p1 : ∫ ω, Xmode Z kb₁ t ω * Xmode Z kb₂ r ω ∂P = 0 := by
      simp only [Xmode_eq]
      have : ∀ ω, sgn kb₁.2 * NegSobolev.fourierCoeff (Z t ω) (idx kb₁.1 kb₁.2) *
          (sgn kb₂.2 * NegSobolev.fourierCoeff (Z r ω) (idx kb₂.1 kb₂.2)) =
          (sgn kb₁.2 * sgn kb₂.2) * (NegSobolev.fourierCoeff (Z t ω) (idx kb₁.1 kb₁.2) *
            NegSobolev.fourierCoeff (Z r ω) (idx kb₂.1 kb₂.2)) := fun ω => by ring
      simp_rw [this]
      rw [integral_const_mul, Z_cov hd hs0 hsd hβ mf _ _ (NNReal.coe_nonneg t) (NNReal.coe_nonneg r), if_neg hne', mul_zero]
    simp only [Pi.mul_apply]
    rw [p1, m1]
    simp

end Indep

end Qch

end HRS
