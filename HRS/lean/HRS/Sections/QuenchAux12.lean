import HRS.Sections.QuenchAux11

/-!
# Packet QUENCH (Q27), part 12: one mode of the field is an OU process driven by a Brownian motion

`ModeField` ⟹ `OUNoise` for `Y = Z^0(e_j)`, `G = ncoord j`; the Brownian motion `B_j`, its independence of
`Z^0(e_j)`, and the integrated OU equation.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

open HRS.Sec7

variable {d : ℕ}

section ModeOU

variable {s β β₀ m : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Z : ℝ → Ω → NegSobolev d m} {Y : Ω → NegSobolev d m}

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)

include hd hs0 hsd hβ in
theorem ouNoise_of_modeField (mf : ModeField d s β β₀ m P Z Y) (j : NonzeroLattice d) :
    OUNoise (lamMode d s β j.1) (varMode d s β j.1) (varMode d s β₀ j.1) P
      (fun ω => NegSobolev.fourierCoeff (Y ω) j) (fun t ω => ncoord s β Y Z j t ω) := by
  classical
  refine ⟨?_, mean_fcY mf j, fun t => noise_mean hd hs0 hsd hβ mf j (NNReal.coe_nonneg t), ?_, fun t => ?_,
    fun t r => ?_, ?_, ?_⟩
  · -- the Gaussian process over `Option ℝ≥0`
    refine ⟨fun I => ?_⟩
    set n := I.card with hn
    let ι : I ≃ Fin n := I.equivFin
    let js : Fin n → NonzeroLattice d := fun _ => j
    let ts : Fin n → ℝ := fun a => optTime (ι.symm a).1
    have hts : ∀ a, 0 ≤ ts a := by
      intro a
      show 0 ≤ optTime (ι.symm a).1
      rcases hp : (ι.symm a).1 with _ | t
      · exact le_rfl
      · exact NNReal.coe_nonneg t
    obtain ⟨hindep, hlaw⟩ := mf.gp n js ts hts
    haveI : IsGaussian (Measure.map (fun ω => (WithLp.toLp 2 (fun a => ncoord s β Y Z (js a) (ts a) ω) :
        EuclideanSpace ℝ (Fin n))) P) := by rw [hlaw]; infer_instance
    have hH := IsGaussian.hasGaussianLaw (aemeas_Gvec mf js ts)
    let K : EuclideanSpace ℝ (Fin n) →L[ℝ] (I → ℝ) :=
      ContinuousLinearMap.pi fun p => optCoef 1 p.1 • (EuclideanSpace.proj (ι p) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    let L : NegSobolev d m →L[ℝ] (I → ℝ) :=
      ContinuousLinearMap.pi fun p => (if p.1 = none then (1 : ℝ) else 0) • HRS.FieldSingAux.coordCLM m j
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
    have hproj : ∀ (i : Fin n) (f : Fin n → ℝ),
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (WithLp.toLp 2 f) = f i :=
      fun i f => rfl
    simp only [Pi.add_apply, Function.comp_apply, K, L, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.smul_apply, HRS.FieldSingAux.coordCLM_apply, smul_eq_mul, hproj]
    rw [Finset.restrict_def]
    rcases hp : p.1 with _ | t
    · simp only [hp, optCoef, if_true, zero_mul, zero_add, one_mul]
      rfl
    · simp only [hp, optCoef, reduceCtorEq, if_false, zero_mul, add_zero, one_mul, ι, js, ts]
      rw [Equiv.symm_apply_apply, hp]
      rfl
  · simpa using mf.covY j j
  · -- Y * G = 0
    have hmY := memLp2_fcY mf j
    have hmG := memLp2_ncoord hd hs0 hsd hβ mf j (NNReal.coe_nonneg t)
    have := (indep_ncoord_fcY hd hs0 hsd hβ mf j j (NNReal.coe_nonneg t)).integral_mul_eq_mul_integral
      hmG.aestronglyMeasurable hmY.aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    have h2 : ∫ ω, NegSobolev.fourierCoeff (Y ω) j * ncoord s β Y Z j t ω ∂P = 0 := by
      simp_rw [mul_comm (NegSobolev.fourierCoeff (Y _) j)]
      rw [this, mean_fcY mf j, mul_zero]
    exact h2
  · simpa using noise_cov hd hs0 hsd hβ mf j j (NNReal.coe_nonneg t) (NNReal.coe_nonneg r)
  · filter_upwards [mf.cont] with ω hc
    have hIci : ContinuousOn (fun t => Z t ω) (Set.Ici 0) := by
      intro x hx
      have hmem : Set.Icc (0 : ℝ) (x + 1) ∈ 𝓝[Set.Ici (0 : ℝ)] x := by
        have : Set.Iio (x + 1) ∈ 𝓝 x := Iio_mem_nhds (by linarith)
        refine mem_nhdsWithin.2 ⟨Set.Iio (x + 1), isOpen_Iio, by simp, ?_⟩
        intro y hy
        exact ⟨hy.2, le_of_lt hy.1⟩
      exact (hc (x + 1) x ⟨hx, by linarith⟩).mono_of_mem_nhdsWithin hmem
    have hcomp : Continuous fun u : ℝ => Z (max u 0) ω :=
      hIci.comp_continuous (continuous_id.max continuous_const) (fun u => (Set.mem_Ici.2 (le_max_right u 0)))
    have h1 : Continuous fun u : ℝ => NegSobolev.fourierCoeff (Z (max u 0) ω) j :=
      (HRS.FieldSingAux.coordCLM m j).continuous.comp hcomp
    have h2 : Continuous fun u : ℝ => Real.exp (-(lamMode d s β j.1) * max u 0) :=
      Real.continuous_exp.comp (continuous_const.mul (continuous_id.max continuous_const))
    exact h1.sub (h2.mul continuous_const)
  · filter_upwards [mf.init] with ω h
    simp [ncoord, h]

end ModeOU

end Qch

end HRS
