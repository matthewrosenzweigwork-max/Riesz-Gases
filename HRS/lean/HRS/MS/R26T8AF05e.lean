import HRS.MS.R26T8AF05d
import HRS.MS.R26T8AF05b
import HRS.MS.R26T8AF01a

/-!
# S8.2 observed-time layer, packet T8A.F05: nonlocal J and Euler-J bounds at the displayed finite index

`r26t8a_oneJ_sobolev`: for thermal `ρ` and `SobSmooth f`, `J f = oneJ(critCoeff) f` is `SobSmooth`,
`‖J f‖_{H^r} ≤ C ‖f‖_{H^{r+1}}` and `‖E J f‖_{H^r} ≤ C ‖f‖_{H^{r+2}}`, with `C` independent of `f`.
Route: `J f = ∑_j T_j(h_j)` with `h_j = ρ ∂_j f` Schwartz (F05d), F02b for each `T_j`, F03 for the Euler commutator.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux
open HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_f05e_mulR {x y : ℝ≥0∞} (h : x ≤ y) (a : ℝ≥0∞) : x * a ≤ y * a := by
  gcongr

theorem r26t8a_f05e_sob_scale (c : ℝ) (r : ℝ) (u : Euc d → ℝ) :
    sobolevNormE r (fun x => c * u x) ≤ ENNReal.ofReal |c| * sobolevNormE r u := by
  by_cases hc : c = 0
  · subst hc
    have e : (fun x : Euc d => (0 : ℝ) * u x) = fun _ : Euc d => (0 : ℝ) := by
      funext x
      simp
    rw [e, r26t8a_f05c_sob_zero]
    simp
  by_cases hu : HRS.PDE.ToolboxRd.MemSobolev r u
  · have hae := fourierL2_smul hu.1 c
    have hint : Integrable (fun ξ : Euc d =>
        (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ r * ‖fourierL2 (fun x => c * u x) ξ‖ ^ 2) := by
      refine ((hu.2).const_mul (c ^ 2)).congr ?_
      filter_upwards [hae] with ξ hξ
      simp only [hξ, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      ring
    have hcu : HRS.PDE.ToolboxRd.MemSobolev r (fun x => c * u x) := ⟨hu.1.const_mul c, hint⟩
    have hsq : sobolevNormSq r (fun x => c * u x) = c ^ 2 * sobolevNormSq r u := by
      unfold sobolevNormSq
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hae] with ξ hξ
      simp only [hξ, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      ring
    unfold sobolevNormE
    rw [if_pos hcu, if_pos hu]
    exact le_of_eq (by rw [hsq, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs,
      ENNReal.ofReal_mul (abs_nonneg c)])
  · have hu' : sobolevNormE r u = ⊤ := by
      unfold sobolevNormE
      rw [if_neg hu]
    rw [hu', ENNReal.mul_top (ENNReal.ofReal_pos.2 (abs_pos.2 hc)).ne']
    exact le_top

theorem r26t8a_f05e_euler_sum_fun {ι : Type*} (s : Finset ι) (F : ι → Euc d → ℝ)
    (hF : ∀ i ∈ s, Differentiable ℝ (F i)) :
    r26t8a_Euler (fun x => ∑ i ∈ s, F i x) = fun x => ∑ i ∈ s, r26t8a_Euler (F i) x := by
  funext x
  unfold r26t8a_Euler
  have hfun : (fun y => ∑ i ∈ s, F i y) = ∑ i ∈ s, F i := by
    funext y
    simp [Finset.sum_apply]
  rw [hfun, fderiv_sum (fun i hi => hF i hi x), ContinuousLinearMap.sum_apply]

theorem r26t8a_oneJ_sobolev (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, r26t8a_SobSmooth f →
      r26t8a_SobSmooth (oneJ (critCoeff d a beta rho) f) ∧
      sobolevNormE (r : ℝ) (oneJ (critCoeff d a beta rho) f) ≤
        ENNReal.ofReal C * sobolevNormE ((r + 1 : ℕ) : ℝ) f ∧
      sobolevNormE (r : ℝ) (r26t8a_Euler (oneJ (critCoeff d a beta rho) f)) ≤
        ENNReal.ofReal C * sobolevNormE ((r + 2 : ℕ) : ℝ) f := by
  classical
  obtain ⟨σ, hσ, -⟩ := r26t8a_thermal_sqrt d hd a beta ha hbeta rho hrho
  have hnn : ∀ x, 0 ≤ rho x := fun x => (hrho.2).1.nonneg x
  have hsq : ∀ x, rho x = σ x * σ x := fun x => by
    rw [hσ x, Real.mul_self_sqrt (hnn x)]
  choose K1 K2 hK1 hK2 hpc using fun j : Fin d => r26t8a_f05d_piece σ rho hsq r j
  obtain ⟨CF, hCF, hFb⟩ := r26t8a_forceConv_sobolev d hd r
  refine ⟨∑ j : Fin d, (CF * K1 j + CF * K2 j + |criticalS d - 1| * (CF * K1 j)), ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => add_nonneg (add_nonneg (mul_nonneg hCF (hK1 j))
      (mul_nonneg hCF (hK2 j))) (mul_nonneg (abs_nonneg _) (mul_nonneg hCF (hK1 j)))
  intro f hf
  have hdata : ∀ j : Fin d, ∃ h G : SchwartzMap (Euc d) ℝ,
      (∀ x, h x = rho x * fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) ∧
      (∀ x, G x = fderiv ℝ (⇑h) x x) ∧
      sobolevNormE (r : ℝ) (⇑h) + eLpNorm (⇑h) 1 volume ≤
        ENNReal.ofReal (K1 j) * sobolevNormE ((r : ℝ) + 1) f ∧
      sobolevNormE (r : ℝ) (⇑G) + eLpNorm (⇑G) 1 volume ≤
        ENNReal.ofReal (K2 j) * sobolevNormE ((r : ℝ) + 2) f :=
    fun j => hpc j f hf
  choose H Gs hkey hG hb1 hb2 using hdata
  have hfun_j : ∀ j : Fin d,
      (fun y => rho y * fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ))) = ⇑(H j) :=
    fun j => funext fun y => (hkey j y).symm
  have honeJ : oneJ (critCoeff d a beta rho) f =
      fun x => ∑ j : Fin d, r26t8a_forceConv j (⇑(H j)) x := by
    funext x
    rw [r26t8a_f05b_oneJ_eq a beta rho f x]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfun_j j]
  have hFdiff : ∀ j : Fin d, Differentiable ℝ (fun x => r26t8a_forceConv j (⇑(H j)) x) :=
    fun j => ((hFb j (H j)).1.1).differentiable (by simp)
  have hSobSum : r26t8a_SobSmooth (fun x => ∑ j : Fin d, r26t8a_forceConv j (⇑(H j)) x) :=
    r26t8a_f05c_sum_sob Finset.univ (fun j x => r26t8a_forceConv j (⇑(H j)) x)
      (fun j _ => (hFb j (H j)).1)
  have hcast1 : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
  have hcast2 : ((r + 2 : ℕ) : ℝ) = (r : ℝ) + 2 := by push_cast; ring
  rw [hcast1, hcast2]
  have hC1 : ∀ j : Fin d, CF * K1 j ≤
      (CF * K1 j + CF * K2 j + |criticalS d - 1| * (CF * K1 j)) := fun j => by
    have h1 := mul_nonneg hCF (hK2 j)
    have h2 := mul_nonneg (abs_nonneg (criticalS d - 1)) (mul_nonneg hCF (hK1 j))
    linarith
  have hC2 : ∀ j : Fin d, CF * K2 j + |criticalS d - 1| * (CF * K1 j) ≤
      (CF * K1 j + CF * K2 j + |criticalS d - 1| * (CF * K1 j)) := fun j => by
    have h1 := mul_nonneg hCF (hK1 j)
    linarith
  have hnnA : ∀ j : Fin d, 0 ≤ CF * K1 j := fun j => mul_nonneg hCF (hK1 j)
  refine ⟨by rw [honeJ]; exact hSobSum, ?_, ?_⟩
  · -- order r bound on J f
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin d)),
        sobolevNormE (r : ℝ) (fun x => r26t8a_forceConv j (⇑(H j)) x) ≤
          ENNReal.ofReal (CF * K1 j) * sobolevNormE ((r : ℝ) + 1) f := fun j _ =>
      r26t8a_f05d_mul_chain CF (K1 j) hCF (hK1 j) _ _ _ (hFb j (H j)).2 (hb1 j)
    rw [honeJ]
    refine le_trans (r26t8a_f05c_sob_sum (r : ℝ) Finset.univ
      (fun j x => r26t8a_forceConv j (⇑(H j)) x)) ?_
    refine le_trans (r26t8a_f05d_sum_comb Finset.univ (fun j => CF * K1 j) hnnA _ _ hterm) ?_
    exact r26t8a_f05e_mulR (ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun j _ => hC1 j)) _
  · -- order r+2 bound on the Euler derivative of J f
    have hE : r26t8a_Euler (fun x => ∑ j : Fin d, r26t8a_forceConv j (⇑(H j)) x) =
        fun x => ∑ j : Fin d, r26t8a_Euler (fun y => r26t8a_forceConv j (⇑(H j)) y) x :=
      r26t8a_f05e_euler_sum_fun Finset.univ (fun j x => r26t8a_forceConv j (⇑(H j)) x)
        (fun j _ => hFdiff j)
    have hEj : ∀ j ∈ (Finset.univ : Finset (Fin d)),
        sobolevNormE (r : ℝ) (fun x => r26t8a_Euler (fun y => r26t8a_forceConv j (⇑(H j)) y) x) ≤
          ENNReal.ofReal (CF * K2 j + |criticalS d - 1| * (CF * K1 j)) *
            sobolevNormE ((r : ℝ) + 2) f := by
      intro j _
      have e := r26t8a_forceConv_euler d hd j (H j)
      have eG : r26t8a_Euler (⇑(H j)) = ⇑(Gs j) := funext fun x => (hG j x).symm
      rw [eG] at e
      have e' : (fun x => r26t8a_Euler (fun y => r26t8a_forceConv j (⇑(H j)) y) x) =
          fun x => r26t8a_forceConv j (⇑(Gs j)) x +
            (criticalS d - 1) * r26t8a_forceConv j (⇑(H j)) x := by
        funext x
        exact congrFun e x
      rw [e']
      have hA : sobolevNormE (r : ℝ) (fun x => r26t8a_forceConv j (⇑(Gs j)) x) ≤
          ENNReal.ofReal (CF * K2 j) * sobolevNormE ((r : ℝ) + 2) f :=
        r26t8a_f05d_mul_chain CF (K2 j) hCF (hK2 j) _ _ _ (hFb j (Gs j)).2 (hb2 j)
      have hBj : sobolevNormE (r : ℝ) (fun x => r26t8a_forceConv j (⇑(H j)) x) ≤
          ENNReal.ofReal (CF * K1 j) * sobolevNormE ((r : ℝ) + 2) f :=
        (r26t8a_f05d_mul_chain CF (K1 j) hCF (hK1 j) _ _ _ (hFb j (H j)).2 (hb1 j)).trans
          (r26t8a_f05d_mulL (r26t8a_f05c_sob_mono (by linarith) f) _)
      have hB : sobolevNormE (r : ℝ) (fun x => (criticalS d - 1) *
          r26t8a_forceConv j (⇑(H j)) x) ≤
          ENNReal.ofReal (|criticalS d - 1| * (CF * K1 j)) * sobolevNormE ((r : ℝ) + 2) f :=
        (r26t8a_f05e_sob_scale _ _ _).trans
          ((r26t8a_f05d_mulL hBj _).trans (le_of_eq (by
            rw [ENNReal.ofReal_mul (abs_nonneg _), mul_assoc])))
      refine le_trans (HRS.MH.AdjointRd.Phase2SA12V3.sa12v3_sobolevNormE_add_le (r : ℝ)
        (fun x => r26t8a_forceConv j (⇑(Gs j)) x)
        (fun x => (criticalS d - 1) * r26t8a_forceConv j (⇑(H j)) x)) ?_
      exact r26t8a_f05d_add_comb _ _ (mul_nonneg hCF (hK2 j))
        (mul_nonneg (abs_nonneg _) (hnnA j)) _ _ _ hA hB
    rw [honeJ, hE]
    refine le_trans (r26t8a_f05c_sob_sum (r : ℝ) Finset.univ
      (fun j x => r26t8a_Euler (fun y => r26t8a_forceConv j (⇑(H j)) y) x)) ?_
    refine le_trans (r26t8a_f05d_sum_comb Finset.univ
      (fun j => CF * K2 j + |criticalS d - 1| * (CF * K1 j))
      (fun j => add_nonneg (mul_nonneg hCF (hK2 j)) (mul_nonneg (abs_nonneg _) (hnnA j)))
      _ _ hEj) ?_
    exact r26t8a_f05e_mulR (ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun j _ => hC2 j)) _

end HRS.MS.R26T8A

end
