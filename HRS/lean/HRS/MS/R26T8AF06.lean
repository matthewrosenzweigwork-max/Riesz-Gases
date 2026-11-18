import HRS.MS.R26T8AF00
import HRS.MS.R26T8AF01b
import HRS.MS.MovBridgeAux7
import HRS.MS.MovLinAux9
import HRS.MS.UlOrbitAux1

/-!
# S8.2 observed-time layer, packet T8A.F06: the local generator and its square have weighted order two and four
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.MovOsc

variable {d : ℕ}

local notation "𝒮" => SchwartzMap (Euc d) ℝ

/-- the Schwartz map `P g` as an explicit sum of coordinate pieces -/
def r26t8a_f06_Pj (a beta : ℝ) (rho : Euc d → ℝ) (g : 𝒮) (j : Fin d) : 𝒮 :=
  beta⁻¹ • mova1_D j (mova1_D j g) - a • mova1_X j (mova1_D j g) -
    mova3b2_bsm (fun x => forceMean rho x j) (mova1_D j g)

def r26t8a_f06_P (a beta : ℝ) (rho : Euc d → ℝ) (g : 𝒮) : 𝒮 :=
  ∑ j, r26t8a_f06_Pj a beta rho g j

theorem r26t8a_f06_apply (a beta : ℝ) (rho : Euc d → ℝ)
    (hF : ∀ j : Fin d, (fun x => forceMean rho x j).HasTemperateGrowth) (g : 𝒮) (x : Euc d) :
    r26t8a_f06_P a beta rho g x = r26t8a_localP a beta rho g x := by
  have hg : ContDiff ℝ 2 (⇑g) := g.smooth 2
  have hlap : Laplacian.laplacian (⇑g) x =
      ∑ j : Fin d, mova1_D j (mova1_D j g) x := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (⇑g)
      (EuclideanSpace.basisFun (Fin d) ℝ)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mova1_D_comm_apply, iteratedFDeriv_two_apply]
    simp
  have hx : fderiv ℝ (⇑g) x x = ∑ j : Fin d, x j * mova1_D j g x := by
    have e : x = ∑ j : Fin d, x j • EuclideanSpace.single j (1 : ℝ) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    have e2 : fderiv ℝ (⇑g) x x = fderiv ℝ (⇑g) x (∑ j : Fin d, x j • EuclideanSpace.single j (1 : ℝ)) :=
      congrArg (fderiv ℝ (⇑g) x) e
    rw [e2]
    simp [map_sum, mova1_D_apply]
  have hin : inner ℝ (forceMean rho x) (gradient (⇑g) x) =
      ∑ j : Fin d, forceMean rho x j * mova1_D j g x := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [HRS.MS.MovLin.mov2d_grad_coord]
    simp [mova1_D_apply, mul_comm]
  unfold r26t8a_f06_P r26t8a_f06_Pj r26t8a_localP
  rw [hlap, hx, hin]
  simp only [sum_apply, sub_apply, smul_apply, mova1_X_apply,
    mova3b2_bsm_apply (hF _), smul_eq_mul]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- `H^n ≤ C Σ^n` on Schwartz functions, in `ℝ≥0∞` form -/
theorem r26t8a_f06_sob (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ g : 𝒮,
    sobolevNormE (n : ℝ) (⇑g) ≤ ENNReal.ofReal (C * oscNorm (n : ℝ) g) := by
  have hD : ∀ j : Fin d, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : 𝒮, mo_l2 ((mova1_D j)^[n] g) ≤ C * oscNorm (n : ℝ) g :=
    fun j => mova1_l2_le (mova1_Bnd_Diter j n)
  choose Cj hCj0 hCj using hD
  refine ⟨Real.sqrt (((d : ℝ) + 1) ^ n) * (1 + ∑ j, Cj j),
    mul_nonneg (Real.sqrt_nonneg _) (by have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hCj0 j); linarith), fun g => ?_⟩
  obtain ⟨hmem, hb⟩ := mova1_sobolev_bound n g
  unfold sobolevNormE
  rw [if_pos hmem]
  refine ENNReal.ofReal_le_ofReal ?_
  have h0 : mo_l2 g ≤ oscNorm (n : ℝ) g := by
    have h1 := oscNorm_zero (⇑g) (g.memLp 2)
    have h2 := (mo_mono (r := 0) (r' := (n : ℝ)) (Nat.cast_nonneg n) (memOsc_schwartz (n : ℝ) g)).2
    unfold mo_l2; rw [← h1]; exact h2
  have h3 : ∑ j : Fin d, mo_l2 ((mova1_D j)^[n] g) ≤ (∑ j, Cj j) * oscNorm (n : ℝ) g := by
    rw [Finset.sum_mul]; exact Finset.sum_le_sum fun j _ => hCj j g
  have hb' : HRS.Whole.sobolevNorm (n : ℝ) (⇑g) ≤ Real.sqrt (((d : ℝ) + 1) ^ n) *
      (mo_l2 g + ∑ j : Fin d, mo_l2 ((mova1_D j)^[n] g)) := hb
  have hsq : Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (n : ℝ) (⇑g)) =
      HRS.Whole.sobolevNorm (n : ℝ) (⇑g) := rfl
  rw [hsq]
  refine hb'.trans ?_
  have := mul_le_mul_of_nonneg_left (add_le_add h0 h3) (Real.sqrt_nonneg (((d : ℝ) + 1) ^ n))
  calc _ ≤ _ := this
    _ = _ := by ring

theorem r26t8a_f06_W_sum (n : ℕ) {ι : Type*} (s : Finset ι) (g : ι → 𝒮) :
    mova1_W n (∑ i ∈ s, g i) ≤ ∑ i ∈ s, mova1_W n (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := mova3c_W_smul n 0 (0 : 𝒮)
    simp at this
    simp [this]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (mova3b2_W_add n _ _).trans (add_le_add le_rfl ih)

theorem r26t8a_f06_W_sub (n : ℕ) (f g : 𝒮) : mova1_W n (f - g) ≤ mova1_W n f + mova1_W n g := by
  have h := mova3b2_W_add n f ((-1 : ℝ) • g)
  rw [mova3c_W_smul] at h
  simpa [sub_eq_add_neg] using h

theorem r26t8a_f06_bnd_nat {k : ℕ} {T : 𝒮 → 𝒮} (h : mova1_Bnd k T) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝒮, oscNorm (n : ℝ) (T f) ≤ C * oscNorm ((n + k : ℕ) : ℝ) f := by
  obtain ⟨C, hC, h⟩ := h (n : ℝ)
  exact ⟨C, hC, fun f => by simpa using h f⟩

/-- coordinate piece of `P` in the word norm -/
theorem r26t8a_f06_Wj (a beta : ℝ) (rho : Euc d → ℝ)
    (hF : ∀ j : Fin d, (fun x => forceMean rho x j).HasTemperateGrowth)
    (hFb : ∀ (j : Fin d) (N : ℕ), HRS.MemCb N (fun x => forceMean rho x j)) (j : Fin d) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : 𝒮,
      mova1_W n (r26t8a_f06_Pj a beta rho g j) ≤ C * oscNorm ((n + 2 : ℕ) : ℝ) g := by
  obtain ⟨Kw, hKw, hW⟩ := mova3c_W_le_osc (d := d) n
  obtain ⟨C1, hC1, h1⟩ := r26t8a_f06_bnd_nat (mova1_Bnd_comp (mova1_Bnd_D j) (mova1_Bnd_D j)) n
  obtain ⟨C2, hC2, h2⟩ := r26t8a_f06_bnd_nat (mova1_Bnd_comp (mova1_Bnd_X j) (mova1_Bnd_D j)) n
  obtain ⟨C3, hC3, h3⟩ := r26t8a_f06_bnd_nat (mova1_Bnd_D j) n
  obtain ⟨Cm, hCm, hM⟩ := mo_mult_memCb (d := d) (n : ℝ) n (by rw [abs_of_nonneg (Nat.cast_nonneg n)])
  set A : ℝ := HRS.cbNorm n (fun x => forceMean rho x j) with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => Real.iSup_nonneg fun z => norm_nonneg _
  have hmono : ∀ (m : ℕ), n + 2 ≥ m → ∀ g : 𝒮, oscNorm ((m : ℕ) : ℝ) g ≤ oscNorm ((n + 2 : ℕ) : ℝ) g :=
    fun m hm g => HRS.MS.Ul.ul6_osc_mono hm g
  refine ⟨Kw * (|beta⁻¹| * C1 + |a| * C2 + Cm * A * C3), by positivity, fun g => ?_⟩
  have hDD : oscNorm (n : ℝ) (⇑(mova1_D j (mova1_D j g))) ≤ C1 * oscNorm ((n + 2 : ℕ) : ℝ) g :=
    h1 g
  have hXD : oscNorm (n : ℝ) (⇑(mova1_X j (mova1_D j g))) ≤ C2 * oscNorm ((n + 2 : ℕ) : ℝ) g := h2 g
  have hD1 : oscNorm (n : ℝ) (⇑(mova1_D j g)) ≤ C3 * oscNorm ((n + 2 : ℕ) : ℝ) g :=
    (h3 g).trans (mul_le_mul_of_nonneg_left (hmono (n + 1) (by omega) g) hC3)
  have hB : oscNorm (n : ℝ) (⇑(mova3b2_bsm (fun x => forceMean rho x j) (mova1_D j g))) ≤
      Cm * A * (C3 * oscNorm ((n + 2 : ℕ) : ℝ) g) := by
    have hfun : (⇑(mova3b2_bsm (fun x => forceMean rho x j) (mova1_D j g)) : Euc d → ℝ) =
        fun x => forceMean rho x j * mova1_D j g x := funext (mova3b2_bsm_apply (hF j) _)
    rw [hfun]
    refine (hM _ (hF j) (hFb j n) _ (memOsc_schwartz (n : ℝ) _)).2.trans ?_
    exact mul_le_mul_of_nonneg_left hD1 (mul_nonneg hCm hA0)
  have eW : ∀ w : 𝒮, mova1_W n w ≤ Kw * oscNorm (n : ℝ) w := hW
  unfold r26t8a_f06_Pj
  refine (r26t8a_f06_W_sub n _ _).trans ?_
  refine (add_le_add (r26t8a_f06_W_sub n _ _) le_rfl).trans ?_
  rw [mova3c_W_smul, mova3c_W_smul]
  have t1 := eW (mova1_D j (mova1_D j g))
  have t2 := eW (mova1_X j (mova1_D j g))
  have t3 := eW (mova3b2_bsm (fun x => forceMean rho x j) (mova1_D j g))
  have u1 : |beta⁻¹| * mova1_W n (mova1_D j (mova1_D j g)) ≤
      |beta⁻¹| * (Kw * (C1 * oscNorm ((n + 2 : ℕ) : ℝ) g)) :=
    mul_le_mul_of_nonneg_left (t1.trans (mul_le_mul_of_nonneg_left hDD hKw)) (abs_nonneg _)
  have u2 : |a| * mova1_W n (mova1_X j (mova1_D j g)) ≤
      |a| * (Kw * (C2 * oscNorm ((n + 2 : ℕ) : ℝ) g)) :=
    mul_le_mul_of_nonneg_left (t2.trans (mul_le_mul_of_nonneg_left hXD hKw)) (abs_nonneg _)
  have u3 := t3.trans (mul_le_mul_of_nonneg_left hB hKw)
  nlinarith [u1, u2, u3]

theorem r26t8a_f06_Psigma (a beta : ℝ) (rho : Euc d → ℝ)
    (hF : ∀ j : Fin d, (fun x => forceMean rho x j).HasTemperateGrowth)
    (hFb : ∀ (j : Fin d) (N : ℕ), HRS.MemCb N (fun x => forceMean rho x j)) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : 𝒮,
      oscNorm (n : ℝ) (r26t8a_f06_P a beta rho g) ≤ C * oscNorm ((n + 2 : ℕ) : ℝ) g := by
  obtain ⟨Cl, hCl, hl⟩ := mova1_lower_W (d := d) n
  have hj := fun j => r26t8a_f06_Wj a beta rho hF hFb j n
  choose Cj hCj0 hCj using hj
  refine ⟨Cl * ∑ j, Cj j, mul_nonneg hCl (Finset.sum_nonneg fun j _ => hCj0 j), fun g => ?_⟩
  refine (hl _).trans ?_
  have h1 := r26t8a_f06_W_sum n Finset.univ (fun j => r26t8a_f06_Pj a beta rho g j)
  have h2 : ∑ j, mova1_W n (r26t8a_f06_Pj a beta rho g j) ≤
      (∑ j, Cj j) * oscNorm ((n + 2 : ℕ) : ℝ) g := by
    rw [Finset.sum_mul]; exact Finset.sum_le_sum fun j _ => hCj j g
  calc Cl * mova1_W n (r26t8a_f06_P a beta rho g)
      ≤ Cl * ((∑ j, Cj j) * oscNorm ((n + 2 : ℕ) : ℝ) g) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hCl
    _ = _ := by ring

theorem r26t8a_f06_force_comp (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) :
    (∀ j : Fin d, (fun x => forceMean rho x j).HasTemperateGrowth) ∧
    (∀ (j : Fin d) (N : ℕ), HRS.MemCb N (fun x => forceMean rho x j)) := by
  obtain ⟨hsm, hb⟩ := r26t8a_thermal_force d hd a beta ha hbeta rho hrho
  have hcomp : ∀ j : Fin d, (fun x => forceMean rho x j) =
      (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) ∘ forceMean rho := fun j => rfl
  have hder : ∀ (j : Fin d) (k : ℕ) (x : Euc d),
      ‖iteratedFDeriv ℝ k (fun x => forceMean rho x j) x‖ ≤
        ‖iteratedFDeriv ℝ k (forceMean rho) x‖ := by
    intro j k x
    rw [hcomp j]
    refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ (hsm.contDiffAt) (by simp)).trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) (HRS.MS.Ul.ul6_proj_norm_le j)
  have hsmj : ∀ j : Fin d, ContDiff ℝ ∞ (fun x => forceMean rho x j) := fun j =>
    (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).contDiff.comp hsm
  refine ⟨fun j => ⟨hsmj j, fun n => ?_⟩, fun j N => ⟨(hsmj j).of_le (by exact_mod_cast le_top), ?_⟩⟩
  · obtain ⟨C, hC0, hC⟩ := hb n
    exact ⟨0, C, fun x => by
      simpa using (hder j n x).trans ((le_add_of_nonneg_right (norm_nonneg _)).trans (hC x))⟩
  · intro k hk
    obtain ⟨C, hC0, hC⟩ := hb k
    refine ⟨C, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (hder j k x).trans ((le_add_of_nonneg_right (norm_nonneg _)).trans (hC x))

end HRS.MS.R26T8A

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.MovOsc

theorem r26t8a_localP_osc (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SchwartzMap (Euc d) ℝ,
      (∃ p : SchwartzMap (Euc d) ℝ, ⇑p = r26t8a_localP a beta rho f) ∧
      sobolevNormE (r : ℝ) (r26t8a_localP a beta rho f) ≤
        ENNReal.ofReal (C * oscNorm ((r + 2 : ℕ) : ℝ) f) ∧
      sobolevNormE (r : ℝ) (r26t8a_localP a beta rho (r26t8a_localP a beta rho f)) ≤
        ENNReal.ofReal (C * oscNorm ((r + 4 : ℕ) : ℝ) f) := by
  obtain ⟨hF, hFb⟩ := r26t8a_f06_force_comp d hd a beta ha hbeta rho hrho
  obtain ⟨Cs, hCs, hs⟩ := r26t8a_f06_sob (d := d) r
  obtain ⟨C1, hC1, h1⟩ := r26t8a_f06_Psigma a beta rho hF hFb r
  obtain ⟨C2, hC2, h2⟩ := r26t8a_f06_Psigma a beta rho hF hFb (r + 2)
  refine ⟨Cs * C1 * (1 + C2), by positivity, fun f => ⟨⟨r26t8a_f06_P a beta rho f, ?_⟩, ?_, ?_⟩⟩
  · funext x; exact r26t8a_f06_apply a beta rho hF f x
  · have e : (⇑(r26t8a_f06_P a beta rho f) : Euc d → ℝ) = r26t8a_localP a beta rho f :=
      funext fun x => r26t8a_f06_apply a beta rho hF f x
    rw [← e]
    refine (hs _).trans (ENNReal.ofReal_le_ofReal ?_)
    have := mul_le_mul_of_nonneg_left (h1 f) hCs
    have h0 : 0 ≤ oscNorm ((r + 2 : ℕ) : ℝ) f := Real.sqrt_nonneg _
    nlinarith [mul_nonneg (mul_nonneg hCs hC1) (mul_nonneg hC2 h0)]
  · have e : (⇑(r26t8a_f06_P a beta rho f) : Euc d → ℝ) = r26t8a_localP a beta rho f :=
      funext fun x => r26t8a_f06_apply a beta rho hF f x
    have e2 : r26t8a_localP a beta rho (r26t8a_localP a beta rho f) =
        ⇑(r26t8a_f06_P a beta rho (r26t8a_f06_P a beta rho f)) := by
      funext x
      rw [← e]
      exact (r26t8a_f06_apply a beta rho hF (r26t8a_f06_P a beta rho f) x).symm
    rw [e2]
    refine (hs _).trans (ENNReal.ofReal_le_ofReal ?_)
    have a1 := h1 (r26t8a_f06_P a beta rho f)
    have a2 : oscNorm ((r + 2 : ℕ) : ℝ) (r26t8a_f06_P a beta rho f) ≤
        C2 * oscNorm ((r + 4 : ℕ) : ℝ) f := h2 f
    have h0 : 0 ≤ oscNorm ((r + 4 : ℕ) : ℝ) f := Real.sqrt_nonneg _
    have h3 : oscNorm ((r + 2 : ℕ) : ℝ) f ≤ oscNorm ((r + 4 : ℕ) : ℝ) f :=
      HRS.MS.Ul.ul6_osc_mono (by omega) f
    have b1 : oscNorm (r : ℝ) (r26t8a_f06_P a beta rho (r26t8a_f06_P a beta rho f)) ≤
        C1 * (C2 * oscNorm ((r + 4 : ℕ) : ℝ) f) :=
      a1.trans (mul_le_mul_of_nonneg_left a2 hC1)
    have := mul_le_mul_of_nonneg_left b1 hCs
    nlinarith [mul_nonneg (mul_nonneg hCs hC1) h0, mul_nonneg (mul_nonneg hCs hC1) (mul_nonneg hC2 h0)]

end HRS.MS.R26T8A

end
