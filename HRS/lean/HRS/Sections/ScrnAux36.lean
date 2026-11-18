import HRS.Sections.ScrnAux35

/-!
# Packet SCRN, part 36: time profiles `θ(r) = e^{-(T-r)λ}`, the pair bounds and the transport field

* `scrnTheta lam T r = exp (-(T - r) lam)`, `∫_{[0,T]} θ ≤ 1/λ`, `∫_{[0,min(Ta,Tb))} θ_a θ_b ≤ 1/λ`.
* `scrn_GB_pair`: Lipschitz and `Ḣ^{(d-s)/2}` bounds of `⟨∇g, ∇g'⟩` from two `ScrnGB` bundles.
* `scrn_gfb2_v_mf`: the transport field of `mfData` is `-∇g`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace HRS

variable {d : ℕ}

open PDE

/-- The time profile `θ(r) = e^{-(T-r) λ}` of the decay of a transported test. -/
def scrnTheta (lam T r : ℝ) : ℝ := Real.exp (-(T - r) * lam)

lemma scrnTheta_pos (lam T r : ℝ) : 0 < scrnTheta lam T r := Real.exp_pos _

lemma scrnTheta_cont (lam T : ℝ) : Continuous (scrnTheta lam T) := by
  unfold scrnTheta; fun_prop

lemma scrnTheta_le_one {lam T r : ℝ} (hlam : 0 ≤ lam) (hr : r ≤ T) : scrnTheta lam T r ≤ 1 := by
  unfold scrnTheta
  rw [Real.exp_le_one_iff]
  nlinarith [mul_nonneg (sub_nonneg.2 hr) hlam]

lemma scrn_theta_int {lam T : ℝ} (hlam : 0 < lam) (hT : 0 ≤ T) :
    ∫ r in Icc 0 T, scrnTheta lam T r ≤ 1 / lam := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
  have e1 : ∀ r : ℝ, scrnTheta lam T r =
      Real.exp (-T * lam) * (1 / lam) * (2 * (lam / 2) * Real.exp (2 * (lam / 2) * r)) := by
    intro r
    unfold scrnTheta
    have : 2 * (lam / 2) = lam := by ring
    rw [this]
    have h2 : Real.exp (-(T - r) * lam) = Real.exp (-T * lam) * Real.exp (lam * r) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h2]
    field_simp
  simp_rw [e1]
  rw [intervalIntegral.integral_const_mul, scrn_int_exp (lam / 2) T hT]
  have e2 : 2 * (lam / 2) = lam := by ring
  rw [e2]
  have h3 : Real.exp (-T * lam) * Real.exp (lam * T) = 1 := by
    rw [← Real.exp_add, show -T * lam + lam * T = 0 by ring, Real.exp_zero]
  have : Real.exp (-T * lam) * (1 / lam) * (Real.exp (lam * T) - 1) = (1 - Real.exp (-T * lam)) / lam := by
    calc Real.exp (-T * lam) * (1 / lam) * (Real.exp (lam * T) - 1)
        = (1 / lam) * (Real.exp (-T * lam) * Real.exp (lam * T) - Real.exp (-T * lam)) := by ring
      _ = (1 / lam) * (1 - Real.exp (-T * lam)) := by rw [h3]
      _ = _ := by ring
  rw [this]
  exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-T * lam)]) hlam.le

lemma scrn_theta_pair_int {lam Ta Tb : ℝ} (hlam : 0 < lam) (ha : 0 ≤ Ta) (hb : 0 ≤ Tb) :
    ∫ r in Ico 0 (min Ta Tb), scrnTheta lam Ta r * scrnTheta lam Tb r ≤ 1 / lam := by
  have hca := scrnTheta_cont lam Ta
  have hcb := scrnTheta_cont lam Tb
  have h1 : ∫ r in Ico 0 (min Ta Tb), scrnTheta lam Ta r * scrnTheta lam Tb r ≤
      ∫ r in Ico 0 (min Ta Tb), scrnTheta lam Ta r := by
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ico fun r hr => ?_
    · exact ((hca.mul hcb).integrableOn_Icc (a := 0) (b := min Ta Tb)).mono_set Ico_subset_Icc_self
    · exact (hca.integrableOn_Icc (a := 0) (b := min Ta Tb)).mono_set Ico_subset_Icc_self
    · have hrb : r ≤ Tb := hr.2.le.trans (min_le_right _ _)
      have := scrnTheta_le_one hlam.le hrb
      have := scrnTheta_pos lam Ta r
      nlinarith
  have h2 : ∫ r in Ico 0 (min Ta Tb), scrnTheta lam Ta r ≤ ∫ r in Icc 0 Ta, scrnTheta lam Ta r := by
    refine setIntegral_mono_set (hca.integrableOn_Icc) ?_ ?_
    · exact Filter.Eventually.of_forall fun r => (scrnTheta_pos lam Ta r).le
    · refine Filter.Eventually.of_forall fun r hr => ?_
      exact ⟨hr.1, hr.2.le.trans (min_le_left _ _)⟩
  exact h1.trans (h2.trans (scrn_theta_int hlam ha))

lemma scrn_isLip_mono {L L' : ℝ} {a : Torus d → ℝ} (h : KernelGrad.IsLipschitz L a) (hL : L ≤ L') :
    KernelGrad.IsLipschitz L' a := by
  intro x y
  refine (h x y).trans (mul_le_mul_of_nonneg_right hL ?_)
  unfold KernelGrad.tdist; exact norm_nonneg _

lemma scrn_gfb2_v_mf {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) (g : Torus d → ℝ) :
    HRS.GF.gfb2_v (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ).M g = scrnV g := by
  funext x
  unfold HRS.GF.gfb2_v scrnV
  show Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (Torus.grad g x) = -Torus.grad g x
  simp [Torus.matVec]

theorem scrn_GB_pair {s ℓ θ θ' C : ℝ} {g g' : Torus d → ℝ} (hsd : s < d) (hℓ : 0 < ℓ)
    (hθ : 0 ≤ θ) (hθ' : 0 ≤ θ') (h : ScrnGB d s ℓ θ g C) (h' : ScrnGB d s ℓ θ' g' C) :
    KernelGrad.IsLipschitz (2 * d * C ^ 2 * ℓ ^ (-(d : ℝ) - 3) * (θ * θ'))
        (fun x => inner ℝ (Torus.grad g x) (Torus.grad g' x)) ∧
      HasFiniteHomSobolev (((d : ℝ) - s) / 2) (fun x => inner ℝ (Torus.grad g x) (Torus.grad g' x)) ∧
      homSobolev (((d : ℝ) - s) / 2) (fun x => inner ℝ (Torus.grad g x) (Torus.grad g' x)) ≤
        2 * d * 2 ^ (3 * (((d : ℝ) - s) / 2) / 2) * C ^ 2 *
          ℓ ^ (-((d : ℝ) + ((d : ℝ) - s)) / 2 - 2) * (θ * θ') := by
  have hC := h.nn
  have hp : ∀ e : ℝ, 0 ≤ ℓ ^ e := fun e => Real.rpow_nonneg hℓ.le e
  have hpp : ∀ x y : ℝ, ℓ ^ x * ℓ ^ y = ℓ ^ (x + y) := fun x y => (Real.rpow_add hℓ x y).symm
  refine ⟨?_, ?_⟩
  · refine scrn_isLip_mono (scrn_prod_lip h.ck2 h'.ck2 (Gf := θ * C * ℓ ^ (-((d : ℝ) / 2) - 1))
      (Gg := θ' * C * ℓ ^ (-((d : ℝ) / 2) - 1)) (Hf := θ * C * ℓ ^ (-((d : ℝ) / 2) - 2))
      (Hg := θ' * C * ℓ ^ (-((d : ℝ) / 2) - 2)) h.d1 h'.d1 h.d2 h'.d2) (le_of_eq ?_)
    have e : ℓ ^ (-((d : ℝ) / 2) - 1) * ℓ ^ (-((d : ℝ) / 2) - 2) = ℓ ^ (-(d : ℝ) - 3) := by
      rw [hpp]; congr 1; ring
    calc (d : ℝ) * (θ * C * ℓ ^ (-((d : ℝ) / 2) - 1) * (θ' * C * ℓ ^ (-((d : ℝ) / 2) - 2)) +
          θ' * C * ℓ ^ (-((d : ℝ) / 2) - 1) * (θ * C * ℓ ^ (-((d : ℝ) / 2) - 2)))
        = 2 * d * C ^ 2 * (ℓ ^ (-((d : ℝ) / 2) - 1) * ℓ ^ (-((d : ℝ) / 2) - 2)) * (θ * θ') := by ring
      _ = _ := by rw [e]
  · have ha : (0 : ℝ) ≤ ((d : ℝ) - s) / 2 := by linarith
    obtain ⟨hfin, hhom⟩ := scrn_hom_prod ha h.ck2 h'.ck2
      (Wf := θ * C * ℓ ^ (-((d : ℝ) / 2) - 1)) (Wg := θ' * C * ℓ ^ (-((d : ℝ) / 2) - 1))
      (Hf := θ * C * ℓ ^ (-(2 * (((d : ℝ) - s) / 2) + 2) / 2))
      (Hg := θ' * C * ℓ ^ (-(2 * (((d : ℝ) - s) / 2) + 2) / 2))
      (by have := hp (-((d : ℝ) / 2) - 1); positivity) (by have := hp (-((d : ℝ) / 2) - 1); positivity)
      (by have := hp (-(2 * (((d : ℝ) - s) / 2) + 2) / 2); positivity)
      (by have := hp (-(2 * (((d : ℝ) - s) / 2) + 2) / 2); positivity)
      h.w1 h.w1b h'.w1 h'.w1b h.hq h.hqb h'.hq h'.hqb
    refine ⟨hfin, hhom.trans (le_of_eq ?_)⟩
    have e : ℓ ^ (-(2 * (((d : ℝ) - s) / 2) + 2) / 2) * ℓ ^ (-((d : ℝ) / 2) - 1) =
        ℓ ^ (-((d : ℝ) + ((d : ℝ) - s)) / 2 - 2) := by
      rw [hpp]; congr 1; ring
    calc (d : ℝ) * (2 ^ (3 * (((d : ℝ) - s) / 2) / 2) *
          (θ * C * ℓ ^ (-(2 * (((d : ℝ) - s) / 2) + 2) / 2) * (θ' * C * ℓ ^ (-((d : ℝ) / 2) - 1)) +
            θ * C * ℓ ^ (-((d : ℝ) / 2) - 1) * (θ' * C * ℓ ^ (-(2 * (((d : ℝ) - s) / 2) + 2) / 2))))
        = 2 * d * 2 ^ (3 * (((d : ℝ) - s) / 2) / 2) * C ^ 2 *
            (ℓ ^ (-(2 * (((d : ℝ) - s) / 2) + 2) / 2) * ℓ ^ (-((d : ℝ) / 2) - 1)) * (θ * θ') := by ring
      _ = _ := by rw [e]

end HRS
