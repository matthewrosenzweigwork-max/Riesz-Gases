import HRS.MS.MainRdFieldAux1
import HRS.MP.RdMartingale
import HRS.MH.CommSuperCS10
import HRS.Commutator.Whole.Bridge
import HRS.MS.SuppU15Aux1
import HRS.MS.SuppU15Aux2
import HRS.MS.SuppU15Aux3

/-!
# S.A.6, packet P2: the bridge B5 `selectedCommutatorInput_of_adjoint`

`SelectedCommutatorInput S Γ T K' C₀ Λ fd.eN` from `FieldAdjointInputRd fd S Kad` (`Λ ≥ 1`):

* the transport `v = Mᵀ∇U^{r,t}φ` is Lipschitz with constant `(d²·MB)(d²·Kad‖φ‖)` from the entrywise bound of the
  second derivatives (`deriv` at order `2 ≤ m_*`) and `MatBound`;
* `nd`, `decSuperIso`, `decSuperHilb` (`d-2 ≤ s`): S.B.5(i) `whole_commutator_super`;
* `decSub (sharp a)`: S.B.5(ii) with the clause `wbound` (`HasFracTransportBound (a/2) (2d/(a-2))`);
  `decSub (lower)`: S.B.5(iii) with `commLowRateError = fd.eN`;
* the density facts (`ρ ≤ Λ`, log moment at `s = 0`) come from the weighted bound of `IsRegularMFRd`;
* the completion constant is raised from the constant `C₀B` of S.B.5 to any `C₀ ≥ C₀B`, using monotonicity of `oNΛ` in `C₀`
  and nonnegativity of `F + oNΛ(C₀)` (`CompletionNonnegRd` at the given `C₀`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdField

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.SuppU15

variable {d : ℕ}

/-! ### Elementary lemmas -/

lemma sa6_clm_norm_le_sum (ℓ : Euc d →L[ℝ] ℝ) : ‖ℓ‖ ≤ ∑ a : Fin d, |ℓ (EuclideanSpace.single a (1 : ℝ))| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun a _ => abs_nonneg _) fun x => ?_
  have hx : x = ∑ a, x a • EuclideanSpace.single a (1 : ℝ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  have h1 : ℓ x = ∑ a, x a * ℓ (EuclideanSpace.single a (1 : ℝ)) := by
    conv_lhs => rw [hx]
    simp [map_sum, map_smul]
  rw [Real.norm_eq_abs, h1]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (by
    have := PiLp.norm_apply_le x a
    simpa [Real.norm_eq_abs] using this) (abs_nonneg _)

lemma sa6_matVec_le {MB : ℝ} {N : Matrix (Fin d) (Fin d) ℝ} (hN : ∀ i j, |N i j| ≤ MB) (y : Euc d) :
    ‖Torus.matVec N y‖ ≤ (d * d * max MB 0) * ‖y‖ := by
  refine (u15_norm_le_sum _).trans ?_
  have hy : ∀ j, |y j| ≤ ‖y‖ := fun j => by
    have := PiLp.norm_apply_le y j
    simpa [Real.norm_eq_abs] using this
  have h1 : ∀ i, |Torus.matVec N y i| ≤ d * max MB 0 * ‖y‖ := by
    intro i
    rw [u15_matVec_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |N i j * y j| ≤ ∑ _j : Fin d, max MB 0 * ‖y‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul ((hN i j).trans (le_max_left _ _)) (hy j) (abs_nonneg _) (le_max_right _ _)
      _ = d * max MB 0 * ‖y‖ := by simp [mul_assoc]
  calc ∑ i, |Torus.matVec N y i| ≤ ∑ _i : Fin d, d * max MB 0 * ‖y‖ := Finset.sum_le_sum fun i _ => h1 i
    _ = (d * d * max MB 0) * ‖y‖ := by simp [mul_assoc]

/-- Lipschitz bound of the gradient from the entrywise bound of the second derivatives. -/
lemma sa6_grad_lip {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (i : Fin 2 → Fin d) (x : Euc d), |HRS.Whole.partialDeriv i f x| ≤ B) (x y : Euc d) :
    ‖gradient f x - gradient f y‖ ≤ (d * d * B) * ‖x - y‖ := by
  have hfd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hgb : ∀ b : Fin d, ∀ u v : Euc d,
      |fderiv ℝ f u (EuclideanSpace.single b 1) - fderiv ℝ f v (EuclideanSpace.single b 1)| ≤
        (d * B) * ‖u - v‖ := by
    intro b u v
    set g : Euc d → ℝ := fun z => fderiv ℝ f z (EuclideanSpace.single b 1) with hg
    have hgd : Differentiable ℝ g := fun z => (hfd z).clm_apply (differentiableAt_const _)
    have hbound : ∀ z, ‖fderiv ℝ g z‖ ≤ d * B := by
      intro z
      refine (sa6_clm_norm_le_sum _).trans ?_
      have h1 : fderiv ℝ g z = (fderiv ℝ (fderiv ℝ f) z).flip (EuclideanSpace.single b 1) := by
        simp only [hg]
        rw [fderiv_clm_apply (hfd z) (differentiableAt_const _)]
        simp
      have e : ∀ a : Fin d, fderiv ℝ g z (EuclideanSpace.single a 1) =
          HRS.Whole.partialDeriv (![a, b]) f z := by
        intro a
        rw [h1]
        unfold partialDeriv
        rw [iteratedFDeriv_two_apply]
        simp
      calc ∑ a, |fderiv ℝ g z (EuclideanSpace.single a 1)| ≤ ∑ _a : Fin d, B :=
            Finset.sum_le_sum fun a _ => by rw [e a]; exact hB _ z
        _ = d * B := by simp
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := g) (fun z _ => hgd z)
      (fun z _ => hbound z) convex_univ (Set.mem_univ v) (Set.mem_univ u)
    simpa [Real.norm_eq_abs, hg] using h
  refine (u15_norm_le_sum _).trans ?_
  calc ∑ b, |(gradient f x - gradient f y) b| ≤ ∑ _b : Fin d, (d * B) * ‖x - y‖ := by
        refine Finset.sum_le_sum fun b _ => ?_
        have : (gradient f x - gradient f y) b = fderiv ℝ f x (EuclideanSpace.single b 1) -
            fderiv ℝ f y (EuclideanSpace.single b 1) := by
          simp only [PiLp.sub_apply]
          rw [HRS.MP.RdMart.mrm_grad_component, HRS.MP.RdMart.mrm_grad_component]
        rw [this]; exact hgb b x y
    _ = (d * d * B) * ‖x - y‖ := by simp [mul_assoc]

lemma sa6_hasLip {MB : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : PDE.MatBound MB M) {f : Euc d → ℝ}
    (hf : ContDiff ℝ 2 f) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (i : Fin 2 → Fin d) (x : Euc d), |HRS.Whole.partialDeriv i f x| ≤ B) :
    HasLipBoundW (fun x => Torus.matVec M.transpose (gradient f x))
      ((d * d * max MB 0) * (d * d * B)) := by
  have hMt : ∀ i j, |M.transpose i j| ≤ MB := fun i j => by
    simpa [Matrix.transpose_apply] using hM j i
  have hc0 : 0 ≤ (d * d * max MB 0) * (d * d * B) := by positivity
  refine ⟨Real.toNNReal ((d * d * max MB 0) * (d * d * B)), ?_, by rw [Real.coe_toNNReal _ hc0]⟩
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hc0]
  have e1 : Torus.matVec M.transpose (gradient f x) - Torus.matVec M.transpose (gradient f y) =
      Torus.matVec M.transpose (gradient f x - gradient f y) := by
    unfold Torus.matVec; simp
  rw [e1]
  calc ‖Torus.matVec M.transpose (gradient f x - gradient f y)‖
      ≤ (d * d * max MB 0) * ‖gradient f x - gradient f y‖ := sa6_matVec_le hMt _
    _ ≤ (d * d * max MB 0) * ((d * d * B) * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (sa6_grad_lip hf hB0 hB x y) (by positivity)
    _ = _ := by ring

/-- `ρ_N^t` is a probability density with the weighted bound `⟨x⟩^{d+3}ρ ≤ Λ`. -/
lemma sa6_dens {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 : ℝ} {r mV : ℕ}
    {C₀ : ℝ} {𝔈 : ℕ → ℝ} (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) :
    HRS.Whole.IsProbDensity (S.ρ N t) ∧ ∀ x, jbracket x ^ ((d : ℝ) + 3) * |S.ρ N t x| ≤ max Λ 0 := by
  refine ⟨(hS.mean_field.solution N hN).density t ht, ?_⟩
  obtain ⟨-, hws, hle⟩ := (hS.mean_field.regular N hN).1 t ht
  have hcb : 0 ≤ cbNorm r (S.ρ N t) := Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hws' : weightedSupE r ((d : ℝ) + 3) (S.ρ N t) ≤ ENNReal.ofReal Λ := by
    rw [← ENNReal.ofReal_toReal hws.ne]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  exact u15_weighted_zero hws'

lemma sa6_oN_mono_C0 {s Λ : ℝ} (hΛ : 0 ≤ Λ) {C₁ C₂ : ℝ} (h : C₁ ≤ C₂) (N : ℕ) :
    oNΛ d s C₁ Λ N ≤ oNΛ d s C₂ Λ N := by
  unfold oNΛ
  have : 0 ≤ Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) :=
    mul_nonneg (Real.rpow_nonneg hΛ _) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  nlinarith

lemma sa6_combine {comm F oB oC e A cE Kφ : ℝ} (h : comm ≤ A * (F + oB + cE * e)) (hA : 0 ≤ A)
    (hcE : 0 ≤ cE) (he : 0 ≤ e) (hoB : oB ≤ oC) (hnn : 0 ≤ F + oC)
    (hAK : A * max 1 cE ≤ Kφ) : comm ≤ Kφ * (F + oC + e) := by
  have hm1 : 1 ≤ max 1 cE := le_max_left _ _
  have hm2 : cE ≤ max 1 cE := le_max_right _ _
  have h1 : F + oB + cE * e ≤ max 1 cE * (F + oC + e) := by nlinarith
  have h2 : 0 ≤ F + oC + e := by linarith
  calc comm ≤ A * (F + oB + cE * e) := h
    _ ≤ A * (max 1 cE * (F + oC + e)) := mul_le_mul_of_nonneg_left h1 hA
    _ = (A * max 1 cE) * (F + oC + e) := by ring
    _ ≤ Kφ * (F + oC + e) := mul_le_mul_of_nonneg_right hAK h2

/-- The package of constants of S.B.5 for the density `fd`. -/
def Sa6Pkg (s : ℝ) (fd : FieldDensityRd d s) (MB Λ Lm : ℝ) : Prop :=
  ∃ (C₀B CB cE : ℝ) (Hv : (Euc d → Euc d) → ℝ → Prop), 0 ≤ C₀B ∧ 0 ≤ CB ∧ 0 ≤ cE ∧
    (∀ (N : ℕ), 2 ≤ N → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      (s = 0 → HasLogMoment (HRS.Whole.withDensityReal ρ) Lm) → ∀ X : EucConfig d N, Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ), Hv v K →
        |commN d s v X (HRS.Whole.withDensityReal ρ)| ≤
          CB * K * (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) + oNΛ d s C₀B Λ N + cE * fd.eN N)) ∧
    (∀ Kad : ℝ, ∃ CKa : ℝ, 0 ≤ CKa ∧ ∀ (S : WholeMainData d), S.s = s → PDE.MatBound MB S.M →
      FieldAdjointInputRd fd S Kad → ∀ N : ℕ, 1 ≤ N → ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ S.T →
      ∀ φ : Euc d → ℝ, IsSobolevTest (fd.Gamma : ℝ) φ →
        Hv (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r t φ) x))
          (CKa * HRS.Whole.sobolevNorm (fd.Gamma : ℝ) φ))

/-- The Lipschitz clause for the densities whose commutator estimate is S.B.5(i). -/
lemma sa6_clause_lip {s : ℝ} (fd : FieldDensityRd d s) (MB : ℝ) (Kad : ℝ) :
    ∃ CKa : ℝ, 0 ≤ CKa ∧ ∀ (S : WholeMainData d), S.s = s → PDE.MatBound MB S.M →
      FieldAdjointInputRd fd S Kad → ∀ N : ℕ, 1 ≤ N → ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ S.T →
      ∀ φ : Euc d → ℝ, IsSobolevTest (fd.Gamma : ℝ) φ →
        HasLipBoundW (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r t φ) x))
          (CKa * HRS.Whole.sobolevNorm (fd.Gamma : ℝ) φ) := by
  refine ⟨(d * d * max MB 0) * (d * d * max Kad 0), by positivity, ?_⟩
  intro S _ hM hFA N hN r t hr hrt htT φ hφ
  obtain ⟨-, hcd, -, hbd⟩ := hFA.deriv N hN r t hr hrt htT φ hφ
  have hm2 : 2 ≤ mStar d := by unfold mStar; omega
  have hf2 : ContDiff ℝ 2 (propagatorW (S.coeff N) r t φ) := by
    refine hcd.of_le ?_
    exact_mod_cast hm2
  have hn0 : 0 ≤ HRS.Whole.sobolevNorm (fd.Gamma : ℝ) φ := Real.sqrt_nonneg _
  have hB0 : 0 ≤ max Kad 0 * HRS.Whole.sobolevNorm (fd.Gamma : ℝ) φ := mul_nonneg (le_max_right _ _) hn0
  have := sa6_hasLip hM hf2 hB0 (fun i x => (hbd 2 hm2 i x).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hn0))
  convert this using 1
  ring

lemma sa6_pkg_super {s : ℝ} (fd : FieldDensityRd d s) (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (hsc : (d : ℝ) - 2 ≤ s) (he : ∀ N, fd.eN N = 0) (MB Λ Lm : ℝ) (hΛ : 1 ≤ Λ) :
    Sa6Pkg s fd MB Λ Lm := by
  obtain ⟨C₀B, CB, hC₀B, hCB, hB⟩ :=
    HRS.MH.CommSuper.whole_commutator_super_of_concentration_proof (d := d) hd hs0 hsd hsc Lm
  refine ⟨C₀B, CB, 0, fun v K => HasLipBoundW v K, hC₀B, hCB.le, le_rfl, ?_, fun Kad => ?_⟩
  · intro N hN ρ hρ hΛρ hlog X hX v K hv
    obtain ⟨-, hb⟩ := hB Λ hΛ N hN ρ hρ hΛρ hlog X hX v K hv
    simpa [he N] using hb
  · exact sa6_clause_lip fd MB Kad

lemma sa6_pkg_sharp {s : ℝ} (c : DecayingDensity d s) (a : ℝ)
    (ha' : a < min ((d : ℝ) + 2) (2 * s + 4)) (hda : (d : ℝ) < a)
    (hc : c = DecayingDensity.sharp a ⟨hda, ha'⟩)
    (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (MB Λ Lm : ℝ) (hΛ : 1 ≤ Λ) :
    Sa6Pkg s (FieldDensityRd.decSub c) MB Λ Lm := by
  subst hc
  have ha : (d : ℝ) < a ∧ a < (d : ℝ) + 2 := ⟨hda, lt_of_lt_of_le ha' (min_le_left _ _)⟩
  obtain ⟨C₀B, CB, hC₀B, hCB, hB⟩ :=
    HRS.Commutator.Whole.whole_commutator_sub_sharp_of_subcoulomb hs0 hsd a ha Lm
  refine ⟨C₀B, CB, 0, fun v K => HasFracTransportBound (a / 2) (2 * d / (a - 2)) v K, hC₀B, hCB.le,
    le_rfl, ?_, fun Kad => ⟨max Kad 0, le_max_right _ _, ?_⟩⟩
  · intro N hN ρ hρ hΛρ hlog X hX v K hv
    obtain ⟨-, hb⟩ := hB Λ hΛ N hN ρ hρ hΛρ hlog X hX v K hv
    simpa [FieldDensityRd.eN, DecayingDensity.errorRate] using hb
  · intro S _ _ hFA N hN r t hr hrt htT φ hφ
    have h := hFA.wbound N hN r t hr hrt htT φ hφ
    simp only [FieldDensityRd.wInput] at h
    obtain ⟨L, F, hF, hL, hw, hLK⟩ := h
    refine ⟨L, F, hF, hL, hw, hLK.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)

lemma sa6_pkg_lower {s : ℝ} (hs' : ((d : ℝ) - 4) / 3 < s) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    (MB Λ Lm : ℝ) (hΛ : 1 ≤ Λ) :
    Sa6Pkg s (FieldDensityRd.decSub (DecayingDensity.lower hs')) MB Λ Lm := by
  obtain ⟨C₀B, CB, hC₀B, hCB, hB⟩ :=
    HRS.Commutator.Whole.whole_commutator_sub_lower_of_subcoulomb hs0 hsd Lm
  refine ⟨C₀B, CB, CB,
    fun v K => HasFracTransportBound (((d : ℝ) - s) / 2) (2 * d / ((d : ℝ) - s - 2)) v K,
    hC₀B, hCB.le, hCB.le, ?_, fun Kad => ⟨max Kad 0, le_max_right _ _, ?_⟩⟩
  · intro N hN ρ hρ hΛρ hlog X hX v K hv
    obtain ⟨-, hb⟩ := hB Λ hΛ N hN ρ hρ hΛρ hlog X hX v K hv
    have e : (FieldDensityRd.decSub (DecayingDensity.lower hs')).eN N =
        HRS.Whole.commLowRateError s N := rfl
    rw [e]
    exact hb
  · intro S _ _ hFA N hN r t hr hrt htT φ hφ
    have h := hFA.wbound N hN r t hr hrt htT φ hφ
    simp only [FieldDensityRd.wInput] at h
    obtain ⟨L, F, hF, hL, hw, hLK⟩ := h
    refine ⟨L, F, hF, hL, hw, hLK.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)

theorem sa6_B5 (s : ℝ) (fd : FieldDensityRd d s) (ν₀ MB Λ ΛV G₀ νbar T m20 : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∀ Kad : ℝ, ∃ K' : ℝ,
      ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) → fd.Holds S ν₀ →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 3) (fd.Gamma + 3) C₀ 𝔈 →
        FieldAdjointInputRd fd S Kad →
        SelectedCommutatorInput S (fd.Gamma : ℝ) T K' C₀ Λ fd.eN := by
  classical
  by_cases hex : ∃ S0 : WholeMainData d, S0.s = s ∧ fd.Holds S0 ν₀
  swap
  · exact ⟨0, fun C₀ _ Kad => ⟨0, fun S hs _ _ hH => absurd ⟨S, hs, hH⟩ hex⟩⟩
  obtain ⟨S0, hS0s, hS0⟩ := hex
  have hd1 : 1 ≤ d := S0.hd
  have hs0 : 0 ≤ s := hS0s ▸ S0.hs0
  have hsd : s < d := hS0s ▸ S0.hsd
  have hH1 := hS0 1 le_rfl
  have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos hΛ
  obtain ⟨Lm, hLm⟩ := u15_logmoment (d := d) (L := (d : ℝ) + 3) (by linarith) Λ
  have pkg : Sa6Pkg s fd MB Λ Lm := by
    cases fd with
    | nd Rg =>
      have hsc : (d : ℝ) - 2 ≤ s := by
        have := hH1.1
        rw [hS0s] at this
        exact le_trans (le_max_right _ _) this
      exact sa6_pkg_super _ hd1 hs0 hsd hsc (fun N => rfl) MB Λ Lm hΛ
    | decSuperIso m p =>
      have hsc : (d : ℝ) - 2 ≤ s := by
        have := hH1.1
        rw [hS0s] at this
        exact this.le
      exact sa6_pkg_super _ hd1 hs0 hsd hsc (fun N => rfl) MB Λ Lm hΛ
    | decSuperHilb m =>
      have hsc : (d : ℝ) - 2 ≤ s := by
        have := hH1.1
        rw [hS0s] at this
        exact this.le
      exact sa6_pkg_super _ hd1 hs0 hsd hsc (fun N => rfl) MB Λ Lm hΛ
    | decSub c =>
      have hsub : s < (d : ℝ) - 2 := by
        have := hH1
        simp only [FieldDensityRd.HoldsAt] at this
        rw [hS0s] at this
        exact this
      cases c with
      | sharp a ha =>
        exact sa6_pkg_sharp _ a ha.2 ha.1 rfl hs0 hsub MB Λ Lm hΛ
      | lower hs' => exact sa6_pkg_lower hs' hs0 hsub MB Λ Lm hΛ
  obtain ⟨C₀B, CB, cE, Hv, hC₀B, hCB, hcE, hcomm, hcl⟩ := pkg
  refine ⟨C₀B, fun C₀ hC₀ Kad => ?_⟩
  obtain ⟨CKa, hCKa, hclause⟩ := hcl Kad
  refine ⟨CB * CKa * max 1 cE, fun S hs hT hinv hH R 𝔈 hS hFA => ?_⟩
  intro N hN2 X hX r t hr hrt htT φ hφ
  have hN1 : 1 ≤ N := by omega
  have htT' : t ≤ S.T := by rw [hT]; exact htT
  have hrI : r ∈ Set.Icc (0 : ℝ) S.T := ⟨hr, hrt.trans htT'⟩
  obtain ⟨hprob, hb0⟩ := sa6_dens hS hN1 hrI
  have hρle : ∀ x, S.ρ N r x ≤ Λ := fun x => by
    have := u15_dens_le (by positivity : (0 : ℝ) ≤ (d : ℝ) + 3) hprob.nonneg hb0 x
    rwa [max_eq_left hΛ0.le] at this
  have hlog : s = 0 → HasLogMoment (HRS.Whole.withDensityReal (S.ρ N r)) Lm := fun _ => hLm _ hprob hb0
  have hv := hclause S hs hS.matrix_bound hFA N hN1 r t hr hrt htT' φ hφ
  have hc := hcomm N hN2 (S.ρ N r) hprob hρle hlog X hX _ _ hv
  have hXc : X ∉ eucCollisionSet d N := fun ⟨i, j, hij, hh⟩ => hij (hX hh)
  have hcomp : CompletionNonnegRd d s C₀ := hs ▸ hS.energy.completion
  have hnn := hcomp.2 Λ hΛ N hN2 (S.ρ N r) hprob hρle (fun h0 => (hlog h0).1) X hXc
  have hn0 : 0 ≤ HRS.Whole.sobolevNorm (fd.Gamma : ℝ) φ := Real.sqrt_nonneg _
  have hmono := sa6_oN_mono_C0 (d := d) (s := s) hΛ0.le hC₀ N
  rw [hs]
  exact sa6_combine hc (mul_nonneg hCB (mul_nonneg hCKa hn0)) hcE (HRS.MP.RdRem.mrr_eN_nonneg fd N)
    hmono hnn (by
      have : CB * (CKa * HRS.Whole.sobolevNorm (fd.Gamma : ℝ) φ) * max 1 cE =
          CB * CKa * max 1 cE * HRS.Whole.sobolevNorm (fd.Gamma : ℝ) φ := by ring
      exact this.le)

end HRS.MS.MainRdField
