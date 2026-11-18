import HRS.MS.SuppU3Aux7
import HRS.MP.RdPropKernel
import HRS.Whole.AppendixALemmas

/-!
# U3: `HRS.Whole.AppendixALemmas.adjoint_field_kernel` (S.A.20)

Clauses (1), (2): Riesz representation of the evaluation functionals (`rpk_exists_rep`, `hneg_eq_zero_of_pairing_zero`,
`hneg_norm_le_of_pairing`); (3): Pettis via the countable norming family of tests (`hneg_measurable_iff`);
(4): the abstract `𝒩`-bound `u3_abstract` (`SuppU3Aux6`) applied to `Φ_j(x) = K_j(x) ∈ H^{-Γ}` with the norming
functionals `φ ↦ (J φ, ·)`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.SuppU3
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.HNegInfra HRS.MP.RdProp

variable {d : ℕ}

theorem u3_innerR_eq {Γ : ℝ} (F G : HNeg d Γ) : HNeg.innerR F G = inner ℝ F G := by
  rw [mhn_inner_eq, L2.inner_def]
  unfold HNeg.innerR
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [RCLike.inner_apply, HNeg.fourier]
  ring

/-- The norming functionals `φ ↦ ⟨φ, ·⟩`. -/
def u3_ell (Γ : ℝ) (φ : rpk_Tst d Γ) : HNeg d Γ →L[ℝ] ℝ := innerSL ℝ (rpk_J Γ φ)

theorem u3_ell_apply {Γ : ℝ} (φ : rpk_Tst d Γ) (F : HNeg d Γ) :
    u3_ell Γ φ F = HNeg.pairing φ.1 F := by
  rw [← rpk_J_inner]; rfl

theorem u3_ell_norming (Γ : ℝ) (F : HNeg d Γ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ φ : rpk_Tst d Γ, |u3_ell Γ φ F| ≤ c * HRS.Whole.sobolevNorm Γ φ.1) : ‖F‖ ≤ c :=
  hneg_norm_le_of_pairing F c hc (fun φ hφ => by
    have := h ⟨φ, hφ⟩
    rwa [u3_ell_apply] at this)

theorem u3_pd_one (U : Euc d → ℝ) (j : Fin d) (x : Euc d) :
    partialDeriv (fun _ : Fin 1 => j) U x = fderiv ℝ U x (EuclideanSpace.single j (1:ℝ)) := by
  unfold partialDeriv
  rw [iteratedFDeriv_one_apply]

theorem adjoint_field_kernel_proof : type_of% @HRS.Whole.AppendixALemmas.adjoint_field_kernel := by
  intro d Γ T K χ hχ
  set K₀ : ℝ := max K 0 with hK₀
  have hK₀0 : 0 ≤ K₀ := le_max_right _ _
  have hKK₀ : K ≤ K₀ := le_max_left _ _
  have hms : 3 ≤ mStar d := by unfold mStar; omega
  have hm2 : 2 ≤ mStar d - 1 := by omega
  obtain ⟨Cabs, hCabs⟩ := u3_abstract d (mStar d - 1) hm2 (((d : ℝ) + 1) ^ (mStar d - 1) * K₀)
    (by positivity) χ hχ.1 hχ.2.1
  refine ⟨max K₀ Cabs, fun Cf hadj hmeas => ?_⟩
  have hcd : ∀ N : ℕ, 1 ≤ N → ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Euc d → ℝ,
      IsSobolevTest (Γ : ℝ) φ → ContDiff ℝ (mStar d : ℕ) (propagatorW (Cf N) r t φ) :=
    fun N hN r t hr hrt htT φ hφ => (hadj N hN r t hr hrt htT φ hφ).2.1
  have hlinP : ∀ N : ℕ, 1 ≤ N → ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ φ' : Euc d → ℝ, ∀ c : ℝ,
      IsSobolevTest (Γ : ℝ) φ → IsSobolevTest (Γ : ℝ) φ' →
      propagatorW (Cf N) r t (c • φ + φ') = c • propagatorW (Cf N) r t φ + propagatorW (Cf N) r t φ' := by
    intro N hN r t hr hrt htT φ φ' c hφ hφ'
    have h := (hadj N hN r t hr hrt htT φ' hφ').2.2.1 φ hφ c
    rw [add_comm (c • φ) φ', h, add_comm]
  have hbdP : ∀ N : ℕ, 1 ≤ N → ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Euc d → ℝ,
      IsSobolevTest (Γ : ℝ) φ → ∀ (l : ℕ), l ≤ mStar d → ∀ i : Fin l → Fin d, ∀ x : Euc d,
      |partialDeriv i (propagatorW (Cf N) r t φ) x| ≤ K₀ * HRS.Whole.sobolevNorm (Γ : ℝ) φ :=
    fun N hN r t hr hrt htT φ hφ l hl i x =>
      ((hadj N hN r t hr hrt htT φ hφ).2.2.2 l hl i x).trans
        (mul_le_mul_of_nonneg_right hKK₀ (Real.sqrt_nonneg _))
  refine ⟨?_, ?_, ?_⟩
  · -- (1) existence and uniqueness
    intro N hN j l hl i r t hr hrt htT x
    obtain ⟨k, hk⟩ := rpk_exists_rep (d := d) (Γ := (Γ : ℝ))
      (fun φ => partialDeriv (Fin.cons j i : Fin (l + 1) → Fin d) (propagatorW (Cf N) r t φ) x) K₀
      (fun φ φ' c hφ hφ' => by
        show partialDeriv _ (propagatorW (Cf N) r t (c • φ + φ')) x = _
        rw [hlinP N hN r t hr hrt htT φ φ' c hφ hφ']
        exact u3_partialDeriv_comb _ (hcd N hN r t hr hrt htT φ hφ) (hcd N hN r t hr hrt htT φ' hφ')
          (by omega) c x)
      (fun φ hφ => hbdP N hN r t hr hrt htT φ hφ (l + 1) (by omega) _ x)
    refine ⟨k, hk, fun k' hk' => ?_⟩
    have h0 : k' - k = 0 := hneg_eq_zero_of_pairing_zero _ (fun φ hφ => by
      rw [mhn_pairing_sub hφ, hk φ hφ, hk' φ hφ, sub_self])
    exact sub_eq_zero.1 h0
  · -- (2) the norm bound
    intro N hN j l hl i r t hr hrt htT x k hk
    refine (hneg_norm_le_of_pairing k K₀ hK₀0 (fun φ hφ => ?_)).trans (le_max_left _ _)
    rw [hk φ hφ]
    exact hbdP N hN r t hr hrt htT φ hφ (l + 1) (by omega) _ x
  · intro Kern hKern
    refine ⟨?_, ?_⟩
    · -- (3) measurability
      intro N hN j
      obtain ⟨φ, hφ, -, hnorm⟩ := hneg_norming d (Γ : ℝ)
      rw [hneg_measurable_iff hφ hnorm]
      intro n
      have e : (fun p : {p : ℝ × ℝ × Euc d // 0 ≤ p.1 ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ T} =>
          HNeg.pairing (φ n) (Kern N p.1.1 p.1.2.1 p.1.2.2 j)) =
          fun p => partialDeriv (fun _ : Fin 1 => j) (propagatorW (Cf N) p.1.1 p.1.2.1 (φ n)) p.1.2.2 :=
        funext fun p => hKern N hN j p.1.1 p.1.2.1 p.2.1 p.2.2.1 p.2.2.2 p.1.2.2 (φ n) (hφ n)
      rw [e]
      exact hmeas N hN j (φ n) (hφ n)
    · -- (4) the `𝒩`-bound
      intro B _ hBn N hN r t hr hrt htT
      set Φ : Fin d → Euc d → HNeg d (Γ : ℝ) := fun j x => Kern N r t x j with hΦdef
      have hgfun : ∀ (j : Fin d) (φ : rpk_Tst d (Γ : ℝ)),
          (fun x => u3_ell (Γ : ℝ) φ (Φ j x)) =
            fun x => fderiv ℝ (propagatorW (Cf N) r t φ.1) x (EuclideanSpace.single j (1:ℝ)) := by
        intro j φ
        funext x
        rw [u3_ell_apply, hΦdef]
        simp only
        rw [hKern N hN j r t hr hrt htT x φ.1 φ.2, u3_pd_one]
      have hΦ : ∀ (j : Fin d) (φ : rpk_Tst d (Γ : ℝ)),
          ContDiff ℝ (mStar d - 1 : ℕ) (fun x => u3_ell (Γ : ℝ) φ (Φ j x)) := by
        intro j φ
        rw [hgfun]
        have hU := hcd N hN r t hr hrt htT φ.1 φ.2
        have hf : ContDiff ℝ ((mStar d - 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ (propagatorW (Cf N) r t φ.1)) :=
          hU.fderiv_right (by exact_mod_cast (by omega : mStar d - 1 + 1 ≤ mStar d))
        exact hf.clm_apply contDiff_const
      have hΦb : ∀ (j : Fin d) (φ : rpk_Tst d (Γ : ℝ)), ∀ k ≤ mStar d - 1, ∀ x : Euc d,
          ‖iteratedFDeriv ℝ k (fun x => u3_ell (Γ : ℝ) φ (Φ j x)) x‖ ≤
            (((d : ℝ) + 1) ^ (mStar d - 1) * K₀) * HRS.Whole.sobolevNorm (Γ : ℝ) φ.1 := by
        intro j φ k hk x
        rw [hgfun]
        have hn0 : 0 ≤ HRS.Whole.sobolevNorm (Γ : ℝ) φ.1 := Real.sqrt_nonneg _
        have hU : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (propagatorW (Cf N) r t φ.1) :=
          (hcd N hN r t hr hrt htT φ.1 φ.2).of_le (by exact_mod_cast (by omega : k + 1 ≤ mStar d))
        have h1 := u3_g_bound hU j x (c := K₀ * HRS.Whole.sobolevNorm (Γ : ℝ) φ.1)
          (mul_nonneg hK₀0 hn0)
          (fun i => hbdP N hN r t hr hrt htT φ.1 φ.2 (k + 1) (by omega) i x)
        refine h1.trans ?_
        have h2 : (d : ℝ) ^ k ≤ ((d : ℝ) + 1) ^ (mStar d - 1) :=
          (pow_le_pow_left₀ (Nat.cast_nonneg d) (by linarith) k).trans
            (pow_le_pow_right₀ (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith) hk)
        calc (d : ℝ) ^ k * (K₀ * HRS.Whole.sobolevNorm (Γ : ℝ) φ.1)
            ≤ ((d : ℝ) + 1) ^ (mStar d - 1) * (K₀ * HRS.Whole.sobolevNorm (Γ : ℝ) φ.1) :=
              mul_le_mul_of_nonneg_right h2 (mul_nonneg hK₀0 hn0)
          _ = _ := by ring
      have key := hCabs (H := HNeg d (Γ : ℝ)) (ι := rpk_Tst d (Γ : ℝ)) (u3_ell (Γ : ℝ))
        (fun φ => HRS.Whole.sobolevNorm (Γ : ℝ) φ.1) (u3_ell_norming (Γ : ℝ)) Φ hΦ hΦb B hBn
      have e : (fun x => ∑ j : Fin d, HNeg.innerR (B (Kern N r t x j)) (Kern N r t x j)) =
          fun x => ∑ j : Fin d, inner ℝ (B (Φ j x)) (Φ j x) := by
        funext x; simp only [u3_innerR_eq]; rfl
      rw [e]
      refine le_trans ?_ (ENNReal.ofReal_le_ofReal (le_max_right K₀ Cabs))
      unfold cNormE lipNormE
      exact key

end HRS.MS.SuppU3
