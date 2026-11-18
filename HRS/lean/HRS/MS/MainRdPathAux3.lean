import HRS.MS.MainRdPathAux2
import HRS.MP.RdPropAssemble
import HRS.MP.RdRemainder
import HRS.MP.RdInitClose

/-!
# S.A.9, packet P2: the three-term decomposition at the index `q = Γ + 2`

For `N ≥ 1`: the transported empirical initial field `Iq`, the thermal stochastic convolution `Mq` (`IsStochConvW`,
`τ ≡ T`) and the remainder `Rm = Z - Iq - Mq` with `IsRemainderW` (from `sa6_pairing_identity` at the index `q`).
Also the lift `ι : H^{-Γ} → H^{-q}` (Riesz representative of the restricted functional) and the level monotonicity of
the adjoint input.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdMart HRS.MP.RdProp
  HRS.MP.HNegInfra HRS.MP.RdRem HRS.MS.MainRdField HRS.MH.DualityRd

variable {d : ℕ}

/-! ### Level monotonicity and the lift -/

theorem sa9_adj_mono {C : WholeCoeff d} {T K : ℝ} {j : ℕ} {a b : ℝ} (hab : a ≤ b)
    (h : AdjointInputOneD a j C T K) : AdjointInputOneD b j C T (max K 0) := by
  intro r t hr hrt htT φ hφ
  have hφa : IsSobolevTest a φ := ⟨hφ.1, HRS.PDE.ToolboxRd.FourierAux.memSobolev_mono hab hφ.2⟩
  obtain ⟨h1, h2, h3, h4⟩ := h r t hr hrt htT φ hφa
  refine ⟨h1, h2, fun φ₂ hφ₂ c => h3 φ₂ ⟨hφ₂.1, HRS.PDE.ToolboxRd.FourierAux.memSobolev_mono hab hφ₂.2⟩ c,
    fun l hl i x => (h4 l hl i x).trans ?_⟩
  have hn := mrr_sobolevNorm_mono hab hφ.2
  have hn0 : 0 ≤ HRS.Whole.sobolevNorm a φ := Real.sqrt_nonneg _
  exact (mul_le_mul_of_nonneg_right (le_max_left K 0) hn0).trans
    (mul_le_mul_of_nonneg_left hn (le_max_right K 0))

theorem sa9_adjDeriv_mono {Cf : ℕ → WholeCoeff d} {T K : ℝ} {j : ℕ} {a b : ℝ} (hab : a ≤ b)
    (h : AdjointDerivInput a j Cf T K) : AdjointDerivInput b j Cf T (max K 0) :=
  fun N hN => sa9_adj_mono hab (h N hN)

theorem sa9_adj_order_mono {C : WholeCoeff d} {T K : ℝ} {Γ : ℝ} {j j' : ℕ} (hj : j' ≤ j)
    (h : AdjointInputOneD Γ j C T K) : AdjointInputOneD Γ j' C T K := by
  intro r t hr hrt htT φ hφ
  obtain ⟨h1, h2, h3, h4⟩ := h r t hr hrt htT φ hφ
  exact ⟨h1, h2.of_le (by exact_mod_cast hj), h3, fun l hl i x => h4 l (hl.trans hj) i x⟩

theorem sa9_pairing_comb {Γ : ℝ} {φ φ' : Euc d → ℝ} (hφ : IsSobolevTest Γ φ) (hφ' : IsSobolevTest Γ φ')
    (c : ℝ) (F : HNeg d Γ) :
    HNeg.pairing (c • φ + φ') F = c * HNeg.pairing φ F + HNeg.pairing φ' F := by
  let a : rpk_Tst d Γ := ⟨φ, hφ⟩
  let b : rpk_Tst d Γ := ⟨φ', hφ'⟩
  have h := HRS.MP.RdProp.rpk_J_inner (c • a + b) F
  rw [map_add, map_smul, inner_add_left, real_inner_smul_left, HRS.MP.RdProp.rpk_J_inner,
    HRS.MP.RdProp.rpk_J_inner] at h
  exact h.symm

/-- The lift of `H^{-Γ}` into `H^{-q}`, `Γ ≤ q`: the Riesz representative of the restricted functional. -/
theorem sa9_exists_lift {Γ q : ℕ} (hΓq : Γ ≤ q) :
    ∃ ι : HNeg d (Γ : ℝ) → HNeg d (q : ℝ), ∀ (F : HNeg d (Γ : ℝ)) (φ : Euc d → ℝ),
      IsSobolevTest (q : ℝ) φ → HNeg.pairing φ (ι F) = HNeg.pairing φ F := by
  classical
  have hq : (Γ : ℝ) ≤ q := by exact_mod_cast hΓq
  have hex : ∀ F : HNeg d (Γ : ℝ), ∃ k : HNeg d (q : ℝ), ∀ φ : Euc d → ℝ,
      IsSobolevTest (q : ℝ) φ → HNeg.pairing φ k = HNeg.pairing φ F := by
    intro F
    refine HRS.MP.RdProp.rpk_exists_rep (fun φ => HNeg.pairing φ F) ‖F‖ ?_ ?_
    · intro φ φ' c hφ hφ'
      have hφΓ : IsSobolevTest (Γ : ℝ) φ := ⟨hφ.1, HRS.PDE.ToolboxRd.FourierAux.memSobolev_mono hq hφ.2⟩
      have hφΓ' : IsSobolevTest (Γ : ℝ) φ' := ⟨hφ'.1, HRS.PDE.ToolboxRd.FourierAux.memSobolev_mono hq hφ'.2⟩
      exact sa9_pairing_comb hφΓ hφΓ' c F
    · intro φ hφ
      have hφΓ : IsSobolevTest (Γ : ℝ) φ := ⟨hφ.1, HRS.PDE.ToolboxRd.FourierAux.memSobolev_mono hq hφ.2⟩
      exact (hneg_pairing_le hφΓ F).trans
        (mul_le_mul_of_nonneg_left (mrr_sobolevNorm_mono hq hφ.2) (norm_nonneg _))
  choose ι hι using hex
  exact ⟨ι, hι⟩

/-! ### The transported empirical initial field -/

section Initial

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ}
  {𝔈 : ℕ → ℝ} {q : ℕ} {Kad : ℝ}

theorem sa9_exists_Iq (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈)
    (hadj : AdjointDerivInput (q : ℝ) (mStar d) S.coeff S.T Kad) :
    ∃ Iq : ∀ N, ℝ → (R N).Ω → HNeg d (q : ℝ),
      (∀ N : ℕ, 1 ≤ N → ∀ t, Measurable (Iq N t)) ∧
      (∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ ζ, ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ →
        HNeg.pairing φ (Iq N t ζ) = S.sigma N *
          (HRS.Whole.pair (HRS.Whole.empirical ((R N).X 0 ζ)) (propagatorW (S.coeff N) 0 t φ) -
            HRS.Whole.pair S.μ0 (propagatorW (S.coeff N) 0 t φ))) := by
  classical
  have hT : 0 ≤ S.T := S.hT.le
  have hex : ∀ (N : ℕ) (t : ℝ) (ζ : (R N).Ω), ∃ k : HNeg d (q : ℝ), 1 ≤ N →
      ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ → HNeg.pairing φ k = S.sigma N *
          (HRS.Whole.pair (HRS.Whole.empirical ((R N).X 0 ζ)) (propagatorW (S.coeff N) 0 (mrrClamp S.T t) φ) -
            HRS.Whole.pair S.μ0 (propagatorW (S.coeff N) 0 (mrrClamp S.T t) φ)) := by
    intro N t ζ
    by_cases hN : 1 ≤ N
    · have hc := mrrClamp_mem hT t
      haveI := HRS.Whole.empirical_isProbabilityMeasure (show 0 < N from hN) ((R N).X 0 ζ)
      haveI := S.hμ0
      obtain ⟨k, hk⟩ := sa6_riesz_U hT (hadj N hN) hc.1 hc.2 (HRS.Whole.empirical ((R N).X 0 ζ)) S.μ0
        (S.sigma N)
      exact ⟨k, fun _ φ hφ => hk φ hφ⟩
    · exact ⟨0, fun h => absurd h hN⟩
  choose Iq hIq using hex
  refine ⟨fun N t ζ => Iq N t ζ, fun N hN t => ?_, fun N hN t ht ζ φ hφ => ?_⟩
  · refine mrm_measurable_of_pairings fun φ hφ => ?_
    have hc := mrrClamp_mem hT t
    have : (fun ζ => HNeg.pairing φ (Iq N t ζ)) = fun ζ => S.sigma N *
        (HRS.Whole.pair (HRS.Whole.empirical ((R N).X 0 ζ)) (propagatorW (S.coeff N) 0 (mrrClamp S.T t) φ) -
          HRS.Whole.pair S.μ0 (propagatorW (S.coeff N) 0 (mrrClamp S.T t) φ)) := by
      funext ζ; exact hIq N t ζ hN φ hφ
    rw [this]
    have hcont : Continuous (propagatorW (S.coeff N) 0 (mrrClamp S.T t) φ) :=
      ((hadj N hN 0 _ le_rfl hc.1 hc.2 φ hφ).2.1).continuous
    exact ((sa6_meas_pair_emp (show 0 < N from hN)
      (Q09A.selectedFlow_measurable (hS.flow N hN) 0) hcont).sub_const _).const_mul _
  · have := hIq N t ζ hN φ hφ
    rwa [mrrClamp_of_mem ht] at this

end Initial

/-! ### The decomposition -/

section Decomp

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}
  {Γ : ℕ} {Kad C₁ : ℝ}

theorem sa9_decomp (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 5) (Γ + 5) C₀ 𝔈)
    (hadj : AdjointDerivInput ((Γ + 2 : ℕ) : ℝ) (mStar d) S.coeff S.T Kad)
    (hker : ∀ N : ℕ, 1 ≤ N → KernelBoundRd (S.coeff N) S.T (Γ + 2) C₁)
    (Z : ∀ N, ℝ → (R N).Ω → HNeg d ((Γ + 2 : ℕ) : ℝ))
    (hZm : ∀ N : ℕ, 1 ≤ N → ∀ t, Measurable (Z N t))
    (hZp : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ ζ, ∀ φ : Euc d → ℝ,
      IsSobolevTest ((Γ + 2 : ℕ) : ℝ) φ → HNeg.pairing φ (Z N t ζ) = S.sigma N *
        (HRS.Whole.pair (HRS.Whole.empirical ((R N).X (Real.toNNReal t) ζ)) φ -
          HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N t)) φ)) :
    ∃ (ℱ : ∀ N, Filtration ℝ (R N).mΩ) (W' : ∀ N, ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ)
      (Iq Mq Rm : ∀ N, ℝ → (R N).Ω → HNeg d ((Γ + 2 : ℕ) : ℝ)),
      (∀ N : ℕ, 1 ≤ N → IsWholeFilteredSolution (R N).P (ℱ N) (W' N) (R N).W (R N).X) ∧
      (∀ N : ℕ, 1 ≤ N → IsStochConvW (R N).P (ℱ N) (W' N) (S.coeff N)
        (S.sigma N * Real.sqrt (2 * S.invβ N) / N) (Γ + 2) S.T (R N).X (fun _ => S.T) (Mq N)) ∧
      (∀ N : ℕ, 1 ≤ N → (∀ t, Measurable (Iq N t)) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ φ : Euc d → ℝ, IsSobolevTest ((Γ + 2 : ℕ) : ℝ) φ →
          ∀ᵐ ζ ∂(R N).P, HNeg.pairing φ (Iq N t ζ) = S.AN N * (S.κ N *
            (HRS.Whole.pair (HRS.Whole.empirical ((R N).X₀ ζ)) (propagatorW (S.coeff N) 0 t φ) -
              HRS.Whole.pair S.μ0 (propagatorW (S.coeff N) 0 t φ)))) ∧
      (∀ N : ℕ, 1 ≤ N → IsRemainderW S R N (Γ + 2) (Rm N)) ∧
      (∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ ζ, Rm N t ζ = Z N t ζ - Iq N t ζ - Mq N t ζ) := by
  classical
  obtain ⟨Iq, hIqm, hIqp⟩ := sa9_exists_Iq hS hadj
  choose ℱ W' hF using hS.filtered
  -- the kernel families
  have hKex : ∀ N : ℕ, ∃ Kern : Fin d → ℝ → ℝ → Euc d → HNeg d ((Γ + 2 : ℕ) : ℝ),
      1 ≤ N → MrmKern (S.coeff N) S.T (Γ + 2) |C₁| Kern := by
    intro N
    by_cases hN : 1 ≤ N
    · obtain ⟨K, hK⟩ := mrmKern_exists (S.coeff N) S.T (Γ + 2) C₁ (hker N hN)
      exact ⟨K, fun _ => hK⟩
    · exact ⟨fun _ _ _ _ => 0, fun h => absurd h hN⟩
  choose Kern hKern using hKex
  have hMex : ∀ N : ℕ, ∃ M : ℝ → (R N).Ω → HNeg d ((Γ + 2 : ℕ) : ℝ), 1 ≤ N →
      IsStochConvW (R N).P (ℱ N) (W' N) (S.coeff N) (S.sigma N * Real.sqrt (2 * S.invβ N) / N)
        (Γ + 2) S.T (R N).X (fun _ => S.T) M := by
    intro N
    by_cases hN : 1 ≤ N
    · obtain ⟨M, hM⟩ := mrm_exists_stochConv (hF N).brownian (hKern N hN) _ (fun _ => S.T) (R N).X
        (hF N).progressive (sa6_tau_prog (ℱ N) S.T)
      exact ⟨M, fun _ => hM⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hN⟩
  choose Mq hMq using hMex
  refine ⟨ℱ, W', Iq, Mq, fun N t ζ => if t ∈ Set.Icc (0 : ℝ) S.T then Z N t ζ - Iq N t ζ - Mq N t ζ else 0,
    fun N hN => hF N, hMq, fun N hN => ⟨hIqm N hN, fun t ht φ hφ => ?_⟩, fun N hN => ?_,
    fun N hN t ht ζ => by simp only [if_pos ht]⟩
  · have hX0eq : ∀ᵐ ζ ∂(R N).P, (R N).X 0 ζ = (R N).X₀ ζ := (flow_contact (hS.flow N hN)).1.init
    filter_upwards [hX0eq] with ζ h
    rw [hIqp N hN t ht ζ φ hφ, h, ← sa6_AN_mul_kappa S N]
    simp only [HRS.Whole.pair]
    ring
  · have hS' : RdStanding S R MB Λ ΛV G₀ m20 ((Γ + 2) + 3) ((Γ + 2) + 3) C₀ 𝔈 := hS
    refine ⟨fun t => ?_, fun t ht φ hφ => ?_⟩
    · by_cases ht : t ∈ Set.Icc (0 : ℝ) S.T
      · simp only [if_pos ht]
        exact ((hZm N hN t).sub (hIqm N hN t)).sub ((hMq N hN).1 t)
      · simp only [if_neg ht]; exact measurable_const
    · simp only [if_pos ht]
      obtain ⟨K₁, hK₁⟩ := sa6_kern_exists (hadj N hN)
      have key := sa6_pairing_identity hS' hadj hN ht (hF N) hK₁
        (Mq N) (fun φ hφ => (hMq N hN).2 t ht φ hφ) (fun ζ => Z N t ζ) (fun ζ => Iq N t ζ)
        (fun φ hφ => ae_of_all _ fun ζ => hZp N hN t ht ζ φ hφ)
        (fun φ hφ => ae_of_all _ fun ζ => hIqp N hN t ht ζ φ hφ) φ hφ
      exact key

end Decomp

end HRS.MS.MainRdPath
