import HRS.Whole.AppendixALemmas2
import HRS.MP.KernIncr
import HRS.Main.A9Aux2
import HRS.Main.A8PAux9

/-!
# Packet MPREM: `E sup_t ‖ℝ_N^t‖_{H^{-q_T}} ≤ C T σ_N 𝔈_N` on the torus (S.A.25)

Stage 1: the dual-norm bound from rational trigonometric tests, and the pathwise bound of the
remainder integral, uniform in the test function (the exceptional null set does not depend on the test).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MP.RemSup

open HRS HRS.PDE HRS.Main HRS.Main.A8P HRS.GF HRS.Uniform HRS.MP.KernIncr
open HRS.Whole.AppendixALemmas (qT HasContVersion IsRemainderT)

variable {d : ℕ}

/-! ### Dual norm from rational trigonometric tests -/

/-- the index set of the rational trigonometric polynomials -/
abbrev MrsIdx (d : ℕ) := Σ S : Finset (NonzeroLattice d), (S → ℚ)

/-- the real coefficient vector of a rational index -/
def mrsB (p : MrsIdx d) : NonzeroLattice d → ℝ :=
  fun k => if hk : k ∈ p.1 then ((p.2 ⟨k, hk⟩ : ℚ) : ℝ) else 0

instance : Countable (MrsIdx d) := by
  classical
  unfold MrsIdx
  infer_instance

theorem mrs_rat_approx (x : ℝ) (n : ℕ) : ∃ q : ℚ, |(q : ℝ) - x| < 1 / ((n : ℝ) + 1) := by
  obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show x < x + 1 / ((n : ℝ) + 1) by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith)
  refine ⟨q, ?_⟩
  rw [abs_lt]
  constructor <;> linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]

theorem mrs_norm_le_of_rat {m : ℝ} (F : NegSobolev d m) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ p : MrsIdx d, |NegSobolev.eval F (FieldSingAux.trigPoly p.1 (mrsB p))| ≤
      B * sobolevNorm m (FieldSingAux.trigPoly p.1 (mrsB p))) : ‖F‖ ≤ B := by
  classical
  refine mpk_norm_le_of_eval F B hB fun S b => ?_
  choose r hr using mrs_rat_approx
  let pn : ℕ → MrsIdx d := fun n => ⟨S, fun k => r (b k.1) n⟩
  have hb : ∀ k ∈ S, Tendsto (fun n => mrsB (pn n) k) atTop (𝓝 (b k)) := by
    intro k hk
    have e : ∀ n, mrsB (pn n) k = ((r (b k) n : ℚ) : ℝ) := by
      intro n
      simp [mrsB, pn, hk]
    simp_rw [e]
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [Real.dist_eq]
    exact (hr (b k) n).le
  have hev : Tendsto (fun n => NegSobolev.eval F (FieldSingAux.trigPoly (pn n).1 (mrsB (pn n)))) atTop
      (𝓝 (NegSobolev.eval F (FieldSingAux.trigPoly S b))) := by
    have : ∀ (c : NonzeroLattice d → ℝ), NegSobolev.eval F (FieldSingAux.trigPoly S c) =
        ∑ k ∈ S, NegSobolev.fourierCoeff F k * c k := fun c => mpk_eval_trigPoly F S c
    show Tendsto (fun n => NegSobolev.eval F (FieldSingAux.trigPoly S (mrsB (pn n)))) atTop _
    simp_rw [this]
    exact tendsto_finsetSum _ fun k hk => (hb k hk).const_mul _
  have hnm : Tendsto (fun n => sobolevNorm m (FieldSingAux.trigPoly (pn n).1 (mrsB (pn n)))) atTop
      (𝓝 (sobolevNorm m (FieldSingAux.trigPoly S b))) := by
    show Tendsto (fun n => sobolevNorm m (FieldSingAux.trigPoly S (mrsB (pn n)))) atTop _
    simp_rw [mpk_sobolevNorm_trigPoly]
    refine (Real.continuous_sqrt.tendsto _).comp ?_
    exact tendsto_finsetSum _ fun k hk => (((hb k hk).pow 2).const_mul _)
  exact le_of_tendsto_of_tendsto' hev.abs (hnm.const_mul B) fun n => h (pn n)

/-! ### The pathwise bound, uniform in the test -/

section Path

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

/-- The a.s. pathwise bound of the remainder integral, with a null set independent of `t` and `φ`
(transcription of `a8p_rem_ae`). -/
theorem mrs_rem_ae_all (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {C₀' Cq cT : ℝ} (hcom : A8CommSpec d S.s C₀' Cq) (hCq : 0 ≤ Cq) (hC : C₀' ≤ C₀) (hcT0 : 0 ≤ cT)
    (hcT : ∀ (M : Matrix (Fin d) (Fin d) ℝ), PDE.MatBound MB M → ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
      MemSobolev (PDE.mStar d : ℝ) ψ →
        HasTransportBound d S.s (gfb2_v M ψ) (cT * sobolevNorm (PDE.mStar d : ℝ) ψ)) :
    ∀ᵐ ω ∂(R N).P, ∀ t ∈ Set.Icc 0 S.T, ∀ φ : Torus d → ℝ, Continuous φ →
      MemSobolev (PDE.mStar d : ℝ) φ →
      |∫ r in (0 : ℝ)..t, flucInteraction (S.dyn N) (propagator (S.dyn N) (S.ρ N) r t φ)
          ((R N).X (Real.toNNReal r) ω) (S.ρ N r)| ≤
        (1 / 2) * (Cq * (cT * a8pK Λ₁ t φ)) * ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω := by
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hXc, hocc, -⟩ := a8p_flow_facts hS hN1
  obtain ⟨hint, -, -⟩ := a8p_energy_integral hS hN1 (C₀ := C₀) (Λ := Λ) hF.progressive
  have hΛ := a8p_Lam_ge_one hS
  have hcom' := hcom.mono hC hCq
  have hT0 : 0 ≤ S.T := S.hT.le
  have hten : ∀ᵐ ω ∂(R N).P, 0 ≤ ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω :=
    Eventually.of_forall fun ω => setIntegral_nonneg measurableSet_Icc fun r _ => a8pEn_nonneg S R N C₀ Λ r ω
  rcases hocc with hM0 | hocc
  · -- `M = 0`: the remainder vanishes
    filter_upwards [hten] with ω hω t ht φ hφc hφ
    have hK0 := a8pK_nonneg Λ₁ t φ
    have hcoef0 : 0 ≤ (1 / 2 : ℝ) * (Cq * (cT * a8pK Λ₁ t φ)) :=
      mul_nonneg (by norm_num) (mul_nonneg hCq (mul_nonneg hcT0 hK0))
    have : ∀ r, flucInteraction (S.dyn N) (propagator (S.dyn N) (S.ρ N) r t φ)
        ((R N).X (Real.toNNReal r) ω) (S.ρ N r) = 0 := fun r => a8p_flucInteraction_zero hM0 _ _ _
    simp only [this, intervalIntegral.integral_zero, abs_zero]
    exact mul_nonneg hcoef0 hω
  · filter_upwards [hocc, hint] with ω hω hωi t ht φ hφc hφ
    obtain ⟨hCk, hcl, hb⟩ := a8p_adj_pkg hspec hCa hS hN1 ht hφc hφ
    have hK0 := a8pK_nonneg Λ₁ t φ
    have hcoef0 : 0 ≤ (1 / 2 : ℝ) * (Cq * (cT * a8pK Λ₁ t φ)) :=
      mul_nonneg (by norm_num) (mul_nonneg hCq (mul_nonneg hcT0 hK0))
    have hnull : ∀ᵐ r ∂(volume : Measure ℝ),
        ¬ (r ∈ Set.Icc 0 S.T ∧ (R N).X (Real.toNNReal r) ω ∈ collisionSet d N) :=
      measure_eq_zero_iff_ae_notMem.1 hω
    have hrest : ∀ᵐ r ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
        ‖flucInteraction (S.dyn N) (propagator (S.dyn N) (S.ρ N) r t φ)
          ((R N).X (Real.toNNReal r) ω) (S.ρ N r)‖ ≤
        (1 / 2) * (Cq * (cT * a8pK Λ₁ t φ)) * a8pEn S R N C₀ Λ r ω := by
      refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
      filter_upwards [hnull] with r hr hrmem
      have hrt : r ∈ Set.Icc (0 : ℝ) t := ⟨hrmem.1.le, hrmem.2⟩
      have hrT : r ∈ Set.Icc (0 : ℝ) S.T := ⟨hrmem.1.le, hrmem.2.trans ht.2⟩
      have hcoll : (R N).X (Real.toNNReal r) ω ∉ collisionSet d N := fun h => hr ⟨hrT, h⟩
      obtain ⟨hmem, hnorm, -⟩ := hb r hrt
      have hCk2 : Torus.IsCk 2 (propagator (S.dyn N) (S.ρ N) r t φ) := hcl.c2 r hrt
      have hTB := hcT (S.dyn N).M hS.matrix_bound _ hCk2 hmem
      have hTB' : HasTransportBound d S.s (gfb2_v (S.dyn N).M (propagator (S.dyn N) (S.ρ N) r t φ))
          (cT * a8pK Λ₁ t φ) := by
        obtain ⟨L, F, hL, hF0, hlip, hfrac, hLK⟩ := hTB
        refine ⟨L, F, hL, hF0, hlip, hfrac, hLK.trans ?_⟩
        exact mul_le_mul_of_nonneg_left hnorm hcT0
      have hdens := (hS.mean_field.solution N hN1).density r hrT
      have hpt := a8p_rem_pointwise S.hd S.hs0 S.hsd hcom' hCq hΛ hN (D := S.dyn N) rfl hdens
        (fun x => a8p_rho_le hS hN1 hrT x) hCk2 hTB' _ hcoll
      rw [Real.norm_eq_abs]
      refine hpt.trans ?_
      have hge := a8pEn_ge S R N C₀ Λ r ω
      unfold correctedEnergy at hge
      exact mul_le_mul_of_nonneg_left hge (mul_nonneg (by norm_num) (mul_nonneg hCq (mul_nonneg hcT0 hK0)))
    have hIoc : IntegrableOn (fun r => a8pEn S R N C₀ Λ r ω) (Set.Ioc (0 : ℝ) t) :=
      hωi.mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl ht.2))
    rw [intervalIntegral.integral_of_le ht.1, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hIoc.const_mul _) hrest).trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hcoef0
    refine setIntegral_mono_set hωi (Eventually.of_forall fun r => a8pEn_nonneg S R N C₀ Λ r ω) ?_
    exact Eventually.of_forall fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩

end Path

/-! ### Supremum over the continuous version -/

theorem mrs_dense_closure {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    t ∈ closure (Set.Icc (0 : ℝ) T ∩ Set.range ((↑) : ℚ → ℝ)) := by
  have hd : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
  have h1 : Set.Ioo (0 : ℝ) T ⊆ closure (Set.Ioo (0 : ℝ) T ∩ Set.range ((↑) : ℚ → ℝ)) :=
    hd.open_subset_closure_inter isOpen_Ioo
  have h2 : Set.Icc (0 : ℝ) T = closure (Set.Ioo (0 : ℝ) T) := (closure_Ioo hT.ne).symm
  rw [h2] at ht
  have h3 : closure (Set.Ioo (0 : ℝ) T) ⊆ closure (Set.Ioo (0 : ℝ) T ∩ Set.range ((↑) : ℚ → ℝ)) := by
    simpa using closure_mono h1
  exact closure_mono (Set.inter_subset_inter_left _ Set.Ioo_subset_Icc_self) (h3 ht)

section Sup

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

/-- Generic form: from an a.s. pathwise bound of the remainder integral, uniform in the test, to the
a.s. bound of `sup_t ‖Rc_t‖` for the continuous version. -/
theorem mrs_sup_gen {N : ℕ} {Q cT Λ₁ : ℝ} (hQ0 : 0 ≤ Q) (hcT0 : 0 ≤ cT) (E : (R N).Ω → ℝ)
    (hE0 : ∀ᵐ ζ ∂(R N).P, 0 ≤ E ζ)
    (hpath : ∀ᵐ ω ∂(R N).P, ∀ t ∈ Set.Icc 0 S.T, ∀ φ : Torus d → ℝ, Continuous φ →
      MemSobolev (PDE.mStar d : ℝ) φ →
      |∫ r in (0 : ℝ)..t, flucInteraction (S.dyn N) (propagator (S.dyn N) (S.ρ N) r t φ)
          ((R N).X (Real.toNNReal r) ω) (S.ρ N r)| ≤
        (1 / 2) * (Q * (cT * a8pK Λ₁ t φ)) * E ω)
    (Rm Rc : ℝ → (R N).Ω → NegSobolev d ((qT d : ℕ) : ℝ))
    (hRem : IsRemainderT (R N).P (S.dyn N) (S.ρ N) (S.sigma N) ((qT d : ℕ) : ℝ) S.T (R N).X Rm)
    (hCont : HasContVersion S.T (R N).P Rm Rc) :
    ∀ᵐ ζ ∂(R N).P, ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ‖Rc t ζ‖ ≤ S.sigma N * ((1 / 2) * (Q * (cT * Real.exp (|Λ₁| * S.T)))) * E ζ := by
  have hT0 : 0 < S.T := S.hT
  have hσ := a8p_sigma_nonneg S N
  have hid : ∀ᵐ ζ ∂(R N).P, ∀ (q : ℚ) (p : MrsIdx d), (q : ℝ) ∈ Set.Icc (0 : ℝ) S.T →
      NegSobolev.eval (Rm q ζ) (FieldSingAux.trigPoly p.1 (mrsB p)) =
        S.sigma N * ∫ r in (0 : ℝ)..(q : ℝ), flucInteraction (S.dyn N)
          (propagator (S.dyn N) (S.ρ N) r q (FieldSingAux.trigPoly p.1 (mrsB p)))
          ((R N).X (Real.toNNReal r) ζ) (S.ρ N r) := by
    rw [ae_all_iff]; intro q
    rw [ae_all_iff]; intro p
    by_cases hq : (q : ℝ) ∈ Set.Icc (0 : ℝ) S.T
    · filter_upwards [hRem.2 q hq _ (mpk_test_trigPoly p.1 (mrsB p)).1
        (mpk_test_trigPoly p.1 (mrsB p)).2] with ζ hζ _ using hζ
    · exact Eventually.of_forall fun ζ h => absurd h hq
  have hRcRm : ∀ᵐ ζ ∂(R N).P, ∀ q : ℚ, (q : ℝ) ∈ Set.Icc (0 : ℝ) S.T → Rc q ζ = Rm q ζ := by
    rw [ae_all_iff]; intro q
    by_cases hq : (q : ℝ) ∈ Set.Icc (0 : ℝ) S.T
    · filter_upwards [hCont.1 q hq] with ζ hζ _ using hζ
    · exact Eventually.of_forall fun ζ h => absurd h hq
  filter_upwards [hpath, hid, hRcRm, hCont.2, hE0] with ζ h1 h2 h3 h4 h5
  set Kc : ℝ := (1 / 2) * (Q * (cT * Real.exp (|Λ₁| * S.T))) with hKc
  have hKc0 : 0 ≤ Kc := by
    have := Real.exp_pos (|Λ₁| * S.T)
    positivity
  have hB0 : 0 ≤ S.sigma N * Kc * E ζ := by positivity
  have hrat : ∀ q : ℚ, (q : ℝ) ∈ Set.Icc (0 : ℝ) S.T → ‖Rc q ζ‖ ≤ S.sigma N * Kc * E ζ := by
    intro q hq
    rw [h3 q hq]
    refine mrs_norm_le_of_rat _ _ hB0 fun p => ?_
    set φ := FieldSingAux.trigPoly p.1 (mrsB p) with hφ
    have hφt : MPKTest φ := mpk_test_trigPoly p.1 (mrsB p)
    have hφc : Continuous φ := mpk_cont_of_smooth hφt.1
    have hφm : MemSobolev (qT d : ℝ) φ := A33.a33_memSob _ hφt.1
    have hφm' : MemSobolev (PDE.mStar d : ℝ) φ := A33.a33_memSob _ hφt.1
    have hle : ((PDE.mStar d : ℕ) : ℝ) ≤ ((qT d : ℕ) : ℝ) := by
      have : PDE.mStar d ≤ qT d := by
        unfold HRS.Whole.AppendixALemmas.qT Main.gammaIdx; omega
      exact_mod_cast this
    have hnorm := a8p_sobolevNorm_mono hφm hle
    rw [h2 q p hq, abs_mul, abs_of_nonneg hσ]
    have hp := h1 q hq φ hφc hφm'
    have hK : a8pK Λ₁ q φ ≤ Real.exp (|Λ₁| * S.T) * sobolevNorm (qT d : ℝ) φ := by
      unfold a8pK
      have h0 : 0 ≤ sobolevNorm (PDE.mStar d : ℝ) φ := Real.sqrt_nonneg _
      calc Real.exp (|Λ₁| * q) * sobolevNorm (PDE.mStar d : ℝ) φ
          ≤ Real.exp (|Λ₁| * S.T) * sobolevNorm (PDE.mStar d : ℝ) φ :=
            mul_le_mul_of_nonneg_right (Real.exp_le_exp.2
              (mul_le_mul_of_nonneg_left hq.2 (abs_nonneg _))) h0
        _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le
    have hsn : 0 ≤ sobolevNorm (qT d : ℝ) φ := Real.sqrt_nonneg _
    calc S.sigma N * |∫ r in (0 : ℝ)..(q : ℝ), flucInteraction (S.dyn N)
          (propagator (S.dyn N) (S.ρ N) r q φ) ((R N).X (Real.toNNReal r) ζ) (S.ρ N r)|
        ≤ S.sigma N * ((1 / 2) * (Q * (cT * a8pK Λ₁ q φ)) * E ζ) :=
          mul_le_mul_of_nonneg_left hp hσ
      _ ≤ S.sigma N * ((1 / 2) * (Q * (cT * (Real.exp (|Λ₁| * S.T) * sobolevNorm (qT d : ℝ) φ))) * E ζ) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ h5) hσ
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK hcT0) hQ0)
            (by norm_num)
      _ = S.sigma N * Kc * E ζ * sobolevNorm (qT d : ℝ) φ := by rw [hKc]; ring
  intro t ht
  have hcn : ContinuousOn (fun t => ‖Rc t ζ‖) (Set.Icc (0 : ℝ) S.T) := h4.norm
  refine ContinuousWithinAt.closure_le (f := fun t => ‖Rc t ζ‖) (g := fun _ => S.sigma N * Kc * E ζ)
    (s := Set.Icc (0 : ℝ) S.T ∩ Set.range ((↑) : ℚ → ℝ)) (x := t)
    (mrs_dense_closure hT0 ht) ?_ continuousWithinAt_const ?_
  · exact (hcn t ht).mono Set.inter_subset_left
  · rintro y ⟨hy, q, rfl⟩
    exact hrat q hy

end Sup

/-! ### The case `N = 1` -/

section One

open HRS.CoercAux KernelAux Set

variable {s : ℝ}

theorem mrs_diag_const1 (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 1 ≤ N →
      gT d s (smearScale d N Λ ^ 2) 0 / (2 * N) + (1 + Λ) * nearB d s (smearScale d N Λ ^ 2) ≤
        oNΛ d s C₀ Λ N := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : 0 < ((d : ℝ) - s) / 2 := by linarith
  have hA := subA_nonneg_one hd hs0 hsd
  -- the `nearB` part
  have hnear : ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 1 ≤ N →
      (1 + Λ) * nearB d s (smearScale d N Λ ^ 2) ≤
        (2 * subA d s / (((d : ℝ) - s) / 2)) * (Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)) := by
    intro Λ hΛ N hN
    have hN1 : 1 ≤ N := hN
    have hΛ0 : 0 < Λ := by linarith
    have hB := nearB_nonneg hd hs0 hsd (ε := smearScale d N Λ ^ 2)
      (by have := smearScale_pos (d := d) hN1 hΛ0; positivity)
    rw [← smear_a_eq (s := s) hd hN1 hΛ0]
    unfold nearB at hB ⊢
    have : (1 + Λ) * (subA d s * ((smearScale d N Λ ^ 2) ^ (((d : ℝ) - s) / 2) / (((d : ℝ) - s) / 2))) ≤
        (2 * Λ) * (subA d s * ((smearScale d N Λ ^ 2) ^ (((d : ℝ) - s) / 2) / (((d : ℝ) - s) / 2))) :=
      mul_le_mul_of_nonneg_right (by linarith) hB
    refine this.trans (le_of_eq ?_)
    field_simp
  have hq : ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 1 ≤ N →
      0 < smearScale d N Λ ^ 2 ∧ smearScale d N Λ ^ 2 ≤ 1 := by
    intro Λ hΛ N hN
    have hN1 : 1 ≤ N := hN
    have hΛ0 : 0 < Λ := by linarith
    have hNΛ : 1 ≤ (N : ℝ) * Λ := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith
    have h1 := smearScale_pos (d := d) hN1 hΛ0
    have h2 : smearScale d N Λ ≤ 1 := by
      unfold smearScale
      exact Real.rpow_le_one_of_one_le_of_nonpos hNΛ (by
        have : (0:ℝ) < 1 / d := by positivity
        have e : -(1 : ℝ) / d = -(1 / d) := by ring
        rw [e]; linarith)
    exact ⟨by positivity, by nlinarith⟩
  by_cases hs : s = 0
  · subst hs
    obtain ⟨C, hC⟩ := gT_zero_le_zero (d := d) hd hd0
    refine ⟨max C 0 / 2 + 2 * subA d 0 / (((d : ℝ) - 0) / 2), by positivity, fun Λ hΛ N hN => ?_⟩
    have hN1 : 1 ≤ N := hN
    have hΛ0 : 0 < Λ := by linarith
    obtain ⟨hq0, hq1⟩ := hq Λ hΛ N hN
    have h1 := hC _ hq0 hq1
    rw [smear_log_eq hd hN1 hΛ0] at h1
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have h2 := hnear Λ hΛ N hN
    have hone : Λ ^ ((0 : ℝ) / d) = 1 := by rw [zero_div, Real.rpow_zero]
    have e : (N : ℝ) ^ ((0 : ℝ) / d - 1) = (N : ℝ)⁻¹ := by
      rw [zero_div, zero_sub, Real.rpow_neg_one]
    rw [hone, e] at h2
    have h3 : gT d 0 (smearScale d N Λ ^ 2) 0 / (2 * N) ≤
        Real.log (N * Λ) / (2 * d * N) + max C 0 / 2 * (N : ℝ)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      have : Real.log (N * Λ) / (2 * d * N) * (2 * N) = 1 / d * Real.log (N * Λ) := by
        field_simp
      have h4 : C ≤ max C 0 := le_max_left _ _
      have h5 : max C 0 / 2 * (N : ℝ)⁻¹ * (2 * N) = max C 0 := by field_simp
      calc gT d 0 (smearScale d N Λ ^ 2) 0 ≤ 1 / 2 * (2 / d * Real.log (N * Λ)) + C := h1
        _ ≤ 1 / d * Real.log (N * Λ) + max C 0 := by
            have : 1 / 2 * (2 / (d : ℝ) * Real.log (N * Λ)) = 1 / d * Real.log (N * Λ) := by ring
            rw [this]; linarith
        _ = _ := by rw [add_mul, this, h5]
    unfold oNΛ
    rw [if_pos rfl, hone, e]
    have h6 : (max C 0 / 2 + 2 * subA d 0 / (((d : ℝ) - 0) / 2)) * 1 * (N : ℝ)⁻¹ =
        max C 0 / 2 * (N : ℝ)⁻¹ + 2 * subA d 0 / (((d : ℝ) - 0) / 2) * (1 * (N : ℝ)⁻¹) := by ring
    rw [h6]
    linarith
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    obtain ⟨C, hC0, hC⟩ := gT_zero_le_pos hd hspos hsd
    refine ⟨C / 2 + 2 * subA d s / (((d : ℝ) - s) / 2), by positivity, fun Λ hΛ N hN => ?_⟩
    have hN1 : 1 ≤ N := hN
    have hΛ0 : 0 < Λ := by linarith
    obtain ⟨hq0, hq1⟩ := hq Λ hΛ N hN
    have h1 := hC _ hq0 hq1
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have h2 := hnear Λ hΛ N hN
    have h3 : gT d s (smearScale d N Λ ^ 2) 0 / (2 * N) ≤
        C / 2 * (Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)) := by
      rw [div_le_iff₀ (by positivity)]
      have h5 := smear_neg_eq (s := s) hd hN1 hΛ0
      have h6 : (smearScale d N Λ ^ 2) ^ (-s / 2) = (Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)) * N := by
        rw [← h5]; field_simp
      calc gT d s (smearScale d N Λ ^ 2) 0 ≤ C * (smearScale d N Λ ^ 2) ^ (-s / 2) := h1
        _ = C / 2 * (Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)) * (2 * N) := by rw [h6]; ring
    unfold oNΛ
    rw [if_neg hs, zero_add]
    have h7 : (C / 2 + 2 * subA d s / (((d : ℝ) - s) / 2)) * Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) =
        C / 2 * (Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)) +
          2 * subA d s / (((d : ℝ) - s) / 2) * (Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)) := by ring
    rw [h7]
    linarith

/-- For `N = 1` the corrected energy is nonnegative for a suitable completion constant. -/
theorem mrs_energy_nonneg_one (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ : ℝ, ∀ Λ : ℝ, 1 ≤ Λ → ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d 1, 0 ≤ rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ 1 := by
  obtain ⟨C₀, hC₀, hconst⟩ := mrs_diag_const1 hd hs0 hsd
  refine ⟨C₀, fun Λ hΛ ρ hρ hρΛ X => ?_⟩
  have hΛ0 : 0 < Λ := by linarith
  have hε : 0 < smearScale d 1 Λ ^ 2 := by
    have := smearScale_pos (d := d) (N := 1) le_rfl hΛ0; positivity
  haveI := isProb_withDensityReal hρ
  have hQ := Q_eq_tsum (c := HRS.CoercAux.cT d s (smearScale d 1 Λ ^ 2)) (by norm_num)
    ((summable_cT hd hs0 hsd hε).abs) X (withDensityReal ρ)
  have hX : X ∉ collisionSet d 1 := by
    rintro ⟨i, j, hij, -⟩
    exact hij (Subsingleton.elim i j)
  have hge := rieszEnergy_ge_aux hd hs0 hsd hε hρ hΛ0.le hρΛ (by norm_num) X hX
  have hc := hconst Λ hΛ 1 le_rfl
  have hQ' : Esq d s (smearScale d 1 Λ ^ 2) X (withDensityReal ρ) =
      (1 / ((1 : ℕ) : ℝ) ^ 2) * ∑ i, ∑ j, gT d s (smearScale d 1 Λ ^ 2) (X i - X j)
        - (2 / ((1 : ℕ) : ℝ)) * ∑ i, ∫ y, gT d s (smearScale d 1 Λ ^ 2) (X i - y) ∂(withDensityReal ρ)
        + ∫ x, ∫ y, gT d s (smearScale d 1 Λ ^ 2) (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ) :=
    hQ.symm
  have := Esq_nonneg hd hs0 hsd hε X (withDensityReal ρ)
  rw [hQ'] at this
  linarith

end One

section OneComm

/-- Crude bound of the interaction term for a single particle. -/
theorem mrs_one_comm (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (Λ : ℝ) (D : DynData d), D.s = s → ∀ ρ : Torus d → ℝ, IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ → ∀ K : ℝ,
      HasTransportBound d s (gfb2_v D.M ψ) K → ∀ X : Config d 1,
      |flucInteraction D ψ X ρ| ≤ (3 / 2) * (max Λ 0 * c) * K := by
  obtain ⟨C, hC0, hC⟩ := HRS.Commutator.commKernel_bound hd hs0 hsd
  have hgi : Integrable (fun z : Torus d => (‖z‖ ^ (-s) + 1)) volume :=
    (KernelGrad.integrable_norm_rpow_neg (by omega) hsd).add (integrable_const _)
  set I := ∫ z : Torus d, (‖z‖ ^ (-s) + 1) with hI
  have hI0 : 0 ≤ I := integral_nonneg fun z => by positivity
  refine ⟨C * I, mul_nonneg hC0 hI0, ?_⟩
  intro Λ D hDs ρ hρ hΛ ψ hψ K hTB X
  obtain ⟨L, F, hL, hF, hlip, hfrac, hLK⟩ := hTB
  have hLK' : L ≤ K := by
    by_cases h : s < d - 2
    · rw [if_pos h] at hLK; linarith
    · rw [if_neg h] at hLK; linarith
  have hOff := HRS.Commutator.offDiagIntegrable_of_lipschitz hd hs0 hsd hρ hΛ X hL hlip
  have hflu := gfb2_flucInteraction_eq D hψ X ρ (by
    intro i
    have := hOff.1 i
    simpa [hDs] using this)
  rw [hDs] at hflu
  set k := commKernel (periodicRieszGrad d s) (gfb2_v D.M ψ) with hk
  have hK0 : 0 ≤ C * L := mul_nonneg hC0 hL
  have hbound : ∀ x y : Torus d, |k x y| ≤ (C * L) * (‖x - y‖ ^ (-s) + 1) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      rw [hk]; unfold commKernel
      rw [if_pos rfl, abs_zero]
      exact mul_nonneg hK0 (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) zero_le_one)
    · have h1 := hC L (gfb2_v D.M ψ) hL hlip x y hxy
      have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
      have h2 : KernelGrad.tdist x y ^ (-s) ≤ ‖x - y‖ ^ (-s) := by
        rw [KernelGrad.tdist_eq_sub_zero]
        exact Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hz) (KernelGrad.norm_le_tdist _)
          (by linarith)
      calc |k x y| ≤ C * L * (KernelGrad.tdist x y ^ (-s) + 1) := h1
        _ ≤ (C * L) * (‖x - y‖ ^ (-s) + 1) := mul_le_mul_of_nonneg_left (by linarith) hK0
  have hgi' : ∀ x : Torus d, Integrable (fun y : Torus d => (C * L) * (‖x - y‖ ^ (-s) + 1)) volume :=
    fun x => (hgi.const_mul (C * L)).comp_sub_left x
  have hΛB : ∀ x, ρ x ≤ max Λ 0 := fun x => (hΛ x).trans (le_max_left _ _)
  have hB0 : 0 ≤ max Λ 0 := le_max_right _ _
  haveI := isProb_withDensityReal hρ
  set J : ℝ := max Λ 0 * (C * L * I) with hJ
  have hfib : ∀ x : Torus d, |∫ y, k x y ∂(withDensityReal ρ)| ≤ J := by
    intro x
    have h1 : |∫ y, k x y ∂(withDensityReal ρ)| ≤ ∫ y, |k x y| ∂(withDensityReal ρ) := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := withDensityReal ρ) (k x)
    have h2 : ∫ y, |k x y| ∂(withDensityReal ρ) ≤
        ∫ y, (C * L) * (‖x - y‖ ^ (-s) + 1) ∂(withDensityReal ρ) :=
      integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
        (HRS.Commutator.absConv_integrable_mu hΛB (hgi' x)) (Eventually.of_forall fun y => hbound x y)
    have h3 : ∫ y : Torus d, (C * L) * (‖x - y‖ ^ (-s) + 1)
        = ∫ z : Torus d, (C * L) * (‖z‖ ^ (-s) + 1) :=
      integral_sub_left_eq_self (fun z : Torus d => (C * L) * (‖z‖ ^ (-s) + 1)) volume x
    have h4 : ∫ z : Torus d, (C * L) * (‖z‖ ^ (-s) + 1) = C * L * I := by
      rw [integral_const_mul]
    have h5 := HRS.Commutator.absConv_integral_mu_le hΛB hB0
      (g := fun y : Torus d => (C * L) * (‖x - y‖ ^ (-s) + 1))
      (fun y => mul_nonneg hK0 (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) zero_le_one)) (hgi' x)
    rw [h3, h4] at h5
    exact h1.trans (h2.trans h5)
  have hdbl : |∫ x, ∫ y, k x y ∂(withDensityReal ρ) ∂(withDensityReal ρ)| ≤ J := by
    have := norm_integral_le_of_norm_le_const (μ := withDensityReal ρ)
      (f := fun x => ∫ y, k x y ∂(withDensityReal ρ)) (C := J)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfib x)
    simpa [Real.norm_eq_abs] using this
  have hcomm : |commQuantity d s (gfb2_v D.M ψ) X (withDensityReal ρ)| ≤ 3 * J := by
    have hz : ∀ i : Fin 1, (Finset.univ.erase i) = ∅ := fun i => by
      ext j; simp [Finset.mem_erase, Subsingleton.elim j i]
    have e : commQuantity d s (gfb2_v D.M ψ) X (withDensityReal ρ) =
        -(2 * ∫ y, k (X 0) y ∂(withDensityReal ρ)) + ∫ x, ∫ y, k x y ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
      unfold commQuantity commQuantityWith offDiagPairing
      simp only [hz, Finset.sum_empty, Finset.sum_const_zero, Fin.sum_univ_one, Nat.cast_one]
      rw [← hk]
      ring
    rw [e]
    have h1 := hfib (X 0)
    have h2 := abs_le.1 h1
    have h3 := abs_le.1 hdbl
    rw [abs_le]
    constructor <;> nlinarith [h2.1, h2.2, h3.1, h3.2]
  have hJK : J ≤ max Λ 0 * (C * I) * K := by
    rw [hJ]
    have : C * L * I ≤ C * K * I := by
      have := mul_le_mul_of_nonneg_left hLK' hC0
      exact mul_le_mul_of_nonneg_right this hI0
    calc max Λ 0 * (C * L * I) ≤ max Λ 0 * (C * K * I) := mul_le_mul_of_nonneg_left this hB0
      _ = _ := by ring
  rw [hflu, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith [hcomm, hJK]

end OneComm

/-! ### Cores for fixed `N` -/

theorem mrs_lint_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : Type*} [NormedAddCommGroup E]
    {T : ℝ} (Rc : ℝ → Ω → E) (B : Ω → ℝ)
    (h : ∀ᵐ ζ ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ‖Rc t ζ‖ ≤ B ζ) :
    ∫⁻ ζ, ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Rc t ζ‖ₑ ∂P ≤ ∫⁻ ζ, ENNReal.ofReal (B ζ) ∂P := by
  refine lintegral_mono_ae ?_
  filter_upwards [h] with ζ hζ
  refine iSup₂_le fun t ht => ?_
  rw [← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal (hζ t ht)

section Core

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

/-- Core estimate for one `N ≥ 2`. -/
theorem mrs_core2 (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {C₀' Cq cT : ℝ} (hcom : A8CommSpec d S.s C₀' Cq) (hCq : 0 ≤ Cq) (hC : C₀' ≤ C₀) (hcT0 : 0 ≤ cT)
    (hcT : ∀ (M : Matrix (Fin d) (Fin d) ℝ), PDE.MatBound MB M → ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
      MemSobolev (PDE.mStar d : ℝ) ψ →
        HasTransportBound d S.s (gfb2_v M ψ) (cT * sobolevNorm (PDE.mStar d : ℝ) ψ))
    (Rm Rc : ℝ → (R N).Ω → NegSobolev d ((qT d : ℕ) : ℝ))
    (hRem : IsRemainderT (R N).P (S.dyn N) (S.ρ N) (S.sigma N) ((qT d : ℕ) : ℝ) S.T (R N).X Rm)
    (hCont : HasContVersion S.T (R N).P Rm Rc) :
    ∫⁻ ζ, ⨆ t ∈ Set.Icc (0 : ℝ) S.T, ‖Rc t ζ‖ₑ ∂(R N).P ≤
      ENNReal.ofReal (((1 / 2) * (Cq * (cT * Real.exp (|Λ₁| * S.T)))) * S.T * S.sigma N * 𝔈 N) := by
  have hpath := mrs_rem_ae_all hspec hCa hS hN hF hcom hCq hC hcT0 hcT
  obtain ⟨-, hen, -⟩ := a8p_energy_integral hS (by omega) (C₀ := C₀) (Λ := Λ) hF.progressive
  have hσ := a8p_sigma_nonneg S N
  have hE0 : ∀ᵐ ζ ∂(R N).P, 0 ≤ ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ζ :=
    Eventually.of_forall fun ω => setIntegral_nonneg measurableSet_Icc fun r _ => a8pEn_nonneg S R N C₀ Λ r ω
  have hsup := mrs_sup_gen (S := S) (Λ₁ := Λ₁) hCq hcT0 _ hE0 hpath Rm Rc hRem hCont
  set Kc : ℝ := (1 / 2) * (Cq * (cT * Real.exp (|Λ₁| * S.T))) with hKc
  have hKc0 : 0 ≤ Kc := by
    have := Real.exp_pos (|Λ₁| * S.T)
    positivity
  refine (mrs_lint_le Rc _ hsup).trans ?_
  calc ∫⁻ ζ, ENNReal.ofReal (S.sigma N * Kc * ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ζ) ∂(R N).P
      = ∫⁻ ζ, ENNReal.ofReal (S.sigma N * Kc) *
            ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ζ) ∂(R N).P := by
        refine lintegral_congr fun ζ => ?_
        rw [ENNReal.ofReal_mul (mul_nonneg hσ hKc0)]
    _ = ENNReal.ofReal (S.sigma N * Kc) *
          ∫⁻ ζ, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ζ) ∂(R N).P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (S.sigma N * Kc) * ENNReal.ofReal (S.T * 𝔈 N) := by gcongr
    _ = ENNReal.ofReal (Kc * S.T * S.sigma N * 𝔈 N) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hσ hKc0)]
        congr 1
        ring

/-- Pathwise bound for one particle, uniform in everything. -/
theorem mrs_rem_all_one (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {c : ℝ} (hc0 : 0 ≤ c)
    (hone : ∀ (Λ' : ℝ) (D : DynData d), D.s = S.s → ∀ ρ : Torus d → ℝ, IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ') → ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ → ∀ K : ℝ,
      HasTransportBound d S.s (gfb2_v D.M ψ) K → ∀ X : Config d 1,
      |flucInteraction D ψ X ρ| ≤ (3 / 2) * (max Λ' 0 * c) * K)
    {cT : ℝ} (hcT0 : 0 ≤ cT)
    (hcT : ∀ (M : Matrix (Fin d) (Fin d) ℝ), PDE.MatBound MB M → ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
      MemSobolev (PDE.mStar d : ℝ) ψ →
        HasTransportBound d S.s (gfb2_v M ψ) (cT * sobolevNorm (PDE.mStar d : ℝ) ψ))
    (ω : (R 1).Ω) :
    ∀ t ∈ Set.Icc 0 S.T, ∀ φ : Torus d → ℝ, Continuous φ → MemSobolev (PDE.mStar d : ℝ) φ →
      |∫ r in (0 : ℝ)..t, flucInteraction (S.dyn 1) (propagator (S.dyn 1) (S.ρ 1) r t φ)
          ((R 1).X (Real.toNNReal r) ω) (S.ρ 1 r)| ≤
        (1 / 2) * ((3 * (max Λ 0 * c)) * (cT * a8pK Λ₁ t φ)) * S.T := by
  intro t ht φ hφc hφ
  obtain ⟨hCk, hcl, hb⟩ := a8p_adj_pkg hspec hCa hS (N := 1) le_rfl ht hφc hφ
  have hK0 := a8pK_nonneg Λ₁ t φ
  set Bd : ℝ := (3 / 2) * (max Λ 0 * c) * (cT * a8pK Λ₁ t φ) with hBd
  have hBd0 : 0 ≤ Bd := by positivity
  have hpt : ∀ r ∈ Set.uIoc (0 : ℝ) t, ‖flucInteraction (S.dyn 1) (propagator (S.dyn 1) (S.ρ 1) r t φ)
      ((R 1).X (Real.toNNReal r) ω) (S.ρ 1 r)‖ ≤ Bd := by
    intro r hr
    rw [Set.uIoc_of_le ht.1] at hr
    have hrt : r ∈ Set.Icc (0 : ℝ) t := ⟨hr.1.le, hr.2⟩
    have hrT : r ∈ Set.Icc (0 : ℝ) S.T := ⟨hr.1.le, hr.2.trans ht.2⟩
    obtain ⟨hmem, hnorm, -⟩ := hb r hrt
    have hCk2 : Torus.IsCk 2 (propagator (S.dyn 1) (S.ρ 1) r t φ) := hcl.c2 r hrt
    have hTB := hcT (S.dyn 1).M hS.matrix_bound _ hCk2 hmem
    have hTB' : HasTransportBound d S.s (gfb2_v (S.dyn 1).M (propagator (S.dyn 1) (S.ρ 1) r t φ))
        (cT * a8pK Λ₁ t φ) := by
      obtain ⟨L, F, hL, hF0, hlip, hfrac, hLK⟩ := hTB
      refine ⟨L, F, hL, hF0, hlip, hfrac, hLK.trans ?_⟩
      exact mul_le_mul_of_nonneg_left hnorm hcT0
    have hdens := (hS.mean_field.solution 1 le_rfl).density r hrT
    rw [Real.norm_eq_abs]
    exact hone Λ (S.dyn 1) rfl _ hdens (fun x => a8p_rho_le hS le_rfl hrT x) _ hCk2 _ hTB' _
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [Real.norm_eq_abs] at h
  refine h.trans ?_
  rw [sub_zero, abs_of_nonneg ht.1]
  have : Bd * t ≤ Bd * S.T := mul_le_mul_of_nonneg_left ht.2 hBd0
  refine this.trans (le_of_eq ?_)
  rw [hBd]; ring

/-- `𝔈 1 ≥ 1` once `C₀` is large. -/
theorem mrs_E_one_ge {C₀'' : ℝ}
    (hnn : ∀ Λ' : ℝ, 1 ≤ Λ' → ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ') →
      ∀ X : Config d 1, 0 ≤ rieszEnergy d S.s X (withDensityReal ρ) + oNΛ d S.s C₀'' Λ' 1)
    (hC : C₀'' + 1 ≤ C₀)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) : 1 ≤ 𝔈 1 := by
  have hΛ1 := a8p_Lam_ge_one hS
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) S.T := ⟨le_rfl, S.hT.le⟩
  have hbd := hS.energy.bound 1 le_rfl 0 h0
  have hdens := (hS.mean_field.solution 1 le_rfl).density 0 h0
  have hge : ∀ ω, (1 : ℝ) ≤ correctedEnergy (S.dyn 1) C₀ Λ (S.ρ 1) ((R 1).X (Real.toNNReal 0) ω) 0 := by
    intro ω
    have h1 := hnn Λ hΛ1 (S.ρ 1 0) hdens (fun x => a8p_rho_le hS le_rfl h0 x) ((R 1).X (Real.toNNReal 0) ω)
    unfold correctedEnergy
    have hexp : (1 : ℝ) ≤ Λ ^ (S.s / d) := Real.one_le_rpow hΛ1 (div_nonneg S.hs0 (Nat.cast_nonneg d))
    have e1 : oNΛ d S.s C₀ Λ 1 = oNΛ d S.s C₀'' Λ 1 + (C₀ - C₀'') * Λ ^ (S.s / d) := by
      unfold oNΛ
      simp only [Nat.cast_one, Real.one_rpow, mul_one]
      ring
    have h2 : (C₀ - C₀'') * Λ ^ (S.s / d) ≥ 1 := by nlinarith
    show (1 : ℝ) ≤ rieszEnergy d S.s _ _ + oNΛ d S.s C₀ Λ 1
    rw [e1]
    linarith
  have h1 : ∫⁻ ω, ENNReal.ofReal 1 ∂(R 1).P ≤ ∫⁻ ω, ENNReal.ofReal
      (correctedEnergy (S.dyn 1) C₀ Λ (S.ρ 1) ((R 1).X (Real.toNNReal 0) ω) 0) ∂(R 1).P :=
    lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hge ω)
  rw [lintegral_const, measure_univ, mul_one] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (hS.energy.pos 1 le_rfl).le).1 (h1.trans hbd)

/-- Core estimate for `N = 1`. -/
theorem mrs_core1 (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {c : ℝ} (hc0 : 0 ≤ c)
    (hone : ∀ (Λ' : ℝ) (D : DynData d), D.s = S.s → ∀ ρ : Torus d → ℝ, IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ') → ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ → ∀ K : ℝ,
      HasTransportBound d S.s (gfb2_v D.M ψ) K → ∀ X : Config d 1,
      |flucInteraction D ψ X ρ| ≤ (3 / 2) * (max Λ' 0 * c) * K)
    {cT : ℝ} (hcT0 : 0 ≤ cT)
    (hcT : ∀ (M : Matrix (Fin d) (Fin d) ℝ), PDE.MatBound MB M → ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
      MemSobolev (PDE.mStar d : ℝ) ψ →
        HasTransportBound d S.s (gfb2_v M ψ) (cT * sobolevNorm (PDE.mStar d : ℝ) ψ))
    (hE1 : 1 ≤ 𝔈 1)
    (Rm Rc : ℝ → (R 1).Ω → NegSobolev d ((qT d : ℕ) : ℝ))
    (hRem : IsRemainderT (R 1).P (S.dyn 1) (S.ρ 1) (S.sigma 1) ((qT d : ℕ) : ℝ) S.T (R 1).X Rm)
    (hCont : HasContVersion S.T (R 1).P Rm Rc) :
    ∫⁻ ζ, ⨆ t ∈ Set.Icc (0 : ℝ) S.T, ‖Rc t ζ‖ₑ ∂(R 1).P ≤
      ENNReal.ofReal (((1 / 2) * ((3 * (max Λ 0 * c)) * (cT * Real.exp (|Λ₁| * S.T)))) * S.T *
        S.sigma 1 * 𝔈 1) := by
  have hσ := a8p_sigma_nonneg S 1
  have hQ0 : 0 ≤ 3 * (max Λ 0 * c) := by positivity
  have hpath : ∀ᵐ ω ∂(R 1).P, ∀ t ∈ Set.Icc 0 S.T, ∀ φ : Torus d → ℝ, Continuous φ →
      MemSobolev (PDE.mStar d : ℝ) φ →
      |∫ r in (0 : ℝ)..t, flucInteraction (S.dyn 1) (propagator (S.dyn 1) (S.ρ 1) r t φ)
          ((R 1).X (Real.toNNReal r) ω) (S.ρ 1 r)| ≤
        (1 / 2) * ((3 * (max Λ 0 * c)) * (cT * a8pK Λ₁ t φ)) * (fun _ => S.T) ω :=
    Eventually.of_forall fun ω => mrs_rem_all_one hspec hCa hS hc0 hone hcT0 hcT ω
  have hsup := mrs_sup_gen (S := S) (Λ₁ := Λ₁) hQ0 hcT0 (fun _ => S.T)
    (Eventually.of_forall fun _ => S.hT.le) hpath Rm Rc hRem hCont
  set Kc : ℝ := (1 / 2) * ((3 * (max Λ 0 * c)) * (cT * Real.exp (|Λ₁| * S.T))) with hKc
  have hKc0 : 0 ≤ Kc := by
    have := Real.exp_pos (|Λ₁| * S.T)
    positivity
  refine (mrs_lint_le Rc _ hsup).trans ?_
  rw [lintegral_const, measure_univ, mul_one]
  refine ENNReal.ofReal_le_ofReal ?_
  have : 0 ≤ Kc * S.T * S.sigma 1 := by have := S.hT.le; positivity
  nlinarith

end Core

/-! ### The per-`N` lemma and the frozen theorem -/

open HRS.Whole.AppendixALemmas in
/-- **Per-`N` form of S.A.25 (torus), `N ≥ 2`.**  `C` and the threshold `C₀min` do not depend on `N`;
hypotheses only on the fixed `N`. -/
theorem path_remainder_torus_perN (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∃ C : ℝ, ∀ (S : Main.MainData d), S.s = s → S.T = T →
      ∀ (R : ∀ N, Main.Realization d N) (𝔈 : ℕ → ℝ),
        Main.TorusStanding S R Rg ν₀ MB Λ VB (Main.gammaIdx d) C₀ Cc 𝔈 →
        ∀ (N : ℕ), 2 ≤ N → ∀ (Rm Rc : ℝ → (R N).Ω → NegSobolev d ((qT d : ℕ) : ℝ)),
        IsRemainderT (R N).P (S.dyn N) (S.ρ N) (S.sigma N) ((qT d : ℕ) : ℝ) T (R N).X Rm →
        HasContVersion T (R N).P Rm Rc →
          ∫⁻ ζ, ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Rc t ζ‖ₑ ∂(R N).P ≤
            ENNReal.ofReal (C * T * S.sigma N * 𝔈 N) := by
  by_cases hok : 1 ≤ d ∧ 0 ≤ s ∧ s < d
  swap
  · exact ⟨0, fun Rg ν₀ MB Λ T VB C₀ Cc _ => ⟨0, fun S hs =>
      absurd ⟨S.hd, hs ▸ S.hs0, hs ▸ S.hsd⟩ hok⟩⟩
  obtain ⟨hd, hs0, hsd⟩ := hok
  obtain ⟨C₀', Cq, hC₀', hCq, hcom⟩ := a8p_commSpec hd hs0 hsd
  refine ⟨C₀', fun Rg ν₀ MB Λ T VB C₀ Cc hC => ?_⟩
  obtain ⟨Ca, Λ₁, hCa, hspec⟩ := a8p_adjSpec hd s hs0 hsd Rg MB Λ VB ν₀
  obtain ⟨cT, hcT0, hcT⟩ := a8p_transport_bound hd MB s hs0
  refine ⟨(1 / 2) * (Cq * (cT * Real.exp (|Λ₁| * T))), ?_⟩
  intro S hSs hST R 𝔈 hS N hN Rm Rc hRem hCont
  subst hSs hST
  have hSm := A9.a9_standing_mStar hS
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N (by omega)
  exact mrs_core2 hspec hCa.le hSm hN hF hcom hCq.le hC hcT0 hcT Rm Rc hRem hCont

open HRS.Whole.AppendixALemmas in
theorem path_remainder_torus_proof (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∃ C : ℝ, ∀ (S : Main.MainData d), S.s = s → S.T = T →
      ∀ (R : ∀ N, Main.Realization d N) (𝔈 : ℕ → ℝ),
        Main.TorusStanding S R Rg ν₀ MB Λ VB (Main.gammaIdx d) C₀ Cc 𝔈 →
        ∀ (Rm Rc : ∀ N, ℝ → (R N).Ω → NegSobolev d ((qT d : ℕ) : ℝ)),
        (∀ N : ℕ, 1 ≤ N → IsRemainderT (R N).P (S.dyn N) (S.ρ N) (S.sigma N) ((qT d : ℕ) : ℝ) T
          (R N).X (Rm N)) →
        (∀ N : ℕ, 1 ≤ N → HasContVersion T (R N).P (Rm N) (Rc N)) →
        (∀ N : ℕ, 1 ≤ N →
          ∫⁻ ζ, ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Rc N t ζ‖ₑ ∂(R N).P ≤
            ENNReal.ofReal (C * T * S.sigma N * 𝔈 N)) ∧
        Tendsto (fun N => C * T * S.sigma N * 𝔈 N) atTop (𝓝 0) := by
  by_cases hok : 1 ≤ d ∧ 0 ≤ s ∧ s < d
  swap
  · exact ⟨0, fun Rg ν₀ MB Λ T VB C₀ Cc _ => ⟨0, fun S hs =>
      absurd ⟨S.hd, hs ▸ S.hs0, hs ▸ S.hsd⟩ hok⟩⟩
  obtain ⟨hd, hs0, hsd⟩ := hok
  obtain ⟨C₀', Cq, hC₀', hCq, hcom⟩ := a8p_commSpec hd hs0 hsd
  obtain ⟨C₀'', hnn⟩ := mrs_energy_nonneg_one hd hs0 hsd
  obtain ⟨c, hc0, hone⟩ := mrs_one_comm hd hs0 hsd
  refine ⟨max C₀' (C₀'' + 1), fun Rg ν₀ MB Λ T VB C₀ Cc hC => ?_⟩
  have hC1 : C₀' ≤ C₀ := (le_max_left _ _).trans hC
  have hC2 : C₀'' + 1 ≤ C₀ := (le_max_right _ _).trans hC
  obtain ⟨Ca, Λ₁, hCa, hspec⟩ := a8p_adjSpec hd s hs0 hsd Rg MB Λ VB ν₀
  obtain ⟨cT, hcT0, hcT⟩ := a8p_transport_bound hd MB s hs0
  have hex := Real.exp_pos (|Λ₁| * T)
  have hK2 : 0 ≤ (1 / 2) * (Cq * (cT * Real.exp (|Λ₁| * T))) := by positivity
  have hK1 : 0 ≤ (1 / 2) * ((3 * (max Λ 0 * c)) * (cT * Real.exp (|Λ₁| * T))) := by positivity
  refine ⟨max ((1 / 2) * (Cq * (cT * Real.exp (|Λ₁| * T))))
    ((1 / 2) * ((3 * (max Λ 0 * c)) * (cT * Real.exp (|Λ₁| * T)))), ?_⟩
  intro S hSs hST R 𝔈 hS Rm Rc hRem hCont
  subst hSs hST
  have hSm := A9.a9_standing_mStar hS
  refine ⟨fun N hN => ?_, ?_⟩
  · have hσ := a8p_sigma_nonneg S N
    have hE := (hS.energy.pos N hN).le
    have hTσE : 0 ≤ S.T * S.sigma N * 𝔈 N := by have := S.hT.le; positivity
    rcases Nat.lt_or_ge N 2 with h1 | h2
    · have hN1 : N = 1 := by omega
      subst hN1
      have hE1 := mrs_E_one_ge hnn hC2 hSm
      refine (mrs_core1 hspec hCa.le hSm hc0 hone hcT0 hcT hE1 (Rm 1) (Rc 1) (hRem 1 le_rfl)
        (hCont 1 le_rfl)).trans (ENNReal.ofReal_le_ofReal ?_)
      have := le_max_right ((1 / 2) * (Cq * (cT * Real.exp (|Λ₁| * S.T))))
        ((1 / 2) * ((3 * (max Λ 0 * c)) * (cT * Real.exp (|Λ₁| * S.T))))
      calc _ = ((1 / 2) * ((3 * (max Λ 0 * c)) * (cT * Real.exp (|Λ₁| * S.T)))) * (S.T * S.sigma 1 * 𝔈 1) := by ring
        _ ≤ _ := by rw [mul_assoc _ S.T]; nlinarith [mul_le_mul_of_nonneg_right this hTσE]
    · obtain ⟨ℱ, W', hF⟩ := hS.filtered N (by omega)
      refine (mrs_core2 hspec hCa.le hSm h2 hF hcom hCq.le hC1 hcT0 hcT (Rm N) (Rc N) (hRem N hN)
        (hCont N hN)).trans (ENNReal.ofReal_le_ofReal ?_)
      have := le_max_left ((1 / 2) * (Cq * (cT * Real.exp (|Λ₁| * S.T))))
        ((1 / 2) * ((3 * (max Λ 0 * c)) * (cT * Real.exp (|Λ₁| * S.T))))
      nlinarith [mul_le_mul_of_nonneg_right this hTσE]
  · have := (hS.energy.small).const_mul (max ((1 / 2) * (Cq * (cT * Real.exp (|Λ₁| * S.T))))
      ((1 / 2) * ((3 * (max Λ 0 * c)) * (cT * Real.exp (|Λ₁| * S.T)))) * S.T)
    rw [mul_zero] at this
    refine this.congr fun N => ?_
    ring

example := (@path_remainder_torus_proof : type_of% @HRS.Whole.AppendixALemmas.path_remainder_torus)

end HRS.MP.RemSup
