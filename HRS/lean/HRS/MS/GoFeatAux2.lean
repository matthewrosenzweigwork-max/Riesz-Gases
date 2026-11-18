import HRS.MS.GoFeatAux1
import HRS.MS.AdjSubTie
import HRS.MH.CommSuperCS10

/-!
# S5.5, the commutator bound `general_orbits_commutator` (assembly)

* `s55_sharp_all_sub_of_decay_and_tail`: the conditional statement `HRS.MS.SuppU15.sharp_all_sub_of_decay_and_tail_proof`
  (S4.14) with the additional output `0 ≤ C` (its proof gives `C = Csub * (...)` with `Csub > 0`; the frozen
  statement forgets the sign, which is needed here to compare the energies `F + o_N` at two completion constants).
  The proof is that of the merged theorem.
* `s55_sharp_all_sub_pos`: `sharp_all_sub` with `0 ≤ C`, from `adjoint_decay_proof` and `sharp_tail_bound_proof`
  (as in `AdjSubTie.lean`).
* `general_orbits_commutator_proof`: branch A (`s < d-2`): `s55_sharp_all_sub_pos` at `φ = oscTestFun m α` with
  `s55_adjointDecayHyp` (`GoCommAux1`) and the oscillator bounds `s55_osc_bounds` (`GoFeatAux1`);
  branch B (`s ≥ d-2`): `whole_commutator_super` for the transport `Mᵀ∇U(r,t)φ`, which is Lipschitz with constant
  `‖Mᵀ‖ cbNorm_{k+1}(U φ) ≤ ‖Mᵀ‖ K ‖φ‖_ul` (`UlAdjointInput`).  In both branches the completion constant of
  the conclusion is converted from `oNΛ`/`oN` at the constant of the cited theorem to `oN` at any larger
  `b.C₀` (`C₀min`), using that `F + o_N` is nonnegative at `b.C₀` (`WholeSetup.energy_nonneg`) and that `o_N` is
  nondecreasing in its constant.  Helper names carry the prefix `s55_`; namespace `HRS.MS.Go`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Go

open HRS.Whole HRS.MS.SuppU15

variable {d : ℕ}

theorem s55_sharp_all_sub_of_decay_and_tail (hd : 2 ≤ d) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) (s : ℝ)
    (M Q : Matrix (Fin d) (Fin d) ℝ) (c : Euc d) (T νstar : ℝ) (k : ℕ) (L Λ K : ℝ)
    (hs : s < (d : ℝ) - 2) (hk : ((d : ℝ) + 1) / 2 + 1 < k)
    (hAD : ∃ C : ℝ, ∀ (ν : ℝ) (ρ : ℝ → Euc d → ℝ), AdjointDecayHyp θ s M Q c T νstar k L Λ K ν ρ →
      ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Euc d → ℝ,
        ContDiff ℝ ((k + 2 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) φ →
        ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ < ⊤ →
        ContDiff ℝ k (propagatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) r t φ) ∧
        decayNormE k (s + 1) (propagatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) r t φ) ≤
          ENNReal.ofReal C * (decayNormE k (s + 1) φ +
            ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ))
    (hST : 0 ≤ s → ∃ C : ℝ, ∀ f : Euc d → ℝ, ContDiff ℝ k f → decayNormE k (s + 1) f < ⊤ →
      ∃ w : Fin d → Euc d → ℝ,
        (∀ i, IsFracDerivRep (((d : ℝ) + 1) / 2) (fun x => gradient f x i) (w i)) ∧
        (∀ i, MemLp (w i) (ENNReal.ofReal (2 * d / (((d : ℝ) + 1) - 2))) volume) ∧
        (⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 2 f x‖) +
          ∑ i, eLpNorm (w i) (ENNReal.ofReal (2 * d / (((d : ℝ) + 1) - 2))) volume ≤
            ENNReal.ofReal C * decayNormE k (s + 1) f) :
    ∃ C₀ C : ℝ, 0 ≤ C ∧ ∀ (ν : ℝ) (ρ : ℝ → Euc d → ℝ), AdjointDecayHyp θ s M Q c T νstar k L Λ K ν ρ →
      ∀ (N : ℕ), 2 ≤ N → ∀ X : EucConfig d N, Function.Injective X →
      ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Euc d → ℝ,
        ContDiff ℝ ((k + 2 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) φ →
        decayNormE k (s + 1) φ < ⊤ → ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ < ⊤ →
        |commN d s (fun x => Torus.matVec M.transpose
              (gradient (propagatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) r t φ) x))
            X (HRS.Whole.withDensityReal (ρ r))| ≤
          C * ((decayNormE k (s + 1) φ).toReal +
              (ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ).toReal) *
            (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (ρ r)) + oN d s C₀ N) := by
  by_cases hs0 : 0 ≤ s
  swap
  · exact ⟨0, 0, le_rfl, fun ν ρ hyp => absurd hyp.s_range.1 hs0⟩
  by_cases hL : (d : ℝ) + 1 < L
  swap
  · refine ⟨0, 0, le_rfl, fun ν ρ hyp => ?_⟩
    exfalso; apply hL
    have h1 := hyp.L_range
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  obtain ⟨CAD, hAD'⟩ := hAD
  obtain ⟨CST, hST'⟩ := hST hs0
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hk2 : 2 ≤ k := by
    have h1 : (2 : ℝ) < k := by linarith
    have h2 : (2 : ℕ) < k := by exact_mod_cast h1
    omega
  obtain ⟨Lm, hLm⟩ := u15_logmoment hL Λ
  have ha : (d : ℝ) < (d : ℝ) + 1 ∧ (d : ℝ) + 1 < (d : ℝ) + 2 := ⟨by linarith, by linarith⟩
  obtain ⟨C₀', Csub, hC₀', hCsub, H⟩ :=
    HRS.Commutator.Whole.whole_commutator_sub_sharp_of_subcoulomb hs0 hs ((d : ℝ) + 1) ha Lm
  have hcM0 : 0 ≤ u15_cM M.transpose := u15_cM_nonneg _
  refine ⟨C₀' * (max Λ 1) ^ (s / d) + Real.log (max Λ 1) / (2 * d),
    Csub * (u15_cM M.transpose * max CST 0 * max CAD 0),
    mul_nonneg hCsub.le (mul_nonneg (mul_nonneg hcM0 (le_max_right _ _)) (le_max_right _ _)), ?_⟩
  intro ν ρ hyp N hN X hX r t hr hrt htT φ hφ hdec hul
  obtain ⟨hcd, hdecf⟩ := hAD' ν ρ hyp r t hr hrt htT φ hφ hul
  set f := propagatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) r t φ with hf
  have hdecf' : decayNormE k (s + 1) f < ⊤ :=
    lt_of_le_of_lt hdecf (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨hdec, hul⟩))
  obtain ⟨w, hw1, hw2, hw3⟩ := hST' f hcd hdecf'
  have hSne : ((⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 2 f x‖) +
      ∑ i, eLpNorm (w i) (ENNReal.ofReal (2 * d / (((d : ℝ) + 1) - 2))) volume) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdecf'.ne) hw3
  have hp : 1 ≤ 2 * (d : ℝ) / (((d : ℝ) + 1) - 2) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hf2 : ContDiff ℝ 2 f := hcd.of_le (by exact_mod_cast hk2)
  have hTr := u15_transport M.transpose hp hf2 hw1 hw2 hSne
  -- the numeric bound on the constant
  have hSle : ((⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 2 f x‖) +
      ∑ i, eLpNorm (w i) (ENNReal.ofReal (2 * d / (((d : ℝ) + 1) - 2))) volume).toReal ≤
      max CST 0 * (decayNormE k (s + 1) f).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdecf'.ne) hw3
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal'] at this
  have hdle : (decayNormE k (s + 1) f).toReal ≤
      max CAD 0 * ((decayNormE k (s + 1) φ).toReal +
        (ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ).toReal) := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.2 ⟨hdec.ne, hul.ne⟩)) hdecf
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal', ENNReal.toReal_add hdec.ne hul.ne] at this
  set S' := (decayNormE k (s + 1) φ).toReal + (ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ).toReal with hS'
  have hS'0 : 0 ≤ S' := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hKle : u15_cM M.transpose * ((⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ 2 f x‖) +
      ∑ i, eLpNorm (w i) (ENNReal.ofReal (2 * d / (((d : ℝ) + 1) - 2))) volume).toReal ≤
      u15_cM M.transpose * max CST 0 * max CAD 0 * S' := by
    calc _ ≤ u15_cM M.transpose * (max CST 0 * (max CAD 0 * S')) :=
          mul_le_mul_of_nonneg_left (hSle.trans (mul_le_mul_of_nonneg_left hdle (le_max_right _ _))) hcM0
      _ = _ := by ring
  have hv := u15_hasFrac_mono hTr hKle
  -- the density
  obtain ⟨hprob, -, hwt⟩ := hyp.density r ⟨hr, hrt.trans htT⟩
  have hL0 : (0 : ℝ) ≤ L := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hb0 : ∀ x, jbracket x ^ L * |ρ r x| ≤ max Λ 0 := u15_weighted_zero hwt
  have hρle : ∀ x, ρ r x ≤ max Λ 1 := fun x =>
    (u15_dens_le hL0 hprob.nonneg hb0 x).trans (max_le_max le_rfl zero_le_one)
  have hlog : s = 0 → HRS.Whole.HasLogMoment (HRS.Whole.withDensityReal (ρ r)) Lm :=
    fun _ => hLm (ρ r) hprob hb0
  obtain ⟨-, hb⟩ := H (max Λ 1) (le_max_right _ _) N hN (ρ r) hprob hρle hlog X hX _ _ hv
  have hd1 : 1 ≤ d := by omega
  have hoN := u15_oNΛ_le hd1 hs0 C₀' (max Λ 1) (le_max_right _ _) (N := N) (by omega)
  have hnn : 0 ≤ Csub * (u15_cM M.transpose * max CST 0 * max CAD 0 * S') :=
    mul_nonneg hCsub.le (mul_nonneg (mul_nonneg (mul_nonneg hcM0 (le_max_right _ _)) (le_max_right _ _)) hS'0)
  calc _ ≤ _ := hb
    _ ≤ Csub * (u15_cM M.transpose * max CST 0 * max CAD 0 * S') *
          (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (ρ r)) +
            oN d s (C₀' * (max Λ 1) ^ (s / d) + Real.log (max Λ 1) / (2 * d)) N) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hoN _) hnn
    _ = _ := by ring




theorem s55_sharp_all_sub_pos : ∀ {d : ℕ}, 2 ≤ d → ∀ (θ : Euc d → ℝ), IsUlCutoff θ → ∀ (s : ℝ)
    (M Q : Matrix (Fin d) (Fin d) ℝ) (c : Euc d) (T νstar : ℝ) (k : ℕ) (L Λ K : ℝ),
    s < (d : ℝ) - 2 → ((d : ℝ) + 1) / 2 + 1 < k →
    ∃ C₀ C : ℝ, 0 ≤ C ∧ ∀ (ν : ℝ) (ρ : ℝ → Euc d → ℝ), AdjointDecayHyp θ s M Q c T νstar k L Λ K ν ρ →
      ∀ (N : ℕ), 2 ≤ N → ∀ X : EucConfig d N, Function.Injective X →
      ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Euc d → ℝ,
        ContDiff ℝ ((k + 2 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) φ →
        decayNormE k (s + 1) φ < ⊤ → ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ < ⊤ →
        |commN d s (fun x => Torus.matVec M.transpose
              (gradient (propagatorW ((⟨s, M, quadV Q c, ν⟩ : WholeDyn d).coeff ρ) r t φ) x))
            X (HRS.Whole.withDensityReal (ρ r))| ≤
          C * ((decayNormE k (s + 1) φ).toReal +
              (ulNormE (k + 2 + ⌈(d : ℝ) / 2⌉₊) θ φ).toReal) *
            (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (ρ r)) + oN d s C₀ N) := by
  intro d hd θ hθ s M Q c T νstar k L Λ K hs hk
  have hk2 : 2 ≤ k := by
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have h1 : (2 : ℝ) < k := by linarith
    have h2 : (2 : ℕ) < k := by exact_mod_cast h1
    omega
  refine s55_sharp_all_sub_of_decay_and_tail hd θ hθ s M Q c T νstar k L Λ K hs hk
    (HRS.MS.AdjDecay.adjoint_decay_proof hd θ hθ s M Q c T νstar k hk2 L Λ K) (fun hs0 => ?_)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ha : (d : ℝ) < (d : ℝ) + 1 ∧ (d : ℝ) + 1 < (d : ℝ) + 2 := ⟨by linarith, by linarith⟩
  exact sharp_tail_bound_proof hd ((d : ℝ) + 1) s k ha hk hs0

lemma s55_oN_mono (s : ℝ) {C₁ C₂ : ℝ} (h : C₁ ≤ C₂) (N : ℕ) : oN d s C₁ N ≤ oN d s C₂ N := by
  unfold oN
  have : 0 ≤ (N : ℝ) ^ (s / d - 1) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  nlinarith

lemma s55_grad_lip_cb {f : Euc d → ℝ} (hf : MemCb 2 f) (x y : Euc d) :
    ‖gradient f x - gradient f y‖ ≤ HRS.cbNorm 2 f * ‖x - y‖ := by
  have hL : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ HRS.cbNorm 2 f := by
    intro z
    have h0 : ‖iteratedFDeriv ℝ 2 f z‖ ≤ ⨆ w : Euc d, ‖iteratedFDeriv ℝ 2 f w‖ :=
      le_ciSup (hf.2 2 le_rfl) z
    refine h0.trans ?_
    unfold HRS.cbNorm
    exact Finset.single_le_sum (f := fun j => ⨆ w : Euc d, ‖iteratedFDeriv ℝ j f w‖)
      (fun j _ => Real.iSup_nonneg fun w => norm_nonneg _) (Finset.mem_range.2 (by norm_num))
  have hb : ∀ z ∈ (Set.univ : Set (Euc d)), ‖fderiv ℝ (gradient f) z‖ ≤ HRS.cbNorm 2 f := by
    intro z _
    refine (HRS.MH.DualityRd.db1_fderiv_gradient_le hf.1 z).trans ?_
    have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := z) (n := 1)
    have h2 := norm_iteratedFDeriv_one (𝕜 := ℝ) (x := z) (fderiv ℝ f)
    rw [← h2, h1]
    exact hL z
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => HRS.MH.DualityRd.db1_gradient_differentiable hf.1 z) hb convex_univ (Set.mem_univ x)
    (Set.mem_univ y)
  rw [norm_sub_rev (gradient f x), norm_sub_rev x y]
  exact h

lemma s55_cb_mono {f : Euc d → ℝ} {j n : ℕ} (hjn : j ≤ n) : HRS.cbNorm j f ≤ HRS.cbNorm n f := by
  unfold HRS.cbNorm
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
    fun i _ _ => Real.iSup_nonneg fun w => norm_nonneg _


lemma s55_cd_of_inf {f : Euc d → ℝ} (n : ℕ) (h : ContDiff ℝ ∞ f) : ContDiff ℝ (n : WithTop ℕ∞) f :=
  h.of_le (by exact_mod_cast le_top)

lemma s55_toReal_le {a : ℝ≥0∞} {B : ℝ} (hB : 0 ≤ B) (h : a ≤ ENNReal.ofReal B) : a.toReal ≤ B := by
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal hB] at this

theorem general_orbits_commutator_proof : type_of% @HRS.Whole.general_orbits_commutator := by
  intro d b₀ hb
  have hd2 : 2 ≤ d := hb.hd
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd2
  have hs0 := hb.hs0
  have hsd := hb.hsd
  have hL := hb.hL
  have hk := hb.hk
  have hk0 : (0 : ℝ) ≤ b₀.k := Nat.cast_nonneg _
  have hk2 : 2 ≤ b₀.k := by
    have h1 : (2 : ℝ) < b₀.k := by linarith
    exact_mod_cast h1.le
  have hL1 : (d : ℝ) + 1 < b₀.L := by linarith
  have hL0 : (0 : ℝ) ≤ b₀.L := by linarith
  have hceil : ⌈(d : ℝ) / 2⌉₊ ≤ d := Nat.ceil_le.2 (by linarith)
  have hr0 : b₀.k + 2 + ⌈(d : ℝ) / 2⌉₊ ≤ b₀.J := by unfold WholeBounds.J; omega
  have hceil2 : ⌈(b₀.s + 1 + b₀.k) / 2⌉₊ ≤ d + b₀.k + 1 := by
    apply Nat.ceil_le.2; push_cast; linarith
  have hkJ : b₀.k + 2 * ⌈(b₀.s + 1 + b₀.k) / 2⌉₊ ≤ b₀.J := by unfold WholeBounds.J; omega
  obtain ⟨Cosc, hCosc0, hosc⟩ := s55_osc_bounds hb.hθ b₀.m (b₀.k + 2 + ⌈(d : ℝ) / 2⌉₊) b₀.k
    (b₀.s + 1) (by linarith) b₀.J hr0 hkJ
  by_cases hsA : b₀.s < (d : ℝ) - 2
  · -- branch A: `s < d - 2`
    have hkA : ((d : ℝ) + 1) / 2 + 1 < b₀.k := by linarith
    obtain ⟨C₀A, CA, hCA0, hA⟩ := s55_sharp_all_sub_pos hd2 b₀.θ hb.hθ b₀.s b₀.M b₀.Q b₀.c b₀.T
      b₀.νstar b₀.k b₀.L b₀.Λ b₀.K hsA hkA
    refine ⟨C₀A, fun b hbeq hC0 => ?_⟩
    obtain ⟨c, rfl⟩ : ∃ c, b = { b₀ with C₀ := c } := ⟨b.C₀, hbeq⟩
    have hbv : ({ b₀ with C₀ := c } : WholeBounds d).Valid :=
      ⟨hb.hd, hb.hs0, hb.hsd, hb.hT, hb.hQ, hb.hθ, hb.hk, hb.hm, hb.hL, hb.hν⟩
    refine ⟨CA * (2 * Cosc), fun S N hN X hX r t hr hrt htT α => ?_⟩
    have hyp := s55_adjointDecayHyp ({ b₀ with C₀ := c } : WholeBounds d) hbv hsA.le S N
    obtain ⟨hφd, hul, hdec⟩ := hosc α
    have hφ : ContDiff ℝ ((b₀.k + 2 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) (oscTestFun b₀.m α) :=
      s55_cd_of_inf _ hφd
    have hEpos : 0 ≤ oscEigenvalue d α ^ (((b₀.J : ℝ) - b₀.m) / 2) :=
      (Real.rpow_pos_of_pos (oscEigenvalue_pos α) _).le
    have hdecfin := hdec.trans_lt ENNReal.ofReal_lt_top
    have hulfin := hul.trans_lt ENNReal.ofReal_lt_top
    have h := hA (S.invβ N) (S.ρ N) hyp N hN X hX r t hr hrt htT (oscTestFun b₀.m α) hφ hdecfin hulfin
    have hdec' := s55_toReal_le (by positivity) hdec
    have hul' := s55_toReal_le (by positivity) hul
    have hXc : X ∉ eucCollisionSet d N := fun ⟨i, j, hij, hh⟩ => hij (hX hh)
    have hG : 0 ≤ rieszModulatedEnergy d b₀.s X (HRS.Whole.withDensityReal (S.ρ N r)) + oN d b₀.s c N :=
      S.energy_nonneg N hN r ⟨hr, hrt.trans htT⟩ X hXc
    have hC0' : C₀A ≤ c := hC0
    have hmono := s55_oN_mono (d := d) b₀.s hC0' N
    set F := rieszModulatedEnergy d b₀.s X (HRS.Whole.withDensityReal (S.ρ N r)) with hF
    set Sx : ℝ := (decayNormE b₀.k (b₀.s + 1) (oscTestFun b₀.m α)).toReal +
      (ulNormE (b₀.k + 2 + ⌈(d : ℝ) / 2⌉₊) b₀.θ (oscTestFun b₀.m α)).toReal with hSx
    have hSx0 : 0 ≤ Sx := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    have hSx1 : Sx ≤ 2 * Cosc * oscEigenvalue d α ^ (((b₀.J : ℝ) - b₀.m) / 2) := by
      rw [hSx]; nlinarith
    refine h.trans ?_
    calc CA * Sx * (F + oN d b₀.s C₀A N) ≤ CA * Sx * (F + oN d b₀.s c N) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hCA0 hSx0)
      _ ≤ CA * (2 * Cosc * oscEigenvalue d α ^ (((b₀.J : ℝ) - b₀.m) / 2)) * (F + oN d b₀.s c N) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSx1 hCA0) hG
      _ = CA * (2 * Cosc) * oscEigenvalue d α ^ (((b₀.J : ℝ) - b₀.m) / 2) * (F + oN d b₀.s c N) := by ring
  · -- branch B: `s ≥ d - 2`
    have hsB : (d : ℝ) - 2 ≤ b₀.s := not_lt.1 hsA
    obtain ⟨Lm, hLm⟩ := u15_logmoment hL1 b₀.Λ
    obtain ⟨C₀B, CB, hC₀B, hCB, hB⟩ :=
      HRS.MH.CommSuper.whole_commutator_super_of_concentration_proof (d := d) hd1 hs0 hsd hsB Lm
    refine ⟨C₀B * (max b₀.Λ 1) ^ (b₀.s / d) + Real.log (max b₀.Λ 1) / (2 * d), fun b hbeq hC0 => ?_⟩
    obtain ⟨c, rfl⟩ : ∃ c, b = { b₀ with C₀ := c } := ⟨b.C₀, hbeq⟩
    refine ⟨CB * (u15_cM b₀.M.transpose * max b₀.K 0 * Cosc), fun S N hN X hX r t hr hrt htT α => ?_⟩
    obtain ⟨hφd, hul, hdec⟩ := hosc α
    have hEpos : 0 ≤ oscEigenvalue d α ^ (((b₀.J : ℝ) - b₀.m) / 2) :=
      (Real.rpow_pos_of_pos (oscEigenvalue_pos α) _).le
    have hφ : ContDiff ℝ ((b₀.k + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) (oscTestFun b₀.m α) :=
      s55_cd_of_inf _ hφd
    have hulfin := hul.trans_lt ENNReal.ofReal_lt_top
    have hrT : r ∈ Set.Icc (0 : ℝ) b₀.T := ⟨hr, hrt.trans htT⟩
    -- the adjoint input
    obtain ⟨-, hmem0, hcb0⟩ := S.adjoint N r t hr hrt htT (oscTestFun b₀.m α) hφ hulfin
    have e : b₀.k + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ = b₀.k + 2 + ⌈(d : ℝ) / 2⌉₊ := by omega
    have hmem : MemCb (b₀.k + 1) (propagatorW (S.coeff N) r t (oscTestFun b₀.m α)) := hmem0
    have hcb : HRS.cbNorm (b₀.k + 1) (propagatorW (S.coeff N) r t (oscTestFun b₀.m α)) ≤
        b₀.K * (ulNormE (b₀.k + 1 + 1 + ⌈(d : ℝ) / 2⌉₊) b₀.θ (oscTestFun b₀.m α)).toReal := hcb0
    rw [e] at hcb
    set f := propagatorW (S.coeff N) r t (oscTestFun b₀.m α) with hf
    set ulr : ℝ := (ulNormE (b₀.k + 2 + ⌈(d : ℝ) / 2⌉₊) b₀.θ (oscTestFun b₀.m α)).toReal with hulr
    have hulr0 : 0 ≤ ulr := ENNReal.toReal_nonneg
    have hulr1 : ulr ≤ Cosc * oscEigenvalue d α ^ (((b₀.J : ℝ) - b₀.m) / 2) :=
      s55_toReal_le (by positivity) hul
    have hmem2 : MemCb 2 f := ⟨hmem.1.of_le (by exact_mod_cast (by omega : 2 ≤ b₀.k + 1)),
      fun j hj => hmem.2 j (by omega)⟩
    -- Lipschitz transport
    set cM : ℝ := u15_cM b₀.M.transpose with hcM
    have hcM0 : 0 ≤ cM := u15_cM_nonneg _
    set v : Euc d → Euc d := fun x => Torus.matVec b₀.M.transpose (gradient f x) with hv
    have hcb0 : 0 ≤ HRS.cbNorm (b₀.k + 1) f :=
      Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
    have hcb2 : HRS.cbNorm 2 f ≤ HRS.cbNorm (b₀.k + 1) f := s55_cb_mono (by omega)
    have hLip : LipschitzWith (Real.toNNReal (cM * HRS.cbNorm (b₀.k + 1) f)) v := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (mul_nonneg hcM0 hcb0)]
      have e1 : v x - v y = Torus.matVec b₀.M.transpose (gradient f x - gradient f y) := by
        simp only [hv, Torus.matVec]; simp
      rw [e1]
      calc ‖Torus.matVec b₀.M.transpose (gradient f x - gradient f y)‖
          ≤ cM * ‖gradient f x - gradient f y‖ := u15_matVec_norm_le _ _
        _ ≤ cM * (HRS.cbNorm 2 f * ‖x - y‖) :=
            mul_le_mul_of_nonneg_left (s55_grad_lip_cb hmem2 x y) hcM0
        _ ≤ cM * (HRS.cbNorm (b₀.k + 1) f * ‖x - y‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcb2 (norm_nonneg _)) hcM0
        _ = cM * HRS.cbNorm (b₀.k + 1) f * ‖x - y‖ := by ring
    have hKv : cM * HRS.cbNorm (b₀.k + 1) f ≤ cM * (max b₀.K 0 * ulr) := by
      refine mul_le_mul_of_nonneg_left (hcb.trans ?_) hcM0
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hulr0
    have hlip : HasLipBoundW v (cM * (max b₀.K 0 * ulr)) := ⟨_, hLip, by
      rw [Real.coe_toNNReal _ (mul_nonneg hcM0 hcb0)]; exact hKv⟩
    -- the density
    obtain ⟨hprob, -, hwt⟩ : HRS.Whole.IsProbDensity (S.ρ N r) ∧ ContDiff ℝ _ (S.ρ N r) ∧ _ :=
      ⟨(S.mf N).density r hrT, (S.dens N r hrT).1, (S.dens N r hrT).2⟩
    have hb0 : ∀ x, jbracket x ^ b₀.L * |S.ρ N r x| ≤ max b₀.Λ 0 := u15_weighted_zero hwt
    have hρle : ∀ x, S.ρ N r x ≤ max b₀.Λ 1 := fun x =>
      (u15_dens_le hL0 hprob.nonneg hb0 x).trans (max_le_max le_rfl zero_le_one)
    have hlog : b₀.s = 0 → HasLogMoment (HRS.Whole.withDensityReal (S.ρ N r)) Lm :=
      fun _ => hLm (S.ρ N r) hprob hb0
    obtain ⟨-, hb1⟩ := hB (max b₀.Λ 1) (le_max_right _ _) N hN (S.ρ N r) hprob hρle hlog X hX v _ hlip
    have hoN := u15_oNΛ_le hd1 hs0 C₀B (max b₀.Λ 1) (le_max_right _ _) (N := N) (by omega)
    have hXc : X ∉ eucCollisionSet d N := fun ⟨i, j, hij, hh⟩ => hij (hX hh)
    have hG : 0 ≤ rieszModulatedEnergy d b₀.s X (HRS.Whole.withDensityReal (S.ρ N r)) + oN d b₀.s c N :=
      S.energy_nonneg N hN r hrT X hXc
    have hC0' : C₀B * (max b₀.Λ 1) ^ (b₀.s / d) + Real.log (max b₀.Λ 1) / (2 * d) ≤ c := hC0
    have hmono := s55_oN_mono (d := d) b₀.s hC0' N
    set F := rieszModulatedEnergy d b₀.s X (HRS.Whole.withDensityReal (S.ρ N r)) with hF
    have hK0 : 0 ≤ cM * (max b₀.K 0 * ulr) :=
      mul_nonneg hcM0 (mul_nonneg (le_max_right _ _) hulr0)
    refine hb1.trans ?_
    calc CB * (cM * (max b₀.K 0 * ulr)) * (F + oNΛ d b₀.s C₀B (max b₀.Λ 1) N)
        ≤ CB * (cM * (max b₀.K 0 * ulr)) * (F + oN d b₀.s c N) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hCB.le hK0)
      _ ≤ CB * (cM * (max b₀.K 0 * (Cosc * oscEigenvalue d α ^ (((b₀.J : ℝ) - b₀.m) / 2)))) *
            (F + oN d b₀.s c N) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hCB.le) hG
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hulr1 (le_max_right _ _)) hcM0
      _ = CB * (cM * max b₀.K 0 * Cosc) * oscEigenvalue d α ^ (((b₀.J : ℝ) - b₀.m) / 2) *
            (F + oN d b₀.s c N) := by ring

end HRS.MS.Go

