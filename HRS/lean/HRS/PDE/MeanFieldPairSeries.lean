import HRS.PDE.MeanFieldPairSlice
import HRS.PDE.MeanFieldAdjointSmoothing

/-!
# Lemma 4.14, packet P12b: the pair semigroup as a Fourier series (package MF-01)

See `HRS/PDE/MeanFieldAdjointPlan.md`, packet P12b.

* `pairSemigroup_eq_tsum`: `U_t^x U_t^y R = ∑_k [S(t)cos_k(x) S(t)Re R̂(k;·)(y) - S(t)sin_k(x) S(t)Im R̂(k;·)(y)]`.
* `exists_pairSemigroup_decay`: `U_t^x U_t^y R` is `C^j` with exponential decay in `t`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFPair

variable {d : ℕ}

/-! ### P12b helper infrastructure: linearity of the frozen and equilibrium semigroups -/

section SemigroupLinearAux

open HRS.PDE HRS.PDE.MFAdjoint

theorem derivCoeff_smul_aux (j : Fin d) (a : ℂ) (F : Coeff d) :
    derivCoeff j (fun k => a * F k) = fun k => a * derivCoeff j F k := by
  funext k
  simp only [derivCoeff]
  ring

theorem mulCoeff_smul_aux (b : Coeff d) (a : ℂ) (F : Coeff d) :
    mulCoeff b (fun k => a * F k) = fun k => a * mulCoeff b F k := by
  funext k
  simp only [mulCoeff]
  rw [← tsum_mul_left]
  congr 1
  funext j
  ring

theorem rieszMult_smul_aux (d : ℕ) (s : ℝ) (a : ℂ) (F : Coeff d) :
    rieszMult d s (fun k => a * F k) = fun k => a * rieszMult d s F k := by
  funext k
  simp only [rieszMult]
  ring

theorem forwardGen_smul_aux (D : DynData d) (ρ : Torus d → ℝ) (a : ℂ) (F : Coeff d) :
    forwardGen D ρ (fun k => a * F k) = fun k => a * forwardGen D ρ F k := by
  funext k
  simp only [forwardGen, laplaceCoeff, transportCoeff, nonlocalCoeff,
    gradRieszCoeff, derivCoeff_smul_aux, mulCoeff_smul_aux, rieszMult_smul_aux]
  simp only [Finset.mul_sum, mul_sub, mul_add]
  ring_nf

theorem hsInner_smul_aux (m : ℝ) (a : ℂ) (P G : Coeff d) :
    hsInner m (fun k => a * P k) G = a * hsInner m P G := by
  unfold hsInner
  rw [← tsum_mul_left]
  congr 1
  funext k
  ring

theorem isForwardSolution_smul_aux (D : DynData d) (μ : ℝ → Torus d → ℝ) (t : ℝ)
    (a : ℂ) {φc : Coeff d} {F : ℝ → Coeff d} (h : IsForwardSolution D μ t φc F) :
    IsForwardSolution D μ t (fun k => a * φc k) (fun σ => fun k => a * F σ k) := by
  refine ⟨fun τ hτ => MFThermalReg.memHs_smul (h.h1 τ hτ) a, fun k => ?_, fun k τ hτ => ?_⟩
  · have := (h.integrable k).const_mul a
    refine IntegrableOn.congr_fun this (fun σ _ => ?_) measurableSet_Icc
    simp only [forwardGen_smul_aux]
  · show a * F τ k = a * φc k + ∫ σ in (0:ℝ)..τ, forwardGen D (μ (t - σ))
      (fun k' => a * F σ k') k
    have hc : ∫ σ in (0:ℝ)..τ, forwardGen D (μ (t - σ)) (fun k' => a * F σ k') k =
        a * ∫ σ in (0:ℝ)..τ, forwardGen D (μ (t - σ)) (F σ) k := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun σ _ => ?_
      simp only [forwardGen_smul_aux]
    rw [hc, h.eq k τ hτ]
    ring

theorem weakContinuousInHs_smul_aux {m : ℝ} {t : ℝ} (a : ℂ) {F : ℝ → Coeff d}
    (h : WeakContinuousInHs m F t) :
    WeakContinuousInHs m (fun σ => fun k => a * F σ k) t := by
  refine ⟨fun τ hτ => MFThermalReg.memHs_smul (h.1 τ hτ) a, fun G hG => ?_⟩
  exact (continuousOn_const.mul (h.2 G hG)).congr fun τ _ => hsInner_smul_aux m a (F τ) G

theorem propagatorCoeff_smul_aux (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : 1 ≤ m) (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ)
    (μ : ℝ → Torus d → ℝ) (hA : AdjointData s m R MB Λ VB D ν₀ T μ) {t : ℝ}
    (ht : t ∈ Set.Ioc 0 T) (a : ℂ) {φc : Coeff d} (hφ : MemHs (m : ℝ) φc) {τ : ℝ}
    (hτ : τ ∈ Set.Icc 0 t) :
    propagatorCoeff D μ m t (fun k => a * φc k) τ = fun k => a * propagatorCoeff D μ m t φc τ k := by
  obtain ⟨C, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd m hm R MB Λ VB
  obtain ⟨h1, w, -⟩ := hspec D ν₀ T μ hA t ht φc hφ
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  exact propagatorCoeff_eq_of_solution hd hs0 hsd hm hA ht (MFThermalReg.memHs_smul hφ a)
    (isForwardSolution_smul_aux D μ t a h1)
    (weakContinuousInHs_smul_aux a (weakContinuousInHs_mono hm1 w)) τ hτ

theorem frozenCoeff_smul_aux (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : 1 ≤ m) (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (ρβ : Torus d → ℝ)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρβ)) (a : ℂ) {ψc : Coeff d}
    (hψ : MemHs (m : ℝ) ψc) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) :
    frozenCoeff D ρβ m (fun k => a * ψc k) τ = fun k => a * frozenCoeff D ρβ m ψc τ k := by
  rcases hτ.1.eq_or_lt with h0 | hpos
  · subst h0
    rw [frozenCoeff_zero hm (MFThermalReg.memHs_smul hψ a), frozenCoeff_zero hm hψ]
  · unfold frozenCoeff
    exact propagatorCoeff_smul_aux hd s hs0 hsd m hm R MB Λ VB D ν₀ T _ hA ⟨hpos, hτ.2⟩ a hψ
      ⟨hτ.1, le_rfl⟩

theorem frozenCoeff_add_aux (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : 1 ≤ m) (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (ρβ : Torus d → ℝ)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρβ)) {ψc ψc' : Coeff d}
    (hψ : MemHs (m : ℝ) ψc) (hψ' : MemHs (m : ℝ) ψc') {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) :
    frozenCoeff D ρβ m (fun k => ψc k + ψc' k) τ =
      fun k => frozenCoeff D ρβ m ψc τ k + frozenCoeff D ρβ m ψc' τ k := by
  have h := frozenCoeff_sub hd s hs0 hsd m hm R MB Λ VB D ν₀ T ρβ hA (fun k => ψc k + ψc' k) ψc'
    (MFThermalReg.memHs_add hψ hψ') hψ' hτ
  have h2 : (fun k => ψc k + ψc' k) - ψc' = ψc := by
    funext k; simp
  rw [h2] at h
  funext k
  have hk := congrFun h k
  simp only [Pi.sub_apply] at hk
  linear_combination -hk

theorem meanCoeff_add_aux {ρ : Torus d → ℝ} {x y : Coeff d} (hρ : MemHs 0 (coeffOf ρ))
    (hx : MemHs 0 x) (hy : MemHs 0 y) :
    meanCoeff ρ (x + y) = meanCoeff ρ x + meanCoeff ρ y := by
  unfold meanCoeff hsInner
  have hs1 := summable_meanTerm hρ hx
  have hs2 := summable_meanTerm hρ hy
  have h : (∑' k, ((sobWeight 0 k : ℝ) : ℂ) * (coeffOf ρ k * conj ((x + y) k))) =
      (∑' k, ((sobWeight 0 k : ℝ) : ℂ) * (coeffOf ρ k * conj (x k))) +
        ∑' k, ((sobWeight 0 k : ℝ) : ℂ) * (coeffOf ρ k * conj (y k)) := by
    rw [← Summable.tsum_add hs1 hs2]
    refine tsum_congr fun k => ?_
    simp only [Pi.add_apply, map_add]
    ring
  rw [h, Complex.add_re]

theorem centerCoeff_add_aux {ρ : Torus d → ℝ} {x y : Coeff d} (hρ : MemHs 0 (coeffOf ρ))
    (hx : MemHs 0 x) (hy : MemHs 0 y) :
    centerCoeff ρ (x + y) = centerCoeff ρ x + centerCoeff ρ y := by
  unfold centerCoeff
  rw [meanCoeff_add_aux hρ hx hy]
  funext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add]
  ring

theorem toFun_add_aux (a b : Coeff d) (ha : Summable fun k => ‖a k‖)
    (hb : Summable fun k => ‖b k‖) (x : Torus d) :
    toFun (a + b) x = toFun a x + toFun b x := by
  unfold toFun series
  simp only [Pi.add_apply, add_mul]
  rw [((summable_series_terms a ha x).tsum_add (summable_series_terms b hb x)), Complex.add_re]

theorem equilibriumSemigroup_add_fun (hd : 1 ≤ d) (s : ℝ) (νm νp c₀ Λ₀ : ℝ) (β : ℝ)
    (V ρβ : Torus d → ℝ) (H : FrozenHyp d s (2 * mStar d + 4) νm νp c₀ Λ₀ β V ρβ)
    (ψ₁ ψ₂ : Torus d → ℝ) (hψ₁ : Continuous ψ₁) (hψ₂ : Continuous ψ₂)
    (hm₁ : MemSobolev ((mStar d : ℝ) + 4) ψ₁) (hm₂ : MemSobolev ((mStar d : ℝ) + 4) ψ₂)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ (ψ₁ + ψ₂) =
      equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ₁ +
        equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ₂ := by
  have h3 := ClassicalPart.three_le_mStar d
  set m : ℕ := mStar d + 4 with hmdef
  have hm : mStar d + 2 ≤ m := by omega
  have hH : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρβ := H.mono (by omega)
  have hψ₁m : MemSobolev (m : ℝ) ψ₁ := by rw [hmdef]; push_cast; exact hm₁
  have hψ₂m : MemSobolev (m : ℝ) ψ₂ := by rw [hmdef]; push_cast; exact hm₂
  have hψc : Continuous (ψ₁ + ψ₂) := hψ₁.add hψ₂
  have hL2 : MemLp (ψ₁ + ψ₂) 2 volume := hψ₁m.1.add hψ₂m.1
  obtain ⟨hc₁, hre₁, hsum₁⟩ := coeff_data m hm hψ₁ hψ₁m
  obtain ⟨hc₂, hre₂, hsum₂⟩ := coeff_data m hm hψ₂ hψ₂m
  have hcoef : coeffOf (ψ₁ + ψ₂) = coeffOf ψ₁ + coeffOf ψ₂ := by
    funext k; exact MFThermalReg.coeffOf_add_fun hψ₁ hψ₂ k
  have hcm : MemHs (m : ℝ) (coeffOf (ψ₁ + ψ₂)) := by
    rw [hcoef]; exact MFThermalReg.memHs_add hc₁ hc₂
  have hsumψ : MemSobolev (m : ℝ) (ψ₁ + ψ₂) := memSobolev_of_memHs _ _ hL2 hcm
  have hprob := hH.thermal.1
  have hρc := hH.cont (by omega : 1 ≤ m + 3)
  have hρ0 : MemHs 0 (coeffOf ρβ) := MFApriori.memHs_zero_coeffOf_continuous hρc
  obtain ⟨e1, -⟩ := S_eq hd m hm hH hψ₁ hψ₁m hτ
  obtain ⟨e2, -⟩ := S_eq hd m hm hH hψ₂ hψ₂m hτ
  obtain ⟨e3, -⟩ := S_eq hd m hm hH hψc hsumψ hτ
  obtain ⟨hf₁, -, hs₁⟩ := frozenData hd m hm hH hψ₁ hψ₁m hτ
  obtain ⟨hf₂, -, hs₂⟩ := frozenData hd m hm hH hψ₂ hψ₂m hτ
  have hA := adjointData_frozen_level m hH 0 (τ + 1) (by linarith)
  have hF : frozenCoeff (mfData d s hH.hs0 hH.hsd V β hH.hβ) ρβ m (coeffOf (ψ₁ + ψ₂)) τ =
      frozenCoeff (mfData d s hH.hs0 hH.hsd V β hH.hβ) ρβ m (coeffOf ψ₁) τ +
        frozenCoeff (mfData d s hH.hs0 hH.hsd V β hH.hβ) ρβ m (coeffOf ψ₂) τ := by
    rw [hcoef]
    exact frozenCoeff_add_aux hd s hH.hs0 hH.hsd m (by omega) _ _ _ _ _ _ _ _ hA hc₁ hc₂
      ⟨hτ, by linarith⟩
  have hm0 : ∀ c : Coeff d, MemHs (m : ℝ) c → MemHs 0 c := fun c hc => hc.mono (by positivity)
  funext x
  rw [Pi.add_apply, e3, e1, e2, hF, centerCoeff_add_aux hρ0 (hm0 _ hf₁) (hm0 _ hf₂)]
  exact toFun_add_aux _ _ (summable_center hs₁) (summable_center hs₂) x

theorem meanCoeff_smul_aux (ρ : Torus d → ℝ) (a : ℝ) (c : Coeff d) :
    meanCoeff ρ (fun k => (a : ℂ) * c k) = a * meanCoeff ρ c := by
  unfold meanCoeff hsInner
  have h : (∑' k, ((sobWeight 0 k : ℝ) : ℂ) * (coeffOf ρ k * conj ((a : ℂ) * c k))) =
      (a : ℂ) * ∑' k, ((sobWeight 0 k : ℝ) : ℂ) * (coeffOf ρ k * conj (c k)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    simp only [map_mul, Complex.conj_ofReal]
    ring
  rw [h, Complex.re_ofReal_mul]

theorem centerCoeff_smul_aux (ρ : Torus d → ℝ) (a : ℝ) (c : Coeff d) :
    centerCoeff ρ (fun k => (a : ℂ) * c k) = fun k => (a : ℂ) * centerCoeff ρ c k := by
  unfold centerCoeff
  rw [meanCoeff_smul_aux]
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem toFun_smul_aux (a : ℝ) (c : Coeff d) (x : Torus d) :
    toFun (fun k => (a : ℂ) * c k) x = a * toFun c x := by
  unfold toFun series
  have h : (∑' k, (a : ℂ) * c k * Torus.mode k x) = (a : ℂ) * ∑' k, c k * Torus.mode k x := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    ring
  rw [h, Complex.re_ofReal_mul]

theorem equilibriumSemigroup_smul_fun (hd : 1 ≤ d) (s : ℝ) (νm νp c₀ Λ₀ : ℝ) (β : ℝ)
    (V ρβ : Torus d → ℝ) (H : FrozenHyp d s (2 * mStar d + 4) νm νp c₀ Λ₀ β V ρβ)
    (a : ℝ) (ψ : Torus d → ℝ) (hψ : Continuous ψ) (hψm : MemSobolev ((mStar d : ℝ) + 4) ψ)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ (fun x => a * ψ x) =
      fun x => a * equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ x := by
  have h3 := ClassicalPart.three_le_mStar d
  set m : ℕ := mStar d + 4 with hmdef
  have hm : mStar d + 2 ≤ m := by omega
  have hH : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρβ := H.mono (by omega)
  have hψm' : MemSobolev (m : ℝ) ψ := by rw [hmdef]; push_cast; exact hψm
  obtain ⟨hc, hre, hsum⟩ := coeff_data m hm hψ hψm'
  have hcoef : coeffOf (fun x => a * ψ x) = fun k => (a : ℂ) * coeffOf ψ k :=
    funext fun k => MFThermalReg.coeffOf_const_mul_fun a ψ k
  have hL2 : MemLp (fun x => a * ψ x) 2 volume := hψm'.1.const_mul a
  have hsumψ : MemSobolev (m : ℝ) (fun x => a * ψ x) :=
    memSobolev_of_memHs _ _ hL2 (by rw [hcoef]; exact MFThermalReg.memHs_smul hc _)
  obtain ⟨e1, -⟩ := S_eq hd m hm hH hψ hψm' hτ
  obtain ⟨e2, -⟩ := S_eq hd m hm hH (show Continuous (fun x => a * ψ x) from continuous_const.mul hψ) hsumψ hτ
  have hA := adjointData_frozen_level m hH 0 (τ + 1) (by linarith)
  have hF : frozenCoeff (mfData d s hH.hs0 hH.hsd V β hH.hβ) ρβ m (coeffOf (fun x => a * ψ x)) τ =
      fun k => (a : ℂ) * frozenCoeff (mfData d s hH.hs0 hH.hsd V β hH.hβ) ρβ m (coeffOf ψ) τ k := by
    rw [hcoef]
    exact frozenCoeff_smul_aux hd s hH.hs0 hH.hsd m (by omega) _ _ _ _ _ _ _ _ hA (a : ℂ) hc
      ⟨hτ, by linarith⟩
  funext x
  rw [e2, e1, hF, centerCoeff_smul_aux]
  exact toFun_smul_aux a _ x

end SemigroupLinearAux

/-! ### P12b helper infrastructure: series passthrough and bounds -/

section SeriesAux

open HRS.PDE HRS.PDE.MFAdjoint

theorem cd_tsum_ps {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (f : ι → E → ℝ) (L : ℕ) (hf : ∀ i, ContDiff ℝ L (f i)) (B : ι → ℝ) (hB : Summable B)
    (hbd : ∀ i k, k ≤ L → ∀ x, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ B i) :
    ContDiff ℝ L (fun x => ∑' i, f i x) ∧
      (∀ k, k ≤ L → ∀ x, iteratedFDeriv ℝ k (fun y => ∑' i, f i y) x =
        ∑' i, iteratedFDeriv ℝ k (f i) x) ∧
      ∀ k, k ≤ L → ∀ x, ‖iteratedFDeriv ℝ k (fun y => ∑' i, f i y) x‖ ≤ ∑' i, B i := by
  have hv : ∀ k : ℕ, (k : ℕ∞) ≤ (L : ℕ∞) → Summable (fun i => B i) := fun _ _ => hB
  have h'f : ∀ (k : ℕ) (i : ι) (x : E), (k : ℕ∞) ≤ (L : ℕ∞) → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ B i :=
    fun k i x hk => hbd i k (by exact_mod_cast hk) x
  have hcd := contDiff_tsum (𝕜 := ℝ) (N := (L : ℕ∞)) (v := fun _ i => B i)
    (fun i => by exact_mod_cast hf i) hv h'f
  refine ⟨by exact_mod_cast hcd, fun k hk x => ?_, fun k hk x => ?_⟩
  · exact iteratedFDeriv_tsum_apply (N := (L : ℕ∞)) (v := fun _ i => B i)
      (fun i => by exact_mod_cast hf i) hv h'f (by exact_mod_cast hk) x
  · rw [iteratedFDeriv_tsum_apply (N := (L : ℕ∞)) (v := fun _ i => B i)
      (fun i => by exact_mod_cast hf i) hv h'f (by exact_mod_cast hk) x]
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · exact Summable.of_nonneg_of_le (fun i => norm_nonneg _)
        (fun i => h'f k i x (by exact_mod_cast hk)) hB
    · exact Summable.tsum_le_tsum (fun i => h'f k i x (by exact_mod_cast hk))
        (Summable.of_nonneg_of_le (fun i => norm_nonneg _)
          (fun i => h'f k i x (by exact_mod_cast hk)) hB) hB

theorem norm_iter_le_cb_ps {L : ℕ} {φ : Torus d → ℝ} (hφ : Torus.IsCk (L : WithTop ℕ∞) φ) {i : ℕ}
    (hi : i ≤ L) (x : Euc d) :
    ‖iteratedFDeriv ℝ i (Torus.lift φ) x‖ ≤ Torus.cbNorm L φ := by
  unfold Torus.cbNorm
  have hb : ∀ j ∈ Finset.range (L + 1), 0 ≤ ⨆ x : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖ :=
    fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hci : ContDiff ℝ i (Torus.lift φ) := hφ.of_le (by exact_mod_cast hi)
  refine le_trans (le_ciSup (Torus.bddAbove_norm_iteratedFDeriv_lift i φ hci) x) ?_
  exact Finset.single_le_sum hb (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

theorem cbNorm_nonneg_ps (L : ℕ) (φ : Torus d → ℝ) : 0 ≤ Torus.cbNorm L φ :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem sup_le_cb_ps {L : ℕ} {φ : Torus d → ℝ} (hφ : Torus.IsCk (L : WithTop ℕ∞) φ) {i : ℕ}
    (hi : i ≤ L) : ⨆ x : Euc d, ‖iteratedFDeriv ℝ i (Torus.lift φ) x‖ ≤ Torus.cbNorm L φ := by
  unfold Torus.cbNorm
  have hb : ∀ j ∈ Finset.range (L + 1), 0 ≤ ⨆ x : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖ :=
    fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
  exact Finset.single_le_sum hb (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

theorem isCk_tsum_cbNorm_ps {ι : Type*} (L : ℕ) (g : ι → Torus d → ℝ)
    (hg : ∀ i, Torus.IsCk (L : WithTop ℕ∞) (g i))
    (hs : Summable fun i => Torus.cbNorm L (g i)) :
    Torus.IsCk (L : WithTop ℕ∞) (fun y => ∑' i, g i y) ∧
      Torus.cbNorm L (fun y => ∑' i, g i y) ≤ (L + 1) * ∑' i, Torus.cbNorm L (g i) := by
  obtain ⟨h1, -, h3⟩ := cd_tsum_ps (fun i => Torus.lift (g i)) L (fun i => hg i)
    (fun i => Torus.cbNorm L (g i)) hs (fun i k hk x => norm_iter_le_cb_ps (hg i) hk x)
  have e : Torus.lift (fun y => ∑' i, g i y) = fun x => ∑' i, Torus.lift (g i) x := rfl
  have hCk : Torus.IsCk (L : WithTop ℕ∞) (fun y => ∑' i, g i y) := by
    unfold Torus.IsCk; rw [e]; exact h1
  refine ⟨hCk, ?_⟩
  unfold Torus.cbNorm
  calc ∑ j ∈ Finset.range (L + 1), ⨆ x : Euc d, ‖iteratedFDeriv ℝ j
        (Torus.lift fun y => ∑' i, g i y) x‖
      ≤ ∑ j ∈ Finset.range (L + 1), ∑' i, Torus.cbNorm L (g i) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjL : j ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        refine ciSup_le fun x => ?_
        rw [e]; exact h3 j hjL x
    _ = (L + 1) * ∑' i, Torus.cbNorm L (g i) := by simp


/-- `x ↦ a cos(2πk·x) + b sin(2πk·x)`. -/
def trigTerm (a b : ℝ) (k : Lattice d) : Torus d → ℝ :=
  fun x => a * Torus.cosMode k x + b * Torus.sinMode k x

theorem lift_trigTerm (a b : ℝ) (k : Lattice d) :
    Torus.lift (trigTerm a b k) =
      (fun t : ℝ => a * Real.cos t + b * Real.sin t) ∘ Torus.freqFunctional k := by
  funext x
  simp [Torus.lift, trigTerm, Torus.cosMode_mk, Torus.sinMode_mk, Torus.freqFunctional_apply]

theorem trigTerm_isCk (a b : ℝ) (k : Lattice d) (L : ℕ) :
    Torus.IsCk (L : WithTop ℕ∞) (trigTerm a b k) := by
  unfold Torus.IsCk
  rw [lift_trigTerm]
  have h : ContDiff ℝ ⊤ (fun t : ℝ => a * Real.cos t + b * Real.sin t) :=
    (contDiff_const.mul Real.contDiff_cos).add (contDiff_const.mul Real.contDiff_sin)
  exact (h.comp (Torus.freqFunctional k).contDiff).of_le le_top

theorem cbNorm_trigTerm_le (a b : ℝ) (k : Lattice d) (L : ℕ) :
    Torus.cbNorm L (trigTerm a b k) ≤ (L + 1) * ((|a| + |b|) * Lattice.jp k ^ L) := by
  have hjp := Torus.jp_ge_one k
  have hcomb : ContDiff ℝ ⊤ (fun t : ℝ => a * Real.cos t + b * Real.sin t) :=
    (contDiff_const.mul Real.contDiff_cos).add (contDiff_const.mul Real.contDiff_sin)
  have key : ∀ i, i ≤ L → ∀ x : Euc d, ‖iteratedFDeriv ℝ i (Torus.lift (trigTerm a b k)) x‖ ≤
      (|a| + |b|) * Lattice.jp k ^ L := by
    intro i hi x
    rw [lift_trigTerm]
    refine (Torus.norm_iteratedFDeriv_comp_functional _ hcomb _
      (fun i t => norm_iteratedFDeriv_trig_comb a b i t) _ i x).trans ?_
    have h2 : ‖Torus.freqFunctional k‖ ^ i ≤ Lattice.jp k ^ L := by
      calc ‖Torus.freqFunctional k‖ ^ i ≤ Lattice.jp k ^ i := by
            gcongr
            exact (Torus.norm_freqFunctional_le _).trans (Torus.two_pi_enorm_le_jp _)
        _ ≤ Lattice.jp k ^ L := pow_le_pow_right₀ hjp hi
    gcongr
  unfold Torus.cbNorm
  calc ∑ i ∈ Finset.range (L + 1), ⨆ x : Euc d, ‖iteratedFDeriv ℝ i (Torus.lift (trigTerm a b k)) x‖
      ≤ ∑ i ∈ Finset.range (L + 1), ((|a| + |b|) * Lattice.jp k ^ L) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hiL : i ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact ciSup_le fun x => key i hiL x
    _ = _ := by simp


theorem isCk_of_smooth_ps {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (n : ℕ) :
    Torus.IsCk (n : WithTop ℕ∞) f :=
  ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) from hf)
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))

theorem frozenHyp_of_smooth (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (n : ℕ) :
    ∃ c₀ Λ₀ : ℝ, FrozenHyp d s n β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ := by
  have hcont : Continuous ρβ :=
    Torus.continuous_of_continuous_lift (φ := ρβ) (isCk_of_smooth_ps hρC 0).continuous
  obtain ⟨x₀, -, hx₀⟩ := (isCompact_univ (X := Torus d)).exists_isMinOn ⟨0, trivial⟩
    hcont.continuousOn
  refine ⟨ρβ x₀, max (Torus.cbNorm n V) (Torus.cbNorm n ρβ), ?_⟩
  exact ⟨hs0, hsd, hβ, inv_pos.2 hβ, ⟨le_rfl, le_rfl⟩, isCk_of_smooth_ps hV n,
    le_max_left _ _, hρβ, isCk_of_smooth_ps hρC n, le_max_right _ _, hpos x₀,
    fun x => hx₀ (Set.mem_univ x)⟩


theorem memSob_of_isCk_ps {L : ℕ} {h : Torus d → ℝ} (hh : Torus.IsCk (L : WithTop ℕ∞) h) :
    Continuous h ∧ MemSobolev (L : ℝ) h ∧ MemHs (L : ℝ) (coeffOf h) ∧
      hsNorm (L : ℝ) (coeffOf h) ≤ Real.sqrt ((1 + d) ^ L) * Torus.cbNorm L h := by
  have hcont : Continuous h := Torus.continuous_of_continuous_lift hh.continuous
  have hL2 : MemLp h 2 volume :=
    hcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨hm, hb⟩ := ClassicalPart.memHs_coeffOf_cbNorm L h hh
  refine ⟨hcont, memSobolev_of_memHs _ h hL2 hm, hm, ?_⟩
  unfold hsNorm
  calc Real.sqrt (hsNormSq (L : ℝ) (coeffOf h)) ≤ Real.sqrt ((1 + d) ^ L * Torus.cbNorm L h ^ 2) :=
        Real.sqrt_le_sqrt hb
    _ = _ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (cbNorm_nonneg_ps L h)]

theorem S_cb_bound (hd : 1 ≤ d) (s : ℝ) (j L : ℕ) (hL : mStar d + 4 ≤ L)
    (hjL : (d : ℝ) / 2 + j < L) (νm νp c₀ Λ₀ : ℝ) :
    ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ)
      (H : FrozenHyp d s (L + mStar d) νm νp c₀ Λ₀ β V ρβ) (h : Torus d → ℝ),
      Torus.IsCk (L : WithTop ℕ∞) h → ∀ τ : ℝ, 0 ≤ τ →
        Torus.IsCk (j : WithTop ℕ∞)
            (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ h) ∧
        Torus.cbNorm j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ h) ≤
          M * Real.exp (-c * τ) * Torus.cbNorm L h := by
  have h3 := ClassicalPart.three_le_mStar d
  obtain ⟨C, c, hC, hc, hdec⟩ := exists_frozen_hj_decay hd s L hL νm νp c₀ Λ₀
  obtain ⟨Ce, hCe⟩ := toFun_isCk_le (d := d) j (L : ℝ) hjL
  refine ⟨(|Ce| * C * (2 * (1 + |Λ₀|)) * Real.sqrt ((1 + d) ^ L)) + 1, c, by positivity, hc, ?_⟩
  intro β V ρβ H h hh τ hτ
  obtain ⟨hcont, hmem, hcm, hnorm⟩ := memSob_of_isCk_ps hh
  have hH3 : FrozenHyp d s (L + 3) νm νp c₀ Λ₀ β V ρβ := H.mono (by omega)
  have hLm : mStar d + 2 ≤ L := by omega
  have hprob : IsProbDensity ρβ := H.thermal.1
  have hρc : Continuous ρβ := H.cont (by omega)
  have hΛ : ∀ x, ρβ x ≤ Λ₀ := H.le_Lam
  obtain ⟨hSeq, -⟩ := S_eq hd L hLm hH3 hcont hmem hτ
  obtain ⟨hfm, hfre, -⟩ := frozenData hd L hLm hH3 hcont hmem hτ
  obtain ⟨hcc, -⟩ := centerCoeff_bound' hprob hρc hΛ (by positivity : (0 : ℝ) ≤ L) hfm
  have hccre := centerCoeff_isReal (ρ := ρβ) hfre
  obtain ⟨hmS, hnS⟩ := S_facts hd s H.hs0 H.hsd L hL H hcont hmem hτ (L : ℝ) (by positivity) le_rfl
  obtain ⟨hmS', hdecS⟩ := hdec β V ρβ H h hcont hmem τ hτ
  obtain ⟨-, hP⟩ := P_facts hd s H.hs0 H.hsd L hL H hcont hmem (L : ℝ) (by positivity) le_rfl
  obtain ⟨hpm, hpn⟩ := centerCoeff_bound' hprob hρc hΛ (by positivity : (0 : ℝ) ≤ L) hcm
  obtain ⟨hCk, hCb⟩ := hCe _ hcc hccre
  rw [hSeq]
  refine ⟨hCk, ?_⟩
  refine hCb.trans ?_
  have hE : 0 < Real.exp (-c * τ) := Real.exp_pos _
  have hcb0 := cbNorm_nonneg_ps L h
  have hsq0 : 0 ≤ Real.sqrt ((1 + d : ℝ) ^ L) := Real.sqrt_nonneg _
  have hΛ0 : 0 ≤ Λ₀ := (H.hc₀.le.trans (H.hlow 0)).trans (H.le_Lam 0)
  have hP0 : 0 ≤ hsNorm (L : ℝ) (centerCoeff ρβ (coeffOf h)) := MFApriori.hsNorm_nonneg' _ _
  have h1 : hsNorm (L : ℝ) (centerCoeff ρβ (coeffOf h)) ≤
      2 * (1 + Λ₀) * (Real.sqrt ((1 + d) ^ L) * Torus.cbNorm L h) :=
    hpn.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))
  have h2 : hsNorm (L : ℝ) (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ L
      (coeffOf h) τ)) ≤ C * Real.exp (-c * τ) *
        (2 * (1 + Λ₀) * (Real.sqrt ((1 + d) ^ L) * Torus.cbNorm L h)) := by
    rw [← hnS]
    refine hdecS.trans ?_
    rw [hP]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : 2 * (1 + Λ₀) ≤ 2 * (1 + |Λ₀|) := by linarith [le_abs_self Λ₀]
  have hN0 : 0 ≤ hsNorm (L : ℝ) (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ L
      (coeffOf h) τ)) := MFApriori.hsNorm_nonneg' _ _
  calc Ce * hsNorm (L : ℝ) (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ L
        (coeffOf h) τ))
      ≤ |Ce| * hsNorm (L : ℝ) (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ L
        (coeffOf h) τ)) := mul_le_mul_of_nonneg_right (le_abs_self _) hN0
    _ ≤ |Ce| * (C * Real.exp (-c * τ) *
        (2 * (1 + Λ₀) * (Real.sqrt ((1 + d) ^ L) * Torus.cbNorm L h))) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ ≤ |Ce| * (C * Real.exp (-c * τ) *
        (2 * (1 + |Λ₀|) * (Real.sqrt ((1 + d) ^ L) * Torus.cbNorm L h))) := by gcongr
    _ ≤ _ := by
        have : 0 ≤ |Ce| * C * (2 * (1 + |Λ₀|)) * Real.sqrt ((1 + d) ^ L) * Real.exp (-c * τ) *
          Torus.cbNorm L h := by positivity
        nlinarith


theorem abs_le_cb_ps {L : ℕ} {φ : Torus d → ℝ} (hφ : Torus.IsCk (L : WithTop ℕ∞) φ) (x : Torus d) :
    |φ x| ≤ Torus.cbNorm L φ := by
  have := norm_iter_le_cb_ps hφ (Nat.zero_le L) (Torus.rep x)
  rw [norm_iteratedFDeriv_zero] at this
  simpa [Torus.lift, Torus.mk_rep] using this

theorem sob_of_isCk_ps {f : Torus d → ℝ} (hf : Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) f) :
    Continuous f ∧ MemSobolev ((mStar d : ℝ) + 4) f := by
  obtain ⟨hc, hm, -, -⟩ := memSob_of_isCk_ps hf
  refine ⟨hc, ?_⟩
  have : (((mStar d + 4 : ℕ)) : ℝ) = (mStar d : ℝ) + 4 := by push_cast; ring
  rwa [this] at hm

section LinS

variable (hd : 1 ≤ d) {s νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ}
  (H : FrozenHyp d s (2 * mStar d + 4) νm νp c₀ Λ₀ β V ρβ)
include hd

theorem S_add_ps {f g : Torus d → ℝ} (hf : Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) f)
    (hg : Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) g) {τ : ℝ} (hτ : 0 ≤ τ) :
    equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ (fun y => f y + g y) =
      fun y => equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ f y +
        equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ g y := by
  obtain ⟨hfc, hfm⟩ := sob_of_isCk_ps hf
  obtain ⟨hgc, hgm⟩ := sob_of_isCk_ps hg
  exact equilibriumSemigroup_add_fun hd s νm νp c₀ Λ₀ β V ρβ H f g hfc hgc hfm hgm τ hτ

theorem S_smul_ps {f : Torus d → ℝ} (hf : Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) f) (a : ℝ)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ (fun y => a * f y) =
      fun y => a * equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ f y := by
  obtain ⟨hfc, hfm⟩ := sob_of_isCk_ps hf
  exact equilibriumSemigroup_smul_fun hd s νm νp c₀ Λ₀ β V ρβ H a f hfc hfm τ hτ

theorem S_zero_ps {τ : ℝ} (hτ : 0 ≤ τ) :
    equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ (fun _ => (0 : ℝ)) =
      fun _ => 0 := by
  have h0 : Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) (fun _ : Torus d => (0 : ℝ)) :=
    contDiff_const
  have := S_smul_ps hd H h0 0 hτ
  simpa using this

theorem S_sum_ps {ι : Type*} (g : ι → Torus d → ℝ)
    (hg : ∀ i, Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) (g i)) {τ : ℝ} (hτ : 0 ≤ τ)
    (t : Finset ι) [DecidableEq ι] :
    equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ (fun y => ∑ i ∈ t, g i y) =
      fun y => ∑ i ∈ t, equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ (g i) y := by
  induction t using Finset.induction_on with
  | empty => simpa using S_zero_ps hd H hτ
  | insert a t ha ih =>
    have hck : Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) (fun y => ∑ i ∈ t, g i y) := by
      unfold Torus.IsCk
      exact ContDiff.sum fun i _ => hg i
    have := S_add_ps hd H (hg a) hck hτ
    simp only [Finset.sum_insert ha]
    rw [this, ih]

end LinS

theorem series_passthrough (hd : 1 ≤ d) (s νm νp c₀ Λ₀ β : ℝ) (V ρβ : Torus d → ℝ)
    (H : FrozenHyp d s (2 * mStar d + 4) νm νp c₀ Λ₀ β V ρβ) (g : Lattice d → Torus d → ℝ)
    (hg : ∀ k, Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) (g k))
    (hs : Summable fun k => Torus.cbNorm (mStar d + 4) (g k)) {τ : ℝ} (hτ : 0 ≤ τ) (x : Torus d) :
    HasSum (fun k => equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ (g k) x)
      (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ (fun y => ∑' k, g k y) x) := by
  classical
  have h3 := ClassicalPart.three_le_mStar d
  set L : ℕ := mStar d + 4 with hL
  have hH' : FrozenHyp d s (L + mStar d) νm νp c₀ Λ₀ β V ρβ := H.mono (by omega)
  have hjL : (d : ℝ) / 2 + ((0 : ℕ) : ℝ) < (L : ℝ) := by
    have := mStar_gt d
    rw [hL]; push_cast; linarith
  obtain ⟨M, c, hM, hc, hbd⟩ := S_cb_bound hd s 0 L (by omega) hjL νm νp c₀ Λ₀
  have hsp : ∀ y, Summable fun k => g k y := fun y =>
    Summable.of_norm_bounded hs fun k => by
      simpa [Real.norm_eq_abs] using abs_le_cb_ps (hg k) y
  have key : ∀ t : Finset (Lattice d),
      |equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ (fun y => ∑' k, g k y) x -
          ∑ k ∈ t, equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ (g k) x| ≤
        M * ((L + 1) * ∑' k : {k // k ∉ t}, Torus.cbNorm L (g k)) := by
    intro t
    have hsub : Summable fun k : {k // k ∉ t} => Torus.cbNorm L (g k) := hs.subtype _
    obtain ⟨hTc, hTb⟩ := isCk_tsum_cbNorm_ps L (fun k : {k // k ∉ t} => g k) (fun k => hg k) hsub
    have hPc : Torus.IsCk (L : WithTop ℕ∞) (fun y => ∑ k ∈ t, g k y) := by
      unfold Torus.IsCk
      exact ContDiff.sum fun i _ => hg i
    have hF : (fun y => ∑' k, g k y) =
        fun y => (∑ k ∈ t, g k y) + ∑' k : {k // k ∉ t}, g k y := by
      funext y; exact ((hsp y).sum_add_tsum_subtype_compl t).symm
    have h1 := congrFun (S_add_ps hd H hPc hTc hτ) x
    have h2 := congrFun (S_sum_ps hd H g hg hτ t) x
    have e : equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ (fun y => ∑' k, g k y) x -
        ∑ k ∈ t, equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ (g k) x =
        equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ
          (fun y => ∑' k : {k // k ∉ t}, g k y) x := by
      rw [hF]
      rw [h1, h2]
      ring
    rw [e]
    obtain ⟨hSk, hSb⟩ := hbd β V ρβ hH' _ hTc τ hτ
    refine (abs_le_cb_ps hSk x).trans (hSb.trans ?_)
    have hexp : Real.exp (-c * τ) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have h0 := cbNorm_nonneg_ps L (fun y => ∑' k : {k // k ∉ t}, g k y)
    calc M * Real.exp (-c * τ) * Torus.cbNorm L (fun y => ∑' k : {k // k ∉ t}, g k y)
        ≤ M * 1 * Torus.cbNorm L (fun y => ∑' k : {k // k ∉ t}, g k y) := by gcongr
      _ ≤ M * ((L + 1) * ∑' k : {k // k ∉ t}, Torus.cbNorm L (g k)) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left hTb hM.le
  have htail : Tendsto (fun t : Finset (Lattice d) =>
      M * ((L + 1) * ∑' k : {k // k ∉ t}, Torus.cbNorm L (g k))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : Finset (Lattice d) => ∑ k ∈ t, Torus.cbNorm L (g k)) atTop
        (𝓝 (∑' k, Torus.cbNorm L (g k))) := hs.hasSum
    have h2 : Tendsto (fun t : Finset (Lattice d) =>
        (∑' k, Torus.cbNorm L (g k)) - ∑ k ∈ t, Torus.cbNorm L (g k)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := ∑' k, Torus.cbNorm L (g k))).sub h1
    have h3 : ∀ t : Finset (Lattice d), ∑' k : {k // k ∉ t}, Torus.cbNorm L (g k) =
        (∑' k, Torus.cbNorm L (g k)) - ∑ k ∈ t, Torus.cbNorm L (g k) := by
      intro t
      have := hs.sum_add_tsum_subtype_compl t
      linarith
    have h5 := (h2.const_mul ((L : ℝ) + 1)).const_mul M
    simp only [mul_zero] at h5
    exact h5.congr fun t => by rw [h3 t]
  have hconv : Tendsto (fun t : Finset (Lattice d) => ∑ k ∈ t,
      equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ (g k) x) atTop
      (𝓝 (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ (fun y => ∑' k, g k y) x)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun t => dist_nonneg) (fun t => ?_) htail
    rw [Real.dist_eq, abs_sub_comm]
    exact key t
  exact hconv


theorem cbNorm_smul_le_ps {L : ℕ} {φ : Torus d → ℝ} (hφ : Torus.IsCk (L : WithTop ℕ∞) φ) (a : ℝ) :
    Torus.cbNorm L (fun x => a * φ x) ≤ |a| * Torus.cbNorm L φ := by
  unfold Torus.cbNorm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hiL : i ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hci : ContDiff ℝ i (Torus.lift φ) := hφ.of_le (by exact_mod_cast hiL)
  have e : Torus.lift (fun x => a * φ x) = a • Torus.lift φ := by
    funext u; simp [Torus.lift]
  refine ciSup_le fun x => ?_
  rw [e, iteratedFDeriv_const_smul_apply hci.contDiffAt, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (le_ciSup (Torus.bddAbove_norm_iteratedFDeriv_lift i φ hci) x) (abs_nonneg _)

theorem summable_jp_rpow_ps (p : ℝ) (hp : p < -(d : ℝ)) :
    Summable fun k : Lattice d => Lattice.jp k ^ p := by
  rw [Torus.summable_lattice_iff]
  have := summable_jp_rpow (d := d) (-p / 2) (by linarith)
  refine this.congr fun k => ?_
  congr 1
  ring

theorem jp_pow_mul_rpow_ps (k : Lattice d) (L : ℕ) (q : ℝ) :
    Lattice.jp k ^ L * Lattice.jp k ^ q = Lattice.jp k ^ ((L : ℝ) + q) := by
  rw [Real.rpow_add (Torus.jp_pos k), Real.rpow_natCast]

theorem cosMode_eq_trig (k : Lattice d) : Torus.cosMode k = trigTerm 1 0 k := by
  funext x; simp [trigTerm]

theorem sinMode_eq_trig (k : Lattice d) : Torus.sinMode k = trigTerm 0 1 k := by
  funext x; simp [trigTerm]

theorem slice_re_expansion (c : Coeff d) (hs : Summable fun k => ‖c k‖) (x : Torus d) :
    toFun c x = ∑' k : Lattice d, trigTerm (c k).re (-(c k).im) k x := by
  unfold toFun series
  have hsum := summable_series_terms c hs x
  have h2 := (Complex.reCLM.hasSum hsum.hasSum).tsum_eq
  simp only [Complex.reCLM_apply] at h2
  rw [← h2]
  refine tsum_congr fun k => ?_
  simp only [Complex.reCLM_apply, trigTerm, Complex.mul_re, Torus.cosMode, Torus.sinMode]
  ring


theorem isCk_const_mul_ps {L : ℕ} {f : Torus d → ℝ} (hf : Torus.IsCk (L : WithTop ℕ∞) f) (a : ℝ) :
    Torus.IsCk (L : WithTop ℕ∞) (fun y => a * f y) := by
  unfold Torus.IsCk at *
  exact contDiff_const.mul hf

theorem isCk_cos_ps (k : Lattice d) (L : ℕ) : Torus.IsCk (L : WithTop ℕ∞) (Torus.cosMode k) := by
  rw [cosMode_eq_trig]; exact trigTerm_isCk 1 0 k L

theorem isCk_sin_ps (k : Lattice d) (L : ℕ) : Torus.IsCk (L : WithTop ℕ∞) (Torus.sinMode k) := by
  rw [sinMode_eq_trig]; exact trigTerm_isCk 0 1 k L

theorem S_trig_ps (hd : 1 ≤ d) {s νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ}
    (H : FrozenHyp d s (2 * mStar d + 4) νm νp c₀ Λ₀ β V ρβ) (a b : ℝ) (k : Lattice d) {τ : ℝ}
    (hτ : 0 ≤ τ) (x : Torus d) :
    equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ (trigTerm a b k) x =
      a * equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ (Torus.cosMode k) x +
        b * equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ (Torus.sinMode k) x := by
  have hc := isCk_const_mul_ps (isCk_cos_ps k (mStar d + 4)) a
  have hs' := isCk_const_mul_ps (isCk_sin_ps k (mStar d + 4)) b
  have h1 := congrFun (S_add_ps hd H hc hs' hτ) x
  have h2 := congrFun (S_smul_ps hd H (isCk_cos_ps k (mStar d + 4)) a hτ) x
  have h3 := congrFun (S_smul_ps hd H (isCk_sin_ps k (mStar d + 4)) b hτ) x
  show equilibriumSemigroup _ ρβ τ (fun y => a * Torus.cosMode k y + b * Torus.sinMode k y) x = _
  rw [h1, h2, h3]


/-! ### Strong continuity in `t` of the equilibrium semigroup in `C^j` -/

theorem frozen_path_cont_ps (hd : 1 ≤ d) {s νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ} (m : ℕ)
    (hm : 1 ≤ m) (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρβ) {ψc : Coeff d}
    (hψ : MemHs (m : ℝ) ψc) {m'' : ℝ} (hm'' : m'' < m) {T : ℝ} (hT : 0 < T) :
    ContinuousInHsOn m''
      (fun τ => frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ m ψc τ) (Set.Icc 0 T) := by
  have hA := adjointData_frozen_level m H 0 T hT
  obtain ⟨C, -, hspec⟩ := propagatorCoeff_spec hd s H.hs0 H.hsd m hm _ 1 Λ₀ Λ₀
  obtain ⟨-, hw, -⟩ := hspec _ 0 T (fun _ => ρβ) hA T ⟨hT, le_rfl⟩ ψc hψ
  have hc := forward_strong_continuity (m : ℝ) T _ hw m'' hm''
  have heq : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ m ψc τ =
        propagatorCoeff (mfData d s H.hs0 H.hsd V β H.hβ) (fun _ => ρβ) m T ψc τ :=
    fun τ hτ => (frozenCoeff_eq_propagatorCoeff hd s H.hs0 H.hsd m hm _ 1 Λ₀ Λ₀ _ 0 T ρβ hA ψc hψ
      ⟨hT, le_rfl⟩ hτ).symm
  refine ⟨fun τ hτ => by beta_reduce; rw [heq τ hτ]; exact hc.1 τ hτ, fun τ0 hτ0 => ?_⟩
  refine (hc.2 τ0 hτ0).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  rw [heq τ hτ, heq τ0 hτ0]

theorem S_cont_ps (hd : 1 ≤ d) {s νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ} (j L : ℕ)
    (hL : mStar d + 2 ≤ L) (hjL : (d : ℝ) / 2 + j < (L : ℝ) - 1)
    (H : FrozenHyp d s (L + 3) νm νp c₀ Λ₀ β V ρβ) {h : Torus d → ℝ}
    (hh : Torus.IsCk (L : WithTop ℕ∞) h) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Tendsto (fun t : ℝ => Torus.cbNorm j (fun x =>
        equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ t h x -
          equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ t₀ h x))
      (𝓝[Set.Ici 0] t₀) (𝓝 0) := by
  have h3 := ClassicalPart.three_le_mStar d
  obtain ⟨hcont, hmem, hcm, -⟩ := memSob_of_isCk_ps hh
  have hprob : IsProbDensity ρβ := H.thermal.1
  have hρc : Continuous ρβ := H.cont (by omega)
  have hΛ : ∀ x, ρβ x ≤ Λ₀ := H.le_Lam
  have hΛ0 : 0 ≤ Λ₀ := (H.hc₀.le.trans (H.hlow 0)).trans (H.le_Lam 0)
  have hm1 : 1 ≤ L := by omega
  have hm''0 : (0 : ℝ) ≤ (L : ℝ) - 1 := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 + j := by positivity
    linarith
  obtain ⟨Ce, hCe⟩ := toFun_isCk_le (d := d) j ((L : ℝ) - 1) (by linarith)
  set D := mfData d s H.hs0 H.hsd V β H.hβ with hD
  set F : ℝ → Coeff d := fun τ => frozenCoeff D ρβ L (coeffOf h) τ with hF
  have hcont' := frozen_path_cont_ps hd L hm1 H hcm (m'' := (L : ℝ) - 1) (by linarith)
    (T := t₀ + 1) (by linarith)
  have hSe : ∀ τ, 0 ≤ τ → equilibriumSemigroup D ρβ τ h = toFun (centerCoeff ρβ (F τ)) :=
    fun τ hτ => (S_eq hd L hL H hcont hmem hτ).1
  have hFmem : ∀ τ, 0 ≤ τ → MemHs (L : ℝ) (F τ) ∧ IsRealCoeff (F τ) ∧
      Summable (fun k => ‖F τ k‖) := fun τ hτ => frozenData hd L hL H hcont hmem hτ
  have hdiff : ∀ τ, 0 ≤ τ → Torus.cbNorm j (fun x => equilibriumSemigroup D ρβ τ h x -
      equilibriumSemigroup D ρβ t₀ h x) ≤
        |Ce| * (2 * (1 + |Λ₀|)) * hsNorm ((L : ℝ) - 1) (F τ - F t₀) := by
    intro τ hτ
    obtain ⟨hm1τ, hr1, hs1⟩ := hFmem τ hτ
    obtain ⟨hm1₀, hr0, hs0'⟩ := hFmem t₀ ht₀
    have hm1τ' : MemHs ((L : ℝ) - 1) (F τ) := hm1τ.mono (by linarith)
    have hm1₀' : MemHs ((L : ℝ) - 1) (F t₀) := hm1₀.mono (by linarith)
    have hmd : MemHs ((L : ℝ) - 1) (F τ - F t₀) := memHs_sub hm1τ' hm1₀'
    have hm0 : ∀ c : Coeff d, MemHs ((L : ℝ) - 1) c → MemHs 0 c := fun c hc => hc.mono hm''0
    have hρ0 : MemHs 0 (coeffOf ρβ) := MFApriori.memHs_zero_coeffOf_continuous hρc
    have hcs : centerCoeff ρβ (F τ - F t₀) = centerCoeff ρβ (F τ) - centerCoeff ρβ (F t₀) :=
      centerCoeff_sub' hρ0 (hm0 _ hm1τ') (hm0 _ hm1₀')
    have hfun : (fun x => equilibriumSemigroup D ρβ τ h x - equilibriumSemigroup D ρβ t₀ h x) =
        toFun (centerCoeff ρβ (F τ - F t₀)) := by
      funext x
      rw [hcs, hSe τ hτ, hSe t₀ ht₀]
      exact (ClassicalPart.toFun_sub ((ClassicalPart.WS_zero_iff _).2 (summable_center hs1))
        ((ClassicalPart.WS_zero_iff _).2 (summable_center hs0')) x).symm
    obtain ⟨hcc, hccb⟩ := centerCoeff_bound' hprob hρc hΛ hm''0 hmd
    have hre : IsRealCoeff (centerCoeff ρβ (F τ - F t₀)) :=
      centerCoeff_isReal (isRealCoeff_sub' hr1 hr0)
    obtain ⟨-, hCb⟩ := hCe _ hcc hre
    rw [hfun]
    refine hCb.trans ?_
    have hn0 := MFApriori.hsNorm_nonneg' ((L : ℝ) - 1) (F τ - F t₀)
    have h3' : 2 * (1 + Λ₀) ≤ 2 * (1 + |Λ₀|) := by linarith [le_abs_self Λ₀]
    calc Ce * hsNorm ((L : ℝ) - 1) (centerCoeff ρβ (F τ - F t₀))
        ≤ |Ce| * hsNorm ((L : ℝ) - 1) (centerCoeff ρβ (F τ - F t₀)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (MFApriori.hsNorm_nonneg' _ _)
      _ ≤ |Ce| * (2 * (1 + Λ₀) * hsNorm ((L : ℝ) - 1) (F τ - F t₀)) :=
          mul_le_mul_of_nonneg_left hccb (abs_nonneg _)
      _ ≤ |Ce| * (2 * (1 + |Λ₀|) * hsNorm ((L : ℝ) - 1) (F τ - F t₀)) := by gcongr
      _ = _ := by ring
  have hlim : Tendsto (fun τ => hsNorm ((L : ℝ) - 1) (F τ - F t₀)) (𝓝[Set.Ici 0] t₀) (𝓝 0) := by
    have h1 := hcont'.2 t₀ ⟨ht₀, by linarith⟩
    refine h1.mono_left ?_
    rw [nhdsWithin_le_iff]
    have : Set.Ici (0 : ℝ) ∩ Set.Iio (t₀ + 1) ∈ 𝓝[Set.Ici 0] t₀ :=
      inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by linarith)))
    exact Filter.mem_of_superset this (fun τ hτ => ⟨hτ.1, hτ.2.le⟩)
  have hbound : Tendsto (fun τ => |Ce| * (2 * (1 + |Λ₀|)) * hsNorm ((L : ℝ) - 1) (F τ - F t₀))
      (𝓝[Set.Ici 0] t₀) (𝓝 0) := by
    simpa using hlim.const_mul (|Ce| * (2 * (1 + |Λ₀|)))
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards with τ using cbNorm_nonneg_ps _ _
  · filter_upwards [self_mem_nhdsWithin] with τ hτ using hdiff τ hτ


/-! ### Products of functions of `x` and of `y` on `ℝ^d × ℝ^d` -/

theorem norm_iter_comp_fst_ps {f : Euc d → ℝ} {m : ℕ} (hf : ContDiff ℝ m f) {i : ℕ} (hi : i ≤ m)
    (p : Euc d × Euc d) :
    ‖iteratedFDeriv ℝ i (fun q : Euc d × Euc d => f q.1) p‖ ≤ ‖iteratedFDeriv ℝ i f p.1‖ := by
  have e : (fun q : Euc d × Euc d => f q.1) = f ∘ (ContinuousLinearMap.fst ℝ (Euc d) (Euc d)) := rfl
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hf p (by exact_mod_cast hi)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h1 : ‖ContinuousLinearMap.fst ℝ (Euc d) (Euc d)‖ ≤ 1 := ContinuousLinearMap.norm_fst_le _ _ _
  calc ‖iteratedFDeriv ℝ i f ((ContinuousLinearMap.fst ℝ (Euc d) (Euc d)) p)‖ *
        ‖ContinuousLinearMap.fst ℝ (Euc d) (Euc d)‖ ^ i
      ≤ ‖iteratedFDeriv ℝ i f p.1‖ * 1 ^ i :=
        mul_le_mul (le_of_eq rfl) (pow_le_pow_left₀ (norm_nonneg _) h1 i) (by positivity)
          (norm_nonneg _)
    _ = _ := by simp

theorem norm_iter_comp_snd_ps {f : Euc d → ℝ} {m : ℕ} (hf : ContDiff ℝ m f) {i : ℕ} (hi : i ≤ m)
    (p : Euc d × Euc d) :
    ‖iteratedFDeriv ℝ i (fun q : Euc d × Euc d => f q.2) p‖ ≤ ‖iteratedFDeriv ℝ i f p.2‖ := by
  have e : (fun q : Euc d × Euc d => f q.2) = f ∘ (ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) := rfl
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hf p (by exact_mod_cast hi)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h1 : ‖ContinuousLinearMap.snd ℝ (Euc d) (Euc d)‖ ≤ 1 := ContinuousLinearMap.norm_snd_le _ _ _
  calc ‖iteratedFDeriv ℝ i f ((ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) p)‖ *
        ‖ContinuousLinearMap.snd ℝ (Euc d) (Euc d)‖ ^ i
      ≤ ‖iteratedFDeriv ℝ i f p.2‖ * 1 ^ i :=
        mul_le_mul (le_of_eq rfl) (pow_le_pow_left₀ (norm_nonneg _) h1 i) (by positivity)
          (norm_nonneg _)
    _ = _ := by simp

theorem prod_deriv_bound_ps {j : ℕ} {f g : Torus d → ℝ} (hf : Torus.IsCk (j : WithTop ℕ∞) f)
    (hg : Torus.IsCk (j : WithTop ℕ∞) g) :
    ContDiff ℝ j (lift2 (fun x y => f x * g y)) ∧ ∀ i, i ≤ j → ∀ p : Euc d × Euc d,
      ‖iteratedFDeriv ℝ i (lift2 (fun x y => f x * g y)) p‖ ≤
        2 ^ i * (Torus.cbNorm j f * Torus.cbNorm j g) := by
  have e : lift2 (fun x y => f x * g y) = fun q => Torus.lift f q.1 * Torus.lift g q.2 := rfl
  have hf1 : ContDiff ℝ j (fun q : Euc d × Euc d => Torus.lift f q.1) := hf.comp contDiff_fst
  have hg1 : ContDiff ℝ j (fun q : Euc d × Euc d => Torus.lift g q.2) := hg.comp contDiff_snd
  refine ⟨by rw [e]; exact hf1.mul hg1, fun i hi p => ?_⟩
  rw [e]
  refine (norm_iteratedFDeriv_mul_le hf1 hg1 p (by exact_mod_cast hi)).trans ?_
  calc ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) *
        ‖iteratedFDeriv ℝ m (fun q : Euc d × Euc d => Torus.lift f q.1) p‖ *
          ‖iteratedFDeriv ℝ (i - m) (fun q : Euc d × Euc d => Torus.lift g q.2) p‖
      ≤ ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) * (Torus.cbNorm j f * Torus.cbNorm j g) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hmi : m ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
        have h1 := (norm_iter_comp_fst_ps (m := j) hf (hmi.trans hi) p).trans
          (norm_iter_le_cb_ps hf (hmi.trans hi) p.1)
        have h2 := (norm_iter_comp_snd_ps (m := j) hg (by omega : i - m ≤ j) p).trans
          (norm_iter_le_cb_ps hg (by omega : i - m ≤ j) p.2)
        have hc : (0 : ℝ) ≤ i.choose m := Nat.cast_nonneg _
        calc (i.choose m : ℝ) * ‖iteratedFDeriv ℝ m (fun q : Euc d × Euc d => Torus.lift f q.1) p‖ *
              ‖iteratedFDeriv ℝ (i - m) (fun q : Euc d × Euc d => Torus.lift g q.2) p‖
            ≤ (i.choose m : ℝ) * Torus.cbNorm j f * Torus.cbNorm j g :=
              mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 (norm_nonneg _)
                (mul_nonneg hc (cbNorm_nonneg_ps _ _))
          _ = _ := by ring
    _ = 2 ^ i * (Torus.cbNorm j f * Torus.cbNorm j g) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring

theorem isCk_sub_ps {L : ℕ} {f g : Torus d → ℝ} (hf : Torus.IsCk (L : WithTop ℕ∞) f)
    (hg : Torus.IsCk (L : WithTop ℕ∞) g) : Torus.IsCk (L : WithTop ℕ∞) (fun x => f x - g x) := by
  unfold Torus.IsCk at *
  exact hf.sub hg

theorem prod_cont_ps {j : ℕ} (f g : ℝ → Torus d → ℝ) (t₀ : ℝ)
    (hf : ∀ t, 0 ≤ t → Torus.IsCk (j : WithTop ℕ∞) (f t))
    (hg : ∀ t, 0 ≤ t → Torus.IsCk (j : WithTop ℕ∞) (g t)) (ht₀ : 0 ≤ t₀)
    (hfc : Tendsto (fun t => Torus.cbNorm j (fun x => f t x - f t₀ x)) (𝓝[Set.Ici 0] t₀) (𝓝 0))
    (hgc : Tendsto (fun t => Torus.cbNorm j (fun x => g t x - g t₀ x)) (𝓝[Set.Ici 0] t₀) (𝓝 0))
    (K : ℝ) (hK : ∀ t, 0 ≤ t → Torus.cbNorm j (g t) ≤ K) {i : ℕ} (hi : i ≤ j) (p : Euc d × Euc d) :
    ContinuousWithinAt
      (fun t => iteratedFDeriv ℝ i (lift2 (fun x y => f t x * g t y)) p) (Set.Ici 0) t₀ := by
  unfold ContinuousWithinAt
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun t => 2 ^ i * (Torus.cbNorm j (fun x => f t x - f t₀ x) * K +
      Torus.cbNorm j (f t₀) * Torus.cbNorm j (fun x => g t x - g t₀ x))) (𝓝[Set.Ici 0] t₀) (𝓝 0) := by
    have := ((hfc.mul_const K).add (hgc.const_mul (Torus.cbNorm j (f t₀)))).const_mul ((2 : ℝ) ^ i)
    simpa using this
  refine squeeze_zero' ?_ ?_ hb
  · filter_upwards with t using norm_nonneg _
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 ≤ t := ht
    have hA := isCk_sub_ps (hf t ht') (hf t₀ ht₀)
    have hB := isCk_sub_ps (hg t ht') (hg t₀ ht₀)
    obtain ⟨cdA, bdA⟩ := prod_deriv_bound_ps hA (hg t ht')
    obtain ⟨cdB, bdB⟩ := prod_deriv_bound_ps (hf t₀ ht₀) hB
    have hsplit : lift2 (fun x y => f t x * g t y) =
        (lift2 (fun x y => (f t x - f t₀ x) * g t y) +
          lift2 (fun x y => f t₀ x * (g t y - g t₀ y))) +
        lift2 (fun x y => f t₀ x * g t₀ y) := by
      funext q
      simp only [Pi.add_apply, lift2]
      ring
    have hC := (prod_deriv_bound_ps (hf t₀ ht₀) (hg t₀ ht₀)).1
    have e1 : iteratedFDeriv ℝ i (lift2 (fun x y => f t x * g t y)) p -
        iteratedFDeriv ℝ i (lift2 (fun x y => f t₀ x * g t₀ y)) p =
        iteratedFDeriv ℝ i (lift2 (fun x y => (f t x - f t₀ x) * g t y)) p +
          iteratedFDeriv ℝ i (lift2 (fun x y => f t₀ x * (g t y - g t₀ y))) p := by
      have hAB : ContDiff ℝ j (lift2 (fun x y => (f t x - f t₀ x) * g t y) +
          lift2 (fun x y => f t₀ x * (g t y - g t₀ y))) := cdA.add cdB
      rw [hsplit, iteratedFDeriv_add_apply (hAB.contDiffAt.of_le (by exact_mod_cast hi))
        (hC.contDiffAt.of_le (by exact_mod_cast hi)),
        iteratedFDeriv_add_apply (cdA.contDiffAt.of_le (by exact_mod_cast hi))
          (cdB.contDiffAt.of_le (by exact_mod_cast hi))]
      exact add_sub_cancel_right _ _
    show ‖iteratedFDeriv ℝ i (lift2 (fun x y => f t x * g t y)) p -
        iteratedFDeriv ℝ i (lift2 (fun x y => f t₀ x * g t₀ y)) p‖ ≤ _
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    have h1 := bdA i hi p
    have h2 := bdB i hi p
    have hc1 := cbNorm_nonneg_ps j (fun x => f t x - f t₀ x)
    have hc2 := cbNorm_nonneg_ps j (f t₀)
    have hc3 := cbNorm_nonneg_ps j (fun x => g t x - g t₀ x)
    have hK' := hK t ht'
    have hpow : (0 : ℝ) ≤ 2 ^ i := by positivity
    calc ‖iteratedFDeriv ℝ i (lift2 (fun x y => (f t x - f t₀ x) * g t y)) p‖ +
          ‖iteratedFDeriv ℝ i (lift2 (fun x y => f t₀ x * (g t y - g t₀ y))) p‖
        ≤ 2 ^ i * (Torus.cbNorm j (fun x => f t x - f t₀ x) * Torus.cbNorm j (g t)) +
          2 ^ i * (Torus.cbNorm j (f t₀) * Torus.cbNorm j (fun x => g t x - g t₀ x)) :=
          add_le_add h1 h2
      _ ≤ 2 ^ i * (Torus.cbNorm j (fun x => f t x - f t₀ x) * K) +
          2 ^ i * (Torus.cbNorm j (f t₀) * Torus.cbNorm j (fun x => g t x - g t₀ x)) := by
          gcongr
      _ = _ := by ring


/-! ### Series of sums of products -/

theorem term_bound_ps {j : ℕ} {f₁ g₁ f₂ g₂ : Torus d → ℝ}
    (h1 : Torus.IsCk (j : WithTop ℕ∞) f₁) (h2 : Torus.IsCk (j : WithTop ℕ∞) g₁)
    (h3 : Torus.IsCk (j : WithTop ℕ∞) f₂) (h4 : Torus.IsCk (j : WithTop ℕ∞) g₂) :
    ContDiff ℝ j (lift2 (fun x y => f₁ x * g₁ y + f₂ x * g₂ y)) ∧ ∀ i, i ≤ j →
      ∀ p : Euc d × Euc d,
        ‖iteratedFDeriv ℝ i (lift2 (fun x y => f₁ x * g₁ y + f₂ x * g₂ y)) p‖ ≤
          2 ^ j * (Torus.cbNorm j f₁ * Torus.cbNorm j g₁ + Torus.cbNorm j f₂ * Torus.cbNorm j g₂) := by
  obtain ⟨c1, b1⟩ := prod_deriv_bound_ps h1 h2
  obtain ⟨c2, b2⟩ := prod_deriv_bound_ps h3 h4
  have e : lift2 (fun x y => f₁ x * g₁ y + f₂ x * g₂ y) =
      lift2 (fun x y => f₁ x * g₁ y) + lift2 (fun x y => f₂ x * g₂ y) := rfl
  refine ⟨by rw [e]; exact c1.add c2, fun i hi p => ?_⟩
  rw [e, iteratedFDeriv_add_apply (c1.contDiffAt.of_le (by exact_mod_cast hi))
    (c2.contDiffAt.of_le (by exact_mod_cast hi))]
  refine (norm_add_le _ _).trans ?_
  have hp : (2 : ℝ) ^ i ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hi
  have n1 := cbNorm_nonneg_ps j f₁
  have n2 := cbNorm_nonneg_ps j g₁
  have n3 := cbNorm_nonneg_ps j f₂
  have n4 := cbNorm_nonneg_ps j g₂
  calc _ ≤ 2 ^ i * (Torus.cbNorm j f₁ * Torus.cbNorm j g₁) +
        2 ^ i * (Torus.cbNorm j f₂ * Torus.cbNorm j g₂) := add_le_add (b1 i hi p) (b2 i hi p)
    _ ≤ 2 ^ j * (Torus.cbNorm j f₁ * Torus.cbNorm j g₁) +
        2 ^ j * (Torus.cbNorm j f₂ * Torus.cbNorm j g₂) := by gcongr
    _ = _ := by ring

theorem series_assembly_ps {j : ℕ} (F1 G1 F2 G2 : Lattice d → Torus d → ℝ)
    (hF1 : ∀ k, Torus.IsCk (j : WithTop ℕ∞) (F1 k)) (hG1 : ∀ k, Torus.IsCk (j : WithTop ℕ∞) (G1 k))
    (hF2 : ∀ k, Torus.IsCk (j : WithTop ℕ∞) (F2 k)) (hG2 : ∀ k, Torus.IsCk (j : WithTop ℕ∞) (G2 k))
    (B : Lattice d → ℝ) (hB : Summable B)
    (hbd : ∀ k, Torus.cbNorm j (F1 k) * Torus.cbNorm j (G1 k) +
      Torus.cbNorm j (F2 k) * Torus.cbNorm j (G2 k) ≤ B k)
    (Ψ : Torus d → Torus d → ℝ)
    (hΨ : ∀ x y, Ψ x y = ∑' k, (F1 k x * G1 k y + F2 k x * G2 k y)) :
    ContDiff ℝ j (lift2 Ψ) ∧ cbNorm2 j Ψ ≤ (j + 1) * (2 ^ j * ∑' k, B k) ∧
      ∀ i, i ≤ j → ∀ p : Euc d × Euc d, iteratedFDeriv ℝ i (lift2 Ψ) p =
        ∑' k, iteratedFDeriv ℝ i (lift2 (fun x y => F1 k x * G1 k y + F2 k x * G2 k y)) p := by
  have hterm := fun k => term_bound_ps (hF1 k) (hG1 k) (hF2 k) (hG2 k)
  obtain ⟨h1, h2, h3⟩ := cd_tsum_ps (fun k => lift2 (fun x y => F1 k x * G1 k y + F2 k x * G2 k y)) j
    (fun k => (hterm k).1) (fun k => 2 ^ j * B k) (hB.mul_left _)
    (fun k i hi p => ((hterm k).2 i hi p).trans (by
      have := hbd k
      gcongr))
  have e : lift2 Ψ = fun p => ∑' k, lift2 (fun x y => F1 k x * G1 k y + F2 k x * G2 k y) p := by
    funext p; exact hΨ _ _
  have hcd : ContDiff ℝ j (lift2 Ψ) := by rw [e]; exact h1
  have hder : ∀ i, i ≤ j → ∀ p : Euc d × Euc d, iteratedFDeriv ℝ i (lift2 Ψ) p =
      ∑' k, iteratedFDeriv ℝ i (lift2 (fun x y => F1 k x * G1 k y + F2 k x * G2 k y)) p := by
    intro i hi p; rw [e]; exact h2 i hi p
  refine ⟨hcd, ?_, hder⟩
  unfold cbNorm2
  calc ∑ i ∈ Finset.range (j + 1), ⨆ p : Euc d × Euc d, ‖iteratedFDeriv ℝ i (lift2 Ψ) p‖
      ≤ ∑ i ∈ Finset.range (j + 1), (2 ^ j * ∑' k, B k) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        refine ciSup_le fun p => ?_
        have := h3 i hij p
        rw [tsum_mul_left] at this
        rw [e]
        exact this
    _ = _ := by simp

set_option synthInstance.maxHeartbeats 400000 in
theorem completeSpace_mlin_ps (i d : ℕ) : CompleteSpace ((Euc d × Euc d) [×i]→L[ℝ] ℝ) := by
  have : SequentialSpace (Fin i → Euc d × Euc d) := inferInstance
  exact ContinuousMultilinearMap.instCompleteSpace

theorem series_cont_ps {j : ℕ} (F1 G1 F2 G2 : Lattice d → ℝ → Torus d → ℝ)
    (hF1 : ∀ k t, 0 ≤ t → Torus.IsCk (j : WithTop ℕ∞) (F1 k t))
    (hG1 : ∀ k t, 0 ≤ t → Torus.IsCk (j : WithTop ℕ∞) (G1 k t))
    (hF2 : ∀ k t, 0 ≤ t → Torus.IsCk (j : WithTop ℕ∞) (F2 k t))
    (hG2 : ∀ k t, 0 ≤ t → Torus.IsCk (j : WithTop ℕ∞) (G2 k t))
    (B : Lattice d → ℝ) (hB : Summable B)
    (hbd : ∀ k t, 0 ≤ t → Torus.cbNorm j (F1 k t) * Torus.cbNorm j (G1 k t) +
      Torus.cbNorm j (F2 k t) * Torus.cbNorm j (G2 k t) ≤ B k)
    (K1 K2 : Lattice d → ℝ) (hK1 : ∀ k t, 0 ≤ t → Torus.cbNorm j (G1 k t) ≤ K1 k)
    (hK2 : ∀ k t, 0 ≤ t → Torus.cbNorm j (G2 k t) ≤ K2 k)
    (hc : ∀ k t₀, 0 ≤ t₀ →
      Tendsto (fun t => Torus.cbNorm j (fun x => F1 k t x - F1 k t₀ x)) (𝓝[Set.Ici 0] t₀) (𝓝 0) ∧
      Tendsto (fun t => Torus.cbNorm j (fun x => G1 k t x - G1 k t₀ x)) (𝓝[Set.Ici 0] t₀) (𝓝 0) ∧
      Tendsto (fun t => Torus.cbNorm j (fun x => F2 k t x - F2 k t₀ x)) (𝓝[Set.Ici 0] t₀) (𝓝 0) ∧
      Tendsto (fun t => Torus.cbNorm j (fun x => G2 k t x - G2 k t₀ x)) (𝓝[Set.Ici 0] t₀) (𝓝 0))
    (Ψ : ℝ → Torus d → Torus d → ℝ)
    (hΨ : ∀ t, 0 ≤ t → ∀ x y, Ψ t x y = ∑' k, (F1 k t x * G1 k t y + F2 k t x * G2 k t y))
    {i : ℕ} (hi : i ≤ j) (p : Euc d × Euc d) :
    ContinuousOn (fun t => iteratedFDeriv ℝ i (lift2 (Ψ t)) p) (Set.Ici 0) := by
  have hform : ∀ t, 0 ≤ t → iteratedFDeriv ℝ i (lift2 (Ψ t)) p =
      ∑' k, iteratedFDeriv ℝ i (lift2 (fun x y => F1 k t x * G1 k t y + F2 k t x * G2 k t y)) p :=
    fun t ht => (series_assembly_ps (fun k => F1 k t) (fun k => G1 k t) (fun k => F2 k t)
      (fun k => G2 k t) (fun k => hF1 k t ht) (fun k => hG1 k t ht) (fun k => hF2 k t ht)
      (fun k => hG2 k t ht) B hB (fun k => hbd k t ht) (Ψ t) (hΨ t ht)).2.2 i hi p
  refine ContinuousOn.congr (f := fun t => ∑' k, iteratedFDeriv ℝ i
    (lift2 (fun x y => F1 k t x * G1 k t y + F2 k t x * G2 k t y)) p) ?_ (fun t ht => hform t ht)
  haveI := completeSpace_mlin_ps i d
  refine continuousOn_tsum (u := fun k => 2 ^ j * B k) (fun k => ?_) (hB.mul_left _)
    (fun k t ht => ?_)
  · intro t₀ ht₀
    have ht₀' : 0 ≤ t₀ := ht₀
    obtain ⟨c1, c2, c3, c4⟩ := hc k t₀ ht₀'
    have p1 := prod_cont_ps (F1 k) (G1 k) t₀ (hF1 k) (hG1 k) ht₀' c1 c2 (K1 k) (hK1 k) hi p
    have p2 := prod_cont_ps (F2 k) (G2 k) t₀ (hF2 k) (hG2 k) ht₀' c3 c4 (K2 k) (hK2 k) hi p
    have key : ∀ t, 0 ≤ t → iteratedFDeriv ℝ i
        (lift2 (fun x y => F1 k t x * G1 k t y + F2 k t x * G2 k t y)) p =
        iteratedFDeriv ℝ i (lift2 (fun x y => F1 k t x * G1 k t y)) p +
          iteratedFDeriv ℝ i (lift2 (fun x y => F2 k t x * G2 k t y)) p := by
      intro t ht
      have c1' := (prod_deriv_bound_ps (hF1 k t ht) (hG1 k t ht)).1
      have c2' := (prod_deriv_bound_ps (hF2 k t ht) (hG2 k t ht)).1
      exact iteratedFDeriv_add_apply (c1'.contDiffAt.of_le (by exact_mod_cast hi))
        (c2'.contDiffAt.of_le (by exact_mod_cast hi))
    have hsum := p1.add p2
    refine hsum.congr (fun t ht => key t ht) (key t₀ ht₀')
  · obtain ⟨-, hb⟩ := term_bound_ps (hF1 k t ht) (hG1 k t ht) (hF2 k t ht) (hG2 k t ht)
    refine (hb i hi p).trans ?_
    have := hbd k t ht
    gcongr


theorem decay_core_ps {j L J : ℕ} (hJL : 2 * L + d + 1 ≤ J) {M c C1 : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hC1 : 0 ≤ C1) (S : ℝ → (Torus d → ℝ) → Torus d → ℝ)
    (hSA : ∀ t, 0 ≤ t → ∀ h : Torus d → ℝ, Torus.IsCk (L : WithTop ℕ∞) h →
      Torus.IsCk (j : WithTop ℕ∞) (S t h) ∧
        Torus.cbNorm j (S t h) ≤ M * Real.exp (-c * t) * Torus.cbNorm L h)
    (hSB : ∀ h : Torus d → ℝ, Torus.IsCk (L : WithTop ℕ∞) h → ∀ t₀, 0 ≤ t₀ →
      Tendsto (fun t => Torus.cbNorm j (fun x => S t h x - S t₀ h x)) (𝓝[Set.Ici 0] t₀) (𝓝 0))
    (hsl : ∀ R : Torus d → Torus d → ℝ, IsCk2 J R → ∀ k : Lattice d,
      Torus.IsCk (L : WithTop ℕ∞) (fun y => (sliceCoeff R k y).re) ∧
      Torus.IsCk (L : WithTop ℕ∞) (fun y => (sliceCoeff R k y).im) ∧
      Torus.cbNorm L (fun y => (sliceCoeff R k y).re) ≤
        C1 * cbNorm2 J R * Lattice.jp k ^ (-((J - L : ℕ) : ℝ)) ∧
      Torus.cbNorm L (fun y => (sliceCoeff R k y).im) ≤
        C1 * cbNorm2 J R * Lattice.jp k ^ (-((J - L : ℕ) : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : Torus d → Torus d → ℝ), IsCk2 J R →
      ∀ Ψ : ℝ → Torus d → Torus d → ℝ,
      (∀ t, 0 ≤ t → ∀ x y, Ψ t x y = ∑' k : Lattice d,
        (S t (Torus.cosMode k) x * S t (fun y' => (sliceCoeff R k y').re) y -
          S t (Torus.sinMode k) x * S t (fun y' => (sliceCoeff R k y').im) y)) →
      ∀ t, 0 ≤ t → IsCk2 j (Ψ t) ∧ cbNorm2 j (Ψ t) ≤ C * Real.exp (-c * t) * cbNorm2 J R ∧
        ∀ (i : ℕ), i ≤ j → ∀ p : Euc d × Euc d,
          ContinuousOn (fun t' => iteratedFDeriv ℝ i (lift2 (Ψ t')) p) (Set.Ici 0) := by
  set q : ℝ := (L : ℝ) + -((J - L : ℕ) : ℝ) with hq
  have hq' : q < -(d : ℝ) := by
    have : (2 * L + d + 1 : ℝ) ≤ J := by exact_mod_cast hJL
    rw [hq, Nat.cast_sub (by omega : L ≤ J)]
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    linarith
  have hjpsum : Summable fun k : Lattice d => Lattice.jp k ^ q := summable_jp_rpow_ps q hq'
  set Sg0 : ℝ := ∑' k : Lattice d, Lattice.jp k ^ q with hSg
  have hSg0 : 0 ≤ Sg0 := tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos k).le _
  set Kc : ℝ := 2 * (M * M * ((L : ℝ) + 1) * C1) with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  refine ⟨((j : ℝ) + 1) * (2 ^ j * (Kc * Sg0)) + 1, by positivity, ?_⟩
  intro R hR Ψ hΨ
  set G : ℝ := cbNorm2 J R with hG
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  -- the four families
  set F1 : Lattice d → ℝ → Torus d → ℝ := fun k t => S t (Torus.cosMode k) with hF1
  set G1 : Lattice d → ℝ → Torus d → ℝ := fun k t => S t (fun y' => (sliceCoeff R k y').re) with hG1
  set F2 : Lattice d → ℝ → Torus d → ℝ := fun k t => S t (Torus.sinMode k) with hF2
  set G2 : Lattice d → ℝ → Torus d → ℝ := fun k t y => (-1) * S t (fun y' => (sliceCoeff R k y').im) y
    with hG2
  have hcosb : ∀ k : Lattice d, Torus.cbNorm L (Torus.cosMode k : Torus d → ℝ) ≤
      (L + 1) * Lattice.jp k ^ L := by
    intro k
    have := cbNorm_trigTerm_le 1 0 k L
    rw [← cosMode_eq_trig] at this
    simpa using this
  have hsinb : ∀ k : Lattice d, Torus.cbNorm L (Torus.sinMode k : Torus d → ℝ) ≤
      (L + 1) * Lattice.jp k ^ L := by
    intro k
    have := cbNorm_trigTerm_le 0 1 k L
    rw [← sinMode_eq_trig] at this
    simpa using this
  -- regularity
  have hF1c : ∀ k t, 0 ≤ t → Torus.IsCk (j : WithTop ℕ∞) (F1 k t) :=
    fun k t ht => (hSA t ht _ (isCk_cos_ps k L)).1
  have hF2c : ∀ k t, 0 ≤ t → Torus.IsCk (j : WithTop ℕ∞) (F2 k t) :=
    fun k t ht => (hSA t ht _ (isCk_sin_ps k L)).1
  have hG1c : ∀ k t, 0 ≤ t → Torus.IsCk (j : WithTop ℕ∞) (G1 k t) :=
    fun k t ht => (hSA t ht _ (hsl R hR k).1).1
  have hB' : ∀ k t, 0 ≤ t → Torus.IsCk (j : WithTop ℕ∞)
      (S t (fun y' => (sliceCoeff R k y').im)) :=
    fun k t ht => (hSA t ht _ (hsl R hR k).2.1).1
  have hG2c : ∀ k t, 0 ≤ t → Torus.IsCk (j : WithTop ℕ∞) (G2 k t) :=
    fun k t ht => isCk_const_mul_ps (hB' k t ht) (-1)
  -- norm bounds
  have hb1 : ∀ k t, 0 ≤ t → Torus.cbNorm j (F1 k t) ≤
      M * Real.exp (-c * t) * ((L + 1) * Lattice.jp k ^ L) := fun k t ht =>
    ((hSA t ht _ (isCk_cos_ps k L)).2).trans (by
      have := Real.exp_pos (-c * t)
      gcongr
      exact hcosb k)
  have hb3 : ∀ k t, 0 ≤ t → Torus.cbNorm j (F2 k t) ≤
      M * Real.exp (-c * t) * ((L + 1) * Lattice.jp k ^ L) := fun k t ht =>
    ((hSA t ht _ (isCk_sin_ps k L)).2).trans (by
      have := Real.exp_pos (-c * t)
      gcongr
      exact hsinb k)
  have hb2 : ∀ k t, 0 ≤ t → Torus.cbNorm j (G1 k t) ≤
      M * Real.exp (-c * t) * (C1 * G * Lattice.jp k ^ (-((J - L : ℕ) : ℝ))) := fun k t ht =>
    ((hSA t ht _ (hsl R hR k).1).2).trans (by
      have := Real.exp_pos (-c * t)
      gcongr
      exact (hsl R hR k).2.2.1)
  have hb4 : ∀ k t, 0 ≤ t → Torus.cbNorm j (G2 k t) ≤
      M * Real.exp (-c * t) * (C1 * G * Lattice.jp k ^ (-((J - L : ℕ) : ℝ))) := fun k t ht => by
    have h1 := cbNorm_smul_le_ps (hB' k t ht) (-1)
    rw [abs_neg, abs_one, one_mul] at h1
    refine h1.trans (((hSA t ht _ (hsl R hR k).2.1).2).trans ?_)
    have := Real.exp_pos (-c * t)
    gcongr
    exact (hsl R hR k).2.2.2
  -- the product bounds
  have hprod : ∀ k t, 0 ≤ t → Torus.cbNorm j (F1 k t) * Torus.cbNorm j (G1 k t) +
      Torus.cbNorm j (F2 k t) * Torus.cbNorm j (G2 k t) ≤
        (Kc * G * Real.exp (-c * t)) * Lattice.jp k ^ q := by
    intro k t ht
    have he0 := Real.exp_pos (-c * t)
    have he1 : Real.exp (-c * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hjL0 : 0 ≤ Lattice.jp k ^ L := pow_nonneg (Torus.jp_pos k).le L
    have hjm0 := Real.rpow_nonneg (Torus.jp_pos k).le (-((J - L : ℕ) : ℝ))
    have hn1 := cbNorm_nonneg_ps j (F1 k t)
    have hn2 := cbNorm_nonneg_ps j (G1 k t)
    have hn3 := cbNorm_nonneg_ps j (F2 k t)
    have hn4 := cbNorm_nonneg_ps j (G2 k t)
    have hA : 0 ≤ M * Real.exp (-c * t) * ((L + 1) * Lattice.jp k ^ L) := by positivity
    have hBn : 0 ≤ M * Real.exp (-c * t) * (C1 * G * Lattice.jp k ^ (-((J - L : ℕ) : ℝ))) := by
      positivity
    have h12 := mul_le_mul (hb1 k t ht) (hb2 k t ht) hn2 hA
    have h34 := mul_le_mul (hb3 k t ht) (hb4 k t ht) hn4 hA
    have hjq : Lattice.jp k ^ L * Lattice.jp k ^ (-((J - L : ℕ) : ℝ)) = Lattice.jp k ^ q := by
      rw [hq]; exact jp_pow_mul_rpow_ps k L _
    have hee : Real.exp (-c * t) * Real.exp (-c * t) ≤ Real.exp (-c * t) := by nlinarith
    calc _ ≤ 2 * (M * Real.exp (-c * t) * ((L + 1) * Lattice.jp k ^ L) *
          (M * Real.exp (-c * t) * (C1 * G * Lattice.jp k ^ (-((J - L : ℕ) : ℝ))))) := by linarith
      _ = (2 * (M * M * ((L : ℝ) + 1) * C1) * G) * (Real.exp (-c * t) * Real.exp (-c * t)) *
          (Lattice.jp k ^ L * Lattice.jp k ^ (-((J - L : ℕ) : ℝ))) := by ring
      _ ≤ (Kc * G) * Real.exp (-c * t) * Lattice.jp k ^ q := by
          rw [hjq, ← hKc]
          have hKG : 0 ≤ Kc * G := mul_nonneg hKc0 hG0
          have hjq0 : 0 ≤ Lattice.jp k ^ q := Real.rpow_nonneg (Torus.jp_pos k).le _
          have := mul_le_mul_of_nonneg_left hee hKG
          exact mul_le_mul_of_nonneg_right this hjq0
      _ = _ := by ring
  have hΨ' : ∀ t, 0 ≤ t → ∀ x y, Ψ t x y = ∑' k : Lattice d,
      (F1 k t x * G1 k t y + F2 k t x * G2 k t y) := by
    intro t ht x y
    rw [hΨ t ht x y]
    exact tsum_congr fun k => by simp only [hF1, hG1, hF2, hG2]; ring
  intro t ht
  have he0 := (Real.exp_pos (-c * t)).le
  have hsB : Summable fun k : Lattice d => (Kc * G * Real.exp (-c * t)) * Lattice.jp k ^ q :=
    hjpsum.mul_left _
  obtain ⟨hcd, hcb, -⟩ := series_assembly_ps (fun k => F1 k t) (fun k => G1 k t)
    (fun k => F2 k t) (fun k => G2 k t) (fun k => hF1c k t ht) (fun k => hG1c k t ht)
    (fun k => hF2c k t ht) (fun k => hG2c k t ht)
    (fun k => (Kc * G * Real.exp (-c * t)) * Lattice.jp k ^ q) hsB (fun k => hprod k t ht)
    (Ψ t) (hΨ' t ht)
  refine ⟨hcd, ?_, fun i hi p => ?_⟩
  · refine hcb.trans ?_
    rw [tsum_mul_left]
    have h1 : 0 ≤ Real.exp (-c * t) * G := mul_nonneg he0 hG0
    nlinarith
  · have hsB0 : Summable fun k : Lattice d => (Kc * G) * Lattice.jp k ^ q := hjpsum.mul_left _
    have hexp1 : ∀ t : ℝ, 0 ≤ t → Real.exp (-c * t) ≤ 1 :=
      fun t ht => Real.exp_le_one_iff.2 (by nlinarith)
    refine series_cont_ps F1 G1 F2 G2 hF1c hG1c hF2c hG2c (fun k => (Kc * G) * Lattice.jp k ^ q)
      hsB0 (fun k t ht => (hprod k t ht).trans (by
        have hKG : 0 ≤ Kc * G := mul_nonneg hKc0 hG0
        have hjq0 : 0 ≤ Lattice.jp k ^ q := Real.rpow_nonneg (Torus.jp_pos k).le _
        have := mul_le_mul_of_nonneg_left (hexp1 t ht) hKG
        exact mul_le_mul_of_nonneg_right (by linarith) hjq0))
      (fun k => M * (C1 * G * Lattice.jp k ^ (-((J - L : ℕ) : ℝ))))
      (fun k => M * (C1 * G * Lattice.jp k ^ (-((J - L : ℕ) : ℝ))))
      (fun k t ht => (hb2 k t ht).trans (by
        have hn : 0 ≤ M * (C1 * G * Lattice.jp k ^ (-((J - L : ℕ) : ℝ))) :=
          mul_nonneg hM.le (mul_nonneg (mul_nonneg hC1 hG0) (Real.rpow_nonneg (Torus.jp_pos k).le _))
        calc M * Real.exp (-c * t) * (C1 * G * Lattice.jp k ^ (-((J - L : ℕ) : ℝ)))
            = Real.exp (-c * t) * (M * (C1 * G * Lattice.jp k ^ (-((J - L : ℕ) : ℝ)))) := by ring
          _ ≤ 1 * (M * (C1 * G * Lattice.jp k ^ (-((J - L : ℕ) : ℝ)))) :=
              mul_le_mul_of_nonneg_right (hexp1 t ht) hn
          _ = _ := one_mul _))
      (fun k t ht => (hb4 k t ht).trans (by
        have hn : 0 ≤ M * (C1 * G * Lattice.jp k ^ (-((J - L : ℕ) : ℝ))) :=
          mul_nonneg hM.le (mul_nonneg (mul_nonneg hC1 hG0) (Real.rpow_nonneg (Torus.jp_pos k).le _))
        calc M * Real.exp (-c * t) * (C1 * G * Lattice.jp k ^ (-((J - L : ℕ) : ℝ)))
            = Real.exp (-c * t) * (M * (C1 * G * Lattice.jp k ^ (-((J - L : ℕ) : ℝ)))) := by ring
          _ ≤ 1 * (M * (C1 * G * Lattice.jp k ^ (-((J - L : ℕ) : ℝ)))) :=
              mul_le_mul_of_nonneg_right (hexp1 t ht) hn
          _ = _ := one_mul _))
      (fun k t₀ ht₀ => ⟨hSB _ (isCk_cos_ps k L) t₀ ht₀, hSB _ (hsl R hR k).1 t₀ ht₀,
        hSB _ (isCk_sin_ps k L) t₀ ht₀, ?_⟩) Ψ hΨ' hi p
    -- continuity of the `G2` differences
    have hlim := hSB _ (hsl R hR k).2.1 t₀ ht₀
    refine squeeze_zero' ?_ ?_ hlim
    · filter_upwards with t using cbNorm_nonneg_ps _ _
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have hd1 := isCk_sub_ps (hB' k t ht) (hB' k t₀ ht₀)
      have h1 := cbNorm_smul_le_ps hd1 (-1)
      have e : (fun x => G2 k t x - G2 k t₀ x) =
          fun x => (-1) * (S t (fun y' => (sliceCoeff R k y').im) x -
            S t₀ (fun y' => (sliceCoeff R k y').im) x) := by
        funext x; simp only [hG2]; ring
      rw [e]
      simpa using h1

end SeriesAux

theorem pairSemigroup_eq_tsum (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (J : ℕ) (hJ : 3 * mStar d + 2 * d + 8 ≤ J) (R : Torus d → Torus d → ℝ)
    (hR : IsCk2 J R) (t : ℝ) (ht : 0 ≤ t) (x y : Torus d) :
    pairSemigroup (mfData d s hs0 hsd V β hβ) ρβ t R x y =
      ∑' k : Lattice d,
        (equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ t (Torus.cosMode k) x *
            equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ t (fun y' => (sliceCoeff R k y').re) y -
          equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ t (Torus.sinMode k) x *
            equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ t (fun y' => (sliceCoeff R k y').im) y) := by
  -- Route: (1) in `x`, `R(·,y') = ∑_k trigTerm (Re R̂_k(y')) (-Im R̂_k(y')) k` converges in `C^L`
  -- (`L = mStar d + 4`), so `S(t)` passes through (`series_passthrough`);
  -- (2) the resulting function of `y'` is again a `C^L`-convergent series (decay of the slice
  -- coefficients vs. the growth `⟨k⟩^L` of `S(t)cos_k`, `S(t)sin_k`), so `S(t)` passes through again.
  have hd1 : 1 ≤ d := by omega
  have h3 := ClassicalPart.three_le_mStar d
  obtain ⟨c₀, Λ₀, H⟩ := frozenHyp_of_smooth s hs0 hsd β hβ V hV ρβ hρβ hρC hpos (2 * mStar d + 4)
  have hDe : mfData d s hs0 hsd V β hβ = mfData d s H.hs0 H.hsd V β H.hβ := rfl
  rw [hDe]
  set L : ℕ := mStar d + 4 with hL
  have hJL : 2 * L + d + 1 ≤ J := by omega
  have hJd : (d : ℝ) / 2 < J := by
    have : (d : ℝ) + 1 ≤ J := by exact_mod_cast (by omega : d + 1 ≤ J)
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hjL : (d : ℝ) / 2 + ((0 : ℕ) : ℝ) < (L : ℝ) := by
    have := MFAdjoint.mStar_gt d
    rw [hL]; push_cast; linarith
  have hH' : MFAdjoint.FrozenHyp d s (L + mStar d) β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ := H.mono (by omega)
  obtain ⟨M, c, hM, hc, hbd⟩ := S_cb_bound hd1 s 0 L (by omega) hjL β⁻¹ β⁻¹ c₀ Λ₀
  obtain ⟨C0, hC0, hsl0⟩ := exists_sliceCoeff_bound (d := d) 0 J
  obtain ⟨C1, hC1, hsl1⟩ := exists_sliceCoeff_bound (d := d) L (J - L)
  have hG0 : 0 ≤ cbNorm2 J R :=
    Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  set G := cbNorm2 J R with hG
  set S := equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ t with hS
  set a : Lattice d → Torus d → ℝ := fun k y' => (sliceCoeff R k y').re with ha
  set b : Lattice d → Torus d → ℝ := fun k y' => (sliceCoeff R k y').im with hb
  -- bounds on `S(t)` of a trigonometric term at the point `x`
  have hStrig : ∀ (a b : ℝ) (k : Lattice d),
      |S (trigTerm a b k) x| ≤ M * ((L + 1) * ((|a| + |b|) * Lattice.jp k ^ L)) := by
    intro a b k
    obtain ⟨hSk, hSb⟩ := hbd β V ρβ hH' (trigTerm a b k) (trigTerm_isCk a b k L) t ht
    refine (abs_le_cb_ps hSk x).trans (hSb.trans ?_)
    have hexp : Real.exp (-c * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    calc M * Real.exp (-c * t) * Torus.cbNorm L (trigTerm a b k)
        ≤ M * 1 * Torus.cbNorm L (trigTerm a b k) := by
          have := cbNorm_nonneg_ps L (trigTerm a b k)
          gcongr
      _ ≤ M * ((L + 1) * ((|a| + |b|) * Lattice.jp k ^ L)) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left (cbNorm_trigTerm_le a b k L) hM.le
  have hAk : ∀ k, |S (Torus.cosMode k) x| ≤ M * ((L + 1) * Lattice.jp k ^ L) := by
    intro k
    have := hStrig 1 0 k
    rw [← cosMode_eq_trig] at this
    simpa using this
  have hBk : ∀ k, |S (Torus.sinMode k) x| ≤ M * ((L + 1) * Lattice.jp k ^ L) := by
    intro k
    have := hStrig 0 1 k
    rw [← sinMode_eq_trig] at this
    simpa using this
  -- slice bounds
  have hre0 : ∀ k y', |a k y'| ≤ C0 * G * Lattice.jp k ^ (-(J : ℝ)) := by
    intro k y'
    obtain ⟨h1, -, h3', -⟩ := hsl0 J (by omega) R hR k
    exact (abs_le_cb_ps h1 y').trans h3'
  have him0 : ∀ k y', |b k y'| ≤ C0 * G * Lattice.jp k ^ (-(J : ℝ)) := by
    intro k y'
    obtain ⟨-, h2, -, h4⟩ := hsl0 J (by omega) R hR k
    exact (abs_le_cb_ps h2 y').trans h4
  -- Step 1
  have hjpsum1 : Summable fun k : Lattice d => Lattice.jp k ^ ((L : ℝ) + -(J : ℝ)) :=
    summable_jp_rpow_ps _ (by
      have : (2 * L + d + 1 : ℝ) ≤ J := by exact_mod_cast hJL
      push_cast at this ⊢
      have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      linarith)
  have step1 : ∀ y' : Torus d, S (fun x' => R x' y') x =
      ∑' k : Lattice d, (a k y' * S (Torus.cosMode k) x + (-(b k y')) * S (Torus.sinMode k) x) := by
    intro y'
    have hg : ∀ k, Torus.IsCk (L : WithTop ℕ∞) (trigTerm (a k y') (-(b k y')) k) :=
      fun k => trigTerm_isCk _ _ k L
    have hsum : Summable fun k : Lattice d =>
        Torus.cbNorm L (trigTerm (a k y') (-(b k y')) k) := by
      refine Summable.of_nonneg_of_le (fun k => cbNorm_nonneg_ps _ _) (fun k => ?_)
        (hjpsum1.mul_left ((L + 1) * (2 * (C0 * G))))
      refine (cbNorm_trigTerm_le _ _ k L).trans ?_
      have h1 := hre0 k y'
      have h2 := him0 k y'
      rw [abs_neg]
      have hjp := Real.rpow_nonneg (Torus.jp_pos k).le (-(J : ℝ))
      have hjL' := Real.rpow_nonneg (Torus.jp_pos k).le (L : ℝ)
      rw [← jp_pow_mul_rpow_ps k L (-(J : ℝ))]
      have hP : 0 ≤ Lattice.jp k ^ L := pow_nonneg (Torus.jp_pos k).le L
      calc ((L : ℝ) + 1) * ((|a k y'| + |b k y'|) * Lattice.jp k ^ L)
          ≤ ((L : ℝ) + 1) * ((C0 * G * Lattice.jp k ^ (-(J : ℝ)) +
              C0 * G * Lattice.jp k ^ (-(J : ℝ))) * Lattice.jp k ^ L) := by gcongr
        _ = _ := by ring
    have hpass := series_passthrough hd1 s _ _ c₀ Λ₀ β V ρβ H (fun k => trigTerm (a k y') (-(b k y')) k)
      hg hsum ht x
    have hfun : (fun y => ∑' k, trigTerm (a k y') (-(b k y')) k y) = fun x' => R x' y' := by
      funext x'
      obtain ⟨e1, e2⟩ := eq_toFun_sliceCoeff J hJd R hR x' y'
      rw [e1, slice_re_expansion _ e2 x']
    rw [hfun] at hpass
    exact Eq.trans hpass.tsum_eq.symm (tsum_congr fun k => S_trig_ps hd1 H _ _ k ht x)
  -- Step 2
  set h : Lattice d → Torus d → ℝ := fun k y' =>
    S (Torus.cosMode k) x * a k y' + (-(S (Torus.sinMode k) x)) * b k y' with hh
  have hjpsum2 : Summable fun k : Lattice d =>
      Lattice.jp k ^ ((L : ℝ) + -((J - L : ℕ) : ℝ)) :=
    summable_jp_rpow_ps _ (by
      have : (2 * L + d + 1 : ℝ) ≤ J := by exact_mod_cast hJL
      rw [Nat.cast_sub (by omega : L ≤ J)]
      have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      linarith)
  have hhck : ∀ k, Torus.IsCk (L : WithTop ℕ∞) (h k) := by
    intro k
    obtain ⟨h1, h2, -, -⟩ := hsl1 J (by omega) R hR k
    exact (isCk_const_mul_ps h1 _).add (isCk_const_mul_ps h2 _)
  have hhsum : Summable fun k : Lattice d => Torus.cbNorm L (h k) := by
    refine Summable.of_nonneg_of_le (fun k => cbNorm_nonneg_ps _ _) (fun k => ?_)
      (hjpsum2.mul_left (2 * (M * (L + 1)) * (C1 * G)))
    obtain ⟨h1, h2, h3', h4⟩ := hsl1 J (by omega) R hR k
    have hadd := Torus.cbNorm_add_le L (fun y => S (Torus.cosMode k) x * a k y)
      (fun y => (-(S (Torus.sinMode k) x)) * b k y) (isCk_const_mul_ps h1 _) (isCk_const_mul_ps h2 _)
    have hs1 := cbNorm_smul_le_ps h1 (S (Torus.cosMode k) x)
    have hs2 := cbNorm_smul_le_ps h2 (-(S (Torus.sinMode k) x))
    rw [abs_neg] at hs2
    have e : h k = (fun y => S (Torus.cosMode k) x * a k y) +
        (fun y => (-(S (Torus.sinMode k) x)) * b k y) := rfl
    rw [e]
    have hjp := Real.rpow_nonneg (Torus.jp_pos k).le (-((J - L : ℕ) : ℝ))
    have hP : 0 ≤ Lattice.jp k ^ L := pow_nonneg (Torus.jp_pos k).le L
    have hA := hAk k
    have hB := hBk k
    have hMn : 0 ≤ M * ((L + 1) * Lattice.jp k ^ L) := by positivity
    rw [← jp_pow_mul_rpow_ps k L (-((J - L : ℕ) : ℝ))]
    calc Torus.cbNorm L ((fun y => S (Torus.cosMode k) x * a k y) +
          (fun y => (-(S (Torus.sinMode k) x)) * b k y))
        ≤ |S (Torus.cosMode k) x| * Torus.cbNorm L (a k) +
          |S (Torus.sinMode k) x| * Torus.cbNorm L (b k) := hadd.trans (add_le_add hs1 hs2)
      _ ≤ (M * ((L + 1) * Lattice.jp k ^ L)) * (C1 * G * Lattice.jp k ^ (-((J - L : ℕ) : ℝ))) +
          (M * ((L + 1) * Lattice.jp k ^ L)) * (C1 * G * Lattice.jp k ^ (-((J - L : ℕ) : ℝ))) :=
          add_le_add (mul_le_mul hA h3' (cbNorm_nonneg_ps _ _) hMn)
            (mul_le_mul hB h4 (cbNorm_nonneg_ps _ _) hMn)
      _ = _ := by ring
  have hpass2 := series_passthrough hd1 s _ _ c₀ Λ₀ β V ρβ H h hhck hhsum ht y
  have hfun2 : (fun y' => ∑' k, h k y') = fun y' => S (fun x' => R x' y') x := by
    funext y'
    rw [step1 y']
    exact tsum_congr fun k => by simp only [hh]; ring
  rw [hfun2] at hpass2
  show S (fun y' => S (fun x' => R x' y') x) y = _
  refine Eq.trans hpass2.tsum_eq.symm (tsum_congr fun k => ?_)
  have hk := hsl1 J (by omega) R hR k
  have e1 : S (fun y' => S (Torus.cosMode k) x * a k y' + (-(S (Torus.sinMode k) x)) * b k y') y =
      S (fun y' => S (Torus.cosMode k) x * a k y') y +
        S (fun y' => (-(S (Torus.sinMode k) x)) * b k y') y :=
    congrFun (S_add_ps hd1 H (isCk_const_mul_ps hk.1 (S (Torus.cosMode k) x))
      (isCk_const_mul_ps hk.2.1 (-(S (Torus.sinMode k) x))) ht) y
  have e2 : S (fun y' => S (Torus.cosMode k) x * a k y') y =
      S (Torus.cosMode k) x * S (a k) y :=
    congrFun (S_smul_ps hd1 H hk.1 (S (Torus.cosMode k) x) ht) y
  have e3 : S (fun y' => (-(S (Torus.sinMode k) x)) * b k y') y =
      (-(S (Torus.sinMode k) x)) * S (b k) y :=
    congrFun (S_smul_ps hd1 H hk.2.1 (-(S (Torus.sinMode k) x)) ht) y
  show S (h k) y = S (Torus.cosMode k) x * S (a k) y - S (Torus.sinMode k) x * S (b k) y
  show S (fun y' => S (Torus.cosMode k) x * a k y' + (-(S (Torus.sinMode k) x)) * b k y') y = _
  rw [e1, e2, e3]
  ring

theorem exists_pairSemigroup_decay (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρC : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (j : ℕ) :
    ∃ (J : ℕ) (C c : ℝ), 0 < C ∧ 0 < c ∧ ∀ R : Torus d → Torus d → ℝ, IsCk2 J R → ∀ t, 0 ≤ t →
        IsCk2 j (pairSemigroup (mfData d s hs0 hsd V β hβ) ρβ t R) ∧
        cbNorm2 j (pairSemigroup (mfData d s hs0 hsd V β hβ) ρβ t R) ≤ C * Real.exp (-c * t) * cbNorm2 J R ∧
        ∀ (i : ℕ), i ≤ j → ∀ p : Euc d × Euc d, ContinuousOn (fun t' =>
          iteratedFDeriv ℝ i (lift2 (pairSemigroup (mfData d s hs0 hsd V β hβ) ρβ t' R)) p) (Set.Ici 0) := by
  -- Route: `pairSemigroup_eq_tsum` writes `U_t^x U_t^y R` as a series of products of `S(t)`-images of
  -- `cos_k`, `sin_k` and of the slice coefficients; `decay_core_ps` bounds the `C^j` norms of the
  -- terms (`S_cb_bound`: `C^L → C^j` with `e^{-ct}`; slice decay `⟨k⟩^{-(J-L)}`; growth `⟨k⟩^L`),
  -- sums them (`series_assembly_ps`), and proves continuity in `t` termwise (`S_cont_ps`).
  have hd1 : 1 ≤ d := by omega
  have h3 := ClassicalPart.three_le_mStar d
  have hmst := MFAdjoint.mStar_gt d
  set L : ℕ := j + mStar d + 4 with hL
  set J : ℕ := 2 * L + 3 * mStar d + 2 * d + 9 with hJ
  have hJ1 : 3 * mStar d + 2 * d + 8 ≤ J := by omega
  have hJL : 2 * L + d + 1 ≤ J := by omega
  obtain ⟨c₀, Λ₀, H⟩ := frozenHyp_of_smooth s hs0 hsd β hβ V hV ρβ hρβ hρC hpos (L + mStar d)
  have hH3 : MFAdjoint.FrozenHyp d s (L + 3) β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ := H.mono (by omega)
  have hjL : (d : ℝ) / 2 + (j : ℝ) < (L : ℝ) := by
    rw [hL]; push_cast; linarith
  have hjL1 : (d : ℝ) / 2 + (j : ℝ) < (L : ℝ) - 1 := by
    rw [hL]; push_cast; linarith
  obtain ⟨M, c, hM, hc, hbd⟩ := S_cb_bound hd1 s j L (by omega) hjL β⁻¹ β⁻¹ c₀ Λ₀
  obtain ⟨C1, hC1, hsl1⟩ := exists_sliceCoeff_bound (d := d) L (J - L)
  obtain ⟨C, hC, hmain⟩ := decay_core_ps (j := j) (L := L) (J := J) hJL hM hc hC1
    (fun t h => equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ t h)
    (fun t ht h hh => hbd β V ρβ H h hh t ht)
    (fun h hh t₀ ht₀ => S_cont_ps hd1 j L (by omega) hjL1 hH3 hh ht₀)
    (fun R hR k => hsl1 J (by omega) R hR k)
  refine ⟨J, C, c, hC, hc, ?_⟩
  intro R hR t ht
  exact hmain R hR (fun t' => pairSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ t' R)
    (fun t' ht' x y => pairSemigroup_eq_tsum hd s hs0 hsd β hβ V hV ρβ hρβ hρC hpos J hJ1 R hR t' ht'
      x y) t ht

end HRS.PDE.MFPair
