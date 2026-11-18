import HRS.Uniform.Q54cAux14

/-!
# Q54c, part 15: the Sobolev vector `Sv j c` of an admissible coefficient sequence

`Adm j c`: `c` real, absolutely summable, in `H^j`.  `Sv j c = (Re c(0), lpFun j (toFun c)) ∈ ℝ × E_j`.
Then `‖Sv j c‖ ≤ ‖c‖_{H^j} ≤ 2‖Sv j c‖`, `Sv` is linear on admissible sequences, and a coefficient path with an
`H^j`-derivative has an `ℝ × E_j`-valued derivative; hence Lipschitz bounds by the mean value inequality.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

/-- admissible coefficient sequences at level `j`. -/
def Adm (j : ℝ) (c : Coeff d) : Prop :=
  IsRealCoeff c ∧ (Summable fun k => ‖c k‖) ∧ MemHs j c

theorem Adm.comb {j : ℝ} {c c' : Coeff d} (h : Adm j c) (h' : Adm j c') (α β : ℝ) :
    Adm j (fun k => (α : ℂ) * c k + (β : ℂ) * c' k) := by
  refine ⟨fun k => ?_, ?_, ?_⟩
  · simp only [map_add, map_mul, Complex.conj_ofReal]
    rw [h.1 k, h'.1 k]
  · refine Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => ?_) (((h.2.1.mul_left |α|).add (h'.2.1.mul_left |β|)))
    calc ‖(α : ℂ) * c k + (β : ℂ) * c' k‖ ≤ ‖(α : ℂ) * c k‖ + ‖(β : ℂ) * c' k‖ := norm_add_le _ _
      _ = |α| * ‖c k‖ + |β| * ‖c' k‖ := by simp [norm_mul]
  · exact HRS.PDE.MFThermalReg.memHs_add (HRS.PDE.MFThermalReg.memHs_smul h.2.2 (α : ℂ))
      (HRS.PDE.MFThermalReg.memHs_smul h'.2.2 (β : ℂ))

theorem Adm.mono {j j' : ℝ} {c : Coeff d} (h : Adm j c) (hjj : j' ≤ j) : Adm j' c :=
  ⟨h.1, h.2.1, memSobolev_aux hjj h.2.2⟩
where
  memSobolev_aux {a b : ℝ} (hab : a ≤ b) {c : Coeff d} (hc : MemHs b c) : MemHs a c :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (by unfold sobWeight; positivity) (sq_nonneg _))
      (fun k => mul_le_mul_of_nonneg_right
        (by
          unfold sobWeight
          exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (Real.pi * Lattice.enorm k)]) hab)
        (sq_nonneg _)) hc

theorem toFun_comb {c c' : Coeff d} (hc : Summable fun k => ‖c k‖) (hc' : Summable fun k => ‖c' k‖)
    (α β : ℝ) (x : Torus d) :
    toFun (fun k => (α : ℂ) * c k + (β : ℂ) * c' k) x = α * toFun c x + β * toFun c' x := by
  have h1 := summable_series_terms c hc x
  have h2 := summable_series_terms c' hc' x
  have : series (fun k => (α : ℂ) * c k + (β : ℂ) * c' k) x = (α : ℂ) * series c x + (β : ℂ) * series c' x := by
    unfold series
    rw [← tsum_mul_left, ← tsum_mul_left, ← (h1.mul_left (α : ℂ)).tsum_add (h2.mul_left (β : ℂ))]
    exact tsum_congr fun k => by ring
  unfold toFun
  rw [this]
  simp [Complex.add_re, Complex.re_ofReal_mul]

theorem Adm.memSobolev {j : ℝ} {c : Coeff d} (h : Adm j c) :
    MemSobolev j (toFun c) ∧ sobolevNorm j (toFun c) = HRS.PDE.hsNorm j c :=
  HRS.PDE.ClassicalPart.memSobolev_toFun h.2.1 h.2.2 h.1

theorem Adm.coeffOf_toFun {j : ℝ} {c : Coeff d} (h : Adm j c) : coeffOf (toFun c) = c :=
  HRS.PDE.coeffOf_toFun c h.1 h.2.1

theorem Adm.mean_eq {j : ℝ} {c : Coeff d} (h : Adm j c) : Torus.mean (toFun c) = (c 0).re := by
  have h0 := congrFun h.coeffOf_toFun 0
  have h1 : coeffOf (toFun c) 0 = ((∫ x, toFun c x : ℝ) : ℂ) := by
    unfold coeffOf
    exact HRS.PDE.MFApriori.coeffOf_zero_eq_integral' (toFun c)
  rw [h0] at h1
  rw [h1]
  simp [Torus.mean]

/-- the full Sobolev vector. -/
def Sv (j : ℝ) (c : Coeff d) : ℝ × NegSobolev d j := ((c 0).re, lpFun j (toFun c))

theorem sobolevNorm_sq_eq {j : ℝ} {ψ : Torus d → ℝ} (h : MemSobolev j ψ) :
    sobolevNorm j ψ ^ 2 = Torus.mean ψ ^ 2 + ‖lpFun j ψ‖ ^ 2 := by
  rw [lpFun_of_mem h, HRS.Uniform.Q54.norm_sq_lpOf]
  unfold sobolevNorm
  rw [Real.sq_sqrt]
  exact add_nonneg (sq_nonneg _) (tsum_nonneg fun k => mul_nonneg
    (Real.rpow_nonneg (Torus.jp_pos k.1).le _) (sq_nonneg _))

theorem Adm.norm_Sv_le {j : ℝ} {c : Coeff d} (h : Adm j c) : ‖Sv j c‖ ≤ HRS.PDE.hsNorm j c := by
  obtain ⟨hM, hN⟩ := h.memSobolev
  have hsq := sobolevNorm_sq_eq hM
  have hn0 : 0 ≤ sobolevNorm j (toFun c) := Real.sqrt_nonneg _
  rw [← hN]
  refine max_le ?_ ?_
  · rw [Real.norm_eq_abs]
    show |(c 0).re| ≤ _
    rw [← h.mean_eq]
    by_contra hc
    push Not at hc
    have h1 : sobolevNorm j (toFun c) ^ 2 < |Torus.mean (toFun c)| ^ 2 := by
      nlinarith [abs_nonneg (Torus.mean (toFun c))]
    rw [sq_abs] at h1
    nlinarith [sq_nonneg ‖lpFun j (toFun c)‖]
  · exact norm_lpFun_le j _

theorem Adm.hsNorm_le_Sv {j : ℝ} {c : Coeff d} (h : Adm j c) : HRS.PDE.hsNorm j c ≤ 2 * ‖Sv j c‖ := by
  obtain ⟨hM, hN⟩ := h.memSobolev
  have hsq := sobolevNorm_sq_eq hM
  rw [← hN]
  have h1 : |Torus.mean (toFun c)| ≤ ‖Sv j c‖ := by
    rw [h.mean_eq]; exact (le_max_left _ _)
  have h2 : ‖lpFun j (toFun c)‖ ≤ ‖Sv j c‖ := le_max_right _ _
  have hn0 : 0 ≤ ‖Sv j c‖ := norm_nonneg _
  have hm2 : Torus.mean (toFun c) ^ 2 ≤ ‖Sv j c‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hl2 : ‖lpFun j (toFun c)‖ ^ 2 ≤ ‖Sv j c‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hs0 : 0 ≤ sobolevNorm j (toFun c) := Real.sqrt_nonneg _
  by_contra hc
  push Not at hc
  have h3 : (2 * ‖Sv j c‖) ^ 2 < sobolevNorm j (toFun c) ^ 2 := by
    nlinarith
  nlinarith

theorem Sv_comb {j : ℝ} {c c' : Coeff d} (h : Adm j c) (h' : Adm j c') (α β : ℝ) :
    Sv j (fun k => (α : ℂ) * c k + (β : ℂ) * c' k) = α • Sv j c + β • Sv j c' := by
  have hc := (h.comb h' α β)
  unfold Sv
  refine Prod.ext ?_ ?_
  · simp [Complex.add_re, Complex.re_ofReal_mul]
  · have e : toFun (fun k => (α : ℂ) * c k + (β : ℂ) * c' k) =
        fun x => α * toFun c x + β * toFun c' x :=
      funext fun x => toFun_comb h.2.1 h'.2.1 α β x
    simp only [e, Prod.smul_snd, Prod.snd_add]
    exact lpFun_comb h.memSobolev.1 h'.memSobolev.1 α β

theorem Sv_comb3 {j : ℝ} {c c' e : Coeff d} (h : Adm j c) (h' : Adm j c') (he : Adm j e) (α : ℝ) :
    Sv j (fun k => (α : ℂ) * c k - (α : ℂ) * c' k - e k) = α • Sv j c - α • Sv j c' - Sv j e := by
  have h1 : (fun k => (α : ℂ) * c k - (α : ℂ) * c' k - e k) =
      fun k => ((1 : ℝ) : ℂ) * ((α : ℂ) * c k + ((-α : ℝ) : ℂ) * c' k) + ((-1 : ℝ) : ℂ) * e k := by
    funext k; push_cast; ring
  have h2 := h.comb h' α (-α)
  rw [h1, Sv_comb h2 he 1 (-1), Sv_comb h h' α (-α)]
  simp only [one_smul, neg_smul]
  abel

/-- A coefficient path with an `H^j`-derivative has an `ℝ × E_j`-valued derivative. -/
theorem hasDerivWithinAt_Sv {j : ℝ} {F G : ℝ → Coeff d} {s : Set ℝ} {τ : ℝ}
    (hF : ∀ τ' ∈ s, Adm j (F τ')) (hG : Adm j (G τ)) (hτ : τ ∈ s)
    (hlim : Tendsto (fun τ' => HRS.PDE.hsNorm j (fun k => (F τ' k - F τ k) / ((τ' - τ : ℝ) : ℂ) - G τ k))
      (𝓝[s \ {τ}] τ) (𝓝 0)) :
    HasDerivWithinAt (fun τ' => Sv j (F τ')) (Sv j (G τ)) s τ := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with τ' hτ'
  have hτ's : τ' ∈ s := hτ'.1
  have hq : (fun k => (F τ' k - F τ k) / ((τ' - τ : ℝ) : ℂ) - G τ k) =
      fun k => (((τ' - τ)⁻¹ : ℝ) : ℂ) * F τ' k - (((τ' - τ)⁻¹ : ℝ) : ℂ) * F τ k - G τ k := by
    funext k
    push_cast
    ring
  have hsl : slope (fun τ'' => Sv j (F τ'')) τ τ' = ((τ' - τ)⁻¹ : ℝ) • (Sv j (F τ') - Sv j (F τ)) := by
    rw [slope_def_module]
  have e1 : slope (fun τ'' => Sv j (F τ'')) τ τ' - Sv j (G τ) =
      Sv j (fun k => (((τ' - τ)⁻¹ : ℝ) : ℂ) * F τ' k - (((τ' - τ)⁻¹ : ℝ) : ℂ) * F τ k - G τ k) := by
    rw [hsl, Sv_comb3 (hF τ' hτ's) (hF τ hτ) hG, smul_sub]
  have hadm : Adm j (fun k => (((τ' - τ)⁻¹ : ℝ) : ℂ) * F τ' k - (((τ' - τ)⁻¹ : ℝ) : ℂ) * F τ k - G τ k) := by
    have := ((hF τ' hτ's).comb (hF τ hτ) ((τ' - τ)⁻¹) (-(τ' - τ)⁻¹)).comb hG 1 (-1)
    convert this using 1
    funext k; push_cast; ring
  rw [e1]
  calc _ ≤ HRS.PDE.hsNorm j (fun k => (((τ' - τ)⁻¹ : ℝ) : ℂ) * F τ' k - (((τ' - τ)⁻¹ : ℝ) : ℂ) * F τ k - G τ k) :=
        hadm.norm_Sv_le
    _ = _ := by rw [hq]

/-- mean value inequality for an `ℝ × E_j`-valued coefficient path. -/
theorem Sv_lip {j : ℝ} {F G : ℝ → Coeff d} {t L : ℝ}
    (hderiv : ∀ τ ∈ Set.Icc 0 t, HasDerivWithinAt (fun τ' => Sv j (F τ')) (Sv j (G τ)) (Set.Icc 0 t) τ)
    (hb : ∀ τ ∈ Set.Icc 0 t, ‖Sv j (G τ)‖ ≤ L) {τ τ' : ℝ} (hτ : τ ∈ Set.Icc 0 t) (hτ' : τ' ∈ Set.Icc 0 t) :
    ‖Sv j (F τ') - Sv j (F τ)‖ ≤ L * |τ' - τ| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun τ'' => Sv j (F τ''))
    (f' := fun τ'' => Sv j (G τ'')) hderiv hb (convex_Icc 0 t) hτ hτ'
  simpa [Real.norm_eq_abs] using this

end HRS.Uniform.Q54c
