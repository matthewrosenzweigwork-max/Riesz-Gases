import HRS.MS.R2SeAux26

/-!
# S9.9 `r2_static_edgeworth`, packet 27: the quadratic statistic of a finite-rank kernel

Worker S99, namespace `S99`.  `s99_FR`: for `h = ∑ c_{ab} u_a ⊗ u_b` (`u_a ∈ C_c^∞`),
`E[B_h ψ(W_N)] = ½ ∑_{l,q} Q_h(l,q) E[∂_q∂_lψ(G)] + O_h(1/√N)` uniformly in `ψ ∈ Bd 4`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s99_Lc_shift {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]
    {ψ f : α → ℝ} (hψ : BM ψ) (hf : BM f) (c0 : ℝ) :
    Lc P ψ f = Lc P ψ (fun x => f x - c0) := by
  have h := Lc_add (P := P) hψ (hf.add (BM.const (-c0))) (BM.const c0)
  have e : (fun x => f x + -c0 + c0) = f := funext fun x => by ring
  have e2 : (fun x => (fun x => f x + -c0) x + (fun _ => c0) x) = f := funext fun x => by ring
  rw [e2, Lc_const, add_zero] at h
  rw [h]
  congr 1

theorem BM.sub_const {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : BM f) (c : ℝ) :
    BM (fun x => f x - c) := by
  have := hf.add (BM.const (α := α) (-c))
  simpa [sub_eq_add_neg] using this

/-- Exchange of a finite sum with the double series. -/
theorem s99_tsum2_finsum {m : ℕ} (c : Fin m → Fin m → ℝ) (x y : Fin m → ℕ → ℝ) (g : ℕ → ℕ → ℝ)
    (hx : ∀ i, Summable fun l => |x i l|) (hy : ∀ i, Summable fun q => |y i q|)
    (hg : ∀ l q, |g l q| ≤ 1) :
    ∑' l, ∑' q, (∑ i, ∑ j, c i j * (x i l * y j q)) * g l q =
      ∑ i, ∑ j, c i j * ∑' l, ∑' q, x i l * y j q * g l q := by
  have hfq : ∀ l i j, Summable fun q => c i j * (x i l * y j q * g l q) := fun l i j =>
    Summable.of_norm_bounded ((hy j).mul_left (|c i j| * |x i l|)) (fun q => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      calc |c i j| * (|x i l| * |y j q| * |g l q|) ≤ |c i j| * (|x i l| * |y j q| * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hg l q) (by positivity)) (abs_nonneg _)
        _ = |c i j| * |x i l| * |y j q| := by ring)
  have hinner : ∀ l, ∑' q, (∑ i, ∑ j, c i j * (x i l * y j q)) * g l q =
      ∑ i, ∑ j, ∑' q, c i j * (x i l * y j q * g l q) := by
    intro l
    have e : ∀ q, (∑ i, ∑ j, c i j * (x i l * y j q)) * g l q =
        ∑ i, ∑ j, c i j * (x i l * y j q * g l q) := by
      intro q
      simp only [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    simp_rw [e]
    rw [Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => hfq l i j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Summable.tsum_finsetSum (fun j _ => hfq l i j)]
  simp_rw [hinner]
  have hsl : ∀ i j, Summable fun l => ∑' q, c i j * (x i l * y j q * g l q) := by
    intro i j
    refine Summable.of_norm_bounded ((hx i).mul_left (|c i j| * ∑' q, |y j q|)) (fun l => ?_)
    have hg' : HasSum (fun q => |c i j| * |x i l| * |y j q|) (|c i j| * |x i l| * ∑' q, |y j q|) :=
      (hy j).hasSum.mul_left _
    have := tsum_of_norm_bounded hg' (f := fun q => c i j * (x i l * y j q * g l q)) (fun q => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      calc |c i j| * (|x i l| * |y j q| * |g l q|) ≤ |c i j| * (|x i l| * |y j q| * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hg l q) (by positivity)) (abs_nonneg _)
        _ = |c i j| * |x i l| * |y j q| := by ring)
    refine this.trans (le_of_eq ?_)
    ring
  rw [Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => hsl i j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Summable.tsum_finsetSum (fun j _ => hsl i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun l => ?_
  rw [← tsum_mul_left]

section FR

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hS hφ F

set_option maxHeartbeats 4000000 in
theorem s99_FR {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j => susceptibilityCov (rieszKernel d s)
      (thermalMeasure d s a β) γ (φ i) (φ j))) {m : ℕ} {cc : Fin m → Fin m → ℝ}
    {u : Fin m → Euc d → ℝ} (hcu : IsR2FiniteRankData cc u) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ {ψ : SeqL2 → ℝ}, Bd 4 ψ →
      |Bterm d s a β γ φ N (r2FiniteRankKernel cc u) ψ -
        (1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ (r2FiniteRankKernel cc u) l q *
          ∫ z, pd (pd ψ l) q z ∂G| ≤ K / Real.sqrt N := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  have hJ1 : 1 ≤ J1 d := by unfold J1; omega
  have hcb : ∀ i, MemCb (J1 d) (u i) := fun i => s99_cb_of_cinf (hcu.smooth i) (hcu.compactSupport i) (J1 d)
  choose KM hKM0 hKM using fun (i j : Fin m) =>
    s99_Mab hd hs0 hs ha hβ hγ hT hS hφ F hG (hcb i) (hcb j)
  obtain ⟨KY, hKY0, hY2⟩ := s99_Y_L2 hd hs0 hs ha hβ hγ hT hS
  obtain ⟨Kb, hKb0, hbias⟩ := s99_bias hd hs0 hs ha hβ hγ hT hS
  obtain ⟨KT, hKT0, hTL2⟩ := s99_T_L2 hd hs0 hs ha hβ hγ hT hS
  set cu : Fin m → ℝ := fun i => cbNorm (J1 d) (u i) with hcudef
  have hcu0 : ∀ i, 0 ≤ cu i := fun i => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hubd : ∀ i x, |u i x| ≤ cu i := fun i x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le (hcb i) x
    rwa [Real.norm_eq_abs] at this
  have hucont : ∀ i, Continuous (u i) := fun i => (hcu.smooth i).continuous
  have hum : ∀ i, Measurable (u i) := fun i => (hucont i).measurable
  -- the diagonal observable
  set Dg : Euc d → ℝ := fun x => ∑ i, ∑ j, cc i j * (u i x * u j x) with hDg
  set CD : ℝ := ∑ i, ∑ j, |cc i j| * (cu i * cu j) with hCD
  have hCD0 : 0 ≤ CD := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
    have := hcu0 i; have := hcu0 j; positivity
  have hDgbd : ∀ x, |Dg x| ≤ CD := fun x => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hubd i x) (hubd j x) (abs_nonneg _) (hcu0 i)) (abs_nonneg _)
  have hDgc : Continuous Dg := continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    continuous_const.mul ((hucont i).mul (hucont j))
  obtain ⟨KT1, hKT1, hT1⟩ : ∃ KT1 : ℝ, 0 ≤ KT1 ∧ ∀ N : ℕ, 2 ≤ N → ∀ {B : ℝ}, 0 ≤ B → ∀ {w : Euc d → ℝ},
      Measurable w → (∀ x, |w x| ≤ B) →
      ∫ X, |pair (empirical X) w - pair (thermalMeasure d s a β) w| ∂(S46.s46_P d s a β γ N) ≤
        KT1 * B / Real.sqrt N :=
    ⟨KT, hKT0, fun N hN B hB w hw hwb => s99_T_L1 hT hS hKT0 hTL2 hN hB hw hwb⟩
  set K : ℝ := (∑ i, ∑ j, (1 / 2) * |cc i j| * (KM i j + 4 * Kb * KY * (cu i * cu j))) + KT1 * CD with hKdef
  have hK0 : 0 ≤ K := by
    refine add_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_) (by positivity)
    have := hKM0 i j; have := hcu0 i; have := hcu0 j; positivity
  refine ⟨K, hK0, fun N hN ψ hψ => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsq2 : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN).prob
  haveI hν : IsProbabilityMeasure (S46.s46_nu d s a β γ N) := s99_nu_prob hN1
  set P := S46.s46_P d s a β γ N with hPdef
  set ν := S46.s46_nu d s a β γ N with hνdef
  set μ := thermalMeasure d s a β with hμdef
  have hWc : Continuous (fun X : EucConfig d N => featureVec φ ν X) :=
    (s99_W_contDiff hN1 hJ1 hφ).continuous
  set ψW : EucConfig d N → ℝ := fun X => ψ (featureVec φ ν X) with hψWdef
  have hψWm : Measurable ψW := (hψ.1.continuous.comp hWc).measurable
  have hψWb : ∀ X, |ψW X| ≤ 1 := fun X => hψ.abs_le _
  have hψBM : BM ψW := ⟨hψWm, 1, hψWb⟩
  -- the centered observables
  set Ya : Fin m → EucConfig d N → ℝ := fun i X => s45_Yi N (u i) (pair ν (u i)) X with hYa
  set Z : Fin m → EucConfig d N → ℝ := fun i X => Real.sqrt N * (pair (empirical X) (u i) - pair μ (u i))
    with hZ
  set βb : Fin m → ℝ := fun i => Real.sqrt N * (pair ν (u i) - pair μ (u i)) with hβb
  have hYaBM : ∀ i, BM (Ya i) := fun i =>
    ⟨measurable_const.mul ((s45_measurable_pair_empirical hN1 (hum i)).sub measurable_const),
      2 * Real.sqrt N * cu i, fun X => s99_Yi_bd hN1 (hubd i) X⟩
  have hZBM : ∀ i, BM (Z i) := fun i =>
    ⟨measurable_const.mul ((s45_measurable_pair_empirical hN1 (hum i)).sub measurable_const),
      2 * Real.sqrt N * cu i, fun X => s99_Yi_bd (ν := μ) hN1 (hubd i) X⟩
  have hZY : ∀ i X, Z i X = Ya i X + βb i := fun i X => by
    simp only [hZ, hYa, hβb, s45_Yi]; ring
  -- the energy
  set Φ1 : EucConfig d N → ℝ := fun X => ∑ i, ∑ j, ((1 / 2) * cc i j) * (Z i X * Z j X) with hΦ1
  set Φ2 : EucConfig d N → ℝ := fun X => (-(1 / 2)) * pair (empirical X) Dg with hΦ2
  have hDgm : Measurable Dg := hDgc.measurable
  have hΦ2BM : BM (fun X : EucConfig d N => pair (empirical X) Dg) :=
    ⟨s45_measurable_pair_empirical hN1 hDgm, CD, fun X => s45_abs_pair_empirical_le hN1 hDgbd X⟩
  have hΦ1BM : BM Φ1 := BM.sum _ fun i _ => BM.sum _ fun j _ =>
    BM.const_mul _ ((hZBM i).mul (hZBM j))
  have hΦ : ∀ X, (N : ℝ) * pairEnergy (r2FiniteRankKernel cc u) X μ = Φ1 X + Φ2 X := by
    intro X
    rw [s99_pe_finrank hcu μ hN1 X]
    have e : (∑ i, ∑ j, ((1 / 2) * cc i j) * (Z i X * Z j X)) =
        (1 / 2) * ∑ i, ∑ j, cc i j * (Z i X * Z j X) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    simp only [hΦ1, hΦ2]
    rw [e]
    simp only [hZ, hDg]
    ring
  -- (a) `Bterm = L_ψ(Φ)`
  set ΦX : EucConfig d N → ℝ := fun X => Φ1 X + Φ2 X with hΦX
  have hΦXBM : BM ΦX := hΦ1BM.add (hΦ2BM.const_mul _)
  have hBh : ∀ X, Bh d s a β γ N (r2FiniteRankKernel cc u) X = ΦX X - ∫ Y, ΦX Y ∂P := by
    intro X
    unfold Bh
    have e1 : ∫ Y, ΦX Y ∂P = ∫ Y, (N : ℝ) * pairEnergy (r2FiniteRankKernel cc u) Y μ ∂P := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
      simp only [hΦX]; rw [← hΦ Y]
    rw [← hμdef, e1, integral_const_mul, show ΦX X = (N : ℝ) * pairEnergy (r2FiniteRankKernel cc u) X μ from
      (hΦ X).symm]
    ring
  have hBterm : Bterm d s a β γ φ N (r2FiniteRankKernel cc u) ψ = Lc P ψW ΦX := by
    unfold Bterm Lc
    simp_rw [hBh]
    have e : (fun X : EucConfig d N => (ΦX X - ∫ Y, ΦX Y ∂P) * ψ (featureVec φ ν X)) =
        fun X => ΦX X * ψW X - (∫ Y, ΦX Y ∂P) * ψW X := funext fun X => by simp only [hψWdef]; ring
    rw [e, integral_sub (hΦXBM.mul hψBM).integrable (hψBM.integrable.const_mul _), integral_const_mul]
  -- (b), (c) the decomposition
  have hZZ : ∀ i j X, Z i X * Z j X = Ya i X * Ya j X + βb j * Ya i X + βb i * Ya j X + βb i * βb j := by
    intro i j X; rw [hZY i X, hZY j X]; ring
  have hLcZ : ∀ i j, Lc P ψW (fun X => Z i X * Z j X) =
      Lc P ψW (fun X => Ya i X * Ya j X) + βb j * Lc P ψW (Ya i) + βb i * Lc P ψW (Ya j) := by
    intro i j
    have e : (fun X => Z i X * Z j X) = fun X => ((Ya i X * Ya j X + βb j * Ya i X) + βb i * Ya j X) +
        βb i * βb j := by
      funext X; rw [hZZ]
    have b1 : BM (fun X => Ya i X * Ya j X + βb j * Ya i X) :=
      ((hYaBM i).mul (hYaBM j)).add ((hYaBM i).const_mul _)
    have b2 : BM (fun X => (Ya i X * Ya j X + βb j * Ya i X) + βb i * Ya j X) :=
      b1.add ((hYaBM j).const_mul _)
    rw [e, Lc_add hψBM b2 (BM.const _), Lc_const, add_zero, Lc_add hψBM b1 ((hYaBM j).const_mul _),
      Lc_add hψBM ((hYaBM i).mul (hYaBM j)) ((hYaBM i).const_mul _), Lc_smul _ hψBM (hYaBM i),
      Lc_smul _ hψBM (hYaBM j)]
  have hLcΦ1 : Lc P ψW Φ1 = ∑ i, ∑ j, ((1 / 2) * cc i j) * Lc P ψW (fun X => Z i X * Z j X) := by
    have h1 : Lc P ψW Φ1 = ∑ i, Lc P ψW (fun X => ∑ j, ((1 / 2) * cc i j) * (Z i X * Z j X)) :=
      Lc_sum _ hψBM (fun i _ => BM.sum _ fun j _ => BM.const_mul _ ((hZBM i).mul (hZBM j)))
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Lc_sum _ hψBM (fun j _ => BM.const_mul _ ((hZBM i).mul (hZBM j)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Lc_smul _ hψBM ((hZBM i).mul (hZBM j))
  have hLcΦ2 : |Lc P ψW Φ2| ≤ KT1 * CD / Real.sqrt N := by
    have e : Lc P ψW Φ2 = (-(1 / 2)) * Lc P ψW (fun X => pair (empirical X) Dg) :=
      Lc_smul _ hψBM hΦ2BM
    have hsh := s99_Lc_shift (P := P) hψBM hΦ2BM (pair μ Dg)
    have hbm := hΦ2BM.sub_const (pair μ Dg)
    have h2 := Lc_abs_le (P := P) hψWb hψWm hbm
    have h3 := hT1 N hN hCD0 hDgm hDgbd
    rw [e, hsh, abs_mul]
    have : |Lc P ψW (fun X => pair (empirical X) Dg - pair μ Dg)| ≤ 2 * (KT1 * CD / Real.sqrt N) :=
      h2.trans (mul_le_mul_of_nonneg_left h3 (by norm_num))
    calc |-(1 / 2 : ℝ)| * |Lc P ψW (fun X => pair (empirical X) Dg - pair μ Dg)|
        ≤ (1 / 2) * (2 * (KT1 * CD / Real.sqrt N)) := by
          rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact mul_le_mul_of_nonneg_left this (by norm_num)
      _ = KT1 * CD / Real.sqrt N := by ring
  -- (d) the pieces of `L_ψ(Z_i Z_j)`
  have hYL1 : ∀ i, |Lc P ψW (Ya i)| ≤ 2 * (KY * cu i) := by
    intro i
    have h1 := Lc_abs_le (P := P) hψWb hψWm (hYaBM i)
    have hmem : MemLp (Ya i) 2 P := s99_memLp_two_of_bdd (hYaBM i).meas
      (C := 2 * Real.sqrt N * cu i) (fun X => s99_Yi_bd hN1 (hubd i) X)
    have h2 := s99_integral_abs_le_sqrt hmem
    have h3 : ∫ X, (Ya i X) ^ 2 ∂P ≤ (KY * cu i) ^ 2 := (hY2 N hN (cu i) (hcu0 i) (u i) (hum i) (hubd i)).2
    have h4 : Real.sqrt (∫ X, (Ya i X) ^ 2 ∂P) ≤ KY * cu i :=
      (Real.sqrt_le_sqrt h3).trans_eq (Real.sqrt_sq (mul_nonneg hKY0 (hcu0 i)))
    exact h1.trans (mul_le_mul_of_nonneg_left (h2.trans h4) (by norm_num))
  have hβb : ∀ i, |βb i| ≤ Kb * cu i / Real.sqrt N := by
    intro i
    have hb := hbias N hN (cu i) (hcu0 i) (u i) (hum i) (hubd i)
    simp only [hβb]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt N * |pair ν (u i) - pair μ (u i)| ≤ Real.sqrt N * (Kb * cu i / N) :=
          mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
      _ = Kb * cu i / Real.sqrt N := by
          rw [eq_div_iff hsqN.ne']
          calc Real.sqrt N * (Kb * cu i / N) * Real.sqrt N =
              (Real.sqrt N * Real.sqrt N) * (Kb * cu i) / N := by ring
            _ = Kb * cu i := by rw [hsq2]; field_simp
  -- the limit coefficients
  set Gm : ℕ → ℕ → ℝ := fun l q => ∫ z, pd (pd ψ l) q z ∂G with hGm
  have hGb : ∀ l q, |Gm l q| ≤ 1 := fun l q => by
    have := norm_integral_le_of_norm_le_const (μ := G) (f := pd (pd ψ l) q) (C := 1)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact ((hψ.pd l).pd q).abs_le z)
    simpa [Real.norm_eq_abs, hGm] using this
  set b : ℕ → ℝ := fun j => cbNorm (J1 d) (φ j) with hbdef
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := hφ.2
  have hκu : ∀ i l, |kap d s a β γ (u i) φ l| ≤ cu i * (F.K * b l) := fun i l =>
    s99_kap_bd hd hs0 hs ha hβ hγ hT hS hφ F (hum i) (hubd i) l
  have hsumκ : ∀ i, Summable fun l => |kap d s a β γ (u i) φ l| := fun i =>
    Summable.of_nonneg_of_le (fun l => abs_nonneg _) (fun l => hκu i l)
      (hbs.mul_left (cu i * F.K) |>.congr fun l => by ring)
  have hconv : ∑' l, ∑' q, Qk d s a β γ φ (r2FiniteRankKernel cc u) l q * Gm l q =
      ∑ i, ∑ j, cc i j * ∑' l, ∑' q, kap d s a β γ (u i) φ l * kap d s a β γ (u j) φ q * Gm l q := by
    have hQ : ∀ l q, Qk d s a β γ φ (r2FiniteRankKernel cc u) l q =
        ∑ i, ∑ j, cc i j * (kap d s a β γ (u i) φ l * kap d s a β γ (u j) φ q) := by
      intro l q
      have hal : ∀ l, Continuous (aRep d s a β γ (φ l)) := fun l => (F.amem l).1.continuous
      have hab : ∀ l x, |aRep d s a β γ (φ l) x| ≤ F.K * b l := fun l x => by
        have h1 := s99_norm_iter_le_cb (F.amem l) (Nat.zero_le _) x
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
        exact h1.trans (F.anorm l)
      exact s99_Qk_finrank hT hucont (B := ∑ i, cu i) (fun i x => (hubd i x).trans
        (Finset.single_le_sum (f := cu) (fun k _ => hcu0 k) (Finset.mem_univ i))) l q (hal l) (hal q)
        (hab l) (hab q)
    simp_rw [hQ]
    exact s99_tsum2_finsum cc (fun i l => kap d s a β γ (u i) φ l) (fun j q => kap d s a β γ (u j) φ q) Gm
      hsumκ hsumκ hGb
  -- (e) the error for each pair
  have hε : ∀ i j, |Lc P ψW (fun X => Z i X * Z j X) -
      ∑' l, ∑' q, kap d s a β γ (u i) φ l * kap d s a β γ (u j) φ q * Gm l q| ≤
      (KM i j + 4 * Kb * KY * (cu i * cu j)) / Real.sqrt N := by
    intro i j
    have hM := hKM i j N hN hψ
    have hYY : Lc P ψW (fun X => Ya i X * Ya j X) =
        (∫ X, s45_Yi N (u i) (pair ν (u i)) X * (s45_Yi N (u j) (pair ν (u j)) X *
            ψ (featureVec φ ν X)) ∂P) -
          (∫ X, s45_Yi N (u i) (pair ν (u i)) X * s45_Yi N (u j) (pair ν (u j)) X ∂P) *
            (∫ X, ψ (featureVec φ ν X) ∂P) := by
      unfold Lc
      simp only [hψWdef, hYa]
      congr 1
      congr 1
      funext X; ring
    rw [hLcZ, hYY]
    set G0 : ℝ := ∑' l, ∑' q, kap d s a β γ (u i) φ l * kap d s a β γ (u j) φ q * Gm l q with hG0
    have e1 : |βb j * Lc P ψW (Ya i)| ≤ Kb * cu j / Real.sqrt N * (2 * (KY * cu i)) := by
      rw [abs_mul]; exact mul_le_mul (hβb j) (hYL1 i) (abs_nonneg _) (by
        have := hcu0 j; positivity)
    have e2 : |βb i * Lc P ψW (Ya j)| ≤ Kb * cu i / Real.sqrt N * (2 * (KY * cu j)) := by
      rw [abs_mul]; exact mul_le_mul (hβb i) (hYL1 j) (abs_nonneg _) (by
        have := hcu0 i; positivity)
    have hM' : |(∫ X, s45_Yi N (u i) (pair ν (u i)) X * (s45_Yi N (u j) (pair ν (u j)) X *
            ψ (featureVec φ ν X)) ∂P) -
          (∫ X, s45_Yi N (u i) (pair ν (u i)) X * s45_Yi N (u j) (pair ν (u j)) X ∂P) *
            (∫ X, ψ (featureVec φ ν X) ∂P) - G0| ≤ KM i j / Real.sqrt N := hM
    calc _ = |((∫ X, s45_Yi N (u i) (pair ν (u i)) X * (s45_Yi N (u j) (pair ν (u j)) X *
            ψ (featureVec φ ν X)) ∂P) -
          (∫ X, s45_Yi N (u i) (pair ν (u i)) X * s45_Yi N (u j) (pair ν (u j)) X ∂P) *
            (∫ X, ψ (featureVec φ ν X) ∂P) - G0) + βb j * Lc P ψW (Ya i) + βb i * Lc P ψW (Ya j)| := by
          congr 1; ring
      _ ≤ |(∫ X, s45_Yi N (u i) (pair ν (u i)) X * (s45_Yi N (u j) (pair ν (u j)) X *
            ψ (featureVec φ ν X)) ∂P) -
          (∫ X, s45_Yi N (u i) (pair ν (u i)) X * s45_Yi N (u j) (pair ν (u j)) X ∂P) *
            (∫ X, ψ (featureVec φ ν X) ∂P) - G0| + |βb j * Lc P ψW (Ya i)| + |βb i * Lc P ψW (Ya j)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ KM i j / Real.sqrt N + Kb * cu j / Real.sqrt N * (2 * (KY * cu i)) +
            Kb * cu i / Real.sqrt N * (2 * (KY * cu j)) := add_le_add (add_le_add hM' e1) e2
      _ = (KM i j + 4 * Kb * KY * (cu i * cu j)) / Real.sqrt N := by ring
  -- assembly
  rw [hBterm, show ΦX = fun X => Φ1 X + Φ2 X from rfl, Lc_add hψBM hΦ1BM (hΦ2BM.const_mul _), hLcΦ1, hconv,
    Finset.mul_sum]
  have hfin : (∑ i, ∑ j, ((1 / 2) * cc i j) * Lc P ψW (fun X => Z i X * Z j X) + Lc P ψW Φ2) -
      ∑ i, (1 / 2) * ∑ j, cc i j * ∑' l, ∑' q, kap d s a β γ (u i) φ l * kap d s a β γ (u j) φ q * Gm l q =
      (∑ i, ∑ j, ((1 / 2) * cc i j) * (Lc P ψW (fun X => Z i X * Z j X) -
        ∑' l, ∑' q, kap d s a β γ (u i) φ l * kap d s a β γ (u j) φ q * Gm l q)) + Lc P ψW Φ2 := by
    simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
    have : ∀ i j : Fin m, (1 / 2 : ℝ) * (cc i j * ∑' l, ∑' q, kap d s a β γ (u i) φ l *
        kap d s a β γ (u j) φ q * Gm l q) = 1 / 2 * cc i j * ∑' l, ∑' q, kap d s a β γ (u i) φ l *
        kap d s a β γ (u j) φ q * Gm l q := fun i j => by ring
    simp only [this]
    ring
  rw [hfin]
  refine (abs_add_le _ _).trans ?_
  have hsum : |∑ i, ∑ j, ((1 / 2) * cc i j) * (Lc P ψW (fun X => Z i X * Z j X) -
        ∑' l, ∑' q, kap d s a β γ (u i) φ l * kap d s a β γ (u j) φ q * Gm l q)| ≤
      (∑ i, ∑ j, (1 / 2) * |cc i j| * (KM i j + 4 * Kb * KY * (cu i * cu j))) / Real.sqrt N := by
    rw [Finset.sum_div]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Finset.sum_div]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc 1 / 2 * |cc i j| * |Lc P ψW (fun X => Z i X * Z j X) -
          ∑' l, ∑' q, kap d s a β γ (u i) φ l * kap d s a β γ (u j) φ q * Gm l q|
        ≤ 1 / 2 * |cc i j| * ((KM i j + 4 * Kb * KY * (cu i * cu j)) / Real.sqrt N) :=
          mul_le_mul_of_nonneg_left (hε i j) (by positivity)
      _ = _ := by ring
  refine (add_le_add hsum hLcΦ2).trans (le_of_eq ?_)
  simp only [hKdef]
  ring

end FR

end S99

end
