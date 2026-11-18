import HRS.PDE.Uniqueness
import HRS.PDE.Toolbox
import HRS.PDE.EnergyDrift
import HRS.PDE.Assembly

/-!
# Stability of the propagator (Proposition 3.15): helper lemmas

All declarations live in the namespace `HRS.PDE.StabAux` (or are `private`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.StabAux

open HRS.PDE

variable {d : ℕ}

/-! ### Elementary `H^r` facts -/

theorem hsNormSq_finsum_le {ι : Type*} (S : Finset ι) (x : ι → Coeff d) (r : ℝ)
    (hx : ∀ i ∈ S, MemHs r (x i)) :
    MemHs r (fun k => ∑ i ∈ S, x i k) ∧
      hsNormSq r (fun k => ∑ i ∈ S, x i k) ≤ S.card * ∑ i ∈ S, hsNormSq r (x i) := by
  have hle : ∀ k, sobWeight r k * ‖∑ i ∈ S, x i k‖ ^ 2 ≤
      S.card * ∑ i ∈ S, sobWeight r k * ‖x i k‖ ^ 2 := by
    intro k
    have h1 : ‖∑ i ∈ S, x i k‖ ≤ ∑ i ∈ S, ‖x i k‖ := norm_sum_le _ _
    have h2 : ‖∑ i ∈ S, x i k‖ ^ 2 ≤ (∑ i ∈ S, ‖x i k‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 := sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => ‖x i k‖)
    have hw := (sobWeight_pos r k).le
    calc sobWeight r k * ‖∑ i ∈ S, x i k‖ ^ 2
        ≤ sobWeight r k * (S.card * ∑ i ∈ S, ‖x i k‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) hw
      _ = _ := by rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]; 
                  refine Finset.sum_congr rfl fun i _ => by ring
  have hs : ∀ i ∈ S, Summable fun k => sobWeight r k * ‖x i k‖ ^ 2 := hx
  have hsum : Summable fun k => (S.card : ℝ) * ∑ i ∈ S, sobWeight r k * ‖x i k‖ ^ 2 :=
    (summable_sum hs).mul_left _
  have hmem : MemHs r (fun k => ∑ i ∈ S, x i k) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_pos r k).le (sq_nonneg _)) hle hsum
  refine ⟨hmem, ?_⟩
  unfold hsNormSq
  calc ∑' k, sobWeight r k * ‖∑ i ∈ S, x i k‖ ^ 2
      ≤ ∑' k, (S.card : ℝ) * ∑ i ∈ S, sobWeight r k * ‖x i k‖ ^ 2 := hmem.tsum_le_tsum hle hsum
    _ = _ := by
        rw [tsum_mul_left, Summable.tsum_finsetSum hs]

theorem memHs_sub' {r : ℝ} {a b : Coeff d} (ha : MemHs r a) (hb : MemHs r b) :
    MemHs r (a - b) := memHs_sub ha hb

/-- `Δ : H^{r+2} → H^r`. -/
theorem laplace_bound {r : ℝ} {u : Coeff d} (hu : MemHs (r + 2) u) :
    MemHs r (laplaceCoeff u) ∧ hsNormSq r (laplaceCoeff u) ≤ hsNormSq (r + 2) u := by
  have hle : ∀ k, sobWeight r k * ‖laplaceCoeff u k‖ ^ 2 ≤ sobWeight (r + 2) k * ‖u k‖ ^ 2 := by
    intro k
    have h2 : sobWeight (r + 2) k = sobWeight r k * (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ 2 := by
      rw [sobWeight_add]
      congr 1
      unfold sobWeight
      exact_mod_cast Real.rpow_natCast _ 2
    have hn : ‖laplaceCoeff u k‖ ^ 2 =
        (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ 2 * ‖u k‖ ^ 2 := by
      unfold laplaceCoeff
      rw [norm_mul, mul_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [h2, hn]
    have hw := (sobWeight_pos r k).le
    have hb : (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ 2 ≤
        (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ 2 := by
      have : 0 ≤ 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by positivity
      nlinarith
    calc sobWeight r k * ((4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ 2 * ‖u k‖ ^ 2)
        = (sobWeight r k * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ 2) * ‖u k‖ ^ 2 := by ring
      _ ≤ (sobWeight r k * (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ 2) * ‖u k‖ ^ 2 := by
          gcongr
      _ = _ := by ring
  have hs : MemHs r (laplaceCoeff u) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_pos r k).le (sq_nonneg _)) hle hu
  exact ⟨hs, hs.tsum_le_tsum hle hu⟩


theorem hsNormSq_const_mul (r : ℝ) (c : ℂ) (x : Coeff d) (hx : MemHs r x) :
    MemHs r (fun k => c * x k) ∧ hsNormSq r (fun k => c * x k) = ‖c‖ ^ 2 * hsNormSq r x := by
  have e : ∀ k, sobWeight r k * ‖c * x k‖ ^ 2 = ‖c‖ ^ 2 * (sobWeight r k * ‖x k‖ ^ 2) := by
    intro k; rw [norm_mul, mul_pow]; ring
  refine ⟨?_, ?_⟩
  · unfold MemHs; simp_rw [e]; exact hx.mul_left _
  · unfold hsNormSq; simp_rw [e]; exact tsum_mul_left

/-- `∂_j : H^{r+1} → H^r`. -/
theorem deriv_bound {r : ℝ} {u : Coeff d} (hu : MemHs (r + 1) u) (j : Fin d) :
    MemHs r (derivCoeff j u) ∧ hsNormSq r (derivCoeff j u) ≤ hsNormSq (r + 1) u := by
  obtain ⟨h0, h1⟩ := (ProdAux.memHs_succ_iff r u).1 hu
  refine ⟨h1 j, ?_⟩
  rw [ProdAux.hsNormSq_succ r u hu]
  have h2 : hsNormSq r (derivCoeff j u) ≤ ∑ i, hsNormSq r (derivCoeff i u) :=
    Finset.single_le_sum (f := fun i => hsNormSq r (derivCoeff i u))
      (fun i _ => hsNormSq_nonneg _ _) (Finset.mem_univ j)
  linarith [hsNormSq_nonneg r u]

/-- `∂_i g* : H^{r+1} → H^r`. -/
theorem gradRiesz_bound {s : ℝ} (hsd : s < d) (i : Fin d) {r : ℝ} {c : Coeff d}
    (hc : MemHs (r + 1) c) :
    MemHs r (gradRieszCoeff d s i c) ∧
      hsNormSq r (gradRieszCoeff d s i c) ≤ |rieszConst d s| ^ 2 * hsNormSq (r + 1) c := by
  have hle : ∀ k, sobWeight r k * ‖gradRieszCoeff d s i c k‖ ^ 2 ≤
      |rieszConst d s| ^ 2 * (sobWeight (r + 1) k * ‖c k‖ ^ 2) := by
    intro k
    have h := norm_gradRieszCoeff_le hsd i c k
    have h0 := norm_nonneg (gradRieszCoeff d s i c k)
    have h2 : ‖gradRieszCoeff d s i c k‖ ^ 2 ≤ (|rieszConst d s| * sw k * ‖c k‖) ^ 2 :=
      pow_le_pow_left₀ h0 h 2
    have hw := (sobWeight_pos r k).le
    have hw1 : sobWeight (r + 1) k = sobWeight r k * sw k ^ 2 := by
      rw [sobWeight_add, sw_sq, sobWeight_one]
    calc sobWeight r k * ‖gradRieszCoeff d s i c k‖ ^ 2
        ≤ sobWeight r k * (|rieszConst d s| * sw k * ‖c k‖) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 hw
      _ = _ := by rw [hw1]; ring
  have hs : MemHs r (gradRieszCoeff d s i c) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_pos r k).le (sq_nonneg _)) hle
      (hc.mul_left _)
  refine ⟨hs, ?_⟩
  unfold hsNormSq
  rw [← tsum_mul_left]
  exact hs.tsum_le_tsum hle (hc.mul_left _)

theorem prod_nat (hd : 1 ≤ d) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : Torus d → ℝ, Torus.IsCk (n : WithTop ℕ∞) b → ∀ c : Coeff d,
      MemHs (n : ℝ) c → MemHs (n : ℝ) (mulCoeff (coeffOf b) c) ∧
        hsNormSq (n : ℝ) (mulCoeff (coeffOf b) c) ≤
          C * Torus.cbNorm n b ^ 2 * hsNormSq (n : ℝ) c := by
  obtain ⟨C, hC0, hC⟩ := ProdAux.prodBound_all hd n (n : ℝ) (Nat.cast_nonneg n) (by linarith)
  refine ⟨C, hC0, fun b hb c hc => ?_⟩
  have := hC b (by simpa [Nat.ceil_natCast] using hb) c hc
  simpa [Nat.ceil_natCast] using this


/-! ### The generator as a linear expression in the data -/

/-- The generator written with free coefficients: `ν Δu + ∑_j b_j ∂_j u - ∑_{ij} M_{ji} ∂_i g*(ρ ∂_j u)`. -/
def genOp (M : Matrix (Fin d) (Fin d) ℝ) (s ν : ℝ) (bc : Fin d → Coeff d) (ρc : Coeff d)
    (u : Coeff d) : Coeff d :=
  fun k => (ν : ℂ) * laplaceCoeff u k + ∑ j : Fin d, mulCoeff (bc j) (derivCoeff j u) k -
    ∑ i : Fin d, ∑ j : Fin d, ((M j i : ℝ) : ℂ) *
      gradRieszCoeff d s i (mulCoeff ρc (derivCoeff j u)) k

theorem forwardGen_eq_genOp (D : DynData d) (ρ : Torus d → ℝ) (u : Coeff d) :
    forwardGen D ρ u = genOp D.M D.s D.invβ (driftCoeff D ρ) (coeffOf ρ) u := rfl

theorem genOp_bound (hd : 1 ≤ d) (m : ℕ) :
    ∃ Cp Cq : ℝ, 0 ≤ Cp ∧ 0 ≤ Cq ∧ ∀ (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ), s < d →
      ∀ (MB : ℝ), MatBound MB M → ∀ (ν Bb Br : ℝ), 0 ≤ Bb → 0 ≤ Br →
      ∀ (b : Fin d → Torus d → ℝ) (ρ : Torus d → ℝ),
      (∀ j, Torus.IsCk (m : WithTop ℕ∞) (b j)) → (∀ j, Torus.cbNorm m (b j) ≤ Bb) →
      Torus.IsCk ((m + 1 : ℕ) : WithTop ℕ∞) ρ → Torus.cbNorm (m + 1) ρ ≤ Br →
      ∀ u : Coeff d, MemHs ((m : ℝ) + 2) u →
        MemHs (m : ℝ) (genOp M s ν (fun j => coeffOf (b j)) (coeffOf ρ) u) ∧
        hsNormSq (m : ℝ) (genOp M s ν (fun j => coeffOf (b j)) (coeffOf ρ) u) ≤
          (4 * ν ^ 2 + Cp * Bb ^ 2 + Cq * (MB ^ 2 * |rieszConst d s| ^ 2 * Br ^ 2)) *
            hsNormSq ((m : ℝ) + 2) u := by
  obtain ⟨C0, hC0, hP0⟩ := prod_nat hd m
  obtain ⟨C1, hC1, hP1⟩ := prod_nat hd (m + 1)
  have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨4 * d * d * C0, 4 * (d : ℝ) ^ 4 * C1, by positivity, by positivity, ?_⟩
  intro M s hsd MB hM ν Bb Br hBb hBr b ρ hb hbB hρ hρB u hu
  set X := hsNormSq ((m : ℝ) + 2) u with hX
  have hX0 : 0 ≤ X := hsNormSq_nonneg _ _
  have hu1 : MemHs ((m : ℝ) + 1) u := hu.mono (by linarith)
  have hu2 : MemHs (((m : ℝ) + 1) + 1) u := by
    have : ((m : ℝ) + 1) + 1 = (m : ℝ) + 2 := by ring
    rw [this]; exact hu
  have hXle1 : hsNormSq ((m : ℝ) + 1) u ≤ X := hsNormSq_mono (by linarith) hu
  -- derivatives
  have hd0 : ∀ j, MemHs (m : ℝ) (derivCoeff j u) ∧ hsNormSq (m : ℝ) (derivCoeff j u) ≤ X := fun j => by
    obtain ⟨h1, h2⟩ := deriv_bound hu1 j
    exact ⟨h1, h2.trans hXle1⟩
  have hd1 : ∀ j, MemHs ((m : ℝ) + 1) (derivCoeff j u) ∧
      hsNormSq ((m : ℝ) + 1) (derivCoeff j u) ≤ X := fun j => by
    obtain ⟨h1, h2⟩ := deriv_bound hu2 j
    exact ⟨h1, by rw [hX]; convert h2 using 2; ring⟩
  -- term A
  obtain ⟨hAm, hAe⟩ := hsNormSq_const_mul (m : ℝ) (ν : ℂ) _ (laplace_bound hu).1
  have hAle : hsNormSq (m : ℝ) (fun k => (ν : ℂ) * laplaceCoeff u k) ≤ ν ^ 2 * X := by
    rw [hAe, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact mul_le_mul_of_nonneg_left (laplace_bound hu).2 (sq_nonneg _)
  -- term B
  have hT : ∀ j, MemHs (m : ℝ) (mulCoeff (coeffOf (b j)) (derivCoeff j u)) ∧
      hsNormSq (m : ℝ) (mulCoeff (coeffOf (b j)) (derivCoeff j u)) ≤ C0 * Bb ^ 2 * X := by
    intro j
    obtain ⟨h1, h2⟩ := hP0 (b j) (hb j) _ (hd0 j).1
    refine ⟨h1, h2.trans ?_⟩
    have hcb : Torus.cbNorm m (b j) ^ 2 ≤ Bb ^ 2 :=
      pow_le_pow_left₀ (cbNorm_nonneg' _ _) (hbB j) 2
    have hq0 : (0 : ℝ) ≤ C0 * Bb ^ 2 := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hcb hC0) (hd0 j).2 (hsNormSq_nonneg _ _) hq0
  obtain ⟨hBm, hBle⟩ := hsNormSq_finsum_le Finset.univ
    (fun j => mulCoeff (coeffOf (b j)) (derivCoeff j u)) (m : ℝ) (fun j _ => (hT j).1)
  have hBle' : hsNormSq (m : ℝ) (fun k => ∑ j, mulCoeff (coeffOf (b j)) (derivCoeff j u) k) ≤
      (d : ℝ) * (d * (C0 * Bb ^ 2 * X)) := by
    refine hBle.trans ?_
    simp only [Finset.card_univ, Fintype.card_fin]
    refine mul_le_mul_of_nonneg_left ?_ hdd
    refine (Finset.sum_le_sum fun j _ => (hT j).2).trans ?_
    simp
  -- term C
  have hN : ∀ i j, MemHs (m : ℝ) (fun k => ((M j i : ℝ) : ℂ) *
      gradRieszCoeff d s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k) ∧
      hsNormSq (m : ℝ) (fun k => ((M j i : ℝ) : ℂ) *
      gradRieszCoeff d s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k) ≤
        MB ^ 2 * |rieszConst d s| ^ 2 * (C1 * Br ^ 2 * X) := by
    intro i j
    have hρ1 : Torus.IsCk ((m + 1 : ℕ) : WithTop ℕ∞) ρ := hρ
    obtain ⟨h1, h2⟩ := hP1 ρ hρ1 (derivCoeff j u) (by push_cast; exact (hd1 j).1)
    push_cast at h1 h2
    obtain ⟨h3, h4⟩ := gradRiesz_bound hsd i h1
    obtain ⟨h5, h6⟩ := hsNormSq_const_mul (m : ℝ) ((M j i : ℝ) : ℂ) _ h3
    refine ⟨h5, ?_⟩
    rw [h6, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hMj : M j i ^ 2 ≤ MB ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) (hM j i) 2
      rwa [sq_abs] at this
    have hbr : Torus.cbNorm (m + 1) ρ ^ 2 ≤ Br ^ 2 :=
      pow_le_pow_left₀ (cbNorm_nonneg' _ _) hρB 2
    have e1 : hsNormSq ((m : ℝ) + 1) (mulCoeff (coeffOf ρ) (derivCoeff j u)) ≤ C1 * Br ^ 2 * X :=
      h2.trans (mul_le_mul (mul_le_mul_of_nonneg_left hbr hC1) (hd1 j).2 (hsNormSq_nonneg _ _)
        (by positivity))
    have e2 : hsNormSq (m : ℝ) (gradRieszCoeff d s i (mulCoeff (coeffOf ρ) (derivCoeff j u))) ≤
        |rieszConst d s| ^ 2 * (C1 * Br ^ 2 * X) :=
      h4.trans (mul_le_mul_of_nonneg_left e1 (sq_nonneg _))
    have hq := mul_le_mul hMj e2 (hsNormSq_nonneg _ _) (sq_nonneg MB)
    refine hq.trans (le_of_eq ?_)
    ring
  have hCi : ∀ i, MemHs (m : ℝ) (fun k => ∑ j, ((M j i : ℝ) : ℂ) *
      gradRieszCoeff d s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k) ∧
      hsNormSq (m : ℝ) (fun k => ∑ j, ((M j i : ℝ) : ℂ) *
      gradRieszCoeff d s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k) ≤
        (d : ℝ) * (d * (MB ^ 2 * |rieszConst d s| ^ 2 * (C1 * Br ^ 2 * X))) := by
    intro i
    obtain ⟨h1, h2⟩ := hsNormSq_finsum_le Finset.univ (fun j => fun k => ((M j i : ℝ) : ℂ) *
      gradRieszCoeff d s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k) (m : ℝ) (fun j _ => (hN i j).1)
    refine ⟨h1, h2.trans ?_⟩
    simp only [Finset.card_univ, Fintype.card_fin]
    refine mul_le_mul_of_nonneg_left ?_ hdd
    refine (Finset.sum_le_sum fun j _ => (hN i j).2).trans ?_
    simp
  obtain ⟨hCm, hCle⟩ := hsNormSq_finsum_le Finset.univ (fun i => fun k => ∑ j, ((M j i : ℝ) : ℂ) *
      gradRieszCoeff d s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k) (m : ℝ) (fun i _ => (hCi i).1)
  have hCle' : hsNormSq (m : ℝ) (fun k => ∑ i, ∑ j, ((M j i : ℝ) : ℂ) *
      gradRieszCoeff d s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k) ≤
      (d : ℝ) * (d * (d * (d * (MB ^ 2 * |rieszConst d s| ^ 2 * (C1 * Br ^ 2 * X))))) := by
    refine hCle.trans ?_
    simp only [Finset.card_univ, Fintype.card_fin]
    refine mul_le_mul_of_nonneg_left ?_ hdd
    refine (Finset.sum_le_sum fun i _ => (hCi i).2).trans ?_
    simp
  have hAB := ProdAux.hsNormSq_add_le (m : ℝ) hAm hBm
  have hABC := hsNormSq_sub_le hAB.1 hCm
  have heq : genOp M s ν (fun j => coeffOf (b j)) (coeffOf ρ) u =
      ((fun k => (ν : ℂ) * laplaceCoeff u k) + (fun k => ∑ j, mulCoeff (coeffOf (b j)) (derivCoeff j u) k)) -
        (fun k => ∑ i, ∑ j, ((M j i : ℝ) : ℂ) *
          gradRieszCoeff d s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k) := rfl
  rw [heq]
  refine ⟨memHs_sub hAB.1 hCm, ?_⟩
  refine hABC.trans ?_
  have hX1 : 0 ≤ ν ^ 2 * X := by positivity
  have hq : 0 ≤ MB ^ 2 * |rieszConst d s| ^ 2 * (C1 * Br ^ 2 * X) := by positivity
  have hd4 : (d : ℝ) * (d * (d * (d * (MB ^ 2 * |rieszConst d s| ^ 2 * (C1 * Br ^ 2 * X))))) =
      (d : ℝ) ^ 4 * (MB ^ 2 * |rieszConst d s| ^ 2 * (C1 * Br ^ 2 * X)) := by ring
  rw [hd4] at hCle'
  have hCq : 0 ≤ (d : ℝ) ^ 4 * (MB ^ 2 * |rieszConst d s| ^ 2 * (C1 * Br ^ 2 * X)) := by positivity
  have hB0 : 0 ≤ (d : ℝ) * (d * (C0 * Bb ^ 2 * X)) := by positivity
  nlinarith [hAB.2, hAle, hBle', hCle']


/-! ### The drift difference as a `C^m` function -/

theorem isCk_sub' {k : WithTop ℕ∞} {a b : Torus d → ℝ} (ha : Torus.IsCk k a) (hb : Torus.IsCk k b) :
    Torus.IsCk k (a - b) := by
  unfold Torus.IsCk at *
  exact ha.sub hb

theorem exists_driftDiff_ge2 (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : Matrix (Fin d) (Fin d) ℝ), MatBound MB M →
      ∀ (ρ₁ ρ₂ : Torus d → ℝ), IsProbDensity ρ₁ → IsProbDensity ρ₂ →
      Torus.IsCk (m + 3) ρ₁ → Torus.IsCk (m + 3) ρ₂ →
      Torus.cbNorm (m + 3) ρ₁ ≤ Λ → Torus.cbNorm (m + 3) ρ₂ ≤ Λ →
      ∃ b : Fin d → Torus d → ℝ, (∀ j, Torus.IsCk (m : WithTop ℕ∞) (b j)) ∧
        (∀ j, Torus.cbNorm m (b j) ≤ K * Torus.cbNorm (m + 2) (ρ₁ - ρ₂)) ∧
        ∀ j, coeffOf (b j) = fun k => ∑ i, ((M j i : ℝ) : ℂ) *
          gradRieszCoeff d s i (coeffOf (ρ₁ - ρ₂)) k := by
  obtain ⟨C, hC⟩ := coefficient_bounds_diff (by omega) s hs0 hsd m Λ
  refine ⟨(d : ℝ) ^ 2 * |MB| * max C 0, by positivity, ?_⟩
  intro M hM ρ₁ ρ₂ hp₁ hp₂ h₁ h₂ hΛ₁ hΛ₂
  obtain ⟨hF, hFb⟩ := hC ρ₁ ρ₂ hp₁ hp₂ h₁ h₂ hΛ₁ hΛ₂
  set δ : Torus d → ℝ := ρ₁ - ρ₂ with hδ
  set F : Torus d → Euc d := convGradConv (periodicRieszGrad d s) δ with hFdef
  have hδ3 : Torus.IsCk (m + 3) δ := isCk_sub' h₁ h₂
  have hδ1 : Torus.IsCk 1 δ := hδ3.of_le (by norm_cast; omega)
  have hcont : ∀ i, Continuous fun x => F x i := fun i =>
    (EuclideanSpace.proj i).continuous.comp (convGradConv_continuous hd hs0 hsd δ hδ1)
  have hn1 : ∀ j : Fin d, ‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)‖ ≤ 1 := fun j =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      simpa using PiLp.norm_apply_le v j
  have hTn : ∀ j : Fin d, ‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).comp (matCLM M)‖ ≤
      (d : ℝ) ^ 2 * |MB| := fun j =>
    ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hn1 j) (norm_matCLM_le MB M hM) (norm_nonneg _) zero_le_one)).trans
      (by rw [one_mul])
  refine ⟨fun j x => Torus.matVec M (F x) j, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · have e : Torus.lift (fun x => Torus.matVec M (F x) j) =
        ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).comp (matCLM M)) ∘ Torus.lift F := rfl
    unfold Torus.IsCk
    rw [e]
    refine ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).comp (matCLM M)).contDiff.comp ?_
    have := hF
    unfold Torus.IsCk at this
    exact this.of_le (by norm_cast; omega)
  · have h1 := cbNorm_clm_comp_le ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).comp (matCLM M)) (m + 1) F hF
    have h2 : Torus.cbNorm m (fun x => Torus.matVec M (F x) j) ≤
        Torus.cbNorm (m + 1) (fun x => ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).comp (matCLM M)) (F x)) :=
      cbNorm_mono' (by omega) _
    refine h2.trans (h1.trans ?_)
    have hnn := cbNorm_nonneg (d := d) (m + 1) F
    calc ‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).comp (matCLM M)‖ * Torus.cbNorm (m + 1) F
        ≤ ((d : ℝ) ^ 2 * |MB|) * (C * Torus.cbNorm (m + 2) δ) :=
          mul_le_mul (hTn j) hFb hnn (by positivity)
      _ ≤ ((d : ℝ) ^ 2 * |MB|) * (max C 0 * Torus.cbNorm (m + 2) δ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (cbNorm_nonneg _ _)
      _ = _ := by ring
  · have hfj : (fun x => Torus.matVec M (F x) j) =
        fun x => ∑ i, M j i * F x i - (fun _ : Torus d => (0 : ℝ)) x := by
      funext x
      simp [matVec_apply]
    show coeffOf (fun x => Torus.matVec M (F x) j) = _
    rw [hfj, coeffOf_lin Finset.univ (fun i => M j i) (fun i x => F x i) _ hcont continuous_const]
    funext k
    have h0 : coeffOf (fun _ : Torus d => (0 : ℝ)) k = 0 := by
      rw [coeffOf_eq]; simp
    rw [h0, sub_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFdef, convGradConv_coeff hd hs0 hsd δ hδ1 i]


theorem exists_driftDiff_one (hd : d < 2) (s : ℝ) (hsd : s < d) (m : ℕ) (MB : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : Matrix (Fin d) (Fin d) ℝ), MatBound MB M →
      ∀ (ρ₁ ρ₂ : Torus d → ℝ), Torus.IsCk (m + 3) ρ₁ → Torus.IsCk (m + 3) ρ₂ →
      ∃ b : Fin d → Torus d → ℝ, (∀ j, Torus.IsCk (m : WithTop ℕ∞) (b j)) ∧
        (∀ j, Torus.cbNorm m (b j) ≤ K * Torus.cbNorm (m + 2) (ρ₁ - ρ₂)) ∧
        ∀ j, coeffOf (b j) = fun k => ∑ i, ((M j i : ℝ) : ℂ) *
          gradRieszCoeff d s i (coeffOf (ρ₁ - ρ₂)) k := by
  have hdr : (d : ℝ) < 2 := by exact_mod_cast hd
  obtain ⟨Ct, hCt⟩ := toFun_isCk_le (d := d) m ((m : ℝ) + 1) (by linarith)
  set Kn : ℝ := ((d : ℝ) + 1) ^ (m + 2) * ((multiIndices d (m + 2)).card : ℝ) with hKn
  have hKn0 : 0 ≤ Kn := by positivity
  have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨max Ct 0 * ((d : ℝ) * |MB| * |rieszConst d s| * Real.sqrt Kn), by positivity, ?_⟩
  intro M hM ρ₁ ρ₂ h₁ h₂
  set δ : Torus d → ℝ := ρ₁ - ρ₂ with hδ
  have hδ3 : Torus.IsCk (m + 3) δ := isCk_sub' h₁ h₂
  have hδ2 : Torus.IsCk ((m + 2 : ℕ) : WithTop ℕ∞) δ := by
    have := hδ3.of_le (show ((m + 2 : ℕ) : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) + 3 by
      norm_cast; omega)
    exact this
  have hδ1 : Torus.IsCk 1 δ := hδ3.of_le (by norm_cast; omega)
  have hreal : IsRealCoeff (coeffOf δ) := isRealCoeff_coeffOf_of_isCk hδ1
  obtain ⟨hH, hHN⟩ := memHs_coeffOf_cbNorm (m + 2) δ hδ2
  have hcast : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 1 + 1 := by push_cast; ring
  rw [hcast] at hH hHN
  set cb : ℝ := Torus.cbNorm (m + 2) δ with hcb
  have hcb0 : 0 ≤ cb := cbNorm_nonneg _ _
  set rc : ℝ := |rieszConst d s| with hrc
  have hgr : ∀ i, IsRealCoeff (gradRieszCoeff d s i (coeffOf δ)) := fun i =>
    isRealCoeff_gradRieszCoeff s i hreal
  have hrow : ∀ j : Fin d, ∑ i : Fin d, M j i ^ 2 ≤ (d : ℝ) * MB ^ 2 := by
    intro j
    calc ∑ i : Fin d, M j i ^ 2 ≤ ∑ _i : Fin d, MB ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := pow_le_pow_left₀ (abs_nonneg _) (hM j i) 2
          rwa [sq_abs] at this
      _ = _ := by simp
  have hmem : ∀ j : Fin d, MemHs ((m : ℝ) + 1) (fun k => ∑ i, ((M j i : ℝ) : ℂ) *
      gradRieszCoeff d s i (coeffOf δ) k) ∧
      hsNormSq ((m : ℝ) + 1) (fun k => ∑ i, ((M j i : ℝ) : ℂ) *
        gradRieszCoeff d s i (coeffOf δ) k) ≤ ((d : ℝ) * |MB| * rc * Real.sqrt Kn * cb) ^ 2 := by
    intro j
    have hg : ∀ i, MemHs ((m : ℝ) + 1) (fun k => ((M j i : ℝ) : ℂ) *
        gradRieszCoeff d s i (coeffOf δ) k) ∧
        hsNormSq ((m : ℝ) + 1) (fun k => ((M j i : ℝ) : ℂ) *
        gradRieszCoeff d s i (coeffOf δ) k) ≤ M j i ^ 2 * (rc ^ 2 * (Kn * cb ^ 2)) := by
      intro i
      obtain ⟨h1, h2⟩ := gradRiesz_bound hsd i hH
      obtain ⟨h3, h4⟩ := hsNormSq_const_mul ((m : ℝ) + 1) ((M j i : ℝ) : ℂ) _ h1
      refine ⟨h3, ?_⟩
      rw [h4, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left hHN (sq_nonneg _)))
        (sq_nonneg _)
    obtain ⟨h1, h2⟩ := hsNormSq_finsum_le Finset.univ (fun i => fun k => ((M j i : ℝ) : ℂ) *
      gradRieszCoeff d s i (coeffOf δ) k) ((m : ℝ) + 1) (fun i _ => (hg i).1)
    refine ⟨h1, h2.trans ?_⟩
    simp only [Finset.card_univ, Fintype.card_fin]
    have h3 : ∑ i, hsNormSq ((m : ℝ) + 1) (fun k => ((M j i : ℝ) : ℂ) *
        gradRieszCoeff d s i (coeffOf δ) k) ≤ ∑ i : Fin d, M j i ^ 2 * (rc ^ 2 * (Kn * cb ^ 2)) :=
      Finset.sum_le_sum fun i _ => (hg i).2
    rw [← Finset.sum_mul] at h3
    have h5 : (∑ i : Fin d, M j i ^ 2) * (rc ^ 2 * (Kn * cb ^ 2)) ≤
        ((d : ℝ) * MB ^ 2) * (rc ^ 2 * (Kn * cb ^ 2)) :=
      mul_le_mul_of_nonneg_right (hrow j) (by positivity)
    have hsq : ((d : ℝ) * |MB| * rc * Real.sqrt Kn * cb) ^ 2 =
        (d : ℝ) ^ 2 * MB ^ 2 * (rc ^ 2 * (Kn * cb ^ 2)) := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow, sq_abs, Real.sq_sqrt hKn0]; ring
    rw [hsq]
    calc (d : ℝ) * ∑ i, hsNormSq ((m : ℝ) + 1) (fun k => ((M j i : ℝ) : ℂ) *
          gradRieszCoeff d s i (coeffOf δ) k)
        ≤ (d : ℝ) * (((d : ℝ) * MB ^ 2) * (rc ^ 2 * (Kn * cb ^ 2))) :=
          mul_le_mul_of_nonneg_left (h3.trans h5) hdd
      _ = _ := by ring
  have hrealj : ∀ j : Fin d, IsRealCoeff (fun k => ∑ i, ((M j i : ℝ) : ℂ) *
      gradRieszCoeff d s i (coeffOf δ) k) := by
    intro j k
    simp only [map_sum, map_mul, Complex.conj_ofReal]
    exact Finset.sum_congr rfl fun i _ => by rw [hgr i k]
  refine ⟨fun j => toFun (fun k => ∑ i, ((M j i : ℝ) : ℂ) * gradRieszCoeff d s i (coeffOf δ) k),
    fun j => (hCt _ (hmem j).1 (hrealj j)).1, fun j => ?_, fun j => ?_⟩
  · obtain ⟨-, hcbj⟩ := hCt _ (hmem j).1 (hrealj j)
    refine hcbj.trans ?_
    have hnn : 0 ≤ hsNorm ((m : ℝ) + 1) (fun k => ∑ i, ((M j i : ℝ) : ℂ) *
      gradRieszCoeff d s i (coeffOf δ) k) := Real.sqrt_nonneg _
    have hle : hsNorm ((m : ℝ) + 1) (fun k => ∑ i, ((M j i : ℝ) : ℂ) *
        gradRieszCoeff d s i (coeffOf δ) k) ≤ (d : ℝ) * |MB| * rc * Real.sqrt Kn * cb := by
      unfold hsNorm
      calc Real.sqrt _ ≤ Real.sqrt (((d : ℝ) * |MB| * rc * Real.sqrt Kn * cb) ^ 2) :=
            Real.sqrt_le_sqrt (hmem j).2
        _ = _ := Real.sqrt_sq (by positivity)
    calc Ct * hsNorm ((m : ℝ) + 1) (fun k => ∑ i, ((M j i : ℝ) : ℂ) *
          gradRieszCoeff d s i (coeffOf δ) k)
        ≤ max Ct 0 * hsNorm ((m : ℝ) + 1) (fun k => ∑ i, ((M j i : ℝ) : ℂ) *
          gradRieszCoeff d s i (coeffOf δ) k) := mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
      _ ≤ max Ct 0 * ((d : ℝ) * |MB| * rc * Real.sqrt Kn * cb) :=
          mul_le_mul_of_nonneg_left hle (le_max_right _ _)
      _ = _ := by ring
  · exact coeffOf_toFun _ (hrealj j)
      (summable_norm_of_memHs ((m : ℝ) + 1) (by linarith) _ (hmem j).1)


theorem exists_driftDiff (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : Matrix (Fin d) (Fin d) ℝ), MatBound MB M →
      ∀ (ρ₁ ρ₂ : Torus d → ℝ), IsProbDensity ρ₁ → IsProbDensity ρ₂ →
      Torus.IsCk (m + 3) ρ₁ → Torus.IsCk (m + 3) ρ₂ →
      Torus.cbNorm (m + 3) ρ₁ ≤ Λ → Torus.cbNorm (m + 3) ρ₂ ≤ Λ →
      ∃ b : Fin d → Torus d → ℝ, (∀ j, Torus.IsCk (m : WithTop ℕ∞) (b j)) ∧
        (∀ j, Torus.cbNorm m (b j) ≤ K * Torus.cbNorm (m + 2) (ρ₁ - ρ₂)) ∧
        ∀ j, coeffOf (b j) = fun k => ∑ i, ((M j i : ℝ) : ℂ) *
          gradRieszCoeff d s i (coeffOf (ρ₁ - ρ₂)) k := by
  by_cases h2 : 2 ≤ d
  · exact exists_driftDiff_ge2 h2 s hs0 hsd m MB Λ
  · obtain ⟨K, hK0, hK⟩ := exists_driftDiff_one (by omega) s hsd m MB
    exact ⟨K, hK0, fun M hM ρ₁ ρ₂ _ _ h₁ h₂ _ _ => hK M hM ρ₁ ρ₂ h₁ h₂⟩

/-! ### Linearity helpers -/

theorem mulCoeff_sub_left {a₁ a₂ c : Coeff d} (h₁ : MemHs 0 a₁) (h₂ : MemHs 0 a₂) (hc : MemHs 0 c) :
    mulCoeff (a₁ - a₂) c = mulCoeff a₁ c - mulCoeff a₂ c := by
  funext k
  unfold mulCoeff
  simp only [Pi.sub_apply, sub_mul]
  exact (summable_mulCoeff a₁ c h₁ hc k).tsum_sub (summable_mulCoeff a₂ c h₂ hc k)

theorem gradRieszCoeff_sub (s : ℝ) (i : Fin d) (c₁ c₂ : Coeff d) :
    gradRieszCoeff d s i (c₁ - c₂) = gradRieszCoeff d s i c₁ - gradRieszCoeff d s i c₂ := by
  funext k
  simp only [gradRieszCoeff, rieszMult, derivCoeff, Pi.sub_apply]
  ring

theorem coeffOf_sub' {ρ₁ ρ₂ : Torus d → ℝ} (h₁ : Continuous ρ₁) (h₂ : Continuous ρ₂) :
    coeffOf (ρ₁ - ρ₂) = coeffOf ρ₁ - coeffOf ρ₂ := by
  funext k
  rw [Pi.sub_apply, coeffOf_eq, coeffOf_eq, coeffOf_eq, ← integral_sub]
  · congr 1
    funext x
    simp only [Pi.sub_apply, Complex.ofReal_sub, mul_sub]
  · exact integrable_of_continuous' ((Torus.continuous_mode _).mul (Complex.continuous_ofReal.comp h₁))
  · exact integrable_of_continuous' ((Torus.continuous_mode _).mul (Complex.continuous_ofReal.comp h₂))

theorem forwardGen_diff_eq (D₁ D₂ : DynData d) (hM : D₁.M = D₂.M) (hs : D₁.s = D₂.s)
    (hV : D₁.V = D₂.V) (ρ₁ ρ₂ : Torus d → ℝ) (hρ₁ : Continuous ρ₁) (hρ₂ : Continuous ρ₂)
    (hr₁ : MemHs 0 (coeffOf ρ₁)) (hr₂ : MemHs 0 (coeffOf ρ₂))
    (hb₁ : ∀ j, MemHs 0 (driftCoeff D₁ ρ₁ j)) (hb₂ : ∀ j, MemHs 0 (driftCoeff D₂ ρ₂ j))
    (b : Fin d → Torus d → ℝ)
    (hb : ∀ j, coeffOf (b j) = fun k => ∑ i, ((D₁.M j i : ℝ) : ℂ) *
          gradRieszCoeff d D₁.s i (coeffOf (ρ₁ - ρ₂)) k)
    (u : Coeff d) (hu : MemHs 1 u) :
    forwardGen D₁ ρ₁ u - forwardGen D₂ ρ₂ u =
      genOp D₁.M D₁.s (D₁.invβ - D₂.invβ) (fun j => coeffOf (b j)) (coeffOf (ρ₁ - ρ₂)) u := by
  have hd0 : ∀ j, MemHs 0 (derivCoeff j u) := fun j => (memHs_zero_deriv hu j).1
  have hdr : ∀ j, driftCoeff D₁ ρ₁ j - driftCoeff D₂ ρ₂ j = coeffOf (b j) := by
    intro j
    rw [hb j]
    funext k
    simp only [driftCoeff, Pi.sub_apply, ← hM, ← hs, ← hV]
    rw [coeffOf_sub' hρ₁ hρ₂]
    simp only [gradRieszCoeff_sub, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  have hcs := coeffOf_sub' hρ₁ hρ₂
  funext k
  simp only [forwardGen, transportCoeff, nonlocalCoeff, genOp, Pi.sub_apply]
  have e1 : ∀ j, mulCoeff (driftCoeff D₁ ρ₁ j) (derivCoeff j u) k -
      mulCoeff (driftCoeff D₂ ρ₂ j) (derivCoeff j u) k =
      mulCoeff (coeffOf (b j)) (derivCoeff j u) k := by
    intro j
    rw [← hdr j, mulCoeff_sub_left (hb₁ j) (hb₂ j) (hd0 j)]
    rfl
  have e2 : ∀ j, mulCoeff (coeffOf ρ₁) (derivCoeff j u) - mulCoeff (coeffOf ρ₂) (derivCoeff j u) =
      mulCoeff (coeffOf (ρ₁ - ρ₂)) (derivCoeff j u) := by
    intro j
    rw [hcs, mulCoeff_sub_left hr₁ hr₂ (hd0 j)]
  have e3 : ∀ i j, gradRieszCoeff d D₁.s i (mulCoeff (coeffOf ρ₁) (derivCoeff j u)) k -
      gradRieszCoeff d D₁.s i (mulCoeff (coeffOf ρ₂) (derivCoeff j u)) k =
      gradRieszCoeff d D₁.s i (mulCoeff (coeffOf (ρ₁ - ρ₂)) (derivCoeff j u)) k := by
    intro i j
    rw [← e2 j, gradRieszCoeff_sub]
    rfl
  simp only [← hM, ← hs]
  have s1 : ∑ j, mulCoeff (driftCoeff D₁ ρ₁ j) (derivCoeff j u) k -
      ∑ j, mulCoeff (driftCoeff D₂ ρ₂ j) (derivCoeff j u) k =
      ∑ j, mulCoeff (coeffOf (b j)) (derivCoeff j u) k := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => e1 j
  have s2 : ∑ i, ∑ j, ((D₁.M j i : ℝ) : ℂ) *
        gradRieszCoeff d D₁.s i (mulCoeff (coeffOf ρ₁) (derivCoeff j u)) k -
      ∑ i, ∑ j, ((D₁.M j i : ℝ) : ℂ) *
        gradRieszCoeff d D₁.s i (mulCoeff (coeffOf ρ₂) (derivCoeff j u)) k =
      ∑ i, ∑ j, ((D₁.M j i : ℝ) : ℂ) *
        gradRieszCoeff d D₁.s i (mulCoeff (coeffOf (ρ₁ - ρ₂)) (derivCoeff j u)) k := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_sub, e3 i j]
  push_cast
  linear_combination s1 - s2


/-! ### Bounds of the generator `H^{m+2} → H^m` -/

theorem forwardGen_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ VB : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (D : DynData d), D.s = s → MatBound MB D.M → VHyp m VB D.V →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsCk (m + 3) ρ → Torus.cbNorm (m + 3) ρ ≤ Λ →
      ∀ u : Coeff d, MemHs ((m : ℝ) + 2) u →
        MemHs (m : ℝ) (forwardGen D ρ u) ∧
        hsNormSq (m : ℝ) (forwardGen D ρ u) ≤ (4 * D.invβ ^ 2 + c) * hsNormSq ((m : ℝ) + 2) u := by
  obtain ⟨B, hB⟩ := exists_driftFuns hd s hs0 hsd m MB Λ VB
  obtain ⟨Cp, Cq, hCp, hCq, hG⟩ := genOp_bound hd m
  refine ⟨Cp * |B| ^ 2 + Cq * (MB ^ 2 * |rieszConst d s| ^ 2 * |Λ| ^ 2), by positivity, ?_⟩
  intro D hDs hM hV ρ hprob hρ hρΛ u hu
  obtain ⟨b, hb1, hb2, hb3⟩ := hB D hDs hM hV ρ hprob hρ hρΛ
  have hdr : driftCoeff D ρ = fun j => coeffOf (b j) := funext fun j => (hb3 j).symm
  have hρ1 : Torus.IsCk ((m + 1 : ℕ) : WithTop ℕ∞) ρ := hρ.of_le (by norm_cast; omega)
  have hρB : Torus.cbNorm (m + 1) ρ ≤ |Λ| :=
    (cbNorm_mono' (by omega) ρ).trans (hρΛ.trans (le_abs_self _))
  have hbm : ∀ j, Torus.IsCk (m : WithTop ℕ∞) (b j) := fun j => (hb1 j).of_le (by norm_cast; omega)
  have hbB : ∀ j, Torus.cbNorm m (b j) ≤ |B| := fun j =>
    (cbNorm_mono' (by omega) (b j)).trans ((hb2 j).trans (le_abs_self _))
  have := hG D.M D.s (hDs ▸ hsd) MB hM D.invβ |B| |Λ| (abs_nonneg _) (abs_nonneg _) b ρ hbm hbB
    hρ1 hρB u hu
  rw [forwardGen_eq_genOp, hdr]
  refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
  rw [hDs, sq_abs, sq_abs]
  ring

theorem forwardGen_diff_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ : ℝ) :
    ∃ Kd : ℝ, 0 ≤ Kd ∧ ∀ (D₁ D₂ : DynData d), D₁.s = s → D₂.s = s → D₁.M = D₂.M →
      MatBound MB D₁.M → D₁.V = D₂.V →
      ∀ ρ₁ ρ₂ : Torus d → ℝ, IsProbDensity ρ₁ → IsProbDensity ρ₂ →
      Torus.IsCk (m + 3) ρ₁ → Torus.IsCk (m + 3) ρ₂ →
      Torus.cbNorm (m + 3) ρ₁ ≤ Λ → Torus.cbNorm (m + 3) ρ₂ ≤ Λ →
      MemHs 0 (coeffOf ρ₁) → MemHs 0 (coeffOf ρ₂) →
      (∀ j, MemHs 0 (driftCoeff D₁ ρ₁ j)) → (∀ j, MemHs 0 (driftCoeff D₂ ρ₂ j)) →
      ∀ δ : ℝ, Torus.cbNorm (m + 2) (ρ₁ - ρ₂) ≤ δ →
      ∀ u : Coeff d, MemHs ((m : ℝ) + 2) u →
        MemHs (m : ℝ) (forwardGen D₁ ρ₁ u - forwardGen D₂ ρ₂ u) ∧
        hsNormSq (m : ℝ) (forwardGen D₁ ρ₁ u - forwardGen D₂ ρ₂ u) ≤
          (Kd * (|D₁.invβ - D₂.invβ| + δ)) ^ 2 * hsNormSq ((m : ℝ) + 2) u := by
  obtain ⟨K, hK0, hK⟩ := exists_driftDiff hd s hs0 hsd m MB Λ
  obtain ⟨Cp, Cq, hCp, hCq, hG⟩ := genOp_bound hd m
  set rc : ℝ := |rieszConst d s| with hrc
  refine ⟨Real.sqrt (4 + Cp * K ^ 2 + Cq * (MB ^ 2 * rc ^ 2)), Real.sqrt_nonneg _, ?_⟩
  intro D₁ D₂ hs₁ hs₂ hM hMB hV ρ₁ ρ₂ hp₁ hp₂ h₁ h₂ hΛ₁ hΛ₂ hr₁ hr₂ hb₁ hb₂ δ hδ u hu
  obtain ⟨b, hb1, hb2, hb3⟩ := hK D₁.M hMB ρ₁ ρ₂ hp₁ hp₂ h₁ h₂ hΛ₁ hΛ₂
  have hcn : 0 ≤ Torus.cbNorm (m + 2) (ρ₁ - ρ₂) := cbNorm_nonneg _ _
  have hδ0 : 0 ≤ δ := hcn.trans hδ
  have hc1 : Continuous ρ₁ := continuous_of_isCkU h₁
  have hc2 : Continuous ρ₂ := continuous_of_isCkU h₂
  have hu1 : MemHs 1 u := hu.mono (by linarith)
  have heq := forwardGen_diff_eq D₁ D₂ hM (hs₁.trans hs₂.symm) hV ρ₁ ρ₂ hc1 hc2 hr₁ hr₂ hb₁ hb₂ b
    (by rw [hs₁]; exact hb3) u hu1
  rw [heq]
  have hδ2 : Torus.IsCk (m + 3) (ρ₁ - ρ₂) := isCk_sub' h₁ h₂
  have hρ1 : Torus.IsCk ((m + 1 : ℕ) : WithTop ℕ∞) (ρ₁ - ρ₂) := hδ2.of_le (by norm_cast; omega)
  have hρB : Torus.cbNorm (m + 1) (ρ₁ - ρ₂) ≤ δ :=
    (cbNorm_mono' (by omega) _).trans hδ
  have hbm : ∀ j, Torus.cbNorm m (b j) ≤ K * δ := fun j =>
    (hb2 j).trans (mul_le_mul_of_nonneg_left hδ hK0)
  have := hG D₁.M D₁.s (hs₁ ▸ hsd) MB hMB (D₁.invβ - D₂.invβ) (K * δ) δ (by positivity) hδ0 b
    (ρ₁ - ρ₂) hb1 hbm hρ1 hρB u hu
  refine ⟨this.1, this.2.trans ?_⟩
  rw [hs₁]
  set X := hsNormSq ((m : ℝ) + 2) u
  have hX0 : 0 ≤ X := hsNormSq_nonneg _ _
  refine mul_le_mul_of_nonneg_right ?_ hX0
  set a := |D₁.invβ - D₂.invβ| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  have hsq : (D₁.invβ - D₂.invβ) ^ 2 = a ^ 2 := (sq_abs _).symm
  have hP : 0 ≤ Cp * K ^ 2 + Cq * (MB ^ 2 * rc ^ 2) := by positivity
  have hQ : 0 ≤ 4 + Cp * K ^ 2 + Cq * (MB ^ 2 * rc ^ 2) := by positivity
  have hRHS : (Real.sqrt (4 + Cp * K ^ 2 + Cq * (MB ^ 2 * rc ^ 2)) * (a + δ)) ^ 2 =
      (4 + Cp * K ^ 2 + Cq * (MB ^ 2 * rc ^ 2)) * (a + δ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hQ]
  rw [hRHS, hsq]
  have h1 : a ^ 2 ≤ (a + δ) ^ 2 := by nlinarith
  have h2 : δ ^ 2 ≤ (a + δ) ^ 2 := by nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 hP
  have e : Cp * (K ^ 2 * δ ^ 2) + Cq * (MB ^ 2 * |rieszConst d s| ^ 2 * δ ^ 2) =
      (Cp * K ^ 2 + Cq * (MB ^ 2 * rc ^ 2)) * δ ^ 2 := by rw [hrc]; ring
  nlinarith [e, h1, h3]


/-! ### The complex form estimate at level `r` -/

theorem pairing_real_w {n : ℕ} (W : Lattice d → ℝ) (hW : ∀ k, W (-k) = W k) {a b : Coeff d}
    (ha : IsRealCoeff a) (hb : IsRealCoeff b) :
    (∑ k ∈ boxFinset d n, (W k : ℂ) * (a k * conj (b k))).im = 0 := by
  set T := ∑ k ∈ boxFinset d n, (W k : ℂ) * (a k * conj (b k)) with hT
  have h : conj T = T := by
    rw [hT, map_sum]
    refine Finset.sum_nbij' (fun k => -k) (fun k => -k) ?_ ?_ ?_ ?_ ?_
    · intro k hk; rw [mem_boxFinset] at hk ⊢; exact hk.neg
    · intro k hk; rw [mem_boxFinset] at hk ⊢; exact hk.neg
    · intro k _; simp
    · intro k _; simp
    · intro k _
      simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
      rw [hW k, ← ha k, show b k = conj (b (-k)) by have := hb (-k); rwa [neg_neg] at this]
  exact Complex.conj_eq_iff_im.1 h

theorem complex_form_w {n : ℕ} {L : Coeff d → Coeff d} {Λ₀ : ℝ} (r : ℝ)
    (hadd : ∀ a b, IsTrigPoly n a → IsTrigPoly n b → L (a + b) = L a + L b)
    (hsmul : ∀ (c : ℂ) a, L (c • a) = c • L a)
    (hrefl : ∀ a, L (reflConj a) = reflConj (L a))
    (hreal : ∀ G, IsRealCoeff G → IsTrigPoly n G →
      (hsInner r (L G) G).re ≤ Λ₀ * hsNormSq r G)
    (w : Coeff d) (hw : IsTrigPoly n w) : (hsInner r (L w) w).re ≤ Λ₀ * hsNormSq r w := by
  set u : Coeff d := fun k => (w k + conj (w (-k))) / 2 with hu
  set v : Coeff d := fun k => (w k - conj (w (-k))) / (2 * Complex.I) with hv
  have hur : IsRealCoeff u := by
    intro k; simp only [hu, map_div₀, map_add, Complex.conj_conj, neg_neg, map_ofNat]; simp [add_comm]
  have hvr : IsRealCoeff v := by
    intro k
    simp only [hv, map_div₀, map_sub, Complex.conj_conj, neg_neg, map_mul, Complex.conj_I,
      map_ofNat]
    field_simp
    ring
  have hut : IsTrigPoly n u := by
    intro k hk
    by_contra hb
    apply hk
    have h1 : w k = 0 := hw.eq_zero hb
    have h2 : w (-k) = 0 := hw.eq_zero (fun h => hb (inBox_neg_iff.1 h))
    simp [hu, h1, h2]
  have hvt : IsTrigPoly n v := by
    intro k hk
    by_contra hb
    apply hk
    have h1 : w k = 0 := hw.eq_zero hb
    have h2 : w (-k) = 0 := hw.eq_zero (fun h => hb (inBox_neg_iff.1 h))
    simp [hv, h1, h2]
  have hwuv : w = u + Complex.I • v := by
    funext k
    simp only [hu, hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hIv : IsTrigPoly n (Complex.I • v) := hvt.smul _
  have hLw : L w = L u + Complex.I • L v := by
    conv_lhs => rw [hwuv]
    rw [hadd u _ hut hIv, hsmul]
  have hLur : IsRealCoeff (L u) := by
    rw [isRealCoeff_iff_reflConj, ← hrefl, (isRealCoeff_iff_reflConj u).1 hur]
  have hLvr : IsRealCoeff (L v) := by
    rw [isRealCoeff_iff_reflConj, ← hrefl, (isRealCoeff_iff_reflConj v).1 hvr]
  -- finite sums
  have hQ : ∀ a b : Coeff d, IsTrigPoly n b →
      hsInner r a b = ∑ k ∈ boxFinset d n, (sobWeight r k : ℂ) * (a k * conj (b k)) := by
    intro a b hb
    rw [hsInner_trig hb r]
  have hN : ∀ a : Coeff d, IsTrigPoly n a →
      hsNormSq r a = ∑ k ∈ boxFinset d n, sobWeight r k * ‖a k‖ ^ 2 := by
    intro a ha
    rw [hsNormSq_trig ha r]
  have hwk : ∀ k, w k = u k + Complex.I * v k := fun k => by
    have := congrFun hwuv k
    simpa using this
  set W : Lattice d → ℝ := fun k => sobWeight r k with hWdef
  have hWs : ∀ k, W (-k) = W k := fun k => sobWeight_neg r k
  have e1 : ∑ k ∈ boxFinset d n, (W k : ℂ) * (L w k * conj (w k)) =
      (∑ k ∈ boxFinset d n, (W k : ℂ) * (L u k * conj (u k))) +
        (∑ k ∈ boxFinset d n, (W k : ℂ) * (L v k * conj (v k))) +
        Complex.I * ((∑ k ∈ boxFinset d n, (W k : ℂ) * (L v k * conj (u k))) -
          (∑ k ∈ boxFinset d n, (W k : ℂ) * (L u k * conj (v k)))) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hLw, hwk k]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, Complex.conj_I]
    have hI := Complex.I_sq
    linear_combination ((W k : ℂ) * (L v k * conj (v k))) * (-hI) + 0 * hI
  have e2 : ∑ k ∈ boxFinset d n, W k * ‖w k‖ ^ 2 =
      (∑ k ∈ boxFinset d n, W k * ‖u k‖ ^ 2) + (∑ k ∈ boxFinset d n, W k * ‖v k‖ ^ 2) +
        2 * (∑ k ∈ boxFinset d n, (W k : ℂ) * (u k * conj (v k))).im := by
    rw [Complex.im_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hwk k]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hp1 : (∑ k ∈ boxFinset d n, (W k : ℂ) * (L v k * conj (u k))).im = 0 :=
    pairing_real_w W hWs hLvr hur
  have hp2 : (∑ k ∈ boxFinset d n, (W k : ℂ) * (L u k * conj (v k))).im = 0 :=
    pairing_real_w W hWs hLur hvr
  have hp3 : (∑ k ∈ boxFinset d n, (W k : ℂ) * (u k * conj (v k))).im = 0 :=
    pairing_real_w W hWs hur hvr
  have hre : (hsInner r (L w) w).re = (hsInner r (L u) u).re + (hsInner r (L v) v).re := by
    rw [hQ _ _ hw, hQ _ _ hut, hQ _ _ hvt, e1]
    simp [Complex.add_re, Complex.sub_im, hp1, hp2]
    rfl
  have hnorm : hsNormSq r w = hsNormSq r u + hsNormSq r v := by
    rw [hN w hw, hN u hut, hN v hvt, e2, hp3]; ring
  rw [hre, hnorm]
  have := hreal u hur hut
  have := hreal v hvr hvt
  nlinarith


/-! ### Weighted Cauchy-Schwarz and the extension of the energy inequality to `H^{r+2}` -/

theorem weighted_cs {r : ℝ} {a b : Coeff d} (ha : MemHs r a) (hb : MemHs r b) :
    Summable (fun k => sobWeight r k * (‖a k‖ * ‖b k‖)) ∧
      ∑' k, sobWeight r k * (‖a k‖ * ‖b k‖) ≤ hsNorm r a * hsNorm r b := by
  have hW : ∀ k : Lattice d, Real.sqrt (sobWeight r k) ^ 2 = sobWeight r k := fun k =>
    Real.sq_sqrt (sobWeight_pos r k).le
  have hsa : Summable fun k => (Real.sqrt (sobWeight r k) * ‖a k‖) ^ 2 :=
    ha.congr fun k => by rw [mul_pow, hW]
  have hsb : Summable fun k => (Real.sqrt (sobWeight r k) * ‖b k‖) ^ 2 :=
    hb.congr fun k => by rw [mul_pow, hW]
  have h := Torus.cs_tsum (fun k => Real.sqrt (sobWeight r k) * ‖a k‖)
    (fun k => Real.sqrt (sobWeight r k) * ‖b k‖)
    (fun k => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (fun k => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hsa hsb
  have e : ∀ k, (Real.sqrt (sobWeight r k) * ‖a k‖) * (Real.sqrt (sobWeight r k) * ‖b k‖) =
      sobWeight r k * (‖a k‖ * ‖b k‖) := fun k => by
    calc _ = Real.sqrt (sobWeight r k) ^ 2 * (‖a k‖ * ‖b k‖) := by ring
      _ = _ := by rw [hW k]
  have ea : ∑' k, (Real.sqrt (sobWeight r k) * ‖a k‖) ^ 2 = hsNormSq r a := by
    unfold hsNormSq; exact tsum_congr fun k => by rw [mul_pow, hW]
  have eb : ∑' k, (Real.sqrt (sobWeight r k) * ‖b k‖) ^ 2 = hsNormSq r b := by
    unfold hsNormSq; exact tsum_congr fun k => by rw [mul_pow, hW]
  simp_rw [e] at h
  rw [ea, eb] at h
  exact h

theorem hsInner_summable {r : ℝ} {a b : Coeff d} (ha : MemHs r a) (hb : MemHs r b) :
    Summable (fun k => ((sobWeight r k : ℝ) : ℂ) * (a k * conj (b k))) := by
  refine Summable.of_norm ?_
  refine (weighted_cs ha hb).1.congr fun k => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sobWeight_pos r k), norm_mul,
    Complex.norm_conj]

theorem norm_hsInner_le {r : ℝ} {a b : Coeff d} (ha : MemHs r a) (hb : MemHs r b) :
    ‖hsInner r a b‖ ≤ hsNorm r a * hsNorm r b := by
  unfold hsInner
  refine (norm_tsum_le_tsum_norm (hsInner_summable ha hb).norm).trans ?_
  refine le_trans (le_of_eq ?_) (weighted_cs ha hb).2
  refine tsum_congr fun k => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sobWeight_pos r k), norm_mul,
    Complex.norm_conj]

theorem hsInner_add_left {r : ℝ} {a₁ a₂ b : Coeff d} (h₁ : MemHs r a₁) (h₂ : MemHs r a₂)
    (hb : MemHs r b) : hsInner r (a₁ + a₂) b = hsInner r a₁ b + hsInner r a₂ b := by
  unfold hsInner
  rw [← (hsInner_summable h₁ hb).tsum_add (hsInner_summable h₂ hb)]
  refine tsum_congr fun k => ?_
  simp only [Pi.add_apply]
  ring

theorem hsNormSq_eq_norm_sq {r : ℝ} (a : Coeff d) : hsNormSq r a = hsNorm r a ^ 2 := by
  unfold hsNorm
  rw [Real.sq_sqrt (hsNormSq_nonneg _ _)]

/-- The energy inequality, known for trigonometric polynomials, extends to `H^{r+2}`. -/
theorem energy_extend {L : Coeff d → Coeff d} {K Λ₀ : ℝ} (r : ℝ) (hK0 : 0 ≤ K)
    (hbd : ∀ u, MemHs (r + 2) u → MemHs r (L u) ∧ hsNormSq r (L u) ≤ K ^ 2 * hsNormSq (r + 2) u)
    (hsub : ∀ u v, MemHs (r + 2) u → MemHs (r + 2) v → L (u - v) = L u - L v)
    (hen : ∀ n w, IsTrigPoly n w → (hsInner r (L w) w).re ≤ Λ₀ * hsNormSq r w)
    (u : Coeff d) (hu : MemHs (r + 2) u) : (hsInner r (L u) u).re ≤ Λ₀ * hsNormSq r u := by
  have hu0 : MemHs r u := hu.mono (by linarith)
  obtain ⟨hLu, -⟩ := hbd u hu
  have hmain : ∀ n : ℕ, ∑ k ∈ boxFinset d n, (sobWeight r k * ((L u k) * conj (u k))).re ≤
      Λ₀ * ∑ k ∈ boxFinset d n, sobWeight r k * ‖u k‖ ^ 2 +
        K * hsNorm (r + 2) (u - truncCoeff n u) * hsNorm r u := by
    intro n
    set P := truncCoeff n u with hP
    have hPt : IsTrigPoly n P := isTrigPoly_truncCoeff n u
    have hPm : MemHs (r + 2) P := memHs_truncCoeff n hu
    have hRm : MemHs (r + 2) (u - P) := memHs_sub_truncCoeff n hu
    have hPk : ∀ k ∈ boxFinset d n, P k = u k := fun k hk => by
      simp [hP, truncCoeff, mem_boxFinset.1 hk]
    have hLu' : L u = L P + L (u - P) := by
      rw [hsub u P hu hPm]; abel
    obtain ⟨hLPm, -⟩ := hbd P hPm
    obtain ⟨hLRm, hLRb⟩ := hbd (u - P) hRm
    have hPm0 : MemHs r P := hPm.mono (by linarith)
    -- the box sum is the inner product with `P`
    have e1 : ∑ k ∈ boxFinset d n, ((sobWeight r k : ℝ) : ℂ) * ((L u k) * conj (u k)) =
        hsInner r (L u) P := by
      rw [hsInner_trig hPt r]
      exact Finset.sum_congr rfl fun k hk => by rw [hPk k hk]
    have e2 : hsInner r (L u) P = hsInner r (L P) P + hsInner r (L (u - P)) P := by
      rw [hLu']
      exact hsInner_add_left hLPm hLRm hPm0
    have e3 : ∑ k ∈ boxFinset d n, (sobWeight r k * ((L u k) * conj (u k))).re =
        (hsInner r (L u) P).re := by
      rw [← e1, Complex.re_sum]
    rw [e3, e2, Complex.add_re]
    have h1 := hen n P hPt
    have h2 : (hsInner r (L (u - P)) P).re ≤ ‖hsInner r (L (u - P)) P‖ := Complex.re_le_norm _
    have h3 := norm_hsInner_le hLRm hPm0
    have h4 : hsNorm r (L (u - P)) ≤ K * hsNorm (r + 2) (u - P) := by
      unfold hsNorm
      calc Real.sqrt (hsNormSq r (L (u - P))) ≤ Real.sqrt ((K * hsNorm (r + 2) (u - P)) ^ 2) := by
            apply Real.sqrt_le_sqrt
            refine hLRb.trans (le_of_eq ?_)
            rw [mul_pow, ← hsNormSq_eq_norm_sq]
        _ = _ := Real.sqrt_sq (mul_nonneg hK0 (Real.sqrt_nonneg _))
    have h5 : hsNorm r P ≤ hsNorm r u := Real.sqrt_le_sqrt (hsNormSq_truncCoeff_le n hu0)
    have h6 : hsNormSq r P = ∑ k ∈ boxFinset d n, sobWeight r k * ‖u k‖ ^ 2 := by
      rw [hsNormSq_trig hPt r]
      exact Finset.sum_congr rfl fun k hk => by rw [hPk k hk]
    have h7 : hsNorm r (L (u - P)) * hsNorm r P ≤
        K * hsNorm (r + 2) (u - P) * hsNorm r u :=
      mul_le_mul h4 h5 (Real.sqrt_nonneg _) (mul_nonneg hK0 (Real.sqrt_nonneg _))
    rw [← h6]
    linarith
  -- pass to the limit
  have hsumre : Summable fun k => (sobWeight r k * ((L u k) * conj (u k))).re := by
    have := hsInner_summable hLu hu0
    exact (Complex.reCLM.summable this).congr fun k => by simp
  have t1 : Tendsto (fun n : ℕ => ∑ k ∈ boxFinset d n, (sobWeight r k * ((L u k) * conj (u k))).re)
      atTop (𝓝 (hsInner r (L u) u).re) := by
    have := tendsto_box_sum hsumre
    convert this using 2
    unfold hsInner
    rw [Complex.re_tsum (hsInner_summable hLu hu0)]
  have t2 : Tendsto (fun n : ℕ => ∑ k ∈ boxFinset d n, sobWeight r k * ‖u k‖ ^ 2) atTop
      (𝓝 (hsNormSq r u)) := tendsto_box_sum hu0
  have t3 := (truncCoeff_tendsto (r + 2) u hu).2
  have t4 : Tendsto (fun n : ℕ => Λ₀ * ∑ k ∈ boxFinset d n, sobWeight r k * ‖u k‖ ^ 2 +
      K * hsNorm (r + 2) (u - truncCoeff n u) * hsNorm r u) atTop
      (𝓝 (Λ₀ * hsNormSq r u + K * 0 * hsNorm r u)) :=
    (t2.const_mul Λ₀).add ((t3.const_mul K).mul_const _)
  rw [mul_zero, zero_mul, add_zero] at t4
  exact le_of_tendsto_of_tendsto' t1 t4 hmain


/-! ### The energy inequality at level `m` on `H^{m+2}` -/

theorem adjointData_mono {s : ℝ} {m m' : ℕ} (hmm : m' ≤ m) {R : Regime} {MB Λ VB : ℝ}
    {D : DynData d} {ν₀ T : ℝ} {μ : ℝ → Torus d → ℝ} (h : AdjointData s m R MB Λ VB D ν₀ T μ) :
    AdjointData s m' R MB Λ VB D ν₀ T μ := by
  have hle : (m' : WithTop ℕ∞) + 3 ≤ (m : WithTop ℕ∞) + 3 := by
    gcongr
  refine ⟨h.hs, h.hM, ⟨?_, ?_⟩, ⟨h.hμ.prob, fun r hr => ?_, fun r hr => ?_, h.hμ.cont⟩, h.hT,
    h.regime⟩
  · exact (h.hV.1).of_le hle
  · exact (cbNorm_mono' (by omega) _).trans h.hV.2
  · exact (h.hμ.smooth r hr).of_le hle
  · exact (cbNorm_mono' (by omega) _).trans (h.hμ.bound r hr)

theorem forwardGen_sub_adj (hd : 1 ≤ d) {s : ℝ} {m : ℕ} {R : Regime} {MB Λ VB : ℝ}
    {D : DynData d} {ν₀ T : ℝ} {μ : ℝ → Torus d → ℝ}
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T)
    {u v : Coeff d} (hu : MemHs 1 u) (hv : MemHs 1 v) :
    forwardGen D (μ r) (u - v) = forwardGen D (μ r) u - forwardGen D (μ r) v := by
  obtain ⟨K, hK0, hK⟩ := uniform_multBound hd hA
  exact forwardGen_sub_H1 D _ (hK r hr).1.memHs0 (fun j => ((hK r hr).2 j).memHs0) hu hv

theorem stab_energy (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (R : Regime) (m : ℕ)
    (MB Λ VB : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
      (_ : AdjointData s m R MB Λ VB D ν₀ T μ) (r : ℝ) (_ : r ∈ Set.Icc 0 T) (u : Coeff d),
      MemHs ((m : ℝ) + 2) u →
      (hsInner (m : ℝ) (forwardGen D (μ r) u) u).re ≤
        R.lambdaM C ν₀ (thetaOrder d s) * hsNormSq (m : ℝ) u := by
  obtain ⟨C, hC, hmain⟩ := energy_form_estimate hd s hs0 hsd m R MB Λ VB
  obtain ⟨c, hc0, hc⟩ := forwardGen_bound hd s hs0 hsd m MB Λ VB
  refine ⟨C, hC, fun D ν₀ T μ hA r hr u hu => ?_⟩
  obtain ⟨lam, q, hlq⟩ : ∃ (lam : Fin d → ℝ) (q : Fin d → Euc d),
      R.IsR2 → IsSymDiag D.M lam q := by
    by_cases hR : R.IsR2
    · obtain ⟨lam, q, h⟩ := exists_symDiag (regime_symNonpos hR hA.regime)
      exact ⟨lam, q, fun _ => h⟩
    · exact ⟨0, fun _ => 0, fun h => absurd h hR⟩
  have hreal : ∀ n, ∀ G, IsRealCoeff G → IsTrigPoly n G →
      (hsInner (m : ℝ) (forwardGen D (μ r) G) G).re ≤
        R.lambdaM C ν₀ (thetaOrder d s) * hsNormSq (m : ℝ) G := by
    intro n G hG hGt
    exact (hmain D ν₀ T μ hA lam q hlq r hr n G hG hGt).2.trans
      (energyRHS_le hd R _ D m lam q (fun hR l => (hlq hR).nonneg l) (μ r) G)
  have hρ := isRealCoeff_coeffOf_of_isCk (hA.hμ.smooth r hr)
  have hV := isRealCoeff_coeffOf_of_isCk hA.hV.1
  have htrig : ∀ n w, IsTrigPoly n w → (hsInner (m : ℝ) (forwardGen D (μ r) w) w).re ≤
      R.lambdaM C ν₀ (thetaOrder d s) * hsNormSq (m : ℝ) w := fun n w hw =>
    complex_form_w (L := forwardGen D (μ r)) (m : ℝ)
      (fun a b ha hb => forwardGen_add D (μ r) a b ha hb)
      (fun c a => forwardGen_smul D (μ r) a c)
      (fun a => forwardGen_reflConj D (μ r) hρ hV a) (hreal n) w hw
  refine energy_extend (L := forwardGen D (μ r)) (K := Real.sqrt (4 * D.invβ ^ 2 + c)) (m : ℝ)
    (Real.sqrt_nonneg _) (fun v hv => ?_) (fun v w hv hw => ?_) htrig u hu
  · obtain ⟨h1, h2⟩ := hc D hA.hs hA.hM hA.hV (μ r) (hA.hμ.prob r hr) (hA.hμ.smooth r hr)
      (hA.hμ.bound r hr) v hv
    refine ⟨h1, h2.trans (le_of_eq ?_)⟩
    rw [Real.sq_sqrt (by positivity)]
  · exact forwardGen_sub_adj hd hA hr (hv.mono (by
      have : (1 : ℝ) ≤ m + 2 := by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
      exact this)) (hw.mono (by
      have : (1 : ℝ) ≤ m + 2 := by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
      exact this))


/-! ### The energy identity for a coordinatewise primitive -/

theorem abstract_identity (r : ℝ) (T0 B G : ℝ) (hT0 : 0 ≤ T0) (w g : ℝ → Coeff d)
    (hw : ∀ σ ∈ Set.Icc 0 T0, MemHs r (w σ) ∧ hsNormSq r (w σ) ≤ B)
    (hg : ∀ σ ∈ Set.Icc 0 T0, MemHs r (g σ) ∧ hsNormSq r (g σ) ≤ G)
    (hint : ∀ k, IntegrableOn (fun σ => g σ k) (Set.Icc 0 T0))
    (heq : ∀ k, ∀ τ ∈ Set.Icc 0 T0, w τ k = ∫ σ in (0:ℝ)..τ, g σ k) :
    (∀ τ ∈ Set.Icc 0 T0, IntervalIntegrable (fun σ => 2 * (hsInner r (g σ) (w σ)).re) volume 0 τ) ∧
      ∀ τ ∈ Set.Icc 0 T0, hsNormSq r (w τ) =
        ∫ σ in (0:ℝ)..τ, 2 * (hsInner r (g σ) (w σ)).re := by
  set I : Set ℝ := Set.Icc 0 T0 with hI
  have hmem0 : (0 : ℝ) ∈ I := ⟨le_rfl, hT0⟩
  have hzk : ∀ k, ContinuousOn (fun σ => w σ k) I := by
    intro k
    have h := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := T0) (μ := volume)
      (f := fun σ => g σ k) (by rw [Set.uIcc_of_le hT0]; exact hint k)
    rw [Set.uIcc_of_le hT0] at h
    exact h.congr fun τ hτ => heq k τ hτ
  have hgint : ∀ k, ∀ τ ∈ I, IntervalIntegrable (fun σ => g σ k) volume 0 τ := by
    intro k τ hτ
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
    exact (hint k).mono_set (Set.Icc_subset_Icc_right hτ.2)
  have hmode : ∀ k, ∀ τ ∈ I, ‖w τ k‖ ^ 2 =
      ∫ σ in (0:ℝ)..τ, 2 * (g σ k * conj (w σ k)).re := by
    intro k τ hτ
    rw [heq k τ hτ, norm_sq_primitive (fun σ => g σ k) τ (hgint k τ hτ)]
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    have hσI : σ ∈ I := Set.uIcc_subset_Icc hmem0 hτ hσ
    rw [← heq k σ hσI]
  have hY1 : ∀ k, ∀ τ ∈ I, IntervalIntegrable
      (fun σ => 2 * (g σ k * conj (w σ k)).re) volume 0 τ := by
    intro k τ hτ
    have hsub : Set.uIcc 0 τ ⊆ I := Set.uIcc_subset_Icc hmem0 hτ
    have hc : ContinuousOn (fun σ => conj (w σ k)) (Set.uIcc 0 τ) :=
      (Complex.continuous_conj.comp_continuousOn (hzk k)).mono hsub
    have h1 := (hgint k τ hτ).mul_continuousOn hc
    have h2 : IntervalIntegrable (fun σ => (g σ k * conj (w σ k)).re) volume 0 τ :=
      intervalIntegrable_iff.2 (Complex.reCLM.integrable_comp (intervalIntegrable_iff.1 h1))
    exact h2.const_mul 2
  -- the finite sums
  set Yn : ℕ → ℝ → ℝ := fun n σ => ∑ k ∈ boxFinset d n,
    sobWeight r k * (2 * (g σ k * conj (w σ k)).re) with hYn
  set Sn : ℕ → ℝ → ℝ := fun n τ => ∑ k ∈ boxFinset d n, sobWeight r k * ‖w τ k‖ ^ 2 with hSn
  have hSY : ∀ n, ∀ τ ∈ I, Sn n τ = ∫ σ in (0:ℝ)..τ, Yn n σ := by
    intro n τ hτ
    simp only [hSn, hYn]
    rw [intervalIntegral.integral_finsetSum fun k _ => (hY1 k τ hτ).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul, hmode k τ hτ]
  have hYint : ∀ n, ∀ τ ∈ I, IntervalIntegrable (Yn n) volume 0 τ := by
    intro n τ hτ
    have := IntervalIntegrable.sum (boxFinset d n) fun k _ => (hY1 k τ hτ).const_mul (sobWeight r k)
    convert this using 1
    funext σ
    simp [hYn, Finset.sum_apply]
  -- the limit function
  set Y : ℝ → ℝ := fun σ => 2 * (hsInner r (g σ) (w σ)).re with hY
  have hsumre : ∀ σ ∈ I, Summable fun k => sobWeight r k * (2 * (g σ k * conj (w σ k)).re) := by
    intro σ hσ
    have := (Complex.reCLM.summable (hsInner_summable (hg σ hσ).1 (hw σ hσ).1)).mul_left 2
    refine this.congr fun k => ?_
    simp
    ring
  have hlim : ∀ σ ∈ I, Tendsto (fun n => Yn n σ) atTop (𝓝 (Y σ)) := by
    intro σ hσ
    have := tendsto_box_sum (hsumre σ hσ)
    convert this using 2
    simp only [hY, hsInner]
    rw [Complex.re_tsum (hsInner_summable (hg σ hσ).1 (hw σ hσ).1), ← tsum_mul_left]
    exact tsum_congr fun k => by simp; ring
  have hbd : ∀ n, ∀ σ ∈ I, ‖Yn n σ‖ ≤ 2 * (Real.sqrt G * Real.sqrt B) := by
    intro n σ hσ
    obtain ⟨hcs1, hcs2⟩ := weighted_cs (hg σ hσ).1 (hw σ hσ).1
    have h1 : ‖Yn n σ‖ ≤ ∑ k ∈ boxFinset d n, 2 * (sobWeight r k * (‖g σ k‖ * ‖w σ k‖)) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_mul, Real.norm_of_nonneg (sobWeight_pos r k).le, Real.norm_eq_abs]
      have : |2 * (g σ k * conj (w σ k)).re| ≤ 2 * (‖g σ k‖ * ‖w σ k‖) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
        rw [norm_mul, Complex.norm_conj]
      calc sobWeight r k * |2 * (g σ k * conj (w σ k)).re|
          ≤ sobWeight r k * (2 * (‖g σ k‖ * ‖w σ k‖)) :=
            mul_le_mul_of_nonneg_left this (sobWeight_pos r k).le
        _ = _ := by ring
    refine h1.trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (Summable.sum_le_tsum _ (fun k _ => mul_nonneg (sobWeight_pos r k).le
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hcs1).trans (hcs2.trans ?_)
    exact mul_le_mul (Real.sqrt_le_sqrt (hg σ hσ).2) (Real.sqrt_le_sqrt (hw σ hσ).2)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hmeasYk : ∀ k, AEStronglyMeasurable
      (fun σ => sobWeight r k * (2 * (g σ k * conj (w σ k)).re)) (volume.restrict I) := by
    intro k
    have h1 : AEStronglyMeasurable (fun σ => g σ k) (volume.restrict I) := (hint k).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun σ => conj (w σ k)) (volume.restrict I) :=
      (Complex.continuous_conj.comp_continuousOn (hzk k)).aestronglyMeasurable measurableSet_Icc
    exact (Complex.continuous_re.comp_aestronglyMeasurable (h1.mul h2)).const_mul 2 |>.const_mul _
  have hmeasYn : ∀ n, AEStronglyMeasurable (Yn n) (volume.restrict I) := by
    intro n
    have := Finset.aestronglyMeasurable_fun_sum (boxFinset d n) fun k _ => hmeasYk k
    convert this using 1
  have hmeasY : AEStronglyMeasurable Y (volume.restrict I) := by
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop) (f := Yn) hmeasYn ?_
    exact (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hlim)
  have hYbd : ∀ σ ∈ I, ‖Y σ‖ ≤ 2 * (Real.sqrt G * Real.sqrt B) := fun σ hσ =>
    le_of_tendsto' (hlim σ hσ).norm fun n => hbd n σ hσ
  have hYii : ∀ τ ∈ I, IntervalIntegrable Y volume 0 τ := fun τ hτ => ii_of_bdd hmeasY hYbd hτ
  refine ⟨hYii, fun τ hτ => ?_⟩
  have hsubIoc : Set.uIoc 0 τ ⊆ I := by
    rw [Set.uIoc_of_le hτ.1]; exact fun x hx => ⟨hx.1.le, hx.2.trans hτ.2⟩
  have ta : Tendsto (fun n => Sn n τ) atTop (𝓝 (hsNormSq r (w τ))) := tendsto_box_sum (hw τ hτ).1
  have tb : Tendsto (fun n => ∫ σ in (0:ℝ)..τ, Yn n σ) atTop (𝓝 (∫ σ in (0:ℝ)..τ, Y σ)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => 2 * (Real.sqrt G * Real.sqrt B)) ?_ ?_ intervalIntegrable_const ?_
    · exact Filter.Eventually.of_forall fun n => (hmeasYn n).mono_set hsubIoc
    · exact Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun σ hσ =>
        hbd n σ (hsubIoc hσ)
    · exact Filter.Eventually.of_forall fun σ hσ => hlim σ (hsubIoc hσ)
  have tc : Tendsto (fun n => Sn n τ) atTop (𝓝 (∫ σ in (0:ℝ)..τ, Y σ)) :=
    tb.congr fun n => (hSY n τ hτ).symm
  exact tendsto_nhds_unique ta tc


/-! ### Linear Gronwall for a primitive -/

theorem gronwall_prim (Y b : ℝ → ℝ) (a T0 : ℝ) (hT0 : 0 ≤ T0)
    (hY : IntervalIntegrable Y volume 0 T0) (hb : IntervalIntegrable b volume 0 T0)
    (hle : ∀ σ ∈ Set.Icc 0 T0, Y σ ≤ a * (∫ s in (0:ℝ)..σ, Y s) + b σ) :
    ∫ σ in (0:ℝ)..T0, Y σ ≤ ∫ σ in (0:ℝ)..T0, Real.exp (a * (T0 - σ)) * b σ := by
  set f : ℝ → ℝ := fun x => ∫ s in (0:ℝ)..x, Y s with hf
  set g : ℝ → ℝ := fun x => Real.exp (-a * x) with hg
  have hac : AbsolutelyContinuousOnInterval f 0 T0 :=
    hY.absolutelyContinuousOnInterval_intervalIntegral (c := 0) Set.left_mem_uIcc
  have hgc : ContDiff ℝ 1 g := by
    unfold g
    exact (Real.contDiff_exp).comp (contDiff_const.mul contDiff_id)
  have hgac : AbsolutelyContinuousOnInterval g 0 T0 := hgc.contDiffOn.absolutelyContinuousOnInterval
  have hgd : ∀ x, HasDerivAt g (-a * g x) x := by
    intro x
    have := ((hasDerivAt_id x).const_mul (-a)).exp
    simpa [hg, mul_comm] using this
  have h1 := hac.integral_deriv_mul_eq_sub hgac
  have hf0 : f 0 = 0 := by simp [hf]
  have hfc : ContinuousOn f (Set.uIcc 0 T0) :=
    intervalIntegral.continuousOn_primitive_interval' hY (a := 0) Set.left_mem_uIcc
  have hgcont : Continuous g := hgc.continuous
  have h2 : ∫ x in (0:ℝ)..T0, (deriv f x * g x + f x * deriv g x) =
      ∫ x in (0:ℝ)..T0, (Y x * g x + f x * (-a * g x)) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hY.ae_hasDerivAt_integral] with x hx hxI
    have hxI' : x ∈ Set.uIcc 0 T0 := Set.uIoc_subset_uIcc hxI
    have := (hx hxI' 0 Set.left_mem_uIcc).deriv
    simp only [hf] at this ⊢
    rw [this, (hgd x).deriv]
  rw [h2, hf0, zero_mul, sub_zero] at h1
  -- the right-hand side
  have hint1 : IntervalIntegrable (fun x => Y x * g x) volume 0 T0 :=
    hY.mul_continuousOn hgcont.continuousOn
  have hint2 : IntervalIntegrable (fun x => f x * (-a * g x)) volume 0 T0 :=
    (hfc.mul (continuousOn_const.mul hgcont.continuousOn)).intervalIntegrable
  have hint3 : IntervalIntegrable (fun x => b x * g x) volume 0 T0 :=
    hb.mul_continuousOn hgcont.continuousOn
  have h3 : ∫ x in (0:ℝ)..T0, (Y x * g x + f x * (-a * g x)) ≤ ∫ x in (0:ℝ)..T0, b x * g x := by
    refine intervalIntegral.integral_mono_on hT0 (hint1.add hint2) hint3 fun x hx => ?_
    have := hle x hx
    have hgpos : 0 < g x := Real.exp_pos _
    simp only [hf]
    nlinarith [mul_le_mul_of_nonneg_right this hgpos.le]
  rw [h1] at h3
  have hfT : f T0 = ∫ σ in (0:ℝ)..T0, Y σ := rfl
  have e : ∫ σ in (0:ℝ)..T0, Real.exp (a * (T0 - σ)) * b σ =
      Real.exp (a * T0) * ∫ σ in (0:ℝ)..T0, b σ * g σ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun σ _ => ?_
    simp only [hg]
    rw [show a * (T0 - σ) = a * T0 + -a * σ by ring, Real.exp_add]
    ring
  rw [e, ← hfT]
  have hgT : g T0 = Real.exp (-a * T0) := rfl
  have hpos : 0 < Real.exp (a * T0) := Real.exp_pos _
  have hprod : Real.exp (a * T0) * Real.exp (-a * T0) = 1 := by
    rw [← Real.exp_add]; simp
  calc f T0 = Real.exp (a * T0) * (f T0 * g T0) := by
        rw [hgT]; calc f T0 = f T0 * (Real.exp (a * T0) * Real.exp (-a * T0)) := by rw [hprod, mul_one]
          _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 hpos.le


/-! ### Two abstract steps of the core estimate -/

theorem pointwise_ineq {r : ℝ} (g Lw S w : Coeff d) (hgs : g = Lw + S) (hLm : MemHs r Lw)
    (hSm : MemHs r S) (hwm : MemHs r w) {Λm y τe : ℝ} (hpos : 0 < τe) (_hy0 : 0 ≤ y)
    (hen : (hsInner r Lw w).re ≤ Λm * hsNormSq r w) (hSn : hsNorm r S ≤ y) :
    2 * (hsInner r g w).re ≤ (2 * Λm + 1 / τe) * hsNormSq r w + τe * y ^ 2 := by
  have hx0 : 0 ≤ hsNorm r w := Real.sqrt_nonneg _
  have hxsq : hsNorm r w ^ 2 = hsNormSq r w := (hsNormSq_eq_norm_sq _).symm
  have h1 : (hsInner r S w).re ≤ y * hsNorm r w :=
    (Complex.re_le_norm _).trans ((norm_hsInner_le hSm hwm).trans
      (mul_le_mul_of_nonneg_right hSn hx0))
  have h2 : 2 * hsNorm r w * y ≤ hsNorm r w ^ 2 / τe + τe * y ^ 2 := by
    rw [div_add' _ _ _ hpos.ne', le_div_iff₀ hpos]
    nlinarith [sq_nonneg (hsNorm r w - τe * y)]
  have h3 : hsNorm r w ^ 2 / τe = (1 / τe) * hsNormSq r w := by rw [hxsq]; ring
  rw [hgs, hsInner_add_left hLm hSm hwm, Complex.add_re]
  nlinarith [h1, h2, h3]

theorem gronwall_final (Y : ℝ → ℝ) (Λm Λ₂ Λ' ς τe φ : ℝ) (hpos : 0 < τe) (hΛm : Λm ≤ Λ')
    (hΛ₂ : Λ₂ ≤ Λ') (hii : IntervalIntegrable Y volume 0 τe)
    (hle : ∀ σ ∈ Set.Icc 0 τe, Y σ ≤ (2 * Λm + 1 / τe) * (∫ s in (0:ℝ)..σ, Y s) +
      τe * ς ^ 2 * Real.exp (2 * Λ₂ * σ))
    (hφ : φ = ∫ s in (0:ℝ)..τe, Y s) :
    φ ≤ τe * (τe * ς ^ 2 * Real.exp 1 * Real.exp (2 * Λ' * τe)) := by
  have hbf_ii : IntervalIntegrable (fun σ => τe * ς ^ 2 * Real.exp (2 * Λ₂ * σ)) volume 0 τe := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hgr := gronwall_prim Y _ (2 * Λm + 1 / τe) τe hpos.le hii hbf_ii hle
  rw [hφ]
  refine hgr.trans ?_
  have hcont : Continuous fun σ : ℝ => Real.exp ((2 * Λm + 1 / τe) * (τe - σ)) *
      (τe * ς ^ 2 * Real.exp (2 * Λ₂ * σ)) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).mul
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
  calc ∫ σ in (0:ℝ)..τe, Real.exp ((2 * Λm + 1 / τe) * (τe - σ)) *
        (τe * ς ^ 2 * Real.exp (2 * Λ₂ * σ))
      ≤ ∫ σ in (0:ℝ)..τe, (τe * ς ^ 2 * Real.exp 1 * Real.exp (2 * Λ' * τe)) := by
        refine intervalIntegral.integral_mono_on hpos.le (hcont.intervalIntegrable _ _)
          intervalIntegrable_const fun σ hσ => ?_
        have h1 : (τe - σ) / τe ≤ 1 := by
          rw [div_le_one hpos]; linarith [hσ.1]
        have h2 : (2 * Λm + 1 / τe) * (τe - σ) + 2 * Λ₂ * σ ≤ 1 + 2 * Λ' * τe := by
          have e1 : (2 * Λm + 1 / τe) * (τe - σ) = 2 * Λm * (τe - σ) + (τe - σ) / τe := by
            field_simp
          have e2 : 2 * Λm * (τe - σ) ≤ 2 * Λ' * (τe - σ) :=
            mul_le_mul_of_nonneg_right (by linarith) (by linarith [hσ.2])
          have e3 : 2 * Λ₂ * σ ≤ 2 * Λ' * σ :=
            mul_le_mul_of_nonneg_right (by linarith) hσ.1
          nlinarith [e1, e2, e3, h1]
        have h3 : Real.exp ((2 * Λm + 1 / τe) * (τe - σ)) * Real.exp (2 * Λ₂ * σ) ≤
            Real.exp 1 * Real.exp (2 * Λ' * τe) := by
          rw [← Real.exp_add, ← Real.exp_add]
          exact Real.exp_le_exp.2 h2
        have h4 : 0 ≤ τe * ς ^ 2 := by positivity
        calc Real.exp ((2 * Λm + 1 / τe) * (τe - σ)) * (τe * ς ^ 2 * Real.exp (2 * Λ₂ * σ))
            = (τe * ς ^ 2) * (Real.exp ((2 * Λm + 1 / τe) * (τe - σ)) * Real.exp (2 * Λ₂ * σ)) := by
              ring
          _ ≤ (τe * ς ^ 2) * (Real.exp 1 * Real.exp (2 * Λ' * τe)) :=
              mul_le_mul_of_nonneg_left h3 h4
          _ = _ := by ring
    _ = _ := by simp; ring

/-! ### The core estimate -/

theorem lambdaM_mono {R : Regime} {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {invβ ν₀ T : ℝ}
    {μ : ℝ → Torus d → ℝ} (hR : R.Holds d s M invβ ν₀ T μ) {C C' : ℝ} (h : C ≤ C') (θ : ℝ) :
    R.lambdaM C ν₀ θ ≤ R.lambdaM C' ν₀ θ := by
  cases R with
  | R3 =>
    obtain ⟨-, hν, -⟩ := hR
    unfold Regime.lambdaM
    have := Real.rpow_nonneg hν.le (-(θ / (2 - θ)))
    exact mul_le_mul_of_nonneg_right h (by linarith)
  | R1 => exact h
  | R2a => exact h
  | R2b _ => exact h
  | R2c => exact h

set_option maxHeartbeats 1000000 in
theorem stability_core (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (R : Regime)
    (MB Λ VB : ℝ) (C₂ : ℝ) (hC₂ : 0 < C₂) :
    ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧
      ∀ (D₁ D₂ : DynData d) (ν₀ T : ℝ) (μ₁ μ₂ : ℝ → Torus d → ℝ)
        (_ : AdjointData s (m + 2) R MB Λ VB D₁ ν₀ T μ₁)
        (_ : AdjointData s (m + 2) R MB Λ VB D₂ ν₀ T μ₂) (_ : D₁.M = D₂.M) (_ : D₁.V = D₂.V)
        (δ : ℝ) (_ : ∀ r ∈ Set.Icc 0 T, Torus.cbNorm (m + 2) (μ₁ r - μ₂ r) ≤ δ)
        (φc : Coeff d) (_ : MemHs ((m : ℝ) + 2) φc) (t : ℝ) (_ : t ∈ Set.Ioc 0 T)
        (F₁ F₂ : ℝ → Coeff d)
        (_ : IsForwardSolution D₁ μ₁ t φc F₁) (_ : WeakContinuousInHs ((m : ℝ) + 2) F₁ t)
        (_ : IsForwardSolution D₂ μ₂ t φc F₂) (_ : WeakContinuousInHs ((m : ℝ) + 2) F₂ t)
        (_ : ∀ τ ∈ Set.Icc 0 t, hsNorm ((m : ℝ) + 2) (F₁ τ) ≤
          Real.exp (R.lambdaM C₂ ν₀ (thetaOrder d s) * τ) * hsNorm ((m : ℝ) + 2) φc)
        (_ : ∀ τ ∈ Set.Icc 0 t, hsNorm ((m : ℝ) + 2) (F₂ τ) ≤
          Real.exp (R.lambdaM C₂ ν₀ (thetaOrder d s) * τ) * hsNorm ((m : ℝ) + 2) φc)
        (τe : ℝ) (_ : 0 ≤ τe) (_ : τe ≤ t),
        hsNorm (m : ℝ) (F₁ τe - F₂ τe) ≤
          C * τe * Real.exp (R.lambdaM C' ν₀ (thetaOrder d s) * τe) *
            (|D₁.invβ - D₂.invβ| + δ) * hsNorm ((m : ℝ) + 2) φc := by
  obtain ⟨Cm, hCm, hen⟩ := stab_energy hd s hs0 hsd R m MB Λ VB
  obtain ⟨Kd, hKd0, hKd⟩ := forwardGen_diff_bound hd s hs0 hsd m MB Λ
  obtain ⟨c, hc0, hc⟩ := forwardGen_bound hd s hs0 hsd m MB Λ VB
  refine ⟨Real.sqrt (Real.exp 1) * Kd + 1, max C₂ Cm, by positivity, lt_max_of_lt_left hC₂, ?_⟩
  intro D₁ D₂ ν₀ T μ₁ μ₂ hA₁ hA₂ hM hV δ hδ φc hφ t ht F₁ F₂ h₁ w₁ h₂ w₂ b₁ b₂ τe hτe0 hτet
  have ht0 : 0 < t := ht.1
  have htT : t ≤ T := ht.2
  have hF0 : ∀ (D : DynData d) (μ : ℝ → Torus d → ℝ) (F : ℝ → Coeff d),
      IsForwardSolution D μ t φc F → F 0 = φc := fun D μ F hF => funext fun k => by
    rw [hF.eq k 0 ⟨le_rfl, ht0.le⟩]; simp
  rcases hτe0.eq_or_lt with h0 | hpos
  · subst h0
    rw [hF0 D₁ μ₁ F₁ h₁, hF0 D₂ μ₂ F₂ h₂, sub_self]
    simp [hsNorm, hsNormSq]
  have hA₁m := adjointData_mono (by omega : m ≤ m + 2) hA₁
  have hA₂m := adjointData_mono (by omega : m ≤ m + 2) hA₂
  have hs₁ : D₁.s = s := hA₁.hs
  have hs₂ : D₂.s = s := hA₂.hs
  set θ := thetaOrder d s with hθ
  set Λ₂ := R.lambdaM C₂ ν₀ θ with hΛ₂
  set Λm := R.lambdaM Cm ν₀ θ with hΛm
  set Λ' := R.lambdaM (max C₂ Cm) ν₀ θ with hΛ'
  have hΛ₂le : Λ₂ ≤ Λ' := lambdaM_mono hA₁.regime (le_max_left _ _) θ
  have hΛmle : Λm ≤ Λ' := lambdaM_mono hA₁.regime (le_max_right _ _) θ
  set N := hsNorm ((m : ℝ) + 2) φc with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hδ0 : 0 ≤ δ := (cbNorm_nonneg _ _).trans (hδ 0 ⟨le_rfl, ht0.le.trans htT⟩)
  set Q : ℝ := |D₁.invβ - D₂.invβ| + δ with hQdef
  have hQ0 : 0 ≤ Q := by positivity
  set ς : ℝ := Kd * Q * N with hς
  have hς0 : 0 ≤ ς := by positivity
  have hIcc : ∀ σ ∈ Set.Icc 0 τe, t - σ ∈ Set.Icc (0 : ℝ) T := fun σ hσ =>
    ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hσt : ∀ σ ∈ Set.Icc 0 τe, σ ∈ Set.Icc 0 t := fun σ hσ => ⟨hσ.1, hσ.2.trans hτet⟩
  have hm2 : (1 : ℝ) ≤ (m : ℝ) + 2 := by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
  have hm0 : (m : ℝ) ≤ (m : ℝ) + 2 := by linarith
  have hF1 : ∀ σ ∈ Set.Icc 0 t, MemHs ((m : ℝ) + 2) (F₁ σ) := w₁.1
  have hF2 : ∀ σ ∈ Set.Icc 0 t, MemHs ((m : ℝ) + 2) (F₂ σ) := w₂.1
  -- a priori bounds
  set Eb : ℝ := Real.exp (|Λ₂| * t) * N with hEb
  have hEb0 : 0 ≤ Eb := by positivity
  have hexp : ∀ σ ∈ Set.Icc 0 t, Real.exp (Λ₂ * σ) ≤ Real.exp (|Λ₂| * t) := fun σ hσ =>
    Real.exp_le_exp.2 ((mul_le_mul_of_nonneg_right (le_abs_self _) hσ.1).trans
      (mul_le_mul_of_nonneg_left hσ.2 (abs_nonneg _)))
  have hFb : ∀ (F : ℝ → Coeff d), (∀ τ ∈ Set.Icc 0 t, hsNorm ((m : ℝ) + 2) (F τ) ≤
      Real.exp (Λ₂ * τ) * N) → ∀ σ ∈ Set.Icc 0 t, hsNormSq ((m : ℝ) + 2) (F σ) ≤ Eb ^ 2 := by
    intro F hF σ hσ
    rw [hsNormSq_eq_norm_sq]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) ((hF σ hσ).trans
      (mul_le_mul_of_nonneg_right (hexp σ hσ) hN0)) 2
  have hFb1 := hFb F₁ b₁
  have hFb2 := hFb F₂ b₂
  -- the difference and the source
  set w : ℝ → Coeff d := fun σ => F₁ σ - F₂ σ with hw
  set g : ℝ → Coeff d := fun σ => forwardGen D₁ (μ₁ (t - σ)) (F₁ σ) -
    forwardGen D₂ (μ₂ (t - σ)) (F₂ σ) with hg
  set S : ℝ → Coeff d := fun σ => forwardGen D₁ (μ₁ (t - σ)) (F₂ σ) -
    forwardGen D₂ (μ₂ (t - σ)) (F₂ σ) with hS
  have hwm2 : ∀ σ ∈ Set.Icc 0 τe, MemHs ((m : ℝ) + 2) (w σ) ∧
      hsNormSq ((m : ℝ) + 2) (w σ) ≤ 4 * Eb ^ 2 := by
    intro σ hσ
    have h1 := hF1 σ (hσt σ hσ)
    have h2 := hF2 σ (hσt σ hσ)
    refine ⟨memHs_sub h1 h2, (hsNormSq_sub_le h1 h2).trans ?_⟩
    nlinarith [hFb1 σ (hσt σ hσ), hFb2 σ (hσt σ hσ)]
  have hwm : ∀ σ ∈ Set.Icc 0 τe, MemHs (m : ℝ) (w σ) ∧ hsNormSq (m : ℝ) (w σ) ≤ 4 * Eb ^ 2 :=
    fun σ hσ => ⟨(hwm2 σ hσ).1.mono hm0,
      (hsNormSq_mono hm0 (hwm2 σ hσ).1).trans (hwm2 σ hσ).2⟩
  -- the generators applied to `F_i`
  have hL1 : ∀ σ ∈ Set.Icc 0 τe, ∀ u : Coeff d, MemHs ((m : ℝ) + 2) u →
      MemHs (m : ℝ) (forwardGen D₁ (μ₁ (t - σ)) u) ∧
      hsNormSq (m : ℝ) (forwardGen D₁ (μ₁ (t - σ)) u) ≤
        (4 * D₁.invβ ^ 2 + c) * hsNormSq ((m : ℝ) + 2) u := fun σ hσ u hu =>
    hc D₁ hs₁ hA₁m.hM hA₁m.hV (μ₁ (t - σ)) (hA₁m.hμ.prob _ (hIcc σ hσ))
      (hA₁m.hμ.smooth _ (hIcc σ hσ)) (hA₁m.hμ.bound _ (hIcc σ hσ)) u hu
  have hL2 : ∀ σ ∈ Set.Icc 0 τe, ∀ u : Coeff d, MemHs ((m : ℝ) + 2) u →
      MemHs (m : ℝ) (forwardGen D₂ (μ₂ (t - σ)) u) ∧
      hsNormSq (m : ℝ) (forwardGen D₂ (μ₂ (t - σ)) u) ≤
        (4 * D₂.invβ ^ 2 + c) * hsNormSq ((m : ℝ) + 2) u := fun σ hσ u hu =>
    hc D₂ hs₂ (hM ▸ hA₁m.hM) hA₂m.hV (μ₂ (t - σ)) (hA₂m.hμ.prob _ (hIcc σ hσ))
      (hA₂m.hμ.smooth _ (hIcc σ hσ)) (hA₂m.hμ.bound _ (hIcc σ hσ)) u hu
  set G : ℝ := 2 * ((4 * D₁.invβ ^ 2 + c) * Eb ^ 2) + 2 * ((4 * D₂.invβ ^ 2 + c) * Eb ^ 2) with hG
  have hgm : ∀ σ ∈ Set.Icc 0 τe, MemHs (m : ℝ) (g σ) ∧ hsNormSq (m : ℝ) (g σ) ≤ G := by
    intro σ hσ
    obtain ⟨a1, a2⟩ := hL1 σ hσ (F₁ σ) (hF1 σ (hσt σ hσ))
    obtain ⟨b1, b2⟩ := hL2 σ hσ (F₂ σ) (hF2 σ (hσt σ hσ))
    refine ⟨memHs_sub a1 b1, (hsNormSq_sub_le a1 b1).trans ?_⟩
    have e1 := mul_le_mul_of_nonneg_left (hFb1 σ (hσt σ hσ)) (by positivity : 0 ≤ 4 * D₁.invβ ^ 2 + c)
    have e2 := mul_le_mul_of_nonneg_left (hFb2 σ (hσt σ hσ)) (by positivity : 0 ≤ 4 * D₂.invβ ^ 2 + c)
    rw [hG]
    nlinarith [a2.trans e1, b2.trans e2]
  have hint : ∀ k, IntegrableOn (fun σ => g σ k) (Set.Icc 0 τe) := fun k =>
    ((h₁.integrable k).sub (h₂.integrable k)).mono_set (Set.Icc_subset_Icc_right hτet)
  have heq : ∀ k, ∀ τ ∈ Set.Icc 0 τe, w τ k = ∫ σ in (0:ℝ)..τ, g σ k := by
    intro k τ hτ
    have hτt : τ ∈ Set.Icc 0 t := hσt τ hτ
    have hi : ∀ F : ℝ → Coeff d, ∀ (D : DynData d) (μ : ℝ → Torus d → ℝ),
        (∀ k, IntegrableOn (fun σ => forwardGen D (μ (t - σ)) (F σ) k) (Set.Icc 0 t)) →
        IntervalIntegrable (fun σ => forwardGen D (μ (t - σ)) (F σ) k) volume 0 τ :=
      fun F D μ hF => by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
        exact (hF k).mono_set (Set.Icc_subset_Icc_right hτt.2)
    show F₁ τ k - F₂ τ k = ∫ σ in (0:ℝ)..τ, (forwardGen D₁ (μ₁ (t - σ)) (F₁ σ) k -
      forwardGen D₂ (μ₂ (t - σ)) (F₂ σ) k)
    rw [h₁.eq k τ hτt, h₂.eq k τ hτt, intervalIntegral.integral_sub (hi F₁ D₁ μ₁ h₁.integrable)
      (hi F₂ D₂ μ₂ h₂.integrable)]
    ring
  obtain ⟨hii, hid⟩ := abstract_identity (m : ℝ) τe (4 * Eb ^ 2) G hτe0 w g
    (fun σ hσ => ⟨(hwm σ hσ).1, (hwm σ hσ).2⟩) hgm hint heq
  set Y : ℝ → ℝ := fun σ => 2 * (hsInner (m : ℝ) (g σ) (w σ)).re with hYdef
  obtain ⟨K₁, -, hK₁⟩ := uniform_multBound hd hA₁m
  obtain ⟨K₂, -, hK₂⟩ := uniform_multBound hd hA₂m
  -- the pointwise differential inequality
  have hle : ∀ σ ∈ Set.Icc 0 τe, Y σ ≤ (2 * Λm + 1 / τe) * (∫ s in (0:ℝ)..σ, Y s) +
      τe * ς ^ 2 * Real.exp (2 * Λ₂ * σ) := by
    intro σ hσ
    rw [← hid σ hσ]
    have hgs : g σ = forwardGen D₁ (μ₁ (t - σ)) (w σ) + S σ := by
      have := forwardGen_sub_adj hd hA₁m (hIcc σ hσ) ((hF1 σ (hσt σ hσ)).mono hm2)
        ((hF2 σ (hσt σ hσ)).mono hm2)
      simp only [hg, hS, hw]
      rw [this]; abel
    obtain ⟨hLm, -⟩ := hL1 σ hσ (w σ) (hwm2 σ hσ).1
    obtain ⟨hSm, hSb⟩ := hKd D₁ D₂ hs₁ hs₂ hM hA₁m.hM hV (μ₁ (t - σ)) (μ₂ (t - σ))
      (hA₁m.hμ.prob _ (hIcc σ hσ)) (hA₂m.hμ.prob _ (hIcc σ hσ))
      (hA₁m.hμ.smooth _ (hIcc σ hσ)) (hA₂m.hμ.smooth _ (hIcc σ hσ))
      (hA₁m.hμ.bound _ (hIcc σ hσ)) (hA₂m.hμ.bound _ (hIcc σ hσ))
      (hK₁ _ (hIcc σ hσ)).1.memHs0 (hK₂ _ (hIcc σ hσ)).1.memHs0
      (fun j => ((hK₁ _ (hIcc σ hσ)).2 j).memHs0) (fun j => ((hK₂ _ (hIcc σ hσ)).2 j).memHs0)
      δ (hδ _ (hIcc σ hσ)) (F₂ σ) (hF2 σ (hσt σ hσ))
    have hSn : hsNorm (m : ℝ) (S σ) ≤ ς * Real.exp (Λ₂ * σ) := by
      have h1 : hsNorm (m : ℝ) (S σ) ≤ Kd * Q * hsNorm ((m : ℝ) + 2) (F₂ σ) := by
        unfold hsNorm
        calc Real.sqrt (hsNormSq (m : ℝ) (S σ))
            ≤ Real.sqrt ((Kd * Q) ^ 2 * hsNormSq ((m : ℝ) + 2) (F₂ σ)) := Real.sqrt_le_sqrt hSb
          _ = _ := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
      refine h1.trans ?_
      calc Kd * Q * hsNorm ((m : ℝ) + 2) (F₂ σ) ≤ Kd * Q * (Real.exp (Λ₂ * σ) * N) :=
            mul_le_mul_of_nonneg_left (b₂ σ (hσt σ hσ)) (by positivity)
        _ = _ := by rw [hς]; ring
    have hen' := hen D₁ ν₀ T μ₁ hA₁m (t - σ) (hIcc σ hσ) (w σ) (hwm2 σ hσ).1
    have hY : Y σ = 2 * (hsInner (m : ℝ) (forwardGen D₁ (μ₁ (t - σ)) (w σ)) (w σ)).re +
        2 * (hsInner (m : ℝ) (S σ) (w σ)).re := by
      simp only [hYdef]
      rw [hgs, hsInner_add_left hLm hSm (hwm σ hσ).1, Complex.add_re]; ring
    have hy0 : 0 ≤ ς * Real.exp (Λ₂ * σ) := by positivity
    have hpi := pointwise_ineq (g σ) _ (S σ) (w σ) hgs hLm hSm (hwm σ hσ).1 (Λm := Λm) hpos hy0
      hen' hSn
    have hy2 : (ς * Real.exp (Λ₂ * σ)) ^ 2 = ς ^ 2 * Real.exp (2 * Λ₂ * σ) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast; ring
    rw [hy2] at hpi
    rw [← mul_assoc] at hpi
    exact hpi
  have hfin := gronwall_final Y Λm Λ₂ Λ' ς τe (hsNormSq (m : ℝ) (w τe)) hpos hΛmle hΛ₂le
    (hii τe ⟨hτe0, le_rfl⟩) hle (hid τe ⟨hτe0, le_rfl⟩)
  have hX0 : 0 ≤ τe * ς * Real.sqrt (Real.exp 1) * Real.exp (Λ' * τe) := by positivity
  have hXsq : (τe * ς * Real.sqrt (Real.exp 1) * Real.exp (Λ' * τe)) ^ 2 =
      τe * (τe * ς ^ 2 * Real.exp 1 * Real.exp (2 * Λ' * τe)) := by
    have e1 : Real.exp (Λ' * τe) ^ 2 = Real.exp (2 * Λ' * τe) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e2 : Real.sqrt (Real.exp 1) ^ 2 = Real.exp 1 := Real.sq_sqrt (Real.exp_pos 1).le
    calc (τe * ς * Real.sqrt (Real.exp 1) * Real.exp (Λ' * τe)) ^ 2
        = τe ^ 2 * ς ^ 2 * Real.sqrt (Real.exp 1) ^ 2 * Real.exp (Λ' * τe) ^ 2 := by ring
      _ = _ := by rw [e1, e2]; ring
  have hnorm : hsNorm (m : ℝ) (F₁ τe - F₂ τe) ≤
      τe * ς * Real.sqrt (Real.exp 1) * Real.exp (Λ' * τe) := by
    unfold hsNorm
    calc Real.sqrt (hsNormSq (m : ℝ) (F₁ τe - F₂ τe))
        ≤ Real.sqrt ((τe * ς * Real.sqrt (Real.exp 1) * Real.exp (Λ' * τe)) ^ 2) :=
          Real.sqrt_le_sqrt (hXsq ▸ hfin)
      _ = _ := Real.sqrt_sq hX0
  refine hnorm.trans ?_
  have hq : 0 ≤ τe * Real.exp (Λ' * τe) * Q * N := by positivity
  have hKe : 0 ≤ Kd * Real.sqrt (Real.exp 1) := by positivity
  rw [hς]
  nlinarith [mul_nonneg hKe hq, hq]

/-- At `t = 0` the propagator path is the constant datum. -/
theorem propagatorCoeff_zero (D : DynData d) (μ : ℝ → Torus d → ℝ) (M : ℝ) (φc : Coeff d)
    (hφ : MemHs M φc) (hM : 1 ≤ M) : propagatorCoeff D μ M 0 φc 0 = φc := by
  have hex : ∃ F, IsForwardSolution D μ 0 φc F ∧ WeakContinuousInHs M F 0 :=
    ⟨fun _ => φc, ⟨fun τ _ => hφ.mono hM, fun k => by simp, fun k τ hτ => by
      have : τ = 0 := le_antisymm hτ.2 hτ.1
      subst this; simp⟩, ⟨fun τ _ => hφ, fun G _ => continuousOn_const⟩⟩
  have hdef : propagatorCoeff D μ M 0 φc = hex.choose := by
    unfold propagatorCoeff; simp only [hex, dite_true]
  obtain ⟨h1, -⟩ := hex.choose_spec
  rw [hdef]
  funext k
  rw [h1.eq k 0 ⟨le_rfl, le_rfl⟩]
  simp

end HRS.PDE.StabAux
