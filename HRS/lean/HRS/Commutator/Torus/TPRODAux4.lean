import HRS.Commutator.Torus.TPRODAux3
import HRS.Commutator.Torus.LEIBTAux27
import HRS.Commutator.Whole.LocalAuxSAMP12

/-!
# T-PROD helper file 4: the product estimate, abstract form

`tprod_core`: from Bessel representations of the two factors (with `L^{p₁}`, `L^{p₂}` bounds) and the
inhomogeneous Leibniz rule `leibt_main`, via Fejér smoothing of the first factor, the component sum, Parseval
and Fatou, we get `‖⟨f,u⟩‖_{H^α(𝕋_R)}`-bound.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

lemma tprod_box_of_support {η : ℝ} (hη : 0 < η) (k : Lattice d)
    (hk : ¬ HRS.PDE.InBox (⌈2 / η⌉₊) k) : 2 < η * Lattice.enorm k := by
  unfold HRS.PDE.InBox at hk
  push_neg at hk
  obtain ⟨i, hi⟩ := hk
  have h1 : ((⌈2 / η⌉₊ : ℕ) : ℝ) < |(k i : ℝ)| := by
    have h2 : ((⌈2 / η⌉₊ : ℤ) : ℝ) < ((|k i| : ℤ) : ℝ) := by exact_mod_cast hi
    simpa using h2
  have h2 : |(k i : ℝ)| ≤ Lattice.enorm k := by
    unfold Lattice.enorm
    have := PiLp.norm_apply_le (Lattice.toEuc k) i
    simpa [Lattice.toEuc] using this
  have h3 : 2 / η ≤ ((⌈2 / η⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h4 : 2 / η < Lattice.enorm k := by linarith
  rw [div_lt_iff₀ hη] at h4
  linarith

lemma tprod_exponent_identity (hd : 3 ≤ d) (hsd : s < (d : ℝ) - 2) (hs0 : 0 ≤ s) :
    (ENNReal.ofReal (Whole.p1E d s))⁻¹ + (ENNReal.ofReal (Whole.p2E d s))⁻¹ = 2⁻¹ := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 0 < (d : ℝ) - s - 2 := by linarith
  have h2 : 0 < s + 2 := by linarith
  have hP0 : 0 < Whole.p1E d s := by unfold Whole.p1E; positivity
  have hQ0 : 0 < Whole.p2E d s := by unfold Whole.p2E; positivity
  rw [← ENNReal.ofReal_inv_of_pos hP0, ← ENNReal.ofReal_inv_of_pos hQ0,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have : (Whole.p1E d s)⁻¹ + (Whole.p2E d s)⁻¹ = (2 : ℝ)⁻¹ := by
    unfold Whole.p1E Whole.p2E
    field_simp
    ring
  rw [this, ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

lemma tprod_p2_gt_one (hd : 3 ≤ d) (hsd : s < (d : ℝ) - 2) (hs0 : 0 ≤ s) : 1 < Whole.p2E d s := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  unfold Whole.p2E
  rw [lt_div_iff₀ (by linarith)]
  linarith

theorem tprod_core (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ CL : ℝ, 0 < CL ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ Cu : ℝ, 0 ≤ Cu →
      ∀ (f W u U : Torus d → Euc d) (X Nu : ℝ≥0∞), Continuous f → Continuous u →
      (∀ i, IsBesselRepT η (Whole.alphaE d s) (fun x => f x i) (fun x => W x i)) →
      (∀ i, IsBesselRepT η (Whole.alphaE d s) (fun x => u x i) (fun x => U x i)) →
      (∀ i (k : Lattice d), 2 < η * Lattice.enorm k → Torus.fcoef (fun x => u x i) k = 0) →
      eLpNorm (fun x => ‖W x‖) (ENNReal.ofReal (Whole.p1E d s)) volume ≤ X →
      eLpNorm (fun x => ‖f x‖) (ENNReal.ofReal (Whole.p1E d s)) volume ≤ X → X ≠ ⊤ →
      eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal (Whole.p2E d s)) volume ≤ Nu → Nu ≠ ⊤ →
      eLpNorm (fun x => ‖U x‖) (ENNReal.ofReal (Whole.p2E d s)) volume ≤ ENNReal.ofReal Cu * Nu →
        MemLp (fun x => inner ℝ (f x) (u x)) 2 volume ∧
        (sobSqT η (Whole.alphaE d s) (fun k => Torus.fcoef (fun x => inner ℝ (f x) (u x)) k)) ^
            ((1 : ℝ) / 2) ≤
          ENNReal.ofReal (η ^ ((d : ℝ) / 2)) *
            ((d : ℝ≥0∞) * (ENNReal.ofReal CL * (1 + ENNReal.ofReal Cu) * X * Nu)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hα1, hαd, hα0, hp1, hαp⟩ := HRS.Commutator.Whole.SAMP1.exponents hd hs0 hsd
  have hq1 : 1 < Whole.p2E d s := tprod_p2_gt_one hd hsd hs0
  have hpq := tprod_exponent_identity hd hsd hs0
  have hP1 : 1 < ENNReal.ofReal (Whole.p1E d s) := ENNReal.one_lt_ofReal.2 hp1
  have hQ1 : 1 < ENNReal.ofReal (Whole.p2E d s) := ENNReal.one_lt_ofReal.2 hq1
  obtain ⟨CL, hCL, hLeib⟩ := leibt_main (d := d) hd1 (Whole.alphaE d s) hα0 2
    (ENNReal.ofReal (Whole.p1E d s)) (ENNReal.ofReal (Whole.p2E d s))
    (ENNReal.ofReal (Whole.p2E d s)) (ENNReal.ofReal (Whole.p1E d s))
    (by norm_num) (by norm_num) hP1 hQ1 hQ1 hP1 hpq (by rw [add_comm]; exact hpq)
  refine ⟨CL, hCL, ?_⟩
  intro η hη hη1 Cu hCu f W u U X Nu hfc huc hrf hru hsupp hWX hfX hXtop hNu hNutop hUN
  set α := Whole.alphaE d s with hα
  set P := Whole.p1E d s with hP
  set Q := Whole.p2E d s with hQ
  have hcomp : ∀ (z : Euc d) (i : Fin d), ‖z i‖ ≤ ‖‖z‖‖ := fun z i => by
    rw [norm_norm]
    exact PiLp.norm_apply_le z i
  have hfi : ∀ i, Continuous (fun x => f x i) := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hfc
  have hui : ∀ i, Continuous (fun x => u x i) := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp huc
  have hus : ∀ i, Torus.IsSmooth (fun x => u x i) := fun i =>
    tprod_smooth_of_box (hui i) (⌈2 / η⌉₊) fun k hk => hsupp i k (tprod_box_of_support hη k hk)
  -- component bounds
  have hfN : ∀ i, eLpNorm (fun x => f x i) (ENNReal.ofReal P) volume ≤ X := fun i =>
    le_trans (eLpNorm_mono (hfi i).aestronglyMeasurable fun x => hcomp (f x) i) hfX
  have huN : ∀ i, eLpNorm (fun x => u x i) (ENNReal.ofReal Q) volume ≤ Nu := fun i =>
    le_trans (eLpNorm_mono (hui i).aestronglyMeasurable fun x => hcomp (u x) i) hNu
  have hcompw : ∀ i, eLpNorm (fun x => W x i) (ENNReal.ofReal P) volume ≤ X ∨
      ¬ AEStronglyMeasurable (fun x => W x i) volume := fun i => by
    by_cases h : AEStronglyMeasurable (fun x => W x i) volume
    · exact Or.inl (le_trans (eLpNorm_mono h fun x => hcomp (W x) i) hWX)
    · exact Or.inr h
  have hcompU : ∀ i, eLpNorm (fun x => U x i) (ENNReal.ofReal Q) volume ≤ ENNReal.ofReal Cu * Nu ∨
      ¬ AEStronglyMeasurable (fun x => U x i) volume := fun i => by
    by_cases h : AEStronglyMeasurable (fun x => U x i) volume
    · exact Or.inl (le_trans (eLpNorm_mono h fun x => hcomp (U x) i) hUN)
    · exact Or.inr h
  have hUNtop : ENNReal.ofReal Cu * Nu ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hNutop
  have hall : ∀ i : Fin d, ∃ ψ H : ℕ → Torus d → ℝ, (∀ N, Continuous (ψ N) ∧ Continuous (H N)) ∧
      (∀ N k, Torus.fcoef (H N) k =
        (((1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (α / 2) : ℝ) : ℂ) *
          Torus.fcoef (ψ N) k) ∧
      (∀ N, eLpNorm (H N) 2 volume ≤ ENNReal.ofReal CL * (1 + ENNReal.ofReal Cu) * X * Nu) ∧
      ∀ k, Tendsto (fun N => Torus.fcoef (ψ N) k) atTop
        (𝓝 (Torus.fcoef (fun x => f x i * u x i) k)) := by
    intro i
    obtain ⟨ψ, H, hc, hco, hbd, hlim⟩ := tprod_comp (η := η) (α := α) (CL := CL) hη hη1 hp1 hq1
      (fun f g h F G H => hLeib η hη hη1 f g h F G H) (hfi i) (hus i) (hrf i) (hru i)
      hXtop hUNtop (fun h => (hcompw i).resolve_right (not_not.2 h))
      (fun h => (hcompU i).resolve_right (not_not.2 h))
    refine ⟨ψ, H, hc, hco, fun N => (hbd N).trans ?_, hlim⟩
    calc ENNReal.ofReal CL * (X * eLpNorm (fun x => u x i) (ENNReal.ofReal Q) volume +
          ENNReal.ofReal Cu * Nu * eLpNorm (fun x => f x i) (ENNReal.ofReal P) volume)
        ≤ ENNReal.ofReal CL * (X * Nu + ENNReal.ofReal Cu * Nu * X) := by
          gcongr
          · exact huN i
          · exact hfN i
      _ = ENNReal.ofReal CL * (1 + ENNReal.ofReal Cu) * X * Nu := by ring
  choose ψ H hc hco hbd hlim using hall
  -- the continuous function `h`
  have hfun : (fun x => inner ℝ (f x) (u x)) = fun x => ∑ i, f x i * u x i := by
    funext x
    simp [PiLp.inner_apply, mul_comm]
  have hhc : Continuous (fun x => ∑ i, f x i * u x i) :=
    continuous_finsetSum _ fun i _ => (hfi i).mul (hui i)
  have hmem : MemLp (fun x => ∑ i, f x i * u x i) 2 volume :=
    hhc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [hfun]
  refine ⟨hmem, ?_⟩
  -- totals
  set Ht : ℕ → Torus d → ℝ := fun N x => ∑ i, H i N x with hHt
  set ψt : ℕ → Torus d → ℝ := fun N x => ∑ i, ψ i N x with hψt
  have hHtc : ∀ N, Continuous (Ht N) := fun N => continuous_finsetSum _ fun i _ => (hc i N).2
  have hHti : ∀ i N, Integrable (H i N) := fun i N =>
    HRS.PDE.MFThermalExist.integrable_of_continuous' (hc i N).2
  have hψti : ∀ i N, Integrable (ψ i N) := fun i N =>
    HRS.PDE.MFThermalExist.integrable_of_continuous' (hc i N).1
  have hHtm : ∀ N, MemLp (Ht N) 2 volume := fun N =>
    (hHtc N).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hHtco : ∀ N k, Torus.fcoef (Ht N) k =
      (((1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (α / 2) : ℝ) : ℂ) *
        ∑ i, Torus.fcoef (ψ i N) k := by
    intro N k
    simp only [hHt]
    rw [tprod_fcoef_sum Finset.univ (fun i => hHti i N) k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hco i N k
  have hbdt : ∀ N, eLpNorm (Ht N) 2 volume ≤
      (d : ℝ≥0∞) * (ENNReal.ofReal CL * (1 + ENNReal.ofReal Cu) * X * Nu) := by
    intro N
    have h1 : Ht N = ∑ i : Fin d, H i N := by
      funext x; simp [hHt]
    rw [h1]
    refine (eLpNorm_sum_le (by norm_num)).trans ?_
    calc ∑ i : Fin d, eLpNorm (H i N) 2 volume
        ≤ ∑ i : Fin d, ENNReal.ofReal CL * (1 + ENNReal.ofReal Cu) * X * Nu :=
          Finset.sum_le_sum fun i _ => hbd i N
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  set cN : ℕ → Lattice d → ℂ := fun N k => ∑ i, Torus.fcoef (ψ i N) k with hcN
  have hsob : ∀ N, sobSqT η α (cN N) ≤
      ENNReal.ofReal (η ^ d) * ((d : ℝ≥0∞) * (ENNReal.ofReal CL * (1 + ENNReal.ofReal Cu) * X * Nu)) ^ 2 := by
    intro N
    rw [tprod_sobSq_eq (hHtm N) (hHtco N)]
    gcongr
    exact hbdt N
  have hlimt : ∀ k, Tendsto (fun N => cN N k) atTop
      (𝓝 (Torus.fcoef (fun x => ∑ i, f x i * u x i) k)) := by
    intro k
    have hint : ∀ i, Integrable (fun x => f x i * u x i) := fun i =>
      HRS.PDE.MFThermalExist.integrable_of_continuous' ((hfi i).mul (hui i))
    rw [tprod_fcoef_sum Finset.univ hint k]
    exact tendsto_finsetSum _ fun i _ => hlim i k
  have hfat := tprod_sobSq_fatou hlimt hsob
  calc (sobSqT η α fun k => Torus.fcoef (fun x => ∑ i, f x i * u x i) k) ^ ((1 : ℝ) / 2)
      ≤ (ENNReal.ofReal (η ^ d) *
          ((d : ℝ≥0∞) * (ENNReal.ofReal CL * (1 + ENNReal.ofReal Cu) * X * Nu)) ^ 2) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow hfat (by norm_num)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.rpow_natCast,
          ← Real.rpow_mul hη.le]
        congr 3
        ring

end HRS.Commutator.TorusNote
