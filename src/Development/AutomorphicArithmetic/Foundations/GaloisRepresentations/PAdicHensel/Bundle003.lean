module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private lemma UpperTheory.Gal.G1.normInt_eq_one {q : ℕ} [Fact q.Prime] {n : ℤ} (h : ¬ (q : ℤ) ∣ n) :
    ‖(n : ℤ_[q])‖ = 1 :=
  le_antisymm (PadicInt.norm_le_one _)
    (not_lt.mp fun hlt => h ((PadicInt.norm_int_lt_one_iff_dvd n).mp hlt))

private lemma UpperTheory.Gal.G1.norm_lt_one_iff_toZMod {q : ℕ} [Fact q.Prime] (x : ℤ_[q]) :
    ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

private lemma UpperTheory.Gal.G1.norm_eq_one_of_toZMod {q : ℕ} [Fact q.Prime] {x : ℤ_[q]}
    (h : PadicInt.toZMod x ≠ 0) : ‖x‖ = 1 :=
  le_antisymm (PadicInt.norm_le_one _)
    (not_lt.mp fun hlt => h ((UpperTheory.Gal.G1.norm_lt_one_iff_toZMod x).mp hlt))

private lemma UpperTheory.Gal.G1.hens {q : ℕ} [Fact q.Prime] (c d a : ℤ_[q]) (h2 : ‖(2 : ℤ_[q])‖ = 1)
    (hc : ‖c‖ = 1) (ha : ‖a‖ = 1) (h : ‖c * a ^ 2 + d‖ < 1) : ∃ z : ℤ_[q], c * z ^ 2 + d = 0 := by
  let F : Polynomial ℤ_[q] := Polynomial.C c * Polynomial.X ^ 2 + Polynomial.C d
  have hF : ∀ t, Polynomial.aeval t F = c * t ^ 2 + d := by
    intro t; simp [F]
  have hF' : ∀ t, Polynomial.aeval t (Polynomial.derivative F) = c * (2 * t) := by
    intro t
    simp [F]
    exact Or.inl (Or.inl one_add_one_eq_two)
  have hn : ‖Polynomial.aeval a (Polynomial.derivative F)‖ = 1 := by
    rw [hF', norm_mul, norm_mul, hc, h2, ha]; simp
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := a) (by rw [hn, hF]; simpa using h)
  exact ⟨z, by rwa [hF] at hz⟩

theorem UpperTheory.Gal.G1.pPadicUnitNorm :
    PadicUnitNorm := by
  intro q _ D hqD u hu
  have hq2 : ¬ (q : ℤ) ∣ 2 := fun h => hqD (Dvd.dvd.mul_right h D)
  have hqd : ¬ (q : ℤ) ∣ D := fun h => hqD (Dvd.dvd.mul_left h 2)
  have h2 : ‖(2 : ℤ_[q])‖ = 1 := by
    have := UpperTheory.Gal.G1.normInt_eq_one (q := q) hq2
    simpa using this
  have hD : ‖(D : ℤ_[q])‖ = 1 := UpperTheory.Gal.G1.normInt_eq_one hqd
  have hodd : Fintype.card (ZMod q) % 2 = 1 := by
    rw [ZMod.card]
    rcases (Fact.out : q.Prime).eq_two_or_odd with h | h
    · subst h; exact absurd (by norm_num) hq2
    · exact h
  let U : ℤ_[q] := ⟨u, hu.le⟩
  have hU : ‖U‖ = 1 := hu
  have hUc : ((U : ℤ_[q]) : ℚ_[q]) = u := rfl
  have hub : PadicInt.toZMod U ≠ 0 := fun h0 =>
    absurd hU ((UpperTheory.Gal.G1.norm_lt_one_iff_toZMod U).mpr h0).ne
  have hDb : -(D : ZMod q) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hqd
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.X ^ 2)
    (g := Polynomial.C (-(D : ZMod q)) * Polynomial.X ^ 2 + Polynomial.C 0 * Polynomial.X
      + Polynomial.C (-PadicInt.toZMod U))
    (by simp) (Polynomial.degree_quadratic hDb) hodd
  have hab' : a ^ 2 - (D : ZMod q) * b ^ 2 - PadicInt.toZMod U = 0 := by
    simp at hab
    linear_combination hab
  let x0 : ℤ_[q] := (a.val : ℤ_[q])
  let y0 : ℤ_[q] := (b.val : ℤ_[q])
  have hx : PadicInt.toZMod x0 = a := by simp [x0]
  have hy : PadicInt.toZMod y0 = b := by simp [y0]
  have hDz : PadicInt.toZMod (D : ℤ_[q]) = (D : ZMod q) := by simp
  have key : ‖x0 ^ 2 - (D : ℤ_[q]) * y0 ^ 2 - U‖ < 1 := by
    rw [UpperTheory.Gal.G1.norm_lt_one_iff_toZMod]
    simp only [map_sub, map_mul, map_pow, hx, hy, hDz]
    exact hab'
  have hor : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨ha0, hb0⟩ := hcon
    apply hub
    rw [ha0, hb0] at hab'
    simpa using hab'
  rcases hor with ha | hb
  · have hx1 : ‖x0‖ = 1 := UpperTheory.Gal.G1.norm_eq_one_of_toZMod (by rwa [hx])
    obtain ⟨z, hz⟩ := UpperTheory.Gal.G1.hens 1 (-((D : ℤ_[q]) * y0 ^ 2 + U)) x0 h2 (by simp) hx1 (by
      have e : 1 * x0 ^ 2 + -((D : ℤ_[q]) * y0 ^ 2 + U) = x0 ^ 2 - (D : ℤ_[q]) * y0 ^ 2 - U := by ring
      rw [e]; exact key)
    refine ⟨z, y0, ?_⟩
    have h3 := congrArg (fun t : ℤ_[q] => (t : ℚ_[q])) hz
    simp only [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_neg, PadicInt.coe_one,
      PadicInt.coe_zero, PadicInt.coe_intCast, hUc] at h3
    linear_combination -h3
  · have hy1 : ‖y0‖ = 1 := UpperTheory.Gal.G1.norm_eq_one_of_toZMod (by rwa [hy])
    obtain ⟨z, hz⟩ := UpperTheory.Gal.G1.hens (D : ℤ_[q]) (U - x0 ^ 2) y0 h2 hD hy1 (by
      have e : (D : ℤ_[q]) * y0 ^ 2 + (U - x0 ^ 2) = -(x0 ^ 2 - (D : ℤ_[q]) * y0 ^ 2 - U) := by ring
      rw [e, norm_neg]; exact key)
    refine ⟨x0, z, ?_⟩
    have h3 := congrArg (fun t : ℤ_[q] => (t : ℚ_[q])) hz
    simp only [PadicInt.coe_add, PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow,
      PadicInt.coe_zero, PadicInt.coe_intCast, hUc] at h3
    linear_combination h3
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private lemma val_alg (v : HeightOneSpectrum ℤ) (s : ℚ) :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) s) = v.valuation ℚ s :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v s

private lemma exists_gen (v : HeightOneSpectrum ℤ) :
    ∃ q : ℕ, q ≠ 0 ∧ v.asIdeal = Ideal.span {(q : ℤ)} := by
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal v.asIdeal
  have hg' : v.asIdeal = Ideal.span {g} := hg
  refine ⟨g.natAbs, ?_, ?_⟩
  · intro h0
    apply v.ne_bot
    rw [hg', Int.natAbs_eq_zero.mp h0]
    simp
  · rw [hg', Ideal.span_singleton_eq_span_singleton]
    exact Int.associated_natAbs g

private lemma val_nat (v : HeightOneSpectrum ℤ) (q : ℕ) :
    v.valuation ℚ (q : ℚ) = v.intValuation (q : ℤ) := by
  rw [← v.valuation_of_algebraMap (K := ℚ)]
  simp

private lemma val_self (v : HeightOneSpectrum ℤ) {q : ℕ} (h0 : q ≠ 0)
    (h : v.asIdeal = Ideal.span {(q : ℤ)}) : v.valuation ℚ (q : ℚ) = WithZero.exp (-1 : ℤ) := by
  rw [val_nat]
  exact HeightOneSpectrum.intValuation_singleton v (by exact_mod_cast h0) h

private lemma val_other (v w : HeightOneSpectrum ℤ) {q : ℕ}
    (h : v.asIdeal = Ideal.span {(q : ℤ)}) (hne : w ≠ v) : w.valuation ℚ (q : ℚ) = 1 := by
  rw [val_nat]
  apply le_antisymm (w.intValuation_le_one _)
  rw [← not_lt, w.intValuation_lt_one_iff_mem]
  intro hm
  apply hne
  have hle : v.asIdeal ≤ w.asIdeal := by
    rw [h, Ideal.span_le]
    simpa using hm
  exact HeightOneSpectrum.ext ((v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm)

private lemma finite_ne_one (p : ℕ) (t : (AfP p)ˣ) :
    {v : AwayP p | Valued.v (AfP.eval v (t : AfP p)) ≠ 1}.Finite := by
  have ht := (t : AfP p).2
  have hti := ((t⁻¹ : (AfP p)ˣ) : AfP p).2
  refine (Filter.eventually_cofinite.mp (ht.and hti)).subset ?_
  intro v hv hboth
  apply hv
  obtain ⟨h1, h2⟩ := hboth
  have h1' : Valued.v (AfP.eval v (t : AfP p)) ≤ 1 := h1
  have h2' : Valued.v (AfP.eval v ((t⁻¹ : (AfP p)ˣ) : AfP p)) ≤ 1 := h2
  have hm : Valued.v (AfP.eval v (t : AfP p)) * Valued.v (AfP.eval v ((t⁻¹ : (AfP p)ˣ) : AfP p)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  apply le_antisymm h1'
  calc (1 : WithZero (Multiplicative ℤ)) = _ := hm.symm
    _ ≤ Valued.v (AfP.eval v (t : AfP p)) * 1 := mul_le_mul_right h2' _
    _ = _ := mul_one _

private lemma val_ne_zero (p : ℕ) (t : (AfP p)ˣ) (v : AwayP p) :
    Valued.v (AfP.eval v (t : AfP p)) ≠ 0 := by
  intro h
  have hm : Valued.v (AfP.eval v (t : AfP p)) * Valued.v (AfP.eval v ((t⁻¹ : (AfP p)ˣ) : AfP p)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  rw [h, zero_mul] at hm
  exact zero_ne_one hm

theorem UpperTheory.Gal.G1.pScale :
    Scale := by
  intro p t
  classical
  choose q hq0 hq using fun v : AwayP p => exists_gen v.1
  let n : AwayP p → ℤ := fun v => WithZero.log (Valued.v (AfP.eval v (t : AfP p)))
  let S := (finite_ne_one p t).toFinset
  refine ⟨∏ v ∈ S, ((q v : ℚ) ^ (-n v)), ?_, ?_⟩
  · apply Finset.prod_pos
    intro v _
    apply zpow_pos
    exact_mod_cast Nat.pos_of_ne_zero (hq0 v)
  · intro w
    rw [val_alg, map_prod]
    have hterm : ∀ v ∈ S, w.1.valuation ℚ ((q v : ℚ) ^ (-n v)) =
        if v = w then WithZero.exp (n v) else 1 := by
      intro v _
      rw [map_zpow₀]
      split_ifs with hvw
      · subst hvw
        rw [val_self v.1 (hq0 v) (hq v), ← WithZero.exp_zsmul]
        simp
      · rw [val_other v.1 w.1 (hq v) (fun h => hvw (Subtype.ext h.symm)), _root_.one_zpow]
    rw [Finset.prod_congr rfl hterm, Finset.prod_ite_eq']
    split_ifs with hw
    · exact (WithZero.exp_log (val_ne_zero p t w)).symm
    · have : ¬ Valued.v (AfP.eval w (t : AfP p)) ≠ 1 := by
        intro h
        apply hw
        simpa [S] using h
      exact not_not.mp this
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pBlockMat :
    BlockMat := by
  intro R _ σ hσ c x y hc h m
  let b : Matrix (Fin 2) (Fin 2) R := !![x, -σ y; y, σ x]
  let b' : Matrix (Fin 2) (Fin 2) R := !![c * σ x, c * σ y; -(c * y), c * x]
  let M : Matrix (Fin 1 ⊕ (Fin 2 × Fin m)) (Fin 1 ⊕ (Fin 2 × Fin m)) R :=
    fromBlocks 1 0 0 (blockDiagonal fun _ => b)
  let M' : Matrix (Fin 1 ⊕ (Fin 2 × Fin m)) (Fin 1 ⊕ (Fin 2 × Fin m)) R :=
    fromBlocks 1 0 0 (blockDiagonal fun _ => b')
  let e : Fin 1 ⊕ (Fin 2 × Fin m) ≃ Fin (2 * m + 1) :=
    ((Equiv.refl (Fin 1)).sumCongr finProdFinEquiv).trans
      (finSumFinEquiv.trans (finCongr (by omega)))
  have hbd : (fromBlocks 1 0 0 (blockDiagonal fun _ : Fin m => (1 : Matrix (Fin 2) (Fin 2) R)) :
      Matrix (Fin 1 ⊕ (Fin 2 × Fin m)) (Fin 1 ⊕ (Fin 2 × Fin m)) R) = 1 := by
    have h1 : (blockDiagonal fun _ : Fin m => (1 : Matrix (Fin 2) (Fin 2) R)) = 1 :=
      blockDiagonal_one
    rw [h1, fromBlocks_one]
  have hbb' : b * b' = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b, b', Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination h | ring
  have hb'b : b' * b = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b, b', Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination h | ring
  have hu : (b.map σ)ᵀ * diagonal (fun _ : Fin 2 => c) * b = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b, Matrix.mul_apply, Fin.sum_univ_two, hσ] <;>
      first | linear_combination h | ring
  have hM : M * M' = 1 := by
    simp only [M, M', fromBlocks_multiply]
    rw [← blockDiagonal_mul]
    simp only [hbb', Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    exact hbd
  have hM' : M' * M = 1 := by
    simp only [M, M', fromBlocks_multiply]
    rw [← blockDiagonal_mul]
    simp only [hb'b, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    exact hbd
  have hD : (fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then (1 : R) else c) ∘ e =
      Sum.elim (fun _ => 1) (fun _ => c) := by
    funext p
    rcases p with p | p
    · have hp : p = 0 := Subsingleton.elim _ _
      subst hp
      simp [e]
      intro hne
      exact (hne (Fin.ext (by simp))).elim
    · simp [e]
  have hd2 : (diagonal fun _ : Fin 2 × Fin m => c) =
      blockDiagonal fun _ : Fin m => diagonal fun _ : Fin 2 => c := by
    rw [blockDiagonal_diagonal]
  have hcore : (M.map σ)ᵀ *
      diagonal ((fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then (1 : R) else c) ∘ e) * M = 1 := by
    rw [hD, ← fromBlocks_diagonal]
    simp only [M, fromBlocks_map, fromBlocks_transpose, blockDiagonal_map _ _ (map_zero σ),
      blockDiagonal_transpose, hd2]
    simp only [fromBlocks_multiply, Matrix.map_zero _ (map_zero σ), Matrix.transpose_zero,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one]
    rw [← blockDiagonal_mul, ← blockDiagonal_mul]
    simp only [hu]
    simpa using hbd
  have hbS : ∀ (S : Subring R), x ∈ S → y ∈ S → σ x ∈ S → σ y ∈ S → c ∈ S →
      (∀ i j, b i j ∈ S) ∧ ∀ i j, b' i j ∈ S := by
    intro S hx hy hsx hsy hcS
    constructor
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [b] <;>
        first | assumption | exact S.neg_mem hsy
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [b'] <;>
        first | exact S.neg_mem (S.mul_mem hcS hy) | exact S.mul_mem hcS hsx | exact S.mul_mem hcS hsy | exact S.mul_mem hcS hx | exact S.mul_mem hcS hy
  have hblk : ∀ (S : Subring R) (N : Matrix (Fin 2) (Fin 2) R), (∀ i j, N i j ∈ S) →
      ∀ p q, (fromBlocks 1 0 0 (blockDiagonal fun _ : Fin m => N) :
        Matrix (Fin 1 ⊕ (Fin 2 × Fin m)) (Fin 1 ⊕ (Fin 2 × Fin m)) R) p q ∈ S := by
    intro S N hN p q
    rcases p with p | ⟨i, k⟩ <;> rcases q with q | ⟨j, l⟩
    · simp only [fromBlocks_apply₁₁, Matrix.one_apply]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    · simp only [fromBlocks_apply₁₂, Matrix.zero_apply]
      exact S.zero_mem
    · simp only [fromBlocks_apply₂₁, Matrix.zero_apply]
      exact S.zero_mem
    · simp only [fromBlocks_apply₂₂, blockDiagonal_apply]
      split_ifs
      · exact hN _ _
      · exact S.zero_mem
  refine ⟨⟨reindex e e M, reindex e e M', ?_, ?_⟩, ?_, ?_⟩
  · rw [reindex_apply, reindex_apply, submatrix_mul_equiv, hM, submatrix_one_equiv]
  · rw [reindex_apply, reindex_apply, submatrix_mul_equiv, hM', submatrix_one_equiv]
  · have hDD : diagonal (fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then (1 : R) else c) =
        (diagonal ((fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then (1 : R) else c) ∘ e)).submatrix
          e.symm e.symm := by
      rw [submatrix_diagonal_equiv]
      congr 1
      funext i
      simp
    show ((reindex e e M).map σ)ᵀ *
        diagonal (fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then (1 : R) else c) * reindex e e M = 1
    rw [hDD, reindex_apply, ← submatrix_map, transpose_submatrix, submatrix_mul_equiv,
      submatrix_mul_equiv, hcore, submatrix_one_equiv]
  · intro S hx hy hsx hsy hcS i j
    obtain ⟨h1, h2⟩ := hbS S hx hy hsx hsy hcS
    exact ⟨hblk S b h1 _ _, hblk S b' h2 _ _⟩
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pFinCongr :
    PadMap → LocRoot → TrivMat → CongrScale → SplitCongr → DefSign → FinCongr := by
  classical
  intro hPad hLoc hTriv hScale hSplit hD E _ _ _ A n p _ S B B' x x' t t' hT hT' s hs hloc w
  set D : ℤ := A.tr ^ 2 - 4 * A.nm with hDdef
  have hD0 : D ≠ 0 := ne_of_lt A.disc_neg
  set θ : E := (A.ω : E) - (A.bar A.ω : E) with hθdef
  have hθc : (IsCMField.complexConj E) θ = -θ := by
    rw [hθdef, map_sub, A.bar_eq, IsCMField.complexConj_apply_apply]
    ring
  have hθ2 : θ ^ 2 = (D : E) := by
    have h1 : ((A.ω + A.bar A.ω : 𝓞 E) : E) = ((A.tr : 𝓞 E) : E) := by rw [A.tr_eq]
    have h2 : ((A.ω * A.bar A.ω : 𝓞 E) : E) = ((A.nm : 𝓞 E) : E) := by rw [A.nm_eq]
    have c1 : ((A.tr : 𝓞 E) : E) = (A.tr : E) := map_intCast (algebraMap (𝓞 E) E) A.tr
    have c2 : ((A.nm : 𝓞 E) : E) = (A.nm : E) := map_intCast (algebraMap (𝓞 E) E) A.nm
    rw [c1] at h1
    rw [c2] at h2
    push_cast at h1 h2
    rw [hθdef, hDdef]
    push_cast
    linear_combination ((A.ω : E) + (A.bar A.ω : E) + (A.tr : E)) * h1 - 4 * h2
  obtain ⟨hM1, hM2, hM3⟩ := hD E A n p S B
  obtain ⟨hN1, hN2, hN3⟩ := hD E A n p S B'
  have hs0 : (s : E) ≠ 0 := by exact_mod_cast hs.ne'
  have hsym : ∀ a b, (IsCMField.complexConj E) (((s : E) • (mat S ↑B.β * (A.H n)⁻¹)) a b) =
      ((s : E) • (mat S ↑B.β * (A.H n)⁻¹)) b a := by
    intro a b
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_ratCast, hM1 a b]
  have hdet : ((s : E) • (mat S ↑B.β * (A.H n)⁻¹)).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hs0) hM2
  obtain ⟨v, ι, hv⟩ := hPad (maximalRealSubfield E) w
  by_cases hvp : v.asIdeal = Ideal.span {(p : ℤ)}
  · have hpw : ((p : ℤ) : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal :=
      hv _ (by rw [hvp]; exact Ideal.subset_span rfl)
    obtain ⟨hnd, hr⟩ := (S.good).1
    obtain ⟨ρ, hρ, -⟩ := hLoc (maximalRealSubfield E) w A.tr A.nm p (Fact.out) (by exact_mod_cast hpw) hnd hr
    refine hSplit E n _ _ hsym hN1 hdet hN2 (HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w)
      θ D hD0 hθc hθ2 (2 * (ρ : HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w) - A.tr) ?_
    have hρ' := congrArg (fun z : HeightOneSpectrum.adicCompletionIntegers (maximalRealSubfield E) w =>
      (z : HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w)) hρ
    push_cast at hρ'
    rw [hDdef]
    push_cast
    linear_combination 4 * hρ'
  · let v' : AwayP p := ⟨v, hvp⟩
    obtain ⟨a, b, hab⟩ := hloc v'
    let ψ : AfP p →+* HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w :=
      ι.comp (AfP.eval v').toRingHom
    have hH' : (A.H n).map (cj E) = A.H n := by
      have h := congrArg Matrix.transpose (A.herm n)
      rw [Matrix.transpose_transpose] at h
      rw [h]
      exact Matrix.diagonal_transpose _
    obtain ⟨X, hX, hXeq⟩ := hTriv E n (A.H n) (A.herm n) hH' (A.det_ne n) (AfP p)
      (HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w) ψ (mat S ↑B.β) x ↑t hT
    obtain ⟨X', hX', hXeq'⟩ := hTriv E n (A.H n) (A.herm n) hH' (A.det_ne n) (AfP p)
      (HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w) ψ (mat S ↑B'.β) x' ↑t' hT'
    have ht0 : ψ ↑t' ≠ 0 := (t'.isUnit.map ψ).ne_zero
    have heq : ψ ↑t' = (s : HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w) * ψ ↑t *
        (ι a ^ 2 - (D : HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w) * ι b ^ 2) := by
      show ι (AfP.eval v' ↑t') = _
      rw [hab, map_mul, map_mul, map_sub, map_mul, map_pow, map_pow, map_intCast]
      congr 2
      exact eq_ratCast (ι.comp (algebraMap ℚ _)) s
    exact hScale E n (A.H n)⁻¹ _ _ (HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w)
      θ D hθc hθ2 (ψ ↑t) (ψ ↑t') (ι a) (ι b) s ht0 heq X X' hX hX' hXeq hXeq'
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pFinCls :
    UnitCls → FinCongr → InfCongr → DefSign → RelOf → FinCls := by
  classical
  intro hU hF hI hD hR E _ _ _ A n p _ S
  obtain ⟨I, hI0, κ, hκ⟩ := hU p (A.tr ^ 2 - 4 * A.nm) (ne_of_lt A.disc_neg)
  have key : ∀ (B B' : DForm S.G) x t x' t', Triv S.G (AfP p) ↑B.β x t →
      Triv S.G (AfP p) ↑B'.β x' t' → κ t = κ t' → B.Rel B' := by
    intro B B' x t x' t' hT hT' hk
    obtain ⟨s, hs, hloc⟩ := hκ t t' hk
    obtain ⟨hM1, hM2, hM3⟩ := hD E A n p S B
    obtain ⟨hN1, hN2, hN3⟩ := hD E A n p S B'
    have hs0 : (s : E) ≠ 0 := by exact_mod_cast hs.ne'
    have hsym : ∀ a b, (IsCMField.complexConj E) (((s : E) • (mat S ↑B.β * (A.H n)⁻¹)) a b) =
        ((s : E) • (mat S ↑B.β * (A.H n)⁻¹)) b a := by
      intro a b
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_ratCast, hM1 a b]
    have hdet : ((s : E) • (mat S ↑B.β * (A.H n)⁻¹)).det ≠ 0 := by
      rw [Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ hs0) hM2
    obtain ⟨P, hP, hPeq⟩ := GlobalTheory.HermGlobal.congr_of_local_complex (F := maximalRealSubfield E)
      (σ := IsCMField.complexConj E) (IsCMField.complexConj_ne_one E) hsym hN1 hdet hN2
      (fun w => hF E A n p S B B' x x' t t' hT hT' s hs hloc w)
      (by
        intro τ hτ
        have herm : ∀ N : Matrix (Fin n) (Fin n) E,
            (∀ a b, (IsCMField.complexConj E) (N a b) = N b a) → (N.map τ).IsHermitian := by
          intro N hN
          ext i j
          simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
          rw [← hN j i, hτ, starRingEnd_apply]
        have hsm : ((s : E) • (mat S ↑B.β * (A.H n)⁻¹)).map τ =
            (s : ℂ) • (mat S ↑B.β * (A.H n)⁻¹).map τ := by
          ext i j
          simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_ratCast]
        apply hI n _ _ (herm _ hsym) (herm _ hN1)
          (if InfinitePlace.mk τ = InfinitePlace.mk A.τ₀ then 1 else -1)
        · intro v hv
          rw [hsm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re,
            Complex.ratCast_re, Complex.ratCast_im, zero_mul, sub_zero, mul_left_comm]
          exact mul_pos (by exact_mod_cast hs) (hM3 τ v hv)
        · intro v hv
          exact hN3 τ v hv)
    exact hR E A n p S B B' s hs P hP hPeq
  haveI := hI0
  let tOf : DForm S.G → (AfP p)ˣ := fun B => B.trivAf.choose_spec.choose
  have htOf : ∀ B : DForm S.G, Triv S.G (AfP p) ↑B.β B.trivAf.choose (tOf B) :=
    fun B => B.trivAf.choose_spec.choose_spec
  refine Finite.of_injective (fun q : DFCls S.G => κ (tOf (Quot.out (r := DForm.Rel) q))) ?_
  intro q q' h
  rw [← Quot.out_eq q, ← Quot.out_eq q']
  exact Quot.sound (key _ _ _ _ _ _ (htOf _) (htOf _) h)
end
