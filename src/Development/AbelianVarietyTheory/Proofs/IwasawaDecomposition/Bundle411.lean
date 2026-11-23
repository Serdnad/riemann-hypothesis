module

public import Formalism.LocalToGlobal.Divisibility.QLocTied
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle611
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle072
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle396
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle018
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.Mem.LamMul

section Blocks

variable {S : Type*} [CommRing S] {r c : ℕ}

theorem det_eq_of_lower_zero (M : Matrix (Fin (r + c)) (Fin (r + c)) S)
    (h : M.submatrix (Fin.natAdd r) (Fin.castAdd c) = 0) :
    M.det = (M.submatrix (Fin.castAdd c) (Fin.castAdd c)).det * (M.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
  have e : M.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (M.submatrix (Fin.castAdd c) (Fin.castAdd c)) (M.submatrix (Fin.castAdd c) (Fin.natAdd r)) 0
        (M.submatrix (Fin.natAdd r) (Fin.natAdd r)) := by
    rw [← h]
    ext (i | i) (j | j) <;> simp
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M, e, Matrix.det_fromBlocks_zero₂₁]

theorem mul_dd_of_lower_zero (M N : Matrix (Fin (r + c)) (Fin (r + c)) S)
    (h : M.submatrix (Fin.natAdd r) (Fin.castAdd c) = 0) :
    (M * N).submatrix (Fin.natAdd r) (Fin.natAdd r) =
      M.submatrix (Fin.natAdd r) (Fin.natAdd r) * N.submatrix (Fin.natAdd r) (Fin.natAdd r) := by
  ext i j
  have h0 : ∀ a, M (Fin.natAdd r i) (Fin.castAdd c a) = 0 := fun a => congrFun (congrFun h i) a
  simp [Matrix.mul_apply, Fin.sum_univ_add, h0]

theorem dd_mod (I : Ideal S) (K K' : Matrix (Fin (r + c)) (Fin (r + c)) S)
    (hK : ∀ i j, K (Fin.natAdd r i) (Fin.castAdd c j) ∈ I) (hK' : ∀ i j, K' (Fin.natAdd r i) (Fin.castAdd c j) ∈ I)
    (hu : IsUnit K.det) (hu' : IsUnit K'.det) :
    IsUnit (Ideal.Quotient.mk I (K.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) ∧
    IsUnit (Ideal.Quotient.mk I (K'.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) ∧
    ((K * K').submatrix (Fin.natAdd r) (Fin.natAdd r)).det -
      (K.submatrix (Fin.natAdd r) (Fin.natAdd r)).det * (K'.submatrix (Fin.natAdd r) (Fin.natAdd r)).det ∈ I := by
  have key : ∀ X : Matrix (Fin (r + c)) (Fin (r + c)) S, (∀ i j, X (Fin.natAdd r i) (Fin.castAdd c j) ∈ I) →
      ((Ideal.Quotient.mk I).mapMatrix X).submatrix (Fin.natAdd r) (Fin.castAdd c) = 0 := by
    intro X hX
    ext i j
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hX i j
  have sub : ∀ X : Matrix (Fin (r + c)) (Fin (r + c)) S, Ideal.Quotient.mk I (X.submatrix (Fin.natAdd r) (Fin.natAdd r)).det =
      (((Ideal.Quotient.mk I).mapMatrix X).submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
    intro X
    rw [RingHom.map_det]
    rfl
  have unit : ∀ X : Matrix (Fin (r + c)) (Fin (r + c)) S, (∀ i j, X (Fin.natAdd r i) (Fin.castAdd c j) ∈ I) →
      IsUnit X.det → IsUnit (Ideal.Quotient.mk I (X.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) := by
    intro X hX hu
    have h1 : IsUnit ((Ideal.Quotient.mk I).mapMatrix X).det := by
      rw [← RingHom.map_det]
      exact hu.map _
    rw [det_eq_of_lower_zero _ (key X hX)] at h1
    rw [sub]
    exact isUnit_of_mul_isUnit_right h1
  refine ⟨unit K hK hu, unit K' hK' hu', ?_⟩
  rw [← Ideal.Quotient.eq, map_mul, sub, sub, sub, map_mul,
    mul_dd_of_lower_zero _ _ (key K hK), Matrix.det_mul]

end Blocks

section Val

variable {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ) (O : Subring F) (ε : Γ)

def redI (hO : ∀ x ∈ O, v x ≤ 1) : Ideal O where
  carrier := {a | v (a : F) ≤ ε}
  add_mem' {a b} ha hb := by
    show v ((a : F) + b) ≤ ε
    exact (v.map_add _ _).trans (max_le ha hb)
  zero_mem' := by
    show v ((0 : O) : F) ≤ ε
    simp
  smul_mem' a b hb := by
    show v ((a : F) * b) ≤ ε
    rw [map_mul]
    exact (mul_le_of_le_one_left' (hO _ a.2)).trans hb

variable {v O ε}

theorem val_eq_one_of_isUnit (hO : ∀ x ∈ O, v x ≤ 1) (hε : ε < 1) (a : O)
    (h : IsUnit (Ideal.Quotient.mk (redI v O ε hO) a)) : v (a : F) = 1 := by
  obtain ⟨b, hb⟩ := h.exists_right_inv
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have h1 : a * b - 1 ∈ redI v O ε hO := by
    apply Ideal.Quotient.eq.1
    simpa using hb
  have h2 : v ((a : F) * b - 1) ≤ ε := by
    have h1' : v (((a * b - 1 : O)) : F) ≤ ε := h1
    simpa using h1'
  have h3 : v ((a : F) * b) = 1 := by
    have e : (a : F) * b = ((a : F) * b - 1) + 1 := by ring
    rw [e, Valuation.map_add_eq_of_lt_right]
    · simp
    · simpa using h2.trans_lt hε
  rw [map_mul] at h3
  refine le_antisymm (hO _ a.2) ?_
  rw [← h3]
  exact mul_le_of_le_one_right' (hO _ b.2)


omit [LinearOrderedCommGroupWithZero Γ] in
theorem exists_lift {n : ℕ} {k : GL (Fin n) F} (hk : k ∈ GLint O n) :
    ∃ K : Matrix (Fin n) (Fin n) O, (k : Matrix (Fin n) (Fin n) F) = K.map O.subtype ∧ IsUnit K.det := by
  let K : Matrix (Fin n) (Fin n) O := fun i j => ⟨(k : Matrix (Fin n) (Fin n) F) i j, hk.1 i j⟩
  let K' : Matrix (Fin n) (Fin n) O := fun i j => ⟨((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j, hk.2 i j⟩
  have e : (k : Matrix (Fin n) (Fin n) F) = K.map O.subtype := by ext i j; rfl
  have e' : ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = K'.map O.subtype := by ext i j; rfl
  refine ⟨K, e, Matrix.isUnit_det_of_right_inverse (B := K') ?_⟩
  apply Matrix.map_injective (f := O.subtype) Subtype.val_injective
  show (K * K').map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
  rw [Matrix.map_mul, ← e, ← e', ← Units.val_mul, mul_inv_cancel, Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

omit [LinearOrderedCommGroupWithZero Γ] in
theorem det_dd_map {r c : ℕ} (K : Matrix (Fin (r + c)) (Fin (r + c)) O) :
    (bDD (K.map O.subtype)).det = (((K.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : O) : F) := by
  show _ = O.subtype _
  rw [RingHom.map_det]
  rfl

theorem dd_val (hO : ∀ x ∈ O, v x ≤ 1) (hε : ε < 1) {r c : ℕ} {k k' : GL (Fin (r + c)) F}
    (hk : k ∈ GLint O (r + c)) (hk' : k' ∈ GLint O (r + c))
    (hd : ∀ i j, v ((k : Matrix (Fin (r + c)) (Fin (r + c)) F) (Fin.natAdd r i) (Fin.castAdd c j)) ≤ ε)
    (hd' : ∀ i j, v ((k' : Matrix (Fin (r + c)) (Fin (r + c)) F) (Fin.natAdd r i) (Fin.castAdd c j)) ≤ ε) :
    v (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧
    v (bDD (k' : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧
    v ((bDD ((k * k' : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)).det -
      (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det * (bDD (k' : Matrix (Fin (r + c)) (Fin (r + c)) F)).det) ≤ ε := by
  obtain ⟨K, e, hu⟩ := exists_lift hk
  obtain ⟨K', e', hu'⟩ := exists_lift hk'
  have hK : ∀ i j, K (Fin.natAdd r i) (Fin.castAdd c j) ∈ redI v O ε hO := fun i j => by
    have := hd i j
    rw [e] at this
    exact this
  have hK' : ∀ i j, K' (Fin.natAdd r i) (Fin.castAdd c j) ∈ redI v O ε hO := fun i j => by
    have := hd' i j
    rw [e'] at this
    exact this
  obtain ⟨h1, h2, h3⟩ := dd_mod (redI v O ε hO) K K' hK hK' hu hu'
  have em : ((k * k' : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = (K * K').map O.subtype := by
    rw [Units.val_mul, e, e', Matrix.map_mul]
  rw [em, e, e', det_dd_map, det_dd_map, det_dd_map]
  refine ⟨val_eq_one_of_isUnit hO hε _ h1, val_eq_one_of_isUnit hO hε _ h2, ?_⟩
  have h3' : v (((((K * K').submatrix (Fin.natAdd r) (Fin.natAdd r)).det -
      (K.submatrix (Fin.natAdd r) (Fin.natAdd r)).det * (K'.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : O)) : F) ≤ ε := h3
  simpa using h3'

end Val

section Main

theorem lamJ_mul : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (δ : (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → ∀ (r c : ℕ) (k k' : GL (Fin (r + c)) (P.adicCompletion L)), k ∈ parJ (OP P) (piP P : P.adicCompletion L) r c → k' ∈ parJ (OP P) (piP P : P.adicCompletion L) r c → lamJ δ (k * k') = lamJ δ k * lamJ δ k' := by
  intro L _ _ P δ hδ r c k k' hk hk'
  have hO : ∀ x ∈ OP P, Valued.v x ≤ 1 := fun x hx => hx
  have hε : (WithZero.exp (-1 : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπ : Valued.v (piP P : P.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec P
  have small : ∀ {g : GL (Fin (r + c)) (P.adicCompletion L)}, g ∈ parJ (OP P) (piP P : P.adicCompletion L) r c →
      ∀ i j, Valued.v ((g : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) (Fin.natAdd r i) (Fin.castAdd c j)) ≤
        WithZero.exp (-1 : ℤ) := by
    intro g hg i j
    obtain ⟨o, ho, e⟩ := hg.2 i j
    have e' : (g : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) (Fin.natAdd r i) (Fin.castAdd c j) =
        (piP P : P.adicCompletion L) * o := e
    rw [e', map_mul, hπ]
    exact mul_le_of_le_one_right' (hO _ ho)
  obtain ⟨ha, hb, hxy⟩ := dd_val hO hε hk.1 hk'.1 (small hk) (small hk')
  unfold lamJ
  set a := (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).det with hadef
  set b := (bDD (k' : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).det with hbdef
  set x := (bDD ((k * k' : GL (Fin (r + c)) (P.adicCompletion L)) : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).det with hxdef
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hab : Valued.v (a * b) = 1 := by rw [map_mul, ha, hb, one_mul]
  have hx : Valued.v x = 1 := by
    have e : x = (x - a * b) + a * b := by ring
    rw [e, Valuation.map_add_eq_of_lt_right, hab]
    rw [hab]
    exact hxy.trans_lt hε
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx
  have tame := hδ.tame (Units.mk0 x hx0 * (Units.mk0 a ha0 * Units.mk0 b hb0)⁻¹) (by
    show Valued.v _ = 1
    simp [hx, ha, hb]) (by
    have e : x * (a * b)⁻¹ - 1 = (x - a * b) * (a * b)⁻¹ := by field_simp
    simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
    rw [e, map_mul, map_inv₀, hab, inv_one, mul_one]
    exact hxy)
  rw [map_mul, map_inv, mul_inv_eq_one, map_mul] at tame
  simp only [chi0, dif_neg hx0, dif_neg ha0, dif_neg hb0, tame, Units.val_mul]

end Main

end GlobalTheory.Mem.LamMul
end
end

section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.HQStepBlocks

variable {F : Type} [Field F] {r c : ℕ}

theorem submatrix_eq_fromBlocks (x : Matrix (Fin (r + c)) (Fin (r + c)) F) :
    x.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks (bAA x) (bAD x) (bDA x) (bDD x) := by
  ext (i|i) (j|j) <;> simp [bAA, bAD, bDA, bDD]

theorem submatrix_mul' (x y : Matrix (Fin (r + c)) (Fin (r + c)) F) :
    (x * y).submatrix finSumFinEquiv finSumFinEquiv =
      x.submatrix finSumFinEquiv finSumFinEquiv * y.submatrix finSumFinEquiv finSumFinEquiv := by
  rw [Matrix.submatrix_mul_equiv]

theorem blocks_mul (x y : Matrix (Fin (r + c)) (Fin (r + c)) F) :
    bAA (x * y) = bAA x * bAA y + bAD x * bDA y ∧ bAD (x * y) = bAA x * bAD y + bAD x * bDD y ∧
    bDA (x * y) = bDA x * bAA y + bDD x * bDA y ∧ bDD (x * y) = bDA x * bAD y + bDD x * bDD y := by
  have h := submatrix_mul' x y
  rw [submatrix_eq_fromBlocks, submatrix_eq_fromBlocks, submatrix_eq_fromBlocks,
    fromBlocks_multiply, fromBlocks_inj] at h
  exact h

theorem det_eq_of_bDA_eq_zero (x : Matrix (Fin (r + c)) (Fin (r + c)) F) (hx : bDA x = 0) :
    x.det = (bAA x).det * (bDD x).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv x, submatrix_eq_fromBlocks, hx,
    Matrix.det_fromBlocks_zero₂₁]

theorem main : ∀ (F : Type) [Field F] (r c : ℕ) (p q : GL (Fin (r + c)) F), bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 → bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 → bDA ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 ∧ bAA ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bAA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) ∧ bDD ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bDD (q : Matrix (Fin (r + c)) (Fin (r + c)) F) ∧ (p : Matrix (Fin (r + c)) (Fin (r + c)) F).det = (bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det * (bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ∧ bDA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 := by
  intro F _ r c p q hp hq
  obtain ⟨h11, -, h21, h22⟩ := blocks_mul (p : Matrix (Fin (r + c)) (Fin (r + c)) F) (q : Matrix _ _ F)
  refine ⟨?_, ?_, ?_, det_eq_of_bDA_eq_zero _ hp, ?_⟩
  · rw [Units.val_mul, h21, hp, hq]; simp
  · rw [Units.val_mul, h11, hq]; simp
  · rw [Units.val_mul, h22, hp]; simp
  · obtain ⟨k11, -, k21, -⟩ := blocks_mul ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)
      (p : Matrix _ _ F)
    have hone : ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) * (p : Matrix _ _ F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hone, hp, Matrix.mul_zero, add_zero] at k11 k21
    have e11 : bAA (1 : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 := by
      ext i j; simp [bAA, Matrix.one_apply]
    have e21 : bDA (1 : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 := by
      ext i j; simp [bDA, Matrix.one_apply, Fin.ext_iff]; omega
    rw [e11] at k11
    rw [e21] at k21
    have hA : bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bAA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 :=
      mul_eq_one_comm.mp k11.symm
    calc bDA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)
        = bDA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) *
            (bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bAA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)) := by
          rw [hA, Matrix.mul_one]
      _ = 0 := by rw [← Matrix.mul_assoc, ← k21, Matrix.zero_mul]

end GlobalTheory.HQStepBlocks
end

section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.Mem.HD

private theorem lt_one_iff_le_exp_neg_one (g : WithZero (Multiplicative ℤ)) :
    g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
  induction g using WithZero.expRecOn with
  | zero => simp
  | exp a => rw [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]; omega

theorem isLocalAt_adicCompletionIntegers_uniformizer (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) :
    IsLocalAt (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) := by
  have hv : Valued.v ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L)
      = WithZero.exp (-1 : ℤ) := unif_spec P
  have hne : ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) ≠ 0 := Units.ne_zero _
  have mem : ∀ x : P.adicCompletion L, x ∈ OP P ↔ Valued.v x ≤ 1 := fun x =>
    HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 L) (K := L) (v := P)
  have hexp : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp (-1 : ℤ) :=
    zero_lt_iff.2 WithZero.exp_ne_zero
  refine ⟨?_, ?_⟩
  · intro h
    have h1 := (mem _).1 h
    rw [map_inv₀, hv, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega
  · intro x hx hnot
    have hx1 : Valued.v x ≤ 1 := (mem x).1 hx
    have hx_eq : Valued.v x = 1 := by
      by_contra hne1
      have hlt : Valued.v x < 1 := lt_of_le_of_ne hx1 hne1
      have hle := (lt_one_iff_le_exp_neg_one _).1 hlt
      refine hnot (((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L)⁻¹ * x) ?_ ?_
      · rw [mem, map_mul, map_inv₀, hv]
        exact inv_mul_le_one_of_le₀ hle hexp.le
      · rw [mul_inv_cancel_left₀ hne]
    rw [mem, map_inv₀, hx_eq, inv_one]

end GlobalTheory.Mem.HD
end

section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.SphCyclic

variable {L : Type} [Field L] [NumberField L] {P : HeightOneSpectrum (𝓞 L)}

theorem nrm_eq {nrm : AbsoluteValue (P.adicCompletion L) ℝ} (h : IsNrm P nrm) (x : (P.adicCompletion L)ˣ) :
    nrm x = (qP P : ℝ) ^ (WithZero.log (Valued.v (x : P.adicCompletion L))) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective L P (WithZero.exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero (hπ.symm.trans (map_zero _))
  set m := WithZero.log (Valued.v (x : P.adicCompletion L)) with hm
  have hx : Valued.v (x : P.adicCompletion L) = WithZero.exp m := (WithZero.exp_log (by simp)).symm
  have h1 : nrm π = (qP P : ℝ)⁻¹ := (h (Units.mk0 π hπ0)).2 hπ
  have h2 := (h (x * (Units.mk0 π hπ0) ^ m)).1 (by
    show Valued.v ((x * (Units.mk0 π hπ0) ^ m : (P.adicCompletion L)ˣ) : P.adicCompletion L) = 1
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_mk0,
      hπ, hx, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp)
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_mk0, h1, _root_.inv_zpow] at h2
  exact eq_of_div_eq_one h2

theorem exists_isUnrM : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (nrm : AbsoluteValue (P.adicCompletion L) ℝ), IsNrm P nrm → ∀ (ν : ℕ → (P.adicCompletion L)ˣ →* ℂˣ), (∀ i, IsNu P (ν i)) → ∀ r t j : ℕ, 1 ≤ t → ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (ρ : GL (Fin r) (P.adicCompletion L) × GL (Fin (j * t)) (P.adicCompletion L) →* (V ≃ₗᵢ[ℂ] V)), IsUnrM (OP P) nrm r (j * t) (satC nrm ν t (j * t)) ρ := by
  intro L _ _ P nrm hn ν hν r t j _
  letI := GlobalTheory.LocalData.complRel P
  haveI := GlobalTheory.LocalData.isLocalField P
  haveI : (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (P.adicCompletion L))
    (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ)))
  have hK : GlobalTheory.SplitWeil.KO (P.adicCompletion L) (Fin (j * t)) = GLint (OP P) (j * t) := by
    ext g
    rw [GlobalTheory.SplitFlip.mem_KO_iff]
    simp only [he.le_one_iff_le_one, Valuation.mem_integer_iff]
    exact Iff.rfl
  obtain ⟨V, _, _, ρ, h1, h2, v, h3, h4, φ, κ, h5, h6, h7, h8, h9, h10⟩ :=
    @exists_rep_eqBlocks (P.adicCompletion L) _ _ _ _ j t (instMeasGL _) (instBorelGL _) (fun a => ν (a + 1))
      (fun a => (hν _).unitary) (fun a x hx => (hν _).unr x (he.eq_one_iff_eq_one.1 hx))
      (GL (Fin r) (P.adicCompletion L)) _ _
  rw [hK] at h4 h6 h9 h10
  refine ⟨V, inferInstance, inferInstance, ρ, h1, h2, v, h3, fun k₁ _ => h4 k₁, φ, κ, fun b hb k hk => ?_,
    h8.toIsMulLeftInvariant, h9, h10⟩
  have hd : ∀ x, b.val x x ≠ 0 := by
    have := b.det_ne_zero
    rw [det_of_upperTriangular hb] at this
    exact fun x => Finset.prod_ne_zero_iff.1 this x (Finset.mem_univ _)
  have h11 := h5 b (fun x => Units.mk0 _ (hd x)) (fun x y h => hb h) (fun _ => rfl) 1
  rw [mul_one, h7, mul_one] at h11
  rw [h6 b k hk, h11]
  refine Finset.prod_congr rfl fun x _ => ?_
  have h12 : GlobalTheory.SplitWeil.nabs (P.adicCompletion L) (Units.mk0 _ (hd x)) = nrm (b.val x x) :=
    (GlobalTheory.LGrp.BorelCompletion.nabs_completion P _).trans (nrm_eq hn (Units.mk0 _ (hd x))).symm
  rw [h12, satC, chi0, dite_eq_right (hd x), mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (nrm.pos (hd x))]
  congr 3
  have : ((x : ℕ) : ℝ) = (((x : ℕ) % t : ℕ) : ℝ) + (((x : ℕ) / t : ℕ) : ℝ) * t := by
    exact_mod_cast (Nat.mod_add_div' (x : ℕ) t).symm
  linarith

end GlobalTheory.SphCyclic
end

section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.ParahoricTopo

theorem isClopen_OP {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) :
    IsClopen ((OP P : Subring (P.adicCompletion L)) : Set (P.adicCompletion L)) :=
  Valued.isClopen_valuationSubring (P.adicCompletion L)

theorem isClopen_mulSet {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))
    (ϖ : P.adicCompletion L) (hϖ : ϖ ≠ 0) :
    IsClopen {y : P.adicCompletion L | ∃ o ∈ OP P, y = ϖ * o} := by
  have e : {y : P.adicCompletion L | ∃ o ∈ OP P, y = ϖ * o} =
      (fun y => ϖ⁻¹ * y) ⁻¹' ((OP P : Subring (P.adicCompletion L)) : Set (P.adicCompletion L)) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨o, ho, rfl⟩
      rwa [← mul_assoc, inv_mul_cancel₀ hϖ, one_mul]
    · intro h
      exact ⟨_, h, by rw [← mul_assoc, mul_inv_cancel₀ hϖ, one_mul]⟩
  rw [e]
  exact (isClopen_OP P).preimage (continuous_const.mul continuous_id)

theorem isOpen_isCompact_parJ : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (r c : ℕ), IsOpen (parJ (OP P) (piP P : P.adicCompletion L) r c) ∧ IsCompact (parJ (OP P) (piP P : P.adicCompletion L) r c) := by
  intro L _ _ P r c
  letI := GlobalTheory.LocalData.complRel P
  haveI := GlobalTheory.LocalData.isLocalField P
  haveI : (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (P.adicCompletion L))
    (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ)))
  have hK : GlobalTheory.SplitWeil.KO (P.adicCompletion L) (Fin (r + c)) = GLint (OP P) (r + c) := by
    ext g
    rw [GlobalTheory.SplitFlip.mem_KO_iff]
    simp only [he.le_one_iff_le_one, Valuation.mem_integer_iff]
    exact Iff.rfl
  have hS := isClopen_mulSet P (piP P : P.adicCompletion L) (Units.ne_zero _)
  set B : Set (GL (Fin (r + c)) (P.adicCompletion L)) :=
    {k | bDA (k : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) ∈
      IIset (t := c) (a := r) (OP P) (piP P : P.adicCompletion L)} with hB
  have hBe : B = ⋂ i : Fin c, ⋂ j : Fin r,
      (fun k : GL (Fin (r + c)) (P.adicCompletion L) =>
        (k : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) (Fin.natAdd r i) (Fin.castAdd c j)) ⁻¹'
        {y : P.adicCompletion L | ∃ o ∈ OP P, y = (piP P : P.adicCompletion L) * o} := by
    ext k
    simp only [hB, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, IIset, bDA, Matrix.submatrix_apply]
  have hcont : ∀ (i : Fin (r + c)) (j : Fin (r + c)), Continuous fun k : GL (Fin (r + c)) (P.adicCompletion L) =>
      (k : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) i j := fun i j =>
    (Units.continuous_val (M := Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).matrix_elem i j
  have hBc : IsClopen B := by
    rw [hBe]
    exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j => hS.preimage (hcont _ _)
  have hP : parJ (OP P) (piP P : P.adicCompletion L) r c =
      (GlobalTheory.SplitWeil.KO (P.adicCompletion L) (Fin (r + c)) : Set _) ∩ B := by
    rw [hK]; rfl
  rw [hP]
  exact ⟨GlobalTheory.SplitFlip.isOpen_KO.inter hBc.isOpen, GlobalTheory.SplitFlip.isCompact_KO.inter_right hBc.isClosed⟩

end GlobalTheory.ParahoricTopo
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaFunction_eq_unitSmul_of_diagonalCoefficient_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f f' : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → (∀ w, ∫ x in 𝓕, heisO ψ S T w f' x * star (f' x) ∂μ = ∫ x in 𝓕, heisO ψ S T w f x * star (f x) ∂μ) → ∃ c : ℂ, ‖c‖ = 1 ∧ f' = c • f := by
  first | exact @GlobalTheory.ThetaCoefficient.exists_unit_smul_of_coefficient_eq | exact GlobalTheory.ThetaCoefficient.exists_unit_smul_of_coefficient_eq | (intros; apply GlobalTheory.ThetaCoefficient.exists_unit_smul_of_coefficient_eq <;> assumption)
end
