module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
import Formalism.LocalRingCardinality.DataTheta
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped Matrix ComplexConjugate nonZeroDivisors
open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.WEq

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

local notation "hermF" => ReciprocityTheory.ChartRestriction.G.FD.herm
local notation "ccF" => ReciprocityTheory.ChartRestriction.G.FD.cc

def dSgn (r k : ℕ) : Matrix (Fin r) (Fin r) E := Matrix.diagonal fun a => if (a : ℕ) < k then 1 else -1

theorem dSgn_hermF (r k : ℕ) (a b : Fin r) : ccF (dSgn (E := E) r k a b) = dSgn r k b a := by
  by_cases h : a = b
  · subst h
    simp only [dSgn, Matrix.diagonal_apply_eq, ReciprocityTheory.ChartRestriction.G.FD.cc]
    split_ifs <;> simp
  · simp [dSgn, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h), ReciprocityTheory.ChartRestriction.G.FD.cc]

theorem dSgn_det (k : ℕ) : (dSgn (E := E) r k).det ≠ 0 := by
  rw [dSgn, Matrix.det_diagonal, Finset.prod_ne_zero_iff]
  intro a _
  split_ifs <;> norm_num

theorem mem_one_iff_isIntegral (z : E) : z ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ IsIntegral ℤ z := by
  rw [FractionalIdeal.mem_one_iff, IsIntegralClosure.isIntegral_iff (A := 𝓞 E)]

theorem cc_isIntegral {z : E} (h : IsIntegral ℤ z) : IsIntegral ℤ (cc z) :=
  h.map (IsCMField.complexConj E : E →+* E).toIntAlgHom

theorem herm_diag (d : Fin r → E) (x y : Fin r → E) :
    hermF (Matrix.diagonal d) x y = ∑ a, x a * d a * ccF (y a) := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem mem_stdLat_iff_forall_isIntegral (n : ℕ) (x : Fin n → E) :
    x ∈ GlobalTheory.InertWitt.stdLat E n ↔ ∀ i, IsIntegral ℤ (x i) := by
  constructor
  · rintro ⟨w, rfl⟩ i
    exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mpr ⟨w i, rfl⟩
  · intro h
    choose w hw using fun i => (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp (h i)
    exact ⟨w, funext fun i => hw i⟩

private theorem isIntegral_ite_one_neg_one (k : ℕ) (a : Fin r) : IsIntegral ℤ (if (a : ℕ) < k then (1 : E) else -1) := by
  split_ifs
  · exact isIntegral_one
  · exact isIntegral_one.neg

theorem mod_std (k : ℕ) (x : Fin r → E) : x ∈ GlobalTheory.InertWitt.stdLat E r ↔
    ∀ y ∈ GlobalTheory.InertWitt.stdLat E r, hermF (dSgn r k) x y ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [mem_stdLat_iff_forall_isIntegral]
  constructor
  · intro hx y hy
    rw [mem_stdLat_iff_forall_isIntegral] at hy
    rw [mem_one_iff_isIntegral, dSgn, herm_diag]
    exact IsIntegral.sum _ fun a _ => ((hx a).mul (isIntegral_ite_one_neg_one k a)).mul (cc_isIntegral (hy a))
  · intro h i
    have hy : (Pi.single i 1 : Fin r → E) ∈ GlobalTheory.InertWitt.stdLat E r := by
      rw [mem_stdLat_iff_forall_isIntegral]
      intro j
      by_cases hj : j = i
      · subst hj; simpa using isIntegral_one
      · simpa [Pi.single_apply, hj] using isIntegral_zero
    have h1 := h _ hy
    rw [mem_one_iff_isIntegral, dSgn, herm_diag] at h1
    have h2 : IsIntegral ℤ (x i * (if (i : ℕ) < k then (1 : E) else -1)) := by
      convert h1 using 1
      rw [Finset.sum_eq_single i]
      · simp [ReciprocityTheory.ChartRestriction.G.FD.cc]
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · simp
    have h3 := h2.mul (isIntegral_ite_one_neg_one k i)
    have h4 : x i * (if (i : ℕ) < k then (1 : E) else -1) * (if (i : ℕ) < k then (1 : E) else -1) = x i := by
      split_ifs <;> ring
    rwa [h4] at h3

def ext {k : ℕ} (hr : 2 * k = r) (u : Fin k → E) : Fin r → E := fun a =>
  if h : (a : ℕ) < k then u ⟨a, h⟩ else u ⟨a - k, by have := a.isLt; omega⟩

def extL {k : ℕ} (hr : 2 * k = r) : (Fin k → E) →ₗ[E] (Fin r → E) where
  toFun := ext hr
  map_add' u v := by funext a; simp only [ext, Pi.add_apply]; split_ifs <;> rfl
  map_smul' c u := by funext a; simp only [ext, Pi.smul_apply, RingHom.id_apply]; split_ifs <;> rfl

theorem extL_injective {k : ℕ} (hr : 2 * k = r) : Function.Injective (extL (E := E) hr) := by
  intro u v h
  funext i
  have := congrFun h ⟨i, by omega⟩
  simpa [extL, ext, i.isLt] using this

theorem herm_ext {k : ℕ} (hr : 2 * k = r) (u v : Fin k → E) :
    hermF (dSgn r k) (ext hr u) (ext hr v) = 0 := by
  rw [dSgn, herm_diag]
  subst hr
  rw [← Equiv.sum_comp (finCongr (two_mul k).symm), Fin.sum_univ_add]
  simp [ext, Matrix.diagonal_apply_eq]

end Gen

end PositivityTheory.Rg.Sw.Glob.WEq
end
end

section

open Matrix NumberField GlobalTheory.Inertia
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.WLt

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev hf {n : Type} [Fintype n] (G : Matrix n n E) (x y : n → E) : E := x ⬝ᵥ G *ᵥ (FD.cc ∘ y)

theorem cc_mulVec {n m : Type} [Fintype n] [Fintype m] (P : Matrix n m E) (y : m → E) :
    FD.cc ∘ (P *ᵥ y) = P.map FD.cc *ᵥ (FD.cc ∘ y) := by
  funext i

  simp [mulVec, dotProduct, FD.cc, map_sum, map_mul]

theorem hf_congr {n m : Type} [Fintype n] [Fintype m] (G : Matrix n n E) (P : Matrix n m E) (x y : m → E) :
    hf (Pᵀ * G * P.map FD.cc) x y = hf G (P *ᵥ x) (P *ᵥ y) := by
  simp only [hf]
  rw [cc_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem hf_submatrix {n m : Type} [Fintype n] [Fintype m] (G : Matrix n n E) (e : m ≃ n) (x y : m → E) :
    hf (G.submatrix e e) x y = hf G (x ∘ e.symm) (y ∘ e.symm) := by
  simp only [hf, submatrix_mulVec_equiv, Function.comp_def, Equiv.symm_symm]
  rw [dotProduct, dotProduct, ← Equiv.sum_comp e (fun i => x (e.symm i) * _)]
  simp

theorem hf_symm {n : Type} [Fintype n] {G : Matrix n n E} (hG : ∀ a b, FD.cc (G a b) = G b a) (x y : n → E) :
    hf G y x = FD.cc (hf G x y) := by
  have hc : ∀ s : Finset n, ∀ f : n → E, FD.cc (∑ i ∈ s, f i) = ∑ i ∈ s, FD.cc (f i) :=
    fun s f => map_sum (IsCMField.complexConj E) f s
  have hm : ∀ a b : E, FD.cc (a * b) = FD.cc a * FD.cc b := fun a b => map_mul (IsCMField.complexConj E) a b
  simp only [hf, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, hc, hm, cc_cc, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hf_add_left {n : Type} [Fintype n] (G : Matrix n n E) (x x' y : n → E) :
    hf G (x + x') y = hf G x y + hf G x' y := by simp [hf, add_dotProduct]

theorem hf_smul_left {n : Type} [Fintype n] (G : Matrix n n E) (a : E) (x y : n → E) :
    hf G (a • x) y = a * hf G x y := by simp [hf, smul_dotProduct]

theorem hf_add_right {n : Type} [Fintype n] (G : Matrix n n E) (x y y' : n → E) :
    hf G x (y + y') = hf G x y + hf G x y' := by
  have h : FD.cc ∘ (y + y') = FD.cc ∘ y + FD.cc ∘ y' :=
    funext fun i => map_add (IsCMField.complexConj E) (y i) (y' i)
  simp only [hf, h, mulVec_add, dotProduct_add]

theorem hf_smul_right {n : Type} [Fintype n] (G : Matrix n n E) (a : E) (x y : n → E) :
    hf G x (a • y) = FD.cc a * hf G x y := by
  have h : FD.cc ∘ (a • y) = FD.cc a • (FD.cc ∘ y) :=
    funext fun i => map_mul (IsCMField.complexConj E) a (y i)
  simp only [hf, h, mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem exists_isotropic_of_three_le_of_indefinite {m : ℕ} (G : Matrix (Fin m) (Fin m) E) (hG : ∀ a b, FD.cc (G a b) = G b a)
    (hd : G.det ≠ 0) (h3 : 3 ≤ m)
    (hs : ∀ τ : E →+* ℂ, 1 ≤ posIndex (G.map τ) ∧ 1 ≤ negIndex (G.map τ)) :
    ∃ z : Fin m → E, z ≠ 0 ∧ hf G z z = 0 := by
  obtain ⟨P, d, hP, hPd, hdr, hd0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal_herm hG
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  have hsig : ∀ τ : E →+* ℂ, (∃ i, 0 < (τ (d i)).re) ∧ ∃ j, (τ (d j)).re < 0 := by
    intro τ
    obtain ⟨h1, h2⟩ := hs τ
    rw [posIndex_map_eq_card_of_congr_diagonal τ hP hPd] at h1
    have hPd' : Pᵀ * (-G) * P.map FD.cc = diagonal (-d) := by
      rw [Matrix.mul_neg, Matrix.neg_mul, hPd, diagonal_neg]
      rfl
    have hneg : (-G).map τ = -(G.map τ) := by
      ext i j
      simp
    have h2' : 1 ≤ posIndex ((-G).map τ) := by
      rwa [hneg, posIndex_neg]
    rw [posIndex_map_eq_card_of_congr_diagonal τ hP hPd'] at h2'
    obtain ⟨i, hi⟩ := Finset.card_pos.mp h1
    obtain ⟨j, hj⟩ := Finset.card_pos.mp h2'
    refine ⟨⟨i, by simpa using hi⟩, ⟨j, ?_⟩⟩
    simpa using hj
  obtain ⟨z, hz, hz0⟩ := iso_diag d (by omega) hdr (hd0 hd) hsig
  refine ⟨P *ᵥ z, fun h => hz (eq_zero_of_mulVec_eq_zero hP h), ?_⟩
  rw [← hf_congr, hPd]
  exact hz0

theorem iso_gen {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n E) (hG : ∀ a b, FD.cc (G a b) = G b a)
    (hd : G.det ≠ 0) (h3 : 3 ≤ Fintype.card n)
    (hs : ∀ τ : E →+* ℂ, 1 ≤ posIndex (G.map τ) ∧ 1 ≤ negIndex (G.map τ)) :
    ∃ z : n → E, z ≠ 0 ∧ hf G z z = 0 := by
  obtain ⟨e⟩ : Nonempty (Fin (Fintype.card n) ≃ n) := ⟨(Fintype.equivFin n).symm⟩
  obtain ⟨z, hz, hz0⟩ := exists_isotropic_of_three_le_of_indefinite (G.submatrix e e) (fun a b => hG _ _)
    (by rwa [det_submatrix_equiv_self]) h3
    (fun τ => by rw [← submatrix_map, posIndex_submatrix_equiv, negIndex_submatrix_equiv]; exact hs τ)
  refine ⟨z ∘ e.symm, ?_, ?_⟩
  · intro h
    apply hz
    funext i
    simpa using congrFun h (e i)
  · rw [← hf_submatrix]
    exact hz0

end PositivityTheory.Rg.Sw.Glob.WLt

end
end

section

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

variable {n : ℕ}

lemma jj_mul_jj : JJ n * JJ n = -1 := by
  have h : JJ n * JJ n = fromBlocks (-1) (-0) (-0) (-1) := by
    simp [JJ, fromBlocks_multiply]
  rw [h, ← fromBlocks_neg, fromBlocks_one]

lemma conj_jj {Y : M2 n} (hU : IsUnit Y) (hG : Yᴴ * JJ n * Y = JJ n) : Y * JJ n * Yᴴ = JJ n := by
  have h1 : (Y * JJ n * Yᴴ * JJ n) * Y = (-1) * Y := by
    calc (Y * JJ n * Yᴴ * JJ n) * Y = Y * JJ n * (Yᴴ * JJ n * Y) := by simp only [Matrix.mul_assoc]
      _ = Y * (JJ n * JJ n) := by rw [hG, Matrix.mul_assoc]
      _ = (-1) * Y := by rw [jj_mul_jj]; simp
  have h2 : Y * JJ n * Yᴴ * JJ n = -1 := hU.mul_left_inj.mp h1
  calc Y * JJ n * Yᴴ = (Y * JJ n * Yᴴ * JJ n) * (-JJ n) := by
        simp only [Matrix.mul_assoc, Matrix.mul_neg, jj_mul_jj, neg_neg, Matrix.mul_one]
    _ = JJ n := by rw [h2]; simp

lemma rows_rel {A B C Dm : Matrix (Fin n) (Fin n) ℂ}
    (h : fromBlocks A B C Dm * JJ n * (fromBlocks A B C Dm)ᴴ = JJ n) :
    C * Dmᴴ = Dm * Cᴴ ∧ A * Dmᴴ - B * Cᴴ = 1 := by
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.mul_zero, add_zero,
    zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul] at h
  obtain ⟨-, h12, -, h22⟩ := fromBlocks_inj.mp h
  exact ⟨(neg_add_eq_zero.mp h22).symm, by rw [sub_eq_neg_add]; exact h12⟩

lemma det_S_ne {A B C Dm : Matrix (Fin n) (Fin n) ℂ} (h : A * Dmᴴ - B * Cᴴ = 1) :
    (C * Cᴴ + Dm * Dmᴴ).det ≠ 0 := by
  intro hd
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have e : star v ⬝ᵥ ((C * Cᴴ + Dm * Dmᴴ) *ᵥ v) =
      star (Cᴴ *ᵥ v) ⬝ᵥ (Cᴴ *ᵥ v) + star (Dmᴴ *ᵥ v) ⬝ᵥ (Dmᴴ *ᵥ v) := by
    rw [star_mulVec, star_mulVec, conjTranspose_conjTranspose, conjTranspose_conjTranspose, ← dotProduct_mulVec,
      ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, ← dotProduct_add, ← add_mulVec]
  rw [hv, dotProduct_zero] at e
  have n1 := dotProduct_star_self_nonneg (Cᴴ *ᵥ v)
  have n2 := dotProduct_star_self_nonneg (Dmᴴ *ᵥ v)
  obtain ⟨z1, z2⟩ := (add_eq_zero_iff_of_nonneg n1 n2).mp e.symm
  have hC : Cᴴ *ᵥ v = 0 := dotProduct_star_self_eq_zero.mp z1
  have hD : Dmᴴ *ᵥ v = 0 := dotProduct_star_self_eq_zero.mp z2
  have : (A * Dmᴴ - B * Cᴴ) *ᵥ v = 0 := by
    rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hC, hD, mulVec_zero, mulVec_zero, sub_zero]
  rw [h, one_mulVec] at this
  exact hv0 this

lemma first_cayley_block_mul_conjTranspose {g : M2 n} (h1 : g * gᴴ = 1) (h2 : g * JJ n * gᴴ = JJ n) : u1 g * (u1 g)ᴴ = 1 := by
  have hg : g = fromBlocks g.toBlocks₁₁ g.toBlocks₁₂ g.toBlocks₂₁ g.toBlocks₂₂ := (fromBlocks_toBlocks g).symm
  have hr := (rows_rel (A := g.toBlocks₁₁) (B := g.toBlocks₁₂) (by rw [← hg]; exact h2)).1
  have hn : g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ = 1 := by
    have h := h1
    rw [hg, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one] at h
    exact (fromBlocks_inj.mp h).2.2.2
  have hs : star Complex.I = -Complex.I := by simp
  have hI' : -Complex.I * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
  have key : u1 g * (u1 g)ᴴ = g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ := by
    rw [u1, conjTranspose_add, conjTranspose_smul, hs, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hI', one_smul, hr]
    rw [neg_smul]
    abel
  rw [key, hn]

lemma norm_det_first_cayley_block_unitary {g : M2 n} (h1 : g * gᴴ = 1) (h2 : g * JJ n * gᴴ = JJ n) : ‖(u1 g).det‖ = 1 := by
  have h := congrArg (fun M => ‖Matrix.det M‖) (first_cayley_block_mul_conjTranspose h1 h2)
  simp only [det_mul, det_conjTranspose, det_one, norm_mul, norm_star, norm_one] at h
  nlinarith [norm_nonneg (u1 g).det]

theorem hLoc_mul (q k₀ : GR n) (hq : (mR q).toBlocks₂₁ = 0) (hk : InK (mR k₀)) :
    hLoc (q * k₀) = ‖(mR q).toBlocks₁₁.det‖ ^ 2 := by
  have hm : mR (q * k₀) = mR q * mR k₀ := rfl
  have hQG : InG (mR q) := q.2
  obtain ⟨A, B, Dd, hQ⟩ : ∃ A B Dd : Matrix (Fin n) (Fin n) ℂ, mR q = fromBlocks A B 0 Dd :=
    ⟨(mR q).toBlocks₁₁, (mR q).toBlocks₁₂, (mR q).toBlocks₂₂, by
      conv_lhs => rw [← fromBlocks_toBlocks (mR q)]
      rw [hq]⟩
  have hAD : Aᴴ * Dd = 1 := by
    have h := hQG
    unfold InG at h
    rw [hQ] at h
    simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, conjTranspose_zero, neg_zero] at h
    exact (fromBlocks_inj.mp h).2.1
  have hK1 : mR k₀ * (mR k₀)ᴴ = 1 := mul_eq_one_comm.mp hk.2
  have hK2 : mR k₀ * JJ n * (mR k₀)ᴴ = JJ n := conj_jj k₀.1.isUnit hk.1
  have hu : u1 (mR q * mR k₀) = Dd * u1 (mR k₀) := by
    rw [hQ]
    conv_lhs => rw [← fromBlocks_toBlocks (mR k₀)]
    simp only [u1, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
      Matrix.mul_add, Matrix.mul_smul]
  have hdet : ‖A.det‖ * ‖Dd.det‖ = 1 := by
    have h := congrArg (fun M => ‖Matrix.det M‖) hAD
    simpa only [det_mul, det_conjTranspose, norm_mul, norm_star, det_one, norm_one] using h
  have hA0 : ‖A.det‖ ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hdet; exact zero_ne_one hdet
  have hDd : ‖Dd.det‖ = 1 / ‖A.det‖ := eq_one_div_of_mul_eq_one_right hdet
  unfold hLoc
  rw [hm, hu, det_mul, norm_mul, norm_det_first_cayley_block_unitary hK1 hK2, mul_one, hQ, toBlocks_fromBlocks₁₁, hDd, one_div, inv_pow,
    inv_inv]

lemma exists_normalizer {S : Matrix (Fin n) (Fin n) ℂ} (hH : S.IsHermitian) (hP : S.PosSemidef)
    (hd : S.det ≠ 0) : ∃ T : Matrix (Fin n) (Fin n) ℂ, T * S * Tᴴ = 1 := by
  classical
  have hpos : ∀ i, 0 < hH.eigenvalues i := by
    intro i
    have h0 : 0 ≤ hH.eigenvalues i := hP.eigenvalues_nonneg i
    have hne : hH.eigenvalues i ≠ 0 := by
      intro h
      apply hd
      rw [hH.det_eq_prod_eigenvalues]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h])
    exact lt_of_le_of_ne h0 (Ne.symm hne)
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin n) (Fin n) ℂ, U = (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) :=
    ⟨_, rfl⟩
  have hUU : star U * U = 1 := by
    rw [hU, ← Unitary.coe_star]; exact Unitary.coe_star_mul_self _
  have hspec : S = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [hU]; exact h
  obtain ⟨Dm, hDm⟩ : ∃ Dm : Matrix (Fin n) (Fin n) ℂ,
      Dm = diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) := ⟨_, rfl⟩
  refine ⟨Dm * star U, ?_⟩
  have hTh : (Dm * star U)ᴴ = U * Dm := by
    rw [conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose, hDm, diagonal_conjTranspose]
    congr 2
    funext i
    simp
  rw [hTh, hspec]
  calc Dm * star U * (U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U) * (U * Dm)
      = Dm * (star U * U) * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * (star U * U) * Dm := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [hUU, Matrix.mul_one, Matrix.mul_one, hDm, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      have hl := hpos i
      have hs : Real.sqrt (hH.eigenvalues i) ^ 2 = hH.eigenvalues i := Real.sq_sqrt hl.le
      simp only [Function.comp_apply]
      have e : (RCLike.ofReal (hH.eigenvalues i) : ℂ) = ((hH.eigenvalues i : ℝ) : ℂ) := rfl
      rw [e, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
      congr 1
      rw [mul_comm ((Real.sqrt (hH.eigenvalues i))⁻¹) (hH.eigenvalues i), mul_assoc, ← sq, inv_pow, hs,
        mul_inv_cancel₀ hl.ne']

theorem locIwasawa (y : GR n) : ∃ q k₀ : GR n, y = q * k₀ ∧ (mR q).toBlocks₂₁ = 0 ∧ InK (mR k₀) ∧
    hLoc y = ‖(mR q).toBlocks₁₁.det‖ ^ 2 := by
  classical
  obtain ⟨A, B, C, Dm, hY⟩ : ∃ A B C Dm : Matrix (Fin n) (Fin n) ℂ, mR y = fromBlocks A B C Dm :=
    ⟨_, _, _, _, (fromBlocks_toBlocks _).symm⟩
  have hYG : InG (mR y) := y.2
  have hYJ : mR y * JJ n * (mR y)ᴴ = JJ n := conj_jj y.1.isUnit hYG
  rw [hY] at hYJ
  obtain ⟨hCD, hAB⟩ := rows_rel hYJ
  have hSH : (C * Cᴴ + Dm * Dmᴴ).IsHermitian :=
    (isHermitian_mul_conjTranspose_self C).add (isHermitian_mul_conjTranspose_self Dm)
  have hSP : (C * Cᴴ + Dm * Dmᴴ).PosSemidef :=
    (posSemidef_self_mul_conjTranspose C).add (posSemidef_self_mul_conjTranspose Dm)
  obtain ⟨T, hT⟩ := exists_normalizer hSH hSP (det_S_ne hAB)
  have hN : (T * C) * (T * C)ᴴ + (T * Dm) * (T * Dm)ᴴ = 1 := by
    rw [← hT, conjTranspose_mul, conjTranspose_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have hI' : (T * C) * (T * Dm)ᴴ = (T * Dm) * (T * C)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc C, hCD, Matrix.mul_assoc]
  have hBL : C * (T * Dm)ᴴ = Dm * (T * C)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, ← Matrix.mul_assoc, hCD, Matrix.mul_assoc]
  obtain ⟨C', hC'⟩ : ∃ C' : Matrix (Fin n) (Fin n) ℂ, C' = T * C := ⟨_, rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D' : Matrix (Fin n) (Fin n) ℂ, D' = T * Dm := ⟨_, rfl⟩
  rw [← hC', ← hD'] at hN hI' hBL
  obtain ⟨K0, hK0⟩ : ∃ K0 : M2 n, K0 = fromBlocks D' (-C') C' D' := ⟨_, rfl⟩
  have hKK : K0 * K0ᴴ = 1 := by
    rw [hK0, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one]
    simp only [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    rw [fromBlocks_inj]
    refine ⟨by rw [add_comm]; exact hN, by rw [hI']; exact add_neg_cancel _, by rw [hI']; exact add_neg_cancel _, hN⟩
  have hKK' : K0ᴴ * K0 = 1 := mul_eq_one_comm.mp hKK
  have hJK : JJ n * K0 = K0 * JJ n := by
    rw [hK0]
    simp [JJ, fromBlocks_multiply]
  have hKG : K0ᴴ * JJ n * K0 = JJ n := by
    rw [Matrix.mul_assoc, hJK, ← Matrix.mul_assoc, hKK', Matrix.one_mul]
  let u : (M2 n)ˣ := ⟨K0, K0ᴴ, hKK, hKK'⟩
  let kG : GR n := ⟨u, hKG⟩
  have hkK : InK (mR kG) := ⟨hKG, hKK'⟩
  obtain ⟨q, hq⟩ : ∃ q : GR n, q = y * kG⁻¹ := ⟨_, rfl⟩
  have hyq : y = q * kG := by rw [hq, inv_mul_cancel_right]
  have hmq : mR q = mR y * K0ᴴ := by rw [hq]; rfl
  have h21 : (mR q).toBlocks₂₁ = 0 := by
    rw [hmq, hY, hK0, fromBlocks_conjTranspose, fromBlocks_multiply, toBlocks_fromBlocks₂₁, conjTranspose_neg,
      Matrix.mul_neg, hBL, add_neg_cancel]
  refine ⟨q, kG, hyq, h21, hkK, ?_⟩
  rw [hyq]
  exact hLoc_mul q kG h21 hkK

end PositivityTheory.Rg.Sw.Glob
end
end
