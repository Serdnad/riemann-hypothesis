module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SurjOfIndep
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipBasis
public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.ColsDim
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle008
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle029
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ} (ε : Fin n → Bool)

def frm3 (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Fin r ⊕ (Fin r ⊕ Unit) → Fin n → ℂ :=
  Sum.elim e (Sum.elim f (fun _ => z))

structure Hyp (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (T : ℂ) : Prop where
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0
  ff : ∀ a b, hJ ε (f a) (f b) = 0
  ez : ∀ a, hJ ε (e a) z = 0
  fz : ∀ a, hJ ε (f a) z = 0
  zz : hJ ε z z = -T

theorem Hyp.fe {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℂ} (h : Hyp ε e f z T) (a b : Fin r) :
    hJ ε (f a) (e b) = if a = b then 1 else 0 := by
  rw [hJ_conj, h.ef]; by_cases hab : b = a
  · subst hab; simp
  · rw [if_neg hab, if_neg (Ne.symm hab), map_zero]

theorem Hyp.ze {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℂ} (h : Hyp ε e f z T) (a : Fin r) :
    hJ ε z (e a) = 0 := by rw [hJ_conj, h.ez, map_zero]

theorem Hyp.zf {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℂ} (h : Hyp ε e f z T) (a : Fin r) :
    hJ ε z (f a) = 0 := by rw [hJ_conj, h.fz, map_zero]

theorem gram_eq_of_hyp {e f e' f' : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ} {T : ℂ}
    (h : Hyp ε e f z T) (h' : Hyp ε e' f' z' T) (i j : Fin r ⊕ (Fin r ⊕ Unit)) :
    hJ ε (frm3 e f z i) (frm3 e f z j) = hJ ε (frm3 e' f' z' i) (frm3 e' f' z' j) := by
  rcases i with a | a | _ <;> rcases j with b | b | _ <;>
    simp only [frm3, Sum.elim_inl, Sum.elim_inr, h.ee, h'.ee, h.ef, h'.ef, h.ff, h'.ff, h.ez, h'.ez, h.fz, h'.fz,
      h.zz, h'.zz, h.fe, h'.fe, h.ze, h'.ze, h.zf, h'.zf]

theorem gram_nd_of_hyp {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℂ} (hT : T ≠ 0) (h : Hyp ε e f z T) :
    (Matrix.of fun i j => hJ ε (frm3 e f z i) (frm3 e f z j)).det ≠ 0 := by
  intro hdet
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hw0
  have row : ∀ i, ∑ j, hJ ε (frm3 e f z i) (frm3 e f z j) * w j = 0 := fun i => by
    have := congrFun hw i
    simpa [mulVec, dotProduct] using this
  funext i
  rcases i with a | a | u
  · have := row (Sum.inr (Sum.inl a))
    simpa [Fintype.sum_sum_type, frm3, h.fe, h.ff, h.fz] using this
  · have := row (Sum.inl a)
    simpa [Fintype.sum_sum_type, frm3, h.ee, h.ef, h.ez] using this
  · have := row (Sum.inr (Sum.inr u))
    simp [Fintype.sum_sum_type, frm3, h.ze, h.zf, h.zz] at this
    rcases this with h1 | h1
    · exact absurd h1 hT
    · simpa using h1

theorem coord_inj {k : ℕ} (hdim : n = 2 * r + 1 + k)
    (hsig : (Finset.univ.filter (fun i => ε i = false)).card = r + 1) :
    ∃ (N : Fin (r + 1) → Fin n) (P : Fin (r + k) → Fin n), Function.Injective N ∧ Function.Injective P ∧
      (∀ y, ε (N y) = false) ∧ (∀ x, ε (P x) = true) := by
  set sN := Finset.univ.filter (fun i : Fin n => ε i = false) with hsN
  set sP := Finset.univ.filter (fun i : Fin n => ε i = true) with hsP
  have hcard : sP.card + sN.card = n := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i : Fin n => ε i = true)
    simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at this
    exact this
  have hP : sP.card = r + k := by omega
  let eN := sN.equivFinOfCardEq hsig
  let eP := sP.equivFinOfCardEq hP
  refine ⟨fun y => (eN.symm y).1, fun x => (eP.symm x).1, ?_, ?_, fun y => ?_, fun x => ?_⟩
  · exact Subtype.val_injective.comp eN.symm.injective
  · exact Subtype.val_injective.comp eP.symm.injective
  · exact (Finset.mem_filter.1 (eN.symm y).2).2
  · exact (Finset.mem_filter.1 (eP.symm x).2).2

theorem complement {k : ℕ} (hdim : n = 2 * r + 1 + k)
    (hsig : (Finset.univ.filter (fun i => ε i = false)).card = r + 1)
    {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℝ} (hT : 0 < T) (h : Hyp ε e f z (T : ℂ)) :
    ∃ w : Fin k → Fin n → ℂ, (∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0) ∧
      (∀ c a, hJ ε (e c) (w a) = 0) ∧ (∀ c a, hJ ε (f c) (w a) = 0) ∧ (∀ a, hJ ε z (w a) = 0) := by
  obtain ⟨N, P, hN, hP, hNs, hPs⟩ := coord_inj ε hdim hsig
  have hNP : ∀ y x, N y ≠ P x := fun y x h => by have := hNs y; rw [h, hPs x] at this; exact Bool.noConfusion this
  set sq : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) with hsq
  have hsqc : conj sq = sq := Complex.conj_ofReal _
  have hsq2 : sq * sq = 1 / 2 := by
    rw [hsq, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  let p : Fin r → Fin n := fun c => P (Fin.castAdd k c)
  let q : Fin r → Fin n := fun c => N (Fin.castSucc c)
  let qz : Fin n := N (Fin.last r)
  let wi : Fin k → Fin n := fun j => P (Fin.natAdd r j)
  let e0 : Fin r → Fin n → ℂ := fun c => sq • (dl (p c) + dl (q c))
  let f0 : Fin r → Fin n → ℂ := fun c => sq • (dl (p c) - dl (q c))
  let z0 : Fin n → ℂ := ((Real.sqrt T : ℝ) : ℂ) • dl qz
  let w0 : Fin k → Fin n → ℂ := fun j => dl (wi j)
  have hp : Function.Injective p := hP.comp (Fin.castAdd_injective r k)
  have hq : Function.Injective q := hN.comp (Fin.castSucc_injective r)
  have hqz : ∀ c, q c ≠ qz := fun c h => Fin.castSucc_ne_last c (hN h)
  have hwi : Function.Injective wi := hP.comp (Fin.natAdd_injective k r)
  have hpw : ∀ c j, p c ≠ wi j := fun c j h => by
    have h1 := congrArg Fin.val (hP h)
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at h1
    omega
  have hd : ∀ i j, hJ ε (dl i) (dl j) = if i = j then (if ε i then 1 else -1) else 0 := hJ_dl ε
  have pp : ∀ a b, hJ ε (dl (p a)) (dl (p b)) = if a = b then 1 else 0 := fun a b => by
    rw [hd]; by_cases hab : a = b
    · subst hab; simp [p, hPs]
    · rw [if_neg (hp.ne hab), if_neg hab]
  have qq : ∀ a b, hJ ε (dl (q a)) (dl (q b)) = if a = b then -1 else 0 := fun a b => by
    rw [hd]; by_cases hab : a = b
    · subst hab; simp [q, hNs]
    · rw [if_neg (hq.ne hab), if_neg hab]
  have pq : ∀ a b, hJ ε (dl (p a)) (dl (q b)) = 0 := fun a b => by rw [hd, if_neg (hNP _ _).symm]
  have qp : ∀ a b, hJ ε (dl (q a)) (dl (p b)) = 0 := fun a b => by rw [hd, if_neg (hNP _ _)]
  have h0 : Hyp ε e0 f0 z0 (T : ℂ) := by
    refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, fun a => ?_, ?_⟩
    · simp only [e0, hJ_smul_left, hJ_smul_right, hJ_add_left, hJ_add_right, pp, qq, pq, qp, hsqc]
      split_ifs <;> ring
    · simp only [e0, f0, hJ_smul_left, hJ_smul_right, hJ_add_left, hJ_sub_right, pp, qq, pq, qp, hsqc]
      split_ifs
      · linear_combination 2 * hsq2
      · ring
    · simp only [f0, hJ_smul_left, hJ_smul_right, hJ_sub_left, hJ_sub_right, pp, qq, pq, qp, hsqc]
      split_ifs <;> ring
    · have h1 : p a ≠ qz := (hNP _ _).symm
      simp only [e0, z0, hJ_smul_left, hJ_smul_right, hJ_add_left, hd, if_neg h1, if_neg (hqz a)]
      ring
    · have h1 : p a ≠ qz := (hNP _ _).symm
      simp only [f0, z0, hJ_smul_left, hJ_smul_right, hJ_sub_left, hd, if_neg h1, if_neg (hqz a)]
      ring
    · have hs : ((Real.sqrt T : ℝ) : ℂ) * ((Real.sqrt T : ℝ) : ℂ) = (T : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hT.le]
      have hq0 : ε qz = false := hNs _
      simp only [z0, hJ_smul_left, hJ_smul_right, hd, if_true, Complex.conj_ofReal, hq0, Bool.false_eq_true,
        if_false]
      linear_combination (-1 : ℂ) * hs
  obtain ⟨g, hg⟩ := witt_of_gram' ε (frm3 e0 f0 z0) (frm3 e f z) (gram_eq_of_hyp ε h0 h)
    (gram_nd_of_hyp ε (by exact_mod_cast hT.ne') h0)
  have hiso := isIsom_uMat ε g
  have he : ∀ c, Formalism.MainNotions.S.uMat g *ᵥ e0 c = e c := fun c => hg (Sum.inl c)
  have hf : ∀ c, Formalism.MainNotions.S.uMat g *ᵥ f0 c = f c := fun c => hg (Sum.inr (Sum.inl c))
  have hz : Formalism.MainNotions.S.uMat g *ᵥ z0 = z := hg (Sum.inr (Sum.inr ()))
  have ww : ∀ a b, hJ ε (w0 a) (w0 b) = if a = b then 1 else 0 := fun a b => by
    simp only [w0]; rw [hd]; by_cases hab : a = b
    · subst hab; simp [wi, hPs]
    · rw [if_neg (hwi.ne hab), if_neg hab]
  have pw : ∀ c j, hJ ε (dl (p c)) (w0 j) = 0 := fun c j => by simp only [w0]; rw [hd, if_neg (hpw c j)]
  have qw : ∀ c j, hJ ε (dl (q c)) (w0 j) = 0 := fun c j => by simp only [w0]; rw [hd, if_neg (hNP _ _)]
  have zw : ∀ j, hJ ε (dl qz) (w0 j) = 0 := fun j => by simp only [w0]; rw [hd, if_neg (hNP _ _)]
  refine ⟨fun j => Formalism.MainNotions.S.uMat g *ᵥ w0 j, fun a b => by rw [hiso, ww], fun c a => ?_, fun c a => ?_, fun a => ?_⟩
  · rw [← he, hiso]; simp only [e0, hJ_smul_left, hJ_add_left, pw, qw]; ring
  · rw [← hf, hiso]; simp only [f0, hJ_smul_left, hJ_sub_left, pw, qw]; ring
  · rw [← hz, hiso]; simp only [z0, hJ_smul_left, zw]; ring

end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI
end
end

section

noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB

section CayInv

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [Invertible (2 : K)]

theorem half_add_half' (M : Matrix ι ι K) : (⅟2 : K) • M + (⅟2 : K) • M = M := by
  rw [← add_smul, invOf_two_add_invOf_two, one_smul]

theorem cay_eq {N : ℕ} {Z : Matrix ι ι K} (hN : ((⅟2 : K) • Z) ^ N = 0) :
    cay N Z = (1 + (⅟2 : K) • Z) * geo N ((⅟2 : K) • Z) := by
  set Y : Matrix ι ι K := (⅟2 : K) • Z with hY
  set G := geo N Y with hG
  have hBG : (1 - Y) * G = 1 := by rw [hG, geo, mul_neg_geom_sum, hN, sub_zero]
  have e1 : G = 1 + Y * G := by
    have := hBG
    rw [Matrix.sub_mul, Matrix.one_mul] at this
    rw [← this]; abel
  have e2 : Z = Y + Y := by rw [hY, half_add_half']
  have e3 : cay N Z = 1 + Z * G := rfl
  rw [e3, Matrix.add_mul, Matrix.one_mul]
  calc 1 + Z * G = (1 + Y * G) + Y * G := by rw [e2, Matrix.add_mul]; abel
    _ = G + Y * G := by rw [← e1]

theorem cay_neg_mul {N : ℕ} {Z : Matrix ι ι K} (hN : ((⅟2 : K) • Z) ^ N = 0) : cay N (-Z) * cay N Z = 1 := by
  have hN' : ((⅟2 : K) • -Z) ^ N = 0 := by rw [smul_neg, neg_pow, hN, mul_zero]
  rw [cay_eq hN, cay_eq hN', smul_neg]
  set Y : Matrix ι ι K := (⅟2 : K) • Z with hY
  have h1 : geo N (-Y) * (1 + Y) = 1 := by
    have := geom_sum_mul_neg (-Y) N
    rw [sub_neg_eq_add] at this
    rw [geo, this, neg_pow, hN, mul_zero, sub_zero]
  have h2 : (1 - Y) * geo N Y = 1 := by rw [geo, mul_neg_geom_sum, hN, sub_zero]
  calc (1 + -Y) * geo N (-Y) * ((1 + Y) * geo N Y) = (1 - Y) * (geo N (-Y) * (1 + Y)) * geo N Y := by
        rw [← sub_eq_add_neg]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one, h2]

end CayInv

def mkUJ {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : Formalism.REAL.inUJ ε g) : Formalism.REAL.UJ ε :=
  ⟨⟨g, Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, mul_comm_one (by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, Formalism.REAL.Jm_mul_self]),
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, Formalism.REAL.Jm_mul_self]⟩, hg⟩

section RatEl

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

abbrev N0 (D : D7) : ℕ := 2 * D.R.rS + 2

theorem lvk_lt (k : Kap X) : lvk X k < N0 D := by show lvk X k < 2 * D.R.rS + 2; have := lvk_le X k; omega

theorem nil_of_pat {K : Type*} [CommRing K] {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) K}
    (hY : InPat (lvk X) k Y) (c : K) : (c • Y) ^ N0 D = 0 :=
  pow_eq_zero_of_inPat hk (lvk_lt X) (inPat_smul c hY)

def gE (Y : Matrix (Kap X) (Kap X) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
  Bm X * cay (N0 D) Y * Bm' X

theorem gE_mul {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y) :
    gE X (-Y) * gE X Y = 1 := by
  unfold gE
  have e : Bm X * cay (N0 D) (-Y) * Bm' X * (Bm X * cay (N0 D) Y * Bm' X) =
      Bm X * (cay (N0 D) (-Y) * ((Bm' X * Bm X) * cay (N0 D) Y)) * Bm' X := by simp only [Matrix.mul_assoc]
  rw [e, Bm'_mul_Bm, Matrix.one_mul, cay_neg_mul (nil_of_pat X hk hY _), Matrix.mul_one, Bm_mul_Bm']

theorem gE_mul' {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y) :
    gE X Y * gE X (-Y) = 1 := by
  have := gE_mul X hk (inPat_neg hY)
  rwa [neg_neg] at this

theorem cT_eq {m p : Type} (M : Matrix m p X.B.I.E) : Formalism.UG.cT (starRingEnd X.B.I.E) M = Mᴴ := by
  ext i j
  simp only [Formalism.UG.cT, conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
  rfl

theorem gE_unitary {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : (gE X Y)ᴴ * X.B.I.J * gE X Y = X.B.I.J := by
  have hc := cay_unitary hYs (nil_of_pat X hk hY (⅟2 : X.B.I.E))
  have hh : (Bm' X)ᴴ * (Bm X)ᴴ = 1 := by rw [← conjTranspose_mul, Bm_mul_Bm', conjTranspose_one]
  have hJB := JB_eq X
  unfold gE
  calc (Bm X * cay (N0 D) Y * Bm' X)ᴴ * X.B.I.J * (Bm X * cay (N0 D) Y * Bm' X)
      = (Bm' X)ᴴ * ((cay (N0 D) Y)ᴴ * ((Bm X)ᴴ * X.B.I.J * Bm X) * cay (N0 D) Y) * Bm' X := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (Bm' X)ᴴ * (Bm X)ᴴ * X.B.I.J * (Bm X * Bm' X) := by
        rw [← hJB, hc, hJB]; simp only [Matrix.mul_assoc]
    _ = X.B.I.J := by rw [hh, Bm_mul_Bm', Matrix.one_mul, Matrix.mul_one]

def gGL {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y) :
    GL (Fin X.B.I.n) X.B.I.E :=
  ⟨gE X Y, gE X (-Y), gE_mul' X hk hY, gE_mul X hk hY⟩

theorem gGL_mem {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : gGL X hk hY ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J := by
  show Formalism.UG.cT (starRingEnd X.B.I.E) (gE X Y) * X.B.I.J * gE X Y = X.B.I.J
  rw [cT_eq]
  exact gE_unitary X hk hY hYs

theorem sig_eq : (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E) = starRingEnd X.B.I.E := RingHom.ext fun _ => rfl

theorem gE_real (v : InfinitePlace X.B.I.F) (Y : Matrix (Kap X) (Kap X) X.B.I.E) :
    (X.B.I.P v)⁻¹ * (gE X Y).map (X.B.I.φ v) * X.B.I.P v =
      Bv X v * cay (N0 D) (Y.map (X.B.I.φ v)) * Bv' X v := by
  unfold gE Bv Bv'
  rw [Matrix.map_mul, Matrix.map_mul, cay_map]
  simp only [Matrix.mul_assoc]

theorem skew_map (v : InfinitePlace X.B.I.F) {Y : Matrix (Kap X) (Kap X) X.B.I.E}
    (hYs : Yᴴ * JB X = -(JB X * Y)) :
    (Y.map (X.B.I.φ v))ᴴ * JBv X v = -(JBv X v * Y.map (X.B.I.φ v)) := by
  rw [JBv, map_conjTranspose, ← Matrix.map_mul, hYs, ← Matrix.map_mul, Matrix.map_neg]
  exact fun a => map_neg _ a

theorem inUJ_real {k : ℕ} (hk : 1 ≤ k) (v : InfinitePlace X.B.I.F) {Y : Matrix (Kap X) (Kap X) X.B.I.E}
    (hY : InPat (lvk X) k Y) (hYs : Yᴴ * JB X = -(JB X * Y)) :
    Formalism.REAL.inUJ (X.B.I.ε v) ((X.B.I.P v)⁻¹ * (gE X Y).map (X.B.I.φ v) * X.B.I.P v) := by
  rw [gE_real]
  unfold Formalism.REAL.inUJ
  have hc := cay_unitary (skew_map X v hYs) (nil_of_pat X hk (inPat_map (X.B.I.φ v) hY) (⅟2 : ℂ))
  have hh : (Bv' X v)ᴴ * (Bv X v)ᴴ = 1 := by rw [← conjTranspose_mul, Bv_mul_Bv', conjTranspose_one]
  calc (Bv X v * cay (N0 D) (Y.map (X.B.I.φ v)) * Bv' X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) *
        (Bv X v * cay (N0 D) (Y.map (X.B.I.φ v)) * Bv' X v)
      = (Bv' X v)ᴴ * ((cay (N0 D) (Y.map (X.B.I.φ v)))ᴴ * ((Bv X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Bv X v) *
        cay (N0 D) (Y.map (X.B.I.φ v))) * Bv' X v := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (Bv' X v)ᴴ * ((Bv X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Bv X v) * Bv' X v := by rw [Bv_gram, hc]
    _ = ((Bv' X v)ᴴ * (Bv X v)ᴴ) * Formalism.REAL.Jm (X.B.I.ε v) * (Bv X v * Bv' X v) := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (X.B.I.ε v) := by rw [hh, Bv_mul_Bv', Matrix.one_mul, Matrix.mul_one]

def gA {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : X.B.I.GA :=
  (fun v => mkUJ (X.B.I.ε v) _ (inUJ_real X hk v hY hYs),
    Formalism.L2.SG.ColsDim.ratHom X.B.I.cm.sig X.B.I.J (Af X.B.I.F)
      ⟨gGL X hk hY, by rw [sig_eq]; exact gGL_mem X hk hY hYs⟩)

theorem gA_GF {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : gA X hk hY hYs ∈ X.B.I.GFset :=
  ⟨gGL X hk hY, gGL_mem X hk hY hYs, fun v => rfl, rfl⟩

theorem Mv_gA {k : ℕ} (hk : 1 ≤ k) (v : InfinitePlace X.B.I.F) {Y : Matrix (Kap X) (Kap X) X.B.I.E}
    (hY : InPat (lvk X) k Y) (hYs : Yᴴ * JB X = -(JB X * Y)) :
    Mv X v (gA X hk hY hYs).1 = cay (N0 D) (Y.map (X.B.I.φ v)) := by
  unfold Mv
  show Bv' X v * ((X.B.I.P v)⁻¹ * (gE X Y).map (X.B.I.φ v) * X.B.I.P v) * Bv X v = _
  rw [gE_real]
  simp only [← Matrix.mul_assoc, Bv'_mul_Bv, Matrix.one_mul]
  rw [Matrix.mul_assoc, Bv'_mul_Bv, Matrix.mul_one]

theorem gA_ninf {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : (gA X hk hY hYs).1 ∈ X.NinfU u := by
  intro v
  apply inN_of_pat X u v
  have := Mv_gA X hk v hY hYs
  unfold Mv at this
  rw [this]
  exact inPat_mono hk (cay_sub_one _ (inPat_map (X.B.I.φ v) hY))

end RatEl
end SlabNDensePf
end Pf
end SG
end L2
end Formalism
end
end

section

noncomputable section

open MeasureTheory Topology
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

section ProdF

variable {ι : Type} [Fintype ι] {r : ℕ} {G : ι → Type} [∀ v, Group (G v)] [∀ v, MeasurableSpace (G v)]
  [∀ v, MeasurableMul₂ (G v)] [∀ v, MeasurableInv (G v)]

theorem prod_formula (mG : ∀ v, Measure (G v)) [∀ v, SigmaFinite (mG v)]
    (ν : ∀ v, Measure (Fin (r + 1) → ℂ)) [∀ v, SigmaFinite (ν v)]
    (μ μ' : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)] [∀ v, SigmaFinite (μ' v)]
    (h : ∀ v, (Fin (r + 1) → ℂ) → G v) (hh : ∀ v, Measurable (h v))
    (hm : ∀ v, mG v = ((ν v).prod ((μ v).prod (μ' v))).map (fun x => x.2.1 * h v x.1 * x.2.2⁻¹))
    (φ : ((v : ι) → G v) → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ x, φ x ∂Measure.pi mG = ∫⁻ c, ∫⁻ s, ∫⁻ s', φ (s * (fun v => h v (c v)) * s'⁻¹)
      ∂Measure.pi μ' ∂Measure.pi μ ∂Measure.pi ν := by
  have hFm : ∀ v, Measurable
      (fun x : (Fin (r + 1) → ℂ) × (G v × G v) => x.2.1 * h v x.1 * x.2.2⁻¹) :=
    fun v => ((measurable_fst.comp measurable_snd).mul ((hh v).comp measurable_fst)).mul
      (measurable_snd.comp measurable_snd).inv
  have : ∀ v, SigmaFinite (((ν v).prod ((μ v).prod (μ' v))).map
      (fun x : (Fin (r + 1) → ℂ) × (G v × G v) => x.2.1 * h v x.1 * x.2.2⁻¹)) := fun v => by
    rw [← hm v]; infer_instance
  have hpi : Measure.pi mG = (Measure.pi fun v => (ν v).prod ((μ v).prod (μ' v))).map
      (fun y v => (y v).2.1 * h v (y v).1 * (y v).2.2⁻¹) := by
    rw [Measure.pi_map_pi (fun v => (hFm v).aemeasurable)]
    congr 1; funext v; exact hm v
  have hYm : Measurable (fun (y : (v : ι) → (Fin (r + 1) → ℂ) × (G v × G v)) (v : ι) =>
      (y v).2.1 * h v (y v).1 * (y v).2.2⁻¹) :=
    Measurable.of_eval fun v => (hFm v).comp (measurable_pi_apply v)
  have hgm : Measurable (fun z : ((v : ι) → (Fin (r + 1) → ℂ)) × (((v : ι) → G v) × ((v : ι) → G v)) =>
      φ (z.2.1 * (fun v => h v (z.1 v)) * z.2.2⁻¹)) := by
    refine hφ.comp (((measurable_fst.comp measurable_snd).mul ?_).mul
      (measurable_snd.comp measurable_snd).inv)
    exact Measurable.of_eval fun v => (hh v).comp ((measurable_pi_apply v).comp measurable_fst)
  have hE1 := measurePreserving_piProd (α := fun _ => Fin (r + 1) → ℂ) (β := fun v => G v × G v)
    ν (fun v => (μ v).prod (μ' v))
  have hE2 := (MeasurePreserving.id (Measure.pi ν)).prod
    (measurePreserving_piProd (α := G) (β := G) μ μ')
  have hE := hE2.comp hE1
  rw [hpi, lintegral_map hφ hYm]
  refine Eq.trans ?_ ((hE.lintegral_comp hgm).trans ?_)
  · rfl
  rw [lintegral_prod _ hgm.aemeasurable]
  refine lintegral_congr fun c => ?_
  exact lintegral_prod (fun y : ((v : ι) → G v) × ((v : ι) → G v) =>
    φ (y.1 * (fun v => h v (c v)) * y.2⁻¹)) (hgm.comp measurable_prodMk_left).aemeasurable

theorem dc_switch (μ μ' : Measure ((v : ι) → G v)) [SFinite μ'] (φ : ((v : ι) → G v) → ℝ≥0∞) (hφ : Measurable φ)
    (γ t t' : (v : ι) → G v) (ht : μ.map (fun x => x * t) = μ) (ht' : μ'.map (fun x => x * t') = μ') :
    ∫⁻ s, ∫⁻ s', φ (s * (t * γ * t'⁻¹) * s'⁻¹) ∂μ' ∂μ = ∫⁻ s, ∫⁻ s', φ (s * γ * s'⁻¹) ∂μ' ∂μ := by
  have hΦ : Measurable fun a : (v : ι) → G v => ∫⁻ s', φ (a * γ * s'⁻¹) ∂μ' :=
    (hφ.comp ((measurable_fst.mul_const γ).mul measurable_snd.inv)).lintegral_prod_right'
  have inner : ∀ a : (v : ι) → G v,
      ∫⁻ s', φ (a * γ * (s' * t')⁻¹) ∂μ' = ∫⁻ s', φ (a * γ * s'⁻¹) ∂μ' := by
    intro a
    have hf : Measurable fun s' : (v : ι) → G v => φ (a * γ * s'⁻¹) :=
      hφ.comp (measurable_const.mul measurable_inv)
    rw [← lintegral_map hf (measurable_mul_const t'), ht']
  calc ∫⁻ s, ∫⁻ s', φ (s * (t * γ * t'⁻¹) * s'⁻¹) ∂μ' ∂μ
      = ∫⁻ s, ∫⁻ s', φ (s * t * γ * (s' * t')⁻¹) ∂μ' ∂μ := by
        refine lintegral_congr fun s => lintegral_congr fun s' => ?_
        congr 1; group
    _ = ∫⁻ s, ∫⁻ s', φ (s * t * γ * s'⁻¹) ∂μ' ∂μ :=
        lintegral_congr fun s => inner (s * t)
    _ = ∫⁻ s, ∫⁻ s', φ (s * γ * s'⁻¹) ∂μ' ∂μ := by
        rw [← lintegral_map hΦ (measurable_mul_const t), ht]

end ProdF

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end
end
