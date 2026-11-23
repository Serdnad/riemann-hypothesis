module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Idempotents
import Batteries.Tactic.Lint.Basic
import Batteries.Tactic.Lint.Misc
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.BigOperators
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

@[expose] public section

section

open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.alghom_of_units :
    ∀ {K E : Type} [CommRing K] [Ring E] [Algebra K E] {σ : Type} [Fintype σ] [DecidableEq σ] (d : σ → Type) [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)] (e : ∀ s, d s → d s → E), (∀ s i j k, e s i j * e s j k = e s i k) → (∀ s i j k l, j ≠ k → e s i j * e s k l = 0) → (∀ s t i j k l, s ≠ t → e s i j * e t k l = 0) → ∑ s, ∑ i, e s i i = 1 → ∃ j : (∀ s, Matrix (d s) (d s) K) →ₐ[K] E, ∀ s i k, j (Pi.single s (single i k 1)) = e s i k := by
  intro K E _ _ _ σ _ _ d _ _ _ e hmul horth hst hsum
  let f : (∀ s, Matrix (d s) (d s) K) → E := fun M => ∑ s, ∑ i, ∑ k, M s i k • e s i k
  have hadd : ∀ M N, f (M + N) = f M + f N := by
    intro M N
    simp only [f, Pi.add_apply, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  have hsmul : ∀ (c : K) M, f (c • M) = c • f M := by
    intro c M
    simp only [f, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have key : ∀ (N : ∀ s, Matrix (d s) (d s) K) s i j (a : K),
      (a • e s i j) * f N = ∑ k, (a * N s j k) • e s i k := by
    intro N s i j a
    simp only [f]
    rw [Finset.mul_sum, Finset.sum_eq_single s]
    · rw [Finset.mul_sum, Finset.sum_eq_single j]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_mul_smul_comm, hmul]
      · intro l _ hl
        rw [Finset.mul_sum]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [smul_mul_smul_comm, horth s i j l k (Ne.symm hl), smul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro t _ ht
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [smul_mul_smul_comm, hst s t i j l k (Ne.symm ht), smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hm : ∀ M N, f (M * N) = f M * f N := by
    intro M N
    have : f M * f N = ∑ s, ∑ i, ∑ j, ∑ k, (M s i j * N s j k) • e s i k := by
      show (∑ s, ∑ i, ∑ k, M s i k • e s i k) * f N = _
      simp only [Finset.sum_mul, key]
    rw [this]
    simp only [f, Pi.mul_apply, Matrix.mul_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  have h1 : f 1 = 1 := by
    simp only [f, Pi.one_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hsum
  let L : (∀ s, Matrix (d s) (d s) K) →ₗ[K] E :=
    { toFun := f, map_add' := hadd, map_smul' := hsmul }
  refine ⟨AlgHom.ofLinearMap L h1 hm, ?_⟩
  intro s i k
  show f (Pi.single s (Matrix.single i k 1)) = e s i k
  simp only [f]
  rw [Finset.sum_eq_single s]
  · rw [Pi.single_eq_same]
    simp only [Matrix.single_apply, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb
        rw [if_neg]
        exact fun h => hb h.2.symm
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro b _ hb
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [if_neg]
      exact fun h => hb h.1.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro t _ ht
    simp [Pi.single_eq_of_ne ht]
  · intro h; exact absurd (Finset.mem_univ _) h
end

section

noncomputable section

namespace UpperTheory.V.AlgebraTools

structure TrInv (B E : Type*) [CommRing B] [Ring E] [Algebra B E] where
  st : E →ₗ[B] E
  st_mul : ∀ x y, st (x * y) = st y * st x
  st_st : ∀ x, st (st x) = x
  tr : E →ₗ[B] B
  tr_comm : ∀ x y, tr (x * y) = tr (y * x)
  tr_st : ∀ x, tr (st x) = tr x

structure OddForm (B N : Type*) [CommRing B] [AddCommGroup N] [Module B N] where
  be : N →ₗ[B] N →ₗ[B] B
  symm : ∀ b b', be b b' = be b' b
  assoc : ∀ b b' b'', be b b' • b'' = be b' b'' • b

namespace OddForm

variable {B N : Type*} [CommRing B] [AddCommGroup N] [Module B N]

instance : Inhabited (OddForm B N) := ⟨⟨0, fun _ _ => rfl, fun _ _ _ => by simp⟩⟩

@[nolint unusedArguments]
def Ext (_ : OddForm B N) : Type _ := B × N

variable (Φ : OddForm B N)

instance : AddCommGroup Φ.Ext := inferInstanceAs (AddCommGroup (B × N))
instance : Module B Φ.Ext := inferInstanceAs (Module B (B × N))

def el (a : B) (b : N) : Φ.Ext := (a, b)

variable {Φ}

def Ext.ev (z : Φ.Ext) : B := Prod.fst z

def Ext.od (z : Φ.Ext) : N := Prod.snd z

@[ext] theorem ext {z w : Φ.Ext} (hev : z.ev = w.ev) (hod : z.od = w.od) : z = w :=
  Prod.ext hev hod

instance : One Φ.Ext := ⟨Φ.el 1 0⟩
instance : Mul Φ.Ext := ⟨fun z w => Φ.el (z.ev * w.ev + Φ.be z.od w.od) (z.ev • w.od + w.ev • z.od)⟩

@[simp] theorem ev_one : (1 : Φ.Ext).ev = 1 := rfl
@[simp] theorem od_one : (1 : Φ.Ext).od = 0 := rfl
@[simp] theorem ev_zero : (0 : Φ.Ext).ev = 0 := rfl
@[simp] theorem od_zero : (0 : Φ.Ext).od = 0 := rfl
@[simp] theorem ev_add (z w : Φ.Ext) : (z + w).ev = z.ev + w.ev := rfl
@[simp] theorem od_add (z w : Φ.Ext) : (z + w).od = z.od + w.od := rfl
@[simp] theorem ev_smul (c : B) (z : Φ.Ext) : (c • z).ev = c * z.ev := rfl
@[simp] theorem od_smul (c : B) (z : Φ.Ext) : (c • z).od = c • z.od := rfl
@[simp] theorem ev_mul (z w : Φ.Ext) : (z * w).ev = z.ev * w.ev + Φ.be z.od w.od := rfl
@[simp] theorem od_mul (z w : Φ.Ext) : (z * w).od = z.ev • w.od + w.ev • z.od := rfl

instance : CommRing Φ.Ext :=
  { (inferInstance : AddCommGroup Φ.Ext), (inferInstance : One Φ.Ext), (inferInstance : Mul Φ.Ext) with
    mul_assoc := fun x y z => by
      ext
      · simp; ring
      · simp only [od_mul, ev_mul, add_smul, smul_add, smul_smul]
        rw [Φ.assoc x.od y.od z.od, mul_comm z.ev x.ev, mul_comm z.ev y.ev]; abel
    one_mul := fun x => by ext <;> simp
    mul_one := fun x => by ext <;> simp
    zero_mul := fun x => by ext <;> simp
    mul_zero := fun x => by ext <;> simp
    left_distrib := fun x y z => by
      ext
      · simp; ring
      · simp [add_smul]; abel
    right_distrib := fun x y z => by
      ext
      · simp; ring
      · simp [add_smul]; abel
    mul_comm := fun x y => by
      ext
      · simp [mul_comm, Φ.symm x.od]
      · simp [add_comm] }

instance : Algebra B Φ.Ext :=
  Algebra.ofModule
    (fun c x y => by
      ext
      · simp; ring
      · simp [smul_smul, mul_comm, add_comm])
    (fun c x y => by
      ext
      · simp; ring
      · simp [smul_smul, mul_comm, add_comm])

instance [Module.Finite B N] : Module.Finite B Φ.Ext := inferInstanceAs (Module.Finite B (B × N))

def red (Φ : OddForm B N) : Ideal B := Ideal.span {c | ∃ b b', c = Φ.be b b'}

end OddForm

variable {B E : Type*} [CommRing B] [Ring E] [Algebra B E]

def corner (B : Type*) [CommRing B] [Algebra B E] (e e' : E) : Submodule B E :=
  LinearMap.range ((LinearMap.mulLeft B e).comp (LinearMap.mulRight B e'))

def cornerProj (B : Type*) [CommRing B] [Algebra B E] (e e' : E) : E →ₗ[B] corner B e e' :=
  ((LinearMap.mulLeft B e).comp (LinearMap.mulRight B e')).rangeRestrict

structure TrInv.Units (T : TrInv B E) (ι : Type*) [Fintype ι] (o : ι → ι) where
  ep : ι → E
  x : ι → E
  o_o : ∀ i, o (o i) = o i
  coi : CompleteOrthogonalIdempotents ep
  st_ep : ∀ i, T.st (ep i) = ep i
  tr_ep : ∀ i, T.tr (ep i) = 1
  rank_one : ∀ i y, ∃ b : B, ep i * y * ep i = b • ep i
  x_mem : ∀ i, ep (o i) * x i * ep i = x i
  x_base : ∀ i, x (o i) = ep (o i)
  x_st : ∀ i, x i * T.st (x i) = ep (o i)
  st_mul_x_eq : ∀ i, T.st (x i) * x i = ep i

namespace TrInv.Units

variable {T : TrInv B E} {ι : Type*} [Fintype ι] {o : ι → ι} (U : T.Units ι o)

theorem corner_eq (i : ι) (y : E) : U.ep i * y * U.ep i = T.tr (U.ep i * y * U.ep i) • U.ep i := by
  obtain ⟨b, hb⟩ := U.rank_one i y
  rw [hb, map_smul, U.tr_ep, smul_eq_mul, mul_one]

def oddForm (p q : ι) : OddForm B (corner B (U.ep p) (U.ep q)) where
  be := LinearMap.mk₂ B (fun b b' => T.tr (b.1 * T.st b'.1))
    (fun _ _ _ => by simp [add_mul]) (fun _ _ _ => by simp) (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp)
  symm b b' := by
    simp only [LinearMap.mk₂_apply]
    rw [← T.tr_st, T.st_mul, T.st_st]
  assoc := by
    rintro ⟨_, y, rfl⟩ ⟨_, y', rfl⟩ ⟨_, y'', rfl⟩
    apply Subtype.ext
    have hp := (U.coi.idem p).eq
    have hq := (U.coi.idem q).eq
    have hp' : ∀ z, U.ep p * (U.ep p * z) = U.ep p * z := fun z => by rw [← mul_assoc, hp]
    have hq' : ∀ z, U.ep q * (U.ep q * z) = U.ep q * z := fun z => by rw [← mul_assoc, hq]
    have h1 := U.corner_eq p (y * U.ep q * T.st y')
    have h2 := U.corner_eq q (T.st y' * U.ep p * y'')
    have h3 : T.tr (U.ep p * (y' * U.ep q) * T.st (U.ep p * (y'' * U.ep q))) =
        T.tr (U.ep q * (T.st y' * U.ep p * y'') * U.ep q) := by
      rw [← T.tr_st, T.st_mul, T.st_st, T.tr_comm]
      simp only [T.st_mul, U.st_ep, mul_assoc, hp']
    have h4 : T.tr (U.ep p * (y * U.ep q) * T.st (U.ep p * (y' * U.ep q))) =
        T.tr (U.ep p * (y * U.ep q * T.st y') * U.ep p) := by
      simp only [T.st_mul, U.st_ep, mul_assoc, hq']
    simp only [LinearMap.mk₂_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      SetLike.val_smul]
    rw [h3, h4]
    calc _ = (T.tr (U.ep p * (y * U.ep q * T.st y') * U.ep p) • U.ep p) * (y'' * U.ep q) := by
          rw [smul_mul_assoc]
      _ = U.ep p * y * (U.ep q * (T.st y' * U.ep p * y'') * U.ep q) := by
          rw [← h1]; simp only [mul_assoc]
      _ = _ := by rw [h2, mul_smul_comm, ← h2, mul_assoc (U.ep p)]

def vr (p q : ι) (y : E) : Matrix ι ι (U.oddForm p q).Ext := Matrix.of fun i j =>
  (U.oddForm p q).el (T.tr (U.x i * y * T.st (U.x j)))
    (cornerProj B (U.ep p) (U.ep q) (U.x i * y * T.st (U.x j)) +
      cornerProj B (U.ep p) (U.ep q) (T.st (U.x i * y * T.st (U.x j))))

end TrInv.Units

end UpperTheory.V.AlgebraTools
end
end

section

open Polynomial Matrix IsLocalRing TensorProduct

namespace UpperTheory.V.AlgebraTools

private def DGood {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι R) : Prop :=
  ∃ P : Matrix ι ι R, IsUnit P.det ∧ (Pᵀ * H * P).IsDiag

private theorem dgood_congr {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (H Q : Matrix ι ι R) (hQ : IsUnit Q.det) (h : DGood (Qᵀ * H * Q)) : DGood H := by
  obtain ⟨P, hP, hD⟩ := h
  refine ⟨Q * P, by rw [det_mul]; exact hQ.mul hP, ?_⟩
  rw [transpose_mul]
  simpa only [Matrix.mul_assoc] using hD

private theorem dgood_reindex {R : Type} [CommRing R] {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : κ ≃ ι)
    (H : Matrix ι ι R) (h : DGood (H.submatrix e e)) : DGood H := by
  obtain ⟨P, hP, hD⟩ := h
  refine ⟨P.submatrix e.symm e.symm, by rw [det_submatrix_equiv_self]; exact hP, ?_⟩
  have key : (P.submatrix e.symm e.symm)ᵀ * H * P.submatrix e.symm e.symm
      = (Pᵀ * H.submatrix e e * P).submatrix e.symm e.symm := by
    rw [← submatrix_mul_equiv _ _ _ e.symm _, ← submatrix_mul_equiv _ _ _ e.symm _,
      transpose_submatrix, submatrix_submatrix]
    simp
  rw [key]
  exact hD.submatrix e.symm.injective

private theorem pivot {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι R) (h2 : IsUnit (2 : R)) (hs : Hᵀ = H) (hd : IsUnit H.det) (i : ι) :
    ∃ Q : Matrix ι ι R, IsUnit Q.det ∧ IsUnit ((Qᵀ * H * Q) i i) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, IsUnit (H i j) := by
    by_contra hne
    push_neg at hne
    have key : ∑ j, H i j * adjugate H j i = H.det := by
      have := congrFun (congrFun (mul_adjugate H) i) i
      simpa [Matrix.mul_apply] using this
    have hm : ∑ j, H i j * adjugate H j i ∈ maximalIdeal R :=
      Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _
        (by rw [mem_maximalIdeal, mem_nonunits_iff]; exact hne j)
    rw [key, mem_maximalIdeal, mem_nonunits_iff] at hm
    exact hm hd
  by_cases hij : j = i
  · subst hij
    exact ⟨1, by simp, by simpa using hj⟩
  · have hji : H j i = H i j := by
      have := congrFun (congrFun hs i) j
      simpa using this
    have hent : ∀ c : R, ((transvection j i c)ᵀ * H * transvection j i c) i i
        = H i i + 2 * c * H i j + c * c * H j j := by
      intro c
      simp [transvection, Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
        add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite, Ne.symm hij, hij, hji]
      ring
    by_cases hp : IsUnit (H i i + 2 * 1 * H i j + 1 * 1 * H j j)
    · exact ⟨transvection j i 1, by rw [det_transvection_of_ne j i hij]; exact isUnit_one,
        by rw [hent]; exact hp⟩
    · refine ⟨transvection j i (-1), by rw [det_transvection_of_ne j i hij]; exact isUnit_one, ?_⟩
      rw [hent]
      by_contra hm
      have hx : (H i i + 2 * 1 * H i j + 1 * 1 * H j j)
          - (H i i + 2 * (-1) * H i j + (-1) * (-1) * H j j) ∈ maximalIdeal R :=
        Ideal.sub_mem _ ((mem_maximalIdeal _).2 hp) ((mem_maximalIdeal _).2 hm)
      have e4 : (H i i + 2 * 1 * H i j + 1 * 1 * H j j)
          - (H i i + 2 * (-1) * H i j + (-1) * (-1) * H j j) = 2 * 2 * H i j := by ring
      rw [e4, mem_maximalIdeal, mem_nonunits_iff] at hx
      exact hx ((h2.mul h2).mul hj)

private theorem step {R : Type} [CommRing R] {κ : Type} [Fintype κ] [DecidableEq κ]
    (ih : ∀ H : Matrix κ κ R, Hᵀ = H → IsUnit H.det → DGood H)
    (H : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R) (hs : Hᵀ = H) (hd : IsUnit H.det)
    (h0 : IsUnit (H (Sum.inl ()) (Sum.inl ()))) : DGood H := by
  classical
  have hH : H = fromBlocks (H (Sum.inl ()) (Sum.inl ()) • (1 : Matrix Unit Unit R))
      H.toBlocks₁₂ H.toBlocks₁₂ᵀ H.toBlocks₂₂ := by
    ext (⟨⟩ | k) (⟨⟩ | l)
    · simp
    · simp [toBlocks₁₂]
    · have := congrFun (congrFun hs (Sum.inl ())) (Sum.inr k)
      simp only [transpose_apply] at this
      simp [toBlocks₁₂, this]
    · simp [toBlocks₂₂]
  generalize H (Sum.inl ()) (Sum.inl ()) = a at hH h0
  generalize H.toBlocks₁₂ = B at hH
  generalize H.toBlocks₂₂ = D at hH
  subst hH
  have hDs : Dᵀ = D := by
    have := hs
    rw [fromBlocks_transpose] at this
    exact (fromBlocks_inj.1 this).2.2.2
  obtain ⟨b, hab⟩ := h0.exists_right_inv
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  have hE : (fromBlocks 1 (-(b • B)) 0 1 : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R)ᵀ
      * fromBlocks (a • 1) B Bᵀ D * fromBlocks 1 (-(b • B)) 0 1
      = fromBlocks (a • 1) 0 0 (D - b • (Bᵀ * B)) := by
    simp [fromBlocks_transpose, fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hba, hab, sub_eq_neg_add]
  have hQ : IsUnit (fromBlocks 1 (-(b • B)) 0 1 : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R).det := by
    rw [det_fromBlocks_zero₂₁]; simp
  apply dgood_congr _ _ hQ
  rw [hE]
  have hSs : (D - b • (Bᵀ * B))ᵀ = D - b • (Bᵀ * B) := by
    rw [transpose_sub, transpose_smul, transpose_mul, transpose_transpose, hDs]
  have hSd : IsUnit (D - b • (Bᵀ * B)).det := by
    have h1 : IsUnit (fromBlocks (a • 1) 0 0 (D - b • (Bᵀ * B)) :
        Matrix (Unit ⊕ κ) (Unit ⊕ κ) R).det := by
      rw [← hE, det_mul, det_mul, det_transpose]
      exact (hQ.mul hd).mul hQ
    rw [det_fromBlocks_zero₂₁] at h1
    exact isUnit_of_mul_isUnit_right h1
  obtain ⟨P₀, hP₀, hP₀d⟩ := ih _ hSs hSd
  refine ⟨fromBlocks 1 0 0 P₀, ?_, ?_⟩
  · rw [det_fromBlocks_zero₂₁, det_one, one_mul]; exact hP₀
  · have hF : (fromBlocks 1 0 0 P₀ : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R)ᵀ
        * fromBlocks (a • 1) 0 0 (D - b • (Bᵀ * B)) * fromBlocks 1 0 0 P₀
        = fromBlocks (a • 1) 0 0 (P₀ᵀ * (D - b • (Bᵀ * B)) * P₀) := by
      simp [fromBlocks_transpose, fromBlocks_multiply]
    rw [hF]
    exact IsDiag.fromBlocks (fun i j h => absurd (Subsingleton.elim i j) h) hP₀d

private theorem dgood_fin {R : Type} [CommRing R] [IsLocalRing R] (h2 : IsUnit (2 : R)) (n : ℕ) :
    ∀ H : Matrix (Fin n) (Fin n) R, Hᵀ = H → IsUnit H.det → DGood H := by
  induction n with
  | zero =>
    intro H _ _
    exact ⟨1, by simp, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro H hs hd
    have e : Unit ⊕ Fin n ≃ Fin (n + 1) := Fintype.equivFinOfCardEq (by simp [add_comm])
    obtain ⟨Q, hQ, hQi⟩ := pivot H h2 hs hd (e (Sum.inl ()))
    apply dgood_congr H Q hQ
    apply dgood_reindex e
    apply step ih
    · simp [transpose_submatrix, transpose_mul, hs, Matrix.mul_assoc]
    · rw [det_submatrix_equiv_self, det_mul, det_mul, det_transpose]
      exact (hQ.mul hd).mul hQ
    · exact hQi

end UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.diag_local :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] {n : ℕ} (H : Matrix (Fin n) (Fin n) R), IsUnit (2 : R) → Hᵀ = H → IsUnit H.det → ∃ (P : GL (Fin n) R) (c : Fin n → Rˣ), (P : Matrix (Fin n) (Fin n) R)ᵀ * H * P = diagonal fun i => (c i : R) := by
  intro R _ _ n H h2 hs hd
  obtain ⟨P, hP, hD⟩ := UpperTheory.V.AlgebraTools.dgood_fin h2 n H hs hd
  have hDu : IsUnit (Pᵀ * H * P).det := by
    rw [det_mul, det_mul, det_transpose]
    exact (hP.mul hd).mul hP
  have hdiag : ∀ i, IsUnit ((Pᵀ * H * P) i i) := by
    intro i
    rw [← hD.diagonal_diag, det_diagonal] at hDu
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (Pᵀ * H * P).diag (Finset.mem_univ i)) hDu
  refine ⟨((isUnit_iff_isUnit_det P).2 hP).unit, fun i => (hdiag i).unit, ?_⟩
  simp only [IsUnit.unit_spec]
  exact hD.diagonal_diag.symm
end

section

open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.sqrt_one_add :
    ∀ {B : Type} [CommRing B] (I : Ideal B) [HenselianRing B I] (a : B), IsUnit (2 : B) → a - 1 ∈ I → ∃ α : Bˣ, (α : B) ^ 2 = a ∧ (α : B) - 1 ∈ I := by
  intro B _ I _ a h2 ha
  have hmon : (X ^ 2 - C a : B[X]).Monic := by
    apply Polynomial.monic_X_pow_sub_C
    norm_num
  obtain ⟨α, hroot, hα⟩ := HenselianRing.is_henselian (X ^ 2 - C a) hmon 1
    (by
      have : (X ^ 2 - C a : B[X]).eval 1 = -(a - 1) := by simp <;> ring
      rw [this]
      exact I.neg_mem ha)
    (by
      have : (derivative (X ^ 2 - C a : B[X])).eval 1 = 2 := by
        simp only [derivative_sub, derivative_X_pow, derivative_C, eval_sub, eval_mul, eval_C,
          eval_pow, eval_one, eval_zero]
        norm_num
      rw [this]
      exact h2.map _)
  have hu : IsUnit α :=
    Ideal.isUnit_of_sub_one_mem_jacobson α (HenselianRing.jac (I := I) hα)
  refine ⟨hu.unit, ?_, ?_⟩
  · simp only [IsUnit.unit_spec]
    have := hroot
    simp [Polynomial.IsRoot] at this
    exact sub_eq_zero.mp this
  · simpa using hα
end
