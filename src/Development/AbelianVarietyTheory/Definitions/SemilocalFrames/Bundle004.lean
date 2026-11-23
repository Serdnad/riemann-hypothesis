module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
public import Formalism.FormalDegreeBessel.Bundle001
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass

def nCoords (k r : ℕ) (x : Mt k r) :
    ({p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) // p.1.val < r ∧ p.1 < p.2 ∧ p.2.val ≤ r + k} → ℂ) ×
      ({p : Fin r × Fin r // p.1 < p.2} → ℂ) × (Fin r → ℝ) :=
  (fun p => x p.1.1 p.1.2, fun p => x (eI k r p.1.1) (esI k r p.1.2), fun a => (x (eI k r a) (esI k r a)).im)

section Ring

variable {A : Type} [CommRing A]

def sideM {n a b : ℕ} (P : Matrix (Fin n) (Fin a) A) (Q : Matrix (Fin n) (Fin b) A) :
    Matrix (Fin n) (Fin (a + b)) A := fun i => Fin.append (P i) (Q i)

end Ring

section Glob

variable {E : Type} [Field E] [NumberField E]

def id1 (E : Type) [Field E] [NumberField E] (r : ℕ) : Fin (r + 1 + r) → FractionalIdeal (𝓞 E)⁰ E :=
  Fin.append (fun b : Fin (r + 1) => dInv E (r - (b : ℕ))) fun b : Fin r => (dInv E (r - (b : ℕ)))⁻¹

def Adapted {k r : ℕ} (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E)
    (s : Fin r → ℝ) : Prop :=
  ∀ (w : InfinitePlace E) (a : Fin r),
    (A w).mulVec (fun i => w.embedding (P i a.castSucc)) = (s a : ℂ) • bvec (eI k r a) ∧
    (A w).mulVec (fun i => w.embedding (f i a)) = ((s a)⁻¹ : ℂ) • bvec (esI k r a)

def IsDomN (σ : E →+* E) {k r : ℕ} (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (𝓓 : Set (InfinitePlace E → Mt k r)) : Prop :=
  MeasurableSet 𝓓 ∧ ∀ x : InfinitePlace E → Mt k r, (∀ w, Matrix.of (x w) ∈ Nset k r) →
    ∃! γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E, (InN σ J P γ ∧ latMap γ Λ = Λ) ∧
      (fun w => Matrix.of.symm (A w * γ.map w.embedding * (A w)⁻¹ * Matrix.of (x w))) ∈ 𝓓

variable {F : Type} [Field F] [NumberField F] [Algebra F E]


end Glob

end GlobalTheory.SnMass
end
end

section

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ContModel

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.ContModel.relVol_of_le {W : Type} [AddCommGroup W]
    {W0 A B : AddSubgroup W} (h : B ≤ A) (hB : B.relIndex W0 ≠ 0) :
    _root_.GlobalTheory.HL.relVol W0 A = B.relIndex A * _root_.GlobalTheory.HL.relVol W0 B := by
  unfold _root_.GlobalTheory.HL.relVol
  have h1 := AddSubgroup.relIndex_inf_mul_relIndex W0 B A
  have h2 := AddSubgroup.relIndex_inf_mul_relIndex B W0 A
  have h3 := AddSubgroup.relIndex_inf_mul_relIndex B A W0
  rw [inf_eq_left.mpr h] at h1 h3
  rw [inf_comm W0 B] at h1
  rw [inf_comm W0 A] at h2
  rw [← h3] at hB ⊢
  have hd : (B.relIndex (A ⊓ W0) : ℝ) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul hB
  have hα : (A.relIndex W0 : ℝ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul hB
  have key : (W0.relIndex B : ℝ) * B.relIndex A = B.relIndex (A ⊓ W0) * W0.relIndex A := by
    exact_mod_cast h1.trans h2.symm
  push_cast
  field_simp
  linear_combination (-1 : ℝ) * key

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
private theorem ncard_image_mk_eq_mul_relIndex_of_le {W : Type} [AddCommGroup W] {A B : AddSubgroup W} (h : B ≤ A)
    {S : Set W} (hS : ∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) :
    ((QuotientAddGroup.mk : W → W ⧸ B) '' S).ncard =
      ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard * B.relIndex A := by
  set Ab : AddSubgroup (W ⧸ B) := A.map (QuotientAddGroup.mk' B) with hAb
  set T : Set ((W ⧸ B) ⧸ Ab) :=
    (QuotientAddGroup.mk : W ⧸ B → (W ⧸ B) ⧸ Ab) '' ((QuotientAddGroup.mk : W → W ⧸ B) '' S) with hT
  have hpre : (QuotientAddGroup.mk : W ⧸ B → (W ⧸ B) ⧸ Ab) ⁻¹' T =
      (QuotientAddGroup.mk : W → W ⧸ B) '' S := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, hz⟩
      induction y using QuotientAddGroup.induction_on with
      | H w =>
        rw [QuotientAddGroup.eq, hAb, AddSubgroup.mem_map] at hz
        obtain ⟨a, ha, hax⟩ := hz
        have hax' : ((a : W) : W ⧸ B) = -((x : W) : W ⧸ B) + (w : W ⧸ B) := hax
        refine ⟨x + a, hS x hx a ha, ?_⟩
        rw [QuotientAddGroup.mk_add, hax']
        abel
    · intro hy
      exact ⟨y, hy, rfl⟩
  have e1 : Nat.card ((QuotientAddGroup.mk : W ⧸ B → (W ⧸ B) ⧸ Ab) ⁻¹' T) = Nat.card Ab * Nat.card T :=
    (Nat.card_congr (QuotientAddGroup.preimageMkEquivAddSubgroupProdSet Ab T)).trans (Nat.card_prod _ _)
  have e2 : Nat.card Ab = B.relIndex A := by
    rw [hAb, ← AddSubgroup.relIndex_bot_left, ← AddSubgroup.relIndex_comap, AddMonoidHom.comap_bot,
      QuotientAddGroup.ker_mk']
  have e3 : ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard = T.ncard := by
    rw [← Set.ncard_image_of_injective T (QuotientAddGroup.quotientQuotientEquivQuotient B A h).injective]
    congr 1
    rw [hT, Set.image_image, Set.image_image]
    rfl
  rw [← hpre, ← Nat.card_coe_set_eq, e1, e2, e3, Nat.card_coe_set_eq, mul_comm]


open ValuativeRel in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.ContModel.cont_eq {W : Type} [AddCommGroup W]
    {W0 A : AddSubgroup W} {S : Set W} (hA : _root_.GlobalTheory.HL.GoodSub W0 A S) :
    _root_.GlobalTheory.HL.cont W0 S =
      (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * _root_.GlobalTheory.HL.relVol W0 A := by
  have hS : _root_.GlobalTheory.HL.IsCO W0 S := ⟨A, hA⟩
  rw [_root_.GlobalTheory.HL.cont, dite_eq_left hS]
  have hA' : _root_.GlobalTheory.HL.GoodSub W0 hS.choose S := hS.choose_spec
  have hB : (A ⊓ hS.choose).relIndex W0 ≠ 0 := AddSubgroup.relIndex_inf_ne_zero hA.1 hA'.1
  rw [_root_.GlobalTheory.HL.ContModel.relVol_of_le (inf_le_right : A ⊓ hS.choose ≤ hS.choose) hB,
    _root_.GlobalTheory.HL.ContModel.relVol_of_le (inf_le_left : A ⊓ hS.choose ≤ A) hB,
    ← mul_assoc, ← mul_assoc]
  congr 1
  exact_mod_cast (ncard_image_mk_eq_mul_relIndex_of_le (inf_le_right : A ⊓ hS.choose ≤ hS.choose) hA'.2.2.1).symm.trans
    (ncard_image_mk_eq_mul_relIndex_of_le (inf_le_left : A ⊓ hS.choose ≤ A) hA.2.2.1)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]


open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
theorem _root_.GlobalTheory.HL.ContModel.gramT_rmul (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n m : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    _root_.GlobalTheory.HL.gramT L Hm (_root_.GlobalTheory.HL.rmul x A) =
      _root_.GlobalTheory.HL.cT L A * _root_.GlobalTheory.HL.gramT L Hm x * A := by
  ext a b

  simp only [_root_.GlobalTheory.HL.gramT, _root_.GlobalTheory.HL.rmul, _root_.GlobalTheory.HL.hf,
  _root_.GlobalTheory.HL.cT, Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply,
  Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine (Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun l _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
theorem _root_.GlobalTheory.HL.ContModel.cj_mem (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [_root_.Formalism.MainNotions.S.Loc.LocE.O_def] at *
  exact hx.map (L.cj.toAlgHom.restrictScalars 𝒪[F])


open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
theorem _root_.GlobalTheory.HL.ContModel.gramT_thick (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (ϖ : 𝒪[F]) {n m : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (Ω : Set (Fin m → Fin n → E)) (Γ : Matrix (Fin m) (Fin m) E)
    (i : ℕ) (hΩ : ∀ y ∈ Ω, _root_.GlobalTheory.HL.gramT L Hm y = Γ) :
    ∀ x ∈ _root_.GlobalTheory.HL.thick L ϖ Ω i,
      _root_.GlobalTheory.HL.gramT L Hm x ∈ _root_.GlobalTheory.HL.horb L ϖ Γ i := by
  rintro x ⟨y, hy, A, hA, rfl⟩
  exact ⟨A, hA, by rw [_root_.GlobalTheory.HL.ContModel.gramT_rmul, hΩ y hy]⟩

end GlobalTheory.HL.ContModel
end
end

section

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.IdxInt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Frames

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

def Ysp (J : ℕ) : Submodule E S.V := S.spanTo S.f J ⊔ S.spanTo S.f' J

def refB (J : ℕ) (Λ : Submodule L.O S.V) : AddSubgroup (S.V × S.V) :=
  ((S.spanTo S.f J).toAddSubgroup.prod (S.spanTo S.f' J).toAddSubgroup) ⊓
    (Λ.toAddSubgroup.map (algebraMap F E S.th • (LinearMap.id : S.V →ₗ[E] S.V)).toAddMonoidHom).comap
      (AddMonoidHom.fst S.V S.V + AddMonoidHom.snd S.V S.V)

def refU (J : ℕ) (Λ : Submodule L.O S.V) : AddSubgroup S.V :=
  Λ.toAddSubgroup ⊓ (perp L S.Hm (S.Ysp J)).toAddSubgroup

def refT : AddSubgroup E :=
  (AddMonoidHom.id E + (L.cj : E →+* E).toAddMonoidHom).ker ⊓
    L.O.toAddSubgroup.map (AddMonoidHom.mulLeft (algebraMap F E ((S.ϖ : F) ^ S.a)))

abbrev MW : Type := (S.V × S.V) × S.V × E

def refA (J : ℕ) (Λ : Submodule L.O S.V) : AddSubgroup S.MW :=
  (S.refB J Λ).prod ((S.refU J Λ).prod S.refT)

def sOf (w : S.MW) : E := algebraMap F E 2⁻¹ * S.h w.2.1 w.2.1 + w.2.2

def Mv (J : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V) (w : S.MW) : Prop :=
  S.IsMove J d Λ w.1.1 w.1.2 w.2.1 (S.sOf w)

def MvTo (J : ℕ) (d : S.Datum) (Λ Λ₁ : Submodule L.O S.V) (w : S.MW) : Prop :=
  S.Mv J d Λ w ∧ (Λ₁ : Set S.V) = S.moved Λ w.1.1 w.2.1 (S.sOf w)

def NoLeak (Λ : Submodule L.O S.V) (u : S.V) : Prop := ∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1

def InZ (u : S.V) : Prop := ∃ c : 𝒪[F], S.h u u = algebraMap F E ((S.ϖ : F) ^ S.a * c)

def chiM (j : Fin r) (d : S.Datum) (Λ : Submodule L.O S.V) (b : S.V × S.V) (u : S.V) : ℂ :=
  L.psi0 (-(algebraMap F E S.th⁻¹ *
    S.h (S.h b.1 (S.es j) • S.fr d Λ j.succ + S.h b.2 (S.es' j) • S.fr' d Λ j.succ) u))

def cK (β βJ : ℕ) : ℝ := (S.q : ℝ) ^ S.a * β / βJ

def kern (β J βJ : ℕ) (d : S.Datum) (Λ Λ₁ : Submodule L.O S.V) : ℝ :=
  S.cK β βJ * (cint (S.refA J Λ) (ind (S.MvTo J d Λ Λ₁))).re

end GlobalTheory.HL.Frames
end
end

section

noncomputable section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise

namespace GlobalTheory.HL

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

structure Coord (P : LocNG.FPair H r) (S : Frames M.L r k) where
  e : V ≃ₗ[E] S.V
  h_eq : ∀ x y, S.h (e x) (e y) = H.h x y
  f_eq : ∀ a, S.f a = e (P.A.f a)
  f'_eq : ∀ a, S.f' a = e (P.B.f a)
  es_eq : ∀ a, S.es a = e (P.A.es a)
  es'_eq : ∀ a, S.es' a = e (P.B.es a)
  T_eq : (S.T : F) = P.A.T
  T'_eq : (S.T' : F) = P.B.T
  gg_none : M.split = none → S.gg = false
  gg_some : ∀ g, M.split = some g → S.gg = true ∧ S.ϖ = g.q

namespace Coord

variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)

def grp : (V ≃ₗ[E] V) ≃* S.GLV where
  toFun g := (c.e.symm.trans g).trans c.e
  invFun g := (c.e.trans g).trans c.e.symm
  left_inv g := by ext v; simp
  right_inv g := by ext v; simp
  map_mul' a b := by ext v; simp

def lat (Λ : Submodule M.L.O V) : Submodule M.L.O S.V :=
  Λ.map ((c.e : V →ₗ[E] S.V).restrictScalars M.L.O)

def inn (f : Fin (r + 1) → V) (L : Submodule M.L.O (H.Wb f)) : Submodule M.L.O S.V :=
  c.lat ((L.comap ((H.mkW f).restrictScalars M.L.O)).map ((H.perp (H.X f)).subtype.restrictScalars M.L.O))

def dat (d : LocNG.Datum P) : S.Datum :=
  (c.inn P.A.f d.L, c.inn P.B.f d.L',
    {p | ∃ (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))), p = (c.e x', c.e x) ∧
      ((M.split = none ∧ H.mkW P.B.f x' ∈ d.L' ∧ H.mkW P.A.f x ∈ d.L) ∨
        (H.mkW P.B.f x', H.mkW P.A.f x) ∈ d.io)})

end Coord

end GlobalTheory.HL
end
end
