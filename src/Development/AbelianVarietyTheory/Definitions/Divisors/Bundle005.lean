module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Aesop.BuiltinRules
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UCls.Model

open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
variable (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)

theorem isUA_mul {g h : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUA c G g) (hh : IsUA c G h) :
    IsUA c G (g * h) :=
  ⟨by rw [det_mul]; exact hg.1.mul hh.1, fun x y => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hg.2, hh.2]⟩

theorem isUA_inv {g : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUA c G g) : IsUA c G g⁻¹ :=
  ⟨isUnit_nonsing_inv_det g hg.1, fun x y => by
    rw [← hg.2, mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv g hg.1, one_mulVec, one_mulVec]⟩

theorem IsKM_maps {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) {x : Fin n → RA F E}
    (hx : x ∈ hat F L) : k *ᵥ x ∈ hat F L := by
  obtain ⟨y, hy, e⟩ := hk.2.1 x hx
  have : k *ᵥ x = M • y + x := by rw [← e]; abel
  rw [this]
  exact add_mem (nsmul_mem hy M) hx

theorem isKM_mul {k h : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) (hh : IsKM c G L M h) :
    IsKM c G L M (k * h) := by
  refine ⟨isUA_mul c G hk.1 hh.1, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, e⟩ := hk.2.1 _ (IsKM_maps c G L M hh hx)
    obtain ⟨z, hz, e'⟩ := hh.2.1 x hx
    refine ⟨y + z, add_mem hy hz, ?_⟩
    rw [← mulVec_mulVec, smul_add, ← e, ← e']; abel
  · obtain ⟨y, hy, e⟩ := hk.2.2 x hx
    obtain ⟨z, hz, e'⟩ := hh.2.2 y hy
    exact ⟨z, hz, by rw [← mulVec_mulVec, e', e]⟩

theorem isKM_inv {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) : IsKM c G L M k⁻¹ := by
  have hi : ∀ z, k⁻¹ *ᵥ (k *ᵥ z) = z := fun z => by
    rw [mulVec_mulVec, nonsing_inv_mul k hk.1.1, one_mulVec]
  refine ⟨isUA_inv c G hk.1, fun x hx => ?_, fun x hx => ⟨k *ᵥ x, IsKM_maps c G L M hk hx, hi x⟩⟩
  obtain ⟨z, hz, e⟩ := hk.2.2 x hx
  obtain ⟨y, hy, e'⟩ := hk.2.1 z hz
  refine ⟨-y, neg_mem hy, ?_⟩
  rw [← e, hi, smul_neg, ← e']; abel

theorem one_tmul_injective : Function.Injective fun x : E => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x := by
  have hA : Function.Injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)) := by
    obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.1 (RingOfIntegers.not_isField F)
    let v : HeightOneSpectrum (𝓞 F) := ⟨p, hp, hp0⟩
    haveI : Nontrivial (FiniteAdeleRing (𝓞 F) F) := ⟨0, 1, fun h => by
      have := congrArg (fun a : FiniteAdeleRing (𝓞 F) F => a v) h
      exact zero_ne_one (α := v.adicCompletion F) this⟩
    exact (algebraMap F _).injective
  exact Algebra.TensorProduct.includeRight_injective hA

theorem ratM_det (γ : Matrix (Fin n) (Fin n) E) :
    (ratM F γ).det = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ γ.det :=
  (AlgHom.map_det (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) γ).symm

end GlobalTheory.UCls.Model
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

section Abstract

variable {k : Type} [Field k] {M M' M₁ M₂ M₃ : Type} [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
  [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂] [AddCommGroup M₃] [Module k M₃]

structure Cx (k M : Type) [Field k] [AddCommGroup M] [Module k M] where

  C : ℤ → Submodule k M

  D : M →ₗ[k] M

namespace Cx

def IsCx (K : Cx k M) : Prop := ∀ n, ∀ a ∈ K.C n, K.D a ∈ K.C (n + 1) ∧ K.D (K.D a) = 0

def Z (K : Cx k M) (n : ℤ) : Submodule k M := K.C n ⊓ LinearMap.ker K.D

def B (K : Cx k M) (n : ℤ) : Submodule k M := (K.C (n - 1)).map K.D

abbrev H (K : Cx k M) (n : ℤ) : Type := K.Z n ⧸ (K.B n).submoduleOf (K.Z n)

end Cx

def Adj (K : Cx k M) (L : Cx k M') (β : M →ₗ[k] M' →ₗ[k] k) (N : ℤ) : Prop :=
  ∀ n, ∃ ε : ℤˣ, ∀ a ∈ K.C n, ∀ b ∈ L.C (N - n - 1), β (K.D a) b = ε • β a (L.D b)

def IsMap (K : Cx k M) (L : Cx k M') (f : M →ₗ[k] M') : Prop := ∀ n, ∀ a ∈ K.C n, f a ∈ L.C n ∧ f (K.D a) = L.D (f a)

def pt (k : Type) [Field k] : Cx k k := ⟨fun n => if n = 0 then ⊤ else ⊥, 0⟩

end Abstract

section Cech

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module k E]


variable (k ι E) in
def deltaL : (Finset ι → E) →ₗ[k] (Finset ι → E) where
  toFun := GlobalTheory.DI.delta
  map_add' a b := by
    funext t
    simp [GlobalTheory.DI.delta, Finset.sum_add_distrib]
  map_smul' r a := by
    funext t
    simp only [GlobalTheory.DI.delta, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

def cechC (F : Finset ι → Submodule k E) (n : ℤ) : Submodule k (Finset ι → E) :=
  Submodule.pi Set.univ fun s => if s.Nonempty ∧ (s.card : ℤ) = n + 1 then F s else ⊥

def cech (F : Finset ι → Submodule k E) : Cx k (Finset ι → E) := ⟨cechC F, deltaL k ι E⟩

def totD (d : E →ₗ[k] E) : (Finset ι → E) →ₗ[k] (Finset ι → E) :=
  deltaL k ι E + LinearMap.pi fun s => ((-1 : ℤ) ^ s.card) • (d ∘ₗ LinearMap.proj s)

def totC (T : ℕ → Finset ι → Submodule k E) (a b : ℕ) (n : ℤ) : Submodule k (Finset ι → E) :=
  Submodule.pi Set.univ fun s =>
    if s.Nonempty ∧ (a : ℤ) ≤ n + 1 - s.card ∧ n + 1 - s.card < b then T (n + 1 - s.card).toNat s else ⊥

def cupPair [Fintype ι] {E' : Type} [AddCommGroup E'] [Module k E'] (β : E →ₗ[k] E' →ₗ[k] k) :
    (Finset ι → E) →ₗ[k] (Finset ι → E') →ₗ[k] k :=
  ∑ j : ι, β.compl₁₂ (LinearMap.proj (Finset.univ.filter (· ≤ j))) (LinearMap.proj (Finset.univ.filter (j ≤ ·)))

end Cech

section Alg

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [Ring E] [Algebra k E]

end Alg

end GlobalTheory.PD
end
end

section

set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology

namespace GlobalTheory.AnPer.Charts

open CategoryTheory GlobalTheory.CatCoh

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}


set_option autoImplicit false in
open TopologicalSpace Filter Topology in
open CategoryTheory in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} {K : _root_.GlobalTheory.AnPer.Charts F} in
theorem _root_.GlobalTheory.AnPer.Charts.tsze_nil {O : Type} [CommRing O] [Algebra ℂ O] :
    IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom ℂ O (Fin g → O)).toRingHom) := by
  refine ⟨2, ?_⟩
  rw [pow_two, Submodule.zero_eq_bot, ← le_bot_iff, Ideal.mul_le]
  intro x hx y hy
  rw [RingHom.mem_ker] at hx hy
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.fstHom_apply] at hx hy
  rw [Ideal.mem_bot]
  ext <;> simp [hx, hy]


variable (K) in
@[reducible] def jet (k : K.K) : K.Obj where
  k := k
  C := TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))
  alg := ((TrivSqZeroExt.inlHom _ _).comp (K.cst k)).toAlgebra
  J := RingHom.ker (TrivSqZeroExt.fstHom ℂ (Hol (K.W k)) (Fin g → Hol (K.W k))).toRingHom
  nil := tsze_nil
  ρ := TrivSqZeroExt.inlHom _ _
  ρ_cst _ := rfl

def tszeSec {O : Type} [CommRing O] [Algebra ℂ O] (D : Fin g → Derivation ℂ O O) : O →+* TrivSqZeroExt O (Fin g → O) where
  toFun h := TrivSqZeroExt.inl h + TrivSqZeroExt.inr fun a ↦ D a h
  map_one' := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)
  map_zero' := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)
  map_add' x y := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)
  map_mul' x y := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)


set_option autoImplicit false in
open TopologicalSpace Filter Topology in
open CategoryTheory in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} {K : _root_.GlobalTheory.AnPer.Charts F} in
theorem _root_.GlobalTheory.AnPer.Charts.fst_tszeSec {O : Type} [CommRing O] [Algebra ℂ O]
    (D : Fin g → Derivation ℂ O O) (h : O) :
    (_root_.GlobalTheory.AnPer.Charts.tszeSec D h).fst = h := by
  simp [_root_.GlobalTheory.AnPer.Charts.tszeSec]


set_option autoImplicit false in
open TopologicalSpace Filter Topology in
open CategoryTheory in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} {K : _root_.GlobalTheory.AnPer.Charts F} in
theorem _root_.GlobalTheory.AnPer.Charts.snd_tszeSec {O : Type} [CommRing O] [Algebra ℂ O]
    (D : Fin g → Derivation ℂ O O) (h : O) (a : Fin g) :
    (_root_.GlobalTheory.AnPer.Charts.tszeSec D h).snd a = D a h := by
  simp [_root_.GlobalTheory.AnPer.Charts.tszeSec]

def jetSec (k : K.K) : Hol (K.W k) →+* TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)) := tszeSec dw


set_option autoImplicit false in
open TopologicalSpace Filter Topology in
open CategoryTheory in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} {K : _root_.GlobalTheory.AnPer.Charts F} in
theorem _root_.GlobalTheory.AnPer.Charts.tsze_expand {O : Type} [CommRing O] (h : O) (v : Fin g → O) :
    (TrivSqZeroExt.inl h + TrivSqZeroExt.inr v : TrivSqZeroExt O (Fin g → O)) = TrivSqZeroExt.inl h +
      ∑ a, TrivSqZeroExt.inl (v a) * TrivSqZeroExt.inr (Pi.single a (1 : O)) := by
  congr 1
  simp only [TrivSqZeroExt.inl_mul_inr]
  ext b
  · simp [TrivSqZeroExt.fst_sum]
  · simp [TrivSqZeroExt.snd_sum, Finset.sum_apply, Pi.single_apply]

def jet0 (k : K.K) : K.Hom (K.triv k) (K.jet k) :=
  ptHom (K.jet k) (K.le_refl k)

def jet1 (k : K.K) : K.Hom (K.triv k) (K.jet k) :=
  fromTriv (K.jet k) (K.le_refl k) (jetSec k)
    (fun f ↦ TrivSqZeroExt.ext (fst_tszeSec _ _) (funext fun a ↦ (snd_tszeSec _ _ a).trans (dw_cst k a f)))
    (Relation.ReflTransGen.single ⟨fun a ↦ TrivSqZeroExt.inr (Pi.single a 1), fun _ ↦ rfl,
      fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _, fun h ↦ by
        simp only [RingHom.comp_apply, sh_refl]
        exact tsze_expand h fun a ↦ dw a h⟩)

end GlobalTheory.AnPer.Charts
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

def ofCatMap {C D : CommRingCat.{0} ⥤ Cat.{0,0}} (α : C ⟶ D) : ofCat C ⟶ ofCat D :=
  (flipFunctor _ _ _).map (Functor.whiskerLeft Scheme.Γ (Functor.whiskerRight α nerveFunctor))

def Um (N : ℕ) (A : Type) [CommRing A] : Type := {v : Fin N → A // Ideal.span (Set.range v) = ⊤}

instance (N : ℕ) (A : Type) [CommRing A] : SmallCategory (Um N A) where
  Hom v w := {p : GL (Fin N) A × Aˣ // (p.1 : Matrix _ _ A).mulVec v.1 = (p.2 : A) • w.1}
  id v := ⟨1, by simp⟩
  comp f g := ⟨g.1 * f.1, by
    rw [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, f.2, Matrix.mulVec_smul, g.2,
      smul_smul, mul_comm]⟩
  id_comp f := Subtype.ext (mul_one _)
  comp_id f := Subtype.ext (one_mul _)
  assoc f g h := Subtype.ext (mul_assoc _ _ _).symm

def Um.map (N : ℕ) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : Um N A ⥤ Um N B where
  obj v := ⟨f ∘ v.1, by rw [Set.range_comp, ← Ideal.map_span, v.2, Ideal.map_top]⟩
  map {v w} p := ⟨(Matrix.GeneralLinearGroup.map f p.1.1, Units.map (f : A →* B) p.1.2), by
    funext i
    have h := congrArg f (congrFun p.2 i)
    rw [RingHom.map_mulVec] at h
    simpa using h⟩
  map_id v := Subtype.ext (Prod.ext (map_one (Matrix.GeneralLinearGroup.map f)) (map_one (Units.map (f : A →* B))))
  map_comp p q := Subtype.ext (Prod.ext (map_mul (Matrix.GeneralLinearGroup.map f) _ _) (map_mul (Units.map (f : A →* B)) _ _))

def pglCat (N : ℕ) : CommRingCat.{0} ⥤ Cat.{0,0} where
  obj A := Cat.of (Um N A)
  map f := (Um.map N f.hom).toCatHom
  map_id A := rfl
  map_comp f g := rfl

def PGL (N : ℕ) : Spc := ofCat (pglCat N)

def Um.toGL (N : ℕ) (A : Type) [CommRing A] : Um N A ⥤ SingleObj (GL (Fin N) A) where
  obj _ := SingleObj.star _
  map p := p.1.1
  map_id _ := rfl
  map_comp _ _ := rfl

def Um.toLine (N : ℕ) (A : Type) [CommRing A] : Um N A ⥤ SingleObj (GL (Fin 1) A) where
  obj _ := SingleObj.star _
  map p := Matrix.GeneralLinearGroup.scalar (Fin 1) p.1.2
  map_id _ := map_one (Matrix.GeneralLinearGroup.scalar (Fin 1))
  map_comp _ _ := map_mul (Matrix.GeneralLinearGroup.scalar (Fin 1)) _ _

def PGL.pr (N : ℕ) : PGL N ⟶ ofCat (glCat N) :=
  ofCatMap { app := fun A => (Um.toGL N A).toCatHom, naturality := fun _ _ _ => rfl }

def PGL.line (N : ℕ) : PGL N ⟶ ofCat (glCat 1) :=
  ofCatMap
    { app := fun A => (Um.toLine N A).toCatHom
      naturality := fun A B f => by
        apply Cat.Hom.ext
        refine CategoryTheory.Functor.hext (fun _ => rfl) (fun v w p => heq_of_eq ?_)
        change Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.map (f.hom : A →* B) p.1.2) =
          Matrix.GeneralLinearGroup.map f.hom (Matrix.GeneralLinearGroup.scalar (Fin 1) p.1.2)
        ext i j
        obtain rfl : i = j := Subsingleton.elim _ _
        simp }

def prodCat (C D : CommRingCat.{0} ⥤ Cat.{0,0}) : CommRingCat.{0} ⥤ Cat.{0,0} where
  obj A := Cat.of (C.obj A × D.obj A)
  map f := ((C.map f).toFunctor.prod (D.map f).toFunctor).toCatHom
  map_id A := by rw [C.map_id, D.map_id]; rfl
  map_comp f g := by rw [C.map_comp, D.map_comp]; rfl

def liftCat {E : Spc} {C D : CommRingCat.{0} ⥤ Cat.{0,0}} (V : E ⟶ ofCat C) (W : E ⟶ ofCat D) : E ⟶ ofCat (prodCat C D) where
  app n :=
    { app := fun U => TypeCat.ofHom fun x =>
        Functor.prod' (show Fin (n.unop.len + 1) ⥤ C.obj (Scheme.Γ.obj U) from (V.app n).app U x)
          (show Fin (n.unop.len + 1) ⥤ D.obj (Scheme.Γ.obj U) from (W.app n).app U x)
      naturality := fun U U' f => by
        ext x
        have h1 := ConcreteCategory.congr_hom ((V.app n).naturality f) x
        have h2 := ConcreteCategory.congr_hom ((W.app n).naturality f) x
        exact congrArg₂ Functor.prod' h1 h2 }
  naturality n m f := by
    ext U x
    have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (V.naturality f) U) x
    have h2 := ConcreteCategory.congr_hom (NatTrans.congr_app (W.naturality f) U) x
    exact congrArg₂ Functor.prod' h1 h2

def blockMat (a b : ℕ) (A : Type) [CommRing A] :
    Matrix (Fin a) (Fin a) A × Matrix (Fin b) (Fin b) A →* Matrix (Fin (a + b)) (Fin (a + b)) A where
  toFun p := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks p.1 0 0 p.2)
  map_one' := by simp
  map_mul' p q := by simp [Matrix.fromBlocks_multiply]

def blockGL (a b : ℕ) (A : Type) [CommRing A] (g : GL (Fin a) A) (h : GL (Fin b) A) : GL (Fin (a + b)) A :=
  Units.map (blockMat a b A) (MulEquiv.prodUnits.symm (g, h))

theorem blockGL_val (a b : ℕ) (A : Type) [CommRing A] (g : GL (Fin a) A) (h : GL (Fin b) A) :
    Units.val (blockGL a b A g h) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.val 0 0 h.val) := rfl

open CategoryTheory Limits AlgebraicGeometry Opposite in
theorem _root_.GlobalTheory.EtC.blockGL_map (a b : ℕ) {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (g : GL (Fin a) A) (h : GL (Fin b) A) :
    _root_.GlobalTheory.EtC.blockGL a b B (Matrix.GeneralLinearGroup.map f g)
        (Matrix.GeneralLinearGroup.map f h) =
      Matrix.GeneralLinearGroup.map f (_root_.GlobalTheory.EtC.blockGL a b A g h) := by
  ext i j
  simp only [_root_.GlobalTheory.EtC.blockGL_val, Matrix.GeneralLinearGroup.map_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

def blockFun (a b : ℕ) (A : Type) [CommRing A] :
    SingleObj (GL (Fin a) A) × SingleObj (GL (Fin b) A) ⥤ SingleObj (GL (Fin (a + b)) A) where
  obj _ := SingleObj.star _
  map p := blockGL a b A p.1 p.2
  map_id _ := Units.ext (map_one (blockMat a b A))
  map_comp f g := Units.ext (map_mul (blockMat a b A) (Units.val (show GL (Fin a) A from g.1), Units.val (show GL (Fin b) A from g.2))
    (Units.val (show GL (Fin a) A from f.1), Units.val (show GL (Fin b) A from f.2)))

def blockNat (a b : ℕ) : prodCat (glCat a) (glCat b) ⟶ glCat (a + b) where
  app A := (blockFun a b A).toCatHom
  naturality A B f := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.hext (fun _ => rfl) (fun v w p => heq_of_eq ?_)
    exact blockGL_map a b f.hom p.1 p.2

def bsumOf {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) : E ⟶ ofCat (glCat (a + b)) :=
  liftCat V W ≫ ofCatMap (blockNat a b)

def grpSimplex {Γ : Type} [Group Γ] {m : ℕ} (g : Fin m → Γ) : ComposableArrows (SingleObj Γ) m :=
  ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Γ) (fun i => (g i)⁻¹)

def grpPt {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} (g : Fin m → Γ) :
    yoneda.obj X ⟶ (cst (SingleObj Γ) ⨯ sch.obj X).obj (op (SimplexCategory.mk m)) :=
  haveI : PreservesLimit (pair (cst (SingleObj Γ)) (sch.obj X))
      ((evaluation SimplexCategoryᵒᵖ (Scheme.{0}ᵒᵖ ⥤ Type)).obj (op (SimplexCategory.mk m))) :=
    (evaluation_preservesLimitsOfShape (J := Discrete WalkingPair) _).preservesLimit
  prod.lift
    ({ app := fun U => TypeCat.ofHom fun _ => grpSimplex g, naturality := fun _ _ _ => rfl } :
      yoneda.obj X ⟶ (cst (SingleObj Γ)).obj (op (SimplexCategory.mk m))) (𝟙 (yoneda.obj X)) ≫
    (PreservesLimitPair.iso ((evaluation _ _).obj (op (SimplexCategory.mk m))) (cst (SingleObj Γ)) (sch.obj X)).inv

def IsSlant (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} (c : (Fin m → Γ) →₀ R)
    (z : CochainComplex.HomComplex.Cocycle ((chains R).obj (sch.obj X)) ((chains R).obj (cst (SingleObj Γ) ⨯ sch.obj X)) (-(m : ℤ))) :
    Prop :=
  (∀ (p p' : ℤ) (h : p + -(m : ℤ) = p'), p ≠ 0 → z.1.v p p' h = 0) ∧
  z.1.v 0 (-(m : ℤ)) (zero_add _) =
    (((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
        (((SimplicialObject.whiskering _ _).obj (free R)).obj (sch.obj X))).extendXIso
        ComplexShape.embeddingDownNat (i := 0) (i' := 0) (by simp)).hom ≫
      (c.sum fun g r => (ULift.up r : ULift.{1} R) • (free R).map (grpPt X g)) ≫
      (((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
        (((SimplicialObject.whiskering _ _).obj (free R)).obj (cst (SingleObj Γ) ⨯ sch.obj X))).extendXIso
        ComplexShape.embeddingDownNat (i := m) (i' := -(m : ℤ)) (by simp)).inv

def IsSlantMap (R : Type) [CommRing R] (Γ : Type) [Group Γ] (X : Scheme.{0}) (F : Shv R) (m : ℕ) (n : ℤ)
    (S : groupHomology (Rep.trivial R Γ R) m →+ H R (cst (SingleObj Γ) ⨯ sch.obj X) F (m + n) →+ H R (sch.obj X) F n) : Prop :=
  ∀ (c : groupHomology.cycles (Rep.trivial R Γ R) m) z, IsSlant R X (groupHomology.iCycles (Rep.trivial R Γ R) m c) z →
    S (groupHomology.π (Rep.trivial R Γ R) m c) = HK.pre R z F (m + n) n (by ring)


open scoped Classical in
open Classical in
def slantR (R : Type) [CommRing R] (Γ : Type) [Group Γ] (X : Scheme.{0}) (F : Shv R) (m : ℕ) (n : ℤ) :
    groupHomology (Rep.trivial R Γ R) m →+ H R (cst (SingleObj Γ) ⨯ sch.obj X) F (m + n) →+ H R (sch.obj X) F n :=
  if h : ∃ S, IsSlantMap R Γ X F m n S then h.choose else 0

end GlobalTheory.EtC

end
end
