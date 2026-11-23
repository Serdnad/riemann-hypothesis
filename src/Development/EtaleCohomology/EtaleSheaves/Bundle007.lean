module

public import Development.EtaleCohomology.EtaleSheaves.Bundle004
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
public import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

section

noncomputable section
open CategoryTheory Limits Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC Pretriangulated

namespace LateralTheory.E.E8.ExciseCut.ConeZeroPf

universe u v

theorem tri_zero {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, Functor.Additive (CategoryTheory.shiftFunctor D n)] [Pretriangulated D]
    (T : Triangle D) (hT : T ∈ distTriang D) (Y : ℤ → D) (e : ∀ n, Y n ≅ (Y (n - 1))⟦(1 : ℤ)⟧)
    (hb : ∀ n, Function.Bijective (fun g : T.obj₂ ⟶ Y n => T.mor₁ ≫ g)) (n : ℤ) (x : T.obj₃ ⟶ Y n) : x = 0 := by
  have hy : T.mor₂ ≫ x = 0 := by
    apply (hb n).1
    simp only [comp_zero, ← Category.assoc, comp_distTriang_mor_zero₁₂ T hT, zero_comp]
  obtain ⟨g, rfl⟩ := Triangle.yoneda_exact₃ T hT x hy
  obtain ⟨h, hh⟩ := (CategoryTheory.shiftFunctor D (1 : ℤ)).map_surjective (g ≫ (e n).hom)
  obtain ⟨k, rfl⟩ := (hb (n - 1)).2 h
  have : g = (CategoryTheory.shiftFunctor D (1 : ℤ)).map (T.mor₁ ≫ k) ≫ (e n).inv := by
    rw [hh, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [this, Functor.map_comp]
  simp only [← Category.assoc, comp_distTriang_mor_zero₃₁ T hT, zero_comp]

variable (R : Type) [CommRing R]

theorem pull_toHom {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (n : ℤ) (x : HK R L F n) :
    CohomologyClass.toHom (HK.pull R φ F n x) =
      (HomotopyCategory.quotient _ _).map φ ≫ CohomologyClass.toHom x := by
  obtain ⟨b, rfl⟩ := x.mk_surjective
  have : zcomp (Cocycle.ofHom φ) b (zero_add n) = b.precomp φ := by
    ext p q hpq
    simp [zcomp, Cocycle.precomp]
  change CohomologyClass.toHom (CohomologyClass.mk (zcomp (Cocycle.ofHom φ) b (zero_add n))) = _
  rw [this, CohomologyClass.toHom_mk, CohomologyClass.toHom_mk, Cocycle.equivHomShift_symm_precomp, Functor.map_comp]

theorem hb' {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (hb : ∀ n, Function.Bijective (HK.pull R φ F n)) (n : ℤ) :
    Function.Bijective (fun g : (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj L ⟶
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj ((res R F)⟦n⟧) =>
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).map φ ≫ g) := by
  have : (fun g : (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj L ⟶
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj ((res R F)⟦n⟧) =>
      (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).map φ ≫ g) =
      (CohomologyClass.homAddEquiv) ∘ (HK.pull R φ F n) ∘ (CohomologyClass.homAddEquiv.symm) := by
    funext g
    simp only [Function.comp_apply, CohomologyClass.homAddEquiv_apply, pull_toHom]
    congr 1
    exact (CohomologyClass.homAddEquiv.apply_symm_apply g).symm
  rw [this]
  exact CohomologyClass.homAddEquiv.bijective.comp ((hb n).comp CohomologyClass.homAddEquiv.symm.bijective)

def shIso (E : Cx R) (n : ℤ) :
    (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj (E⟦n⟧) ≅
      ((HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj (E⟦n - 1⟧))⟦(1 : ℤ)⟧ :=
  (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).mapIso
    ((CategoryTheory.shiftFunctorAdd' (CochainComplex (Shv R) ℤ) (n - 1) 1 n (by omega)).app E) ≪≫
    ((HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).app (E⟦n - 1⟧)

end LateralTheory.E.E8.ExciseCut.ConeZeroPf

open LateralTheory.E.E8.ExciseCut.ConeZeroPf in
theorem LateralTheory.E.E8.ExciseCut.LeafConeZero_of : LateralTheory.E.E8.ExciseCut.LeafConeZero := by
  intro R _ K L φ F hb n
  refine ⟨fun x y => ?_⟩
  apply (CohomologyClass.toHom_bijective _ _ _).1
  have hz := fun x : HK R (mappingCone φ) F n =>
    tri_zero (mappingCone.triangleh φ) (HomotopyCategory.mappingCone_triangleh_distinguished φ)
      (fun n => (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)).obj ((res R F)⟦n⟧))
      (shIso R (res R F)) (hb' R φ F hb) n (CohomologyClass.toHom x)
  exact (hz x).trans (hz y).symm
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafNatCupPf

section

variable {R : Type} [CommRing R]

theorem chainsXIso_inv_map {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  dsimp only [chains, chainsXIso, Functor.comp_map]
  rw [ComplexShape.embeddingDownNat.extendFunctor_map (C := Shv R)]
  erw [HomologicalComplex.extendMap_f _ _ (i := p) (i' := -(p : ℤ)) rfl]
  simp only [chainsN]
  erw [Iso.inv_hom_id_assoc]
  simp

theorem free_map_freeGen {P Q : PSh} (g : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map g).hom.app (op U)).hom (freeGen R P U x) = freeGen R Q U (g.app (op U) x) := by
  have h := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (ULift.up x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map g))
  have h2 : (((freeP R).map g).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (g.app (op U) x)) :=
    ModuleCat.free_map_apply (R := ULift.{1} R) _ _
  exact h.symm.trans (congrArg ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom h2)

theorem ev_pull {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x =
      ev α p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x) := by
  simp only [ev]
  rw [Cochain.comp_v _ _ (zero_add n) (-(p : ℤ)) (-(p : ℤ)) s (add_zero _) h, Cochain.ofHom_v,
    ← Category.assoc, chainsXIso_inv_map, Category.assoc]
  rw [← free_map_freeGen]
  rfl

theorem sub_pull {E E' : Spc} (f : E ⟶ E') {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (f.app (op (SimplexCategory.mk l))).app (op U) (x.sub j l h) =
      Sx.sub (E := E') (N := N) ((f.app (op (SimplexCategory.mk N))).app (op U) x) j l h := by
  have := ConcreteCategory.congr_hom (congr_app (f.naturality (SimplexCategory.subinterval j l h).op) (op U)) x
  simp only [Sx.sub]
  exact this

theorem isAW_pull {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E') I n) (β : Cochain ((chains R).obj E') J m) (γ : Cochain ((chains R).obj E') K k)
    (hγ : μ.IsAW hk α β γ) :
    μ.IsAW hk ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n))
      ((Cochain.ofHom ((chains R).map f)).comp β (zero_add m))
      ((Cochain.ofHom ((chains R).map f)).comp γ (zero_add k)) := by
  intro N w h U x
  rw [ev_pull, hγ]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ev_pull, ev_pull, sub_pull, sub_pull]

theorem pull_mk {E E' : Spc} (f : E ⟶ E') (F : Shv R) (n : ℤ) (z : Cocycle ((chains R).obj E') (res R F) n) :
    pull R f F n (CohomologyClass.mk z) = CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add n)) :=
  rfl

theorem zcomp_ofHom_val {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (z : Cocycle ((chains R).obj E') I n) :
    (zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add n)).1 = (Cochain.ofHom ((chains R).map f)).comp z.1 (zero_add n) :=
  rfl

end

open CupProductRingLaws in
theorem LeafNatCup_of (hc : LeafCupSpec) : LeafNatCup := by
  intro q _ E E' f n m i j a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := (hc (ZMod q) (twPair q i j) E' rfl).1 α β
  have e1 : cup q (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ :=
    (hc (ZMod q) (twPair q i j) E' rfl).2 α β γ hγ
  have hAW := isAW_pull (twPair q i j) f rfl α.1 β.1 γ.1 hγ
  rw [← zcomp_ofHom_val, ← zcomp_ofHom_val, ← zcomp_ofHom_val] at hAW
  have e2 := (hc (ZMod q) (twPair q i j) E rfl).2 _ _ _ hAW
  rw [e1, pull_mk, pull_mk, pull_mk]
  exact e2.symm

end LateralTheory.E.LeafNatCupPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafNatOnePf

variable {R : Type} [CommRing R]

theorem free_map_freeGen {P Q : PSh} (g : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map g).hom.app (op U)).hom (freeGen R P U x) = freeGen R Q U (g.app (op U) x) := by
  have h := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map g))
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.coe_comp] at h
  unfold freeGen
  refine h.symm.trans (congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom y) ?_)
  exact ModuleCat.free_map_apply (R := ULift.{1} R) (uliftFunctor.{1}.map (g.app (op U))) (ULift.up.{1} x)

theorem chainsXIso_nat {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  unfold chainsXIso chains
  rw [Functor.comp_map, ComplexShape.Embedding.extendFunctor_map,
    HomologicalComplex.extendMap_f _ _ (i := p) (i' := -(p : ℤ)) rfl]
  erw [Iso.inv_hom_id_assoc]
  rfl

theorem ev_pull {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E') I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x) := by
  unfold ev
  rw [Cochain.comp_v _ _ (zero_add n) (-(p : ℤ)) (-(p : ℤ)) s (by omega) (by omega), Cochain.ofHom_v,
    ← Category.assoc, chainsXIso_nat, Category.assoc]
  rw [← free_map_freeGen]
  rfl

theorem LeafNatOne_of (hOne : LateralTheory.E.CupProductRingLaws.LeafOneSpec) : LateralTheory.E.CupProductRingLaws.LeafNatOne := by
  intro q _ E E' f hE'
  have hE : Inv q E := fun U ⟨x⟩ => hE' U ⟨(f.app (op (SimplexCategory.mk 0))).app (op U) x⟩
  obtain ⟨⟨α, hα⟩, h'⟩ := hOne q E' hE'
  rw [h' α hα]
  let β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0 :=
    zcomp (Cocycle.ofHom ((chains (ZMod q)).map f)) α (zero_add 0)
  have hβ : LateralTheory.E.CupProductRingLaws.IsOneCocycle q E β := fun U x ζ => by
    rw [← hα U ((f.app (op (SimplexCategory.mk 0))).app (op U) x) ζ]
    exact ev_pull f α.1 0 0 _ U x
  rw [(hOne q E hE).2 β hβ]
  rfl

end LateralTheory.E.LeafNatOnePf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwPairUniquePf

def PairHtpy {R : Type} [CommRing R] {I J K : Cx R} (μ μ' : Pair I J K) : Prop :=
  ∃ h : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w + 1 →
      Sec (I.X s) U →ₗ[ULift.{1} R] Sec (J.X t) U →ₗ[ULift.{1} R] Sec (K.X w) U,
    (∀ {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (hw : s + t = w + 1) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      Sec.res g (h U s t w hw a b) = h V s t w hw (Sec.res g a) (Sec.res g b)) ∧
    ∀ (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      μ.mul U s t w hw a b - μ'.mul U s t w hw a b =
        Sec.map (K.d (w - 1) w) (h U s t (w - 1) (by omega) a b) +
          h U (s + 1) t w (by omega) (Sec.map (I.d s (s + 1)) a) b +
          s.negOnePow • h U s (t + 1) w (by omega) a (Sec.map (J.d t (t + 1)) b)

def LeafTwPairHtpy : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ) (μ μ' : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j)))),
  IsTwPair μ → IsTwPair μ' → PairHtpy μ μ'

def LeafHtpyAW : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ μ' : Pair I J K), PairHtpy μ μ' →
  ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ γ' : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ'.IsAW hk α.1 β.1 γ'.1 →
    CohomologyClass.mk γ = CohomologyClass.mk γ'

theorem cup_eq_of_aw {R : Type} [CommRing R] {I J K : Cx R} (hc : LateralTheory.E.CupProductRingLaws.LeafCupSpec) (μ μ' : Pair I J K)
    (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (hAW : ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
      (γ γ' : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ'.IsAW hk α.1 β.1 γ'.1 →
      CohomologyClass.mk γ = CohomologyClass.mk γ') :
    μ.cup E hk = μ'.cup E hk := by
  obtain ⟨ex, sp⟩ := hc R μ E hk
  obtain ⟨ex', sp'⟩ := hc R μ' E hk
  ext a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := ex α β
  obtain ⟨γ', hγ'⟩ := ex' α β
  rw [sp α β γ hγ, sp' α β γ' hγ']
  exact hAW α β γ γ' hγ hγ'

end LateralTheory.E.LeafTwPairUniquePf

open LateralTheory.E.LeafTwPairUniquePf in
theorem LateralTheory.E.CupProductRingLaws.LeafTwPairUnique_of (hc : LateralTheory.E.CupProductRingLaws.LeafCupSpec) (hh : LeafTwPairHtpy)
    (ha : LeafHtpyAW) : LateralTheory.E.CupProductRingLaws.LeafTwPairUnique := by
  intro q _ i j μ μ' hμ hμ' E n m k hk
  exact cup_eq_of_aw hc μ μ' E hk (ha (ZMod q) μ μ' (hh q i j μ μ' hμ hμ') E hk)
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8.TwSec.FieldZ

variable {q : ℕ} [NeZero q] {K : Type} [CommRing K] [IsDomain K]

theorem prim_isPrim (ξ : Prim q K) : IsPrimitiveRoot ξ.1 q := by
  have : NeZero (q : K) := ⟨ξ.2.1.ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic q (Int.castRingHom K)]
  have h := ξ.2.2
  rw [Polynomial.aeval_def] at h
  rw [Polynomial.IsRoot, Polynomial.eval_map]
  simpa [Polynomial.eval₂_eq_eval_map] using h

theorem pow_val (ζ : Prim q K) (n : ℕ) : ζ.1 ^ n = ζ.1 ^ ((n : ZMod q).val) := by
  rw [ZMod.val_natCast]
  conv_lhs => rw [← Nat.mod_add_div n q, pow_add, pow_mul, (prim_isPrim ζ).pow_eq_one, one_pow, mul_one]

theorem exists_unit (ζ ξ : Prim q K) : ∃ u : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (u : ZMod q).val := by
  obtain ⟨i, hi, h⟩ := (prim_isPrim ζ).eq_pow_of_pow_eq_one (prim_isPrim ξ).pow_eq_one
  have hc : i.Coprime q := ((prim_isPrim ζ).pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (h ▸ prim_isPrim ξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, h]

theorem unit_unique (ζ : Prim q K) {u v : (ZMod q)ˣ} (h : ζ.1 ^ (u : ZMod q).val = ζ.1 ^ (v : ZMod q).val) : u = v :=
  Units.ext (ZMod.val_injective q ((prim_isPrim ζ).pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))


open Classical in
def ex (j : ℤ) (ζ : Prim q K) (ξ : Prim q K) : ZMod q :=
  if h : ∃ u : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (u : ZMod q).val then (((h.choose) ^ j : (ZMod q)ˣ) : ZMod q) else 0

theorem ex_spec (j : ℤ) (ζ ξ : Prim q K) (u : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (u : ZMod q).val) :
    ex j ζ ξ = ((u ^ j : (ZMod q)ˣ) : ZMod q) := by
  have he : ∃ u : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (u : ZMod q).val := ⟨u, h⟩
  unfold ex
  rw [dite_eq_left he, unit_unique ζ (he.choose_spec.symm.trans h)]

def Φ (j : ℤ) (ζ : Prim q K) : (Prim q K →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination (ULift.{1} (ZMod q)) (fun ξ => ULift.up (ex j ζ ξ))

theorem rel_le (j : ℤ) (ζ : Prim q K) : twRel q j K ≤ LinearMap.ker (Φ j ζ) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ', ξ, a, h, rfl⟩
  obtain ⟨u, hu⟩ := exists_unit ζ ζ'
  have hξ : ξ.1 = ζ.1 ^ ((u * a : (ZMod q)ˣ) : ZMod q).val := by
    rw [h, hu, ← pow_mul, pow_val ζ, Units.val_mul, Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  simp only [SetLike.mem_coe, LinearMap.mem_ker, Φ, map_sub, Finsupp.linearCombination_single]
  rw [ex_spec j ζ ξ _ hξ, ex_spec j ζ ζ' _ hu, mul_zpow]
  apply ULift.ext
  simp [mul_comm]

theorem key (j : ℤ) (ζ : Prim q K) (c : ZMod q)
    (h : (ULift.up.{1} c • Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q))) :
      (Prim q K →₀ ULift.{1} (ZMod q)) ⧸ twRel q j K) = 0) : c = 0 := by
  have h2 := congrArg ((twRel q j K).liftQ (Φ j ζ) (rel_le j ζ)) h
  rw [LinearMap.map_smul, Submodule.liftQ_apply, map_zero, Φ, Finsupp.linearCombination_single,
    ex_spec j ζ ζ 1 ((pow_one ζ.1).symm.trans (by rw [pow_val ζ 1, Nat.cast_one, Units.val_one]))] at h2
  have h3 := congrArg ULift.down h2
  simpa using h3

end FieldZ

theorem LeafTwFieldZ_of : LeafTwFieldZ := by
  intro q _ j K hK ζ c h
  have : IsDomain K := hK.isDomain
  exact FieldZ.key j ζ c h

end LateralTheory.E.E8.TwSec
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.E.E8.TwSec

theorem twAdj_comap_surj (A : Type) [CommRing A] (q : ℕ) [NeZero q] :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (AdjoinRoot (cyclotomic q A)))) := by
  have hm := cyclotomic.monic q A
  have := Module.Free.of_basis (AdjoinRoot.powerBasis' hm).basis
  have : Module.Finite A (AdjoinRoot (cyclotomic q A)) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis' hm).basis
  intro p
  have : Nontrivial A := by
    rcases subsingleton_or_nontrivial A with h | h
    · exact absurd (Subsingleton.elim p.asIdeal ⊤) p.isPrime.ne_top
    · exact h
  have : Nontrivial (AdjoinRoot (cyclotomic q A)) := by
    have hd : 0 < (cyclotomic q A).natDegree := by
      rw [natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos q)
    have : Nonempty (Fin (cyclotomic q A).natDegree) := ⟨⟨0, hd⟩⟩
    exact (AdjoinRoot.powerBasisAux' hm).repr.symm.injective.nontrivial
  exact Algebra.IsIntegral.comap_surjective A _ p

theorem twAdj_etale (A : Type) [CommRing A] (q : ℕ) (hq : IsUnit (q : A)) :
    Algebra.Etale A (AdjoinRoot (cyclotomic q A)) := by
  have hsep : (cyclotomic q A).Separable :=
    (separable_X_pow_sub_C_unit (1 : Aˣ) hq).of_dvd (by simpa using cyclotomic.dvd_X_pow_sub_one q A)
  obtain ⟨a, b, hab⟩ := hsep
  let P : StandardEtalePair A := ⟨cyclotomic q A, cyclotomic.monic q A, 1,
    ⟨b, a, 0, by rw [pow_zero, ← hab]; ring⟩⟩
  let e1 : P.Ring ≃ₐ[A] Localization.Away (AdjoinRoot.mk (cyclotomic q A) 1) := P.equivAwayAdjoinRoot
  let e2 : AdjoinRoot (cyclotomic q A) ≃ₐ[AdjoinRoot (cyclotomic q A)]
      Localization.Away (AdjoinRoot.mk (cyclotomic q A) 1) :=
    IsLocalization.atUnit _ _ (AdjoinRoot.mk (cyclotomic q A) 1) (by rw [map_one]; exact isUnit_one)
  have := Algebra.IsStandardEtale.of_equiv (e1.trans (e2.symm.restrictScalars A))
  infer_instance

theorem LeafTwAdj_of : LeafTwAdj := by
  intro q _ U u hq
  obtain ⟨R, f, hf, ⟨x, rfl⟩, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (X := U) (x := u) (U := ⊤) (by simp)
  have hqR : IsUnit ((q : ℕ) : R) := by
    simpa using (hq.map f.appTop.hom).map (Scheme.ΓSpecIso R).hom.hom
  have := twAdj_etale R q hqR
  let φ : R ⟶ CommRingCat.of (AdjoinRoot (cyclotomic q R)) :=
    CommRingCat.ofHom (algebraMap R (AdjoinRoot (cyclotomic q R)))
  have hφ : Etale (Spec.map φ) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr this)
  refine ⟨Spec (.of (AdjoinRoot (cyclotomic q R))), Spec.map φ ≫ f, inferInstance, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := twAdj_comap_surj R q x
    refine ⟨y, ?_⟩
    subst hy
    rfl
  · let ψ := (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot (cyclotomic q R)))).inv.hom
    refine ⟨⟨ψ (AdjoinRoot.root _), ?_, ?_⟩⟩
    · simpa using (hqR.map (algebraMap R (AdjoinRoot (cyclotomic q R)))).map ψ
    · have h0 : aeval (AdjoinRoot.root (cyclotomic q R)) (cyclotomic q ℤ) = 0 := by
        rw [← aeval_map_algebraMap R, map_cyclotomic, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      have := aeval_algHom_apply ψ.toIntAlgHom (AdjoinRoot.root (cyclotomic q R)) (cyclotomic q ℤ)
      rw [h0, map_zero] at this
      exact this

end LateralTheory.E.E8.TwSec
end
end
