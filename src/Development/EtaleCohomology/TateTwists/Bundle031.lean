module

public import Development.EtaleCohomology.TateTwists.TensorVanishing.TensZero
public import Development.EtaleCohomology.TateTwists.Bundle024
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleFoundations.columnPf

theorem loc_top (U : Scheme.{0}) {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (hPQ : ∀ V g, P V g → Q V g) :
    Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h1 : Loc U P) (h2 : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hP⟩ := h1
  obtain ⟨T, hT, hQ⟩ := h2
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hP V g hg.1, hQ V g hg.2⟩⟩

theorem loc_bind {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} {Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U P) (hPQ : ∀ V g, P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  classical
  obtain ⟨S, hS, hP⟩ := h
  choose T hT hQ using hPQ
  refine ⟨Sieve.bind S.arrows fun V g hg => T V g (hP V g hg), Scheme.etaleTopology.bind_covering hS
    (fun V g hg => hT V g (hP V g hg)), ?_⟩
  rintro W _ ⟨V, k, g, hg, hk, rfl⟩
  exact hQ V g (hP V g hg) W k hk

theorem loc_finset {ι : Type*} (s : Finset ι) {U : Scheme.{0}} {P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : ∀ i ∈ s, Loc U (P i)) : Loc U fun V g => ∀ i ∈ s, P i V g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact loc_top U (by simp)
  | insert a s ha ih =>
    have := loc_and (h a (by simp)) (ih fun i hi => h i (by simp [hi]))
    exact loc_mono this fun V g ⟨h1, h2⟩ i hi => by
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact h1
      · exact h2 i hi

theorem loc_empty (U : Scheme.{0}) [IsEmpty U] (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) : Loc U P :=
  ⟨⊥, Scheme.bot_mem_grothendieckTopology U, fun _ _ h => h.elim⟩

def lift : Prop :=
  ∀ (R : Type) [CommRing R] (M : Shv R) (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ M.obj),
    (∀ (U : Scheme.{0}) (y : Sec M U), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = Sec.res g y) →
    (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) →
    ∀ (F G : Shv R) (δ : F ⟶ G) (U : Scheme.{0}) (x : Sec F U ⊗[ULift.{1} R] Sec M U),
      TensorProduct.map (δ.hom.app (op U)).hom LinearMap.id x = 0 →
      Loc U fun V g => ∃ x' : Sec F V ⊗[ULift.{1} R] P.obj (op V),
        TensorProduct.map (δ.hom.app (op V)).hom LinearMap.id x' = 0 ∧
        TensorProduct.map LinearMap.id (φ.app (op V)).hom x' = TensorProduct.map (F.obj.map g.op).hom (M.obj.map g.op).hom x

def kill : Prop :=
  ∀ (R : Type) [CommRing R] (C : Cx R) (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)),
    LateralTheory.EtaleFoundations.acyc.LocAcyc C → ∀ (V : Scheme.{0}) (s : ℤ) (x' : Sec (C.X s) V ⊗[ULift.{1} R] P.obj (op V)),
      Module.Flat (ULift.{1} R) (P.obj (op V)) →
      TensorProduct.map ((C.d s (s + 1)).hom.app (op V)).hom LinearMap.id x' = 0 →
      Loc V fun W k => ∃ y : Sec (C.X (s - 1)) W ⊗[ULift.{1} R] P.obj (op W),
        TensorProduct.map ((C.d (s - 1) s).hom.app (op W)).hom LinearMap.id y =
          TensorProduct.map ((C.X s).obj.map k.op).hom (P.map k.op).hom x'

end LateralTheory.EtaleFoundations.columnPf

open LateralTheory.EtaleFoundations.columnPf in
theorem LateralTheory.EtaleFoundations.acyc.column_of_cut (hL : lift) (hK : kill) : LateralTheory.EtaleFoundations.acyc.column := by
  intro R _ C J hJ hC U s t x hx
  obtain ⟨P, φ, hsurj, hker, hflat⟩ := hJ t
  refine loc_bind (hL R (J.X t) P φ hsurj hker (C.X s) (C.X (s + 1)) (C.d s (s + 1)) U x hx) ?_
  rintro V g ⟨x', hx'0, hx'⟩
  by_cases hV : Nonempty V
  · refine loc_mono (hK R C P hC V s x' (hflat V hV) hx'0) ?_
    rintro W k ⟨y, hy⟩
    refine ⟨TensorProduct.map LinearMap.id (φ.app (op W)).hom y, ?_⟩
    have e1 : TensorProduct.map ((C.d (s - 1) s).hom.app (op W)).hom LinearMap.id
        (TensorProduct.map LinearMap.id (φ.app (op W)).hom y) =
        TensorProduct.map LinearMap.id (φ.app (op W)).hom
          (TensorProduct.map ((C.d (s - 1) s).hom.app (op W)).hom LinearMap.id y) := by
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp, ← TensorProduct.map_comp]
      rfl
    rw [e1, hy, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
    have e2 : (TensorProduct.map ((C.X s).obj.map (k ≫ g).op).hom ((J.X t).obj.map (k ≫ g).op).hom) x =
        TensorProduct.map ((C.X s).obj.map k.op).hom ((J.X t).obj.map k.op).hom
          (TensorProduct.map ((C.X s).obj.map g.op).hom ((J.X t).obj.map g.op).hom x) := by
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, op_comp, Functor.map_comp, Functor.map_comp]
      rfl
    rw [e2, ← hx', ← LinearMap.comp_apply, ← TensorProduct.map_comp]
    congr 2
    have := φ.naturality k.op
    exact congrArg ModuleCat.Hom.hom this
  · have : IsEmpty V := not_nonempty_iff.1 hV
    exact loc_empty V _

open LateralTheory.EtaleFoundations.columnPf in
theorem LateralTheory.EtaleFoundations.columnPf.kill_of : kill := by
  classical
  intro R _ C P hC V s x' hflat hx'
  set d := ((C.d s (s + 1)).hom.app (op V)).hom
  have hex := Module.Flat.rTensor_exact (M := P.obj (op V)) (LinearMap.exact_subtype_ker_map d)
  obtain ⟨w, hw⟩ := (hex x').1 hx'
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset w
  have hloc : ∀ i ∈ S, Loc V fun W k => ∃ y : Sec (C.X (s - 1)) W,
      Sec.map (C.d (s - 1) s) y = Sec.res k (i.1 : Sec (C.X s) V) := fun i _ =>
    hC V s (i.1 : Sec (C.X s) V) i.1.2
  refine loc_mono (loc_finset S hloc) ?_
  intro W k hk
  choose y hy using hk
  refine ⟨∑ i ∈ S.attach, y i.1 i.2 ⊗ₜ (P.map k.op).hom i.1.2, ?_⟩

  rw [map_sum, ← hw, hS, map_sum, map_sum]
  rw [← Finset.sum_attach S]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.id_apply]
  congr 1
  exact hy i.1 i.2
end

section

open CategoryTheory GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations.KTP

theorem twGenR_nat {q : ℕ} (A B : CommRingCat.{0}) (f : A ⟶ B) (ζ : Prim q A) :
    ((twF q 1).map f).hom (twGenR A ζ) = twGenR B (Prim.map f.hom ζ) := by
  change Submodule.Quotient.mk (Finsupp.lmapDomain _ _ _ (Finsupp.single ζ 1)) = _
  simp [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rfl

theorem prim_pow {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hp
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, ζ.2.2, zero_mul] at h
  exact sub_eq_zero.1 h

theorem list_pow {q : ℕ} {A : Type} [CommRing A] (l : List (Prim q A)) : ((l.map fun ζ => ζ.1).prod) ^ q = 1 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [mul_pow, prim_pow, ih]

theorem q_smul {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (x : M) : q • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext; simp
  rw [this, zero_smul]

variable {q : ℕ} {A : Type} [CommRing A] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]

theorem sum_eq_of_prod_eq [NeZero q] (τ' : Prim q A → M)
    (hl : ∀ l : List (Prim q A), (l.map fun ζ => ζ.1).prod = 1 → (l.map τ').sum = 0)
    (l1 l2 : List (Prim q A)) (h : (l1.map fun ζ => ζ.1).prod = (l2.map fun ζ => ζ.1).prod) :
    (l1.map τ').sum = (l2.map τ').sum := by
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have := hl (l1 ++ (List.replicate (q - 1) l2).flatten) (by
    simp only [List.map_append, List.prod_append, List.map_flatten, List.map_replicate, List.prod_flatten,
      List.prod_replicate, h, ← pow_succ']
    rw [Nat.sub_add_cancel hq, list_pow])
  simp only [List.map_append, List.sum_append, List.map_flatten, List.map_replicate, List.sum_flatten,
    List.sum_replicate] at this
  have h2 := q_smul (q := q) (l2.map τ').sum
  have h3 : q • (l2.map τ').sum = (q - 1) • (l2.map τ').sum + (l2.map τ').sum := by
    rw [← succ_nsmul, Nat.sub_add_cancel hq]
  rw [h3] at h2
  have := this.trans h2.symm
  rw [add_comm ((q-1) • _) _] at this
  exact add_left_cancel (a := (q-1) • (l2.map τ').sum) (by rw [add_comm _ (List.sum _), this, add_comm])

def rel (q : ℕ) [NeZero q] (A : Type) [CommRing A] : Setoid Aˣ where
  r x y := ∃ l : List (Prim q A), (y : A) = (l.map fun ζ => ζ.1).prod * x
  iseqv := by
    refine ⟨fun x => ⟨[], by simp⟩, ?_, ?_⟩
    · rintro x y ⟨l, hl⟩
      refine ⟨(List.replicate (q - 1) l).flatten, ?_⟩
      have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
      simp only [List.map_flatten, List.map_replicate, List.prod_flatten, List.prod_replicate, hl, ← mul_assoc,
        ← pow_succ]
      rw [Nat.sub_add_cancel hq, list_pow, one_mul]
    · rintro x y z ⟨l, hl⟩ ⟨m, hm⟩
      exact ⟨m ++ l, by simp [hm, hl, mul_assoc]⟩

theorem exists_chi [NeZero q] (τ' : Prim q A → M)
    (hl : ∀ l : List (Prim q A), (l.map fun ζ => ζ.1).prod = 1 → (l.map τ').sum = 0) :
    ∃ χ : Aˣ → M, ∀ (ζ : Prim q A) (v w : Aˣ), (w : A) = ζ.1 * v → χ w = χ v + τ' ζ := by
  classical
  let S := rel q A
  let r : Aˣ → Aˣ := fun x => Quotient.out (s := S) (Quotient.mk S x)
  have hr : ∀ x, S.r (r x) x := fun x => Quotient.exact (s := S) (Quotient.out_eq (s := S) (Quotient.mk S x))
  let L : Aˣ → List (Prim q A) := fun x => Classical.choose (hr x)
  have hL : ∀ x : Aˣ, (x : A) = ((L x).map fun ζ => ζ.1).prod * (r x : A) := fun x => Classical.choose_spec (hr x)
  refine ⟨fun x => ((L x).map τ').sum, ?_⟩
  intro ζ v w h
  have hvw : S.r v w := ⟨[ζ], by simp [h]⟩
  have hrr : r w = r v := by
    show Quotient.out (s := S) (Quotient.mk S w) = Quotient.out (s := S) (Quotient.mk S v)
    rw [Quotient.sound (s := S) (S.iseqv.symm hvw)]
  have key : ((L w).map fun ζ => ζ.1).prod = ((ζ :: L v).map fun ζ => ζ.1).prod := by
    have e1 := hL w
    rw [h, hL v, hrr, ← mul_assoc] at e1
    simp only [List.map_cons, List.prod_cons]
    exact ((Units.isUnit (r v)).mul_left_inj).1 e1.symm
  show ((L w).map τ').sum = ((L v).map τ').sum + τ' ζ
  rw [sum_eq_of_prod_eq τ' hl _ _ key]
  simp [add_comm]

noncomputable section Cons
variable (q : ℕ) (T : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (τ : twF q 1 ⟶ T)

abbrev R := ULift.{1} (ZMod q)

abbrev Mo (A : CommRingCat.{0}) := (T.obj A) × ((A : Type)ˣ →₀ R q)

def Idx (A : CommRingCat.{0}) := {p : Prim q A × (A : Type)ˣ × (A : Type)ˣ // ((p.2.2 : (A : Type))) = p.1.1 * p.2.1}

def relv (A : CommRingCat.{0}) (p : Idx q A) : Mo q T A :=
  (-(τ.app A).hom (twGenR A p.1.1), Finsupp.single p.1.2.2 1 - Finsupp.single p.1.2.1 1)

def N (A : CommRingCat.{0}) : Submodule (R q) (Mo q T A) := Submodule.span (R q) (Set.range (relv q T τ A))

def Gm {A B : CommRingCat.{0}} (f : A ⟶ B) : Mo q T A →ₗ[R q] Mo q T B :=
  (T.map f).hom.prodMap (Finsupp.lmapDomain (R q) (R q) (Units.map f.hom.toMonoidHom))

theorem tau_nat {A B : CommRingCat.{0}} (f : A ⟶ B) (ζ : Prim q A) :
    (τ.app B).hom (twGenR B (Prim.map f.hom ζ)) = (T.map f).hom ((τ.app A).hom (twGenR A ζ)) := by
  rw [← twGenR_nat]
  exact congrArg (fun g => ModuleCat.Hom.hom g (twGenR A ζ)) (τ.naturality f)

theorem N_le {A B : CommRingCat.{0}} (f : A ⟶ B) : N q T τ A ≤ (N q T τ B).comap (Gm q T f) := by
  rw [N, Submodule.span_le]
  rintro _ ⟨p, rfl⟩
  apply Submodule.subset_span
  refine ⟨⟨(Prim.map f.hom p.1.1, Units.map f.hom.toMonoidHom p.1.2.1, Units.map f.hom.toMonoidHom p.1.2.2), ?_⟩, ?_⟩
  · simp [Units.coe_map, p.2, Prim.map]
  · simp [relv, Gm, tau_nat, Finsupp.mapDomain_sub, Finsupp.mapDomain_single]

def Gf : CommRingCat.{0} ⥤ ModuleCat.{1} (R q) where
  obj A := ModuleCat.of (R q) (Mo q T A ⧸ N q T τ A)
  map f := ModuleCat.ofHom ((N q T τ _).mapQ (N q T τ _) (Gm q T f) (N_le q T τ f))
  map_id A := by
    ext x <;> simp [Gm]
  map_comp f g := by
    ext x <;> (simp [Gm]; try rfl)

def iota : T ⟶ Gf q T τ where
  app A := ModuleCat.ofHom ((N q T τ A).mkQ ∘ₗ LinearMap.inl (R q) _ _)
  naturality A B f := by
    ext x
    change (Submodule.Quotient.mk ((T.map f).hom x, (0 : (B : Type)ˣ →₀ R q)) : Mo q T B ⧸ N q T τ B) =
      Submodule.Quotient.mk (Gm q T f (x, 0))
    simp [Gm]

def sec (A : CommRingCat.{0}) (v : (A : Type)ˣ) : (Gf q T τ).obj A :=
  Submodule.Quotient.mk (p := N q T τ A) ((0 : T.obj A), Finsupp.single v 1)

theorem sec_nat (A B : CommRingCat.{0}) (f : A ⟶ B) (v : (A : Type)ˣ) :
    ((Gf q T τ).map f).hom (sec q T τ A v) = sec q T τ B (Units.map f.hom.toMonoidHom v) := by
  show (Submodule.Quotient.mk (Gm q T f (0, Finsupp.single v 1)) : Mo q T B ⧸ N q T τ B) =
    Submodule.Quotient.mk (0, Finsupp.single _ 1)
  simp [Gm, Finsupp.mapDomain_single]

theorem sec_rel (A : CommRingCat.{0}) (ζ : Prim q A) (v w : (A : Type)ˣ) (h : (w : (A : Type)) = ζ.1 * v) :
    sec q T τ A w = sec q T τ A v + ((iota q T τ).app A).hom ((τ.app A).hom (twGenR A ζ)) := by
  have hm : relv q T τ A ⟨(ζ, v, w), h⟩ ∈ N q T τ A := Submodule.subset_span ⟨_, rfl⟩
  have key : (Submodule.Quotient.mk (0, Finsupp.single w 1) : Mo q T A ⧸ N q T τ A) =
      Submodule.Quotient.mk (0, Finsupp.single v 1) + Submodule.Quotient.mk ((τ.app A).hom (twGenR A ζ), 0) := by
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    convert hm using 1
    ext <;> simp [relv]
  exact key

theorem iota_inj [NeZero q]
    (hl : ∀ (A : CommRingCat.{0}) (l : List (Prim q A)), (l.map fun ζ => ζ.1).prod = 1 →
      (l.map fun ζ => (τ.app A).hom (twGenR A ζ)).sum = 0) (A : CommRingCat.{0}) :
    Function.Injective ((iota q T τ).app A).hom := by
  obtain ⟨χ, hχ⟩ := exists_chi (M := T.obj A) (fun ζ => (τ.app A).hom (twGenR A ζ)) (hl A)
  let φ : Mo q T A →ₗ[R q] T.obj A :=
    LinearMap.fst _ _ _ + (Finsupp.linearCombination (R q) χ) ∘ₗ LinearMap.snd _ _ _
  have hN : N q T τ A ≤ LinearMap.ker φ := by
    rw [N, Submodule.span_le]
    rintro _ ⟨⟨⟨ζ, v, w⟩, h⟩, rfl⟩
    simp [φ, relv, hχ ζ v w h]
  intro a b hab
  have hab' : (Submodule.Quotient.mk (a, 0) : Mo q T A ⧸ N q T τ A) = Submodule.Quotient.mk (b, 0) := hab
  rw [Submodule.Quotient.eq] at hab'
  have := hN hab'
  simpa [φ, sub_eq_zero] using this

end Cons

theorem main : MuTwistQuotientEmbedsInUnitTorsorPresheaf := by
  intro q _ T τ hl
  exact ⟨Gf q T τ, iota q T τ, iota_inj q T τ hl, sec q T τ, sec_nat q T τ, sec_rel q T τ⟩
end LateralTheory.EtaleFoundations.KTP

namespace LateralTheory.EtaleFoundations
theorem mu_twist_quotient_embeds_in_unit_torsor_presheaf : MuTwistQuotientEmbedsInUnitTorsorPresheaf := KTP.main
end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section
namespace LateralTheory.EtaleFoundations.stairPf
variable {R : Type} [CommRing R] {C J T : Cx R}

theorem tens_zero' {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module (ULift.{1} R) M]
    [Module (ULift.{1} R) N] (hN : ∀ m : N, m = 0) (x : M ⊗[ULift.{1} R] N) : x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul m n => rw [hN n, TensorProduct.tmul_zero]
  | add a b ha hb => rw [ha, hb, add_zero]

theorem res_apply {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens C J U w) (p : Ix w) :
    (Tens.res g w x) p = TensorProduct.map ((C.X p.1.1).obj.map g.op).hom ((J.X p.1.2).obj.map g.op).hom (x p) := by
  unfold Tens.res; rw [DirectSum.lmap_apply]

theorem nat_tens {V U : Scheme.{0}} (g : V ⟶ U) (s s' t : ℤ) (v : Sec (C.X s) U ⊗[ULift.{1} R] Sec (J.X t) U) :
    TensorProduct.map ((C.d s s').hom.app (op V)).hom LinearMap.id
        (TensorProduct.map ((C.X s).obj.map g.op).hom ((J.X t).obj.map g.op).hom v) =
      TensorProduct.map ((C.X s').obj.map g.op).hom ((J.X t).obj.map g.op).hom
        (TensorProduct.map ((C.d s s').hom.app (op U)).hom LinearMap.id v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    congr 1; exact map_res (C.d s s') g a
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem lift_Dm' (τ : Pair C J T) (U : Scheme.{0}) (w w' : ℤ) (hw : w + 1 = w') (x : Tens C J U w) :
    τ.lift U w' (Dm U w w' hw x) = Sec.map (T.d w w') (τ.lift U w x) := by
  subst hw; exact lift_Dm τ U w x

theorem lof_shift (U : Scheme.{0}) (n s s' t : ℤ) (hs : s + 1 = s') (h1 : (s + 1) + t = n) (h2 : s' + t = n)
    (y : Sec (C.X s) U ⊗[ULift.{1} R] Sec (J.X t) U) :
    DirectSum.lof (ULift.{1} R) (Ix n) (Cmp C J U n) ⟨(s + 1, t), h1⟩
        (TensorProduct.map ((C.d s (s + 1)).hom.app (op U)).hom LinearMap.id y) =
      DirectSum.lof (ULift.{1} R) (Ix n) (Cmp C J U n) ⟨(s', t), h2⟩
        (TensorProduct.map ((C.d s s').hom.app (op U)).hom LinearMap.id y) := by
  subst hs; rfl

theorem lof_ne (U : Scheme.{0}) (n : ℤ) (i j : Ix n) (h : i.1.2 ≠ j.1.2) (v : Cmp C J U n i) :
    (DirectSum.lof (ULift.{1} R) (Ix n) (Cmp C J U n) i v) j = 0 := by
  classical
  rw [DirectSum.lof_eq_of]
  exact DirectSum.of_eq_of_ne _ _ _ (fun e => h (by rw [e]))

theorem lof_same (U : Scheme.{0}) (n : ℤ) (i : Ix n) (v : Cmp C J U n i) :
    (DirectSum.lof (ULift.{1} R) (Ix n) (Cmp C J U n) i v) i = v := by
  classical
  rw [DirectSum.lof_eq_of]
  exact DirectSum.of_eq_same _ _

theorem smap_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := map_add _ _ _
theorem smap_sub {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x - y) = Sec.map φ x - Sec.map φ y := map_sub _ _ _
theorem smap_zero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 := map_zero _
theorem sres_sub {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x - y) = Sec.res g x - Sec.res g y := map_sub _ _ _
theorem sres_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _

def Step : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (τ : Pair C J T), τ.IsTensor → LateralTheory.EtaleFoundations.acyc.ColExact C J →
    ∀ (n t0 : ℤ) (V : Scheme.{0}) (x : Tens C J V n), (∀ p : Ix n, p.1.2 < t0 → x p = 0) →
      Sec.map (T.d n (n + 1)) (τ.lift V n x) = 0 →
      Loc V fun W h => ∃ (x' : Tens C J W n) (Y : Tens C J W (n - 1)),
        (∀ p : Ix n, p.1.2 < t0 + 1 → x' p = 0) ∧ Tens.res h n x = x' + Dm W (n - 1) n (by ring) Y

theorem main (hS : Step) (τ : Pair C J T) (a : ℤ) [C.IsStrictlyGE a] (hτ : τ.IsTensor)
    (hc : LateralTheory.EtaleFoundations.acyc.ColExact C J) (n : ℤ) :
    ∀ k : ℕ, ∀ (V : Scheme.{0}) (x : Tens C J V n), (∀ p : Ix n, p.1.2 < n - a + 1 - k → x p = 0) →
      Sec.map (T.d n (n + 1)) (τ.lift V n x) = 0 →
      Loc V fun W h => ∃ y : Sec (T.X (n - 1)) W, Sec.map (T.d (n - 1) n) y = Sec.res h (τ.lift V n x) := by
  intro k
  induction k with
  | zero =>
    intro V x hx _
    obtain rfl : x = 0 := DFinsupp.ext fun p => by
      by_cases hp : p.1.2 < n - a + 1 - ((0 : ℕ) : ℤ)
      · exact hx p hp
      · exact tens_zero (fun m => sec_zero a (by have := p.2; push_cast at hp; omega) m) (x p)
    exact loc_all fun W h => ⟨0, by rw [smap_zero, map_zero, sres_zero]⟩
  | succ k ih =>
    intro V x hx hd
    refine loc_bind (hS R τ hτ hc n (n - a + 1 - ((k + 1 : ℕ) : ℤ)) V x hx hd) fun W h hW => ?_
    obtain ⟨x', Y, hv, he⟩ := hW
    have hl : τ.lift W n x' = Sec.res h (τ.lift V n x) - Sec.map (T.d (n - 1) n) (τ.lift W (n - 1) Y) := by
      rw [← lift_res, he, map_add (f := _), lift_Dm']; abel
    have hd' : Sec.map (T.d n (n + 1)) (τ.lift W n x') = 0 := by
      rw [hl, smap_sub, map_res, hd, sres_zero, map_dd, sub_zero]
    refine loc_mono (ih W x' (fun p hp => hv p (by push_cast at hp ⊢; omega)) hd') fun W' h' hy => ?_
    obtain ⟨y, hy⟩ := hy
    refine ⟨y + Sec.res h' (τ.lift W (n - 1) Y), ?_⟩
    rw [smap_add, map_res, hy, hl, sres_sub, res_comp]; abel

end LateralTheory.EtaleFoundations.stairPf

open LateralTheory.EtaleFoundations.acyc LateralTheory.EtaleFoundations.stairPf in
theorem LateralTheory.EtaleFoundations.acyc.stair_of (hS : Step) : LateralTheory.EtaleFoundations.acyc.stair := by
  intro R _ C J T a b _ _ τ hτ hc U n z hz
  refine loc_bind (hτ.1 U n z) fun V g hV => ?_
  obtain ⟨x, hx⟩ := hV
  have key := main hS τ a hτ hc n ((n - a + 1 - b).toNat) V x
    (fun p hp => tens_zero' (fun m => sec_zero (C := J) b
      (by have := Int.self_le_toNat (n - a + 1 - b); have := p.2; omega) m) (x p))
    (by rw [hx, map_res, hz, sres_zero])
  exact loc_mono key fun W h hy => by
    obtain ⟨y, hy⟩ := hy
    exact ⟨y, by rw [hy, hx, res_comp]⟩
end
end
