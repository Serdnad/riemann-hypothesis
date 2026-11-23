module

public import Development.EtaleCohomology.CohomologicalPurity.InrFold
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def Vec (N k : ℕ) (U : Scheme.{0}) : Type :=
  {v : Fin N → Γ(U, ⊤) // ∀ p : U, ∃ i : Fin N, k ≤ i.val ∧ p ∈ U.basicOpen (v i)}

instance (N k : ℕ) (U : Scheme.{0}) : SmallCategory (Vec N k U) where
  Hom v w := {u : (Γ(U, ⊤))ˣ // ∀ i, v.1 i = (u : Γ(U, ⊤)) * w.1 i}
  id v := ⟨1, by simp⟩
  comp f g := ⟨g.1 * f.1, fun i => by rw [f.2 i, g.2 i, Units.val_mul]; ring⟩
  id_comp f := Subtype.ext (mul_one _)
  comp_id f := Subtype.ext (one_mul _)
  assoc f g h := Subtype.ext (mul_assoc _ _ _).symm

def Vec.map (N k : ℕ) {V U : Scheme.{0}} (f : V ⟶ U) : Vec N k U ⥤ Vec N k V where
  obj v := ⟨fun i => f.appTop.hom (v.1 i), fun p => by
    obtain ⟨i, hi, hp⟩ := v.2 (f p)
    exact ⟨i, hi, by rw [← Scheme.preimage_basicOpen_top]; exact hp⟩⟩
  map {v w} u := ⟨Units.map (f.appTop.hom : Γ(U, ⊤) →* Γ(V, ⊤)) u.1, fun i => by
    change f.appTop.hom (v.1 i) = f.appTop.hom _ * f.appTop.hom _
    rw [u.2 i, map_mul]⟩
  map_id v := Subtype.ext (map_one (Units.map (f.appTop.hom : Γ(U, ⊤) →* Γ(V, ⊤))))
  map_comp p q := Subtype.ext (map_mul (Units.map (f.appTop.hom : Γ(U, ⊤) →* Γ(V, ⊤))) _ _)

def vecCat (N k : ℕ) : Scheme.{0}ᵒᵖ ⥤ Cat.{0,0} where
  obj U := Cat.of (Vec N k U.unop)
  map f := (Vec.map N k f.unop).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

def nerveMap {C D : Scheme.{0}ᵒᵖ ⥤ Cat.{0,0}} (α : C ⟶ D) :
    ((C ⋙ nerveFunctor).flip : Spc) ⟶ ((D ⋙ nerveFunctor).flip : Spc) :=
  (flipFunctor _ _ _).map (Functor.whiskerRight α nerveFunctor)

def Pj (N k : ℕ) : Spc := (vecCat N k ⋙ nerveFunctor).flip

def Vec.incl (N : ℕ) (U : Scheme.{0}) : Vec N 1 U ⥤ Vec N 0 U where
  obj v := ⟨v.1, fun p => (v.2 p).imp fun _ h => ⟨Nat.zero_le _, h.2⟩⟩
  map u := u

def Vec.tail (d : ℕ) (U : Scheme.{0}) : Vec (d + 1) 1 U ⥤ Vec d 0 U where
  obj v := ⟨fun i => v.1 i.succ, fun p => by
    obtain ⟨i, hi, hp⟩ := v.2 p
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 (show i ≠ 0 by rintro rfl; simp at hi)
    exact ⟨j, Nat.zero_le _, hp⟩⟩
  map u := ⟨u.1, fun i => u.2 i.succ⟩

def Vec.line (N k : ℕ) (U : Scheme.{0}) : Vec N k U ⥤ SingleObj (GL (Fin 1) Γ(U, ⊤)) where
  obj _ := SingleObj.star _
  map u := Matrix.GeneralLinearGroup.scalar (Fin 1) u.1
  map_id _ := map_one (Matrix.GeneralLinearGroup.scalar (Fin 1))
  map_comp _ _ := map_mul (Matrix.GeneralLinearGroup.scalar (Fin 1)) _ _

def Pj.incl (N : ℕ) : Pj N 1 ⟶ Pj N 0 :=
  nerveMap { app := fun U => (Vec.incl N U.unop).toCatHom, naturality := fun _ _ _ => rfl }

def Pj.tail (d : ℕ) : Pj (d + 1) 1 ⟶ Pj d 0 :=
  nerveMap { app := fun U => (Vec.tail d U.unop).toCatHom, naturality := fun _ _ _ => rfl }

def Pj.line (N k : ℕ) : Pj N k ⟶ ofCat (glCat 1) :=
  nerveMap (D := Scheme.Γ ⋙ glCat 1)
    { app := fun U => (Vec.line N k U.unop).toCatHom
      naturality := fun A B f => by
        apply Cat.Hom.ext
        refine CategoryTheory.Functor.hext (fun _ => rfl) (fun v w p => heq_of_eq ?_)
        change Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.map (f.unop.appTop.hom : _ →* _) p.1) =
          Matrix.GeneralLinearGroup.map f.unop.appTop.hom (Matrix.GeneralLinearGroup.scalar (Fin 1) p.1)
        ext i j
        obtain rfl : i = j := Subsingleton.elim _ _
        simp }

theorem Pj.incl_line (N : ℕ) : Pj.incl N ≫ Pj.line N 0 = Pj.line N 1 := rfl
theorem Pj.tail_line (d : ℕ) : Pj.tail d ≫ Pj.line d 0 = Pj.line (d + 1) 1 := rfl

def Pj.pt {N k : ℕ} {X : Scheme.{0}} (v : Vec N k X) : sch.obj X ⟶ Pj N k where
  app n :=
    { app := fun U => TypeCat.ofHom fun (f : U.unop ⟶ X) =>
        (Functor.const (Fin (n.unop.len + 1))).obj ((Vec.map N k f).obj v)
      naturality := fun U U' g => by
        ext f
        refine CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq ?_)
        exact ((Vec.map N k g.unop).map_id ((Vec.map N k f).obj v)).symm }
  naturality n m f := rfl

def vec1 {d : ℕ} {A : Type} [CommRing A] (x : Fin d → A) : Vec (d + 1) 0 (Spec (CommRingCat.of A)) :=
  ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Fin.cons 1 x : Fin (d + 1) → A) i), fun p =>
    ⟨0, le_rfl, by simp⟩⟩

abbrev PR (N k : ℕ) (R : Type) [CommRing R] : Spc := Pj N k ⨯ sp R

def hyp (q N k : ℕ) (R : Type) [CommRing R] : Ht q (PR N k R) 2 1 := c1 q (prod.fst ≫ Pj.line N k)

def poly (q N k : ℕ) (R : Type) [CommRing R] (m : ℕ) (n i : ℤ)
    (a : ∀ j : Fin m, Ht q (sp R) (n - 2 * (j : ℕ)) (i - (j : ℕ))) : Ht q (PR N k R) n i :=
  ∑ j : Fin m, ((cup q (pull _ prod.snd _ _ (a j)) (cpow q (hyp q N k R) j)).cast (by ring) (by ring) : Ht q _ n i)

def pr (d : ℕ) (R : Type) [CommRing R] : Arrow Spc :=
  Arrow.mk (prod.map (Pj.incl (d + 1)) (𝟙 _) : PR (d + 1) 1 R ⟶ PR (d + 1) 0 R)

def prMap (d : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) : pr d B ⟶ pr d A :=
  Arrow.homMk (prod.map (𝟙 _) (spMap φ)) (prod.map (𝟙 _) (spMap φ)) (by simp [pr])

def chart {d : ℕ} {A : Type} [CommRing A] (x : Fin d → A) : sp A ⟶ PR (d + 1) 0 A := prod.lift (Pj.pt (vec1 x)) (𝟙 _)

def IsTau (q d : ℕ) (R : Type) [CommRing R] (τ : Hs q (pr d R) (2 * d) d) : Prop :=
  ∃ a, Hs.fgt q (pr d R) _ _ τ = cpow q (hyp q (d + 1) 0 R) d + poly q (d + 1) 0 R d (2 * d) d a

end LateralTheory.CohomologicalPurity.Thom
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem indNbhd_of_nbhd {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (h : Nbhd φ I) :
    IndNbhd φ I :=
  ⟨Discrete PUnit, inferInstance, inferInstance, (Functor.const _).obj (CommRingCat.of B),
    (Functor.const _).map (CommRingCat.ofHom φ), 𝟙 _, ⟨isColimitConstCocone (Discrete PUnit) (CommRingCat.of B)⟩,
    fun _ => ⟨h, Category.comp_id _⟩⟩

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

def Hyp : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ DivisorNaturality ∧ DivisorRingCompatibility ∧ A9 ∧ A11 ∧ B1 ∧ C4 ∧ D1 ∧ E1

def Gysin (d : ℕ) : Prop :=
  ∃ (gys : ∀ (q : ℕ) (P : SP d) (n i : ℤ), Ht q (sch.obj P.Z) n i →+ Ht q (sch.obj P.X) (n + 2 * d) (i + d))
    (rs : ∀ (q : ℕ) (P : SP d) (n i : ℤ), Ht q (sch.obj P.U) (n + 2 * d - 1) (i + d) →+ Ht q (sch.obj P.Z) n i),
  ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) →
  (∀ n i : ℤ, Function.Exact (pull _ (sch.map P.U.ι) (tw q (i + d)) (n + 2 * d - 1)) (rs q P n i) ∧
    Function.Exact (rs q P n i) (gys q P n i) ∧
    Function.Exact (gys q P n i) (pull _ (sch.map P.U.ι) (tw q (i + d)) (n + 2 * d))) ∧
  (∀ (P' : SP d) (φ : P'.Hom P) (n i : ℤ),
    (∀ a, pull _ (sch.map φ.f) _ _ (gys q P n i a) = gys q P' n i (pull _ (sch.map φ.g) _ _ a)) ∧
    ∀ u, pull _ (sch.map φ.g) _ _ (rs q P n i u) = rs q P' n i (pull _ (sch.map (φ.f.resLE P.U P'.U φ.le)) _ _ u)) ∧
  (∀ (n m i j : ℤ) (a : Ht q (sch.obj P.X) n i) (b : Ht q (sch.obj P.Z) m j),
    gys q P (n + m) (i + j) (cup q (pull _ (sch.map P.ι) _ _ a) b) = (cup q a (gys q P m j b)).cast (by ring) (by ring)) ∧
  ∀ r : ℕ, r ∣ q → ∀ n i : ℤ, (∀ a, gys r P n i (red q r _ _ _ a) = red q r _ _ _ (gys q P n i a)) ∧
    ∀ u, rs r P n i (red q r _ _ _ u) = red q r _ _ _ (rs q P n i u)

def Goal : Prop := Hyp → (∀ d, Gysin d) ∧ E6

def LeafAW : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧
  ∀ (E : Spc) (n m : ℤ) (α : Cocycle ((chains _).obj E) (res _ (tw q i)) n) (β : Cocycle ((chains _).obj E) (res _ (tw q j)) m),
    ∃ γ : Cocycle ((chains _).obj E) (res _ (tw q (i + j))) (n + m), (twPair q i j).IsAW rfl α.1 β.1 γ.1 ∧
      cup q (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

def LeafBd : Prop := ∃ δ, IsBd δ

def LeafExc : Prop := A1 → ∀ (q : ℕ) {X' X Z : Scheme.{0}} (f : X' ⟶ X) [Etale f] (ι' : Z ⟶ X') (ι : Z ⟶ X)
  [IsClosedImmersion ι], IsPullback ι' (𝟙 Z) f ι → ∀ (U' : X'.Opens) (U : X.Opens), (U : Set X) = (Set.range ι)ᶜ →
  ∀ h : U' = f ⁻¹ᵁ U, Exc q (opnMap f U' U h.le)

def LeafHens : Prop := Nonempty Hens

def LeafIndExc : Prop := A1 → A4 → B1 → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A), I.FG →
  IndNbhd φ I → IsUnit (q : A) → ∀ h, Exc q (opnMap (Spec.map (CommRingCat.ofHom φ)) (off B (I.map φ)) (off A I) h)

def LeafThom : Prop := Hyp → ∀ d, ∃ th, IsThom d th

def LeafChart : Prop := ∀ (d : ℕ) (P : SP d) (x : P.X) (W : P.X.Opens), x ∈ W →
  ∃ V : P.X.affineOpens, x ∈ V.1 ∧ V.1 ≤ W ∧ (P.ι.ker.ideal V).FG ∧ Chart d Γ(P.X, V.1) (P.ι.ker.ideal V)

def LeafCl : Prop := Hyp → ∀ d, ∃ c, IsCl d c

def LeafTube : Prop := Hyp → ∀ d, ∃ T : ∀ P : SP d, Tube P, ∀ (P' P : SP d) (φ : P'.Hom P),
  ∃ (T' : Tube P') (a : T'.E ⟶ (T P').E) (b : T'.E ⟶ (T P).E), a ≫ (T P').π = T'.π ∧ b ≫ (T P).π = T'.π ≫ sch.map φ.f

def LeafGysin : Prop := Hyp → ∀ d, Gysin d

def LeafSemi : Prop := A9 → (∀ d, Gysin d) → E6

end LateralTheory.CohomologicalPurity
end
end
