module

public import Development.EtaleCohomology.EtaleSheaves.Bundle059
public import Development.EtaleCohomology.EtaleSheaves.Bundle003
public import Development.EtaleCohomology.EtaleSheaves.Bundle058
public import Development.EtaleCohomology.EtaleSheaves.Bundle060
import Development.EtaleCohomology.EtaleSheaves.Bundle008
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.EtaleCohomology.EtaleSheaves.Bundle047
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.SecondDegreeKilling
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

abbrev prS {Y B W S : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (s : S ⟶ B) :
    pullback (pullback.snd p s ≫ s) ι ⟶ pullback p s := pullback.fst _ _

abbrev tY {Y B S : Scheme.{0}} (p : Y ⟶ B) (U : B.Etale) (t : S ⟶ U.left) : pullback p (t ≫ U.hom) ⟶ YU p U :=
  pullback.map p (t ≫ U.hom) p U.hom (𝟙 Y) t (𝟙 B) (by simp) (by simp)

abbrev tW {Y B W S : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (t : S ⟶ U.left) :
    pullback (pullback.snd p (t ≫ U.hom) ≫ (t ≫ U.hom)) ι ⟶ pullback (pullback.snd p U.hom ≫ U.hom) ι :=
  pullback.map _ _ _ _ (tY p U t) (𝟙 W) (𝟙 B) (by simp only [tY, pullback.lift_snd_assoc, Category.assoc]; erw [Category.comp_id]) (by simp)

abbrev rT (q : ℕ) (i : ℤ) {Y B W S : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (t : S ⟶ U.left) (m : ℤ) :=
  rpl q i (prU p ι U) (prS p ι (t ≫ U.hom)) (tW p ι U t) (tY p U t) (pullback.lift_fst _ _ _).symm m

def LeafKillPt : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (m : ℤ) (z : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m),
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ U.left), SH A → rT q i p ι U t m z = 0) →
  Cov U (fun _ a => rY q i p ι a m z = 0)

def LeafPtW : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y ⟶ B), IsProper p → ∀ (A : Type) [CommRing A] (s : Sp A ⟶ B), SH A → ¬ (Set.range s ⊆ V) →
  ∀ m, Subsingleton (Hrel (ZMod q) (sch.map (prS p ι s)) (tw q i) m)

def LeafPtV : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y Y' : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y ⟶ B) (g : Y' ⟶ Y), IsProper p → IsProper (g ≫ p) → ∀ (U : B.Etale) (A : Type) [CommRing A]
  (t : Sp A ⟶ U.left), SH A → Set.range ⇑(t ≫ U.hom) ⊆ (V : Set B) → ∀ (m : ℤ), pl q i (fibMap g p (t ≫ U.hom)) m = 0 →
  ∀ y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m, rT q i (g ≫ p) ι U t m (gY q i p g ι U m y) = 0

theorem LeafKill2_of (hPt : LeafKillPt) (hW : LeafPtW) (hV : LeafPtV) : LeafKill2 := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 toK ι _ V hVW p g1 g2 hp hp1 hp2 hS U y
  refine hPt hH q k hq i toK ι (g1 ≫ p) hp1 U 2 _ ?_
  intro A _ t hA
  by_cases hc : Set.range ⇑(t ≫ U.hom) ⊆ (V : Set B)
  · exact hV hH q k hq i toK ι V hVW p g1 hp hp1 U A t hA hc 2 (hS A (t ≫ U.hom) hA hc).2.1 y
  · have := hW hH q k hq i toK ι V hVW (g1 ≫ p) hp1 A (t ≫ U.hom) hA hc 2
    exact Subsingleton.elim _ _

end LateralTheory.E.SecondDegreeKilling
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafShIsoPf
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves

theorem Cov.bind {B : Scheme.{0}} {U : B.Etale} {P Q : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : Cov U P)
    (hPQ : ∀ U' (a : U' ⟶ U), P U' a → Cov U' (fun U'' b => Q U'' (b ≫ a))) : Cov U Q := by
  obtain ⟨S, hS, hP⟩ := h
  let R : Sieve U :=
    { arrows := fun Z c => ∀ (W : B.Etale) (d : W ⟶ Z), Q W (d ≫ c)
      downward_closed := fun {Z Z'} c hc e W d => by simpa [Category.assoc] using hc W (d ≫ e) }
  refine ⟨R, (EtTop B).transitive hS R ?_, fun U' a ha => by simpa using ha U' (𝟙 _)⟩
  intro Y f hf
  obtain ⟨S', hS', hQ⟩ := hPQ Y f (hP Y f hf)
  refine (EtTop B).superset_covering ?_ hS'
  intro Z c hc W d
  simpa [Category.assoc] using hQ W (d ≫ c) (S'.downward_closed hc d)

abbrev H0 (B : Scheme.{0}) (q : ℕ) := DerivedCategory.homologyFunctor (SShv B q) 0

def EtaleDerivedDegreeZeroHomologyLocallyLifts : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (M : DerivedCategory (SShv B q)) (U : B.Etale)
  (t : (H0 B q).obj ((OU B q).obj U) ⟶ (H0 B q).obj M),
  Cov U (fun U' a => ∃ x : (OU B q).obj U' ⟶ M, (H0 B q).map ((OU B q).map a) ≫ t = (H0 B q).map x)

def EtaleDerivedDegreeZeroHomologyKernelLocallyVanishes : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (M : DerivedCategory (SShv B q)) (U : B.Etale)
  (x : (OU B q).obj U ⟶ M), (H0 B q).map x = 0 → Cov U (fun U' a => (OU B q).map a ≫ x = 0)

def LeafSheafIso : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (F G : SShv B q) (g : F ⟶ G),
  (∀ (U : B.Etale) (t : (H0 B q).obj ((OU B q).obj U) ⟶ F), t ≫ g = 0 →
    Cov U (fun U' a => (H0 B q).map ((OU B q).map a) ≫ t = 0)) →
  (∀ (U : B.Etale) (s : (H0 B q).obj ((OU B q).obj U) ⟶ G),
    Cov U (fun U' a => ∃ t : (H0 B q).obj ((OU B q).obj U') ⟶ F, (H0 B q).map ((OU B q).map a) ≫ s = t ≫ g)) →
  IsIso g

theorem LeafShIso_of (hL : EtaleDerivedDegreeZeroHomologyLocallyLifts) (hK : EtaleDerivedDegreeZeroHomologyKernelLocallyVanishes) (hS : LeafSheafIso) : LeafShIso := by
  intro B q L K ℓ m hinj hsurj
  set f := (shiftFunctor (DerivedCategory (SShv B q)) m).map ℓ with hf
  have key : IsIso ((H0 B q).map f) := by
    apply hS
    · intro U t ht
      refine Cov.bind (hL B q _ U t) ?_
      rintro U' a ⟨x, hx⟩
      have h1 : (H0 B q).map (x ≫ f) = 0 := by
        rw [Functor.map_comp, ← hx, Category.assoc, ht, comp_zero]
      have h2 := hinj U' x 0 ((hK B q _ U' _ h1).mono (fun U'' b hb => by simpa using hb))
      refine h2.mono (fun U'' b hb => ?_)
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, hx, ← Functor.map_comp, hb, comp_zero,
        Functor.map_zero]
    · intro U s
      refine Cov.bind (hL B q _ U s) ?_
      rintro U' a ⟨y, hy⟩
      refine (hsurj U' y).mono (fun U'' b ⟨x, hx⟩ => ⟨(H0 B q).map x, ?_⟩)
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, hy, ← Functor.map_comp, hx, Functor.map_comp]
  have e := ((H0 B q).isoShift m)
  exact (NatIso.isIso_map_iff e ℓ).1 key

end LateralTheory.E.LeafShIsoPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafShMapZeroPf
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

theorem Cov.trans {B : Scheme.{0}} {U : B.Etale} {P Q : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : Cov U P)
    (hPQ : ∀ U' a, P U' a → Cov U' (fun U'' b => Q U'' (b ≫ a))) : Cov U Q := by
  obtain ⟨S, hS, hP⟩ := h
  let R : ∀ ⦃Y : B.Etale⦄ ⦃f : Y ⟶ U⦄, S f → Sieve Y := fun Y f hf =>
    Classical.choose (hPQ Y f (hP Y f hf))
  refine ⟨Sieve.bind S R, (EtTop B).bind_covering hS
    (fun Y f hf => (Classical.choose_spec (hPQ Y f (hP Y f hf))).1), ?_⟩
  rintro U'' _ ⟨Y, g, f, hf, hg, rfl⟩
  exact (Classical.choose_spec (hPQ Y f (hP Y f hf))).2 U'' g hg

def EtaleLift' : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (K : DerivedCategory (SShv B q)) (U : B.Etale)
  (s : (DerivedCategory.homologyFunctor (SShv B q) 0).obj ((OU B q).obj U) ⟶
    (DerivedCategory.homologyFunctor (SShv B q) 0).obj K),
  Cov U (fun U' a => ∃ x : (OU B q).obj U' ⟶ K,
    (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫ s =
      (DerivedCategory.homologyFunctor (SShv B q) 0).map x)

def LeafGen : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (H H' : SShv B q) (g : H ⟶ H'),
  (∀ (U : B.Etale) (s : (DerivedCategory.homologyFunctor (SShv B q) 0).obj ((OU B q).obj U) ⟶ H),
    Cov U (fun U' a => (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫ s ≫ g = 0)) → g = 0

theorem zero_of (hA : EtaleLift') (hB : LeafGen) (B : Scheme.{0}) (q : ℕ) (K K' : DerivedCategory (SShv B q))
    (f : K ⟶ K')
    (h : ∀ (U : B.Etale) (x : (OU B q).obj U ⟶ K), Cov U (fun U' a => (OU B q).map a ≫ x ≫ f = 0)) :
    (DerivedCategory.homologyFunctor (SShv B q) 0).map f = 0 := by
  apply hB B q _ _ _
  intro U s
  refine Cov.trans (hA B q K U s) ?_
  rintro U' a ⟨x, hx⟩
  refine (h U' x).mono fun U'' b hb => ?_
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, reassoc_of% hx, ← Functor.map_comp,
    ← Functor.map_comp, hb, Functor.map_zero]

theorem LeafShMapZero_of (hA : EtaleLift') (hB : LeafGen) : LeafShMapZero := by
  intro B q K K' f m h
  have h0 := zero_of hA hB B q _ _ ((shiftFunctor _ m).map f) h
  have e := (DerivedCategory.homologyFunctor (SShv B q) (0 : ℤ)).shiftIso_hom_naturality m (0 : ℤ) m (by simp) f
  have h0' : ((DerivedCategory.homologyFunctor (SShv B q) (0 : ℤ)).shift (0 : ℤ)).map
      ((shiftFunctor _ m).map f) = 0 := h0
  change ((DerivedCategory.homologyFunctor (SShv B q) (0 : ℤ)).shift m).map f = 0
  rw [← cancel_epi (((DerivedCategory.homologyFunctor (SShv B q) (0 : ℤ)).shiftIso m (0 : ℤ) m (by simp)).hom.app K),
    comp_zero, ← e, h0', zero_comp]

end LateralTheory.E.LeafShMapZeroPf
end
end

section

open Polynomial IntermediateField.algebraAdjoinAdjoin

namespace LateralTheory.E.CurveUnitsOrderAtInfinity

theorem minpolyCoeff : LateralTheory.E.E4.LeafMinpolyCoeff := by
  intro k L _ _ _ s hs F hF x hx i
  subst hF
  have : UniqueFactorizationMonoid (Algebra.adjoin k {s}) := hs.uniqueFactorizationMonoid_adjoin
  have : IsIntegrallyClosed (Algebra.adjoin k {s}) := inferInstance
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' (IntermediateField.adjoin k {s}) hx, coeff_map]
  exact ((minpoly (Algebra.adjoin k {s}) x).coeff i).2

theorem ordInfHom : LateralTheory.E.E4.LeafOrdInfHom :=
  LateralTheory.E.E4.LeafOrdInfHom_of_local (LateralTheory.E.E4.LeafOrdInfLocal_of' LateralTheory.E.E4.LeafFinInf_of LateralTheory.E.E4.LeafFinVal_of)

theorem LeafUnits_of : LateralTheory.E.E4.LeafUnits :=
  LateralTheory.E.E4.LeafUnits_of (LateralTheory.E.E4.LeafUnitsFG_of_dim LateralTheory.E.E4.LeafNoetherDim_of
    (LateralTheory.E.E4.LeafOrdAtInfinity_of_cut ordInfHom minpolyCoeff))

end LateralTheory.E.CurveUnitsOrderAtInfinity
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTensMonoPf
open LateralTheory.E.LeafTwPairExistsPf LateralTheory.E.LeafPairExtPf2

section
variable {R : Type} [CommRing R]

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (h ≫ g) y = Sec.res h (Sec.res g y) := by
  simp [Sec.res]

theorem loc_trans {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  classical
  obtain ⟨S, hS, hP⟩ := h
  let T : ∀ ⦃V : Scheme.{0}⦄ ⦃f : V ⟶ U⦄, S.arrows f → Sieve V := fun V f hf =>
    Classical.choose (hPQ V f (hP V f hf))
  refine ⟨Sieve.bind S.arrows T, (Scheme.etaleTopology.{0}).bind_covering hS
    (fun V f hf => (Classical.choose_spec (hPQ V f (hP V f hf))).1), ?_⟩
  rintro W _ ⟨V, k, f, hf, hk, rfl⟩
  exact (Classical.choose_spec (hPQ V f (hP V f hf))).2 W k hk

theorem eq_zero_of_loc {F : Shv R} {U : Scheme.{0}} (y : Sec F U) (h : Loc U fun _ g => Sec.res g y = 0) : y = 0 := by
  obtain ⟨S, hS, hP⟩ := h
  let e : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ y)
  have := F.property.hom_ext ⟨S, hS⟩ e 0 (fun I => by
    ext1; apply LinearMap.ext_ring
    have := hP _ I.f I.hf
    simpa [e] using this)
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom this) 1
  simpa [e] using h2

theorem mono_of_loc {F G : Shv R} (f : F ⟶ G)
    (h : ∀ (U : Scheme.{0}) (y : Sec F U), Sec.map f y = 0 → Loc U fun _ g => Sec.res g y = 0) : Mono f := by
  have : Mono ((sheafToPresheaf _ _).map f) := by
    have hm : ∀ U, Mono (((sheafToPresheaf Scheme.etaleTopology (ModuleCat (ULift.{1, 0} R))).map f).app U) := by
      intro U
      rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
      intro y hy
      exact eq_zero_of_loc y (h U.unop y hy)
    exact NatTrans.mono_of_mono_app _
  exact (sheafToPresheaf _ _).mono_of_mono_map this

theorem lift_res {I J K : Cx R} (μ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    μ.lift V w (Tens.res g w x) = Sec.res g (μ.lift U w x) := by
  have : (μ.lift V w).comp (Tens.res g w) = ((K.X w).obj.map g.op).hom.comp (μ.lift U w) := by
    apply DirectSum.linearMap_ext; intro p
    apply TensorProduct.ext'; intro a b
    simp [Pair.lift, Tens.res]
    exact (μ.nat g _ _ _ p.2 a b).symm
  exact LinearMap.congr_fun this x

theorem lift_compat {I J K K' : Cx R} (σ : Pair I J K) (ν : Pair I J K') (ι : K ⟶ K')
    (h : ∀ (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      Sec.map (ι.f w) (σ.mul U s t w hw a b) = ν.mul U s t w hw a b) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    Sec.map (ι.f w) (σ.lift U w x) = ν.lift U w x := by
  have : ((ι.f w).hom.app (op U)).hom.comp (σ.lift U w) = ν.lift U w := by
    apply DirectSum.linearMap_ext; intro p
    apply TensorProduct.ext'; intro a b
    simp [Pair.lift]
    exact h U _ _ _ p.2 a b
  exact LinearMap.congr_fun this x
end

def LeafTw0LocSplit : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (n : ℕ) (a : Fin n → Sec ((sgl (tw q 0)).X 0) U),
  Loc U fun V g => ∃ (e : Sec ((sgl (tw q 0)).X 0) V) (c : Fin n → ULift.{1} (ZMod q)),
    (∀ k, Sec.res g (a k) = c k • e) ∧
    (e = 0 ∨ ∃ r : Sec ((res _ (tw q 0)).X 0) V →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q),
      r (Sec.map ((resAug (tw q 0)).f 0) e) = 1)

def LeafPreTensLocInj : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {T : Cx (ZMod q)} (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T),
  τ.IsTensor → ∀ (U : Scheme.{0}) (w : ℤ) (x : Tens (sgl (tw q 0)) (res _ (tw q i)) U w),
  (pre τ (resAug (tw q 0))).lift U w x = 0 → Loc U fun _ g => Tens.res g w x = 0

theorem LeafTensMono_of (hL : LeafPreTensLocInj) : LateralTheory.E.LeafExtTensPf.LeafTensMono := by
  intro q _ i S T σ τ hσ hτ ι hι n
  apply mono_of_loc
  intro U y hy
  have hc := lift_compat σ (pre τ (resAug (tw q 0))) ι (fun U s t w hw a b => hι U s t w hw a b)
  refine loc_trans (hσ.1 U n y) ?_
  rintro V g ⟨x, hx⟩
  have h0 : (pre τ (resAug (tw q 0))).lift V n x = 0 := by
    rw [← hc, hx, ← res_map, hy]; simp
  obtain ⟨S', hS', hP'⟩ := hL q i τ hτ V n x h0
  exact ⟨S', hS', fun W k hk => by
    show Sec.res (k ≫ g) y = 0
    have hk' : Tens.res k n x = 0 := hP' W k hk
    rw [res_comp, ← hx, ← lift_res, hk', map_zero]⟩

end LateralTheory.E.LeafTensMonoPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial Opposite

namespace LateralTheory.E.LocPf

theorem root_mem_range {A K : Type} [CommRing A] [CommRing K] [IsDomain K] (hA : GlobalTheory.EtC.AIC A) (φ : A →+* K) :
    ∀ (n : ℕ) (p : A[X]), p.natDegree = n → p.Monic → ∀ a : K, p.eval₂ φ a = 0 → ∃ b, φ b = a := by
  intro n
  induction n with
  | zero =>
    intro p hn hp a ha
    rw [eq_one_of_monic_natDegree_zero hp hn, eval₂_one] at ha
    exact absurd ha one_ne_zero
  | succ n ih =>
    intro p hn hp a ha
    have : Nontrivial A := by
      by_contra hnt; rw [not_nontrivial_iff_subsingleton] at hnt
      rw [Subsingleton.elim p 0] at hn; simp at hn
    obtain ⟨b, hb⟩ := hA p hp (by omega)
    have e := (mul_divByMonic_eq_iff_isRoot (p := p) (a := b)).mpr hb
    have hq : (p /ₘ (X - C b)).Monic := Monic.of_mul_monic_left (monic_X_sub_C b) (by rw [e]; exact hp)
    have hdeg : (p /ₘ (X - C b)).natDegree = n := by
      have := (monic_X_sub_C b).natDegree_mul hq
      rw [e, natDegree_X_sub_C] at this; omega
    rw [← e, eval₂_mul, eval₂_sub, eval₂_X, eval₂_C] at ha
    rcases mul_eq_zero.mp ha with h | h
    · exact ⟨b, (sub_eq_zero.mp h).symm⟩
    · exact ih _ hdeg hq a h

theorem aic_of_isLocalization {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (M : Submonoid A)
    [IsLocalization M B] (hA : GlobalTheory.EtC.AIC A) : GlobalTheory.EtC.AIC B := by
  intro p hp hd
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite M (fun i : Fin (p.natDegree + 1) => p.coeff i)
  set t := algebraMap A B b with ht
  have hlift : p.scaleRoots t ∈ lifts (algebraMap A B) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    rcases lt_trichotomy i p.natDegree with h | h | h
    · obtain ⟨c, hc⟩ := hb ⟨i, by omega⟩
      refine ⟨c * (b : A) ^ (p.natDegree - i - 1), ?_⟩
      rw [map_mul, map_pow, hc, Algebra.smul_def, ← ht]
      rw [show t ^ (p.natDegree - i) = t * t ^ (p.natDegree - i - 1) by rw [← pow_succ']; congr 1; omega]
      ring
    · subst h; rw [hp.coeff_natDegree]; exact ⟨1, by simp⟩
    · rw [coeff_eq_zero_of_natDegree_lt h]; exact ⟨0, by simp⟩
  obtain ⟨q, hqm, hqd, hq⟩ := lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff t).mpr hp)
  obtain ⟨c, hc⟩ := hA q hq (by rw [hqd, natDegree_scaleRoots]; exact hd)
  obtain ⟨u, hu⟩ := (IsLocalization.map_units B b).exists_right_inv
  refine ⟨u * algebraMap A B c, ?_⟩
  have h1 : p = (p.scaleRoots t).scaleRoots u := by
    rw [← scaleRoots_mul, ht, hu, scaleRoots_one]
  have h2 : (p.scaleRoots t).eval (algebraMap A B c) = 0 := by
    rw [← hqm, Polynomial.eval_map, eval₂_at_apply, hc, map_zero]
  conv_lhs => rw [h1]
  rw [scaleRoots_eval_mul, h2, mul_zero]

theorem germ_comp (Z : Scheme.{0}) {W U : Z.Opens} (i : W ≤ U) (x : Z) (hx : x ∈ W) :
    (Z.presheaf.germ W x hx).hom.comp (Z.presheaf.map (homOfLE i).op).hom = (Z.presheaf.germ U x (i hx)).hom := by
  ext s; simp

theorem exists_small (Z : Scheme.{0}) (h : ∀ z : Z, ∃ U : Z.Opens, IsAffineOpen U ∧ z ∈ U ∧ GlobalTheory.EtC.AIC Γ(Z, U))
    (U : Z.Opens) (z : Z) (hz : z ∈ U) : ∃ W : Z.Opens, W ≤ U ∧ z ∈ W ∧ GlobalTheory.EtC.AIC Γ(Z, W) := by
  obtain ⟨V, hV, hzV, hA⟩ := h z
  obtain ⟨f, hle, hzf⟩ := hV.exists_basicOpen_le (V := U) ⟨z, hz⟩ hzV
  have := hV.isLocalization_basicOpen f
  exact ⟨Z.basicOpen f, hle, hzf, aic_of_isLocalization (Submonoid.powers f) hA⟩

theorem loc : LateralTheory.E.NormACPf.Loc := by
  intro Z hZ h U hU ⟨z0, hz0⟩ p hp hd
  set η := genericPoint Z
  have hη : ∀ W : Z.Opens, (W : Set Z).Nonempty → η ∈ W := fun W hW =>
    ((genericPoint_spec Z).mem_open_set_iff W.isOpen).mpr (by simpa using hW)
  have hηU : η ∈ U := hη U ⟨z0, hz0⟩
  choose W hWU hzW hWA using fun z : U => exists_small Z h U z.1 z.2
  have hηW : ∀ z : U, η ∈ W z := fun z => hη _ ⟨z.1, hzW z⟩
  let gU := (Z.presheaf.germ U η hηU).hom
  let res := fun z : U => (Z.presheaf.map (homOfLE (hWU z)).op).hom
  have hdom : ∀ z : U, Nontrivial Γ(Z, W z) := fun z => by
    have : Nonempty (W z) := ⟨⟨z.1, hzW z⟩⟩; infer_instance
  let z0' : U := ⟨z0, hz0⟩
  obtain ⟨b0, hb0⟩ := hWA z0' (p.map (res z0')) (hp.map _) (by rw [hp.natDegree_map]; exact hd)
  set a := Z.presheaf.germ (W z0') η (hηW z0') b0 with ha_def
  have hroot : p.eval₂ gU a = 0 := by
    have := congrArg (Z.presheaf.germ (W z0') η (hηW z0')).hom hb0
    rw [Polynomial.eval_map, hom_eval₂, germ_comp, map_zero] at this
    exact this
  have hc : ∀ z : U, ∃ c, Z.presheaf.germ (W z) η (hηW z) c = a := by
    intro z
    refine root_mem_range (hWA z) (Z.presheaf.germ (W z) η (hηW z)).hom _ (p.map (res z)) rfl (hp.map _) a ?_
    rw [eval₂_map, germ_comp]; exact hroot
  choose c hcz using hc
  obtain ⟨s1, hs1, -⟩ := TopCat.Sheaf.existsUnique_gluing' Z.sheaf W U (fun z => homOfLE (hWU z))
    (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hzW _⟩) c (by
      intro i j
      apply germ_injective_of_isIntegral Z (U := W i ⊓ W j) η (show η ∈ W i ⊓ W j from ⟨hηW i, hηW j⟩)
      change (Z.presheaf.germ _ η _) (Z.presheaf.map _ (c i)) = (Z.presheaf.germ _ η _) (Z.presheaf.map _ (c j))
      rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hcz, hcz])
  obtain ⟨s, hs⟩ : ∃ s : Γ(Z, U), ∀ i, Z.presheaf.map (homOfLE (hWU i)).op s = c i := ⟨s1, hs1⟩
  have hsa : gU s = a := by
    have := hs z0'
    rw [← hcz z0', ← this]
    change _ = (Z.presheaf.germ _ η _) (Z.presheaf.map _ s)
    rw [TopCat.Presheaf.germ_res_apply]
  refine ⟨s, germ_injective_of_isIntegral Z η hηU ?_⟩
  change gU (p.eval s) = gU 0
  rw [map_zero, ← eval₂_at_apply, hsa, hroot]

end LateralTheory.E.LocPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTensQIsoPf

def LeafSecInj : Prop := ∀ (R : Type) [CommRing R] (F : Shv R), Injective F → ∀ U : Scheme.{0},
  Module.Injective (ULift.{1} R) (Sec F U)

def LeafZModInjFlat : Prop := ∀ (q : ℕ) [NeZero q] (M : Type 1) [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M],
  Module.Injective (ULift.{1} (ZMod q)) M → Module.Flat (ULift.{1} (ZMod q)) M

def LeafTensQIsoGen : Prop := ∀ (R : Type) [CommRing R] {I I' J S T : Cx R} (f : I ⟶ I'), QuasiIso f →
  I.IsStrictlyGE 0 → I'.IsStrictlyGE 0 → J.IsStrictlyGE 0 →
  (∀ (n : ℤ) (U : Scheme.{0}), Module.Flat (ULift.{1} R) (Sec (J.X n) U)) →
  ∀ (σ : Pair I J S) (τ : Pair I' J T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map (f.f s) a) b) →
  QuasiIso ι

theorem resAug_quasiIso (R : Type) [CommRing R] (F : Shv R) : QuasiIso (resAug F) := by
  unfold resAug; exact @InjectiveResolution.instQuasiIsoIntι' _ _ _ _ _

theorem res_strictlyGE (R : Type) [CommRing R] (F : Shv R) : (res R F).IsStrictlyGE 0 := by
  unfold res; infer_instance

theorem sgl_strictlyGE (R : Type) [CommRing R] (F : Shv R) : (sgl F).IsStrictlyGE 0 := by
  infer_instance

theorem LeafTensQIso_of (hgen : LeafTensQIsoGen) (hinj : LeafSecInj) (hflat : LeafZModInjFlat) :
    LateralTheory.E.LeafExtTensPf.LeafTensQIso := by
  intro q _ i S T σ τ hσ hτ ι hι
  exact hgen (ZMod q) (resAug (tw q 0)) (resAug_quasiIso _ _) (sgl_strictlyGE _ _) (res_strictlyGE _ _)
    (res_strictlyGE _ _) (fun n U => hflat q _ (hinj _ _ (LateralTheory.E.LeafExtTensPf.res_injective _ _ n) U)) σ τ hσ hτ ι hι

end LateralTheory.E.LeafTensQIsoPf
end
end
