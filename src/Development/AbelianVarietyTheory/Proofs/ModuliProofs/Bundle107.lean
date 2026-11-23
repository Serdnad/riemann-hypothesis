module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle100
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle101
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfAssociated
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle099
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleOfDensePart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TateIsoFieldExt

theorem exists_unit_of_pow_eq_one {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K] [CharZero K]
    (i : K →+* Ω) (n : ℕ) (hn : 0 < n) (z : Ωˣ) (hz : z ^ n = 1) :
    ∃ u : Kˣ, Units.map i.toMonoidHom u = z := by
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : NeZero (n : K) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  have h2 : IsPrimitiveRoot (i ξ) n := hξ.map_of_injective i.injective
  have hz' : (z : Ω) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hz, Units.val_one]
  obtain ⟨j, -, hj⟩ := h2.eq_pow_of_pow_eq_one hz'
  refine ⟨(hξ.isUnit hn.ne').unit ^ j, Units.ext ?_⟩
  simpa using hj

section Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
  {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω) {Q Q' : Type} [Group Q] [Group Q'] (f : Q →* Q')
  {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'}
  {e : ℕ → Q → Q → Kˣ → Prop} {e' : ℕ → Q' → Q' → Ωˣ → Prop}

theorem units_map_injective : Function.Injective (Units.map i.toMonoidHom) :=
  Units.map_injective i.injective

theorem up (hinj : Function.Injective f)
    (honto : ∀ n, 0 < n → ∀ z : Q', z ^ n = 1 → ∃ y : Q, y ^ n = 1 ∧ f y = z)
    (hact : ∀ c y, f (act c y) = act' c (f y))
    (he : ∀ n y y' c, e' n (f y) (f y') (Units.map i.toMonoidHom c) ↔ e n y y' c)
    (I : TateIso D K Q act e) :
    ∃ I' : TateIso D Ω Q' act' e', ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, I'.ev n v = f (I.ev n v) := by
  refine ⟨{ ζ := fun n => Units.map i.toMonoidHom (I.ζ n)
            ζ_prim := fun n hn => (I.ζ_prim n hn).map_of_injective (units_map_injective i)
            ζ_pow := fun n m hn hm => by rw [← map_pow, I.ζ_pow n m hn hm]
            ev := fun n v => f (I.ev n v)
            add := fun n a b => by rw [I.add, map_mul]
            lin := fun n c a => by rw [I.lin, hact]
            ker := fun n hn a => by rw [← I.ker n hn a, map_eq_one_iff f hinj]
            onto := fun n hn z => ⟨fun hz => ?_, ?_⟩
            tower := fun n m hn hm a => by rw [← map_pow, I.tower n m hn hm]
            isom := fun n hn a b => by rw [← map_zpow, he]; exact I.isom n hn a b },
    fun n _ => ⟨rfl, fun _ => rfl⟩⟩
  · obtain ⟨y, hy, rfl⟩ := honto n hn z hz
    obtain ⟨a, rfl⟩ := (I.onto n hn y).1 hy
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [← map_pow, (I.onto n hn _).2 ⟨a, rfl⟩, map_one]

theorem down [IsAlgClosed K] [CharZero K] (hinj : Function.Injective f)
    (honto : ∀ n, 0 < n → ∀ z : Q', z ^ n = 1 → ∃ y : Q, y ^ n = 1 ∧ f y = z)
    (hact : ∀ c y, f (act c y) = act' c (f y)) (hone : ∀ c, act c 1 = 1)
    (he : ∀ n y y' c, e' n (f y) (f y') (Units.map i.toMonoidHom c) ↔ e n y y' c)
    (I' : TateIso D Ω Q' act' e') :
    ∃ I : TateIso D K Q act e, ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, I'.ev n v = f (I.ev n v) := by
  have h1 : ∀ n, ∃ u : Kˣ, 0 < n → Units.map i.toMonoidHom u = I'.ζ n := fun n => by
    by_cases hn : 0 < n
    · obtain ⟨u, hu⟩ := exists_unit_of_pow_eq_one i n hn _ (I'.ζ_prim n hn).pow_eq_one
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h => absurd h hn⟩
  have h2 : ∀ n v, ∃ y : Q, (0 < n → f y = I'.ev n v) ∧ (¬ 0 < n → y = 1) := fun n v => by
    by_cases hn : 0 < n
    · obtain ⟨y, -, hy⟩ := honto n hn _ ((I'.onto n hn _).2 ⟨v, rfl⟩)
      exact ⟨y, fun _ => hy, fun h => absurd hn h⟩
    · exact ⟨1, fun h => absurd h hn, fun _ => rfl⟩
  choose ζ hζ using h1
  choose ev hev hev0 using h2
  refine ⟨{ ζ := ζ
            ζ_prim := fun n hn => ?_
            ζ_pow := fun n m hn hm => units_map_injective i ?_
            ev := ev
            add := fun n a b => ?_
            lin := fun n c a => ?_
            ker := fun n hn a => by rw [← I'.ker n hn a, ← hev n a hn, map_eq_one_iff f hinj]
            onto := fun n hn z => ?_
            tower := fun n m hn hm a => hinj ?_
            isom := fun n hn a b => ?_ },
    fun n hn => ⟨by rw [← hζ n hn]; rfl, fun v => (hev n v hn).symm⟩⟩
  · refine IsPrimitiveRoot.of_map_of_injective ?_ (units_map_injective i)
    rw [hζ n hn]; exact I'.ζ_prim n hn
  · rw [map_pow, hζ _ (Nat.mul_pos hn hm), hζ n hn, I'.ζ_pow n m hn hm]
  · by_cases hn : 0 < n
    · apply hinj
      rw [map_mul, hev _ _ hn, hev _ _ hn, hev _ _ hn, I'.add]
    · rw [hev0 _ _ hn, hev0 _ _ hn, hev0 _ _ hn, _root_.mul_one]
  · by_cases hn : 0 < n
    · apply hinj
      rw [hact, hev _ _ hn, hev _ _ hn, I'.lin]
    · rw [hev0 _ _ hn, hev0 _ _ hn, hone]
  · rw [← map_eq_one_iff f hinj, map_pow, I'.onto n hn]
    refine exists_congr fun a => ?_
    rw [← hev n a hn, hinj.eq_iff]
  · rw [map_pow, hev _ _ (Nat.mul_pos hn hm), hev _ _ hn, I'.tower n m hn hm]
  · rw [← he, map_zpow, hζ n hn, hev _ _ hn, hev _ _ hn]
    exact I'.isom n hn a b

end Abstract

noncomputable def precomp {S : Scheme.{0}} {T T' : Over S} (g : T' ⟶ T) (A : Over S) [GrpObj A] :
    (T ⟶ A) →* (T' ⟶ A) where
  toFun y := g ≫ y
  map_one' := MonObj.comp_one g
  map_mul' a b := MonObj.comp_mul g a b

theorem tateIso_fieldExt : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A)) (K Ω : Type) [Field K] [Field Ω] [IsAlgClosed K] [IsAlgClosed Ω] [CharZero K] (i : K →+* Ω) (x : Sp K ⟶ S), (∀ I : TateIso D K (Over.mk x ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∃ I' : TateIso D Ω (Over.mk (spMap i ≫ x) ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, I'.ev n v = (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ I.ev n v) ∧ ∀ I' : TateIso D Ω (Over.mk (spMap i ≫ x) ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), (∀ c, IsMonHom (act c)) → ∃ I : TateIso D K (Over.mk x ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, I'.ev n v = (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ I.ev n v := by
  intro hL E _ _ _ H D S P act K Ω _ _ _ _ _ i x
  obtain ⟨hinj, honto⟩ := GlobalTheory.T.torsion_points_descend_field_extension hL S P K Ω i x
  let g : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  have honto' : ∀ n, 0 < n → ∀ z : Over.mk (spMap i ≫ x) ⟶ P.A, z ^ n = 1 →
      ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ precomp g P.A y = z :=
    fun n hn z hz => honto n z (Nat.cast_ne_zero.mpr hn.ne') hz
  refine ⟨fun I => up D i (precomp g P.A) hinj honto' (fun c y => (Category.assoc g y (act c)).symm)
      (fun n y y' c => GlobalTheory.T.weilPairing_fieldExtension_iff S P.A K Ω i x P.L n y y' c P.isAb P.isLB) I,
    fun I' hm => down D i (precomp g P.A) hinj honto' (fun c y => (Category.assoc g y (act c)).symm)
      (fun c => ?_) (fun n y y' c => GlobalTheory.T.weilPairing_fieldExtension_iff S P.A K Ω i x P.L n y y' c P.isAb P.isLB) I'⟩
  haveI := hm c
  exact MonObj.one_comp (act c)

end GlobalTheory.TateIsoFieldExt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem obj_rigid_closed : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S' ∨ IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ :=
  fun hL E _ _ _ H D l B B' _ _ b b' S S' s s' o o' f _ =>
    obj_rigid_of_pol hL obj_isAbelianScheme_dim_rigidified_sym E H D l B B' b b' S S' s s' o o' f

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.PushInv

theorem pushInvertible_of_model : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B F O : Type) [CommRing B] [Field F] [CommRing O] (b : Base l B) (U : Scheme.{0}) (s : U ⟶ Sp B) (o : Obj D l b s) (c : U ⟶ Sp F) (β : O →+* F) (C : Cpt c o.t β), IsDedFrac β → HasTheta C.t.G C.t.PP.L → PushInvertible C.t.G C.t.PP.L := by
  intro hL hL2 hL3 E _ _ _ H D l B F O _ _ _ b U s o c β C hβ hθ
  have hS : Out.SecBaseChangeAnySt := by cases hL; cases hL2; cases hL3; assumption
  have hH : Out.GlobalSectionsRankAlgClosed := by cases hL; cases hL2; cases hL3; assumption
  obtain ⟨⟨hDom, hDed⟩, -, hFr⟩ := hβ
  let _ : Algebra O F := β.toAlgebra
  obtain ⟨hN, -, -, hPre, hFl, hDo, hQC⟩ :=
    GlobalTheory.genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have hPB : IsPullback C.m.φ o.t.G.hom C.t.G.hom (C.jQ ≫ pullback.fst C.s (spMap β)) := C.m.cart.1
  obtain ⟨w, hw, -⟩ := C.m.lin
  have hIso : LBIso o.t.PP.L (C.t.PP.L.pull C.m.φ) := ⟨w, hw⟩
  have hSm : Smooth C.t.G.hom := by
    have sa := C.t.semi
    first | infer_instance | exact sa.1 | (cases sa; assumption)
  have hGI : GeometricallyIntegral C.t.G.hom := by
    have sa := C.t.semi
    have _ := hSm
    have _ : GeometricallyConnected C.t.G.hom := by
      first | infer_instance | (cases sa; assumption)
    exact GlobalTheory.grpObj_geometricallyIntegral_of_smooth C.X C.t.G
  exact @GlobalTheory.PushInv.pushInvertible_of_densePart C.X U hN (C.jQ ≫ pullback.fst C.s (spMap β)) C.normal hPre hFl hDo hQC
    C.t.G o.t.G C.m.φ C.t.PP.L o.t.PP.L hSm hGI hPB C.t.PP.isLB o.t.PP.isLB hIso
    (GlobalTheory.PushInv.pushInvertible_any hS hH U (GlobalTheory.Obj.toPolAV o)) hθ

end GlobalTheory.PushInv
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.EffectiveCube

theorem unitAt_pull {X Y : Scheme.{0}} {N : LB X} (s : N.Sec) (φ : Y ⟶ X) (y : Y)
    (h : φ y ∈ Out.nonzeroLocus s) : UnitAt N (K := PUnit) (fun _ => φ) (fun _ => 1) y := by
  have h' : y ∈ Out.nonzeroLocus (GlobalTheory.secPull s φ) := by
    rw [GlobalTheory.nonzeroLocus_secPull]; exact h
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h'
  exact ⟨GlobalTheory.secPull s φ, fun J hJ => isUnit_sval _ (𝟙 Y) y hJ k hk⟩

theorem exists_mem_of_unitAt {X Y : Scheme.{0}} {N : LB X} (hN : N.IsLB) {I : Type} [Fintype I]
    {φ : I → (Y ⟶ X)} {ε : I → ℤ} {y : Y} (h : UnitAt N φ ε y) :
    ∃ u : (LB.LinComb N φ ε).Sec, y ∈ Out.nonzeroLocus u := by
  obtain ⟨u, hu⟩ := h
  choose J hJ using fun χ : Y ⟶ X => exists_chart hN (χ y)
  exact ⟨u, (mem_nonzeroLocus u y).2 ⟨_, Good.mem hJ φ (𝟙 Y), hu J hJ⟩⟩

theorem exists_fin_cover {X : Scheme.{0}} [CompactSpace X] [JacobsonSpace X] (M : LB X)
    (h : ∀ y : X, IsClosed {y} → ∃ u : M.Sec, y ∈ Out.nonzeroLocus u) :
    ∃ (r : ℕ) (u : Fin r → M.Sec), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  have hall : (Set.univ : Set X) ⊆ ⋃ u : M.Sec, (Out.nonzeroLocus u : Set X) := by
    intro y _
    by_contra hy
    have ho : IsOpen (⋃ u : M.Sec, (Out.nonzeroLocus u : Set X)) :=
      isOpen_iUnion fun u => (Out.nonzeroLocus u).isOpen
    obtain ⟨c, hc, hcl⟩ := nonempty_inter_closedPoints
      (Z := (⋃ u : M.Sec, (Out.nonzeroLocus u : Set X))ᶜ) ⟨y, hy⟩ ho.isClosed_compl.isLocallyClosed
    obtain ⟨u, hu⟩ := h c hcl
    exact hc (Set.mem_iUnion.2 ⟨u, hu⟩)
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover _ (fun u : M.Sec => (Out.nonzeroLocus u).isOpen) hall
  refine ⟨T.card, fun i => (T.equivFin.symm i).1, eq_top_iff.2 fun y _ => ?_⟩
  obtain ⟨u, hu, hy⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨T.equivFin ⟨u, hu⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact hy

theorem exists_sections_cube_cover :
    (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : LB P.A.left) (s : N.Sec), N.IsLB → (∃ j, s.f j ≠ 0) → ∃ (r : ℕ) (u : Fin r → (lbPow N 3).Sec), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  intro hcube K _ _ P N s hN ⟨j, hj⟩
  obtain ⟨t, ht⟩ := hcube _ P N hN
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P.isAb.geomConnected
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres P.A.hom
  have : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom
  let T : Over (Sp K) := Over.mk (𝟙 (Sp K))
  have : IsIntegral (T ⊗ P.A).left :=
    GeometricallyIntegral.geometrically_isIntegral (𝟙 (Sp K)) _ _ (IsPullback.of_hasPullback (𝟙 (Sp K)) P.A.hom).flip
  have : JacobsonSpace P.A.left := LocallyOfFiniteType.jacobsonSpace P.A.hom
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  let π : P.A ⟶ T := Over.homMk P.A.hom (Category.comp_id _)
  have hD : (((snd T P.A).left ⁻¹ᵁ Out.nonzeroLocus s : (T ⊗ P.A).left.Opens) : Set (T ⊗ P.A).left).Nonempty := by
    obtain ⟨d, hd⟩ : ((P.A.left.basicOpen (s.f j) : P.A.left.Opens) : Set P.A.left).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hj ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
    refine ⟨(lift π (𝟙 _)).left d, ?_⟩
    show (snd T P.A).left ((lift π (𝟙 _)).left d) ∈ Out.nonzeroLocus s
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hd⟩
  refine exists_fin_cover _ fun y hy => ?_
  let x : T ⟶ P.A := Over.homMk (pointOfClosedPoint P.A.hom y hy) (pointOfClosedPoint_comp P.A.hom y hy)
  let p : T.left := IsLocalRing.closedPoint K
  have hx : x.left p = y := pointOfClosedPoint_apply P.A.hom y hy p
  have hxπ : x ≫ π = 𝟙 T := Over.OverMorphism.ext (pointOfClosedPoint_comp P.A.hom y hy)
  have good : ∀ a : T ⟶ P.A, (Out.ptSecT P.A (a * x)).left p ∈ (snd T P.A).left ⁻¹ᵁ Out.nonzeroLocus s →
      UnitAt N (K := PUnit) (fun _ => ((π ≫ a) * 𝟙 P.A).left) (fun _ => 1) y := fun a ha => by
    refine unitAt_pull s _ y ?_
    have e : x ≫ ((π ≫ a) * 𝟙 P.A) = Out.ptSecT P.A (a * x) ≫ snd T P.A := by
      simp [Out.ptSecT, MonObj.comp_mul, reassoc_of% hxπ]
    rw [← hx, ← Scheme.Hom.comp_apply, ← Over.comp_left, e]
    exact ha
  obtain ⟨a, ha, -⟩ := NoBasePoint.exists_two_points (𝟙 (Sp K)) _ hD x x
  obtain ⟨b, hb, hc⟩ := NoBasePoint.exists_two_points (𝟙 (Sp K)) _ hD x (a⁻¹ * x)
  rw [← _root_.mul_assoc] at hc
  choose i hi using fun k : Fin 4 => exists_chart hN ((![a, b, b⁻¹ * a⁻¹, 1] k).left p)
  obtain ⟨w, hw⟩ := SepPoints.exists_gen_three hN t ht (π ≫ a) (π ≫ b) (π ≫ (b⁻¹ * a⁻¹)) (𝟙 P.A) 1
    (by rw [pow_one, ← MonObj.comp_mul, ← MonObj.comp_mul]; simp) i (fun k z => by
      have e : (![(π ≫ a).left, (π ≫ b).left, (π ≫ (b⁻¹ * a⁻¹)).left, (1 : P.A ⟶ P.A).left] k) =
          π.left ≫ (![a, b, b⁻¹ * a⁻¹, 1] k).left := by
        fin_cases k
        · rfl
        · rfl
        · rfl
        · exact congrArg (fun q : P.A ⟶ P.A => q.left) (MonObj.comp_one π).symm
      rw [e, Scheme.Hom.comp_apply, spec_pt_eq (k := K) (π.left z) p]
      exact hi k)
  have hw' : UnitAt N _ _ y := ⟨genSec w hw, fun J hJ => by
    rw [sval_genSec w hw _ y hJ]; exact Units.isUnit _⟩
  refine exists_mem_of_unitAt hN (UnitAt.congr hN (formEq_of_add fun U _ hh => ?_)
    (((hw'.mul (good a (ha p))).mul (good b (hb p))).mul (good _ (hc p))))
  simp [Fin.sum_univ_succ]
  module

end GlobalTheory.EffectiveCube
end
end
