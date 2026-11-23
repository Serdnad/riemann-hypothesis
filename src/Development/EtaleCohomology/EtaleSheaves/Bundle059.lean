module

public import Development.EtaleCohomology.EtaleSheaves.Bundle048
public import Development.EtaleCohomology.TateTwists.Bundle019
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.EtaleCohomology.EtaleSheaves.Bundle049
public import Development.EtaleCohomology.EtaleSheaves.Bundle051
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafDegCut
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves

def Cov {B : Scheme.{0}} (U : B.Etale) (P : ∀ U' : B.Etale, (U' ⟶ U) → Prop) : Prop :=
  ∃ S ∈ (EtTop B) U, ∀ (U' : B.Etale) (a : U' ⟶ U), S a → P U' a

theorem Cov.mono {B : Scheme.{0}} {U : B.Etale} {P Q : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : Cov U P)
    (hPQ : ∀ U' a, P U' a → Q U' a) : Cov U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun U' a ha => hPQ U' a (hP U' a ha)⟩

theorem Cov.and {B : Scheme.{0}} {U : B.Etale} {P Q : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : Cov U P) (h' : Cov U Q) :
    Cov U (fun U' a => P U' a ∧ Q U' a) := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨S', hS', hQ⟩ := h'
  exact ⟨S ⊓ S', (EtTop B).intersection_covering hS hS', fun U' a ha => ⟨hP U' a ha.1, hQ U' a ha.2⟩⟩

theorem Cov.all {B : Scheme.{0}} {U : B.Etale} {P : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : ∀ U' a, P U' a) : Cov U P :=
  ⟨⊤, (EtTop B).top_mem U, fun U' a _ => h U' a⟩

def SHV (q : ℕ) (i : ℤ) {B Y0 Y1 Y2 : Scheme.{0}} (V : B.Opens) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1) : Prop :=
  ∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)

abbrev rY (q : ℕ) (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) (m : ℤ) :=
  rpl q i (prU p ι U) (prU p ι U') (resYW p ι a) (resY p a) (pullback.lift_fst _ _ _).symm m

abbrev rB (q : ℕ) (i : ℤ) {B W : Scheme.{0}} (ι : W ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) (m : ℤ) :=
  rpl q i (prB ι U) (prB ι U') (resBW ι a) a.left (pullback.lift_fst _ _ _).symm m

abbrev gY (q : ℕ) (i : ℤ) {B W Y Y' : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) (ι : W ⟶ B) (U : B.Etale) (m : ℤ) :=
  rpl q i (prU p ι U) (prU (g ≫ p) ι U) (mW p g ι U) (mY p g U) (pullback.lift_fst _ _ _).symm m

abbrev bY (q : ℕ) (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (m : ℤ) :=
  rpl q i (prB ι U) (prU p ι U) (toBW p ι U) (toBY p U) (pullback.lift_fst _ _ _).symm m

def LeafNeg : Prop := ∀ (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (m : ℤ), m < 0 →
  Subsingleton (Hrel R f F m)

def LeafShMapZero : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (K K' : DerivedCategory (SShv B q)) (f : K ⟶ K') (m : ℤ),
  (∀ (U : B.Etale) (x : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K),
    Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map f = 0)) →
  (DerivedCategory.homologyFunctor (SShv B q) m).map f = 0

def LeafShIso : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (L K : DerivedCategory (SShv B q)) (ℓ : L ⟶ K) (m : ℤ),
  (∀ (U : B.Etale) (x x' : (OU B q).obj U ⟶ (shiftFunctor _ m).obj L),
    Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map ℓ = (OU B q).map a ≫ x' ≫ (shiftFunctor _ m).map ℓ) →
    Cov U (fun U' a => (OU B q).map a ≫ x = (OU B q).map a ≫ x')) →
  (∀ (U : B.Etale) (y : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K),
    Cov U (fun U' a => ∃ x : (OU B q).obj U' ⟶ (shiftFunctor _ m).obj L, (OU B q).map a ≫ y = x ≫ (shiftFunctor _ m).map ℓ)) →
  IsIso ((DerivedCategory.homologyFunctor (SShv B q) m).map ℓ)

def LeafVan0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ (m : ℤ), 2 < m → ∀ y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m,
  Cov U (fun U' a => rY q i p ι a m y = 0)

def LeafKill2 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) 2,
  Cov U (fun U' a => rY q i (g1 ≫ p) ι a 2 (gY q i p g1 ι U 2 y) = 0)

def LeafKill1 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU (g1 ≫ p) ι U)) (tw q i) 1,
  Cov U (fun U' a => rY q i (g2 ≫ g1 ≫ p) ι a 1 (gY q i (g1 ≫ p) g2 ι U 1 y) = 0)

def LeafVanB : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ (m : ℤ), 0 < m → ∀ c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m,
  Cov U (fun U' a => rB q i ι a m c = 0)

def LeafInj0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0,
  Cov U (fun U' a => rY q i (g2 ≫ g1 ≫ p) ι a 0 (bY q i (g2 ≫ g1 ≫ p) ι U 0 c) = 0) →
  Cov U (fun U' a => rB q i ι a 0 c = 0)

def LeafSurj0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU (g2 ≫ g1 ≫ p) ι U)) (tw q i) 0,
  Cov U (fun U' a => ∃ c : Hrel (ZMod q) (sch.map (prB ι U')) (tw q i) 0,
    bY q i (g2 ≫ g1 ≫ p) ι U' 0 c = rY q i (g2 ≫ g1 ≫ p) ι a 0 y)

theorem loc_zero_map {B : Scheme.{0}} {q : ℕ} {K K' : DerivedCategory (SShv B q)} (f : K ⟶ K') {m : ℤ}
    (X X' : B.Etale → Type 1) [∀ U, Zero (X' U)]
    (e : ∀ U, X U → ((OU B q).obj U ⟶ (shiftFunctor _ m).obj K))
    (e' : ∀ U, X' U → ((OU B q).obj U ⟶ (shiftFunctor _ m).obj K'))
    (hb : ∀ U, Function.Surjective (e U))
    (res' : ∀ U U', (U' ⟶ U) → X' U → X' U') (φ : ∀ U, X U → X' U)
    (hnat : ∀ U U' (a : U' ⟶ U) y, e' U' (res' U U' a y) = (OU B q).map a ≫ e' U y)
    (hf : ∀ U y, e' U (φ U y) = e U y ≫ (shiftFunctor _ m).map f)
    (hv : ∀ U y, Cov U (fun U' a => res' U U' a (φ U y) = 0)) (U : B.Etale)
    (x : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K) :
    Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map f = 0) := by
  obtain ⟨y, rfl⟩ := hb U x
  obtain ⟨y0, hy0⟩ := hb U 0
  refine (Cov.and (hv U y) (hv U y0)).mono fun U' a ⟨h1, h2⟩ => ?_
  rw [← hf, ← hnat, h1, ← h2, hnat, hf, hy0, zero_comp, comp_zero]

theorem loc_zero {B : Scheme.{0}} {q : ℕ} {K : DerivedCategory (SShv B q)} {m : ℤ}
    (X : B.Etale → Type 1) [∀ U, Zero (X U)]
    (e : ∀ U, X U → ((OU B q).obj U ⟶ (shiftFunctor _ m).obj K)) (hb : ∀ U, Function.Surjective (e U))
    (res : ∀ U U', (U' ⟶ U) → X U → X U')
    (hnat : ∀ U U' (a : U' ⟶ U) y, e U' (res U U' a y) = (OU B q).map a ≫ e U y)
    (hv : ∀ U y, Cov U (fun U' a => res U U' a y = 0)) (U : B.Etale)
    (x : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K) :
    Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map (𝟙 K) = 0) :=
  loc_zero_map (𝟙 K) X X e e hb res (fun _ y => y) hnat (fun U y => by simp) hv U x

theorem isZero_of (hZ : LeafShMapZero) {B : Scheme.{0}} {q : ℕ} (K : DerivedCategory (SShv B q)) (m : ℤ)
    (h : ∀ (U : B.Etale) (x : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K),
      Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map (𝟙 K) = 0)) :
    IsZero ((DerivedCategory.homologyFunctor (SShv B q) m).obj K) := by
  rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id]
  exact hZ B q K K (𝟙 K) m h

theorem isZero_neg (hZ : LeafShMapZero) {B : Scheme.{0}} {q : ℕ} (K : DerivedCategory (SShv B q)) (m : ℤ)
    (X : B.Etale → Type 1) (hs : ∀ U, Subsingleton (X U))
    (e : ∀ U, X U → ((OU B q).obj U ⟶ (shiftFunctor _ m).obj K)) (hb : ∀ U, Function.Surjective (e U)) :
    IsZero ((DerivedCategory.homologyFunctor (SShv B q) m).obj K) := by
  refine isZero_of hZ K m fun U x => Cov.all fun U' a => ?_
  obtain ⟨y, rfl⟩ := hb U x
  obtain ⟨y0, hy0⟩ := hb U 0
  rw [Subsingleton.elim y y0, hy0]
  simp

theorem goal_of (hN : LeafNeg) (hZ : LeafShMapZero) (hI : LeafShIso) (hV0 : LeafVan0) (hK2 : LeafKill2)
    (hK1 : LeafKill1) (hVB : LeafVanB) (hIn : LeafInj0) (hSu : LeafSurj0) : LateralTheory.E.EtaleTopologySheaves.LeafDeg := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV p g1 g2 h0 h1 h2 hA K0 K1 K2 L f g ℓ l0 l1 l2 lL r0 r1 r2 rL mf mg mℓ
  have hS : SHV q i V p g1 g2 := hA
  refine ⟨fun m hm => ?_, ?_, ?_, fun m hm => ?_, fun m hm => ?_, ?_⟩
  · exact isZero_of hZ K0 m (loc_zero _ (l0 · m) (fun U => (r0.1 U m).2) (fun U U' a => rY q i p ι a m)
      (fun U U' a y => r0.2 U U' a m y) (fun U y => hV0 hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U m hm y))
  · exact hZ B q K0 K1 f 2 (loc_zero_map f _ _ (l0 · 2) (l1 · 2) (fun U => (r0.1 U 2).2)
      (fun U U' a => rY q i (g1 ≫ p) ι a 2) (fun U => gY q i p g1 ι U 2)
      (fun U U' a y => r1.2 U U' a 2 y) (fun U y => mf U 2 y)
      (fun U y => hK2 hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U y))
  · exact hZ B q K1 K2 g 1 (loc_zero_map g _ _ (l1 · 1) (l2 · 1) (fun U => (r1.1 U 1).2)
      (fun U U' a => rY q i (g2 ≫ g1 ≫ p) ι a 1) (fun U => gY q i (g1 ≫ p) g2 ι U 1)
      (fun U U' a y => r2.2 U U' a 1 y) (fun U y => mg U 1 y)
      (fun U y => hK1 hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U y))
  · exact isZero_neg hZ K2 m _ (fun U => hN _ _ _ m hm) (l2 · m) (fun U => (r2.1 U m).2)
  · rcases lt_or_gt_of_ne hm with hm | hm
    · exact isZero_neg hZ L m _ (fun U => hN _ _ _ m hm) (lL · m) (fun U => (rL.1 U m).2)
    · exact isZero_of hZ L m (loc_zero _ (lL · m) (fun U => (rL.1 U m).2) (fun U U' a => rB q i ι a m)
        (fun U U' a c => rL.2 U U' a m c) (fun U c => hVB hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U m hm c))
  · refine hI B q L K2 ℓ 0 (fun U x x' hx => ?_) (fun U y => ?_)
    · obtain ⟨c, rfl⟩ := (rL.1 U 0).2 x
      obtain ⟨c', rfl⟩ := (rL.1 U 0).2 x'
      have hd := hIn hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U (c - c') (hx.mono fun U' a h => by
        rw [← mℓ U 0 c, ← mℓ U 0 c', ← r2.2 U U' a 0, ← r2.2 U U' a 0] at h
        rw [map_sub, map_sub, (r2.1 U' 0).1 h, sub_self])
      refine hd.mono fun U' a h => ?_
      rw [← rL.2 U U' a 0 c, ← rL.2 U U' a 0 c', sub_eq_zero.1 ((map_sub _ c c').symm.trans h)]
    · obtain ⟨z, rfl⟩ := (r2.1 U 0).2 y
      refine (hSu hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U z).mono fun U' a ⟨c, hc⟩ => ⟨lL U' 0 c, ?_⟩
      rw [← r2.2 U U' a 0 z, ← hc, mℓ U' 0 c]

end LateralTheory.E.LeafDegCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.LeafTwSecPf

namespace LateralTheory.E.LeafTwSurjPf

variable {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) (k : ℤ)

theorem mem_add {U : Over (Spec (CommRingCat.of B))} (s t : ToType ((Pr q k _).obj (op U)))
    (hs : Presheaf.imageSieve (cmap ζ k) s ∈ Scheme.etaleTopology.over _ U)
    (ht : Presheaf.imageSieve (cmap ζ k) t ∈ Scheme.etaleTopology.over _ U) :
    Presheaf.imageSieve (cmap ζ k) (s + t) ∈ Scheme.etaleTopology.over _ U := by
  refine GrothendieckTopology.superset_covering _ ?_ (GrothendieckTopology.intersection_covering _ hs ht)
  rintro V f ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  exact ⟨a + b, by rw [map_add (f := _), ha, hb, map_add (f := _)]⟩

theorem mem_smul {U : Over (Spec (CommRingCat.of B))} (c : ULift.{1} (ZMod q)) (s : ToType ((Pr q k _).obj (op U)))
    (hs : Presheaf.imageSieve (cmap ζ k) s ∈ Scheme.etaleTopology.over _ U) :
    Presheaf.imageSieve (cmap ζ k) (c • s) ∈ Scheme.etaleTopology.over _ U := by
  refine GrothendieckTopology.superset_covering _ ?_ hs
  rintro V f ⟨a, ha⟩
  exact ⟨c • a, by rw [map_smul, ha, map_smul]⟩

theorem mem_zero {U : Over (Spec (CommRingCat.of B))} :
    Presheaf.imageSieve (cmap ζ k) (0 : ToType ((Pr q k _).obj (op U))) ∈ Scheme.etaleTopology.over _ U := by
  refine GrothendieckTopology.superset_covering _ ?_ (GrothendieckTopology.top_mem _ U)
  rintro V f -
  exact ⟨0, by rw [map_zero, map_zero]⟩

theorem rel_single {A : Type} [CommRing A] (ζ' ξ : Prim q A) (a : (ZMod q)ˣ) (h : ξ.1 = ζ'.1 ^ (a : ZMod q).val) :
    Submodule.Quotient.mk (p := twRel q k A) (Finsupp.single ξ 1) =
      (ULift.up ((a ^ k : (ZMod q)ˣ) : ZMod q)) • Submodule.Quotient.mk (p := twRel q k A) (Finsupp.single ζ' 1) := by
  have hm : Finsupp.single ξ 1 - Finsupp.single ζ' (ULift.up ((a ^ k : (ZMod q)ˣ) : ZMod q)) ∈ twRel q k A :=
    Submodule.subset_span ⟨ζ', ξ, a, h, rfl⟩
  rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single, Submodule.Quotient.eq]
  convert hm using 3
  first | rfl | (ext1; simp)

theorem rel_map {A A' : Type} [CommRing A] [CommRing A'] (φ : Prim q A → Prim q A') (ζ' ξ : Prim q A)
    (a : (ZMod q)ˣ) (h : (φ ξ).1 = (φ ζ').1 ^ (a : ZMod q).val) :
    Submodule.Quotient.mk (p := twRel q k A') (Finsupp.mapDomain φ (Finsupp.single ξ 1)) =
      (ULift.up ((a ^ k : (ZMod q)ˣ) : ZMod q)) •
        Submodule.Quotient.mk (p := twRel q k A') (Finsupp.mapDomain φ (Finsupp.single ζ' 1)) := by
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single]
  exact rel_single k _ _ a h

theorem mem_single [NeZero q] (U : Over (Spec (CommRingCat.of B))) (ξ : Prim q Γ(U.left, ⊤)) :
    Presheaf.imageSieve (cmap ζ k)
      (Submodule.Quotient.mk (p := twRel q k Γ(U.left, ⊤)) (Finsupp.single ξ 1) : ToType ((Pr q k _).obj (op U)))
      ∈ Scheme.etaleTopology.over _ U := by
  obtain ⟨S, hS, hP⟩ := LateralTheory.EtaleFoundations.PrimLocPf.part2 q U.left (Prim.map (ρ U) ζ) ξ
  rw [GrothendieckTopology.mem_over_iff]
  refine GrothendieckTopology.superset_covering _ ?_ hS
  intro W g hg
  rw [Sieve.overEquiv_iff]
  obtain ⟨a, ha⟩ := hP W g hg
  refine ⟨ULift.up ((a ^ k : (ZMod q)ˣ) : ZMod q), ?_⟩
  change LinearMap.toSpanSingleton _ _ (gen ζ k (Over.mk (g ≫ U.hom))) (ULift.up ((a ^ k : (ZMod q)ˣ) : ZMod q)) =
    ((Pr q k _).map (Over.homMk g : Over.mk (g ≫ U.hom) ⟶ U).op).hom
      (Submodule.Quotient.mk (p := twRel q k Γ(U.left, ⊤)) (Finsupp.single ξ 1))
  rw [LinearMap.toSpanSingleton_apply, ← gen_map ζ k (Over.homMk g : Over.mk (g ≫ U.hom) ⟶ U)]
  exact (rel_map k _ _ _ a ha).symm

end LateralTheory.E.LeafTwSurjPf

namespace LateralTheory.E.LeafTwSecPf

theorem LeafTwSurj_of : LeafTwSurj := by
  intro q _ B _ ζ k
  constructor
  intro U s
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (twRel q k Γ(U.left, ⊤)) s
  induction x using Finsupp.induction_linear with
  | zero => exact LateralTheory.E.LeafTwSurjPf.mem_zero ζ k
  | add f g hf hg =>
    rw [Submodule.Quotient.mk_add]
    exact LateralTheory.E.LeafTwSurjPf.mem_add ζ k _ _ hf hg
  | single ξ c =>
    have h : Finsupp.single ξ c = c • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h, Submodule.Quotient.mk_smul]
    exact LateralTheory.E.LeafTwSurjPf.mem_smul ζ k c _ (LateralTheory.E.LeafTwSurjPf.mem_single ζ k U ξ)

end LateralTheory.E.LeafTwSecPf
end
end

section

namespace LateralTheory.E.E4

open Polynomial

theorem mem_bot_of_mem_adjoin_inv {k L : Type} [Field k] [Field L] [Algebra k L] (t : L) (ht : Transcendental k t)
    (c : L) (h1 : c ∈ Algebra.adjoin k {t}) (h2 : c ∈ Algebra.adjoin k {t⁻¹}) : c ∈ (⊥ : Subalgebra k L) := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h1 h2
  obtain ⟨p, rfl⟩ := h1
  obtain ⟨q, hq⟩ := h2
  have ht0 : t ≠ 0 := by
    rintro rfl; exact ht (isAlgebraic_zero)
  set N := q.natDegree
  have key : aeval t (X ^ N * p) = aeval t (reflect N q) := by
    let _ : Invertible t⁻¹ := invertibleOfNonzero (inv_ne_zero ht0)
    have h := eval₂_reflect_mul_pow (algebraMap k L) t⁻¹ N q le_rfl
    rw [invOf_eq_inv, inv_inv] at h
    have hq' : aeval t⁻¹ q = aeval t p := hq
    rw [aeval_def, aeval_def] at hq'
    rw [map_mul, map_pow, aeval_X, aeval_def, aeval_def, ← hq', ← h, mul_comm, mul_assoc, ← mul_pow,
      inv_mul_cancel₀ ht0, one_pow, mul_one]
  have hinj : Function.Injective (aeval t : k[X] →ₐ[k] L) := transcendental_iff_injective.mp ht
  have heq := hinj key
  by_cases hp : p = 0
  · simp [hp]
  have hdeg : (X ^ N * p).natDegree = N + p.natDegree := by
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hp, natDegree_X_pow]
  have hle : (reflect N q).natDegree ≤ N := natDegree_reflect_le.trans (by simp [N])
  have hp0 : p.natDegree = 0 := by rw [heq] at hdeg; omega
  rw [eq_C_of_natDegree_eq_zero hp0]
  simp

def LeafMinpolyCoeff : Prop := ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (s : L), Transcendental k s →
  ∀ (F : IntermediateField k L), F = IntermediateField.adjoin k {s} → ∀ x : L, IsIntegral (Algebra.adjoin k {s}) x →
  ∀ i : ℕ, ((minpoly F x).coeff i : L) ∈ Algebra.adjoin k {s}

theorem isIntegral_adjoin_of {k L : Type} [Field k] [Field L] [Algebra k L] (s : L) (x : L)
    (hx : IsIntegral (Algebra.adjoin k {s}) x) : IsIntegral (IntermediateField.adjoin k {s}) x := by
  obtain ⟨p, hm, hp⟩ := hx
  let ι : Algebra.adjoin k {s} →+* IntermediateField.adjoin k {s} :=
    Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin k {s}) |>.toRingHom
  refine ⟨p.map ι, hm.map _, ?_⟩
  rw [eval₂_map]
  exact hp

theorem LeafIntBoth_of' (hM : LeafMinpolyCoeff) : ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (t : L),
    Transcendental k t → ∀ x : L,
    IsIntegral (Algebra.adjoin k {t}) x → IsIntegral (Algebra.adjoin k {t⁻¹}) x → IsIntegral k x := by
  intro k L _ _ _ t ht x h1 h2
  have ht' : Transcendental k t⁻¹ := fun h => ht (by simpa using h.inv)
  set F := IntermediateField.adjoin k {t}
  have hEq : F = IntermediateField.adjoin k {t⁻¹} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      simpa using inv_mem (IntermediateField.mem_adjoin_simple_self k t⁻¹)
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self k t)
  have hxF : IsIntegral F x := isIntegral_adjoin_of t x h1
  have hc : ∀ i, ((minpoly F x).coeff i : L) ∈ (⊥ : Subalgebra k L) := fun i =>
    mem_bot_of_mem_adjoin_inv t ht _ (hM k L t ht F rfl x h1 i) (hM k L t⁻¹ ht' F hEq x h2 i)
  have hl : minpoly F x ∈ lifts (algebraMap k F) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp (hc n)
    exact ⟨a, Subtype.ext ha⟩
  obtain ⟨P, hP, -, hPm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hxF)
  refine ⟨P, hPm, ?_⟩
  have := minpoly.aeval F x
  rw [← hP, aeval_map_algebraMap] at this
  exact this

theorem LeafIntBoth_of (hM : LeafMinpolyCoeff) : LeafIntBoth := LeafIntBoth_of' hM

theorem LeafOrdAtInfinity_of_cut (hV : LeafOrdInfHom) (hM : LeafMinpolyCoeff) : LeafOrdAtInfinity :=
  LeafOrdAtInfinity_of hV (LeafIntBoth_of hM)

end LateralTheory.E.E4
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.BuildCut LateralTheory.E.CompCut

namespace LateralTheory.E.LocACPf

variable {W : Type} [CommRing W]

lemma idem_split {e : W} (he : IsIdempotentElem e) : e * (1 - e) = 0 := by
  rw [mul_sub, mul_one, he.eq, sub_self]

lemma map_zero_of_mem (hW : ProdACF W) (p : Ideal W) [p.IsPrime] {a : W} (ha : a ∈ p) :
    algebraMap W (Localization.AtPrime p) a = 0 := by
  obtain ⟨e, u, he, hu, rfl⟩ := hW.2 a
  have heq : e ∈ p := by
    rcases (inferInstance : p.IsPrime).mem_or_mem ha with h | h
    · exact h
    · exact absurd (p.eq_top_of_isUnit_mem h hu) (inferInstance : p.IsPrime).ne_top
  have h1 : (1 - e) ∈ p.primeCompl := by
    intro h
    have : (1 : W) ∈ p := by simpa using p.add_mem heq h
    exact (inferInstance : p.IsPrime).ne_top ((Ideal.eq_top_iff_one _).2 this)
  rw [IsLocalization.map_eq_zero_iff p.primeCompl]
  refine ⟨⟨1 - e, h1⟩, ?_⟩
  show (1 - e) * (e * u) = 0
  rw [← mul_assoc, mul_comm (1 - e), idem_split he, zero_mul]

lemma map_idem_one (hW : ProdACF W) (p : Ideal W) [p.IsPrime] {e : W} (he : IsIdempotentElem e) (hne : e ∉ p) :
    algebraMap W (Localization.AtPrime p) e = 1 := by
  have h1 : (1 - e) ∈ p := by
    rcases (inferInstance : p.IsPrime).mem_or_mem (show e * (1 - e) ∈ p by rw [idem_split he]; exact p.zero_mem) with h | h
    · exact absurd h hne
    · exact h
  have := map_zero_of_mem hW p h1
  rw [map_sub, map_one, sub_eq_zero] at this
  exact this.symm

lemma surj (hW : ProdACF W) (p : Ideal W) [p.IsPrime] :
    Function.Surjective (algebraMap W (Localization.AtPrime p)) := by
  intro x
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
  obtain ⟨e, u, he, hu, hs⟩ := hW.2 (s : W)
  have hne : e ∉ p := fun h => s.2 (hs ▸ p.mul_mem_right u h)
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  refine ⟨a * e * v, ?_⟩
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, hs]
  have : a * e * v * (e * u) = a * e * e * (v * u) := by ring
  rw [this, hv, mul_one, mul_assoc, he.eq, map_mul, map_idem_one hW p he hne, mul_one]

theorem LocAC_of : LocAC := by
  intro W _ hW q
  have := q.isPrime
  set p := q.asIdeal
  constructor
  · rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal,
      Ideal.map_eq_bot_iff_le_ker]
    intro a ha
    exact map_zero_of_mem hW p ha
  · intro P hP hdeg
    have hl : P ∈ Polynomial.lifts (algebraMap W (Localization.AtPrime p)) := by
      obtain ⟨Q, hQ⟩ := Polynomial.map_surjective _ (surj hW p) P
      exact Polynomial.mem_lifts _ |>.2 ⟨Q, hQ⟩
    obtain ⟨Q, hQ, hdQ, hmQ⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hP
    obtain ⟨r, hr⟩ := hW.1 Q hmQ (hdQ ▸ hdeg)
    refine ⟨algebraMap W _ r, ?_⟩
    rw [← hQ, Polynomial.eval_map, Polynomial.eval₂_at_apply, hr, map_zero]

end LateralTheory.E.LocACPf
end
end

section

open CategoryTheory AlgebraicGeometry

namespace LateralTheory.E.CoverExistence

theorem Cover_of : LateralTheory.E.ChowGraphCut.Cover := by
  intro A _ X p _ _
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have h : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := by
    intro x
    obtain ⟨V, hV, hxV, -⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨V, hV, hxV⟩
  choose V hV hxV using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  refine ⟨t.card, fun j => V (t.equivFin.symm j), fun j => hV _, fun j => ⟨_, hxV _⟩, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩

end LateralTheory.E.CoverExistence
end
