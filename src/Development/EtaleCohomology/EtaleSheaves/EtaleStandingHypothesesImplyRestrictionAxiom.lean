module

import Development.EtaleCohomology.EtaleSheaves.ResZeroOfRange
import Development.EtaleCohomology.EtaleSheaves.FiltrationLevelBase
public import Development.EtaleCohomology.EtaleSheaves.LeafInj0Of
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafInj0WPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf

theorem fgtInj0 (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E)
    (hU : Subsingleton (H R U F (-1))) (y : Hrel R f F 0) (hy : fgt R f F 0 y = 0) : y = 0 := by
  intros
  apply _root_.LateralTheory.E.LeafSurj0WPf.fgt_zero <;> assumption

theorem fgtPull (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (y : Hrel R f F n) :
    pull R f F n (fgt R f F n y) = 0 := by
  apply @LateralTheory.E.RelativeTruncationSingleDegree.pull_fgt <;> assumption

theorem fgtNat (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U)
  (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (n : ℤ) (y : Hrel R f F n) :
  fgt R f' F n (rpull R f f' u e comm F n y) = pull R e F n (fgt R f F n y) := by
  obtain ⟨y, rfl⟩ := y.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  have key : mappingCone.inr ((chains R).map f') ≫ mappingCone.map ((chains R).map f') ((chains R).map f) ((chains R).map u) ((chains R).map e) (by rw [← Functor.map_comp, ← Functor.map_comp, comm]) = (chains R).map e ≫ mappingCone.inr ((chains R).map f) := by
    simp [mappingCone.map]
  simp [zcomp, rmap]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, key]

def LeafSecTw : Prop := ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (s : Sec (tw q i) U.left),
  Sec.res (prB ι U) s = 0 → ∀ x : U.left, U.hom x ∈ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Sec.res a.left s = 0

def LeafSec0W : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (h : Ht q (sch.obj U.left) 0 i),
  pull (ZMod q) (sch.map (prB ι U)) (tw q i) 0 h = 0 → ∀ x : U.left, U.hom x ∈ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ pull (ZMod q) (sch.map a.left) (tw q i) 0 h = 0

theorem etale_standing_hypotheses_imply_restriction_axiom (hH : Hyps) : A9 := by
  unfold Hyps at hH
  exact hH.2.2.2.2.2.2.2.1

theorem LeafSec0W_of (hT : LeafSecTw) : LeafSec0W := by
  intro hH q _ k _ hq i B W s ι _ U h h0 x hx
  obtain ⟨e, hnat, -⟩ := ((etale_standing_hypotheses_imply_restriction_axiom hH) (ZMod q) (tw q i)).2
  obtain ⟨t, rfl⟩ := (e U.left).surjective h
  rw [hnat] at h0
  have h1 : Sec.res (prB ι U) t = 0 := (e _).injective (by rw [h0, map_zero])
  obtain ⟨U', a, y, hy, h2⟩ := hT q k hq i s ι U t h1 x hx
  exact ⟨U', a, y, hy, by rw [hnat, h2, map_zero]⟩

theorem LeafInj0W_of (hT : LeafSecTw) : LeafInj0W := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s ι _ V hV p g1 g2 hp1 hp2 hp3 hS U c x hx
  obtain ⟨U', a, y, hy, hz⟩ := LeafSec0W_of hT hH q k hq i s ι U _ (fgtPull (ZMod q) (tw q i) (sch.map (prB ι U)) 0 c) x hx
  refine ⟨U', a, y, hy, Cov.all ?_⟩
  intro U'' b
  apply fgtInj0 (ZMod q) (tw q i) (sch.map (prB ι U''))
  · exact ((etale_standing_hypotheses_imply_restriction_axiom hH) (ZMod q) (tw q i)).1 _ (-1) (by norm_num)
  · rw [fgtNat]
    have e : (b ≫ a).left = b.left ≫ a.left := rfl
    rw [e, Functor.map_comp, pull_comp, hz, map_zero]

end LateralTheory.E.LeafInj0WPf
