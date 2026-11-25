module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogenyOfSimilitudePullbackObjectsStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPotentialBlockDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObjMapCompBis
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHeckeOfIsHeckeWit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.ValExt


open GlobalTheory.DrinLev.HT.HeckePt GlobalTheory.CechPic in
theorem isPIsog_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N c : ℕ) (S S' : Scheme.{0}) (σ : S ⟶ Sp R) (σ' : S' ⟶ Sp R) (f : S' ⟶ S) (o o' : Obj b N σ) (o₁ o₁' : Obj b N σ') (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ → ∃ ψ₁ : o₁.A ⟶ o₁'.A, IsPIsog c o₁ o₁' ψ₁ ∧ m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ :=
  @_root_.GlobalTheory.UPel.HT.ESPull.isPIsog_pull

theorem of_ext (hext : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (v : Sp V ⟶ Sp R) (o : Obj b N v) (o₀ o₀' : Obj b N (spMap (algebraMap V (FractionRing V)) ≫ v)) (m : ObjMap o₀ o (spMap (algebraMap V (FractionRing V)))) (ψ₀ : o₀.A ⟶ o₀'.A), IsPIsog c o₀ o₀' ψ₀ → ∃ (o' : Obj b N v) (m' : ObjMap o₀' o' (spMap (algebraMap V (FractionRing V)))) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧ m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ) : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ s₀ → ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ t₀ := by
  intro p _ D R _ _ _ _ b N hN hNp _ r w j c _ _ _ _ _ M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst _ _ _ _ _ _ hψ _ V K _ _ _ _ _ _ y x hxy
  let eK : K →+* FractionRing V := (IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).toRingEquiv.toRingHom
  have heK : eK.comp (algebraMap V K) = algebraMap V (FractionRing V) := by
    ext a; exact (IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).commutes a
  let kF : Sp (FractionRing V) ⟶ Sp V := spMap (algebraMap V (FractionRing V))
  let x' : Sp (FractionRing V) ⟶ Y₀ := spMap eK ≫ x
  have hk : kF = spMap eK ≫ spMap (algebraMap V K) := by
    simp only [kF, spMap, ← heK, CommRingCat.ofHom_comp, Spec.map_comp]
  have hxy' : kF ≫ y = x' ≫ s₀ := by rw [hk, Category.assoc, hxy]; rfl
  obtain ⟨o, ⟨my⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X (Sp V) M.s y M.univ
  obtain ⟨oK, ⟨mK⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp (FractionRing V)) (y ≫ M.s) kF o
  have m1 : ObjMap oK M.univ (x' ≫ s₀) := hxy' ▸ GlobalTheory.UPel.HT.ObjMapComp.comp mK my
  obtain ⟨n₀, -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ m1 ms₀
  have key : ∀ σ : Sp (FractionRing V) ⟶ Sp R, x' ≫ (s₀ ≫ M.s) = σ → ∃ o' : Obj b N σ, Nonempty (ObjMap o' o₀' x') := by
    rintro σ rfl
    exact GlobalTheory.HTPull.exists_objMap_pull p D R b N Y₀ (Sp (FractionRing V)) (s₀ ≫ M.s) x' o₀'
  obtain ⟨oK', ⟨n₀'⟩⟩ := key (kF ≫ (y ≫ M.s)) (by rw [← Category.assoc, ← hxy', Category.assoc])
  obtain ⟨ψK, hψK, -⟩ := isPIsog_pull p D R b N c Y₀ (Sp (FractionRing V)) (s₀ ≫ M.s) (kF ≫ (y ≫ M.s)) x' o₀ o₀' oK oK' n₀ n₀' ψ₀ hψ
  obtain ⟨o', m', -, -, -⟩ := hext p D R b N hN hNp c V (y ≫ M.s) o oK oK' mK ψK hψK
  obtain ⟨z, ⟨hz, ⟨mz⟩⟩, -⟩ := M.rep (Sp V) (y ≫ M.s) o'
  refine ⟨z, ?_⟩
  obtain ⟨f, -, huniq⟩ := M.rep (Sp (FractionRing V)) (kF ≫ (y ≫ M.s)) oK'
  have e1 := huniq (kF ≫ z) ⟨by rw [Category.assoc, hz], ⟨GlobalTheory.UPel.HT.ObjMapComp.comp m' mz⟩⟩
  have e2 := huniq (x' ≫ t₀) ⟨by rw [Category.assoc, ← hst, ← Category.assoc, ← hxy', Category.assoc],
    ⟨GlobalTheory.UPel.HT.ObjMapComp.comp n₀' mt₀⟩⟩
  have e3 : spMap eK ≫ (spMap (algebraMap V K) ≫ z) = spMap eK ≫ (x ≫ t₀) := by
    rw [← Category.assoc, ← hk, e1, ← e2, Category.assoc]
  haveI : IsIso (spMap eK) := by
    let e := (IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).toRingEquiv
    have h1 : IsIso (CommRingCat.ofHom eK) := (RingEquiv.toCommRingCatIso e).isIso_hom
    exact inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom eK)))
  exact (cancel_epi (spMap eK)).1 e3

end GlobalTheory.UPel.HT.ES.ValExt
