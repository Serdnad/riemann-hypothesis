module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle632
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle691
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle671
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle326
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle672
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle648
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle296
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle120
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle364
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle379
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle649
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle655
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle080
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle690
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SectionTrace.SecOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle689
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle319
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle678
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle373
import GroundTheory.LocalFields.PadicLogSeries
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle294
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle311
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle293
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle284
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle303
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle304
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.GenSwap

open GlobalTheory.CompanionTheory.BZSwap

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSubquotient_of_equiv {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} {ρ' : Representation ℂ G U}
    (h : IsSubquotient σ ρ) (E : ρ.Equiv ρ') : IsSubquotient σ ρ' :=
  h.trans (IsSubquotient.of_surjective E.symm.toIntertwiningMap E.symm.surjective)

theorem isSubquotient_of_equiv_left {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {τ : Representation ℂ G U}
    {ρ : Representation ℂ G V} (E : σ.Equiv τ) (h : IsSubquotient σ ρ) : IsSubquotient τ ρ :=
  (IsSubquotient.of_surjective E.toIntertwiningMap E.surjective).trans h

theorem isGenericFor_prodIrr (hW : GlobalTheory.BZMir.Leib.WhitHeredity k) (hC : GlobalTheory.BZSeg.CuspGeneric k)
    {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1) {h N : ℕ} (x : Fin h → IrrGL (k := k))
    (hc : ∀ a, (x a).IsCusp) (hd : ∑ a, (x a).1 = N) : IsGenericFor ψ (prodIrr x hd) := by
  rw [← isGeneric_iff_isGenericFor hψ h1]
  exact (GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity k hW h N (fun a => (x a).1) hd (fun a => (x a).2.rep.V)
    (fun a => (x a).rep) (fun a => (x a).2.rep.smooth)).2 fun a =>
      hC _ _ _ (hc a).1 (x a).2.rep.smooth (x a).2.rep.irr (hc a).2

theorem isSubquotient_of_generic_common {N : ℕ} {ψ : AddChar k Circle} (hψ : Continuous ψ) {U V V' W : Type}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W] [Module ℂ W] (T : Representation ℂ (GL (Fin N) k) U) (P : Representation ℂ (GL (Fin N) k) V)
    (P' : Representation ℂ (GL (Fin N) k) V') (hT : IsSubquotient T P) (hT' : IsSubquotient T P')
    (hTg : IsGenericFor ψ T) (hP : IsSmooth P) (hfl : GlobalTheory.SmGL.HasFiniteLength P)
    (hr : Module.rank ℂ (TwJacquet P (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (σ : Representation ℂ (GL (Fin N) k) W) (hi : σ.IsIrreducible) (hgσ : IsGenericFor ψ σ)
    (hsq : IsSubquotient σ P) : IsSubquotient σ P' := by
  have hTs : IsSmooth T := hT.isSmooth hP
  have hTf : GlobalTheory.SmGL.HasFiniteLength T := GlobalTheory.CompanionTheory.IrrSub.hasFiniteLength_of_isSubquotient hT hfl
  obtain ⟨A, B, -, hi', -, hg'⟩ := GlobalTheory.T.generic_has_generic_irreducible_subquotient k ψ hψ N T hTs hTf hTg
  have s₁ := GlobalTheory.ParIndExact.isSubquotient_subQuot A B
  obtain ⟨e⟩ := GlobalTheory.T.whittaker_rank_extension_bound k ψ hψ N P σ (subQuot A B) hP hr hi hi' hsq (s₁.trans hT) hgσ hg'
  exact isSubquotient_of_equiv_left e.symm (s₁.trans hT')

theorem isSubquotient_of_common {s N : ℕ} (hW : GlobalTheory.BZMir.Leib.WhitHeredity k) {ψ : AddChar k Circle}
    (hψ : Continuous ψ) (h1 : ψ ≠ 1) (d : Fin s → ℕ) (hN : ∑ a, d a = N) {X Y Z : Fin s → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    [∀ a, AddCommGroup (Z a)] [∀ a, Module ℂ (Z a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (π' : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Y a))
    (τ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Z a)) (hπ : ∀ a, IsSmooth (π a)) (hπ' : ∀ a, IsSmooth (π' a))
    (hτ : ∀ a, IsSmooth (τ a)) (hq : ∀ a, IsSubquotient (τ a) (π a)) (hq' : ∀ a, IsSubquotient (τ a) (π' a))
    (hg : ∀ a, IsGenericFor ψ (τ a)) {V V' W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W] [Module ℂ W] (P : Representation ℂ (GL (Fin N) k) V) (P' : Representation ℂ (GL (Fin N) k) V')
    (E : (multiProd (stdBlocks d hN) π).Equiv P) (E' : (multiProd (stdBlocks d hN) π').Equiv P')
    (hP : IsSmooth P) (hfl : GlobalTheory.SmGL.HasFiniteLength P)
    (hr : Module.rank ℂ (TwJacquet P (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (σ : Representation ℂ (GL (Fin N) k) W) (hi : σ.IsIrreducible) (hgσ : IsGenericFor ψ σ)
    (hsq : IsSubquotient σ P) : IsSubquotient σ P' := by
  have hTg : IsGenericFor ψ (multiProd (stdBlocks d hN) τ) := by
    obtain ⟨H⟩ := hW ψ hψ h1 s N d hN Z τ hτ
    have : Nontrivial (⨂[ℂ] a, TwJacquet (τ a) (unipB k (Fin (d a))) (whitChar ψ (d a))) :=
      (GlobalTheory.CompanionTheory.Leib.nontrivial_piTensorProduct_iff _).2 hg
    exact H.toEquiv.nontrivial
  exact isSubquotient_of_generic_common hψ _ P P'
    (isSubquotient_of_equiv (GlobalTheory.T.product_preserves_subquotient k d N hN Z X τ π hπ hq) E)
    (isSubquotient_of_equiv (GlobalTheory.T.product_preserves_subquotient k d N hN Z Y τ π' hπ' hq') E') hTg hP hfl hr σ hi hgσ hsq

theorem isSubquotient_of_positions {s N : ℕ} (hW : GlobalTheory.BZMir.Leib.WhitHeredity k) {ψ : AddChar k Circle}
    (hψ : Continuous ψ) (h1 : ψ ≠ 1) (d : Fin s → ℕ) (hN : ∑ a, d a = N) {X Y : Fin s → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (π' : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Y a))
    (hπ : ∀ a, IsSmooth (π a)) (hπ' : ∀ a, IsSmooth (π' a)) (hg : ∀ a, IsGenericFor ψ (π a))
    (hf : ∀ a, GlobalTheory.SmGL.HasFiniteLength (π a))
    (hsw : ∀ a (W : Type) [AddCommGroup W] [Module ℂ W] (g : Representation ℂ (GL (Fin (d a)) k) W),
      IsSmooth g → g.IsIrreducible → IsSubquotient g (π a) → IsSubquotient g (π' a))
    {V V' W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W] [Module ℂ W] (P : Representation ℂ (GL (Fin N) k) V) (P' : Representation ℂ (GL (Fin N) k) V')
    (E : (multiProd (stdBlocks d hN) π).Equiv P) (E' : (multiProd (stdBlocks d hN) π').Equiv P')
    (hP : IsSmooth P) (hfl : GlobalTheory.SmGL.HasFiniteLength P)
    (hr : Module.rank ℂ (TwJacquet P (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (σ : Representation ℂ (GL (Fin N) k) W) (hi : σ.IsIrreducible) (hgσ : IsGenericFor ψ σ)
    (hsq : IsSubquotient σ P) : IsSubquotient σ P' := by
  have ex := fun a => GlobalTheory.T.generic_has_generic_irreducible_subquotient k ψ hψ (d a) (π a) (hπ a) (hf a) (hg a)
  choose A B _ hirr hsm hgen using ex
  have hq : ∀ a, IsSubquotient (subQuot (A a) (B a)) (π a) := fun a => GlobalTheory.ParIndExact.isSubquotient_subQuot _ _
  exact isSubquotient_of_common hW hψ h1 d hN π π' (fun a => subQuot (A a) (B a)) hπ hπ' hsm hq
    (fun a => hsw a _ _ (hsm a) (hirr a) (hq a)) hgen P P' E E' hP hfl hr σ hi hgσ hsq

theorem fac_rev {h j : ℕ} (hj : j + 1 < h) (x : Fin h → IrrGL (k := k)) (i : Fin 2) :
    (fac hj x 1 : Fin 2 → IrrGL (k := k)) (Fin.rev i) = (fac' hj x 1 : Fin 2 → IrrGL (k := k)) i := by
  rw [fac_one hj x, fac'_one hj x]
  fin_cases i <;> rfl

theorem nonempty_equiv_of_eq {n M : ℕ} {u v : Fin n → IrrGL (k := k)} (e : u = v) (h₁ : ∑ a, (u a).1 = M)
    (h₂ : ∑ a, (v a).1 = M) : Nonempty ((prodIrr u h₁).Equiv (prodIrr v h₂)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩



theorem position_swap (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : Zc.Cos.GKLocal k) {h j : ℕ} (hj : j + 1 < h)
    (x : Fin h → IrrGL (k := k)) (d : Fin 3 → ℕ)
    (s₁ : ∀ a, ∑ b, (fac hj x a b).1 = d a) (s₂ : ∀ a, ∑ b, (fac' hj x a b).1 = d a) :
    ∀ a (W : Type) [AddCommGroup W] [Module ℂ W] (g : Representation ℂ (GL (Fin (d a)) k) W),
      IsSmooth g → g.IsIrreducible → IsSubquotient g (prodIrr (fac hj x a) (s₁ a)) →
      IsSubquotient g (prodIrr (fac' hj x a) (s₂ a)) := by
  refine fin_three_forall ?_ ?_ ?_
  · intro W _ _ g _ _ hq
    obtain ⟨E⟩ := nonempty_equiv_of_eq (fac'_zero hj x).symm (s₁ 0) (s₂ 0)
    exact isSubquotient_of_equiv hq E
  · intro W _ _ g hgs hgi hq
    have hd2 : ∑ a, (fac hj x 1 (Fin.rev a)).1 = d 1 :=
      (Equiv.sum_comp Fin.revPerm fun b => (fac hj x 1 b).1).trans (s₁ 1)
    obtain ⟨E⟩ := prodIrr_congr rfl (fun a => fac hj x 1 (Fin.rev a)) (fac' hj x 1) (fun i => fac_rev hj x i) hd2 (s₂ 1)
    exact isSubquotient_of_equiv (GlobalTheory.T.reversed_product_same_subquotients hA hGK (fac hj x 1) (s₁ 1) hd2 g hgs hgi hq) E
  · intro W _ _ g _ _ hq
    obtain ⟨E⟩ := nonempty_equiv_of_eq (fac'_two hj x).symm (s₁ 2) (s₂ 2)
    exact isSubquotient_of_equiv hq E



theorem core (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : Zc.Cos.GKLocal k) (hW : GlobalTheory.BZMir.Leib.WhitHeredity k)
    (hR : GlobalTheory.BZSeg.WhitRankIrr k) (hC : GlobalTheory.BZSeg.CuspGeneric k) (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (h1 : ψ ≠ 1) {h N j : ℕ} (hj : j + 1 < h) (x : Fin h → IrrGL (k := k)) (hc : ∀ a, (x a).IsCusp) (d : Fin 3 → ℕ)
    (s₁ : ∀ a, ∑ b, (fac hj x a b).1 = d a) (s₂ : ∀ a, ∑ b, (fac' hj x a b).1 = d a) (hN : ∑ a, d a = N)
    (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)).1 = N)
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W) (hi : σ.IsIrreducible)
    (hg : IsGenericFor ψ σ) (hsq : IsSubquotient σ (prodIrr x hd)) :
    IsSubquotient σ (prodIrr (fun a => x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)) hd') := by
  have hJ : j < h := by omega
  have hkey : ∀ c, fac' hj x (ofLex (order hj c)).1 (ofLex (order hj c)).2 =
      x (Equiv.swap (⟨j, hJ⟩ : Fin h) ⟨j + 1, hj⟩ c) := fun c =>
    congrArg (fun y => x (Equiv.swap (⟨j, hJ⟩ : Fin h) ⟨j + 1, hj⟩ y)) (place_order hj c)
  obtain ⟨p⟩ := flatten (grp h j) (fac hj x) d s₁ hN (order hj) x (fun c => congrArg x (place_order hj c)) hd
  obtain ⟨q⟩ := flatten (grp h j) (fac' hj x) d s₂ hN (order hj)
    (fun a => x (Equiv.swap (⟨j, hJ⟩ : Fin h) ⟨j + 1, hj⟩ a)) hkey hd'
  exact isSubquotient_of_positions hW hψ h1 d hN (fun a => prodIrr (fac hj x a) (s₁ a))
    (fun a => prodIrr (fac' hj x a) (s₂ a)) (fun _ => isSmooth_prodIrr _ _) (fun _ => isSmooth_prodIrr _ _)
    (fun a => isGenericFor_prodIrr hW hC hψ h1 _ (fun _ => hc _) _) (fun _ => GlobalTheory.T.product_irreducible_finite_length hA _ _)
    (position_swap hA hGK hj x d s₁ s₂) _ _ p q
    (isSmooth_prodIrr _ _) (GlobalTheory.T.product_irreducible_finite_length hA _ _) (GlobalTheory.T.whittaker_rank_product_le_one k hW hR ψ hψ h1 h N x hd) σ hi hg hsq

theorem isSubquotient_prodIrr_swap : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.CuspGeneric k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)), (∀ a, (x a).IsCusp) → ∀ (hd : ∑ a, (x a).1 = N) (j : ℕ) (hj : j + 1 < h) (hd' : ∑ a, (x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsGenericFor ψ σ → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)) hd') := by
  intro k _ _ _ _ hA hGK hW hR hC ψ hψ h1 h N x hc hd j hj hd' W _ _ σ _ hi hg hsq
  have t : ∑ b : Fin 2, ((fac' hj x 1 : Fin 2 → IrrGL (k := k)) b).1 = ∑ b : Fin 2, ((fac hj x 1 : Fin 2 → IrrGL (k := k)) b).1 := by
    rw [fac_one hj x, fac'_one hj x]
    simp [Fin.sum_univ_two, add_comm]
  have s₂ : ∀ a, ∑ b, (fac' hj x a b).1 = ∑ b, (fac hj x a b).1 :=
    fin_three_forall (by rw [fac'_zero hj x]) t (by rw [fac'_two hj x])
  exact core hA hGK hW hR hC ψ hψ h1 hj x hc (fun a => ∑ b, (fac hj x a b).1) (fun _ => rfl) s₂
    ((sum_place hj fun c => (x c).1).trans hd) hd hd' σ hi hg hsq

end GlobalTheory.CompanionTheory.GenSwap

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.pullback_schwartz_linear_independent : PositivityTheory.GramSchwartzFunctions.PullSchLI := by
  first | exact @GlobalTheory.CompanionTheory.PullSch.pullSchLI | exact GlobalTheory.CompanionTheory.PullSch.pullSchLI | (intros; apply GlobalTheory.CompanionTheory.PullSch.pullSchLI <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.WordProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem row_ne_zero {n p N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsSmooth π) (zz : Fin n → IrrGL (k := k)) (σ : Fin p ↪o Fin n)
    (c : Fin n → ℕ) (hc : ∀ a, c (σ a) = (zz (σ a)).1) (hc0 : ∀ j, j ∉ Set.range σ → c j = 0)
    (hz : ∑ a, (zz (σ a)).1 = N) (f : (Σ j, Fin (c j)) ≃ Fin N) (h : jm (fun a => zz (σ a)) hz π ≠ 0) :
    jhMult (piTensor fun j => (clOf (zz j) (c j)).rep.ρ) (_root_.GlobalTheory.SmGL.jac f π) ≠ 0 :=
  GlobalTheory.T.jacquet_multiplicity_order_embedding π hπ zz σ c hc hc0 hz f h

theorem col_equiv (a : IrrGL (k := k)) {α : Type} [Fintype α] [LinearOrder α] (b : α → ℕ) (i₀ : α)
    (hb : b i₀ = a.1) (hb0 : ∀ i, i ≠ i₀ → b i = 0) (g : (Σ i, Fin (b i)) ≃ Fin a.1) :
    Nonempty ((multiProd g fun i => (clOf a (b i)).rep.ρ).Equiv a.rep) :=
  GlobalTheory.T.multi_product_single_factor_equiv a b i₀ hb hb0 g


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem interleave_embed {T : Type 1} {u v w : List T} (h : Zc.Comb.Interleave u v w) :
    ∃ (r : Fin w.length → Fin 2) (σ₀ : Fin u.length ↪o Fin w.length) (σ₁ : Fin v.length ↪o Fin w.length),
      (∀ j, r j = 0 ↔ j ∈ Set.range σ₀) ∧ (∀ j, r j = 1 ↔ j ∈ Set.range σ₁) ∧
        (∀ a, w.get (σ₀ a) = u.get a) ∧ (∀ a, w.get (σ₁ a) = v.get a) :=
  GlobalTheory.T.interleaving_two_colour_embedding h

theorem jm_congr' {h N : ℕ} {x x' : Fin h → IrrGL (k := k)} (e : x = x') (hd : ∑ a, (x a).1 = N)
    (hd' : ∑ a, (x' a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) :
    jm x hd π = jm x' hd' π := by
  subst e; rfl

theorem sum_ite_range {n p : ℕ} (σ : Fin p ↪o Fin n) (P : Fin n → Prop) [DecidablePred P]
    (hP : ∀ j, P j ↔ j ∈ Set.range σ) (F : Fin n → ℕ) :
    ∑ j, (if P j then F j else 0) = ∑ a, F (σ a) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun a _ => σ a) (fun a _ => by simp [hP]) (fun a _ b _ h => σ.injective h)
    (fun j hj => ?_) (fun a _ => rfl)
  obtain ⟨a, rfl⟩ := (hP j).1 (Finset.mem_filter.1 hj).2
  exact ⟨a, Finset.mem_univ _, rfl⟩

theorem jhMult_jac_multiProd_ne_zero {α β n : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    [Fintype n] [DecidableEq n] {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
    (E : (Σ i, m i) ≃ n) (E' : (Σ j, m' j) ≃ n)
    {X : α → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)) (hs : ∀ i, IsSmooth (ρ i))
    (hl : ∀ i, HasFiniteLength (ρ i)) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (Levi k m') Y) (hτ : τ.IsIrreducible) (hτs : IsSmooth τ)
    (b₀ : SizeMatrix m m') (s₀ : ∀ i j, IrrCl (GL (Fin (b₀.1 i j)) k))
    (hrow : ∀ (f : ∀ i, (Σ j, Fin (b₀.1 i j)) ≃ m i) i,
      jhMult (piTensor fun j => (s₀ i j).rep.ρ) (_root_.GlobalTheory.SmGL.jac (f i) (ρ i)) ≠ 0)
    (hcol : ∀ g : ∀ j, (Σ i, Fin (b₀.1 i j)) ≃ m' j,
      jhMult τ (piTensor fun j => multiProd (g j) fun i => (s₀ i j).rep.ρ) ≠ 0) :
    jhMult τ (_root_.GlobalTheory.SmGL.jac E' (multiProd E ρ)) ≠ 0 := by
  classical
  haveI : Fintype (SizeMatrix m m') := Fintype.ofFinite _
  have hG := GlobalTheory.CompanionTheory.GeoLink.geometricLemma k
  let f : ∀ (b : SizeMatrix m m') i, (Σ j, Fin (b.1 i j)) ≃ m i := fun b => b.nonempty_rows.some
  let g : ∀ (b : SizeMatrix m m') j, (Σ i, Fin (b.1 i j)) ≃ m' j := fun b => b.nonempty_cols.some
  rw [multiProd, hG.1.jhMult_eq E E' (isSmooth_piTensor hs) f g hτ]
  intro h0
  refine absurd ((Finset.sum_eq_zero_iff.1 h0) b₀ (Finset.mem_univ _)) ?_
  obtain ⟨T, hTout, hT⟩ := hG.2 α β m m' (fun i j => Fin (b₀.1 i j)) (f b₀) (g b₀) X ρ hs hl
  rw [show jhMult τ (cellFunctor (f b₀) (g b₀) (piTensor ρ)) = _ from hT ⟨Y, τ, hτs, hτ⟩]
  have hmem : s₀ ∈ T := by
    by_contra hn
    obtain ⟨i, hi⟩ := hTout s₀ hn
    exact hrow (f b₀) i hi
  intro hsum
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => hrow (f b₀) i) (hcol (g b₀))
    ((Finset.sum_eq_zero_iff.1 hsum) s₀ hmem)

theorem wd_prod₂_of_interleave_fin (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (X : Fin 2 → IrrGL (k := k))
    (u v w : List (IrrGL (k := k))) (hxu : Wd (X 0).rep u) (hyv : Wd (X 1).rep v) (hw : Zc.Comb.Interleave u v w) :
    Wd (prod₂ (X 0).rep (X 1).rep) w := by
  classical
  obtain ⟨hdu, hju⟩ := hxu
  obtain ⟨hdv, hjv⟩ := hyv
  have hE := interleave_embed (T := IrrGL (k := k)) hw
  obtain ⟨r, σ₀, σ₁, hE⟩ := hE
  obtain ⟨hr0, hr1, hw0, hw1⟩ := hE
  let n := w.length
  let m : Fin 2 → Type := fun i => Fin (X i).1
  let m' : Fin n → Type := fun j => Fin (w.get j).1
  have hdeg0 : ∑ a, (w.get (σ₀ a)).1 = (X 0).1 := by
    rw [← hdu]; exact Finset.sum_congr rfl fun a _ => by rw [hw0]
  have hdeg1 : ∑ a, (w.get (σ₁ a)).1 = (X 1).1 := by
    rw [← hdv]; exact Finset.sum_congr rfl fun a _ => by rw [hw1]
  have hrow : ∀ i : Fin 2, ∑ j, (if r j = i then (w.get j).1 else 0) = (X i).1 := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · exact (sum_ite_range σ₀ _ hr0 _).trans hdeg0
    · exact (sum_ite_range σ₁ _ hr1 _).trans hdeg1
  have hsplit : ∀ j, (w.get j).1 =
      (if r j = 0 then (w.get j).1 else 0) + (if r j = 1 then (w.get j).1 else 0) := by
    intro j
    rcases Fin.exists_fin_two.1 ⟨r j, rfl⟩ with h | h <;> simp [h]
  have hd' : ∑ j, (w.get j).1 = (X 0).1 + (X 1).1 := by
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) (hrow 0) (hrow 1)
  have hd : ∑ a, (X a).1 = (X 0).1 + (X 1).1 := Fin.sum_univ_two _
  let b₀ : SizeMatrix m m' := ⟨fun i j => if r j = i then (w.get j).1 else 0, fun i => by
    simpa [m] using hrow i, fun j => by
    rcases Fin.exists_fin_two.1 ⟨r j, rfl⟩ with h | h <;> simp [m', h]⟩
  let ρ : ∀ i, Representation ℂ (GL (m i) k) (X i).2.rep.V := fun i => (X i).rep
  have hs : ∀ i, IsSmooth (ρ i) := fun i => (X i).2.rep.smooth
  have hl : ∀ i, HasFiniteLength (ρ i) := fun i => hasFiniteLength_of_isIrreducible (X i).2.rep.irr
  let τ := piTensor fun j : Fin n => (w.get j).rep
  have hτ : τ.IsIrreducible := GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA w.get
  have hτs : IsSmooth τ := isSmooth_piTensor fun j => (w.get j).2.rep.smooth
  let s₀ : ∀ i j, IrrCl (GL (Fin (b₀.1 i j)) k) := fun i j => clOf (w.get j) (b₀.1 i j)
  have hrowf : ∀ (f : ∀ i, (Σ j, Fin (b₀.1 i j)) ≃ m i) i,
      jhMult (piTensor fun j => (s₀ i j).rep.ρ) (_root_.GlobalTheory.SmGL.jac (f i) (ρ i)) ≠ 0 := by
    intro f
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · refine row_ne_zero (X 0).rep (hs 0) w.get σ₀ (fun j => b₀.1 0 j) (fun a => ?_) (fun j hj => ?_) hdeg0
        (f 0) ?_
      · simp [b₀, (hr0 (σ₀ a)).2 ⟨a, rfl⟩]
      · simp [b₀, mt (hr0 j).1 hj]
      · rw [jm_congr' (funext hw0) hdeg0 hdu]; exact hju
    · refine row_ne_zero (X 1).rep (hs 1) w.get σ₁ (fun j => b₀.1 1 j) (fun a => ?_) (fun j hj => ?_) hdeg1
        (f 1) ?_
      · simp [b₀, (hr1 (σ₁ a)).2 ⟨a, rfl⟩]
      · simp [b₀, mt (hr1 j).1 hj]
      · rw [jm_congr' (funext hw1) hdeg1 hdv]; exact hjv
  have hcolf : ∀ g : ∀ j, (Σ i, Fin (b₀.1 i j)) ≃ m' j,
      jhMult τ (piTensor fun j => multiProd (g j) fun i => (s₀ i j).rep.ρ) ≠ 0 := by
    intro g
    have hcol : ∀ j, Nonempty ((multiProd (g j) fun i => (s₀ i j).rep.ρ).Equiv (w.get j).rep) := fun j =>
      col_equiv (w.get j) (fun i => b₀.1 i j) (r j) (by simp [b₀]) (fun i hi => by simp [b₀, Ne.symm hi])
        (g j)
    rw [jhMult_congr_right τ (piTensorEquiv fun j => (hcol j).some), jhMult_self hτ]
    exact one_ne_zero
  refine ⟨hd', ?_⟩
  have hφ : Nonempty ((prod₂ (X 0).rep (X 1).rep).Equiv (prodIrr X hd)) :=
    nonempty_prod₂_equiv_prodIrr_rep X hd
  let E' := stdBlocks (fun a => (w.get a).1) hd'
  have e1 : jm w.get hd' (prod₂ (X 0).rep (X 1).rep) = jhMult τ (_root_.GlobalTheory.SmGL.jac E' (prodIrr X hd)) :=
    jhMult_congr_right τ (GlobalTheory.SmGL.Exponents.jacEquiv E' hφ.some)
  rw [e1]
  exact jhMult_jac_multiProd_ne_zero (stdBlocks (fun a => (X a).1) hd) E' ρ hs hl τ hτ hτs b₀ s₀ hrowf hcolf

theorem wd_prod₂_of_interleave (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x y : IrrGL (k := k))
    (u v w : List (IrrGL (k := k))) (_hu : ∀ c ∈ u, c.IsCusp) (_hv : ∀ c ∈ v, c.IsCusp) (hxu : Wd x.rep u)
    (hyv : Wd y.rep v) (hw : Zc.Comb.Interleave u v w) : Wd (prod₂ x.rep y.rep) w := by
  obtain ⟨X, rfl, rfl⟩ : ∃ X : Fin 2 → IrrGL (k := k), X 0 = x ∧ X 1 = y := ⟨![x, y], rfl, rfl⟩
  exact wd_prod₂_of_interleave_fin hA X u v w hxu hyv hw

end GlobalTheory.CompanionTheory.WordProd

end
end

section


theorem _root_.GlobalTheory.T.match_levi_words_of : PositivityTheory.Rg.BcB.F.MLM.MatchLMWordSOf := by
  first | exact @GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf | exact GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf | (intros; apply GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf <;> assumption)
end

section


theorem _root_.GlobalTheory.T.regular_power_torus : PositivityTheory.Rg.BcB.F.MLM.RegPowT := by
  first | exact @GlobalTheory.CompanionTheory.RegPow.regPowT | exact GlobalTheory.CompanionTheory.RegPow.regPowT | (intros; apply GlobalTheory.CompanionTheory.RegPow.regPowT <;> assumption)
end

section

open ResidueKilled.Tr
open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.TChartProof

open Matrix

theorem mat_mul' {D : D7} {n : ℕ} (g h : G D n) : mat (g * h) = mat g * mat h := by
  simp only [mat, map_mul, Units.val_mul]

theorem mat_one' {D : D7} {n : ℕ} : mat (1 : G D n) = 1 := by
  simp only [mat, map_one, Units.val_one]

theorem blkA_mul_of_lowerLeft {R : Type} [CommRing R] {n : ℕ} (X Y : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (hY : ∀ i j : Fin n, Y (Fin.natAdd n i) (Fin.castAdd n j) = 0) : blkA (X * Y) = blkA X * blkA Y := by
  ext i j
  simp only [blkA, Matrix.mul_apply, Fin.sum_univ_add, hY, mul_zero, Finset.sum_const_zero, add_zero,
    toBlocks₁₁, Matrix.of_apply, submatrix_apply, finSumFinEquiv_apply_left]

theorem blkA_one' {R : Type} [CommRing R] {n : ℕ} : blkA (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  ext i j
  simp [blkA, toBlocks₁₁, Matrix.one_apply]

theorem exists_gl_blkA {D : D7} {n : ℕ} {g : G D n} (hg : g ∈ P D n) :
    ∃ a : GL (Fin n) (AE D), blkA (mat g) = a.1 := by
  have hg' : g⁻¹ ∈ P D n := inv_mem hg
  have e₁ : blkA (mat g) * blkA (mat g⁻¹) = 1 := by
    rw [← blkA_mul_of_lowerLeft _ _ (chart_lowerLeft_zero hg'), ← mat_mul', mul_inv_cancel, mat_one', blkA_one']
  have e₂ : blkA (mat g⁻¹) * blkA (mat g) = 1 := by
    rw [← blkA_mul_of_lowerLeft _ _ (chart_lowerLeft_zero hg), ← mat_mul', inv_mul_cancel, mat_one', blkA_one']
  exact ⟨⟨_, _, e₁, e₂⟩, rfl⟩

theorem tChart : TChart := by
  intro hDict hDI hStd D χ V a hMaj
  obtain ⟨m0, hm0, hp0⟩ := GlobalTheory.T.exists_siegel_parabolic_conj_doubled_compact D
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_standardUnitaryChart_doubledSpace D V m0 hm0
  obtain ⟨p, hp⟩ := hp0 V a hMaj κ hκ
  obtain ⟨hc, hc'⟩ := GlobalTheory.T.continuous_standardUnitaryChart_and_symm D V m0 hm0 κ hκ
  obtain ⟨Ψ, h1, h2, h3, h4⟩ := hStd hDict hDI D χ V.rank
  have hG := GlobalTheory.T.standardUnitaryChart_mem_rational_iff D V m0 hm0 κ hκ
  have hP := GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D V m0 hm0 κ hκ
  let κt : GA D (dblSp V) ≃ₜ* G D V.rank :=
    { κ with continuous_toFun := hc, continuous_invFun := hc' }
  have hκt : ∀ g, κt g = κ g := fun _ => rfl
  refine ⟨κt.trans Ψ, p, fun g => ?_, fun g => ?_, fun k => ?_, fun q => ?_, fun x => ?_⟩
  · exact (hG g).trans (h1 (κ g))
  · exact (hP g).trans (h2 (κ g))
  · exact (hp k).trans (h3 _)
  · obtain ⟨b, hb⟩ := exists_gl_blkA ((hP q).1 q.2)
    have e₁ := GlobalTheory.T.standardUnitaryChart_siegelLeviDet_eq D V m0 hm0 κ hκ q b hb
    have e₂ := h4 (κ q) b hb
    rw [e₁]
    exact e₂
  · have e := (hDict D.host.F D.host.E).2.2.2.2 x
    show Real.log _ = _
    rw [e]

end GlobalTheory.CompanionTheory.TChartProof
end

section

open ResidueKilled.Tr

theorem _root_.GlobalTheory.T.standard_section_exists : TStd := by
  first | exact @GlobalTheory.CompanionTheory.StdChart.tStd | exact GlobalTheory.CompanionTheory.StdChart.tStd | (intros; apply GlobalTheory.CompanionTheory.StdChart.tStd <;> assumption)
end
