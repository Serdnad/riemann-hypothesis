module

public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle001
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle002
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain

namespace Formalism.L2

structure RowFrame (D : D7) where
  rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r
  inj : ∀ σ σ', (rep σ).Iso (rep σ') → σ = σ'

structure RowLocTied (D : D7) (lp : LPTiedPlaceholder D) (F : RowFrame D) : Prop where

  sat : ∀ (i : D.nd.Loc) (σ : D.what₂.FT) v (w : PlE D.host), NG.OverPl w v → ∀ (Dv : InertDatum D.host.E D.R.r v w),
    (∃ α, NG.SatAtS (F.rep σ).S Dv α) → ∃ α, NG.SatAtS (F.rep σ).S Dv α ∧ D.naut.satW i σ w = Finset.univ.val.map α

variable {D : D7} {lp : LPTiedPlaceholder D} {F : RowFrame D}

end Formalism.L2
end
end

section

open Formalism.BasicNotions ReciprocityTheory.Aut Formalism.AUTREP

namespace Formalism.L2

theorem AVTied.eigen {D : D7} {M : MtFam D} (A : AVTied D M) (i : D.nd.Loc) (P : D.naut.AV i) (x : D.nd.X i)
    (hx : D.naut.ptV i P = some x) (w : PlE D.host) (k : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (NumberField.maximalRealSubfield D.host.E)) (hw : SplitOut D.nd i w)
    (hc : IsConjPl D.host w s.w) (hu : Formalism.AUTREP.IsUnif D.host.E s.v ϖ) (k1 : 1 ≤ k) (k2 : k ≤ D.R.nV)
    (y : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) (hy : y ∈ D.naut.typeV i P) :
    NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) =
      iotaOC D i ((D.nd.hT i w k : D.nd.X i → D.nd.O i) x) • (M.loc i).real y :=
  (A.ptV i P x).1 hx w k s ϖ hw hc hu k1 k2 y hy

namespace NG

open NumberField ReciprocityTheory.Aut Formalism.AUTREP

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {W W' W'' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [AddCommGroup W''] [Module ℂ W'']

theorem IsoRep.refl (S : Submodule ℂ (GAf L n → W)) : IsoRep S S :=
  ⟨LinearEquiv.refl ℂ S, fun _ _ _ h => h⟩

theorem IsoRep.trans {S : Submodule ℂ (GAf L n → W)} {S' : Submodule ℂ (GAf L n → W')}
    {S'' : Submodule ℂ (GAf L n → W'')} (h1 : IsoRep S S') (h2 : IsoRep S' S'') : IsoRep S S'' := by
  obtain ⟨T1, e1⟩ := h1
  obtain ⟨T2, e2⟩ := h2
  exact ⟨T1.trans T2, fun h f f' e => e2 h (T1 f) (T1 f') (e1 h f f' e)⟩

theorem IsoRep.symm {S : Submodule ℂ (GAf L n → W)} {S' : Submodule ℂ (GAf L n → W')}
    (hS : ∀ h, ∀ f ∈ S, rt L n h f ∈ S) (h1 : IsoRep S S') : IsoRep S' S := by
  obtain ⟨T, e⟩ := h1
  refine ⟨T.symm, fun h g g' hg => ?_⟩
  have key := e h (T.symm g) ⟨rt L n h (T.symm g : GAf L n → W), hS h _ (T.symm g).2⟩ rfl
  rw [LinearEquiv.apply_symm_apply, ← hg] at key
  have : T ⟨rt L n h (T.symm g : GAf L n → W), hS h _ (T.symm g).2⟩ = g' := Subtype.ext key
  rw [← this, LinearEquiv.symm_apply_apply]

theorem AlgWt.Iso.refl (a : AlgWt L n) : a.Iso a := ⟨LinearEquiv.refl ℂ a.W, fun _ _ => rfl⟩

theorem AlgWt.Iso.symm {a b : AlgWt L n} (h : a.Iso b) : b.Iso a := by
  obtain ⟨T, e⟩ := h
  refine ⟨T.symm, fun γ x => ?_⟩
  apply T.injective
  rw [LinearEquiv.apply_symm_apply, e, LinearEquiv.apply_symm_apply]

theorem AlgWt.Iso.trans {a b c : AlgWt L n} (h : a.Iso b) (h' : b.Iso c) : a.Iso c := by
  obtain ⟨T, e⟩ := h
  obtain ⟨T', e'⟩ := h'
  exact ⟨T.trans T', fun γ x => by simp [e, e']⟩

theorem AutRep.iso_equivalence : Equivalence (AutRep.Iso (L := L) (n := n)) := by
  constructor
  · intro π
    exact ⟨AlgWt.Iso.refl π.toAlgWt, IsoRep.refl π.S⟩
  · intro π π' h
    exact ⟨AlgWt.Iso.symm h.1, IsoRep.symm π.irrS.1.stable h.2⟩
  · intro π π' π'' h h'
    exact ⟨AlgWt.Iso.trans h.1 h'.1, IsoRep.trans h.2 h'.2⟩

end NG

end Formalism.L2
end

section

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain

namespace Formalism.L2

def gPl (D : D7) : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) :=
  {v | ∃ w : PlE D.host, NG.OverPl w v ∧ ∃ k, w ∈ placesOver D.host.E (D.host.g k)}

def qPl (D : D7) (χ : Host.HChar D.host.E) : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) :=
  {v | v ∉ gPl D ∧ ∃ w : PlE D.host, NG.OverPl w v ∧ ¬ χ.UnrAt w}

def paraPl (D : D7) (tup : D.what₂.Tup → Fin D.R.m → Host.HChar D.host.E) (i : D.nd.Loc) (j : Fin D.R.m) :
    Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) :=
  qPl D (tup (D.nd.mu i) j)

def embT (D : D7) (t : D.what₂.Tau) : D.host.E →+* ℂ :=
  D.host.emb ((D.eTau t : D.R.Psi) : D.R.GG)

def WtTied (D : D7) (μ : D.what₂.Tup) (j : Fin D.R.m) (m : MtReal D μ (j.1 + 1)) : Prop :=
  ∀ (t : D.what₂.Tau) (sh : ℂ) (a : NG.AlgWt D.host.E D.R.nV) (lam : Fin D.R.nV → ℤ),
    D.naut.infG D.naut.etaT (embT D t) = {sh} → m.wt.IsDual a → a.HWAt (embT D t) lam →
    NG.infOf lam = NG.paramV D.R (D.hc t) j sh

structure LevelTied (D : D7) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → Host.HChar D.host.E) : Prop where

  prod : ∀ i : D.nd.Loc, NG.IsProdLevel (M.loc i).J

  para : ∀ (i : D.nd.Loc) (j : Fin D.R.m), j.1 + 1 = D.nd.j i → ∀ v ∈ paraPl D tup i j,
    ∃ (s : SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.v = v ∧
      NG.IsCompAt (tup (D.nd.mu i) j) s ξ ∧ NG.LevelPara (M.loc i).J (M.loc i).χ s D.R.r ξ

  uni : ∀ (i : D.nd.Loc) (j : Fin D.R.m), j.1 + 1 = D.nd.j i → ∀ (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E),
    s.w = D.naut.plGw k v → ∃ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ)
      (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ ∧
      NG.IsCompAt (tup (D.nd.mu i) j) s ξ ∧ NG.LevelUni (M.loc i).J (M.loc i).χ s D.R.r ψ₀ ξ

  wt : ∀ (μ : D.what₂.Tup) (j : Fin D.R.m), WtTied D μ j (M μ (j.1 + 1) (by omega) (by omega))

  hyp : ∀ (i : D.nd.Loc) (j : Fin D.R.m), j.1 + 1 = D.nd.j i → NG.HypOutside (M.loc i).J (M.loc i).χ (gPl D ∪ paraPl D tup i j)

end Formalism.L2
end
end
