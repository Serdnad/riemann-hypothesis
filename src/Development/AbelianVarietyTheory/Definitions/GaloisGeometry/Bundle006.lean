module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CechDR GlobalTheory.HodgeCoh
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PD

section Hmap

variable {k : Type} [Field k] {M M' : Type} [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']

def Cx.hmap (K : Cx k M) (L : Cx k M') (f : M →ₗ[k] M') (hf : IsMap K L f) (n : ℤ) : K.H n →ₗ[k] L.H n :=
  Submodule.mapQ _ _ ((f.restrict (p := K.Z n) (q := L.Z n) fun a ha => by
      refine ⟨(hf n a ha.1).1, ?_⟩
      change L.D (f a) = 0
      rw [← (hf n a ha.1).2]
      have : K.D a = 0 := ha.2
      rw [this, map_zero]))
    (by
      rintro ⟨a, ha⟩ hb
      obtain ⟨c, hc, e⟩ := hb
      refine ⟨f c, ?_, ?_⟩
      · have h1 := (hf (n - 1) c hc).1
        exact h1
      · change L.D (f c) = f a
        rw [← (hf (n - 1) c hc).2, e]; rfl)

end Hmap

section Pull

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {E E' : Type} [AddCommGroup E] [Module k E]
  [AddCommGroup E'] [Module k E']

def sortSign (τ : κ → ι) (s : Finset κ) : ℤ := ∏ a ∈ s, ∏ b ∈ s, if a < b ∧ τ b < τ a then -1 else 1


open Classical in
def pullC (τ : κ → ι) (φ : E →ₗ[k] E') : (Finset ι → E) →ₗ[k] (Finset κ → E') where
  toFun c s := if Set.InjOn τ s then sortSign τ s • φ (c (s.image τ)) else 0
  map_add' a b := by
    funext s
    by_cases h : Set.InjOn τ s <;> simp [h, smul_add]
  map_smul' r a := by
    funext s
    by_cases h : Set.InjOn τ s <;> simp [h, smul_comm (sortSign τ s) r]

end Pull

section Rat

variable (k : Type) [Field k] {K K' : Type} [Field K] [Field K'] [Algebra k K] [Algebra k K']

def IsDRMap (ψ : K →ₐ[k] K') (φ : DR k K →ₗ[k] DR k K') : Prop :=
  ∀ (q : ℕ) (b : K) (v : Fin q → K), φ (b • ExteriorAlgebra.ιMulti K q fun j => D k K (v j)) =
    ψ b • ExteriorAlgebra.ιMulti K' q fun j => D k K' (ψ (v j))

end Rat

end GlobalTheory.PD
end
end

section

noncomputable section

namespace GlobalTheory.ThetaExh

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def RowSize : Prop := ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ → ∀ w, IsSplitPl H w →
  A.unr (A.locW i σ w) → ∀ α ∈ A.frobEig (A.locW i σ w),
    ‖α‖ < ((normV w : ℕ) : ℝ) ^ (((R.t : ℝ) - 1) / 2)

def RowSizeLe : Prop := ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ → ∀ w, IsSplitPl H w →
  A.unr (A.locW i σ w) → ∀ α ∈ A.frobEig (A.locW i σ w),
    ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((R.r : ℝ) - 1) / 2)

def HeckeSplitOne : Prop := ∀ χ χ' : A.CG 1,
  (∀ᶠ w in Filter.cofinite, IsSplitPl H w → A.locG χ w = A.locG χ' w) → χ = χ'

def Tempered : Prop := ∀ (a : ℕ) (π : A.CG a), A.csd π → A.ralg π → ∀ w, A.tempered (A.locG π w)

def ThetaOne : Prop := ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ → ∃ P, thetaOf N A i σ P

def Pairs (i : N.Loc) (σ : what₂.FT) (P : A.AV i) : Prop :=
  ∃ f ∈ what₂.isot (N.j i) σ, ∃ F ∈ A.typeV i P, inner ℂ F (what₂.thetaT (N.mu i) (N.j i) f) ≠ 0

def HoweUp (i : N.Loc) : Prop := ∀ σ P P', Pairs N A i σ P → Pairs N A i σ P' → P = P'

def TypeOrth (i : N.Loc) : Prop := ∀ P P', P ≠ P' → A.typeV i P ⟂ A.typeV i P'

def PartOrth (i : N.Loc) : Prop := ∀ σ σ', σ ≠ σ' → what₂.isot (N.j i) σ ⟂ what₂.isot (N.j i) σ'

def liftPar (i : N.Loc) (w : PlE H) (a : A.LP w) : A.LP w :=
  A.lpChar (A.lpSum a (spehLoc N A (muPart N A i) w)) (A.locG A.etaTinv w)

def SplitLift (i : N.Loc) : Prop := ∀ σ P, thetaOf N A i σ P → ∀ w, IsSplitPl H w →
  A.locV i P w = liftPar N A i w (A.locW i σ w)

def ParamLaws : Prop := ∀ w : PlE H,
  (∀ a b χ : A.LP w, A.lpDim χ = 1 → A.lpChar (A.lpSum a b) χ = A.lpSum (A.lpChar a χ) (A.lpChar b χ)) ∧
  (∀ χ : A.LP w, A.lpDim χ = 1 → A.lpChar (A.lpZero w) χ = A.lpZero w) ∧
  (∀ (a χ : A.LP w) (s : ℝ), A.lpDim χ = 1 → A.lpChar (A.lpTw a s) χ = A.lpTw (A.lpChar a χ) s) ∧
  (∀ a b χ : A.LP w, A.lpDim χ = 1 → A.lpChar a χ = A.lpChar b χ → a = b) ∧
  (∀ a b c : A.LP w, A.lpSum a c = A.lpSum b c → a = b)

def PtLocal (i : N.Loc) : Prop := ∀ (P : A.AV i) (x : N.X i),
  (∀ w, SplitOut N i w → ∃ p : Polynomial (N.O i),
    p.map (iotaO N A i) = galPol A (A.lpTw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2)) ∧
    p.map (IsLocalRing.residue (N.O i)) = (heckePol N i x w).map (IsLocalRing.residue (N.O i))) →
  ∃ y, A.ptV i P = some y

def PtOfLoc (i : N.Loc) : Prop := ∀ (P P' : A.AV i) (x : N.X i), A.ptV i P' = some x →
  (∀ w, SplitOut N i w → A.locV i P w = A.locV i P' w) → A.ptV i P = some x

def LocOfPt (i : N.Loc) : Prop := ∀ (P P' : A.AV i) (x : N.X i), A.ptV i P = some x →
  A.ptV i P' = some x → ∀ w, IsSplitPl H w → A.locV i P w = A.locV i P' w

def LiftParam (i : N.Loc) : Prop := ∀ σ P, thetaOf N A i σ P → ∃ Sig, HasParamW N A i σ Sig ∧
  IsBCV N A i P (twistIso N A (Sig ++ [muPart N A i]) A.etaTinv)

def TypePlSplit : Prop := ∀ k v, IsSplitPl H (A.plGw k v)

def DownMem (i : N.Loc) : Prop := ∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig →
  (eigC N A i x).map (what₂.thetaP (N.mu i) (N.j i)) ≤ MjSig N A i Sig

def GoodPart (i : N.Loc) : Prop :=
  goodPartM N A i = ⨆ x ∈ ZgoodN N A i, ⨆ Sig ∈ {Sig | HasParamX N A i x Sig}, MjSig N A i Sig

end GlobalTheory.ThetaExh
end
end
