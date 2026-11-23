module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.SplitRead

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.RowTie GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure Irr (n : ℕ) : Type 1 where

  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]

  π : Representation ℂ (GL (Fin n) k) V
  smooth : IsSmooth π
  irr : π.IsIrreducible

attribute [instance] Irr.acg Irr.mod


variable {k} in
def Irr.ofDet (n : ℕ) (χ : kˣ →* ℂˣ) (h : IsSmoothChar χ) : Irr k n where
  V := ℂ
  π := detRep (Fin n) χ
  smooth := (isSmooth_ofChar_iff _).2 h.detChar
  irr := isIrreducible_ofChar _


instance (n : ℕ) : Inhabited (Irr k n) := ⟨Irr.ofDet n 1 (isSmoothChar_of_isUnram fun _ _ => rfl)⟩


variable {k} in
@[reducible] def Irr.toIrrRep {n : ℕ} (π : Irr k n) : IrrRep (GL (Fin n) k) := ⟨π.V, π.π, π.smooth, π.irr⟩


variable {k} in
@[reducible] def Irr.ofIrrRep {n : ℕ} (σ : IrrRep (GL (Fin n) k)) : Irr k n := ⟨σ.V, σ.ρ, σ.smooth, σ.irr⟩




def TameSplit : Prop := ∀ (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), IsSmoothChar χ → IsTame χ →
  ¬ IsUnram χ → v ≠ 0 → IsParahoricVec χ π.π v →
  ∃ (π₁ : Irr k r) (π₂ : Irr k t), IsSpherical π₁.π ∧ IsSpherical π₂.π ∧
    Nonempty (π.π.Equiv (prod₂ π₁.π (twist π₂.π (detChar (Fin t) χ))))

variable {k} {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def speh (a : WD h) (d : ℕ) : WD h :=
  (List.range d).foldr (fun j acc => (a.lpTw (((d : ℝ) - 1) / 2 - j)).lpSum acc) (WD.lpZero (h := h))

structure RecLaws (rc : ∀ n, Irr k n → WD h) : Prop where
  dim : ∀ n π, (rc n π).lpDim = n
  iso : ∀ n (π π' : Irr k n), rc n π = rc n π' ↔ Nonempty (π.π.Equiv π'.π)
  prod : ∀ r t (σ : Irr k r) (τ : Irr k t) (π : Irr k (r + t)), Nonempty (π.π.Equiv (prod₂ σ.π τ.π)) →
    rc (r + t) π = (rc r σ).lpSum (rc t τ)
  det : ∀ t (χ : kˣ →* ℂˣ) (c : Irr k 1) (τ : Irr k t), Nonempty (c.π.Equiv (detRep (Fin 1) χ)) →
    Nonempty (τ.π.Equiv (detRep (Fin t) χ)) → rc t τ = speh (rc 1 c) t
  twist : ∀ n (χ : kˣ →* ℂˣ) (c : Irr k 1) (π π' : Irr k n), Nonempty (c.π.Equiv (detRep (Fin 1) χ)) →
    Nonempty (π'.π.Equiv (twist π.π (detChar (Fin n) χ))) → rc n π' = (rc n π).lpChar (rc 1 c)
  sph : ∀ n (π : Irr k n), (rc n π).unr ↔ IsSpherical π.π
  sat : ∀ n (π : Irr k n) (α : Fin n → ℂˣ), HasSatake π.π α →
    (rc n π).frobEig = Finset.univ.val.map fun i => ((α i)⁻¹ : ℂˣ).1

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

structure ReadAt (T : WDTie N A) (i : N.Loc) (w : PlE H) : Type 1 where

  rc : ∀ n, Irr (w.adicCompletion H.E) n → WD (E := H.E) (A := N.plOm.1 w) (w := w) (N.plOm.2 w)

  row : what₂.FT → Irr (w.adicCompletion H.E) R.r

  rep : A.AV i → Irr (w.adicCompletion H.E) (R.r + R.t)

  mu : (w.adicCompletion H.E)ˣ →* ℂˣ
  eta : (w.adicCompletion H.E)ˣ →* ℂˣ
  mu_ok : IsSmoothChar mu ∧ IsUnitaryChar mu
  eta_ok : IsSmoothChar eta ∧ IsUnram eta
  locW : ∀ σ, what₂.isot (N.j i) σ ≠ ⊥ → T.e w (A.locW i σ w) = rc _ (row σ)
  locV : ∀ P, T.e w (A.locV i P w) = rc _ (rep P)
  locMu : ∀ c : Irr (w.adicCompletion H.E) 1, Nonempty (c.π.Equiv (detRep (Fin 1) mu)) →
    T.e w (A.locG (A.muC i) w) = rc 1 c
  locEta : ∀ c : Irr (w.adicCompletion H.E) 1, Nonempty (c.π.Equiv (detRep (Fin 1) eta⁻¹)) →
    T.e w (A.locG A.etaTinv w) = rc 1 c

abbrev Reading (T : WDTie N A) : Type 1 := ∀ (i : N.Loc) (w : PlE H), IsSplitPl H w → ReadAt T i w

variable {T : WDTie N A} (S : Reading T)

def Laws : Prop := ∀ i w hw, RecLaws (S i w hw).rc

def RowUnit : Prop := ∀ i w hw σ, what₂.isot (N.j i) σ ≠ ⊥ → IsUnitarisable ((S i w hw).row σ).π

def PairRead : Prop := ∀ i w hw σ P, Pairs N A i σ P →
  ThetaPair (S i w hw).mu ((S i w hw).row σ).π
    (twist ((S i w hw).rep P).π (detChar (Fin (R.r + R.t)) (S i w hw).eta))

def TypeTame (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w) : Prop :=
  IsTame (S i w hw).mu ∧ ¬ IsUnram (S i w hw).mu ∧
    ∀ P, ∃ v, v ≠ 0 ∧ IsParahoricVec (S i w hw).mu ((S i w hw).rep P).π v

def TameSplitAll (E : Type) [Field E] [NumberField E] : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), TameSplit (w.adicCompletion E)

end GlobalTheory.SplitRead
end
end

section

noncomputable section

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions NumberField

def MtType {D : D7} (u : D.what₂.Word) (mt : ℕ → D.Dt →* ℂˣ) : Prop :=
  letI := D.host.cmStar
  ∀ (i : ℕ) (h : i < D.R.m), (∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ mt (i + 1) k ^ n = 1) ∧
    ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hcW u τ).e ⟨i, h⟩) ∧
      ∀ z : unitary D.host.E, ((mt (i + 1) (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ

end GlobalTheory.KerJ
end
end

section

noncomputable section

namespace GlobalTheory.HTW.LJ

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual NumberField IsDedekindDomain

variable {D : D7}

section Sets

variable (D)

def c0 : ℚ := ((D.R.t : ℚ) - 1) / 2

def sz (j : ℕ) (ρ : D.what₂.Tau) : ℚ :=
  if h : j - 1 < D.R.m then (D.hc ρ).e ⟨j - 1, h⟩ else 0

def cloudJ (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ :=
  {q | ∃ a : Fin (D.R.k - 1), q = sz D j ρ + (D.hc ρ).v a + c0 D}

def lowJ (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ :=
  {q | ∃ a : Fin D.R.m, q = sz D j ρ - (D.hc ρ).b a + c0 D}

def blockJ : Set ℚ := {q | ∃ c : ℕ, c < D.R.t ∧ q = c}

def Jp (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ := cloudJ D j ρ ∪ lowJ D j ρ ∪ blockJ D

def refl (q : ℚ) : ℚ := ((D.R.t : ℚ) - 1) - q

def reflS (S : Set ℚ) : Set ℚ := {q | refl D q ∈ S}

def Jm (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ := reflS D (Jp D j ρ)

def JJ (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ := if up then Jp D j ρ else Jm D j ρ

def cloudT (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ :=
  if up then cloudJ D j ρ else reflS D (cloudJ D j ρ)

def lowT (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ :=
  if up then lowJ D j ρ else reflS D (lowJ D j ρ)

def JW (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ := cloudT D up j ρ ∪ lowT D up j ρ

def dualS (S : Set ℚ) : Set ℚ := {q | -q - 1 ∈ S}

end Sets

section Emb

variable (D)

def PlaceOf (ρ : D.what₂.Tau) (g : D.R.GG) : Prop :=
  ((D.eTau ρ : D.R.Psi) : D.R.GG) = g ∨
    ((D.eTau ρ : D.R.Psi) : D.R.GG) * D.R.cc = g

def TypeU (ep : Bool) (g : D.R.GG) : Prop := (g ∈ D.R.Psi ↔ ep = true)

def ReadAt (i : D.nd.Loc) (τ₀ : D.host.E →+* Qbar (D.nd.l i)) (g : D.R.GG)
    (ρ : D.what₂.Tau) : Prop :=
  (D.naut.iotaQC i).toRingHom.comp τ₀ = D.host.emb g ∧ PlaceOf D ρ g

variable {D}

def gEmb {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) :
    D.host.E →+* Qbar (D.nd.l i) :=
  (C.LL.1.val.toRingHom).comp (τ.toRingHom.comp (Br.cEw D.nbr i w hw))

end Emb

section Stmt

variable (D)


open Classical in
def hodgeTateJumpsAtModulesForSign (ep : Bool) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1),
      ∃ (g : D.R.GG) (ρ : D.what₂.Tau), ReadAt D i (gEmb C τ) g ρ ∧
        (∀ (x : D.nd.X i) (a : ℤ),
          (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) τ a ↔
            (a : ℚ) ∈ JJ D (decide (TypeU D ep g)) (D.nd.j i) ρ) ∧
          multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) τ a =
            (if (a : ℚ) ∈ JJ D (decide (TypeU D ep g)) (D.nd.j i) ρ then 1 else 0) ∧
          (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) τ a ↔
            (a : ℚ) ∈ dualS (JJ D (decide (TypeU D ep g)) (D.nd.j i) ρ)) ∧
          multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) τ a =
            (if (a : ℚ) ∈ dualS (JJ D (decide (TypeU D ep g)) (D.nd.j i) ρ) then 1 else 0)) ∧
        ∀ (ρπ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), π ∈ D.nd.Z i →
          TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρπ π → ∀ a : ℤ,
          (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ π))) τ a ↔
            (a : ℚ) ∈ JW D (decide (TypeU D ep g)) (D.nd.j i) ρ) ∧
          multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ π))) τ a =
            (if (a : ℚ) ∈ JW D (decide (TypeU D ep g)) (D.nd.j i) ρ then 1 else 0) ∧
          (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρπ π))) τ a ↔
            (a : ℚ) ∈ dualS (JW D (decide (TypeU D ep g)) (D.nd.j i) ρ)) ∧
          multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρπ π))) τ a =
            (if (a : ℚ) ∈ dualS (JW D (decide (TypeU D ep g)) (D.nd.j i) ρ) then 1 else 0)

def ConclusionJa : Prop := ∃ ep : Bool, hodgeTateJumpsAtModulesForSign D ep

end Stmt

end GlobalTheory.HTW.LJ
end
end

section

noncomputable section

namespace GlobalTheory.BlockWindow

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain

def JointTB (D : D7) (HW : HWOf D.loc) (_F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (M0 h0 cB : ℕ) : Prop :=
  D.nd.l i ≠ 2 ∧ ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    Br.inert D.nbr i w hw = IK (D.nbr i w hw).Kw ∧ (D.nbr i w hw).Kw.1 ≤ Ks (D.nbr i w hw).Kw 1 ∧
    ∀ (CL : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ CL.1) (hs : Good (D.nbr i w hw).Kw 1 CL)
      (Y : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥CL.1 ↥(OL CL)),
      IsCrys (Br.PD D.loc D.nbr i w hw) Y.ρ →
      (∀ τ, JumpsInV (Br.PD D.loc D.nbr i w hw) Y.ρ τ
        {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ a}) →
      (∀ a ∈ LocalSituation.Jset (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs) Y,
        -(M0 : ℤ) ≤ a ∧ a ≤ h0) ∧
      ∀ e < D.R.t,
        LocalSituation.cTBY (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs) Y M0 h0 e ≤ cB

def JumpWindow (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
    (h₁ : ℕ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (CL : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ CL.1) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥CL.1),
    ∃ U : Finset ℤ, U.card ≤ D.R.nV ∧ (∀ u ∈ U, -(h₁ : ℤ) ≤ u ∧ u + 1 ≤ h₁) ∧
      ∀ a, IsJumpV (Br.PD D.loc D.nbr i w hw)
        (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ a → a ∈ U

theorem JointTB.mono {D : D7} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW} {i : D.nd.Loc}
    {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))} {π : D.nd.X i} {M0 h0 cB cB' : ℕ} (hle : cB ≤ cB')
    (h : JointTB D HW F i r π M0 h0 cB) : JointTB D HW F i r π M0 h0 cB' := by
  refine ⟨h.1, fun w hw => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h.2 w hw
  refine ⟨h1, h2, fun CL hL hs Y hc hY => ?_⟩
  obtain ⟨k1, k2⟩ := h3 CL hL hs Y hc hY
  exact ⟨k1, fun e he => (k2 e he).trans hle⟩

end GlobalTheory.BlockWindow

end
end
