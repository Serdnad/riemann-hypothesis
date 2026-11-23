module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle384
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
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
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle007
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)



def reG {X : HidaSetting D} (G : GoodOp X) : GoodOp (reX Z X) where
  Rg := (G.Rg)
  Rg_spec := (G.Rg_spec)



def eEECre {X : HidaSetting D} (G : GoodOp X) : EEC X G ≃ₗᵢ[ℂ] EEC (reX Z X) (reG Z G) := (LinearIsometryEquiv.refl ℂ ↥(EEC X G))



theorem measTie_reX {X : HidaSetting D} {hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I} (h : X.MeasTie hb) :
    (reX Z X).MeasTie hb := (h)



theorem measCompat_reX {X : HidaSetting D} {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ}
    (h : Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ) : Formalism.L2.SG.MassDataConc.MeasCompatψ (reX Z X) ψ := (h)



theorem locCompat_reX {X : HidaSetting D} {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ} {w : D.what₂.Word}
    (h : Formalism.L2.SG.LocVol.LocCompatX X ψ w) : Formalism.L2.SG.LocVol.LocCompatX (reX Z X) ψ (wd Z w) := (h)

theorem colDict_congr {X : HidaSetting D} {u : D.what₂.Word} {F : Forms0 D u} (T : Transport X u F) (hK : X.LevelSubgroupCharacter)
    (L : Cu X u hK →ₗ[ℂ] ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)) (hL : ∀ x, L x = colDictL X T hK x) :
    (ColDictInto X T hK → ∀ x, L x ∈ (D.mem u).A.Mu0) ∧
    (ColDictBij X T hK → Function.Injective L ∧ ∀ φ ∈ (D.mem u).A.Mu0, ∃ x, L x = φ) ∧
    ∀ {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (hinj : Function.Injective (sharp hK cs)),
      ColDictIsom X T hK cs hinj → ∀ x y : ColT hinj, inner ℂ x y = (D.fm u).ipC 0 (L (toCu X hK x)) (L (toCu X hK y)) := by
  obtain rfl : L = colDictL X T hK := LinearMap.ext hL
  exact ⟨fun h => h, fun h => h, fun _ _ h => h⟩

section Col



variable {X : HidaSetting D} {u : D.what₂.Word} {F : Forms0 D u} {F' : Forms0 (reD D Z) u} (T : Transport X u F)
    (hy : F'.cls0.y = F.cls0.y) (he : F'.val0.eY = F.val0.eY) (Y : Full X)



private theorem colDict_congr_reTr :
    (ColDictInto X T Y.hK → ColDictInto (reX Z X) (reTr Z T hy he) (reY Z Y).hK) ∧
    (ColDictBij X T Y.hK → ColDictBij (reX Z X) (reTr Z T hy he) (reY Z Y).hK) ∧
    ∀ (hF : FinX Y) (hF' : FinX (reY Z Y)),
      ColDictIsom X T Y.hK (Y.cs u) (hF.shInj u) →
      ColDictIsom (reX Z X) (reTr Z T hy he) (reY Z Y).hK ((reY Z Y).cs u) (hF'.shInj u) := by
  let L' := @colDictL (reD D Z) (reX Z X) u F' (@reTr D Z X u F F' T hy he) Y.hK
  -- Elaborate in the original indices of each term and let the kernel check the
  -- definitional equalities across reD, as in eCure.
  let L : Cu X u Y.hK →ₗ[ℂ] ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) := by
    run_tac
      let value ← Lean.Elab.Tactic.getFVarId (Lean.mkIdent `L')
      Lean.Elab.Tactic.liftMetaFinishingTactic (·.assign (.fvar value))
  have hL : ∀ x, L x = colDictL X T Y.hK x :=
    @colDictL_reTr D Z X u F F' T hy he Y.hK
  have h := colDict_congr T Y.hK L hL
  have result := And.intro h.1 (And.intro h.2.1
    (fun (hF : FinX Y) (_ : FinX (reY Z Y)) => h.2.2 (Y.cs u) (hF.shInj u)))
  run_tac
    let proof ← Lean.Elab.Tactic.getFVarId (Lean.mkIdent `result)
    Lean.Elab.Tactic.liftMetaFinishingTactic (·.assign (.fvar proof))

theorem colDictInto_reTr (h : ColDictInto X T Y.hK) : ColDictInto (reX Z X) (reTr Z T hy he) (reY Z Y).hK :=
  (colDict_congr_reTr Z T hy he Y).1 h



theorem colDictBij_reTr (h : ColDictBij X T Y.hK) : ColDictBij (reX Z X) (reTr Z T hy he) (reY Z Y).hK :=
  (colDict_congr_reTr Z T hy he Y).2.1 h



theorem colDictIsom_reTr (hF : FinX Y) (hF' : FinX (reY Z Y)) (h : ColDictIsom X T Y.hK (Y.cs u) (hF.shInj u)) :
    ColDictIsom (reX Z X) (reTr Z T hy he) (reY Z Y).hK ((reY Z Y).cs u) (hF'.shInj u) :=
  (colDict_congr_reTr Z T hy he Y).2.2 hF hF' h

end Col



theorem levelMatch_reTr {X : HidaSetting D} {u : D.what₂.Word} {F : Forms0 D u} {F' : Forms0 (reD D Z) u} (T : Transport X u F)
    (hl : F'.cls0.lev = F.cls0.lev) (hy : F'.cls0.y = F.cls0.y) (he : F'.val0.eY = F.val0.eY) (Y : Full X)
    (h : LevelMatch X T Y.hK) : LevelMatch (reX Z X) (reTr Z T hy he) (reY Z Y).hK := by
  unfold LevelMatch
  rw [hl]
  exact (h)

end GlobalTheory.Mem.SRe

end
end

section

noncomputable section

namespace GlobalTheory.Mem.Top.V4.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem ev_imp {p q : Ctx → Prop} (hp : Ev p) (h : ∀ K, p K → q K) : Ev q := by
  obtain ⟨ε0, h0, H⟩ := hp
  refine ⟨ε0, h0, fun eps C8 a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, H⟩ := H eps C8 a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, H⟩ := H C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, H⟩ := H cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, H⟩ := H ch hch
  exact ⟨x0, fun K d1 d2 d3 d4 d5 => h K (H K d1 d2 d3 d4 d5)⟩

theorem mem_iff {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {Wt : Set X.B.places.Pl} {xi : X.C.Tup → HChar X.B.host.E}
    (h : MuIsW X f T Wt xi) (w : X.B.places.Pl) : w ∈ Wt ↔ X.W.muAt w ≠ X.C.mu0 := by
  refine ⟨fun hw he => ?_, fun hw => by_contra fun hn => hw (h.off w hn)⟩
  have h1 := h.tw w
  rw [← h.on w hw, he, h.mu0] at h1
  exact (TwFin.tw_fin X.B f T).2.1 w h1.symm

variable (hH : DC.HostExQ) (hLP : LevelPrime) (hSP : SmallPrimeOne) (h2b : StandardLattice.SiegelMassRatioCM)






end GlobalTheory.Mem.Top.V4.Model

end
end

section

noncomputable section

namespace GlobalTheory.Mem.Top.GroupRetwisting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

abbrev BaseP : Type 1 := ∀ B : Base, Fr B.toPre → Prop

structure BaseCond (KP : BaseP) : Prop where
  ex : EvG fun K => ∃ (P : Pre) (f₀ : Fr P), K.Over P ∧ ∀ (S₁ : IntermediateField ℚ ℂ → Finset ℂ)
    (S₂ : IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → Finset ℂ), (∀ F, ∀ z ∈ S₁ F, IsAlgebraic ℚ z) →
    (∀ F F₀, ∀ z ∈ S₂ F F₀, IsAlgebraic ℚ z) →
    ∃ (B : Base) (f : Fr B.toPre), B.toPre = P ∧ HEq f f₀ ∧ KP B f ∧ Has₂ B (S₁ B.KsC) (S₂ B.KsC B.fixedCoefficientFieldInComplex)
  enl : ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre), Enl B B' → HEq f' f → KP B f → KP B' f'

def RetwistG (Q Q' : V4.Slot) : Prop :=
  EvG fun K => ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T), Q K X f T c → ExportAt X.toD7 c.O.nch c.O.xd →
    ∀ (A : ℕ → Finset ℕ) (S₂ : ∀ B : Pre, Fr B → Set (HChar B.host.E) → Finset ℂ), (∀ B f Ξ, ∀ z ∈ S₂ B f Ξ, IsAlgebraic ℚ z) →
      ∃ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B'), Enl X.B B' ∧ HEq f' f ∧ T'.pl = T.pl ∧ T'.Avoids A ∧
        (∀ z ∈ S₂ B'.toPre f' (T'.set f'), ∃ x : B'.LL, B'.embLL x = z) ∧
        ∀ (C : Cols B') (W : RowsRest B' C) (V : DivStage B' C W) (S : SStage B' C W) (N : NStage B' C W) (G : GJStage B' C)
          (c' : V4.Core K ⟨B', C, W, V, S, N, G⟩ f' T'), Q K ⟨B', C, W, V, S, N, G⟩ f' T' c' →
          DQ.TwAllAt (assemble B' C W V S N G) c'.O.nch c'.O.xd ∧ Q' K ⟨B', C, W, V, S, N, G⟩ f' T' c'

def FromCoreAt (Q : V4.Slot) (K : Ctx) (D : D7) (Y : Lay D) : Prop :=
  ∃ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T), Q K X f T c ∧
    (⟨D, layObj Y⟩ : Σ D : D7, Obj2 D) = ⟨X.toD7, c.O⟩

def Forced (K : Ctx) (B : Base) (T : TwDat B) : Prop :=
  ∀ p : ℕ, p.Prime → ((∃ i, p = B.host.g i) ∨ p = B.host.d ∨ (p : ℝ) ≤ K.s.X'' B.R.n) → p ∈ T.pl

abbrev AtP : Type 1 := ∀ (_ : Ctx) (B : Base), Fr B.toPre → TwDat B → Prop

def Step (KP : BaseP) (p q : AtP) : Prop := EvLgG fun K B f T => KP B f → Forced K B T → p K B f T → q K B f T

def HasCore (Q : V4.Slot) : AtP := fun K B f T =>
  ∃ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c

def FirstG (KP : BaseP) (Q : V4.Slot) : Prop := Step KP (fun _ B _ T => T = TwDat.untw B T.pl) (HasCore Q)

def ExportF (KP : BaseP) (Q : V4.Slot) : Prop :=
  EvLgG fun K B f T => KP B f → T = TwDat.untw B T.pl → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W)
    (N : NStage B C W) (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c →
    ExportAt (assemble B C W V S N G) c.O.nch c.O.xd

def Pass (KP : BaseP) (Q : V4.Slot) (r : AtP) : Prop :=
  EvLgG fun K B f T => KP B f → T = TwDat.untw B T.pl → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W)
    (N : NStage B C W) (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c →
    ExportAt (assemble B C W V S N G) c.O.nch c.O.xd →
    ∀ (A : ℕ → Finset ℕ) (S₂ : ∀ P : Pre, Fr P → Set (HChar P.host.E) → Finset ℂ), (∀ P g Ξ, ∀ z ∈ S₂ P g Ξ, IsAlgebraic ℚ z) →
      ∃ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B'), Enl B B' ∧ HEq f' f ∧ T'.pl = T.pl ∧ T'.Avoids A ∧
        (∀ z ∈ S₂ B'.toPre f' (T'.set f'), ∃ x : B'.LL, B'.embLL x = z) ∧ r K B' f' T'

def SecondG (KP : BaseP) (Q Q' : V4.Slot) : Prop :=
  Pass KP Q (HasCore fun K X f T c => Q K X f T c ∧ DQ.TwAllAt X.toD7 c.O.nch c.O.xd ∧ Q' K X f T c)

def LargeBaseConditionG (KP : BaseP) (Q R : V4.Slot) : Prop :=
  EvLgG fun K B f T => KP B f → ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c → R K ⟨B, C, W, V, S, N, G⟩ f T c

theorem evG_all {p : Ctx → Prop} (h : ∀ K, p K) : EvG p := evG_good.imp fun K _ _ _ _ _ => h K

theorem baseCond_of {KP : BaseP} (h : V4.KsCond KP) {PP : ∀ P : Pre, Fr P → Prop}
    (hP : EvG fun K => ∃ (P : Pre) (f : Fr P), K.Over P ∧ PP P f) : BaseCond fun B f => KP B f ∧ PP B.toPre f := by
  refine ⟨((evG_of_ev h.ex).inter hP).imp ?_, fun B B' f f' e hf hk => ⟨h.enl B B' f f' e hf hk.1, ?_⟩⟩
  · rintro K _ _ _ _ ⟨hk, P, f₀, hO, hp⟩
    obtain ⟨B₀, rfl, -⟩ := BaseExt.exists_base P ∅ ∅ ∅ (by simp) (by simp) (by simp)
    refine ⟨_, f₀, hO, fun S₁ S₂ a₁ a₂ => ?_⟩
    obtain ⟨B, f, e, hf, k, H⟩ := hk B₀ f₀ S₁ S₂ hO a₁ a₂
    refine ⟨B, f, e, hf, ⟨k, ?_⟩, H⟩
    generalize B₀.toPre = P₀ at *
    subst e
    cases hf
    exact hp
  · have e1 := e.1
    have h2 := hk.2
    clear hk e
    generalize B.toPre = P at *
    generalize B'.toPre = P' at *
    subst e1
    cases hf
    exact h2

theorem lg_forced (K : Ctx) : large₂ K fun B _ T => Forced K B T := by
  have h : ∀ P : Pre, ∃ S : Finset ℕ,
      ∀ p : ℕ, p.Prime → ((∃ i, p = P.host.g i) ∨ p = P.host.d ∨ (p : ℝ) ≤ K.s.X'' P.R.n) → p ∈ S := fun P => by
    refine ⟨{P.host.g 0, P.host.g 1, P.host.d} ∪ Finset.range (⌊K.s.X'' P.R.n⌋₊ + 1), ?_⟩
    rintro p - (⟨i, rfl⟩ | rfl | h)
    · fin_cases i <;> simp
    · simp
    · exact Finset.mem_union_right _ (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor h)))
  choose S hS using h
  exact ⟨fun _ _ _ => ∅, fun P _ _ _ => S P, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
    fun B _ _ _ _ h _ p hp h' => h (hS _ p hp h')⟩

theorem lg_all (K : Ctx) {p : ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : ∀ B f T, K.Over B.toPre → p B f T) : large₂ K p :=
  (lg_forced K).imp fun B f T hO _ => h B f T hO

section Steps
variable {KP : BaseP} {p q r : AtP}

theorem Step.of_evG (h : EvG fun K => ∀ B f T, K.Over B.toPre → KP B f → Forced K B T → p K B f T → q K B f T) : Step KP p q :=
  EvG.imp h fun K _ _ _ _ H => lg_all K H

theorem Step.of_all (h : ∀ K B f T, K.Over B.toPre → KP B f → Forced K B T → p K B f T → q K B f T) : Step KP p q :=
  Step.of_evG (evG_all h)

theorem Step.trans (h : Step KP p q) (h' : Step KP q r) : Step KP p r :=
  (EvG.inter h h').imp fun _ _ _ _ _ H => (H.1.inter H.2).imp fun _ _ _ _ G a b c => G.2 a b (G.1 a b c)

theorem Step.and (h : Step KP p q) (h' : Step KP p r) : Step KP p fun K B f T => q K B f T ∧ r K B f T :=
  (EvG.inter h h').imp fun _ _ _ _ _ H => (H.1.inter H.2).imp fun _ _ _ _ G a b c => ⟨G.1 a b c, G.2 a b c⟩

theorem Step.of_evLgG (h : EvLgG q) : Step KP p q := EvG.imp h fun _ _ _ _ _ H => H.imp fun _ _ _ _ G _ _ _ => G

end Steps

section Tests
variable (hH : DC.HostExQ) (hLP : LevelPrime) (h2b : StandardLattice.SiegelMassRatioCM)
include hH hLP h2b

end Tests

end GlobalTheory.Mem.Top.GroupRetwisting

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.Model

theorem mem_iff_trace {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] (X : Finset (G → K))
    (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (χ : G → K) :
    χ ∈ X ↔ IsAbsIrrChar χ ∧ ∑ g, (idemOf X).coeff g * χ g = χ 1 := by
  classical
  have hN : ((Fintype.card G : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have key : IsAbsIrrChar χ → χ 1 ≠ 0 ∧ ∑ g, (idemOf X).coeff g * χ g = if χ ∈ X then χ 1 else 0 := fun h => by
    have h1 : χ 1 ≠ 0 := by
      obtain ⟨n, ρ, hρ, hχ⟩ := h
      intro e
      have h2 := hχ 1
      rw [e, map_zero, Representation.char_one, Nat.cast_eq_zero, Module.finrank_zero_iff] at h2
      exact (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
    refine ⟨h1, ?_⟩
    simp only [coeff_idemOf, Finset.sum_mul]
    rw [Finset.sum_comm, ← Finset.sum_ite_eq' X χ fun _ => χ 1]
    refine Finset.sum_congr rfl fun ψ hψ => ?_
    have h3 := conv_char (hX ψ hψ) h 1
    simp only [mul_one] at h3
    apply mul_right_cancel₀ h1
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [h3]
    split_ifs with e
    · rw [e]; field_simp
    · simp
  refine ⟨fun h => ⟨hX χ h, by rw [(key (hX χ h)).2, if_pos h]⟩, fun ⟨h, e⟩ => ?_⟩
  by_contra hn
  rw [(key h).2, if_neg hn] at e
  exact (key h).1 e.symm

section Base

variable {B : Base} {px : PreX B.toPre} (I : ColIn B px)

theorem mem_vGs_iff (h : I.Ok) (P : HeightOneSpectrum (𝓞 B.fields.E)) : P ∈ (B.primes px).vGs ↔ ∃ k, I.C.P.Div k P := by
  classical
  unfold Formalism.L2.Col.Primes.vGs
  rw [Finset.mem_union, h.pibar, h.pibar, Fin.exists_fin_two]

theorem exists_under_of_selHalf (h : SelHalf I) (p : ℕ) (hp : p.Prime) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 B.host.K), ∀ a, ∀ P : HeightOneSpectrum (𝓞 B.host.E), P ∈ I.Q a →
      ((p : ℕ) : 𝓞 B.host.E) ∈ P.asIdeal → P.under (𝓞 B.host.K) = 𝔭 := by
  by_cases e : ∃ a, ∃ P : HeightOneSpectrum (𝓞 B.host.E), P ∈ I.Q a ∧ ((p : ℕ) : 𝓞 B.host.E) ∈ P.asIdeal
  · obtain ⟨b, P', hb, hP'⟩ := e
    exact ⟨P'.under (𝓞 B.host.K), fun a P ha hP => HeightOneSpectrum.ext (h a b P ha P' hb ⟨p, hp, hP, hP'⟩)⟩
  · exact ⟨I.C.P.pb 0, fun a P ha hP => absurd ⟨a, P, ha, hP⟩ e⟩

end Base

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px)

theorem grpAt_iff (h : I.Ok) : GrpAt X I ↔ ∀ k v, I.C.P.Div k (X.toD7.naut.plGw k v) := by
  classical
  refine ⟨fun ⟨⟨plg, hp⟩, _, _⟩ k v => (hp ⟨k, v⟩).1 ▸ (hp ⟨k, v⟩).2, fun H => ?_⟩
  obtain ⟨hc, hi⟩ := GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent X.toD7
  refine ⟨?_, hi, hc⟩
  have hPr := (base_fields_primes_ok X.B px).2.1
  let φ : (Σ k : Fin 2, X.toD7.nd.PlG k) → (X.B.primes px).vGs :=
    fun kv => ⟨X.toD7.naut.plGw kv.1 kv.2, (mem_vGs_iff I h _).2 ⟨kv.1, H _ _⟩⟩
  have hinj : Function.Injective φ := by
    rintro ⟨k, v⟩ ⟨k', v'⟩ e
    have e' : X.toD7.naut.plGw k v = X.toD7.naut.plGw k' v' := congrArg Subtype.val e
    have hk : k = k' := by
      have a := hPr.vG_norm k _ ((h.pibar k _).2 (H k v))
      have b := hPr.vG_norm k' _ ((h.pibar k' _).2 (H k' v'))
      have c : (X.B.primes px).g k = (X.B.primes px).g k' := a.symm.trans ((congrArg (fun P : HeightOneSpectrum (𝓞 X.B.fields.E) => Ideal.absNorm P.asIdeal) e').trans b)
      have := hPr.g_ne
      fin_cases k <;> fin_cases k' <;> first | rfl | exact absurd c this | exact absurd c.symm this
    subst hk
    rw [X.toD7.naut.plGw_inj k e']
  have hsurj : Function.Surjective φ := by
    rintro ⟨P, hP⟩
    obtain ⟨k, hk⟩ := (mem_vGs_iff I h P).1 hP
    let ψ : X.toD7.nd.PlG k → (X.B.primes px).vG k := fun v => ⟨X.toD7.naut.plGw k v, (h.pibar k _).2 (H k v)⟩
    have hψ : Function.Bijective ψ := by
      refine (Fintype.bijective_iff_injective_and_card ψ).2 ⟨fun v v' e => X.toD7.naut.plGw_inj k (congrArg Subtype.val e), ?_⟩
      rw [X.toD7.nd.card_PlG k, Fintype.card_coe, hPr.vG_card k]
      exact (X.toD7.what₂.card_Tau).symm
    obtain ⟨v, hv⟩ := hψ.2 ⟨P, (h.pibar k P).2 hk⟩
    exact ⟨⟨k, v⟩, Subtype.ext (by have := congrArg Subtype.val hv; exact this)⟩
  exact ⟨Equiv.ofBijective φ ⟨hinj, hsurj⟩, fun kv => ⟨rfl, H _ _⟩⟩

theorem grpAt_of_grpTrue (h : I.Ok) (hN : Top.GrpTrue X.N I.C) : GrpAt X I := (grpAt_iff X I h).2 hN.pl

theorem goodSet_of_idem (eR : Gc X.B px ≃* G0g X.toD7.nd) (Xg : Finset (Gc X.B px → X.B.LL)) (hX : ∀ χ ∈ Xg, IsAbsIrrChar χ)
    (he : ∀ g, X.B.embLL ((idemOf Xg).coeff g) = X.toD7.ntypes.e0.coeff (eR g)) : GoodSet X (px := px) eR Xg := by
  refine (goodSet_iff X eR Xg).2 ⟨fun χ => ?_, he⟩

  simp only [← he, ← map_mul, ← map_sum, X.B.embLL.injective.eq_iff]
  exact mem_iff_trace Xg hX χ

end Record

end GlobalTheory.Mem.R3.Model

end
end
