module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle004
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

namespace PositivityTheory.Rg.BcB.F.LemDd

def InfUniq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : Submodule ℂ (Sm E N)) (τ : E →+* ℂ)
  (m m' : Multiset ℂ), V ≠ ⊥ → HasInfCharGL V τ m → HasInfCharGL V τ m' → m = m'

def InfParts : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N) (P : PositivityTheory.Rg.BcB.F.Pre E N)
  (τ : E →+* ℂ), t.Good → t.Untw → TreeParts t P → t.InfOf τ (∑ i, P.m i τ)

def PairNe : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (U₁ : Submodule ℂ (Sm E a))
  (U₂ : Submodule ℂ (Sm E b)) (G : PositivityTheory.Rg.BcB.E.H E a b → ℂ), G ∈ pairSpace U₁ U₂ → G ≠ 0 → U₁ ≠ ⊥ ∧ U₂ ≠ ⊥

def LemD : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N) (P : PositivityTheory.Rg.BcB.F.Pre E N)
  (τ : E →+* ℂ) (m : Multiset ℂ), t.Good → t.Untw → TreeParts t P → HasInfCharGL t.space τ m → t.space ≠ ⊥ →
    ∑ i, P.m i τ = m

theorem lemD_of (h1 : InfUniq) (h2 : InfParts) (h3 : InfTree) : LemD := by
  intro E _ _ _ N t P τ m hg hu hp hm h0
  exact h1 E N t.space τ _ _ h0 (h3 E N t τ _ (h2 E N t P τ hg hu hp)) hm

end PositivityTheory.Rg.BcB.F.LemDd

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

def parts (P : Pre E n) : List (Σ M : ℕ, Submodule ℂ (Sm E M)) := List.ofFn fun i => ⟨P.N i, P.V i⟩

def twPart (χ : HChar E) (x : Σ M : ℕ, Submodule ℂ (Sm E M)) : Σ M : ℕ, Submodule ℂ (Sm E M) :=
  ⟨x.1, x.2.map (mulChi x.1 χ).toLinearMap⟩

def IsJoin (χ₁ χ₂ : HChar E) (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n) : Prop :=
  parts D = (parts Pa).map (twPart χ₁) ++ (parts Pb).map (twPart χ₂)

def embW (a : ℕ) (w : Pl E) : GLw a w →* GA E a := (finGL E a).comp (locGL E a w)

def embT (a : ℕ) (w : Pl E) : GLw a w →* GA E a := (thetaGL a (conjAd E)).comp (embW a w)

def pairRt (a b : ℕ) (w : Pl E) : Representation ℂ (GLw a w × GLw b w) (H E a b → ℂ) :=
  (rightReg ℂ (H E a b) ℂ).comp ((embW a w).prodMap (embW b w))

def pairRtT (a b : ℕ) (w : Pl E) : Representation ℂ (GLw a w × GLw b w) (H E a b → ℂ) :=
  (rightReg ℂ (H E a b) ℂ).comp ((embT a w).prodMap (embT b w))

def IsSat2 {V : Type} [AddCommGroup V] [Module ℂ V] (w : Pl E) (ρ : Representation ℂ (GLw a w × GLw b w) V) (x : V)
    (Ba Bb : Multiset ℂˣ) : Prop :=
  x ∈ fixed ρ (K2 a b w) ∧ Ba.card = a ∧ Bb.card = b ∧ ∀ ϖ, IsUnifV E w ϖ → ∀ i ≤ a, ∀ j ≤ b,
    heckeVec ρ (K2 a b w) (fun g => Tj ℂ a (Ov E w) ϖ i g.1 * Tj ℂ b (Ov E w) ϖ j g.2) x =
      (satEig (qV E w) a Ba i * satEig (qV E w) b Bb j) • x

def ctT (h : a + b = n) (w : Pl E) (ν : (w.adicCompletion E)ˣ →* ℂˣ) (ϖ : w.adicCompletion E) (k : ℕ) :
    GLw a w × GLw b w → ℂ :=
  ctMu h w ν fun u : UL n w => Tj ℂ n (Ov E w) ϖ k u.1

def JoinEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (μ : HChar E) (e : InfinitePlace E → ℤ)
  (Pa : Pre E a) (Pb : Pre E b), IsMu μ e → a + b = n → ∃ D : Pre E n, IsJoin (μ ^ b) (μ ^ a) Pa Pb D

def JoinInf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (χ₁ χ₂ : HChar E)
  (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n), IsJoin χ₁ χ₂ Pa Pb D → ∀ τ,
  ∑ i, D.m i τ = (∑ i, Pa.m i τ).map (· + expo χ₁ τ) + (∑ i, Pb.m i τ).map (· + expo χ₂ τ)

def JoinSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (χ₁ χ₂ : HChar E)
  (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n) (w : Pl E) (Ba Bb : Multiset ℂˣ), IsJoin χ₁ χ₂ Pa Pb D →
  χ₁.UnrAt w → χ₂.UnrAt w → Pa.Sat w Ba → Pb.Sat w Bb →
  D.Sat w (Ba.map (· * χ₁.val w) + Bb.map (· * χ₂.val w))

def TreeInf : Prop := InfTree → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N) (P : Pre E N)
  (τ : E →+* ℂ) (m : Multiset ℂ), t.Good → t.Untw → TreeParts t P → t.space ≠ ⊥ → HasInfCharGL t.space τ m →
  ∑ i, P.m i τ = m

def WeightJoin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n a b : ℕ) (μ : HChar E)
  (e : InfinitePlace E → ℤ) (π : Submodule ℂ (UA E n → ℂ)) (lam : InfinitePlace E → DomWeight n)
  (n₁ n₂ : (E →+* ℂ) → Multiset ℂ), 1 ≤ n → IsMu μ e → IsAutRepU π → (∀ v, HasWeightAt π v.embedding (lam v)) →
  RealSym n₁ → RealSym n₂ →
  (∀ v, (n₁ v.embedding).map (· + (b : ℂ) * (e v : ℂ) / 2) + (n₂ v.embedding).map (· + (a : ℂ) * (e v : ℂ) / 2) =
    infOfWeight (lam v)) →
  ∀ τ lam', HasWeightAt π τ lam' →
    (n₁ τ).map (· + expo (μ ^ b) τ) + (n₂ τ).map (· + expo (μ ^ a) τ) = infOfWeight lam'

def TreeSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N) (P : Pre E N) (w : Pl E),
  t.Good → t.Untw → TreeParts t P →
  (∃ φ ∈ t.space, φ ≠ 0 ∧ ∀ k ∈ KGL w (n := N), finRep E N (locGL E N w k) φ = φ) →
  ∃ B, P.Sat w B ∧ ∀ φ ∈ t.space, φ ≠ 0 → (∀ k ∈ KGL w (n := N), finRep E N (locGL E N w k) φ = φ) →
    IsSatVecGL w ((finRep E N).comp (locGL E N w)) φ B

def PairSat : Prop := TreeSat → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (s₁ : Tr E a) (s₂ : Tr E b)
  (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) (G : H E a b → ℂ), s₁.Good → s₂.Good → s₁.Untw → s₂.Untw → TreeParts s₁ Pa →
  TreeParts s₂ Pb → G ∈ pairSpace s₁.space s₂.space → G ≠ 0 → G ∈ fixed (pairRt a b w) (K2 a b w) →
  ∃ Ba Bb, Pa.Sat w Ba ∧ Pb.Sat w Bb ∧ IsSat2 w (pairRt a b w) G Ba Bb

def ThetaSat2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w u : Pl E) (G : H E a b → ℂ)
  (Ba Bb : Multiset ℂˣ), IsSplitAt w → ConjPl w u → IsSat2 u (pairRt a b u) G Ba Bb →
  IsSat2 w (pairRtT a b w) G (Ba.map (·⁻¹)) (Bb.map (·⁻¹))

def CtSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
  (ν : (w.adicCompletion E)ˣ →* ℂˣ) (c : ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GLw a w × GLw b w) V) (x : V) (Ba Bb : Multiset ℂˣ), IsSplitAt w →
  ν = GlobalTheory.SmGL.unrChar (w.adicCompletion E) c → IsSat2 w ρ x Ba Bb → ∀ ϖ, IsUnifV E w ϖ → ∀ k ≤ n,
    heckeVec ρ (K2 a b w) (ctT h w ν ϖ k) x =
      satEig (qV E w) n (Ba.map (· * c ^ b) + Bb.map (· * c ^ a)) k • x

def MuLoc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (μ : HChar E)
  (e : InfinitePlace E → ℤ) (w : Pl E), IsMu μ e → μ.UnrAt w →
  μ.loc w = GlobalTheory.SmGL.unrChar (w.adicCompletion E) (μ.val w) ∧ (∀ k : ℕ, (μ ^ k).UnrAt w ∧ (μ ^ k).val w = μ.val w ^ k) ∧
    ∀ u, IsSplitAt w → ConjPl w u → μ.UnrAt u ∧ μ.val u = (μ.val w)⁻¹

def SatAtU (π : Submodule ℂ (UA E n → ℂ)) (w : Pl E) (B : Multiset ℂˣ) : Prop :=
  ∃ σ : SmIrr (GLw n w), IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ HasSatGL w σ.ρ B

def SatSplit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (D : Pre E n) (w : Pl E) (B : Multiset ℂˣ), SatAtU π w B → D.Sat w B → D.SplitAt π w

def SatConj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (w u : Pl E) (B : Multiset ℂˣ), IsAutRepU π → IsSplitAt w → ConjPl w u → SatAtU π w B → SatAtU π u (B.map (·⁻¹))

def ReadSplit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n a b : ℕ) (h : a + b = n)
  (μ : HChar E) (e : InfinitePlace E → ℤ) (π : Submodule ℂ (UA E n → ℂ)) (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a)
  (Pb : Pre E b) (D : Pre E n) (G : H E a b → ℂ) (w : Pl E) (B : Multiset ℂˣ) (ϖ : w.adicCompletion E),
  IsMu μ e → IsAutRepU π → s₁.Good → s₂.Good → s₁.Untw → s₂.Untw → TreeParts s₁ Pa → TreeParts s₂ Pb →
  IsJoin (μ ^ b) (μ ^ a) Pa Pb D → G ∈ pairSpace s₁.space s₂.space → G ≠ 0 → IsSplitAt w → μ.UnrAt w → SatAtU π w B →
  IsUnifV E w ϖ →
  (G ∈ fixed (pairRt a b w) (K2 a b w) →
    (∀ k ≤ n, heckeVec (pairRt a b w) (K2 a b w) (ctT h w (μ.loc w) ϖ k) G = satEig (qV E w) n B k • G) →
    D.Sat w B ∧ D.SplitAt π w) ∧
  ∀ u, ConjPl w u → G ∈ fixed (pairRt a b u) (K2 a b u) →
    (∀ k ≤ n, heckeVec (pairRtT a b w) (K2 a b w) (ctT h w (μ.loc w) ϖ k) G = satEig (qV E w) n B k • G) →
    D.Sat u (B.map (·⁻¹)) ∧ D.SplitAt π u

theorem readSplit_of (h1 : TreeSat) (h2 : PairSat) (h3 : ThetaSat2) (h4 : CtSat) (h5 : MuLoc) (h6 : JoinSat)
    (h7 : SatSplit) (h8 : SatConj) : ReadSplit := by
  intro E _ _ _ hE n a b h μ e π s₁ s₂ Pa Pb D G w B ϖ hμ hπ g₁ g₂ u₁ u₂ t₁ t₂ hJ hG h0 hw hun hB hϖ
  obtain ⟨m1, m2, m3⟩ := h5 E hE μ e w hμ hun
  have hq : qV E w ≠ 0 := qV_ne_zero w
  have hc : B.card = n := by
    obtain ⟨σ, -, hs⟩ := hB
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hs.1
    exact (hs.2 x hx hx0).2.2.1
  have key : ∀ (ρ : Representation ℂ (GLw a w × GLw b w) (H E a b → ℂ)) (Ba Bb : Multiset ℂˣ), IsSat2 w ρ G Ba Bb →
      (∀ k ≤ n, heckeVec ρ (K2 a b w) (ctT h w (μ.loc w) ϖ k) G = satEig (qV E w) n B k • G) →
      Ba.map (· * μ.val w ^ b) + Bb.map (· * μ.val w ^ a) = B := fun ρ Ba Bb hs he =>
    eq_of_satEig_eq hq (by simp [hs.2.1, hs.2.2.1, h]) hc fun k hk =>
      smul_left_injective ℂ h0 ((h4 E n a b h w _ _ _ ρ G Ba Bb hw m1 hs ϖ hϖ k hk).symm.trans (he k hk))
  refine ⟨fun hf he => ?_, fun u hu hf he => ?_⟩
  · obtain ⟨Ba, Bb, sa, sb, hs⟩ := h2 h1 E a b s₁ s₂ Pa Pb w G g₁ g₂ u₁ u₂ t₁ t₂ hG h0 hf
    have hD := h6 E n a b _ _ Pa Pb D w Ba Bb hJ (m2 b).1 (m2 a).1 sa sb
    rw [(m2 b).2, (m2 a).2, key _ Ba Bb hs he] at hD
    exact ⟨hD, h7 E n π D w B hB hD⟩
  · obtain ⟨Ba, Bb, sa, sb, hs⟩ := h2 h1 E a b s₁ s₂ Pa Pb u G g₁ g₂ u₁ u₂ t₁ t₂ hG h0 hf
    obtain ⟨hu1, hu2⟩ := m3 u hw hu
    obtain ⟨-, n2, -⟩ := h5 E hE μ e u hμ hu1
    have hD := h6 E n a b _ _ Pa Pb D u Ba Bb hJ (n2 b).1 (n2 a).1 sa sb
    have e1 := key _ _ _ (h3 E a b w u G Ba Bb hw hu hs) he
    have e2 : Ba.map (· * (μ ^ b).val u) + Bb.map (· * (μ ^ a).val u) = B.map (·⁻¹) := by
      rw [(n2 b).2, (n2 a).2, hu2, ← e1]
      simp [Multiset.map_map, mul_comm]
    rw [e2] at hD
    exact ⟨hD, h7 E n π D u _ (h8 E n π w u B hπ hw hu hB) hD⟩

end PositivityTheory.Rg.BcB.F.RS

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical



namespace PositivityTheory.Rg.BcB.F

abbrev borelA (E : Type) [Field E] [NumberField E] (n : ℕ) : MeasurableSpace (GA E n) := borel _

attribute [local instance] borelG borelF borelA

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

structure Chain (μ : HChar E) (e : InfinitePlace E → ℤ) (lam : InfinitePlace E → DomWeight n) : Type 1 where
  ι : Type
  [ft : Fintype ι]
  [ne : Nonempty ι]
  a : ι → ℕ
  l₁ : ∀ i, InfinitePlace E → DomWeight (a i)
  l₂ : ∀ i, InfinitePlace E → DomWeight (n - a i)
  le : ∀ i, a i ≤ n
  inf : ∀ i v, (infOfWeight (l₁ i v)).map (· + ((n - a i : ℕ) : ℂ) * (e v : ℂ) / 2) +
    (infOfWeight (l₂ i v)).map (· + (a i : ℂ) * (e v : ℂ) / 2) = infOfWeight (lam v)
  μG : ∀ a, Measure (GA E a)
  hG : ∀ a, (μG a).IsHaarMeasure
  νC : ∀ a, Measure (G a)
  hC : ∀ a, (νC a).IsHaarMeasure
  c : ι → ℂ
  eq : ∀ S : Set (Pl E), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → GlobalTheory.BCT.IsTest (KL n) K' f →
    ∀ (u₁ : ∀ a, GL (Fin a) E) (u₂ : ∀ a, GL (Fin (n - a)) E), (∀ a, IsTransl (u₁ a) ∧ IsTransl (u₂ a)) →
    ∀ (φ₁ φ₂ : ∀ a (w : Pl E), GLw a w × GLw (n - a) w → ℂ),
    (∀ a ≤ n, IsTestP (φ₁ a) ∧ IsTestP (φ₂ a) ∧ IsTestP (seen (φ₁ a) (φ₂ a)) ∧
      ∀ w ∈ S, Match n a (n - a) w (μ.loc w) (f w) (seen (φ₁ a) (φ₂ a) w)) →
    (∀ i, ∃ w ∈ S, RegAt2 (a i) (n - a i) w (seen (φ₁ (a i)) (φ₂ (a i)) w)) →
    ∀ (val : ι → InfinitePlace E → ℂ) (ψ : ∀ i, InfinitePlace E → GL (Fin (a i)) ℂ × GL (Fin (n - a i)) ℂ → ℂ),
    (∀ i v, LefAt (νC (a i)) (νC (n - a i)) (l₁ i v) (l₂ i v) (val i v) (ψ i v)) → ∀ z : ℂ, (∀ i, ∏ v, val i v = z) →
    z * geomU S lam f = ∑ i, c i *
      ellSum2 (μG (a i)) (μG (n - a i)) (adel S (u₁ (a i)) (u₂ (a i)) (ψ i) (φ₁ (a i)) (φ₂ (a i)))

attribute [instance] Chain.ft Chain.ne

structure Arch (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a)
    (l₂ : InfinitePlace E → DomWeight b) (μ₁ : Measure (GA E a)) (μ₂ : Measure (GA E b)) (μa : Measure (G a))
    (μb : Measure (G b)) : Type 1 where
  D : Dom E a b
  Ma : Mods E a
  Mb : Mods E b
  ν : Measure (Hf E a b)
  ha : μa.IsHaarMeasure
  hb : μb.IsHaarMeasure
  hν : ν.IsHaarMeasure
  hν' : ν.IsMulRightInvariant
  compat : Compat D μa μb ν
  c : ℝ
  c_nonneg : 0 ≤ c
  ca : ∀ g h : GA E a, logSize (g * h) ≤ logSize g + logSize h + c
  cb : ∀ g h : GA E b, logSize (g * h) ≤ logSize g + logSize h + c
  growth : ∀ (κ : Type) [Fintype κ], GrowthAt (⟨a, b, D, Ma, Mb, κ, μa, μb, ν, ha, hb, hν, hν', compat, c, c_nonneg, ca, cb⟩ : Block E) μ₁ μ₂
  Ta : Ops Ma
  Tb : Ops Mb
  vca : ∀ v k val T, IsMult μa (Ma v) k val T → VeryCusp (phiOf (Ma v) (Ta v) k)
  vcb : ∀ v k val T, IsMult μb (Mb v) k val T → VeryCusp (phiOf (Mb v) (Tb v) k)
  lef : ∀ v k k' val val' T, IsMult μa (Ma v) k val T → IsMult μb (Mb v) k' val' T →
    LefAt μa μb (l₁ v) (l₂ v) (val (infOf (l₁ v).w) * val' (infOf (l₂ v).w))
      fun y => phiOf (Ma v) (Ta v) k y.1 * phiOf (Mb v) (Tb v) k' y.2
  bump : ℝ → ℝ
  T : ℝ
  T_nonneg : 0 ≤ T
  isBump : IsBump bump T
  ka : List (Bool × ℕ) → Kers Ma
  kb : List (Bool × ℕ) → Kers Mb
  kera : ∀ w v, IsKer μa (Ma v) w bump (ka w v)
  kerb : ∀ w v, IsKer μb (Mb v) w bump (kb w v)
  one : (∏ v, coshT bump (cas (infOf (l₁ v).w))) * ∏ v, coshT bump (cas (infOf (l₂ v).w)) = 1

namespace Arch

variable {a b : ℕ} {l₁ : InfinitePlace E → DomWeight a} {l₂ : InfinitePlace E → DomWeight b} {μ₁ : Measure (GA E a)}
  {μ₂ : Measure (GA E b)} {μa : Measure (G a)} {μb : Measure (G b)} (A : Arch E a b l₁ l₂ μ₁ μ₂ μa μb)

abbrev blk (κ : Type) [Fintype κ] : Block E :=
  ⟨a, b, A.D, A.Ma, A.Mb, κ, μa, μb, A.ν, A.ha, A.hb, A.hν, A.hν', A.compat, A.c, A.c_nonneg, A.ca, A.cb⟩

def valW {m : ℕ} (w : List (Bool × ℕ)) (χ : Inf m) : ℂ := zVal w χ * coshT A.bump (cas χ)

def χa (_ : Arch E a b l₁ l₂ μ₁ μ₂ μa μb) : InfinitePlace E → Inf a := fun v => infOf (l₁ v).w

def χb (_ : Arch E a b l₁ l₂ μ₁ μ₂ μa μb) : InfinitePlace E → Inf b := fun v => infOf (l₂ v).w

def pt {κ : Type} [Fintype κ] (wa wb : InfinitePlace E → List (Bool × ℕ)) (ψ : Matrix κ κ (Hf E a b → ℂ)) (r : ℝ) :
    PT (A.blk κ) :=
  ⟨fun v => A.ka (wa v) v, fun v => A.kb (wb v) v, fun v => A.valW (wa v), fun v => A.valW (wb v), A.T, ψ, r⟩

end Arch

def sizeOf {a b : ℕ} {κ : Type} (ψ : Matrix κ κ (Hf E a b → ℂ)) : ℝ :=
  if h : ∃ r, 0 ≤ r ∧ ∀ x y g, ψ x y g ≠ 0 → logSize (finGL E a g.1) ≤ r ∧ logSize (finGL E b g.2) ≤ r then h.choose else 0

def ChainEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ lam : InfinitePlace E → DomWeight n, Nonempty (Chain μ e lam)

def ArchEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ)
  (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b) (μ₁ : Measure (GA E a)) (μ₂ : Measure (GA E b))
  (μa : Measure (G a)) (μb : Measure (G b)), μ₁.IsHaarMeasure → μ₂.IsHaarMeasure → μa.IsHaarMeasure → μb.IsHaarMeasure →
  Nonempty (Arch E a b l₁ l₂ μ₁ μ₂ μa μb)

end PositivityTheory.Rg.BcB.F

end
end
