module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.ExtremeSph
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbLem
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle003
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


namespace PositivityTheory.Rg.BcB.F.Tail

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b N : ℕ}

abbrev prodAt (P : Pre E n) (w : Pl E) := lp P w

abbrev pairAt (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) := GlobalTheory.SmGL.extTensor (prodAt Pa w) (prodAt Pb w)

structure Ctx (μ : HChar E) (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n) : Prop where
  g₁ : s₁.Good
  g₂ : s₂.Good
  u₁ : s₁.Untw
  u₂ : s₂.Untw
  t₁ : TreeParts s₁ Pa
  t₂ : TreeParts s₂ Pb
  join : IsJoin (μ ^ b) (μ ^ a) Pa Pb D

def JoinType : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (μ : HChar E)
  (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))), KTypes E Ω →
  ∃ W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ), (∀ N, FiniteDimensional ℂ (W N)) ∧
    ∀ (a b : ℕ), a + b = n → ∀ (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D →
      s₁.AllLeaves (fun M V => M = 0 ∨ ∃ K', ∃ W' ∈ Ω M, HasType K' W' V) →
      s₂.AllLeaves (fun M V => M = 0 ∨ ∃ K', ∃ W' ∈ Ω M, HasType K' W' V) → ∀ i, HasKType (W (D.N i)) (D.V i)

def ReadLev : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (μ : HChar E)
  (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D →
  ∀ (w : Pl E) (K : Subgroup (GLw n w)) (L : Subgroup (GLw a w × GLw b w)) (G : H E a b → ℂ),
  IsOpen (K : Set (GLw n w)) → IsCompact (K : Set (GLw n w)) → IsOpen (L : Set (GLw a w × GLw b w)) →
  (∀ m X, blk h w m X ∈ K → m ∈ L ∧ μ.loc w (GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) = 1) →
  G ∈ pairSpace s₁.space s₂.space → G ≠ 0 → G ∈ fixed (pairRt a b w) L → GlobalTheory.LGrp.IsSpherical (prodAt D w) K

def actP (w : Pl E) (u : GLw a w × GLw b w → ℂ) (G : H E a b → ℂ) : H E a b → ℂ :=
  fun z => hint (K2 a b w) fun m => u m * pairRt a b w m G z

def phiMu (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : GLw n w → ℂ) (x y : GLw n w)
    (m : GLw a w × GLw b w) : ℂ :=
  (μ ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) * phi3 h w f x y m

def matS (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : GLw n w → ℂ) (X : Finset (GLw n w))
    (G : X → H E a b → ℂ) : X → H E a b → ℂ := fun x => ∑ y : X, actP w (phiMu h w μ f x y) (G y)

def ReadS : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (μ : HChar E)
  (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D →
  ∀ (w : Pl E) (K' : Subgroup (GLw n w)) (X : Finset (GLw n w)) (L : Subgroup (GLw a w × GLw b w)) (e : GLw n w → ℂ)
    (P : SmIrr (GLw n w)) (m : ℕ) (G : X → H E a b → ℂ), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w (n := n) →
    (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w (n := n)) →
    (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') → IsOpen (L : Set (GLw a w × GLw b w)) → IsHk K' e →
    (∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) → IsEmpty (τ.ρ.Equiv P.ρ) →
      ∀ v ∈ fixed τ.ρ K', hk τ.ρ K' e v = 0) →
    Module.finrank ℂ (fixed (prodAt D w) K') < m →
    (∀ x, G x ∈ pairSpace s₁.space s₂.space ∧ G x ∈ fixed (pairRt a b w) L) → (matS h w (μ.loc w) e X)^[m] G ≠ 0 →
    GlobalTheory.SmGL.IsSubquotient P.ρ (prodAt D w)

def hkG {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ) (v : V) : V :=
  ∑ᶠ q : G ⧸ K, f q.out • ρ q.out v

def dl (w : Pl E) (x : Fin N → ℤ) : ℂ := qh w ^ (∑ i : Fin N, ((N : ℤ) - 1 - 2 * (i : ℕ)) * x i)

def Gap (x : Fin N → ℤ) : Prop := ∀ i j, i < j → x j + 1 ≤ x i

abbrev I2 (a b : ℕ) (w : Pl E) : Subgroup (GLw a w × GLw b w) := (iwGL a w).prod (iwGL b w)

def dc2 (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (x : Fin a → ℤ) (y : Fin b → ℤ) (m : GLw a w × GLw b w) : ℂ :=
  dcos a w (tdiag ϖ x) m.1 * dcos b w (tdiag ϖ y) m.2

def ev2 (w : Pl E) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ) (x : Fin a → ℤ) (y : Fin b → ℤ) : ℂ :=
  dl w x * pw ξa x * (dl w y * pw ξb y)

def JEig (Pa : Pre E a) (Pb : Pre E b) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ) : Prop :=
  ∃ v ∈ fixed (pairAt Pa Pb w) (I2 a b w), v ≠ 0 ∧
    ∀ x y, Gap x → Gap y → hkG (pairAt Pa Pb w) (I2 a b w) (dc2 w ϖ x y) v = ev2 w ξa ξb x y • v

def ReadT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (μ : HChar E)
  (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D →
  ∀ (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (J : Type) [Fintype J] (c : J → ℂ) (x : J → Fin a → ℤ) (y : J → Fin b → ℤ) (m : ℕ)
    (G : H E a b → ℂ), ordL (ϖ : w.adicCompletion E) = 1 → (∀ j, Gap (x j) ∧ Gap (y j)) →
    Module.finrank ℂ (fixed (pairAt Pa Pb w) (I2 a b w)) ≤ m →
    G ∈ pairSpace s₁.space s₂.space → G ∈ fixed (pairRt a b w) (I2 a b w) →
    (actP w fun g => ∑ j, c j * dc2 w ϖ (x j) (y j) g)^[m] G ≠ 0 →
    ∃ ξa ξb, JEig Pa Pb w ϖ ξa ξb ∧ ∑ j, c j * ev2 w ξa ξb (x j) (y j) ≠ 0

def JEigFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Pa : Pre E a) (Pb : Pre E b) (w : Pl E)
  (ϖ : (w.adicCompletion E)ˣ), ordL (ϖ : w.adicCompletion E) = 1 →
  ∃ (Z : Set ((Fin a → ℂˣ) × (Fin b → ℂˣ))) (m : ℕ), Z.Finite ∧ ∀ (Pa' : Pre E a) (Pb' : Pre E b), PreEquiv Pa Pa' → PreEquiv Pb Pb' →
    Module.finrank ℂ (fixed (pairAt Pa' Pb' w) (I2 a b w)) ≤ m ∧ ∀ ξa ξb, JEig Pa' Pb' w ϖ ξa ξb → (ξa, ξb) ∈ Z

def ExpRead : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Pa : Pre E a) (Pb : Pre E b) (w : Pl E)
  (ϖ : (w.adicCompletion E)ˣ) (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ), ordL (ϖ : w.adicCompletion E) = 1 →
  N3.Mono ξa → N3.Mono ξb → JEig Pa Pb w ϖ ξa ξb →
    Pa.Sat w (Finset.univ.val.map ξa) ∧ Pb.Sat w (Finset.univ.val.map ξb)

def RReadLev : Prop := RS.ReadMod → JoinMod → ReadLev
def RReadS : Prop := RS.ReadMod → JoinMod → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], LocOpUniformizer E) → ReadS
def RReadT : Prop := RS.ReadMod → ReadT
def RExpRead : Prop := N3.N3 → ExpRead

theorem tout_of {π : Submodule ℂ (UA E n → ℂ)} {S T : Finset (Pl E)} {K : ∀ w : Pl E, Subgroup (GLw n w)}
    {W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)} {D : Pre E n}
    (wt : ∀ τ lam, HasWeightAt π τ lam → ∑ i, D.m i τ = infOfWeight lam)
    (good : ∀ᶠ w : Pl E in cofinite, IsSplitAt w → D.SplitAt π w)
    (atS : ∀ w ∈ S, IsSplitAt w → ∃ P : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient P.ρ (prodAt D w) ∧
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ)
    (atT : ∀ w ∈ T, IsUnramU π w → ¬ IsSplitAt w → InertAt π D w)
    (lev : ∀ w, GlobalTheory.LGrp.IsSpherical (prodAt D w) (K w)) (kt : ∀ i, HasKType (W (D.N i)) (D.V i)) : TOut π S T K W D :=
  ⟨⟨wt, Set.Finite.subset (eventually_cofinite.1 good) fun _ hw hx => hw.2 (hx hw.1)⟩, atS, atT, lev, kt⟩

end PositivityTheory.Rg.BcB.F.Tail

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd.B

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Rd


theorem perK (hAV : ActVal) (hBO : BlockOperatorsProductAdjoint) (hCM : ConvMulSt) (hFin : FinSt) (hReal : RealiseSt)
    {E : Type} [Field E] [NumberField E] [IsCMField E] (B : Block E)
    (W₁ : Submodule ℂ (Kinf E B.a → ℂ)) (W₂ : Submodule ℂ (Kinf E B.b → ℂ))
    (K₁ : Subgroup (GL (Fin B.a) (Af E))) (K₂ : Subgroup (GL (Fin B.b) (Af E)))
    (o₁ : IsOpen (K₁ : Set (GL (Fin B.a) (Af E)))) (c₁ : IsCompact (K₁ : Set (GL (Fin B.a) (Af E))))
    (o₂ : IsOpen (K₂ : Set (GL (Fin B.b) (Af E)))) (c₂ : IsCompact (K₂ : Set (GL (Fin B.b) (Af E))))
    (hP : PackAt E B.a B.b B.Ma B.Mb W₁ W₂)
    (Γ : Type) [Countable Γ] (g : Γ → BGen B) (a₀ : Γ) (t₀ : PT B) (bump : ℝ → ℝ) (cK : ℂ)
    (der : InfinitePlace E → Bool → ℕ → Γ × Γ) (X : B.Hb →L[ℂ] B.Hb) (tX : PT B) (jX : ℕ) (χ : ChAlg g X →⋆ₐ[ℂ] ℂ)
    (hok : ∀ x, (g x).Ok) (htX : tX.Ok) (hXe : X = tX.op) (hjX : ∀ χa' χb', tX.val χa' χb' = t₀.val χa' χb' ^ jX)
    (ha₀ : g a₀ = Sum.inr t₀) (hbump : IsBump bump t₀.T)
    (hka0 : ∀ v, IsKer B.μa (B.Ma v) [] bump (t₀.ka v)) (hkb0 : ∀ v, IsKer B.μb (B.Mb v) [] bump (t₀.kb v))
    (hcK : cK * (B.ν.real ((K₁.prod K₂ : Subgroup (Hf E B.a B.b)) : Set (Hf E B.a B.b)) : ℂ) = 1)
    (hψ₀ : ∀ x y h, t₀.ψ x y h = if x = y ∧ h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) then cK else 0)
    (hderA : ∀ v s m, 1 ≤ m → 0 < B.a → ∃ ta : PT B, g (der v s m).1 = Sum.inr ta ∧
      ArchType t₀ ta ∧ ta.kb = t₀.kb ∧ IsKer B.μa (B.Ma v) [(s, m)] bump (ta.ka v) ∧ (∀ v', v' ≠ v → ta.ka v' = t₀.ka v'))
    (hderB : ∀ v s m, 1 ≤ m → 0 < B.b → ∃ tb : PT B, g (der v s m).2 = Sum.inr tb ∧
      ArchType t₀ tb ∧ tb.ka = t₀.ka ∧ IsKer B.μb (B.Mb v) [(s, m)] bump (tb.kb v) ∧ (∀ v', v' ≠ v → tb.kb v' = t₀.kb v'))
    (hcomm : ∀ x y, Commute (g x).op (g y).op ∧ Commute (g x).op (star (g y).op))
    (hXc : ∀ x, Commute X (g x).op ∧ Commute X (star (g x).op)) (hXs : IsSelfAdjoint X)
    (hχn : ∀ y, ‖χ y‖ ≤ ‖(y : B.Hb →L[ℂ] B.Hb)‖) (hχ0 : χ (genE g X a₀) ≠ 0) :
    PerKOut B W₁ W₂ K₁ K₂ g a₀ t₀ der X tX jX χ := by
  haveI := B.ha
  haveI := B.hb
  haveI := B.hν
  haveI : BorelSpace (G B.a) := ⟨rfl⟩
  haveI : BorelSpace (G B.b) := ⟨rfl⟩
  haveI : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  have okOf : ∀ y (t : PT B), g y = Sum.inr t → t.Ok := fun y t hy => by
    have := hok y; rw [hy] at this; exact this
  have ht₀ : t₀.Ok := okOf a₀ t₀ ha₀
  obtain ⟨M, sk, f, hsg, hsX, hk⟩ := hReal E B Γ g a₀ t₀ X tX χ hok htX hXe ha₀ hcomm hXc hXs hχn hχ0
  have hc : ∀ k, sk k (genE g X a₀) ≠ 0 := fun k => (hk k).1
  have hcont : ∀ k i, Continuous (f k i) := fun k => (hk k).2.1
  have hne : ∀ k, f k ≠ 0 := fun k => (hk k).2.2.1
  have heq0 : ∀ k, PositivityTheory.Rg.BcB.E.conv B.D.μ t₀.Φ (f k) = sk k (genE g X a₀) • f k := fun k => (hk k).2.2.2.2.2.1
  have hAt : ∀ k y (t : PT B), g y = Sum.inr t → PositivityTheory.Rg.BcB.E.conv B.D.μ t.Φ (f k) = sk k (genE g X y) • f k := by
    intro k y t hy
    have htok := okOf y t hy
    have e := hCM E B.a B.b B.D B.I t.Φ t₀.Φ (hBO E B t t htok htok).1 (hBO E B t₀ t₀ ht₀ ht₀).1 (f k) (hcont k)
    rw [(hk k).2.2.2.2.2.2.1 y t hy, heq0 k, conv_smul] at e
    have e2 : sk k (genE g X a₀) • PositivityTheory.Rg.BcB.E.conv B.D.μ t.Φ (f k) =
        sk k (genE g X a₀) • (sk k (genE g X y) • f k) := by
      rw [← e, smul_smul, mul_comm]
    exact smul_right_injective _ (hc k) e2
  have hAX : ∀ k, PositivityTheory.Rg.BcB.E.conv B.D.μ tX.Φ (f k) = sk k (XE g X) • f k := by
    intro k
    have e := hCM E B.a B.b B.D B.I tX.Φ t₀.Φ (hBO E B tX tX htX htX).1 (hBO E B t₀ t₀ ht₀ ht₀).1 (f k) (hcont k)
    rw [(hk k).2.2.2.2.2.2.2, heq0 k, conv_smul] at e
    have e2 : sk k (genE g X a₀) • PositivityTheory.Rg.BcB.E.conv B.D.μ tX.Φ (f k) =
        sk k (genE g X a₀) • (sk k (XE g X) • f k) := by
      rw [← e, smul_smul, mul_comm]
    exact smul_right_injective _ (hc k) e2
  have hPk := fun k => packK hBO B W₁ W₂ K₁ K₂ o₁ o₂ hP g t₀ bump cK der ht₀ hbump hka0 hkb0 hψ₀ hderA hderB M (f k)
    (sk k (genE g X a₀)) (fun y => sk k (genE g X y)) (hcont k) (hne k) (hk k).2.2.2.1 (hk k).2.2.2.2.1 (hc k) (heq0 k)
    (hAt k)
  choose χak χbk hgA hgB hEig hTy hS₁ hS₂ hAu₁ hAu₂ hI₁ hI₂ using hPk
  obtain ⟨hFinA, -⟩ := hFin E B K₁ K₂ o₁ c₁ o₂ c₂ cK t₀.ψ hcK hψ₀
  have hrinv : ∀ k, ∀ i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, f k i (x * finH u) = f k i x := by
    intro k i u hu x
    exact (hTy k i).1 u.1 (Subgroup.mem_prod.1 hu).1 u.2 (Subgroup.mem_prod.1 hu).2 x
  have hidk : ∀ k, convF B.ν t₀.ψ (f k) = f k := fun k => (hFinA _ (f k) (hrinv k)).1
  have hAVt : ∀ k (t : PT B), t.Ok → PositivityTheory.Rg.BcB.E.conv B.D.μ t.Φ (f k) =
      t.val (χak k) (χbk k) • convF B.ν t.ψ (f k) := by
    intro k t htok
    exact hAV E B.a B.b B.D B.μa B.μb B.ν B.Ma B.Mb B.κ t₀.ka t.ka t₀.kb t.kb t₀.va t.va t₀.vb t.vb t₀.T t.T t₀.ψ t.ψ
      (f k) (χak k) (χbk k) B.compat ht₀.ka ht₀.kb ht₀.ψ ⟨hcont k, _, hc k, heq0 k⟩ ⟨hS₁ k, hS₂ k⟩ (hEig k) htok.ka
      htok.kb htok.ψ
  have hv₀ : ∀ k, t₀.val (χak k) (χbk k) = sk k (genE g X a₀) := by
    intro k
    have e := hAVt k t₀ ht₀
    rw [hidk k, heq0 k] at e
    exact (smul_cancel (hne k) e).symm
  have hFinK : ∀ k y (t : PT B), g y = Sum.inr t → FinType t₀ t →
      convF B.ν t.ψ (f k) = (sk k (genE g X y) / sk k (genE g X a₀)) • f k := by
    intro k y t hy hft
    have htok := okOf y t hy
    have hv : t.val (χak k) (χbk k) = sk k (genE g X a₀) := by
      rw [← hv₀ k]; unfold PT.val; rw [hft.2.2.1, hft.2.2.2.1]
    have e := hAVt k t htok
    rw [hAt k y t hy, hv] at e
    refine smul_right_injective _ (hc k) ?_
    show sk k (genE g X a₀) • _ = sk k (genE g X a₀) • _
    rw [← e, smul_smul]
    congr 1
    field_simp [hc k]
  have hXK : ∀ k, convF B.ν tX.ψ (f k) = (sk k (XE g X) / sk k (genE g X a₀) ^ jX) • f k := by
    intro k
    have e := hAVt k tX htX
    rw [hAX k, hjX, hv₀ k] at e
    have hcj : sk k (genE g X a₀) ^ jX ≠ 0 := pow_ne_zero _ (hc k)
    refine smul_right_injective _ hcj ?_
    show sk k (genE g X a₀) ^ jX • _ = sk k (genE g X a₀) ^ jX • _
    rw [← e, smul_smul]
    congr 1
    field_simp [hcj]
  have hArchK : ∀ k y (t : PT B), g y = Sum.inr t → ArchType t₀ t → t.val (χak k) (χbk k) = sk k (genE g X y) := by
    intro k y t hy hat
    have e := hAVt k t (okOf y t hy)
    rw [hAt k y t hy, show t.ψ = t₀.ψ from hat, hidk k] at e
    exact (smul_cancel (hne k) e).symm
  have hlimA : ∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χak k v s) m) atTop
      (𝓝 (if 1 ≤ m ∧ 0 < B.a then χ (genE g X (der v s m).1) / χ (genE g X a₀) else if m = 0 then (B.a : ℂ) else 0)) := by
    intro v s m
    refine Tendsto.congr (fun k => (hgA k v s m).symm) ?_
    by_cases h : 1 ≤ m ∧ 0 < B.a
    · simp only [if_pos h]
      exact (hsg _).div (hsg a₀) hχ0
    · by_cases hm : m = 0
      · simp only [if_neg h, if_pos hm]
        refine tendsto_const_nhds.congr (fun k => ?_)
        field_simp [hc k]
      · simp only [if_neg h, if_neg hm, zero_div]
        exact tendsto_const_nhds
  have hlimB : ∀ v s m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χbk k v s) m) atTop
      (𝓝 (if 1 ≤ m ∧ 0 < B.b then χ (genE g X (der v s m).2) / χ (genE g X a₀) else if m = 0 then (B.b : ℂ) else 0)) := by
    intro v s m
    refine Tendsto.congr (fun k => (hgB k v s m).symm) ?_
    by_cases h : 1 ≤ m ∧ 0 < B.b
    · simp only [if_pos h]
      exact (hsg _).div (hsg a₀) hχ0
    · by_cases hm : m = 0
      · simp only [if_neg h, if_pos hm]
        refine tendsto_const_nhds.congr (fun k => ?_)
        field_simp [hc k]
      · simp only [if_neg h, if_neg hm, zero_div]
        exact tendsto_const_nhds
  exact ⟨M, sk, f, χak, χbk, hsg, hsX, hlimA, hlimB, fun k => ⟨hc k, hcont k, hne k, (hk k).2.2.2.1,
    (hk k).2.2.2.2.1, hTy k, hS₁ k, hS₂ k, hAu₁ k, hAu₂ k, hI₁ k, hI₂ k, hFinK k, hXK k, hArchK k⟩⟩

end PositivityTheory.Rg.BcB.F.Rd.B

end
end
