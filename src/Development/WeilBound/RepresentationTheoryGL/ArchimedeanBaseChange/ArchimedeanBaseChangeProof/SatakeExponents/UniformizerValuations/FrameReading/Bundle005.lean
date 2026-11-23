module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.GelfandValueContinuity.FinSt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbAlg
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle452
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle482
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle565
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle586
import GroundTheory.LocalFields.PadicLogSeries
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupExOf
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
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd.B

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Rd

theorem sup_one_ne_bot {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (W : Submodule ℂ (Kinf E a → ℂ)) :
    W ⊔ Submodule.span ℂ {fun _ => (1 : ℂ)} ≠ ⊥ := by
  intro h
  have hm : (fun _ => (1 : ℂ)) ∈ W ⊔ Submodule.span ℂ {fun _ : Kinf E a => (1 : ℂ)} :=
    Submodule.mem_sup_right (Submodule.subset_span rfl)
  rw [h, Submodule.mem_bot] at hm
  have := congrFun hm 1
  simp at this

theorem kTypes_insert {E : Type} [Field E] [NumberField E] [IsCMField E] {Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))}
    (h : KTypes E Ω) : KTypes E (fun M => insert ⊥ (Ω M)) := by
  intro M
  refine ⟨(h M).1.insert _, fun W hW => ?_⟩
  rcases hW with rfl | hW
  · infer_instance
  · exact (h M).2 W hW


theorem readLimit_main (hPack : Pack) (hEF : EFinal) (hAV : ActVal) (hFH : FinHecke) (hVC : ValCont) (hIC : InfConv)
    (hIL : InfLim) (hRE : ReproEx) (hBO : BlockOperatorsProductAdjoint) (hCM : ConvMulSt) (hFin : FinSt) (hReal : RealiseSt) : ReadLimit := by
  intro E _ _ _
  choose Wf₁ Wf₂ hWfd₁ hWfd₂ hP using fun a b (Ma : Mods E a) (Mb : Mods E b) => hPack E a b Ma Mb
  let V₁ : ∀ a b : ℕ, Mods E a → Mods E b → Submodule ℂ (Kinf E a → ℂ) := fun a b Ma Mb =>
    Wf₁ a b Ma Mb ⊔ Submodule.span ℂ {fun _ => (1 : ℂ)}
  let V₂ : ∀ a b : ℕ, Mods E a → Mods E b → Submodule ℂ (Kinf E b → ℂ) := fun a b Ma Mb =>
    Wf₂ a b Ma Mb ⊔ Submodule.span ℂ {fun _ => (1 : ℂ)}
  have hV₁ : ∀ a b Ma Mb, FiniteDimensional ℂ (V₁ a b Ma Mb) := fun a b Ma Mb => by
    haveI := hWfd₁ a b Ma Mb; exact Submodule.finiteDimensional_sup _ _
  have hV₂ : ∀ a b Ma Mb, FiniteDimensional ℂ (V₂ a b Ma Mb) := fun a b Ma Mb => by
    haveI := hWfd₂ a b Ma Mb; exact Submodule.finiteDimensional_sup _ _
  choose Ωf₁ Ωf₂ hΩ₁ hΩ₂ hEr using fun a b (Ma : Mods E a) (Mb : Mods E b) =>
    hEF E a b (V₁ a b Ma Mb) (V₂ a b Ma Mb) (hV₁ a b Ma Mb) (hV₂ a b Ma Mb)
  let Θf₁ : ∀ a b : ℕ, Mods E a → Mods E b → Subgroup (GL (Fin a) (Af E)) → Subgroup (GL (Fin b) (Af E)) → ∀ M : ℕ,
      Set (Subgroup (GL (Fin M) (Af E))) := fun a b Ma Mb K₁ K₂ =>
    if h : IsOpen (K₁ : Set (GL (Fin a) (Af E))) ∧ IsOpen (K₂ : Set (GL (Fin b) (Af E))) then
      (hEr a b Ma Mb K₁ K₂ h.1 h.2).choose else fun _ => ∅
  let Θf₂ : ∀ a b : ℕ, Mods E a → Mods E b → Subgroup (GL (Fin a) (Af E)) → Subgroup (GL (Fin b) (Af E)) → ∀ M : ℕ,
      Set (Subgroup (GL (Fin M) (Af E))) := fun a b Ma Mb K₁ K₂ =>
    if h : IsOpen (K₁ : Set (GL (Fin a) (Af E))) ∧ IsOpen (K₂ : Set (GL (Fin b) (Af E))) then
      (hEr a b Ma Mb K₁ K₂ h.1 h.2).choose_spec.choose else fun _ => ∅
  have hΘ₁ : ∀ a b Ma Mb (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
      (o₁ : IsOpen (K₁ : Set (GL (Fin a) (Af E)))) (o₂ : IsOpen (K₂ : Set (GL (Fin b) (Af E)))),
      Θf₁ a b Ma Mb K₁ K₂ = (hEr a b Ma Mb K₁ K₂ o₁ o₂).choose := fun a b Ma Mb K₁ K₂ o₁ o₂ => dif_pos ⟨o₁, o₂⟩
  have hΘ₂ : ∀ a b Ma Mb (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
      (o₁ : IsOpen (K₁ : Set (GL (Fin a) (Af E)))) (o₂ : IsOpen (K₂ : Set (GL (Fin b) (Af E)))),
      Θf₂ a b Ma Mb K₁ K₂ = (hEr a b Ma Mb K₁ K₂ o₁ o₂).choose_spec.choose := fun a b Ma Mb K₁ K₂ o₁ o₂ => dif_pos ⟨o₁, o₂⟩
  refine ⟨V₁, V₂, fun a b Ma Mb M => insert ⊥ (Ωf₁ a b Ma Mb M), fun a b Ma Mb M => insert ⊥ (Ωf₂ a b Ma Mb M),
    Θf₁, Θf₂, fun a b Ma Mb => ⟨hV₁ a b Ma Mb, hV₂ a b Ma Mb, kTypes_insert (hΩ₁ a b Ma Mb),
      kTypes_insert (hΩ₂ a b Ma Mb), fun M => ⟨⟨⊥, Set.mem_insert _ _⟩, ⟨⊥, Set.mem_insert _ _⟩⟩,
      sup_one_ne_bot _, sup_one_ne_bot _⟩, fun a b Ma Mb K₁ K₂ o₁ o₂ => ?_, ?_⟩
  · rw [hΘ₁ a b Ma Mb K₁ K₂ o₁ o₂, hΘ₂ a b Ma Mb K₁ K₂ o₁ o₂]
    exact ⟨(hEr a b Ma Mb K₁ K₂ o₁ o₂).choose_spec.choose_spec.1, (hEr a b Ma Mb K₁ K₂ o₁ o₂).choose_spec.choose_spec.2.1⟩
  intro B K₁ K₂ o₁ c₁ o₂ c₂ Γ _ g a₀ t₀ bump cK der X tX jX χ _hab hok htX hXe hjX ha₀ hbump _htype hka0 hkb0
    hcK hψ₀ hderA hderB hcomm hXc hXs hχn hχ0 hreg
  rw [hΘ₁ _ _ _ _ K₁ K₂ o₁ o₂, hΘ₂ _ _ _ _ K₁ K₂ o₁ o₂]
  have hEB := (hEr B.a B.b B.Ma B.Mb K₁ K₂ o₁ o₂).choose_spec.choose_spec.2.2
  have hK := perK hAV hBO hCM hFin hReal B (Wf₁ B.a B.b B.Ma B.Mb) (Wf₂ B.a B.b B.Ma B.Mb) K₁ K₂ o₁ c₁ o₂ c₂
    (hP B.a B.b B.Ma B.Mb) Γ g a₀ t₀ bump cK der X tX jX χ hok htX hXe hjX ha₀ hbump hka0 hkb0 hcK hψ₀ hderA hderB
    hcomm hXc hXs hχn hχ0
  exact blockOut_lim hFH hVC hIC hIL hRE hBO hFin B (Wf₁ B.a B.b B.Ma B.Mb) (V₁ B.a B.b B.Ma B.Mb)
    (Wf₂ B.a B.b B.Ma B.Mb) (V₂ B.a B.b B.Ma B.Mb) le_sup_left le_sup_left (Ωf₁ B.a B.b B.Ma B.Mb) (Ωf₂ B.a B.b B.Ma B.Mb)
    (fun M => insert ⊥ (Ωf₁ B.a B.b B.Ma B.Mb M)) (fun M => insert ⊥ (Ωf₂ B.a B.b B.Ma B.Mb M))
    (fun M => Set.subset_insert _ _) (fun M => Set.subset_insert _ _) K₁ K₂ _ _ o₁ c₁ o₂ c₂ hEB Γ g a₀ t₀ cK der X tX jX χ
    hok htX ha₀ hcK hψ₀ hχ0 hreg hK

theorem convMulSt_holds : ConvMulSt := fun _ _ _ _ _ _ D _ _ Φ₁ Φ₂ h₁ h₂ f hf => conv_mulM D Φ₁ Φ₂ h₁ h₂ f hf

theorem readLimit_of (e2 : PositivityTheory.Rg.BcB.E.E2) (pk : Pack) (ef : EFinal) (av : ActVal) (fh : FinHecke) (vc : ValCont)
    (ic : InfConv) (il : InfLim) (re : ReproEx) (tm : TensMul) (bo : BlockOperatorsProductAdjoint) (bw : BlockWordOperators) (bs : BlockLinearCombinations)
    (aw : AdjWords) : ReadLimit :=
  readLimit_main pk ef av fh vc ic il re bo convMulSt_holds finSt (realise e2 tm bo bw bs aw)

end PositivityTheory.Rg.BcB.F.Rd.B

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.Tail

attribute [local instance] borelG borelF borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def idem {w : Pl E} (U : Subgroup (GLw a w × GLw b w)) : LF a b w :=
  (U : Set (GLw a w × GLw b w)).indicator fun _ => ((U.relIndex (K2 a b w) : ℕ) : ℂ)

def IsLev (U : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) : Prop :=
  (∀ w, IsOpen (U w : Set (GLw a w × GLw b w)) ∧ U w ≤ K2 a b w) ∧ ∀ᶠ w in cofinite, U w = K2 a b w

def HasLev (G : H E a b → ℂ) : Prop :=
  ∃ U : Subgroup (Hf E a b), IsOpen (U : Set (Hf E a b)) ∧ ∀ u ∈ U, ∀ x, G (x * finH u) = G x

def OfLev (S : Set (Pl E)) (U₁ U₂ : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (G : H E a b → ℂ) : Prop :=
  HasLev G ∧ ∀ w ∈ S, G ∈ fixed (pairRt a b w) (U₁ w) ∧ (IsSplitAt w → G ∈ fixed (pairRtT a b w) (U₂ w))

def actT (w : Pl E) (u : LF a b w) (G : H E a b → ℂ) : H E a b → ℂ :=
  fun z => hint (K2 a b w) fun m => u m * pairRtT a b w m G z

def locM {k : Type} [Fintype k] (w : Pl E) (M : k → k → LF a b w) (G : k → H E a b → ℂ) : k → H E a b → ℂ :=
  fun x => ∑ y, actP w (M x y) (G y)

def DiagIdem {κ : Pl E → Type} (P : Finset (Pl E)) (U : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (L : LM κ a b) : Prop :=
  ∀ w ∈ P, ∀ x y, L.m w x y = if x = y then idem (U w) else 0

def FmOne : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (κ : Pl E → Type) [∀ w, Fintype (κ w)] (S : Set (Pl E))
  (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w), IsSection S → (↑P : Set (Pl E)) ⊆ S →
  ∀ (U₁ U₂ : ∀ w : Pl E, Subgroup (GLw B.a w × GLw B.b w)) (L : LM κ B.a B.b) (A : Type) (F : A × B.κ → H E B.a B.b → ℂ)
    (w₀ : Pl E), IsLev U₁ → IsLev U₂ → L.Ok P → DiagIdem P U₁ L → (∀ i, OfLev S U₁ U₂ (F i)) → w₀ ∈ S →
    (w₀ ∉ P → (∀ w, w ≠ w₀ → L.s w = idem (U₁ w)) → (∀ w, L.t w = idem (U₂ w)) →
      ∀ i, convF B.ν (fm S P B e L) F i = actP w₀ (L.s w₀) (F i)) ∧
    (IsSplitAt w₀ → (∀ w, L.s w = idem (U₁ w)) → (∀ w, w ≠ w₀ → L.t w = idem (U₂ w)) →
      ∀ i, convF B.ν (fm S P B e L) F i = actT w₀ (L.t w₀) (F i))

def FmPow : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (κ : Pl E → Type) [∀ w, Fintype (κ w)] (S : Set (Pl E))
  (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w), IsSection S → (↑P : Set (Pl E)) ⊆ S →
  ∀ (U₁ U₂ : ∀ w : Pl E, Subgroup (GLw B.a w × GLw B.b w)) (L : LM κ B.a B.b) (A : Type) (F : A × B.κ → H E B.a B.b → ℂ)
    (m : ℕ), IsLev U₁ → IsLev U₂ → L.Ok P → (∀ w, L.s w = idem (U₁ w)) → (∀ w, L.t w = idem (U₂ w)) →
    (∀ w ∈ P, ∀ x y, ∀ u ∈ U₁ w, ∀ g, L.m w x y (u * g) = L.m w x y g ∧ L.m w x y (g * u) = L.m w x y g) →
    (∀ i, OfLev S U₁ U₂ (F i)) → (convF B.ν (fm S P B e L))^[m] F ≠ 0 →
    ∀ w₀ : P, ∃ (α : A) (x : ∀ w : P, κ w), (locM w₀.1 (L.m w₀.1))^[m] (fun y => F (α, e.symm (Function.update x w₀ y))) ≠ 0

def ConvMul : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (A : Type)
  (ψ ψ' : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)) (U : Subgroup (Hf E B.a B.b)) (F : A × B.κ → H E B.a B.b → ℂ), IsFinM ψ → IsFinM ψ' →
  IsOpen (U : Set (Hf E B.a B.b)) → (∀ i, ∀ u ∈ U, ∀ x, F i (x * finH u) = F i x) →
    convF B.ν (mulF B.ν ψ ψ') F = convF B.ν ψ (convF B.ν ψ' F) ∧
      ((∀ x y, ∀ u ∈ U, ∀ h, ψ' x y (u * h) = ψ' x y h) → ∀ i, ∀ u ∈ U, ∀ x, convF B.ν ψ' F i (x * finH u) = convF B.ν ψ' F i x)

def LocPow : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (k : Type) [Fintype k]
  (U : Subgroup (GLw a w × GLw b w)) (G : k → H E a b → ℂ) (m : ℕ), IsOpen (U : Set (GLw a w × GLw b w)) →
  (∀ y, G y ∈ fixed (pairRt a b w) U) →
  (∀ (c : ℂ) (M : k → k → LF a b w), (locM w fun x y => c • M x y)^[m] G ≠ 0 → (locM w M)^[m] G ≠ 0) ∧
    ∀ q : k → LF a b w, (locM w fun x y => if x = y then q x else 0)^[m] G ≠ 0 → ∃ x, (actP w (q x))^[m] (G x) ≠ 0

def ActHecke : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (f : LF a b w) (G : H E a b → ℂ),
  HasCompactSupport f → (∀ k ∈ K2 a b w, ∀ g, f (g * k) = f g) →
  (G ∈ fixed (pairRt a b w) (K2 a b w) → actP w f G = GlobalTheory.LFun.heckeVec (pairRt a b w) (K2 a b w) f G) ∧
    (G ∈ fixed (pairRtT a b w) (K2 a b w) → actT w f G = GlobalTheory.LFun.heckeVec (pairRtT a b w) (K2 a b w) f G)

end PositivityTheory.Rg.BcB.F.Tail

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2



namespace PositivityTheory.Rg.BcB.F.Tail

section Leaves

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_leafList_of_allLeaves {P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} :
    ∀ {N : ℕ} (t : Tr E N), t.AllLeaves P → ∀ x ∈ t.leafList, P x.1 x.2
  | _, .leaf V z, h, x, hx => by
    simp only [Tr.leafList, List.mem_singleton] at hx
    subst hx
    exact h
  | _, .node t₁ t₂, h, x, hx => by
    simp only [Tr.leafList, List.mem_append] at hx
    rcases hx with hx | hx
    · exact mem_leafList_of_allLeaves t₁ h.1 x hx
    · exact mem_leafList_of_allLeaves t₂ h.2 x hx

theorem mem_parts_of_treeParts {N : ℕ} {t : Tr E N} {P : Pre E N} {Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop}
    (ht : TreeParts t P) (hl : t.AllLeaves Q) : ∀ x ∈ parts P, 0 < x.1 ∧ Q x.1 x.2 := by
  intro x hx
  have hx' : x ∈ t.leafList.filter fun y => 0 < y.1 := by
    rw [← ht]
    exact hx
  rw [List.mem_filter] at hx'
  exact ⟨by simpa using hx'.2, mem_leafList_of_allLeaves t hl x hx'.1⟩

end Leaves

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def mulK (N : ℕ) (χ : HChar E) : (Kinf E N → ℂ) →ₗ[ℂ] (Kinf E N → ℂ) where
  toFun f k := (chiDet N χ (infGL E N (Unitary.toUnits k)) : ℂ) * f k
  map_add' f g := by
    funext k
    simp only [Pi.add_apply, mul_add]
  map_smul' c f := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem hasKType_twist {N : ℕ} (χ : HChar E) {K' : Subgroup (GL (Fin N) (Af E))} {W' : Submodule ℂ (Kinf E N → ℂ)}
    {V : Submodule ℂ (Sm E N)} (h : HasType K' W' V) :
    HasKType (W'.map (mulK N χ)) (V.map (mulChi N χ).toLinearMap) := by
  obtain ⟨φ, hφV, hφ0, -, hT⟩ := h
  refine ⟨mulChi N χ φ, Submodule.mem_map_of_mem hφV, ?_, fun g => ?_⟩
  · exact (LinearEquiv.map_ne_zero_iff (mulChi N χ)).2 hφ0
  · have e : (fun k : Kinf E N => ((mulChi N χ φ : Sm E N) : GA E N → ℂ) (g * infGL E N (Unitary.toUnits k))) =
        (chiDet N χ g : ℂ) • mulK N χ (fun k : Kinf E N => (φ : GA E N → ℂ) (g * infGL E N (Unitary.toUnits k))) := by
      funext k
      simp only [mulChi_apply, map_mul, Units.val_mul, Pi.smul_apply, smul_eq_mul, mulK, LinearMap.coe_mk,
        AddHom.coe_mk]
      ring
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (hT g))

theorem HasKType.mono {N : ℕ} {W₁ W₂ : Submodule ℂ (Kinf E N → ℂ)} {V : Submodule ℂ (Sm E N)} (h : W₁ ≤ W₂)
    (hV : HasKType W₁ V) : HasKType W₂ V := by
  obtain ⟨φ, hφ, h0, hW⟩ := hV
  exact ⟨φ, hφ, h0, fun g => h (hW g)⟩

end Twist

theorem joinType : JoinType := by
  intro E _ _ _ n μ Ω hΩ
  have : ∀ M, Finite (Ω M) := fun M => (hΩ M).1.to_subtype
  let W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ) := fun N =>
    ⨆ p : Ω N × Fin (n + 1), (p.1 : Submodule ℂ (Kinf E N → ℂ)).map (mulK N (μ ^ (p.2 : ℕ)))
  have hle : ∀ (N k : ℕ) (W' : Submodule ℂ (Kinf E N → ℂ)), W' ∈ Ω N → k ≤ n → W'.map (mulK N (μ ^ k)) ≤ W N :=
    fun N k W' hW' hk => le_iSup (fun p : Ω N × Fin (n + 1) => (p.1 : Submodule ℂ (Kinf E N → ℂ)).map
      (mulK N (μ ^ (p.2 : ℕ)))) (⟨W', hW'⟩, ⟨k, Nat.lt_succ_of_le hk⟩)
  refine ⟨W, fun N => ?_, ?_⟩
  · have : ∀ p : Ω N × Fin (n + 1), FiniteDimensional ℂ
        ((p.1 : Submodule ℂ (Kinf E N → ℂ)).map (mulK N (μ ^ (p.2 : ℕ)))) := fun p => by
      have := (hΩ N).2 _ p.1.2
      infer_instance
    infer_instance
  intro a b hab s₁ s₂ Pa Pb D hc h₁ h₂ i
  have key : ∀ (k : ℕ), k ≤ n → ∀ x : Σ M : ℕ, Submodule ℂ (Sm E M),
      (0 < x.1 ∧ (x.1 = 0 ∨ ∃ K', ∃ W' ∈ Ω x.1, HasType K' W' x.2)) →
      HasKType (W (twPart (μ ^ k) x).1) (twPart (μ ^ k) x).2 := by
    rintro k hk ⟨M, V⟩ ⟨hM, h0 | ⟨K', W', hW', hT⟩⟩
    · exact absurd h0 (Nat.pos_iff_ne_zero.1 hM)
    · exact HasKType.mono (hle M k W' hW' hk) (hasKType_twist (μ ^ k) hT)
  have hmem : (⟨D.N i, D.V i⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)) ∈ parts D :=
    List.mem_ofFn.2 ⟨i, rfl⟩
  have hj := hc.join
  unfold IsJoin at hj
  rw [hj, List.mem_append, List.mem_map, List.mem_map] at hmem
  rcases hmem with ⟨x, hx, e⟩ | ⟨x, hx, e⟩
  · have := key b (by omega) x (mem_parts_of_treeParts hc.t₁ h₁ x hx)
    rw [e] at this
    exact this
  · have := key a (by omega) x (mem_parts_of_treeParts hc.t₂ h₂ x hx)
    rw [e] at this
    exact this

end PositivityTheory.Rg.BcB.F.Tail

end
end

section

noncomputable section
open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Tail.PSc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem mem_fixed_iff' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {U : Subgroup G} {v : V} : v ∈ fixed ρ U ↔ ∀ u ∈ U, ρ u v = v := by
  constructor
  · intro hv u hu
    have := hv ⟨u, hu⟩
    simpa using this
  · intro hv u
    simpa using hv u u.2

theorem actP_eq_sum (w : Pl E) (U : Subgroup (GLw a w × GLw b w)) (hUo : IsOpen (U : Set (GLw a w × GLw b w)))
    (G : H E a b → ℂ) (hG : G ∈ fixed (pairRt a b w) U) (u : GLw a w × GLw b w → ℂ) (hu : HasCompactSupport u)
    (hur : ∀ g, ∀ k ∈ U, u (g * k) = u g) :
    ∃ (S : Subgroup (GLw a w × GLw b w)) (s : Finset ((GLw a w × GLw b w) ⧸ S)),
      S ≤ U ∧ S ≤ K2 a b w ∧ S.relIndex (K2 a b w) ≠ 0 ∧ (∀ q, q ∉ s → u q.out = 0) ∧
      actP w u G = ((S.relIndex (K2 a b w) : ℕ) : ℂ)⁻¹ • ∑ q ∈ s, u q.out • pairRt a b w q.out G := by
  obtain ⟨hKo, hKc⟩ := GlobalTheory.CompanionTheory.TwistOrbit.isOpen_isCompact_pair_integral_points (E := E) a b w
  set S : Subgroup (GLw a w × GLw b w) := K2 a b w ⊓ U with hSdef
  have hSo : IsOpen (S : Set (GLw a w × GLw b w)) := hKo.inter hUo
  have hidx : S.relIndex (K2 a b w) ≠ 0 :=
    GlobalTheory.FunObj.relIndex_inf_ne_zero (N := K2 a b w) (O := U) (C := K2 a b w) hUo hKc le_rfl le_rfl
  have hfin := GlobalTheory.CompanionTheory.DiagAvg.finite_cosets S hSo u hu
  set s := hfin.toFinset with hsdef
  have hs : ∀ q, q ∉ s → u q.out = 0 := fun q hq => by
    by_contra h0
    exact hq (hfin.mem_toFinset.2 h0)
  have hGf := (mem_fixed_iff'.1 hG)
  refine ⟨S, s, inf_le_right, inf_le_left, hidx, hs, ?_⟩
  funext z
  have hr : S ≤ rStab (fun m => u m * pairRt a b w m G z) := by
    intro k hk g
    show u (g * k) * pairRt a b w (g * k) G z = u g * pairRt a b w g G z
    rw [hur g k (Subgroup.mem_inf.1 hk).2, map_mul, Module.End.mul_apply, hGf k (Subgroup.mem_inf.1 hk).2]
  rw [actP, GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ (K2 a b w) S _ inf_le_left hr hidx]
  rw [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := s) ?_]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
  · intro q hq
    by_contra hqs
    exact hq (by simp [hs q hqs])

theorem lw_actP (w : Pl E) (U : Subgroup (GLw a w × GLw b w)) (hUo : IsOpen (U : Set (GLw a w × GLw b w)))
    (G : H E a b → ℂ) (hG : G ∈ fixed (pairRt a b w) U) (u : GLw a w × GLw b w → ℂ) (hu : HasCompactSupport u)
    (hur : ∀ g, ∀ k ∈ U, u (g * k) = u g) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (GLw a w × GLw b w) Y) (Λ : (H E a b → ℂ) →ₗ[ℂ] Y)
    (hΛ : ∀ g, Λ (pairRt a b w g G) = τ g (Λ G)) (lw : Y →ₗ[ℂ] ℂ) :
    lw (Λ (actP w u G)) = hint (K2 a b w) (fun m => u m * lw (τ m (Λ G))) := by
  obtain ⟨S, s, hSU, hSK, hidx, hs, hEq⟩ := actP_eq_sum w U hUo G hG u hu hur
  have hGf := (mem_fixed_iff'.1 hG)
  have hr : S ≤ rStab (fun m => u m * lw (τ m (Λ G))) := by
    intro k hk g
    show u (g * k) * lw (τ (g * k) (Λ G)) = u g * lw (τ g (Λ G))
    rw [hur g k (hSU hk), map_mul, Module.End.mul_apply, ← hΛ k, hGf k (hSU hk)]

  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ (K2 a b w) S _ hSK hr hidx, hEq, map_smul, map_smul, map_sum, map_sum,
  smul_eq_mul]
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := s) ?_]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_smul, map_smul, hΛ, smul_eq_mul]
  · intro q hq
    by_contra hqs
    exact hq (by simp [hs q hqs])

theorem extTensor_twRep {G₁ G₂ V₁ V₂ : Type} [Group G₁] [Group G₂] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
    [Module ℂ V₂] (ρ₁ : Representation ℂ G₁ V₁) (ρ₂ : Representation ℂ G₂ V₂) (χ₁ : G₁ →* ℂˣ) (χ₂ : G₂ →* ℂˣ)
    (g : G₁ × G₂) (x : V₁ ⊗[ℂ] V₂) :
    GlobalTheory.SmGL.extTensor (twRep ρ₁ χ₁) (twRep ρ₂ χ₂) g x = (((χ₁ g.1 : ℂˣ) : ℂ) * ((χ₂ g.2 : ℂˣ) : ℂ)) •
      GlobalTheory.SmGL.extTensor ρ₁ ρ₂ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v₁ v₂ =>
    simp only [GlobalTheory.SmGL.extTensor_tmul, twRep_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_smul,
      mul_comm]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem mu_fac (μ : HChar E) (w : Pl E) (m : GLw a w × GLw b w) :
    ((μ.loc w ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂˣ) : ℂ) =
      ((μ.loc w ((-1) ^ (a * b)) : ℂˣ) : ℂ) *
        ((((((μ ^ b).loc w).comp GeneralLinearGroup.det) m.1 : ℂˣ) : ℂ) *
          (((((μ ^ a).loc w).comp GeneralLinearGroup.det) m.2 : ℂˣ) : ℂ)) := by
  have hb : ∀ x, (μ ^ b).loc w x = μ.loc w x ^ b := fun x => rfl
  have ha : ∀ x, (μ ^ a).loc w x = μ.loc w x ^ a := fun x => rfl
  simp [map_mul, map_pow, mul_assoc, hb, ha]

end PositivityTheory.Rg.BcB.F.Tail.PSc

end
end

section

noncomputable section

open scoped Classical


set_option maxSynthPendingDepth 3


namespace PositivityTheory.Rg.BcB.F.ChiPin

open PositivityTheory.Rg.BcB.F

variable {ι : Type} {H : ι → Type} [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type}

theorem chi_pin (gen : Γ → Prod' H d) (a₀ : Γ) (v : EuclideanSpace ℂ (Fin d)) (hv : v ≠ 0) (ha₀ : (gen a₀).2 v = v)
    (s : ι) (X : H s →L[ℂ] H s)
    (χ : StarAlgebra.adjoin ℂ (Set.range (fun a : StarAlgebra.adjoin ℂ (Set.range gen) => (a : Prod' H d).1 s) ∪ {X})
      →⋆ₐ[ℂ] ℂ)
    (heig : ∀ a : StarAlgebra.adjoin ℂ (Set.range gen), a.1.2 v ≠ 0 → ∃ c : ℂ, a.1.2 v = c • v ∧
      χ ⟨a.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩)⟩ = c)
    (a : StarAlgebra.adjoin ℂ (Set.range gen)) (c : ℂ) (hc : a.1.2 v = c • v) :
    χ ⟨a.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩)⟩ = c := by
  have key : ∀ b : StarAlgebra.adjoin ℂ (Set.range gen), ∀ e : ℂ, e ≠ 0 → b.1.2 v = e • v →
      χ ⟨b.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨b, rfl⟩)⟩ = e := by
    intro b e he hb
    obtain ⟨c', hc', hχ⟩ := heig b (by rw [hb]; exact smul_ne_zero he hv)
    rw [hχ]
    have h2 : (c' - e) • v = 0 := by rw [sub_smul, ← hc', ← hb, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hv)
  by_cases h0 : c = 0
  · subst h0
    let g : StarAlgebra.adjoin ℂ (Set.range gen) := ⟨gen a₀, StarAlgebra.subset_adjoin ℂ _ ⟨a₀, rfl⟩⟩
    have hg : g.1.2 v = (1 : ℂ) • v := by rw [one_smul]; exact ha₀
    have hab : (a + g).1.2 v = (1 : ℂ) • v := by
      change (a.1.2 + g.1.2) v = _
      rw [ContinuousLinearMap.add_apply, hc, hg, zero_smul, zero_add]
    have e1 := key (a + g) 1 one_ne_zero hab
    have e2 := key g 1 one_ne_zero hg
    have hsum : (⟨(a + g).1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a + g, rfl⟩)⟩ :
        StarAlgebra.adjoin ℂ (Set.range (fun a : StarAlgebra.adjoin ℂ (Set.range gen) => (a : Prod' H d).1 s) ∪ {X})) =
        ⟨a.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩)⟩ +
          ⟨g.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨g, rfl⟩)⟩ := rfl
    rw [hsum, show ∀ p q, χ (p + q) = χ p + χ q from fun p q => χ.toAlgHom.map_add p q, e2] at e1
    linear_combination e1
  · exact key a c h0 hc

end PositivityTheory.Rg.BcB.F.ChiPin

end
end
