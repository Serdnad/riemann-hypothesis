module

public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.Bundle007
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
public import GroundTheory.ProfiniteCohomology.PoitouTate.PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.Bundle009
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.Bundle004
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

section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh
  GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2



theorem locTr0_B (Kf : FiniteSubfield) [NumberField Kf.1]
    [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ}
    [Fact l.Prime] (hr : 0 < r) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (inv : InvFam Kf.1 (AlgebraicClosure ℚ) l r) (hinv : PositivityTheory.PoitouTateConclusion.InvNormalised ζ inv)
    (hS : ContainsAbove S l) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod Kf.1 (AlgebraicClosure ℚ) l r)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (hρ : ContAction ρ) (d : FoundData Kf S l r ζ Av μ M ρ) [IsDiscreteRep d.A] [Finite d.A] (v : S)
    [IsDiscreteRep (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom
      (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A))]
    (E : ↥(H0 (ρ.comp (locFam S Av v))) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 0)
    (hE : ∀ (z : ↥(H0 (ρ.comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 0),
      (∀ s, cochainOf _ (cocycleι _ 0 x) s = d.eM z.1) → E z = cohomologyπ _ 0 x)
    (E' : H2 ((twDual μ ρ).comp (locFam S Av v)) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 2)
    (hE' : ∀ (z : ↥(Z2 ((twDual μ ρ).comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 2),
      (∀ s, cochainOf _ (cocycleι _ 2 x) s = d.eD (z.1 (d.ev v (s 0), d.ev v (s 1)))) → E' (Submodule.Quotient.mk z) = cohomologyπ _ 2 x)
    (a : ↥(H0 (ρ.comp (locFam S Av v)))) (b : H2 ((twDual μ ρ).comp (locFam S Av v))) :
    zmodToQZ (l ^ r) (invAt S Av μ hμ inv v (cupH0H2TwistedDual μ ρ (locFam S Av v) a b)) =
      - gsLocalInvRootsQZ (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs (l ^ r) ⟨v.1, Finset.mem_coe.2 v.2⟩ (cupPairing (ptLocalEval (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs) (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A ⟨v.1, Finset.mem_coe.2 v.2⟩) (rfl : 0 + 2 = 2) (E a) (E' b)) := by
  induction b using Submodule.Quotient.induction_on with
  | H z => ?_
  let vSet : (S : Set (HeightOneSpectrum (𝓞 Kf.1))) := ⟨v.1, Finset.mem_coe.2 v.2⟩
  let Kv := vSet.1.adicCompletion Kf.1
  let family := gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs
  let F := (family vSet).toMonoidHom
  let D := gsRoots (K := Kf) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)
  let A := Rep.res F d.A
  let B := Rep.res F (dualRep D d.A)
  let C := Rep.res F D
  let pairing := ptLocalEval family D d.A vSet
  let φ := locFam S Av v
  let _ : MulOneClass (Dec (F := Kf.1) (Av v)) :=
    (Dec (F := Kf.1) (Av v)).toGroup.toMulOneClass
  let ρ₀ := ρ.comp φ
  let ρ₂ := (twDual μ ρ).comp φ
  let ρchar := (charRep μ).comp φ
  let jp : H2 ρchar →+ QZ := (zmodToQZ (l ^ r)).comp (invAt S Av μ hμ inv v).toAddMonoidHom
  let J : cohomology C 2 →+ QZ :=
    gsLocalInvRootsQZ (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs (l ^ r) vSet
  let rel (c : ZMod (l ^ r)) (y : C.V) : Prop :=
    let root : rootsOfUnity (l ^ r)
        (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) :=
      Additive.toMul y
    root.val.val.val = ζ ^ c.val
  have hc1 : Continuous (d.ev v).toMonoidHom := (d.hev_cont v).1
  have heA := hloc2 ρ φ (d.ev v) (fun g => d.e g) d.A d.eM d.hM F (d.hev v)
  have heB := hloc2 (twDual μ ρ) φ (d.ev v) (fun g => d.e g) (dualRep D d.A) d.eD d.hD F (d.hev v)
  have hbμ (x : M) (y : TDual (ZMod (l ^ r)) M) :
      rel (evalPair x y) (pairing.hom (d.eM x ⊗ₜ[ULift.{0} ℤ] d.eD y)) :=
    d.hDζ y x
  have hJ (W : ↥(Z2 ρchar)) (x : cocycles C 2)
      (h : ∀ s, rel (W.1 (d.ev v (s 0), d.ev v (s 1))) (cochainOf C (cocycleι C 2 x) s)) :
      jp (Submodule.Quotient.mk W) = - J (cohomologyπ C 2 x) :=
    @invCmp Kf ‹_› ‹_› (S : Set (HeightOneSpectrum (𝓞 Kf.1))) inferInstance l r ‹_› hr
      (fun w hw => Finset.mem_coe.2 (hS w hw)) ζ hζ inv hinv d.ιs vSet (Av v) (hAv v)
      (d.ev v) (d.hιs v) (d.hev_cont v).1
      (cocycles2Map ρchar (muLoc Kf.1 l r (Av v)) LinearMap.id continuous_id
        (locFam_apply_eq S Av μ hμ v) W) x h
  -- Use the same local Galois group as the target pairing.
  have hTransfer := transfer_cup_degree_zero_two
    (Hv := AlgebraicClosure Kv ≃ₐ[Kv] AlgebraicClosure Kv)
    (d.ev v) hc1 ρ₀ ρ₂ ρchar evalPair continuous_of_discreteTopology
    (fun g x y => evalPair_equiv μ ρ (φ g) x y) A B C d.eM d.eD heA heB
    pairing rel hbμ E hE E' hE' jp J hJ a z
  unfold cupH0H2TwistedDual
  unfold jp J pairing ρ₀ ρ₂ ρchar A B C F D φ family Kv vSet at hTransfer
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe] at hTransfer
  with_reducible exact hTransfer

end PositivityTheory.Lit1.PTN
end
end

section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh
  GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2



theorem locTr1_C (Kf : FiniteSubfield) [NumberField Kf.1]
    [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ}
    [Fact l.Prime] (hr : 0 < r) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (inv : InvFam Kf.1 (AlgebraicClosure ℚ) l r) (hinv : PositivityTheory.PoitouTateConclusion.InvNormalised ζ inv)
    (hS : ContainsAbove S l) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod Kf.1 (AlgebraicClosure ℚ) l r)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (hρ : ContAction ρ) (d : FoundData Kf S l r ζ Av μ M ρ) [IsDiscreteRep d.A] [Finite d.A] (v : S)
    [IsDiscreteRep (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom
      (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A))]
    (E : H1 (ρ.comp (locFam S Av v)) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 1)
    (hE : ∀ (z : ↥(Z1 (ρ.comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 1),
      (∀ s, cochainOf _ (cocycleι _ 1 x) s = d.eM (z.1 (d.ev v (s 0)))) → E (Submodule.Quotient.mk z) = cohomologyπ _ 1 x)
    (E' : H1 ((twDual μ ρ).comp (locFam S Av v)) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 1)
    (hE' : ∀ (z : ↥(Z1 ((twDual μ ρ).comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 1),
      (∀ s, cochainOf _ (cocycleι _ 1 x) s = d.eD (z.1 (d.ev v (s 0)))) → E' (Submodule.Quotient.mk z) = cohomologyπ _ 1 x)
    (a : H1 (ρ.comp (locFam S Av v))) (b : H1 ((twDual μ ρ).comp (locFam S Av v))) :
    zmodToQZ (l ^ r) (invAt S Av μ hμ inv v (cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v)) b a)) =
      gsLocalInvRootsQZ (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs (l ^ r) ⟨v.1, Finset.mem_coe.2 v.2⟩ (cupPairing (ptLocalEval (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs) (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A ⟨v.1, Finset.mem_coe.2 v.2⟩) (rfl : 1 + 1 = 2) (E a) (E' b)) := by
  classical
  let places : Set (HeightOneSpectrum (𝓞 Kf.1)) := S
  let place : places := ⟨v.1, Finset.mem_coe.2 v.2⟩
  let family := gsFinFamily places d.ιs
  let localHom := (family place).toMonoidHom
  let roots := gsRoots places (l ^ r)
  let localM := Rep.res localHom d.A
  let localDual := Rep.res localHom (dualRep roots d.A)
  let localRoots := Rep.res localHom roots
  let pairing := ptLocalEval family roots d.A place
  let φ := locFam S Av v
  let ev := d.ev v
  let ρM := ρ.comp φ
  let ρD := (twDual μ ρ).comp φ
  let ρchar := (charRep μ).comp φ
  let jp := (zmodToQZ (l ^ r)).comp (invAt S Av μ hμ inv v).toAddMonoidHom
  let J := gsLocalInvRootsQZ places d.ιs (l ^ r) place
  let rel (c : ZMod (l ^ r)) (y : localRoots.V) : Prop :=
    let root : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) places) :=
      Additive.toMul y
    root.val.val.val = ζ ^ c.val
  have hc1 : Continuous ev.toMonoidHom := (d.hev_cont v).1
  have heM := hloc2 ρ φ ev (fun g => d.e g) d.A d.eM d.hM localHom (d.hev v)
  have heD := hloc2 (twDual μ ρ) φ ev (fun g => d.e g)
    (dualRep roots d.A) d.eD d.hD localHom (d.hev v)
  have hbμ (x : M) (y : TDual (ZMod (l ^ r)) M) :
      rel (evalPair x y) (pairing.hom (d.eM x ⊗ₜ[ULift.{0} ℤ] d.eD y)) :=
    d.hDζ y x
  have hJ (W : Z2 ρchar) (x : cocycles localRoots 2)
      (h : ∀ s, rel (W.1 (ev (s 0), ev (s 1))) (cochainOf localRoots (cocycleι localRoots 2 x) s)) :
      jp (Submodule.Quotient.mk W) = - J (cohomologyπ localRoots 2 x) :=
    @invCmp Kf ‹_› ‹_› places inferInstance l r ‹_› hr
      (fun w hw => Finset.mem_coe.2 (hS w hw)) ζ hζ inv hinv d.ιs place (Av v) (hAv v)
      ev (d.hιs v) hc1
      (cocycles2Map ρchar (muLoc Kf.1 l r (Av v)) LinearMap.id continuous_id
        (locFam_apply_eq S Av μ hμ v) W) x h
  have hTransfer := transfer_cup_one_one_general
    (R := ZMod (l ^ r)) (M := TDual (ZMod (l ^ r)) M) (M' := M) (P := ZMod (l ^ r)) (Q := QZ)
    ev hc1 ρD ρM ρchar evalPair.flip continuous_of_discreteTopology
    (fun g y x => evalPair_equiv μ ρ (φ g) x y) (hρ.comp' (continuous_locFam S Av v))
    localDual localM localRoots d.eD d.eM heD heM pairing rel hbμ E' hE' E hE jp J hJ a b
  -- Kernel conversion avoids a costly elaborator comparison of the cohomology types.
  run_tac Lean.Elab.Tactic.withMainContext do
    let proof ← Lean.Elab.Tactic.getFVarId (Lean.mkIdent `hTransfer)
    let goal ← Lean.Elab.Tactic.getMainGoal
    let actual ← Lean.instantiateMVars (← proof.getType)
    let expected ← Lean.instantiateMVars (← goal.getType)
    let context ← Lean.instantiateLCtxMVars (← Lean.getLCtx)
    match Lean.Kernel.isDefEq (← Lean.getEnv) context actual expected with
    | .ok true => goal.assign (.fvar proof)
    | .ok false => throwError "kernel conversion failed for the transfer result"
    | .error e => throwError "{e.toMessageData (← Lean.getOptions)}"

end PositivityTheory.Lit1.PTN
end
end

section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh
  GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2



theorem locTr2' (Kf : FiniteSubfield) [NumberField Kf.1]
    [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ}
    [Fact l.Prime] (hr : 0 < r) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (inv : InvFam Kf.1 (AlgebraicClosure ℚ) l r) (hinv : PositivityTheory.PoitouTateConclusion.InvNormalised ζ inv)
    (hS : ContainsAbove S l) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod Kf.1 (AlgebraicClosure ℚ) l r)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (hρ : ContAction ρ) (d : FoundData Kf S l r ζ Av μ M ρ) [IsDiscreteRep d.A] [Finite d.A] (v : S)
    [IsDiscreteRep (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom
      (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A))]
    (E : H2 (ρ.comp (locFam S Av v)) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 2)
    (hE : ∀ (z : ↥(Z2 (ρ.comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 2),
      (∀ s, cochainOf _ (cocycleι _ 2 x) s = d.eM (z.1 (d.ev v (s 0), d.ev v (s 1)))) → E (Submodule.Quotient.mk z) = cohomologyπ _ 2 x)
    (E' : ↥(H0 ((twDual μ ρ).comp (locFam S Av v))) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 0)
    (hE' : ∀ (z : ↥(H0 ((twDual μ ρ).comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 0),
      (∀ s, cochainOf _ (cocycleι _ 0 x) s = d.eD z.1) → E' z = cohomologyπ _ 0 x)
    (a : H2 (ρ.comp (locFam S Av v))) (b : ↥(H0 ((twDual μ ρ).comp (locFam S Av v)))) :
    zmodToQZ (l ^ r) (invAt S Av μ hμ inv v (cup20 μ ρ (locFam S Av v) a b)) =
      - gsLocalInvRootsQZ (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs (l ^ r) ⟨v.1, Finset.mem_coe.2 v.2⟩ (cupPairing (ptLocalEval (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs) (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A ⟨v.1, Finset.mem_coe.2 v.2⟩) (rfl : 2 + 0 = 2) (E a) (E' b)) := by
  classical
  induction a using Submodule.Quotient.induction_on with
  | H z => ?_
  have hc1 : Continuous (d.ev v).toMonoidHom := (d.hev_cont v).1
  have heA := hloc2 ρ (locFam S Av v) (d.ev v) (fun g => d.e g) d.A d.eM d.hM (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (d.hev v)
  have heB := hloc2 (twDual μ ρ) (locFam S Av v) (d.ev v) (fun g => d.e g)
    (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) d.eD d.hD (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (d.hev v)
  have hbμ : ∀ (x : M) (y : TDual (ZMod (l ^ r)) M),
      ((((Additive.toMul ((ptLocalEval (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs) (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A ⟨v.1, Finset.mem_coe.2 v.2⟩).hom
          (d.eM x ⊗ₜ[ULift.{0} ℤ] d.eD y)) :
        rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) :
        (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) :
        maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) =
        ζ ^ (evalPair x y).val := fun x y => d.hDζ y x
  have hJ : ∀ (W : ↥(Z2 ((charRep μ).comp (locFam S Av v))))
      (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r))) 2),
      (∀ s, ((((Additive.toMul (cochainOf _ (cocycleι _ 2 x) s) :
          rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) :
          (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) :
          maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) =
          ζ ^ (W.1 (d.ev v (s 0), d.ev v (s 1))).val) →
      ((zmodToQZ (l ^ r)).comp (invAt S Av μ hμ inv v).toAddMonoidHom) (Submodule.Quotient.mk W) =
        - gsLocalInvRootsQZ (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs (l ^ r) ⟨v.1, Finset.mem_coe.2 v.2⟩ (cohomologyπ _ 2 x) := fun W x h =>
    @invCmp Kf ‹_› ‹_› (S : Set (HeightOneSpectrum (𝓞 Kf.1))) inferInstance l r ‹_› hr (fun w hw => Finset.mem_coe.2 (hS w hw)) ζ hζ
      inv hinv d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ (Av v) (hAv v) (d.ev v) (d.hιs v) (d.hev_cont v).1
      (cocycles2Map ((charRep μ).comp (locFam S Av v)) (muLoc Kf.1 l r (Av v)) LinearMap.id continuous_id
        (locFam_apply_eq S Av μ hμ v) W) x h
  have h := transfer_cup_degree_two_zero (d.ev v) hc1 (ρ.comp (locFam S Av v)) ((twDual μ ρ).comp (locFam S Av v))
    ((charRep μ).comp (locFam S Av v)) evalPair continuous_of_discreteTopology
    (fun g x y => evalPair_equiv μ ρ (locFam S Av v g) x y)
    (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A))
    (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r))) d.eM d.eD heA heB
    (ptLocalEval (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs) (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A ⟨v.1, Finset.mem_coe.2 v.2⟩)
    (fun c y => ((((Additive.toMul y :
        rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) :
        (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) :
        maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) = ζ ^ c.val)
    hbμ E hE E' hE' ((zmodToQZ (l ^ r)).comp (invAt S Av μ hμ inv v).toAddMonoidHom)
    (gsLocalInvRootsQZ (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs (l ^ r)
      ⟨v.1, Finset.mem_coe.2 v.2⟩) hJ z b
  simp only [cup20]
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe] at h
  with_reducible assumption

end PositivityTheory.Lit1.PTN
end
end
