import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdFlagU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocCharDR

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Loc.ordFlagU_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ) (w : HeightOneSpectrum (𝓞 L)), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a → ∀ (r : Dec (F := L) A →* GL (Fin n) (Qbar l)), Continuous r → ∀ (hh : Fin n → (L →+* Qbar l) → ℤ), (∀ τ, StrictMono fun j => hh j τ) → ∀ (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ) (ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ), (∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) → (∀ i j, i ≠ j → ω i ≠ ω j ∧ ω i ≠ ω j * absPow (w.adicCompletion L) 1) → DRat ι h r (fun τ => Finset.univ.val.map fun j => hh j τ) (fun s => ∏ j, (X - C (ω j (a s) : ℂ))) → W.HasFlag r ψ ∧ PotCrys A r := by
  intro N
  exact UpperTheory.V.Loc.ordinaryFlagOfUnlinkedCharacters
    (_root_.UpperTheory.V.Loc.hecke_char_de_rham_of_local_artin_above_l N) N.aut.berger
