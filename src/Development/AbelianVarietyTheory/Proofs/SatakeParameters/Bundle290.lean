module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle156
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle511
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle250
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle203
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle285
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle157
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle055
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle274
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle255
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle253
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle033
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle032
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle279
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle023
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DRDescent

theorem deRham_descends : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v) (h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v') (l : ℕ) [Fact l.Prime], ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (a : ℕ) (r : _root_.Formalism.ConjugateSelfDual.G K Ω →* GL (Fin a) (Qbar l)), Continuous r → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l K Ω (_root_.ReciprocityTheory.Gal.Dec (F := K) A) O), GlobalTheory.Pst.Induces Bw → ∃ (O' : Type) (_ : CommRing O') (_ : Algebra ℤ_[l] O') (_ : TopologicalSpace O') (Bw' : LocBridge l L Ω (_root_.ReciprocityTheory.Gal.Dec (F := L) A) O'), GlobalTheory.Pst.Induces Bw' ∧ Bw'.j = Bw.j ∧ (IsdRAt P Bw' ((resTo L r).comp (_root_.ReciprocityTheory.Gal.Dec (F := L) A).subtype) → IsdRAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := K) A).subtype)) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' l _ P AI hT a r hr O _ _ _ Bw hj
  obtain ⟨T⟩ := hT
  obtain ⟨LL₀, Bw', hjj, hS, hKle⟩ := GlobalTheory.AboveLRes.exists_bridge (L := L) Bw hj Bw.LL
  have hj' : GlobalTheory.Pst.Induces Bw' := fun x => by rw [hjj]; exact hj x
  refine ⟨_, _, _, _, Bw', hj', hjj, fun hc => ?_⟩
  have hcont : Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Om l))) := Units.continuous_val.comp hr
  obtain ⟨M, hM, hmem⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (_root_.Formalism.ConjugateSelfDual.G K Ω) a r hcont Bw'.LL
  obtain ⟨r₁, -, hr₁⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem r hcont M hmem
  set rE : ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A) →* GL (Fin a) ↥M.1 := r₁.comp (_root_.ReciprocityTheory.Gal.Dec (F := K) A).subtype with hrE
  have hmodE : IsModel Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := K) A).subtype) M rE := by
    refine ⟨hS.trans hM, ?_⟩
    ext g i k
    exact congrArg (fun f : _root_.Formalism.ConjugateSelfDual.G K Ω →* GL (Fin a) (Om l) =>
      ((f (g : _root_.Formalism.ConjugateSelfDual.G K Ω) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hr₁
  have hmodL : IsModel Bw' ((resTo L r).comp (_root_.ReciprocityTheory.Gal.Dec (F := L) A).subtype) M (rE.comp (GlobalTheory.AboveLRes.decRes A)) := by
    refine ⟨hM, ?_⟩
    ext g i k
    exact congrArg (fun f : _root_.Formalism.ConjugateSelfDual.G K Ω →* GL (Fin a) (Om l) =>
      ((f ((GlobalTheory.AboveLRes.decRes (K := K) A g : ↥(_root_.ReciprocityTheory.Gal.Dec (F := K) A)) : _root_.Formalism.ConjugateSelfDual.G K Ω) : GL (Fin a) (Om l)) :
        Matrix (Fin a) (Fin a) (Om l)) i k) hr₁
  have hrep := GlobalTheory.AboveLRes.repE_decRes Bw Bw' hjj hKle M rE
  have hdL : Bw'.IsdRE P M (rE.comp (GlobalTheory.AboveLRes.decRes A)) := (hmodL.isdRAt_iff P).1 hc
  have hdR' : IsDR (P.PD Bw'.Kw) (GlobalTheory.Pst.resTo (Bw.repE M rE) hKle) := by
    unfold IsDR
    rw [← hrep, Module.finrank_fin_fun]
    exact hdL
  have hdR : IsDR (P.PD Bw.Kw) (Bw.repE M rE) :=
    (GlobalTheory.Per.TiedRestrict.isDR_restrict_iff hKle (Bw.repE M rE) T).2 hdR'
  have hdK : Bw.IsdRE P M rE := by
    have := hdR
    unfold IsDR at this
    rw [Module.finrank_fin_fun] at this
    exact this
  exact ⟨M, rE, hmodE, hdK⟩

end GlobalTheory.DRDescent
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowLocal


open Formalism.IndefR.principalLevelFrame in
theorem finTyp_fixed_finiteDimensional : ∀ (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (j : ℕ) (X : RowMod D rep j) (σ : D.what₂.FT), Formalism.IndefR.principalLevelFrame.isotIn (D := D) X.ρ X.C (rep σ) ≠ ⊥ → ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ (rep σ).S ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → NG.rt D.host.E D.R.r κ f = f}) := by
  intro D rep j X σ hne N hN
  obtain ⟨Φ, ⟨hΦe, hΦC⟩, hΦne⟩ : ∃ Φ : (rep σ).S →ₗ[ℂ] X.A,
      (IsEqvA X.ρ (rep σ) Φ ∧ LinearMap.range Φ ≤ X.C) ∧ LinearMap.range Φ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hne
    unfold Formalism.IndefR.principalLevelFrame.isotIn
    exact iSup_eq_bot.2 fun Φ => iSup_eq_bot.2 fun hΦ => hcon Φ hΦ
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot]
    let S' : Submodule ℂ (GAf D.host.E D.R.r → ℂ) := (LinearMap.ker Φ).map (rep σ).S.subtype
    have hS'le : S' ≤ (rep σ).S := by
      rintro f ⟨k, _, rfl⟩
      exact k.2
    have hS'st : ∀ h, ∀ f ∈ S', NG.rt D.host.E D.R.r h f ∈ S' := by
      rintro h f ⟨k, hk, rfl⟩
      refine ⟨⟨NG.rt D.host.E D.R.r h k, (rep σ).stable h k k.2⟩, ?_, rfl⟩
      show Φ _ = 0
      rw [hΦe h k, LinearMap.mem_ker.1 hk, map_zero]
    rcases (rep σ).irr S' hS'le hS'st with h0 | hall
    · rw [eq_bot_iff]
      intro k hk
      have : (k : GAf D.host.E D.R.r → ℂ) ∈ S' := ⟨k, hk, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
    · exfalso
      apply hΦne
      rw [eq_bot_iff]
      rintro a ⟨y, rfl⟩
      have : (y : GAf D.host.E D.R.r → ℂ) ∈ S' := by rw [hall]; exact y.2
      obtain ⟨k, hk, hky⟩ := this
      rw [show y = k from Subtype.ext hky.symm]
      exact (Submodule.mem_bot ℂ).2 (LinearMap.mem_ker.1 hk)
  set F := Submodule.span ℂ {f | f ∈ (rep σ).S ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → NG.rt D.host.E D.R.r κ f = f} with hF
  set T := Submodule.span ℂ {x | x ∈ X.C ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → X.ρ κ x = x} with hT
  have := X.adm N hN
  have hFS : F ≤ (rep σ).S := Submodule.span_le.2 fun f hf => hf.1
  have hFT : ∀ f (hf : f ∈ F), Φ ⟨f, hFS hf⟩ ∈ T := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      refine Submodule.subset_span ⟨hΦC ⟨_, rfl⟩, fun κ hκ => ?_⟩
      rw [← hΦe κ]
      congr 1
      exact Subtype.ext (hx.2 κ hκ)
    | zero =>
      have : (⟨0, hFS F.zero_mem⟩ : (rep σ).S) = 0 := rfl
      rw [this, map_zero]
      exact T.zero_mem
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, hFS (F.add_mem hx hy)⟩ : (rep σ).S) = ⟨x, hFS hx⟩ + ⟨y, hFS hy⟩ := rfl
      rw [this, map_add (f := _)]
      exact T.add_mem ihx ihy
    | smul a x hx ih =>
      have : (⟨a • x, hFS (F.smul_mem a hx)⟩ : (rep σ).S) = a • ⟨x, hFS hx⟩ := rfl
      rw [this, map_smul]
      exact T.smul_mem a ih
  let g : F →ₗ[ℂ] T := LinearMap.codRestrict T (Φ ∘ₗ Submodule.inclusion hFS) (fun f => hFT f f.2)
  have hg : Function.Injective g := by
    intro a b hab
    have h1 : Φ (Submodule.inclusion hFS a) = Φ (Submodule.inclusion hFS b) := congrArg Subtype.val hab
    exact Submodule.inclusion_injective hFS (hinj h1)
  exact Module.Finite.of_injective g hg

end GlobalTheory.RowLocal

namespace GlobalTheory.RowLocal

section Asm
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem isLocS_of_irr (π : NG.FinTyp L n) (s : SplitPlace L) (W : Submodule ℂ (GAf L n → ℂ)) (hWS : W ≤ π.S)
    (hW0 : W ≠ ⊥) (hst : ∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W, NG.rt L n x f ∈ W)
    (hirr : ∀ W' : Submodule ℂ (GAf L n → ℂ), W' ≤ W →
      (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W', NG.rt L n x f ∈ W') → W' = ⊥ ∨ W' = W) :
    ∃ τ, IsLocS π.S s τ := by
  first
  | exact @_root_.GlobalTheory.blockFieldPairProjections.exists_local_component
  | exact _root_.GlobalTheory.blockFieldPairProjections.exists_local_component
  | (apply _root_.GlobalTheory.blockFieldPairProjections.exists_local_component <;> assumption)
  | (intros; apply _root_.GlobalTheory.blockFieldPairProjections.exists_local_component <;> assumption)
  | (intros; apply @_root_.GlobalTheory.blockFieldPairProjections.exists_local_component <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.blockFieldPairProjections.exists_local_component ..)

end Asm
end GlobalTheory.RowLocal

namespace GlobalTheory.RowLocal

theorem finTyp_exists_isLocS : ∀ (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (j : ℕ) (_ : RowMod D rep j) (σ : D.what₂.FT), D.what₂.isot j σ ≠ ⊥ → ∀ s : SplitPlace D.host.E, ∃ τ, IsLocS (rep σ).S s τ := by
  intro D rep j X σ hσ s
  have hB00 : X.B 0 0 = 0 := by
    have h := X.lin 0 X.C.zero_mem 0 X.C.zero_mem 0 X.C.zero_mem 1
    rw [one_smul, add_zero, one_mul] at h
    linear_combination -h
  have hne : Formalism.IndefR.principalLevelFrame.isotIn (D := D) X.ρ X.C (rep σ) ≠ ⊥ := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
    have hmem := (X.isot σ y).1 hy
    intro hbot
    rw [hbot, Submodule.mem_bot] at hmem
    apply hy0
    have h := X.φ_inner y y
    rw [hmem, hB00] at h
    exact inner_self_eq_zero.1 h
  obtain ⟨B', hlin, hherm, hpos, hinv⟩ := GlobalTheory.finTyp_invariant_form_of_isotIn D D.R.r X.A X.ρ X.C X.B X.lin X.herm X.pos
    X.stab X.inv (rep σ) hne
  obtain ⟨W, hWS, hW0, hst, hirr⟩ := GlobalTheory.T.exists_irreducible_subspace_trivialOutside_splitPlace D.host.E D.R.r (rep σ) B' hlin hherm hpos hinv (finTyp_fixed_finiteDimensional D rep j X σ hne) s
  exact isLocS_of_irr (rep σ) s W hWS hW0 hst hirr

end GlobalTheory.RowLocal

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.VTypeTame.ramified_of_isComp : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (ξ : (w.adicCompletion E)ˣ →* ℂˣ), IsComp χ w ξ → ¬ GlobalTheory.SplitWeil.IsUnram ξ → ¬ χ.UnrAt w := by
  intro E _ _ χ w ξ hξ hn hu
  have hc : IsComp χ w (χ.loc w) := ⟨GlobalTheory.HeckeComp.smooth_loc χ w, fun _ => rfl⟩
  have he : ξ = χ.loc w := GlobalTheory.HeckeComp.eq_of_isComp hc hξ
  apply hn
  intro x hx
  rw [he]
  apply hu x
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h1 := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  show Valued.v (x : w.adicCompletion E) = 1
  exact h1.eq_one_iff_eq_one.1 hx
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)), ∃ ξ, IsComp χ w ξ ∧ (∀ ξ', IsComp χ w ξ' → ξ' = ξ) ∧ (χ.IsUnitary → ∀ x, ‖((ξ x : ℂˣ) : ℂ)‖ = 1) := by
  first | exact @GlobalTheory.HeckeComp.main | exact GlobalTheory.HeckeComp.main | (intros; apply GlobalTheory.HeckeComp.main <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac

variable {X : Scheme.{0}} {N : ℕ} (ι : X ⟶ PSpace ℂ N)

theorem resG_fRatio {n : ℕ} {a g : MvPolynomial (Fin (N + 1)) ℂ} (ha : a ∈ grading ℂ N n) (hg : g ∈ grading ℂ N n)
    {W : X.Opens} (hW : W ≤ fOpen ι g) {V : (PSpace ℂ N).Opens} (hV : V ≤ Proj.basicOpen (grading ℂ N) g)
    (hWV : W ≤ ι ⁻¹ᵁ V) :
    resG X hW (fRatio ι a g ha hg) = (ι.appLE V W hWV).hom (frac (grading ℂ N) V a g ha hg hV) := by
  have e : fRatio ι a g ha hg = (ι.appLE (Proj.basicOpen (grading ℂ N) g) (fOpen ι g) le_rfl).hom
      (frac (grading ℂ N) _ a g ha hg le_rfl) := by
    unfold fRatio; rw [Scheme.Hom.app_eq_appLE]; rfl
  rw [e]
  exact (resG_appLE ι _ hW _).trans (appLE_resG ι hV hWV _).symm

theorem basicOpen_fRatio_le {n : ℕ} {a g : MvPolynomial (Fin (N + 1)) ℂ} (ha : a ∈ grading ℂ N n)
    (hg : g ∈ grading ℂ N n) : X.basicOpen (fRatio ι a g ha hg) ≤ fOpen ι a := by
  have e : X.basicOpen (fRatio ι a g ha hg) =
      ι ⁻¹ᵁ (PSpace ℂ N).basicOpen (frac (grading ℂ N) _ a g ha hg le_rfl) :=
    (Scheme.preimage_basicOpen ι _).symm
  rw [e, basicOpen_frac]
  exact ι.preimage_mono inf_le_right

variable {d n : ℕ} (f : Fin (d + 1) → MvPolynomial (Fin (N + 1)) ℂ) (hf : ∀ i, f i ∈ grading ℂ N n)

theorem isCoordFamily_fRatio (hcov : ⨆ i, fOpen ι (f i) = ⊤) :
    IsCoordFamily (fun i => fOpen ι (f i)) (fun i j => fRatio ι (f j) (f i) (hf j) (hf i)) := by
  refine { cover := hcov
           self := fun i => fRatio_self ι (f i) (hf i)
           mul := ?_
           basicOpen_le := fun i j => basicOpen_fRatio_le ι (hf j) (hf i) }
  intro i j k
  have hWV : fOpen ι (f i) ⊓ fOpen ι (f j) ≤
      ι ⁻¹ᵁ (Proj.basicOpen (grading ℂ N) (f i) ⊓ Proj.basicOpen (grading ℂ N) (f j)) :=
    fun x hx => ⟨hx.1, hx.2⟩
  rw [resG_fRatio ι (hf j) (hf i) _ inf_le_left hWV, resG_fRatio ι (hf k) (hf j) _ inf_le_right hWV,
    resG_fRatio ι (hf k) (hf i) _ inf_le_left hWV, ← map_mul]
  exact congrArg _ (frac_mul_eq (by ring))

def formMap (p : X ⟶ Sp ℂ) (hcov : ⨆ i, fOpen ι (f i) = ⊤) : X ⟶ PSpace ℂ d :=
  (isCoordFamily_fRatio ι f hf hcov).toHom p

variable (p : X ⟶ Sp ℂ) (hcov : ⨆ i, fOpen ι (f i) = ⊤)

theorem formMap_preimage (i : Fin (d + 1)) : formMap ι f hf p hcov ⁻¹ᵁ chart ℂ d i = fOpen ι (f i) :=
  (isCoordFamily_fRatio ι f hf hcov).toHom_preimage p i

theorem formMap_str : formMap ι f hf p hcov ≫ PSpace.str ℂ d = p :=
  (isCoordFamily_fRatio ι f hf hcov).toHom_str p

theorem pullRatio_formMap (i j : Fin (d + 1)) :
    pullRatio (formMap ι f hf p hcov) (fOpen ι (f i)) i (formMap_preimage ι f hf p hcov i).ge j =
      fRatio ι (f j) (f i) (hf j) (hf i) :=
  (isCoordFamily_fRatio ι f hf hcov).pullRatio_toHom p i j

theorem isAffineOpen_fOpen [IsClosedImmersion ι] {g : MvPolynomial (Fin (N + 1)) ℂ} (hg : g ∈ grading ℂ N n)
    (hn : 0 < n) : IsAffineOpen (fOpen ι g) :=
  (Proj.isAffineOpen_basicOpen (grading ℂ N) g hg hn).preimage ι

theorem isFinite_formMap [IsClosedImmersion ι] (hp : ι ≫ PSpace.str ℂ N = p) (hn : 0 < n) :
    IsFinite (formMap ι f hf p hcov) := by
  haveI := isProper_str ℂ N
  haveI := isProper_str ℂ d
  have h1 : IsProper (formMap ι f hf p hcov ≫ PSpace.str ℂ d) := by
    rw [formMap_str, ← hp]; infer_instance
  exact IsFinite.iff_isProper_and_isAffineHom.2 ⟨IsProper.of_comp _ (PSpace.str ℂ d),
    isAffineHom_of_isAffineOpen_preimage_chart _ fun i => by
      rw [formMap_preimage]; exact isAffineOpen_fOpen ι (hf i) hn⟩

theorem germ_appLE {Y : Scheme.{0}} (φ : X ⟶ Y) (U : Y.Opens) (W : X.Opens) (h : W ≤ φ ⁻¹ᵁ U) (x : X) (hx : x ∈ W)
    (s : Γ(Y, U)) : (X.presheaf.germ W x hx).hom ((φ.appLE U W h).hom s) =
      (X.presheaf.germ (φ ⁻¹ᵁ U) x (h hx)).hom ((φ.app U).hom s) := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]

theorem ratioSec_eq (i j : Fin (d + 1)) : XCover.ratioSec d i j = ratio ℂ d i j :=
  (awayToSection_mk _ 1 _).trans (frac_eq (by ring))

theorem rat_formMap [IsIntegral X] (j : Fin (d + 1)) (hg : genericPoint X ∈ fOpen ι (f 0)) :
    XCover.rat (formMap ι f hf p hcov) 0 j =
      (X.presheaf.germ (fOpen ι (f 0)) (genericPoint X) hg).hom (fRatio ι (f j) (f 0) (hf j) (hf 0)) := by
  have hmem : genericPoint X ∈ formMap ι f hf p hcov ⁻¹ᵁ XCover.chart d 0 :=
    (formMap_preimage ι f hf p hcov 0).ge hg
  rw [XCover.rat, dite_eq_left hmem, ← pullRatio_formMap ι f hf p hcov 0 j, pullRatio, germ_appLE, ratioSec_eq]


open XCover in
theorem exists_finCover_of_isFinite {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p]
    [inst : Algebra ℂ X.functionField] (hinst : inst = ffAlg p) (φ : X ⟶ PSpace ℂ d) [IsFinite φ]
    (hφ : φ ≫ PSpace.str ℂ d = p) (hgen : ∀ i, genericPoint X ∈ φ ⁻¹ᵁ XCover.chart d i) :
    IsFinCover ℂ X.functionField (crd φ) ∧ IsAffCover p (fun i => φ ⁻¹ᵁ XCover.chart d i) (rB ℂ X.functionField (crd φ)) := by
  have hrat := GlobalTheory.T.pulledBackProjCoordinateRatio_overlap_div d X φ
  have h00 : rat φ 0 0 = 1 := by
    obtain ⟨h1, h2⟩ := hrat 0 0 0 (hgen 0) (hgen 0)
    rw [div_self h1] at h2
    exact h2
  have hch := GlobalTheory.T.projective_chart_affine_cover d X φ
  have hne : ∀ I : Finset (Fin (d + 1)), genericPoint X ∈ I.inf fun i => φ ⁻¹ᵁ XCover.chart d i := by
    intro I
    induction I using Finset.induction_on with
    | empty => simp
    | insert a s _ ih => rw [Finset.inf_insert]; exact ⟨hgen a, ih⟩
  have hring : ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ y, y ∈ rB ℂ X.functionField (crd φ) I ↔
      ∃ f : Γ(X, I.inf fun i => φ ⁻¹ᵁ XCover.chart d i), (X.presheaf.germ _ (genericPoint X) (hne I)).hom f = y := by
    intro I hI y
    constructor
    · exact GlobalTheory.T.chart_function_field_integral d X p hinst φ hφ hgen I hI (hne I) y
    · rintro ⟨f, rfl⟩
      exact GlobalTheory.T.genericGerm_chartInter_integral_coordinateRatios d X p hinst φ hφ hgen I hI (hne I) f
  have h1 : crd φ 0 = 1 := Subtype.ext h00
  haveI : CharZero (fld φ) := charZero_of_injective_algebraMap (algebraMap ℂ (fld φ)).injective
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  refine ⟨IsFinCover.of_charZero ⟨?_, ?_, ?_⟩ (GlobalTheory.T.finite_projection_function_field d X p hinst φ hφ hgen) ?_,
    ⟨?_, fun I hI => hch.2 I hI, hch.1, hne, hring⟩⟩
  · intro i h
    exact (hrat 0 i i (hgen 0) (hgen i)).1 (by simpa [crd_val] using congrArg (fun z : fld φ => (z : X.functionField)) h)
  · simp only [h1, div_one]
    exact AlgebraicIndependent.of_comp (fld φ).val (GlobalTheory.T.algebraicIndependent_pulledBackProjCoordinateRatios d X p hinst φ hφ hgen)
  · simp only [h1, div_one]
    rw [eq_top_iff]
    intro z _
    have hle : fld φ ≤ (IntermediateField.adjoin ℂ (Set.range fun j : Fin d => crd φ j.succ)).map (fld φ).val := by
      show IntermediateField.adjoin ℂ _ ≤ _
      refine IntermediateField.adjoin_le_iff.2 ?_
      rintro _ ⟨j, rfl⟩
      induction j using Fin.cases with
      | zero => rw [h00]; exact one_mem _
      | succ k => exact (IntermediateField.mem_map _).2 ⟨crd φ k.succ, IntermediateField.subset_adjoin ℂ _ ⟨k, rfl⟩, rfl⟩
    obtain ⟨w, hw, hwz⟩ := (IntermediateField.mem_map _).1 (hle z.2)
    have : w = z := Subtype.ext hwz
    rwa [← this]
  · intro i
    exact GlobalTheory.T.affine_germ_subalgebra_smooth X p hinst _ (hch.2 {i} (Finset.singleton_nonempty i)) (hne {i}) _
      (hring {i} (Finset.singleton_nonempty i))
  · subst hinst
    rfl

theorem isFinCover_of_forms : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p]
    [inst : Algebra ℂ X.functionField], inst = ffAlg p → ∀ (N : ℕ) (ι : X ⟶ PSpace ℂ N), IsClosedImmersion ι →
    ι ≫ PSpace.str ℂ N = p → ∀ (n : ℕ) (f : Fin (d + 1) → MvPolynomial (Fin (N + 1)) ℂ)
    (hf : ∀ i, f i ∈ GlobalTheory.ProjSpace.grading ℂ N n), 0 < n → (⨆ i, GlobalTheory.EtProj.fOpen ι (f i) = ⊤) →
    ∀ hg : (∀ i, genericPoint X ∈ GlobalTheory.EtProj.fOpen ι (f i)), ∃ (F : IntermediateField ℂ X.functionField)
    (x : Fin (d + 1) → F), IsFinCover ℂ X.functionField x ∧
    IsAffCover p (fun i => GlobalTheory.EtProj.fOpen ι (f i)) (rB ℂ X.functionField x) ∧
    ∀ j, algebraMap F X.functionField (x j) = (X.presheaf.germ (GlobalTheory.EtProj.fOpen ι (f 0)) (genericPoint X) (hg 0)).hom
      (GlobalTheory.EtProj.fRatio ι (f j) (f 0) (hf j) (hf 0)) := by
  intro X _ p d _ inst hinst N ι hι hp n f hf hn hcov hg
  haveI : IsFinite (formMap ι f hf p hcov) := isFinite_formMap ι f hf p hcov hp hn
  have hpre := formMap_preimage ι f hf p hcov
  obtain ⟨h1, h2⟩ := exists_finCover_of_isFinite p d hinst (formMap ι f hf p hcov) (formMap_str ι f hf p hcov)
    fun i => (hpre i).ge (hg i)
  have hU : (fun i => formMap ι f hf p hcov ⁻¹ᵁ XCover.chart d i) = fun i => fOpen ι (f i) := funext hpre
  rw [hU] at h2
  exact ⟨_, _, h1, h2, fun j => rat_formMap ι f hf p hcov j (hg 0)⟩

end GlobalTheory.EtProj
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

theorem _root_.GlobalTheory.T.polarizedPair_satakeParameter_conjugatePlace : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), GlobalTheory.ContraPair.PolarizedPair π χ → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ B : Multiset ℂˣ, (CG.mk π).HasSat w B → (CG.mk π).HasSat (UpperTheory.V.Af.Bc.cPl w) (B.map fun α => α⁻¹ * (compNorm E χ).val w) := by
  first | exact @GlobalTheory.PolarizedSat.hasSat_conjPlace | exact GlobalTheory.PolarizedSat.hasSat_conjPlace | (intros; apply GlobalTheory.PolarizedSat.hasSat_conjPlace <;> assumption)
end
