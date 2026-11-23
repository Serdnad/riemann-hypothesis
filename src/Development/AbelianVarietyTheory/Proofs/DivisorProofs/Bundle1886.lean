module

public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1864
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle211
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle379
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle312
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasTypeOfMemMult
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle134
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.ExistsFundSetOrth
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.SquareLocus



theorem translate_mul_inv_isLocus : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (c : Pic A.left) (V : A.left.Opens), IsLocus c V → ∀ (T : Over S) (a : T ⟶ A), GlobalTheory.CechPic.pull (a).left c + GlobalTheory.CechPic.pull ((a)⁻¹).left c - 2 • GlobalTheory.CechPic.pull (1 : T ⟶ A).left c = 0 → IsLocus (2 • GlobalTheory.CechPic.pull (fst A T).left c) ((fst A T * (snd A T ≫ a)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a)⁻¹).left ⁻¹ᵁ V) := by
  intro S _ A _ hA c V hV T a h
  have hsq := GlobalTheory.T.theorem_of_square_cechPicard_translates S A hA c (A ⊗ T) (fst A T) (snd A T ≫ a)
  have e1 : (snd A T ≫ a)⁻¹ = snd A T ≫ a⁻¹ := (GrpObj.comp_inv _ _).symm
  have e2 : (1 : A ⊗ T ⟶ A) = snd A T ≫ (1 : T ⟶ A) := (MonObj.comp_one _).symm
  have h0 : pull (snd A T ≫ a).left c + pull (snd A T ≫ a)⁻¹.left c
      - 2 • pull (1 : A ⊗ T ⟶ A).left c = 0 := by
    rw [e1, e2, Over.comp_left, Over.comp_left, Over.comp_left, pull_comp, pull_comp, pull_comp,
      ← map_nsmul, ← map_add, ← map_sub, h, map_zero]
  have h2 : pull (fst A T * (snd A T ≫ a)).left c + pull (fst A T * (snd A T ≫ a)⁻¹).left c
      = 2 • pull (fst A T).left c := by
    rw [hsq, ← sub_eq_zero, ← h0]
    abel
  have hl := (GlobalTheory.T.nonvanishingLocus_pullback_and_vanish_into_locus.1 A.left (A ⊗ T).left (fst A T * (snd A T ≫ a)).left c V hV).add
    (GlobalTheory.T.nonvanishingLocus_pullback_and_vanish_into_locus.1 A.left (A ⊗ T).left (fst A T * (snd A T ≫ a)⁻¹).left c V hV)
  rw [h2] at hl
  exact hl

end GlobalTheory.SquareLocus
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

namespace GlobalTheory

open scoped Pointwise

namespace StarAAbar

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x :=
  D.host.φ₀.injective (by
    rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply, Complex.conj_conj])

theorem coe_smul {L : Type} [Field L] [NumberField L] (σ : Gal(L/ℚ)) (X : 𝓞 L) :
    ((σ • X : 𝓞 L) : L) = σ (X : L) := rfl

theorem bb_ne_bot {D : D7} : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h1 := D.host.𝔟_spec.1
  rw [h] at h1
  simp only [Submodule.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem conj_bb_ne_bot {D : D7} : D.host.conj • D.host.𝔟 ≠ ⊥ := by
  intro h
  apply bb_ne_bot (D := D)
  have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h
  simpa using this

theorem conj_inv_smul {D : D7} (x : 𝓞 D.host.E) : D.host.conj⁻¹ • x = D.host.conj • x := by
  have h : D.host.conj⁻¹ = D.host.conj := by
    rw [inv_eq_iff_mul_eq_one]
    exact AlgEquiv.ext fun y => conj_conj D y
  rw [h]

end StarAAbar




theorem star_mem_AA_of_mem_AAbar : ∀ {D : D7} {c : D.host.E}, c ∈ D.host.AAbar → star c ∈ D.host.AA := by
  intro D c hc
  have hJ : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 StarAAbar.bb_ne_bot
  have hJc : ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 StarAAbar.conj_bb_ne_bot

  have h1 : ∀ y ∈ D.host.conj • D.host.𝔟, c * (y : D.host.E) ∈
      ((D.host.conj • D.host.ccE : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro y hy
    have hyJ : (y : D.host.E) ∈ ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨y, hy, rfl⟩
    have := FractionalIdeal.mul_mem_mul hc hyJ
    unfold Host.AAbar at this
    rwa [mul_assoc, inv_mul_cancel₀ hJc, mul_one] at this

  have h2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c) *
      ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤
      ((D.host.ccE : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    obtain ⟨j', hj', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
    have hy : D.host.conj • j' ∈ D.host.conj • D.host.𝔟 := Ideal.smul_mem_pointwise_smul _ _ _ hj'
    obtain ⟨x, hx, hxe⟩ := (FractionalIdeal.mem_coeIdeal _).1 (h1 _ hy)
    have hxs : D.host.conj • x ∈ D.host.ccE := by
      have := (Ideal.mem_pointwise_smul_iff_inv_smul_mem).1 hx
      rwa [StarAAbar.conj_inv_smul] at this
    have key : star c * algebraMap (𝓞 D.host.E) D.host.E j' = algebraMap (𝓞 D.host.E) D.host.E (D.host.conj • x) := by
      show star c * (j' : D.host.E) = ((D.host.conj • x : 𝓞 D.host.E) : D.host.E)
      rw [StarAAbar.coe_smul, show ((x : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E x from rfl, hxe,
        map_mul, StarAAbar.coe_smul, StarAAbar.conj_conj, StarAAbar.star_eq_conj]
    rw [smul_mul_assoc, key]
    exact Submodule.smul_mem _ _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hxs, rfl⟩)
  have h3 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c) ≤ D.host.AA := by
    unfold Host.AA Host.AA0
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c)
        = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c) *
          ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
          ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hJ, mul_one]
      _ ≤ _ := by gcongr
  exact h3 (FractionalIdeal.mem_spanSingleton_self _ _)

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjHilb

theorem nonempty_antilinear {H H' Y : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H']
    (ev : H → Y → ℂ) (ev' : H' → Y → ℂ)
    (ha : ∀ a b g, ev (a + b) g = ev a g + ev b g) (hs : ∀ (z : ℂ) a g, ev (z • a) g = z * ev a g)
    (ha' : ∀ a b g, ev' (a + b) g = ev' a g + ev' b g) (hs' : ∀ (z : ℂ) a g, ev' (z • a) g = z * ev' a g)
    (hinj : Function.Injective ev) (hinj' : Function.Injective ev')
    (hx : ∀ y, ∃ x, ∀ g, ev' x g = starRingEnd ℂ (ev y g)) (hy : ∀ x, ∃ y, ∀ g, ev y g = starRingEnd ℂ (ev' x g)) :
    Nonempty (H' ≃ₗ⋆[ℂ] H) := by
  choose x hx using hx
  choose y hy using hy
  exact ⟨{ toFun := y
           invFun := x
           map_add' := fun a b => hinj (funext fun g => by rw [ha, hy, hy, hy, ha', map_add (f := _)])
           map_smul' := fun z a => hinj (funext fun g => by rw [hs, hy, hy, hs', map_mul])
           left_inv := fun a => hinj' (funext fun g => by rw [hx, hy, Complex.conj_conj])
           right_inv := fun a => hinj (funext fun g => by rw [hy, hx, Complex.conj_conj]) }⟩

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_conj_value (R : RealDat D A Ks) (hm : R.models_HW) (i : Fin D.R.m) (σ σ' : D.what₂.LL →+* ℂ)
    (c : ∀ τ, (R.MW i σ).H τ ≃ₗᵢ⋆[ℂ] (R.MW i σ').H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) τ), ∀ w, c τ ((R.MW i σ).rep τ g w) = (R.MW i σ').rep τ g (c τ w))
    (v : (R.MW i σ).Vec) (v' : (R.MW i σ').Vec) (hv : ∀ τ, (v' τ : (R.MW i σ').H τ) = c τ (v τ)) (y : (R.HW i σ').H) :
    ∃ x : (R.HW i σ).H, ∀ g, evAt R i σ v x g = starRingEnd ℂ (evAt R i σ' v' y g) := by
  obtain ⟨-, hmul⟩ := GlobalTheory.ConjMult.conj_mult R.θ (R.MW i σ') (R.MW i σ) c hc
  have hχ : (fun k => star (levChi _ (R.βW i) (R.datWp i R.triv) k)) = levChi _ (R.βW i) (R.datWp i R.triv) := by
    funext k
    rw [GlobalTheory.ConjEval.levChi_principal, star_one]
  have h1 : (R.HW i σ').e y ∈ R.Wall i σ' := (hm i _).2.1 ▸ LinearMap.mem_range_self _ y
  obtain ⟨T', hT', h2⟩ := hmul _ _ _ h1
  rw [hχ] at hT'
  obtain ⟨x, rfl⟩ : T' ∈ LinearMap.range (R.HW i σ).e := (hm i σ).2.1.symm ▸ hT'
  exact ⟨x, h2 v _ hv⟩

theorem evAt_inj (R : RealDat D A Ks) (hm : R.models_HW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec)
    (hv : IsUnitV v) : Function.Injective (evAt R i σ v) :=
  GlobalTheory.EvalInj.evAt_injective_of_ne R hm i σ v fun τ h => by
    have := hv τ
    rw [h, norm_zero] at this
    exact zero_ne_one this

theorem conj_hilbert : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → TieIn T R κ v₀ → (∀ i σ, ¬ GoodEmb T.Q.c (res T σ) → Nonempty ((R.HW i σ).H ≃ₗ⋆[ℂ] (R.HW i ((starRingEnd ℂ).comp σ)).H)) ∧ (JEvExists T R κ v₀ → JEvBar T R κ) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hM ht
  have hm := hM.HW
  have hadd : ∀ i (σ' : D.what₂.LL →+* ℂ) (u : (R.MW i σ').Vec) a b g,
      evAt R i σ' u (a + b) g = evAt R i σ' u a g + evAt R i σ' u b g := fun i σ' u a b g => by
    simp [evAt]
  have hsmul : ∀ i (σ' : D.what₂.LL →+* ℂ) (u : (R.MW i σ').Vec) (z : ℂ) a g,
      evAt R i σ' u (z • a) g = z * evAt R i σ' u a g := fun i σ' u z a g => by
    simp [evAt]
  have key : ∀ i σ, ¬ GoodEmb T.Q.c (res T σ) → ∃ v : (R.MW i σ).Vec, IsUnitV v ∧
      (∀ y, ∃ x, ∀ g, evAt R i σ v x g = starRingEnd ℂ (evAt R i _ (v₀ i ((starRingEnd ℂ).comp σ)) y g)) ∧
      ∀ x, ∃ y, ∀ g, evAt R i _ (v₀ i ((starRingEnd ℂ).comp σ)) y g = starRingEnd ℂ (evAt R i σ v x g) := by
    intro i σ hσ
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_antiunitary_intertwiner_conjugateEmbedding_models D G Pl0 T0 A T R κ v₀ hM ht i σ hσ
    obtain ⟨hsm, -⟩ := GlobalTheory.ConjMult.conj_mult R.θ (R.MW i ((starRingEnd ℂ).comp σ)) (R.MW i σ) c hc
    let v : (R.MW i σ).Vec := fun τ => ⟨(c τ).symm (v₀ i ((starRingEnd ℂ).comp σ) τ), (hsm τ _).2 (by
      rw [LinearIsometryEquiv.apply_symm_apply]; exact (v₀ i ((starRingEnd ℂ).comp σ) τ).2)⟩
    refine ⟨v, fun τ => ((c τ).symm.norm_map _).trans ((ht.hv₀ i _).norm R τ),
      exists_conj_value R hm i σ _ c hc v _ fun τ => ((c τ).apply_symm_apply _).symm,
      exists_conj_value R hm i _ σ (fun τ => (c τ).symm) (fun τ g hg w => (c τ).injective ?_) _ v fun τ => rfl⟩
    rw [hc τ g hg, (c τ).apply_symm_apply, (c τ).apply_symm_apply]
  refine ⟨fun i σ hσ => ?_, fun hJ i σ hσ hV => ?_⟩
  · obtain ⟨v, hv, hx, hy⟩ := key i σ hσ
    exact nonempty_antilinear _ _ (hadd _ _ _) (hsmul _ _ _) (hadd _ _ _) (hsmul _ _ _)
      (evAt_inj R hm i _ _ fun τ => (ht.hv₀ i _).norm R τ) (evAt_inj R hm i σ v hv) hx hy
  · obtain ⟨v, hv, hx, -⟩ := key i σ hσ
    exact ⟨v, hv, GlobalTheory.ConjEval.evEx_conj (res T σ) _ _ (hadd _ _ _) (hsmul _ _ _) (hadd _ _ _) (hsmul _ _ _)
      (evAt_inj R hm i σ v hv) hx _ (hJ i ((starRingEnd ℂ).comp σ) (good_resC T hσ) hV)⟩

end GlobalTheory.ConjHilb
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodProjLevel

section Act

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
  {L : LevDat D.host.E ℂ V.rank} {G : Type} [Group G] [Fintype G]

theorem mem_levi_flag_of_mem_parabolic (P : LevelP L.Pg L.r ℂ) {k : GA D V} (hk : k ∈ levG V β (flag1L L)) :
    k ∈ levG V β (withP L P) ∧ levChi V β (withP L P) k = levChi V β (flag1L L) k := by
  have h1 : rTup β L (finE V k) = 1 := by
    have : rTup β L (finE V k) ∈ (⊥ : Subgroup (G0 L.Pg L.r)) := hk.2.2
    exact Subgroup.mem_bot.1 this
  refine ⟨⟨hk.1, hk.2.1, ?_⟩, ?_⟩
  · show rTup β L (finE V k) ∈ P.H
    rw [h1]; exact P.H.one_mem
  · unfold levChi
    rw [levFn_withP, h1, blockDiagonalExtendByOnePrimeField_one, one_mul, levFn_flag1]

theorem isPLevel_of_hasType (hL : LiftsExist V β L) {P : LevelP L.Pg L.r ℂ} {F : GA D V → ℂ}
    (hF : HasType V β (withP L P) F) : IsPLevel V β L P F := by
  have h1 : HasType V β (flag1L L) F := fun k hk h => by
    rw [hF k (mem_levi_flag_of_mem_parabolic P hk).1, (mem_levi_flag_of_mem_parabolic P hk).2]
  refine ⟨h1, fun p => ?_⟩
  obtain ⟨κ, hκ⟩ := hL p.1
  have hp : rTup β L (finE V κ) ∈ P.H := by rw [hκ.2.2]; exact p.2
  have hm : κ ∈ levG V β (withP L P) := ⟨hκ.1, hκ.2.1, hp⟩
  have hc : levChi V β (withP L P) κ = ((P.chi p : ℂˣ) : ℂ) * levChi V β (flagL L) κ := by
    unfold levChi
    rw [levFn_withP, hκ.2.2, extendOne_of_mem _ p.2, Units.val_mul]
  have ha := levChi_ne_zero (β := β) (flagL L) κ
  funext h
  rw [level_action_spec h1 ⟨κ, hκ⟩ κ hκ h, hF κ hm, hc]
  field_simp

theorem postOn_actL_mem (g0 : G0 L.Pg L.r) {X : MMap M}
    (hT : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L))) :
    postOn M (actL V β L g0) X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) := by
  have hU : ∀ v, postOn M (actL V β L g0) X v = actG0 V β L g0 (X v) := fun _ => rfl
  by_cases hex : ∃ κ, IsLevelLift V β L g0 κ
  · have hκ := hex.choose_spec
    have e : postOn M (actL V β L g0) X = (levChi V β (flagL L) hex.choose)⁻¹ • heckeOn M {hex.choose} X := by
      ext v g
      rw [hU, actG0, dite_eq_left hex]
      simp [heckeOn, postOn_apply, heckeLin_apply]
    rw [e]
    refine Submodule.smul_mem _ _ ?_
    rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
    refine GlobalTheory.SphericalOps.isMultMap_heckeOn hT (fun k hk => ?_) fun v k hk g => ?_
    · rw [Finset.mem_singleton.1 hk]
      exact hκ.1
    · obtain ⟨h1, h2⟩ := GlobalTheory.FlagAction.conj_mem_flag1 hκ hk
      simp only [heckeLin_apply, Finset.sum_singleton]
      rw [← h2, ← hT.lev v _ h1]
      group
  · have e : postOn M (actL V β L g0) X = 0 := by
      ext v g
      rw [hU, actG0, dite_eq_right hex]
      rfl
    rw [e]
    exact zero_mem _

theorem postOn_gaL_mem_goodPart (hL : LiftsExist V β L) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ)
    (hc : ∀ g, ∑ a, c a * c (a⁻¹ * g) = c g)
    (hcomm : ∀ g F, HasType V β (flag1L L) F →
      gaL V β L eG c (actL V β L (eG g) F) = actL V β L (eG g) (gaL V β L eG c F))
    (P : LevelP L.Pg L.r ℂ) {X : MMap M}
    (hX : X ∈ Mult θ M (levG V β (withP L P) : Set (GA D V)) (levChi V β (withP L P))) :
    postOn M (gaL V β L eG c) X ∈
      goodPart θ M (levG V β (withP L P) : Set (GA D V)) (levChi V β (withP L P)) (gaL V β L eG c) := by
  have hX1 : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) :=
    GlobalTheory.ProjectedLift.mult_mono (fun k hk => mem_levi_flag_of_mem_parabolic P hk) hX
  have hY : postOn M (gaL V β L eG c) X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) := by
    have e : postOn M (gaL V β L eG c) X = ∑ g, c g • postOn M (actL V β L (eG g)) X := by
      ext v h
      simp [gaL, postOn_apply]
    rw [e]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (postOn_actL_mem _ hX1)
  rw [mem_goodPart]
  refine ⟨?_, fun v => GlobalTheory.ProjectedLift.gaL_gaL hL eG c hc (GlobalTheory.hasType_of_mem_mult θ M β _ X hX1 v)⟩
  have hY' := (GlobalTheory.MultMem.mem_mult_iff ..).1 hY
  refine (GlobalTheory.MultMem.mem_mult_iff ..).2 ⟨hY'.aut, hY'.cusp, fun v => ?_, hY'.equiv, hY'.cont⟩
  have hP := isPLevel_of_hasType hL (GlobalTheory.hasType_of_mem_mult θ M β _ X hX v)
  have hQ : IsPLevel V β L P (gaL V β L eG c (X v)) := by
    refine ⟨hY'.lev v, fun p => ?_⟩
    have e1 : actL V β L p.1 (X v) = ((P.chi p : ℂˣ) : ℂ) • X v := hP.2 p
    have e2 := hcomm (eG.symm p.1) _ hP.1
    rw [MulEquiv.apply_symm_apply, e1, map_smul] at e2
    exact e2.symm
  exact hQ.hasType

end Act

theorem proj_mem_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.grp_record → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ), ∀ U ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P)), postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A)) U ∈ R.Wat i (sg0 D A) P := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h hr hv i P U hU
  have hL : LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
    obtain ⟨c, hc⟩ := h.βW i
    refine GlobalTheory.ParahoricLift.liftsExist _ _ _ _ _ hc (fun PP hP PP' hP' => ?_) (Finset.disjoint_empty_right _)
    obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
    obtain ⟨k', hk'⟩ := (h.Pg PP').1 (hP'.resolve_right (Finset.notMem_empty _))
    exact GlobalTheory.ProjectedLift.not_isConjPl R.C.P hk hk'
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ hv
  have hc : ∀ g, ∑ a, RealDat.eC (A := A) (sg0 D A) a * RealDat.eC (A := A) (sg0 D A) (a⁻¹ * g) =
      RealDat.eC (A := A) (sg0 D A) g := by
    rw [hs]; exact GlobalTheory.ProjectedLift.eC_conv R hr
  exact postOn_gaL_mem_goodPart (L := R.datWp i R.triv) hL R.eG _ hc
    ((GlobalTheory.ProjComm.proj_comm R h hr).2 i (sg0 D A)) P hU

end GlobalTheory.GoodProjLevel

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.schurLemma_thetaFunctions_orientedPair : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (M f)) → (∀ w f, IsThetaFunO ψ S T f → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, IsThetaFunO ψ S T f → M f = c • f := by
  first | exact @GlobalTheory.ThetaSchur.schur | exact GlobalTheory.ThetaSchur.schur | (intros; apply GlobalTheory.ThetaSchur.schur <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.StableRange

theorem adeles_tensor_stableRange_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (a b : AF F ⊗[F] E),
    IsCoprime a b → ∃ t : AF F ⊗[F] E, IsUnit (a + t * b) := by
  intro F E _ _ _ _ _ a b h
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Algebra.IsIntegral (AF F) (AF F ⊗[F] E) := Algebra.IsIntegral.of_finite _ _
  exact stable_adele F a b h

end GlobalTheory.StableRange
end

section

namespace GlobalTheory.ScalarPoin

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory

theorem lintegral_kaF_lt_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x0 : Frame X.Ψ r), IsOrth X x0 → ∃ s0 : ℝ, ∀ s : ℝ, s0 ≤ s →
      ∫⁻ z, ENNReal.ofReal (kaF X x0 s z) ∂muF X x0 < ⊤ := by
  intro E _ _ _ r X x0 ho
  obtain ⟨FF, hF⟩ := GlobalTheory.MetricWeightTest.exists_fundSet_orth X ho
  have hfin := (GlobalTheory.TrueCx.covol_eq X ho hF).1
  refine ⟨4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1, fun s hs => ?_⟩
  obtain ⟨C, hC, hCb⟩ := kaUnfoldStatement_holds r X x0 ho (GlobalTheory.ClosedDiscontinuity.propDisc_closed r X) FF hF s
    (by linarith)
  have h := hCb (fun _ => 1) measurable_const (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  simp only [mul_one, lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, one_mul] at h
  exact h.trans_lt (ENNReal.mul_lt_top hC hfin)

end GlobalTheory.ScalarPoin
end
