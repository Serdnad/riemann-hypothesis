module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2599
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2600
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2593
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2595
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2596
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2467
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValuationLowerBoundHostFieldAllPlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.isPreimmersion_flat_valuationSubring_baseRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), IsBaseRing β → ∀ (W : ValuationSubring c.F) (b : O →+* W), W.subtype.comp b = β → IsPreimmersion (spMap b) ∧ Flat (spMap b) := by
  first | exact @GlobalTheory.ValLocal.preimmersion_flat | exact GlobalTheory.ValLocal.preimmersion_flat | (intros; apply GlobalTheory.ValLocal.preimmersion_flat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.exists_line_sections_externalTensorPower_fibre : ∀ (V K : Type) [CommRing V] [Field K] (f : V →+* K) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (rig : LB.Gen (L.pull (eSec G))) (θ : L.Sec) (n : ℕ) (w : Fin n → (epsR V ⟶ G)) (x : KeyIn K), L.IsLB → IsFibreOf x G L rig θ w f → ∀ N : ℕ, ∃ (X' : Scheme.{0}) (p' : X' ⟶ Sp K) (φ : X' ⟶ (pow G N).left) (L' : LB X') (b : L'.Sec), IsPullback φ p' (pow G N).hom (spMap f) ∧ L'.IsLB ∧ LBIso L' ((boxLB G L N).pull φ) ∧ ∀ s : L'.Sec, ∃ a : K, ∀ i, s.f i = constFn p' _ a * b.f i := by
  first | exact @GlobalTheory.BoxLine.sections_line | exact GlobalTheory.BoxLine.sections_line | (intros; apply GlobalTheory.BoxLine.sections_line <;> assumption)
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem crystallineCechDeRhamComparison_bijective_complexAbelian :
    ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → Function.Bijective (cmp1 (str A)) := by
  intro A _ hA
  have := hA.smooth
  have := hA.proper
  exact GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations.bijective_cechDeRhamComparison_degreeOne (str A)
    inferInstance inferInstance inferInstance

end GlobalTheory.CechPer
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.baseIdealSheafOfIdeal_spec_bijective_calculus : (∀ (C : Type) [CommRing C], Function.Bijective (fun a : Ideal C => baseIdeal (𝟙 (Spec (CommRingCat.of C))) a) ∧ (∀ a b : Ideal C, baseIdeal (𝟙 (Spec (CommRingCat.of C))) (a ⊔ b) = baseIdeal (𝟙 _) a ⊔ baseIdeal (𝟙 _) b)) ∧ (∀ (W : Scheme.{0}) (V : W.affineOpens) (C : Type) [CommRing C] (φ : Γ(W, V.1) →+* C) (J : W.IdealSheafData), J.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) = baseIdeal (𝟙 (Spec (CommRingCat.of C))) ((J.ideal V).map φ)) := by
  first | exact @GlobalTheory.FormalAlg.specIdeal | exact GlobalTheory.FormalAlg.specIdeal | (intros; apply GlobalTheory.FormalAlg.specIdeal <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.surjective_sections_mod_baseIdeal_of_closedImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R) (X Z : Scheme.{0}) (φ : X ⟶ Z) (p : Z ⟶ Spec (CommRingCat.of R)), IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) → ∀ (V : Z.Opens) (hV : IsAffineOpen V), IsAffineOpen (φ ⁻¹ᵁ V) → Function.Surjective ((Ideal.Quotient.mk (((baseIdeal p I).ideal ⟨V, hV⟩).map (φ.app V).hom)).comp (φ.app V).hom) := by
  first | exact @GlobalTheory.FormalAlg.surj_mod_baseIdeal_of_isClosedImmersion | exact GlobalTheory.FormalAlg.surj_mod_baseIdeal_of_isClosedImmersion | (intros; apply GlobalTheory.FormalAlg.surj_mod_baseIdeal_of_isClosedImmersion <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support : (∀ (R : Type) [CommRing R] (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) (J : Ideal R), (baseIdeal f J).comap π = baseIdeal (π ≫ f) J) ∧ (∀ (R C : Type) [CommRing R] [CommRing C] (φ : R →+* C) (W : Scheme.{0}) (p : W ⟶ Spec (CommRingCat.of C)) (J : Ideal R), baseIdeal (p ≫ Spec.map (CommRingCat.ofHom φ)) J = baseIdeal p (J.map φ)) ∧ (∀ (R : Type) [CommRing R] (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (J : Ideal R) (x : W), x ∈ (baseIdeal f J).support ↔ J ≤ (f x).asIdeal) := by
  first | exact @GlobalTheory.FormalAlg.baseIdeal_calculus | exact GlobalTheory.FormalAlg.baseIdeal_calculus | (intros; apply GlobalTheory.FormalAlg.baseIdeal_calculus <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.de_rham_h1_rank_primitive : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → FP R (HH1 A.hom) (2 * g) ∧ DeRhamH1Primitive A := by
  first | exact @GlobalTheory.AbCoh.rank_prim_HH1 | exact GlobalTheory.AbCoh.rank_prim_HH1 | (intros; apply GlobalTheory.AbCoh.rank_prim_HH1 <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.DetHT

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

variable {p : ℕ} [Fact p.Prime]

end Defs

def RegLocSt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : GlobalTheory.Mean4O.Cover Y) (U W : V.X.Opens), (W : Set V.X).Nonempty →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (g : V.X.functionField),
    (∀ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U →
      below (z ≫ V.j) ∈ W → e.w (TrueGeo.valAt (z ≫ V.j) g) ≤ 1) →
    ∀ x ∈ U, (V.p x).asIdeal = v.asIdeal → RegAt x g

end GlobalTheory.DetHT

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.sections_eq_sum_aeval_boundedIntCoeff_ample : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ a b : ℤ, ∃ (c : ℕ) (w : Fin (Module.finrank (ratF x) X.functionField) → X.functionField) (C : ℝ), 0 < C ∧ ∀ (q : ℕ), ∀ f ∈ P.H (e * q + a) b, ∃ T : Fin (Module.finrank (ratF x) X.functionField) → MvPolynomial (Fin (D + 1)) ℤ, (∀ i, (T i).IsHomogeneous (q + c)) ∧ f = ∑ i, MvPolynomial.aeval x (T i) * w i ∧ ∀ R κ : ℝ, 0 < κ → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, κ ≤ P.nu e 0 σ y (x l)) → (∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (e * q + a) b σ y f ≤ R) → ∀ i α, |((AddMonoidAlgebra.coeff (T i) α : ℤ) : ℝ)| ≤ C * R / κ ^ (q + c) := by
  first | exact @GlobalTheory.HSRep.sections_eq_sum_aeval_bounded | exact GlobalTheory.HSRep.sections_eq_sum_aeval_bounded | (intros; apply GlobalTheory.HSRep.sections_eq_sum_aeval_bounded <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical

theorem _root_.GlobalTheory.T.smoothForms_calculus_holomorphicAtlas : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n),
    A.IsForm 1 ∧ (∀ (c : ℂ) (α β : A.Fld), A.IsForm α → A.IsForm β → A.IsForm (α + β) ∧ A.IsForm (α * β) ∧ A.IsForm (c • α) ∧
      A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) ∧ A.del (α + β) = A.del α + A.del β ∧ A.dbar (α + β) = A.dbar α + A.dbar β ∧
      A.del (c • α) = c • A.del α ∧ A.dbar (c • α) = c • A.dbar α) ∧
    (∀ (w : A.Pt → Ev n) (β : A.Fld), A.IsForm (fld A w) → A.IsForm β →
      A.del (fld A w * β) = A.del (fld A w) * β + fld A w * A.del β ∧ A.dbar (fld A w * β) = A.dbar (fld A w) * β + fld A w * A.dbar β) ∧
    (∀ (ι : Type) (w : ι → A.Pt → Ev n) (P : MvPolynomial ι ℝ), (∀ i, A.IsForm (fld A (w i))) → A.IsForm (evalF A w P) ∧
      ((∀ i, A.del (fld A (w i)) = 0) → A.del (evalF A w P) = 0) ∧ ((∀ i, A.dbar (fld A (w i)) = 0) → A.dbar (evalF A w P) = 0)) ∧
    ∀ (M' : Type) [TopologicalSpace M'] (n' : ℕ) (A' : HolAtlas M' n') (f : M' → M), A.IsHolo A' f →
      A.pullback A' f 1 = 1 ∧ ∀ (c : ℂ) (α β : A.Fld), A.pullback A' f (α + β) = A.pullback A' f α + A.pullback A' f β ∧
        A.pullback A' f (α * β) = A.pullback A' f α * A.pullback A' f β ∧ A.pullback A' f (c • α) = c • A.pullback A' f α ∧
        (A.IsForm α → A'.IsForm (A.pullback A' f α) ∧ A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧
          A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α)) := by
  first | exact @GlobalTheory.formCalculus | exact GlobalTheory.formCalculus | (intros; apply GlobalTheory.formCalculus <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefSum.GlobalPoly

theorem vLa_pos_of_mem {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp0 : p ≠ 0)
    (hp : (p : 𝓞 K) ∈ v.asIdeal) : 0 < vLa v (p : K) := by
  have hne : (p : K) ≠ 0 := by exact_mod_cast hp0
  have hlt : v.valuation K (p : K) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 K) K) p, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hp
  have h0 : v.valuation K (p : K) ≠ 0 := by simpa using hne
  have := (WithZero.log_lt_log h0 one_ne_zero).2 hlt
  simp only [WithZero.log_one] at this
  simp only [vLa]; omega

theorem vV_of_isUnit (T : CDVR) {x : T.V} (hx : IsUnit x) : vV T.V (algebraMap T.V T.Fr x) = 0 := by
  have : valV T.V (algebraMap T.V T.Fr x) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h hx
  simp [vV, this]

theorem vV_prime_le (T : CDVR) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hv : 0 < vV T.V (p : T.Fr)) :
    vV T.V (q : T.Fr) ≤ vV T.V (p : T.Fr) := by
  by_cases hpq : q = p
  · subst hpq; exact le_rfl
  have hcop : IsCoprime ((q : ℤ)) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hpq)
  have hcopV : IsCoprime ((q : T.V)) (p : T.V) := by
    simpa using hcop.map (Int.castRingHom T.V)
  have hpm : (p : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
    by_contra h
    have hu : IsUnit (p : T.V) := by
      by_contra h'; exact h ((IsLocalRing.mem_maximalIdeal _).2 h')
    have := vV_of_isUnit T hu
    rw [map_natCast] at this; omega
  have hqu : IsUnit (q : T.V) := by
    by_contra h'
    have hqm : (q : T.V) ∈ IsLocalRing.maximalIdeal T.V := (IsLocalRing.mem_maximalIdeal _).2 h'
    obtain ⟨u, w, huw⟩ := hcopV
    have h1 : (1 : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
      rw [← huw]; exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hqm) (Ideal.mul_mem_left _ _ hpm)
    exact (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have := vV_of_isUnit T hqu
  rw [map_natCast] at this
  rw [this]; exact hv.le

end GlobalTheory.RefSum.GlobalPoly

theorem GlobalTheory.RefSum.GlobalPoly.exists_polyBetween : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (a : (D.host.E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∀ n : ℕ, ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∀ A B : ℝ, NuBetween Xo la (gap Dw a) A B → ∃ P₁ ∈ harmA (Dw := Dw) c a n, PolyBetween Xo la P₁ A B := by
  intro D H Dw l Xo c
  letI := H.starRing
  intro p hp la a ha n hn A B hNu
  obtain ⟨N, hN⟩ := exists_nat_gt (B + ∑ q ∈ D.host.condN.primeFactors,
    1 * D.host.vdH q * ((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2)
  obtain ⟨P₁, hP₁, hglob⟩ := GlobalTheory.T.exists_global_harmonic_congr_column_polynomial D.host.E H Dw l Xo c p la a ha n hn N
  refine ⟨P₁, hP₁, fun T io e ho y hy Ch k => ?_⟩
  obtain ⟨Bc, R, hcols, hR, heq⟩ := hglob T io e ho
  have hchoice := GlobalTheory.T.columnPolynomial_localDepth_eq_placeDepth D.host.E H Dw l Xo c p la T io e ho y Ch (gap Dw a) n Bc hcols k
  have hv : 0 < vV T.V (p : T.Fr) := by
    rw [← map_natCast io p, ho.2]
    exact mul_pos (by exact_mod_cast ho.1) (GlobalTheory.RefSum.GlobalPoly.vLa_pos_of_mem la.1 hp.out.ne_zero la.2)
  have hve : vV T.V (p : T.Fr) = ((vV T.V (p : T.Fr)).toNat : ℤ) := (Int.toNat_of_nonneg hv.le).symm
  have he : 0 < (vV T.V (p : T.Fr)).toNat := by omega
  have hch := GlobalTheory.PlaceInt.HostChart.chBound_host D H Dw l Xo c (fun _ => rfl) T io y Ch _ he a n
    (Formalism.L2.Pj.DF Dw a) le_rfl
  have hNu' := hNu T io e ho y
  have hpert := GlobalTheory.T.localDepth_stable_under_prime_pow_perturbation D.host.E H Dw l Xo c p T io y Ch _ he hve a n N k _ B (polyT Bc (gap Dw a)) R hch hR
    (hchoice.trans_le (hNu'.2 hy)) (by
      refine lt_of_le_of_lt (add_le_add le_rfl (Finset.sum_le_sum fun q hq => ?_)) hN
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hle := GlobalTheory.RefSum.GlobalPoly.vV_prime_le T hp.out hqp hv
      have hr : (vV T.V (q : T.Fr) : ℝ) / ((vV T.V (p : T.Fr)).toNat : ℝ) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast he)]
        rw [hve] at hle
        exact_mod_cast hle
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hr (D.host.vdH_nonneg q)) (Nat.cast_nonneg _)) zero_le_two)
  rw [heq, hpert, hchoice]
  exact ⟨hNu'.1, hNu'.2 hy⟩
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem dbarCoh_algebra : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) , DbarCoh A 1 1 ∧ (∀ w : A.Pt → Ev n, A.IsForm (fld A w) → A.dbar (fld A w) = 0 → DbarCoh A w w) ∧ ∀ (c : ℂ) (w w' z z' : A.Pt → Ev n), DbarCoh A w w' → DbarCoh A z z' → DbarCoh A (c • w) (c • w') ∧ DbarCoh A (w + z) (w' + z') ∧ DbarCoh A (w * z) (w' * z') := by
  intro M _ n A
  obtain ⟨h1, hc, hl, -, -⟩ := GlobalTheory.formCalculus M n A
  have h0 : A.IsForm 0 := by simpa using (hc 0 1 1 h1 h1).2.2.1
  have d0 : A.dbar 0 = 0 := by simpa using (hc 0 1 1 h1 h1).2.2.2.2.2.2.2.2
  have e1 : fld A 1 = 1 := rfl
  have d1 : A.dbar 1 = 0 := by
    have h := (hl 1 1 h1 h1).2
    rw [e1, mul_one, mul_one, one_mul] at h
    simpa using h
  have diag : ∀ w : A.Pt → Ev n, A.IsForm (fld A w) → A.dbar (fld A w) = 0 → DbarCoh A w w :=
    fun w hw dw => ⟨hw, hw, dw, dw, 0, h0, by rw [d0, sub_self]⟩
  refine ⟨diag 1 h1 d1, diag, ?_⟩
  rintro c w w' z z' ⟨hw, hw', dw, dw', u, hu, eu⟩ ⟨hz, hz', dz, dz', v, hv, ev⟩
  have es (x : A.Pt → Ev n) : fld A (c • x) = c • fld A x := rfl
  have ea (x y : A.Pt → Ev n) : fld A (x + y) = fld A x + fld A y := rfl
  have em (x y : A.Pt → Ev n) : fld A (x * y) = fld A x * fld A y := rfl
  have ecomm (x y : A.Pt → Ev n) : fld A x * fld A y = fld A y * fld A x := by rw [← em, ← em, mul_comm]
  have hs (α : A.Fld) (h : A.IsForm α) := (hc c α α h h).2.2.1
  have ds (α : A.Fld) (h : A.IsForm α) := (hc c α α h h).2.2.2.2.2.2.2.2
  have ha (α β : A.Fld) (h : A.IsForm α) (h' : A.IsForm β) := (hc c α β h h').1
  have hm (α β : A.Fld) (h : A.IsForm α) (h' : A.IsForm β) := (hc c α β h h').2.1
  have da (α β : A.Fld) (h : A.IsForm α) (h' : A.IsForm β) := (hc c α β h h').2.2.2.2.2.2.1
  refine ⟨⟨hs _ hw, hs _ hw', ?_, ?_, c • u, hs _ hu, ?_⟩,
    ⟨ha _ _ hw hz, ha _ _ hw' hz', ?_, ?_, u + v, ha _ _ hu hv, ?_⟩,
    ⟨hm _ _ hw hz, hm _ _ hw' hz', ?_, ?_, fld A w * v + fld A z' * u, ha _ _ (hm _ _ hw hv) (hm _ _ hz' hu), ?_⟩⟩
  · rw [es, ds _ hw, dw, smul_zero]
  · rw [es, ds _ hw', dw', smul_zero]
  · rw [es, es, ds _ hu, ← eu, smul_sub]
  · rw [ea, da _ _ hw hz, dw, dz, add_zero]
  · rw [ea, da _ _ hw' hz', dw', dz', add_zero]
  · rw [ea, ea, da _ _ hu hv, ← eu, ← ev]
    abel
  · rw [em, (hl w _ hw hz).2, dw, dz, zero_mul, mul_zero, add_zero]
  · rw [em, (hl w' _ hw' hz').2, dw', dz', zero_mul, mul_zero, add_zero]
  · rw [em, em, da _ _ (hm _ _ hw hv) (hm _ _ hz' hu), (hl w _ hw hv).2, (hl z' _ hz' hu).2, dw, dz', ← eu, ← ev,
      zero_mul, zero_mul, zero_add, zero_add, mul_sub, mul_sub, ecomm z' w, ecomm z' w']
    abel

end GlobalTheory.ChernCalc
end
