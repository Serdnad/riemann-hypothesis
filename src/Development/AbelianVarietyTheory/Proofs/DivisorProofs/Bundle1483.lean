module

import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle041
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralAdelicCoordinatesLatticeMod
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ParabolicAtStandardWeylElement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1431
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle076
import Formalism.DoubleCosetMeasures.StatementZ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle783
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377

@[expose] public section

section

open MeasureTheory Matrix

namespace GlobalTheory
open ValuativeRel

theorem norm_addChar_nonarch {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ0 : AddChar k ℂ) (hψ : Continuous ψ0) (t : k) : ‖ψ0 t‖ = 1 := by
  apply PositivityTheory.KCo.Mod.norm_one <;> assumption

theorem schr_unitary : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (μ : @Measure (κ → k) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (w : (κ → k) × (κ → k)) (φ φ' : (κ → k) → ℂ),
      ∫ y, GlobalTheory.WeilM.schr ψ0 w φ y * (starRingEnd ℂ) (GlobalTheory.WeilM.schr ψ0 w φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ := by
  intro k _ _ _ _ _ ψ0 hψ κ _ μ hμ w φ φ'
  letI : MeasurableSpace (κ → k) := borel _
  haveI : BorelSpace (κ → k) := ⟨rfl⟩
  have h1 : ∀ s : k, ψ0 s * (starRingEnd ℂ) (ψ0 s) = 1 := fun s => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_addChar_nonarch ψ0 hψ s]; simp
  have h2 : (fun y => GlobalTheory.WeilM.schr ψ0 w φ y * (starRingEnd ℂ) (GlobalTheory.WeilM.schr ψ0 w φ' y)) =
      fun y => φ (y + w.1) * (starRingEnd ℂ) (φ' (y + w.1)) := by
    funext y
    simp only [GlobalTheory.WeilM.schr, map_mul]
    have := h1 (y ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2))
    linear_combination (φ (y + w.1) * (starRingEnd ℂ) (φ' (y + w.1))) * this
  rw [h2]
  exact integral_add_right_eq_self (fun y => φ y * (starRingEnd ℂ) (φ' y)) w.1

end GlobalTheory
end

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.raisingSpan_eq_map_span_words_of_isKMod : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), IsKMod ε σ D E → ∀ S : Submodule ℂ H, S ≤ D → raisingSpan ε σ S = (Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ S.comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x}).map D.subtype := by
  first | exact @GlobalTheory.HolDS.raisingSpan_eq_span_words | exact GlobalTheory.HolDS.raisingSpan_eq_span_words | (intros; apply GlobalTheory.HolDS.raisingSpan_eq_span_words <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm
open GlobalTheory.ArchMetricCompare GlobalTheory.ConjUnif

namespace GlobalTheory.ConjTransport

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {s s₁ : Sp ℂ ⟶ Sp B} {o : Obj D l b s} {o₁ : Obj D l b s₁}

theorem cjPt_act (m : ObjMap o₁ o cj) (x : 𝟙_ (Over (Sp ℂ)) ⟶ o.t.G) (a : 𝓞 E) :
    cjPt m.cart (x ≫ o.t.act.act a) = cjPt m.cart x ≫ o₁.t.act.act a := by
  refine pt_ext m.cart ((cjPt_comp _ _).trans ?_)
  rw [Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc (cjPt m.cart x).left, cjPt_comp]
  exact (Category.assoc _ _ _).symm

theorem cjPt_eta (m : ObjMap o₁ o cj) (a : D.La) : cjPt m.cart (o.eta a) = o₁.eta a :=
  pt_ext m.cart ((cjPt_comp _ _).trans (m.eta a).symm)

theorem cjPt_etaA (m : ObjMap o₁ o cj) (a : D.La) : cjPt m.cart (o.etaA a) = o₁.etaA a :=
  pt_ext m.cart ((cjPt_comp _ _).trans (m.etaA a).symm)

theorem exists_unif (m : ObjMap o₁ o cj) {g : ℕ} (u : HolUnif o.t.G o.t.PP.L g) {Hm : Matrix (Fin g) (Fin g) ℂ}
    {κ : u.Λ → ℂ} (hA : u.IsAH Hm κ) :
    ∃ (u₁ : HolUnif o₁.t.G o₁.t.PP.L g) (κ₁ : u₁.Λ → ℂ), u₁.IsAH (Hm.map star) κ₁ ∧
      (∀ z, z ∈ u₁.Λ ↔ star z ∈ u.Λ) ∧ ∀ z, u₁.ex z = cjPt m.cart (u.ex (star z)) := by
  obtain ⟨w, hw, -⟩ := m.lin
  obtain ⟨w', hw', -⟩ := exists_inv w hw
  have hP := pull_isLB o.t.PP.isLB m.cm.F
  exact ⟨carry (conjPull m.cart u) hP o₁.t.PP.isLB hw', _,
    carry_isAH hP o₁.t.PP.isLB hw' (conjPull_isAH m.cart u hA), fun _ => Iff.rfl, fun _ => rfl⟩

theorem herm_map_star {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    (herm (Hm.map star) z w).im = -(herm Hm (star z) (star w)).im := by
  rw [herm, herm, ← star_form]
  rfl

def conjEquiv (g : ℕ) : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := (starL' ℝ (A := Fin g → ℂ)).toLinearEquiv

theorem conjEquiv_apply {g : ℕ} (z : Fin g → ℂ) : conjEquiv g z = star z := rfl

theorem isTransport_conj {s' s₁' : Sp ℂ ⟶ Sp B} {o' : Obj D l b s'} {o₁' : Obj D l b s₁'}
    (m : ObjMap o₁ o cj) (m' : ObjMap o₁' o' cj) {g g' : ℕ}
    {u : HolUnif o.t.G o.t.PP.L g} {u' : HolUnif o'.t.G o'.t.PP.L g'}
    {u₁ : HolUnif o₁.t.G o₁.t.PP.L g} {u₁' : HolUnif o₁'.t.G o₁'.t.PP.L g'}
    {Hm : Matrix (Fin g) (Fin g) ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ}
    (hΛ : ∀ z, z ∈ u₁.Λ ↔ star z ∈ u.Λ) (hx : ∀ z, u₁.ex z = cjPt m.cart (u.ex (star z)))
    (hΛ' : ∀ z, z ∈ u₁'.Λ ↔ star z ∈ u'.Λ) (hx' : ∀ z, u₁'.ex z = cjPt m'.cart (u'.ex (star z)))
    {φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ)} (h : IsTransport o₁ o₁' u₁ u₁' (Hm.map star) (Hm'.map star) φ) :
    IsTransport o o' u u' Hm Hm' ((conjEquiv g).trans (φ.trans (conjEquiv g'))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : ∀ z, ((conjEquiv g).trans (φ.trans (conjEquiv g'))) z = star (φ (star z)) := fun _ => rfl
  refine ⟨fun z => ?_, fun a z w hw => ?_, fun z w => ?_, fun a z hz => ?_, fun a z hz => ?_⟩
  · rw [e, ← hΛ', h1, hΛ, star_star]
  · refine cjPt_injective m'.cart ?_
    rw [e, e, cjPt_act, ← hx', ← hx']
    refine h2 a _ _ ?_
    rw [hx, hx, star_star, star_star, hw, cjPt_act]
  · have := h3 (star z) (star w)
    rw [herm_map_star, herm_map_star, star_star, star_star] at this
    rw [e, e]
    exact neg_injective this
  · refine cjPt_injective m'.cart ?_
    rw [e, ← hx', cjPt_eta]
    refine h4 a _ ?_
    rw [hx, star_star, hz, cjPt_eta]
  · refine cjPt_injective m'.cart ?_
    rw [e, ← hx', cjPt_etaA]
    refine h5 a _ ?_
    rw [hx, star_star, hz, cjPt_etaA]

theorem exists_conj_obj (Xo : Moduli D l) (c : Coeff l) (y : Sp ℂ ⟶ Xo.XF c)
    (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (n : ObjMap o Xo.univ (y ≫ toX Xo c)) :
    ∃ o₁ : Obj D l (baseKA l) ((cj ≫ y) ≫ toX Xo c ≫ Xo.s),
      Nonempty (ObjMap o₁ o cj) ∧ Nonempty (ObjMap o₁ Xo.univ ((cj ≫ y) ≫ toX Xo c)) := by
  obtain ⟨o₁, ⟨m⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _
    ((cj ≫ y) ≫ toX Xo c ≫ Xo.s) cj rfl rfl
    (by rw [DetExtendZero.spMap_id, Category.comp_id, Category.assoc]) o
  obtain ⟨k, -⟩ := ObjComp.objMap_comp n m
  exact ⟨o₁, ⟨m⟩, by rw [Category.assoc cj y (toX Xo c)]; exact ⟨k⟩⟩

end GlobalTheory.ConjTransport

namespace GlobalTheory

open ConjTransport

theorem hasTransport_of_conj (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (e : c.F →+* ℂ)
    (h : HasTransport Xo c U ((starRingEnd ℂ).comp e)) : HasTransport Xo c U e := by
  rintro y y' hy hy' hU hU' o o' ⟨n⟩ ⟨n'⟩ g g' u u' Hm Hm' κ κ' hA hA'
  obtain ⟨o₁, ⟨m⟩, k⟩ := exists_conj_obj Xo c y o n
  obtain ⟨o₁', ⟨m'⟩, k'⟩ := exists_conj_obj Xo c y' o' n'
  obtain ⟨u₁, κ₁, hA₁, hΛ, hx⟩ := exists_unif m u hA
  obtain ⟨u₁', κ₁', hA₁', hΛ', hx'⟩ := exists_unif m' u' hA'
  have a : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ toF Xo c = spMap e →
      (cj ≫ y) ≫ toF Xo c = spMap ((starRingEnd ℂ).comp e) := fun y hy => by
    rw [Category.assoc, hy, DetExtendZero.spMap_comp]
  have r : ∀ y : Sp ℂ ⟶ Xo.XF c, Set.range y ⊆ U → Set.range (cj ≫ y) ⊆ U := by
    rintro y hy _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hy ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ := h (cj ≫ y) (cj ≫ y') (a y hy) (a y' hy') (r y hU) (r y' hU') o₁ o₁' k k' g g' u₁ u₁' _ _ κ₁ κ₁'
    hA₁ hA₁'
  exact ⟨_, isTransport_conj m m' hΛ hx hΛ' hx' hφ⟩

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_integral_adelic_coordinates_lattice_mod : ∀ (D : D7) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)), LatticeBasisLifts.IsLatBasis V hr β → ∀ (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ M : ℕ, 0 < M → ∃ ρ : La →+ (Fin r → LatticeBasisLifts.OAf D), (∀ (b : 𝓞 D.host.E) (a : La), ρ (b • a) = Formalism.L2.DIV.oToS D.host.F D.host.E b • ρ a) ∧ (∀ s : Fin r → LatticeBasisLifts.OAf D, ∃ (a : La) (s' : Fin r → LatticeBasisLifts.OAf D), s = ρ a + M • s') ∧ (∀ I J : Ideal (𝓞 D.host.E), I * J = Ideal.span {(M : 𝓞 D.host.E)} → ∀ a : La, (∀ i, ρ a i ∈ Formalism.L2.DIV.idS D.host.F I) → a ∈ I • (⊤ : Submodule (𝓞 D.host.E) La)) ∧ ∀ (κ : GA D V) (y : GL (Fin r) (LatticeBasisLifts.OAf D)), LatticeBasisLifts.finR V hr κ = Formalism.L2.DIV.frGL β y → ∀ a a' : La, (∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι a') = M • w) ↔ ∃ s : Fin r → LatticeBasisLifts.OAf D, y.1.mulVec (ρ a) - ρ a' = M • s := by
  first | exact @GlobalTheory.GeoActCompare.exists_lattice_coord | exact GlobalTheory.GeoActCompare.exists_lattice_coord | (intros; apply GlobalTheory.GeoActCompare.exists_lattice_coord <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift

theorem circle_eq_one_iff_of_conj {K L : Type} [Field K] [Field L] [Algebra K L] (s t : L →+* ℂ) (a b : Circle) (y : K)
    (ha : (a : ℂ) = s (algebraMap K L y)) (hb : (b : ℂ) = t (algebraMap K L y)) : b = 1 ↔ a = 1 := by
  rw [← Circle.coe_eq_one, ← Circle.coe_eq_one, ha, hb, map_eq_one_iff t t.injective, map_eq_one_iff s s.injective]

theorem logHookSum_of_bijective {D : D7} (i : Fin D.R.m) (l : D.what₂.Tau → D.what₂.Tau) (hl : Function.Bijective l) :
    logHookSum i l = logHookSum i id := by
  have hs : ∀ ρ, (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) :=
    fun ρ => D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  unfold logHookSum
  simp only [pW, qW, hs, id]
  exact hl.sum_comp (fun ρ => Real.log ((hookRows (D.R.sigW ((i : ℕ) + 1)).1 (aPl D i (D.R.sigW ((i : ℕ) + 1)).1 ρ) *
    hookRows (D.R.sigW ((i : ℕ) + 1)).2 (aMi D i (D.R.sigW ((i : ℕ) + 1)).1 (D.R.sigW ((i : ℕ) + 1)).2 ρ) : ℕ) : ℝ))

end GlobalTheory.GalLift
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.GalLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ringHom_eq_on_adjoin_simple {E : Type} [Field E] [Algebra ℚ E] (f g : E →+* ℂ) (s : E) (h : f s = g s) (x : E)
    (hx : x ∈ IntermediateField.adjoin ℚ ({s} : Set E)) : f x = g x := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact h
  | algebraMap q => simp
  | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | inv a _ ha => rw [map_inv₀, map_inv₀, ha]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]

theorem overK_iff_sqrt {D : D7} (σ : D.what₂.LL →+* ℂ) :
    OverK σ ↔ σ (D.embE D.host.sqrtMinusD) = D.what₂.embLL (D.embE D.host.sqrtMinusD) :=
  ⟨fun h => h _ (IntermediateField.mem_adjoin_simple_self ℚ D.host.sqrtMinusD),
    fun h x hx => ringHom_eq_on_adjoin_simple (σ.comp D.embE) (D.what₂.embLL.comp D.embE) D.host.sqrtMinusD h x hx⟩

theorem overK_iff_good_of_pins {D : D7} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (ha : AlgTie T) (hp : T.Q.Pins)
    (σ : D.what₂.LL →+* ℂ) : OverK σ ↔ GoodEmb T.Q.c (res T σ) := by
  have e0 := res_embLL T ha hp.2.2.1
  have h1 : D.what₂.embLL (D.embE D.host.sqrtMinusD) = T.Q.H.rt0 :=
    (RingHom.congr_fun D.embE_φ₀ D.host.sqrtMinusD).trans hp.1.2.2.1.symm
  have h2 : GoodEmb T.Q.c (res T D.what₂.embLL) := e0 ▸ T.toCore.good_σ₀
  have hx : D.embE D.host.sqrtMinusD = algebraMap T.Q.c.F D.what₂.LL
      (IntermediateField.inclusion T.Q.c.le (ReciprocityTheory.ChartRestriction.G.Geo.Tor.baseKA T.Q.l).ρ) :=
    D.what₂.embLL.injective (h1.trans (Eq.symm h2))
  refine (overK_iff_sqrt σ).trans ⟨fun h => ?_, fun h => ?_⟩
  · exact (congrArg σ hx).symm.trans (h.trans h1)
  · exact (congrArg σ hx).trans (Eq.trans h h1.symm)

end GlobalTheory.GalLift
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.DimProdLab

theorem lab_spec {D : D7} (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    labE σ (lab σ ρ) = tauE D ρ ∨ labE σ (lab σ ρ) = (starRingEnd ℂ).comp (tauE D ρ) := by
  unfold lab; rw [dite_eq_left (GlobalTheory.ConjReading.lab_exists σ ρ)]; exact (GlobalTheory.ConjReading.lab_exists σ ρ).choose_spec

theorem lab_injective {D : D7} (σ : D.what₂.LL →+* ℂ) : Function.Injective (lab σ : D.what₂.Tau → D.what₂.Tau) := by
  intro ρ ρ' h
  have cc : ∀ f : D.host.E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp f) = f := GlobalTheory.ConjReading.conj_conj
  rcases lab_spec σ ρ with h1 | h1 <;> rcases lab_spec σ ρ' with h2 | h2 <;> rw [h] at h1
  · exact Formalism.IndefR.Fock.KV.tauE_injective (h1.symm.trans h2)
  · exact absurd (h1.symm.trans h2) (Formalism.IndefR.Fock.KV.tauE_ne_conj _ _)
  · exact absurd (h2.symm.trans h1) (Formalism.IndefR.Fock.KV.tauE_ne_conj _ _)
  · have e := congrArg (fun f => (starRingEnd ℂ).comp f) (h1.symm.trans h2)
    simp only [cc] at e
    exact Formalism.IndefR.Fock.KV.tauE_injective e

theorem dimK_congr {R : Ranks} (hc : HCParam R) {a b : ℕ × ℕ} (e : a = b) :
    dimK a.1 a.2 (Formalism.L2.NTheta.kapW hc a.1 a.2) = dimK b.1 b.2 (Formalism.L2.NTheta.kapW hc b.1 b.2) := by
  subst e; rfl

theorem prod_dims (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) = ((∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ : ℝ) : ℂ) := by
  set s := D.R.sigW ((i : ℕ) + 1)
  let hd : D.what₂.Tau → ℚ := fun τ => dimK s.1 s.2 (Formalism.L2.NTheta.kapW (D.hc τ) s.1 s.2)
  have h1 : ∀ ρ, dimK _ _ (kapAt (Wc D i) σ ρ) = hd (lab σ ρ) := fun ρ =>
    dimK_congr (D.hc (lab σ ρ)) (Formalism.IndefR.Fock.KV.sig_Wc i ρ)
  have h2 : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ = ((hd τ : ℚ) : ℝ) := fun τ =>
    congrArg (fun q : ℚ => (q : ℝ)) (dimK_congr (D.hc τ) (Formalism.IndefR.Fock.KV.sig_Wc i τ))
  have hb : Function.Bijective (lab σ : D.what₂.Tau → D.what₂.Tau) := (lab_injective σ).bijective_of_finite
  simp only [h1, h2]
  refine (Equiv.prod_comp (Equiv.ofBijective _ hb) (fun τ => ((hd τ : ℚ) : ℂ))).trans ?_
  push_cast
  rfl

end GlobalTheory.DimProdLab
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL

noncomputable section
namespace GlobalTheory.ShellVan
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

theorem valuation_unif_zpow {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ϖ : kˣ} (hϖ : IsUnif ϖ) (m : ℤ) : valuation k ((ϖ ^ m : kˣ) : k) = uniformizer k ^ m := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]

theorem shell_eq_zero_of_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ), IsUnif ϖ → ∀ (ν : kˣ →* ℂˣ) (a : ℕ) (μ : Measure (GL (Fin a) k))
    (φ : Matrix (Fin a) (Fin a) k → ℂ) (M' : ℕ), Function.support φ ⊆ scaledInt ϖ a (-(M' : ℤ)) →
    ∀ n : Fin a → ℤ, ¬ (∀ i, -(M' : ℤ) ≤ n i) → ∀ z : ℂ, shell μ ϖ ν z φ n = 0 := by
  intro k _ _ _ _ _ _ ϖ hϖ ν a μ φ M' hS n hn z
  push_neg at hn
  obtain ⟨i, hi⟩ := hn
  unfold _root_.GlobalTheory.SplitFlip.shell
  refine setIntegral_eq_zero_of_forall_eq_zero fun g hg => ?_
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
  suffices h : φ (x * diagGL (fun i => ϖ ^ n i) * y).val = 0 by rw [h, zero_mul, zero_mul]
  by_contra hne
  have hmem := hS hne
  have hd : (diagGL (fun i => ϖ ^ n i)).val =
      (x⁻¹).val * (x * diagGL (fun i => ϖ ^ n i) * y).val * (y⁻¹).val := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have hx' := ((mem_KO_iff x).1 hx).2
  have hy' := ((mem_KO_iff y).1 hy).2
  have bound : ∀ r s, valuation k ((diagGL (fun i => ϖ ^ n i)).val r s) ≤
      valuation k (((ϖ ^ (-(M' : ℤ)) : kˣ) : k)) := by
    intro r s
    rw [hd, Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun t _ => ?_
    rw [map_mul, Matrix.mul_apply]
    calc _ ≤ valuation k (((ϖ ^ (-(M' : ℤ)) : kˣ) : k)) * 1 :=
          mul_le_mul' (Valuation.map_sum_le _ fun q _ => by
            rw [map_mul]
            exact (mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).1 (hx' r q))).trans (hmem q t))
            ((Valuation.mem_integer_iff _ _).1 (hy' t s))
      _ = _ := mul_one _
  have h1 := bound i i
  simp only [diagGL_val, diagonal_apply_eq] at h1
  rw [valuation_unif_zpow hϖ, valuation_unif_zpow hϖ] at h1
  have hu0 : (0 : ValueGroupWithZero k) < uniformizer k := zero_lt_iff.2 uniformizer_ne_zero
  have h2 := (zpow_le_zpow_iff_right_of_lt_one₀ hu0 uniformizer_lt_one).1 h1
  omega

theorem shell_lemma : ShellLemma := by
  intro k _ _ _ _ _ _ ϖ hϖ ν e hram hcond a μ hμ φ hφ
  have : μ.IsHaarMeasure := hμ
  have hMeas : GlobalTheory.CompanionTheory.QL.instMeasGL (K := k) a =
      (inferInstance : MeasurableSpace (GL (Fin a) k)) :=
    (_root_.GlobalTheory.SplitFlip.borel_GL (n := Fin a) (k := k)).measurable_eq.symm
  have hintAux := GlobalTheory.T.integrableOn_cartanDoubleCoset_shellIntegrand k ϖ ν e hcond a
  have hzeroAux := GlobalTheory.T.setIntegral_leftCoset_shellIntegrand_eq_zero k ϖ hϖ ν a
  rw [hMeas] at hintAux hzeroAux
  have hint := @hintAux μ hμ φ hφ
  have h2 : ∀ M : ℤ, IsPeriodic ϖ M φ → ∀ n : Fin a → ℤ, (∃ i, M ≤ n i) → ∀ z : ℂ, shell μ ϖ ν z φ n = 0 := by
    rintro M hM n ⟨i, hi⟩ z
    obtain ⟨u, hu1, hu2⟩ : ∃ u : kˣ, valuation k (u : k) = 1 ∧ ν u ≠ 1 := by
      by_contra h
      push_neg at h
      exact hram h
    obtain ⟨t, htK, heq, hdisj⟩ := GlobalTheory.T.cartanDoubleCoset_finite_disjoint_leftCosets k ϖ a n
    unfold _root_.GlobalTheory.SplitFlip.shell
    rw [heq, integral_biUnion_finset t]
    · exact Finset.sum_eq_zero fun x hx =>
        @hzeroAux μ hμ φ M hM n i hi u hu1 hu2 x (htK x hx) z
    · intro x _
      exact (isOpen_KO.preimage (continuous_const.mul continuous_id)).measurableSet
    · exact hdisj
    · intro x hx
      refine (hint n z).mono_set ?_
      rw [heq]
      exact Set.subset_biUnion_of_mem (u := fun x => {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)}) hx
  have h3 := shell_eq_zero_of_support k ϖ hϖ ν a μ φ
  refine ⟨hint, h2, h3, ?_⟩
  obtain ⟨N, M, hN, hM⟩ := GlobalTheory.SBUniform.exists_bound_period k (Fin a) φ hφ
  have hP : IsPeriodic ϖ (M : ℤ) φ := fun X Z hZ => hM X Z fun i j => by
    have := hZ i j
    rwa [valuation_unif_zpow hϖ] at this
  have hS : Function.support φ ⊆ scaledInt ϖ a (-(N : ℤ)) := fun X hX i j => by
    rw [valuation_unif_zpow hϖ]
    exact hN X hX i j
  refine ((Set.Finite.pi (t := fun _ : Fin a => Set.Ico (-(N : ℤ)) M) fun _ => Set.finite_Ico _ _).preimage
    Subtype.val_injective.injOn).subset ?_
  rintro ⟨n, hn⟩ ⟨z, hz⟩ i -
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hz (h3 N hS n (fun h' => h (h' i)) z)
  · by_contra h
    exact hz (h2 M hP n ⟨i, not_lt.1 h⟩ z)

end GlobalTheory.ShellVan
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0
open GlobalTheory.ThK.EvAt0.PolD

noncomputable section

namespace GlobalTheory.ThK.EvAt0.ZPartArc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piInf_inclR' {w : InfinitePlace F} (τ : EmbOver E w) (x : E) : piInf τ (inclR (F := F) (AF F) x) = τ.1 x := by
  simp [piInf, inclR, compInf, infEmb_tmul]

end GlobalTheory.ThK.EvAt0.ZPartArc
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.lattice_stable_almost_all_places_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (X : Spc F E n)
    (Y : Spc F E d), X.L.IsFullLattice E → ∀ M : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    Set.Finite {w : Pl (F := F) | ¬ ∀ γ ∈ latAtV X Y w, M * γ ∈ latAtV X Y w} := by
  exact @GlobalTheory.AdelMatLat.almost_all_stable
end
