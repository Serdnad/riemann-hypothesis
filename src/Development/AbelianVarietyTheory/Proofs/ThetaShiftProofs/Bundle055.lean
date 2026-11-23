module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointUniqueAndBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsHomogeneousOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle026
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingThick
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle054
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArchimedeanUniqueness.MetricDef
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle019
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle028
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle045
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle026
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle072
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle040
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle027
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle036
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExponentialFamilyDerivSumsAtPeriod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.ArcQ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_letters_equivariant (h1 : Out.Laws) (h2 : Out.Laws2) (hev : GlobalTheory.Reg.EvLaws Xo c)
    {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} (hY : Mono Y.j)
    {K₁ : Type} [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)] {b₀ : O →+* K₁} {A : ArcIn Dw l β K₁ b₀}
    {χ : Sp (PowerSeries K₁) ⟶ Y.X} (W : Wit Y A χ)
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt A.D₀ (epsR K₁)) (th : A.D₀.P.L.Sec) (hth : ThNZ th)
    (ζ : K₁) (y₀ yF : FrPt Xo c (ArcS Dw K₁)) (hy₀ : IsArcFr W e th (arcι Dw K₁) y₀)
    (hchg : FrChg (letM Dw K₁) (cst Dw ζ) y₀ yF)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c) (hF : F ∈ sec Xo c a n)
    (T : Type) [Field T] (φ ψ : ArcS Dw K₁ →+* T) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T)
    (hφψ : ∀ g : LaurentSeries K₁, φ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) _ (MvPolynomial.C g)) =
      ψ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) _ (MvPolynomial.C g)))
    (hb : ∀ τ i j, i < j → b τ i j = 0)
    (hX : ∀ τ i k, ψ (arcX Dw K₁ τ i k) = ∑ j, b τ i j * φ (arcX Dw K₁ τ j k)) :
    ψ (evR Xo c F yF) = (∏ τ, ∏ i, b τ i i ^ a (τ, (i : ℕ))) * φ (evR Xo c F yF) := by
  have : CharZero K₁ := charZero_of_injective_algebraMap (algebraMap c.F K₁).injective
  obtain ⟨hdom, -, -, hconst⟩ := GlobalTheory.ArcConst.algebraic_const E H Dw K₁
  obtain ⟨f₀, hf₀⟩ := hconst c.F (algebraMap c.F (ArcS Dw K₁))
  have hι : φ.comp (arcι Dw K₁) = ψ.comp (arcι Dw K₁) := RingHom.ext fun p => hφψ _
  letI : Algebra c.F T := (φ.comp (algebraMap c.F (ArcS Dw K₁))).toAlgebra
  let φ' : ArcS Dw K₁ →ₐ[c.F] T := { φ with commutes' := fun _ => rfl }
  let ψ' : ArcS Dw K₁ →ₐ[c.F] T :=
    { ψ with
      commutes' := fun r => by
        change ψ (algebraMap c.F (ArcS Dw K₁) r) = φ (algebraMap c.F (ArcS Dw K₁) r)
        rw [hf₀]
        exact (RingHom.congr_fun hι _).symm }
  obtain ⟨y₁, hy₁⟩ := hev.bc _ _ φ' y₀
  obtain ⟨y₂, hy₂⟩ := hev.bc _ _ ψ' y₀
  obtain ⟨z₁, hz₁⟩ := hev.bc _ _ φ' yF
  obtain ⟨z₂, hz₂⟩ := hev.bc _ _ ψ' yF
  have hS := GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c O β Y K₁ b₀ A χ W e th hth _ _ y₀ hy₀
  have a₁ : IsArcFr W e th (φ.comp (arcι Dw K₁)) y₁ := hS.2 hY T φ' y₁ hy₁
  have a₂ : IsArcFr W e th (ψ.comp (arcι Dw K₁)) y₂ := hS.2 hY T ψ' y₂ hy₂
  rw [← hι] at a₂
  obtain rfl : y₂ = y₁ :=
    (GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c O β Y K₁ b₀ A χ W e th hth _ _ y₁ a₁).1 hY y₂ a₂
  have cS := GlobalTheory.Frames.frChg_calculus E H Dw l Xo c (ArcS Dw K₁)
  have cT := GlobalTheory.Frames.frChg_calculus E H Dw l Xo c T
  have c₁ := (cS.2.2.1 T φ' _ _ _ _ _ _ hchg hy₁).1 hz₁
  have c₂ := (cS.2.2.1 T ψ' _ _ _ _ _ _ hchg hy₂).1 hz₂
  have hM : ∀ τ, (letM Dw K₁ τ).map ψ' = b τ * (letM Dw K₁ τ).map φ' := fun τ => by
    ext i k
    exact hX τ i k
  have hζ : ψ' (cst Dw ζ) = 1 * φ' (cst Dw ζ) := by
    rw [one_mul]
    exact (RingHom.congr_fun hι _).symm
  rw [funext hM, hζ] at c₂
  have c₃ : FrChg b 1 z₁ z₂ := (cT.1 _ b _ 1 _ _ _ c₁).2 c₂
  have hbu : ∀ τ i, b τ i i ≠ 0 := fun τ i => by
    have hu := ((GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c T b 1 z₁).2.2.1 z₂ c₃).1 τ
    have htri : (b τ).IsLowerTriangular := fun i j hij => hb τ i j hij
    exact (htri.det_ne_zero_iff.mp hu.ne_zero) i
  let t : Ix Dw → Tˣ := fun o => match o with
    | none => 1
    | some x => Units.mk0 (b x.1 x.2 x.2) (hbu x.1 x.2)
  have hbor : FrBor t z₁ z₂ := (cT.2.2.2 t z₁ z₂).2 ⟨b, fun _ _ => rfl, hb, c₃⟩
  have eS := (GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hev a n F hF (ArcS Dw K₁)).1
  have eT := ((GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hev a n F hF T).2 inferInstance).1 t z₁ z₂ hbor
  rw [eS T φ' yF z₁ hz₁, eS T ψ' yF z₂ hz₂] at eT
  have hw : wchar (ex Dw a n) t = ∏ τ, ∏ i, b τ i i ^ a (τ, (i : ℕ)) := by
    rw [wchar, Fintype.prod_option, Fintype.prod_sigma]
    simp [t, ex]
  rw [hw] at eT
  exact eT

theorem ArcDatum.exists_normal_tangent (h1 : Out.Laws) (h2 : Out.Laws2)
    {K₁ : Type} [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)] (d : ArcDatum Xo c K₁) :
    ∃ (ζ : K₁) (e₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt (d.a.restrict (c.V d.Wp).subtype).D₀ (epsR K₁))
      (y₀ : FrPt Xo c (ArcS Dw K₁)), IsArcFr d.W e₀ d.th (arcι Dw K₁) y₀ ∧
        FrChg (letM Dw K₁) (cst Dw ζ) y₀ d.yF := by
  obtain ⟨ζ, -, -, -, -, e₀, y₀, -, hy₀, hc⟩ := GlobalTheory.ArcQ.exists_normalForm h1 h2 E H Dw l Xo c K₁ d
  exact ⟨ζ, e₀, y₀, hy₀, hc⟩

theorem evR_arc_isHomogeneous : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (K₁ : Type) [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)] (d : ArcDatum Xo c K₁) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), F ∈ sec Xo c a n → ∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁), algebraMap _ (ArcS Dw K₁) P = evR Xo c F d.yF ∧ P.IsHomogeneous (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ))) := by
  intro h1 h2 E _ _ _ H Dw l Xo c hev K₁ _ _ _ d a n F hF
  obtain ⟨ζ, e₀, y₀, hy₀, hc⟩ := d.exists_normal_tangent h1 h2
  have hth : ThNZ d.th := by
    obtain ⟨_, _, _, _, hne, -⟩ := d.isArc3
    exact (GlobalTheory.ThetaOverField.nonzero_generates h1 h2 K₁ _ d.th).1.1 hne
  exact GlobalTheory.BorelAlg.exists_isHomogeneous_of_equivariant E H Dw K₁ a _ fun T _ φ ψ b hφψ hb hX =>
    evR_letters_equivariant h1 h2 hev (GlobalTheory.ThetaShiftProofs.mono_j d.Y (mono_spMap_subtype _)) d.W e₀ d.th hth ζ y₀ d.yF hy₀ hc
      a n F hF T φ ψ b hφψ hb hX

end GlobalTheory.ArcQ
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.arcFramedPoint_unique_and_baseChange :
    Out.Laws → Out.Laws2 →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
      (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
      (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
      (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
      (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ)
      (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th : a.D₀.P.L.Sec),
    ThNZ th →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι : PowerSeries A →+* S) (y : FrPt Xo c S),
    GlobalTheory.ArcQ.IsArcFr W e th ι y →
      (Mono Y.j → ∀ y', GlobalTheory.ArcQ.IsArcFr W e th ι y' → y' = y) ∧
      (Mono Y.j → ∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y₁ : FrPt Xo c T),
        FrMap φ y y₁ → GlobalTheory.ArcQ.IsArcFr W e th (φ.toRingHom.comp ι) y₁) :=
  @GlobalTheory.ArcQ.isArcFr_unique_baseChange
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ArcQ

theorem exists_generic_lift {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {k : Type} [Field k] (bF : c.F →+* k) {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) (χ : Sp (PowerSeries k) ⟶ Y.X)
    (hχ : χ ≫ Y.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp β))
    {S : Type} [CommRing S] [Nontrivial S] (ι : PowerSeries k →+* S) (hι : IsUnit (ι PowerSeries.X))
    (z : Sp S ⟶ Xo.XF c) (hz : z ≫ Y.j = spMap ι ≫ χ) :
    ∃ y : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c, y ≫ Y.j = Out.jK (PowerSeries k) ≫ χ ∧
      y ≫ pullback.snd _ _ = Out.jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF := by
  have := Y.jQ_open
  have w : (Out.jK (PowerSeries k) ≫ χ) ≫ Y.s =
      (Out.jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF) ≫ spMap β := by
    rw [Category.assoc, hχ, spMap_comp]; simp only [Category.assoc]
  obtain ⟨q⟩ : Nonempty (Sp S) := (inferInstance : Nonempty (PrimeSpectrum S))
  have hq : PowerSeries.X ∉ (spMap ι q).asIdeal := fun h =>
    q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show ι PowerSeries.X ∈ q.asIdeal from h) hι)
  obtain ⟨p₀, hp₀⟩ := mem_range_jK _ hq
  have hr : Set.range (pullback.lift _ _ w) ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = p₀ := Subsingleton.elim (α := PrimeSpectrum (FractionRing (PowerSeries k))) _ _
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, hp₀,
      ← Scheme.Hom.comp_apply, ← hz, Scheme.Hom.comp_apply]
    exact GlobalTheory.ThetaShiftProofs.j_mem_abLocus Y _
  have hy := IsOpenImmersion.lift_fac Y.jQ _ hr
  refine ⟨IsOpenImmersion.lift Y.jQ _ hr, ?_, ?_⟩
  · unfold Model.j
    rw [← Category.assoc, hy, pullback.lift_fst]
  · rw [← Y.jQ_over, ← Category.assoc, hy, pullback.lift_snd]

theorem isArcFr_eq_of_overBase : Out.Laws → Out.Laws2 → Out.Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn Dw l (RingHom.id c.F) k bF) (V V' : ValuationSubring ℂ) (Y : Model Xo c (c.V V).subtype) (Y' : Model Xo c (c.V V').subtype) (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : Wit Y (a.restrict (c.V V).subtype) χ) (W' : Wit Y' (a.restrict (c.V V').subtype) χ'), χ ≫ Y.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp (c.V V).subtype) → χ' ≫ Y'.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp (c.V V').subtype) → ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR k)) (th : a.D₀.P.L.Sec), ThNZ th → ∀ (S : Type) [CommRing S] [Algebra c.F S] [Nontrivial S] (ι : PowerSeries k →+* S) (y y' : FrPt Xo c S), IsUnit (ι PowerSeries.X) → IsArcFr W e th ι y → IsArcFr W' e th ι y' → y = y' := by
  intro h1 h2 h5 E _ _ _ H Dw l Xo c k _ bF a V V' Y Y' χ χ' W W' hχ hχ' e th hth S _ _ _ ι y y' hι hy hy'
  have hj : Mono Y.j := GlobalTheory.ThetaShiftProofs.mono_j Y (mono_spMap_subtype _)
  have hj' : Mono Y'.j := GlobalTheory.ThetaShiftProofs.mono_j Y' (mono_spMap_subtype _)
  have hy_lift := hy
  have hy'_lift := hy'
  obtain ⟨z, _, _, _, _, hz, _⟩ := hy_lift
  obtain ⟨z', _, _, _, _, hz', _⟩ := hy'_lift
  obtain ⟨y₀, a₁, a₂⟩ := exists_generic_lift bF Y χ hχ ι hι z hz
  obtain ⟨y₀', b₁, b₂⟩ := exists_generic_lift bF Y' χ' hχ' ι hι z' hz'
  obtain ⟨rfl, hψ⟩ := GlobalTheory.arc_rigidity_two_models_of_mono h1 h2 h5 E H Dw l Xo c k bF a _ _ _ _ Y Y' χ χ' W W' y₀ y₀' a₁ b₁ a₂ b₂
  obtain ⟨ψ, hψ⟩ := hψ hj
  have hy₁ := GlobalTheory.ArcQ.isArcFr_of_agree h1 h2 E H Dw l Xo c k bF a _ _ _ _ Y Y' χ χ' W W' ψ hψ y₀ a₁ b₁ hj e th hth S ι y hι hy
  exact (GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c _ _ Y' k _ _ χ' W' e th hth S ι y' hy').1 hj' y hy₁

end GlobalTheory.ArcQ
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

private theorem prod_option_eq_prod_isSome_of_none_eq_one {V M : Type} [Fintype V] [CommMonoid M] {g : ℕ} (k : V → Option (Fin g))
    (F : V → Option (Fin g) → M) (h1 : ∀ v, F v none = 1) :
    ∏ v, F v (k v) = ∏ w : {v // (k v).isSome = true}, F w.1 (some ((k w.1).get w.2)) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun v => (k v).isSome = true) (fun v => F v (k v))]
  have h2 : ∏ w : {v // ¬ (k v).isSome = true}, F w.1 (k w.1) = 1 := by
    refine Finset.prod_eq_one (fun w _ => ?_)
    have hw : k w.1 = none := by simpa using w.2
    rw [hw, h1]
  rw [h2, _root_.mul_one]
  refine Finset.prod_congr rfl (fun w _ => ?_)
  rw [Option.some_get]

private theorem mLine_prodPow_option_elim_eq_prodPow_isSome {K : Type} [Field K] [NumberField K] {g : ℕ} (ℓ : Fin g → MLine K)
    {V : Type} [Fintype V] (k : V → Option (Fin g)) (mu : V → ℕ) :
    MLine.prodPow (fun v => (k v).elim MLine.one ℓ) mu =
      MLine.prodPow (fun w : {v // (k v).isSome = true} => ℓ ((k w.1).get w.2)) (fun w => mu w.1) := by
  unfold MLine.prodPow
  congr 1
  · exact prod_option_eq_prod_isSome_of_none_eq_one k (fun v o => (o.elim MLine.one ℓ).I ^ mu v) (fun v => by simp [MLine.one])
  · funext σ
    exact prod_option_eq_prod_isSome_of_none_eq_one k (fun v o => (o.elim MLine.one ℓ).n σ ^ mu v) (fun v => by simp [MLine.one])

theorem ndeg_line_option_le {K : Type} [Field K] [NumberField K] {g : ℕ} (abelian₂ : MLine K) (ℓ : Fin g → MLine K)
    (de : MLine K) (La logOm : ℝ) {V : Type} [Fintype V] (k : V → Option (Fin g)) (mu : V → ℕ) (n G : ℕ)
    (h : CMNumbers0 abelian₂ ℓ de La logOm) (hG : g ≤ G) :
    ((de.pow n).tensor (MLine.prodPow (fun v => (k v).elim MLine.one ℓ) mu).dual).Good ∧
    ((de.pow n).tensor (MLine.prodPow (fun v => (k v).elim MLine.one ℓ) mu).dual).ndeg ≤
      (pDeg logOm + (1 / 2) * Real.log La) * (((∑ v, mu v : ℕ) : ℝ) + ((G * n : ℕ) : ℝ)) := by
  rw [mLine_prodPow_option_elim_eq_prodPow_isSome ℓ k mu]
  have hN := degree_norm_base K g abelian₂ ℓ de La logOm {v // (k v).isSome = true} (fun w => (k w.1).get w.2)
    (fun w => mu w.1) n h
  have hLa : 1 ≤ La := h.2.2.2.1
  have hP : 0 ≤ pDeg logOm + (1 / 2) * Real.log La := by
    have h0 := Real.log_nonneg hLa
    have h1 := abs_nonneg logOm
    unfold pDeg
    linarith
  refine ⟨hN.1, le_trans hN.2 (mul_le_mul_of_nonneg_left ?_ hP)⟩
  have hs : ∑ w : {v // (k v).isSome = true}, (mu w.1 : ℝ) ≤ ∑ v, (mu v : ℝ) := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun v => (k v).isSome = true) (fun v => (mu v : ℝ))]
    have h0 : 0 ≤ ∑ w : {v // ¬ (k v).isSome = true}, (mu w.1 : ℝ) :=
      Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    linarith
  have hgG : (g : ℝ) * n ≤ (G : ℝ) * n :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hG) (Nat.cast_nonneg n)
  push_cast
  linarith

theorem valLine_ndeg_le : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (logOm : ℝ) (mo : ArcLt Dw →₀ ℕ) (n : ℕ), 1 ≤ La → LamDegSt H logOm → (s.valLine mo n).Good ∧ (s.valLine mo n).ndeg ≤ (pDeg logOm + (1 / 2) * Real.log La) * (((∑ v, mo v : ℕ) : ℝ) + ((Module.finrank ℚ E / 2 * (Dw.p + Dw.q) * n : ℕ) : ℝ)) := by
  intro hK E _ _ _ H Dw l c K₁ _ _ _ a e th jj n' La c₁ s logOm mo n hLa hdeg
  letI := H.starRing
  have hcm := cmNumbers_of_good hK E H l c (Dw.p - 1) (Dw.q - 1) (Module.finrank ℚ E / 2) s.toCMPart.obj La logOm
    (fun _ => rfl) s.good s.L s.L_good hLa hdeg
  have hg : a.D₀.P.g ≤ Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
    have h9 : a.D₀.P.g = Module.finrank ℚ E / 2 * (Dw.p - 1 + (Dw.q - 1)) := s.good.2.2.2.2.2.2.2.2.1
    rw [h9]
    apply Nat.mul_le_mul_left
    omega
  exact ndeg_line_option_le (K := K₁) s.LamL s.L.ℓ s.Tl.dual La logOm (fun v : ArcLt Dw => s.kind v.1 v.2.2) mo n
    (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) hcm hg

end GlobalTheory.ArcCM
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries ComplexOrder

namespace GlobalTheory.ArcCM.NormTie

theorem isThNormAt_of_keyArchAt {K K' : Type} [Field K] [NumberField K] [Field K'] {x : KeyIn K} {T abelian₂ : MLine K}
    {σ : K →+* ℂ} (h : KeyArchAt x T abelian₂ σ) (y : KeyIn K') (τ : K' →+* ℂ)
    (hy : ∀ z : KeyIn ℂ, KeyPB z x σ → KeyPB z y τ) : Arch.IsThNormAt y.P y.rig y.th τ (T.n σ ^ 2) := by
  obtain ⟨z, u, Hm, W, χ, θ, Fd, hpb, hA, hR, hF, -, hD, e, -⟩ := h
  obtain ⟨φ, he, w, hg, F, hφ, hw, h1, h2, -⟩ := hy z hpb
  exact ⟨z.P, z.rig, z.th, φ, he, w, hφ, hw, h1, h2, u, Hm, χ, θ, Fd, hA, hR, hF, hD, e⟩

theorem isLieNormAt_of_isVecLine {K : Type} [Field K] [NumberField K] {A : Out.PolAV (Sp (𝓞 K))} {x : KeyIn K}
    {φ : x.P.A.left ⟶ A.A.left} {i : Fin x.P.g} {ℓ : MLine K} (h : IsVecLine A x φ i ℓ) (σ : K →+* ℂ) :
    Arch.IsLieNormAt x.P (x.v i) σ (Real.log (ℓ.n σ)) := by
  obtain ⟨xs, u, Hm, χ, W, hg, hpb, hA, hW, e⟩ := h.2.2 σ
  obtain ⟨ψ, hg', hψ, hv⟩ := GlobalTheory.KeyFibre.exists_isPolFibre_of_keyPB K ℂ σ x xs hpb
  obtain ⟨w, hw⟩ := LBIso.symm hψ.2.2
  refine ⟨xs.P, ψ, w, _, hψ.2.1, hw, hv (i.cast hg.symm), u, Hm, χ, W, hA, hW, ?_⟩
  rw [← e, Real.log_pow]
  push_cast
  ring

section Pull

variable {K : Type} [Field K] {D₀ : Out.DegPre K} {DC : Out.DegPre ℂ} {σ : K →+* ℂ} (p : Out.IsPullDeg σ D₀ DC)

include p in
theorem g_eq : DC.P.g = D₀.P.g :=
  ReciprocityTheory.ChartRestriction.G.H1.dim_unique DC.P.A.hom DC.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp p).1 D₀.P.smoothDim)
    (eSec DC.P.A (default : PrimeSpectrum ℂ))

theorem isPolFibre_prj : IsPolFibre σ D₀.P DC.P (prj p) :=
  ⟨g_eq p, pull_grp p, LBIso.symm ⟨p.w, p.w_gen⟩⟩

theorem exists_keyPB {th : D₀.P.L.Sec} {thC : DC.P.L.Sec} (h : ThBC p th thC) (hg : 1 ≤ D₀.P.g) (hn : ThNZ th)
    (v : Fin D₀.P.g → (epsR K ⟶ D₀.P.A)) (hv : IsLieBasis v) :
    ∃ hg' hn' v' hv', KeyPB ⟨DC.P, hg', DC.rig, DC.rig_gen, thC, hn', v', hv'⟩
      ⟨D₀.P, hg, D₀.rig, D₀.rig_gen, th, hn, v, hv⟩ σ := by
  have e := g_eq p
  have c₁ : IsCommMonObj D₀.P.A := D₀.P.isAb.comm
  have c₂ : IsCommMonObj DC.P.A := DC.P.isAb.comm
  obtain ⟨v', hb', hv'⟩ := exists_isLieBasis_baseChange K ℂ σ D₀.P.A DC.P.A (prj p) (pull_grp p)
    D₀.P.isAb.smooth D₀.P.g v hv
  refine ⟨e ▸ hg, GlobalTheory.ArcQBC.thNZ_of_thBC p h hn, fun i => v' (i.cast e), GlobalTheory.KeyTf.isLieBasis_cast e hb',
    prj p, p.he, p.w, e, Chart.dualMapR σ, pull_grp p, p.w_gen, p.w_rig,
    GlobalTheory.KeyPow.appLE_eq_of_stalk _ th thC ((GlobalTheory.ArcQBC.through_iff _ _).1 h), fun a => ?_, ?_, fun i => hv' _⟩
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end Pull

theorem exists_isLieNormAt (hU : ThetaUnifAV) (P : Out.PolAV (Sp ℂ)) (v : epsR ℂ ⟶ P.A) (hv : IsTangent v) :
    ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (z : Fin P.g → ℂ),
      u.IsAH Hm χ ∧ u.IsDiff z v ∧
        Arch.IsLieNormAt P v (RingHom.id ℂ) (Real.log (Real.pi * (hermForm Hm z z).re) / 2) := by
  obtain ⟨rig, hr⟩ := P.rigid
  obtain ⟨u, Hm, χ, -, hA, -, hd, -⟩ := hU P rig hr
  obtain ⟨z, hz, -⟩ := hd v hv
  obtain ⟨h₁, h₂⟩ := GlobalTheory.polFibre_id_comp_cancel.1 ℂ P v
  obtain ⟨w, hw⟩ := LBIso.symm h₁.2.2
  exact ⟨u, Hm, χ, z, hA, hz, P, _, w, v, h₁.2.1, hw, h₂, u, Hm, χ, z, hA, hz, rfl⟩

theorem exists_letter_bound (hU : ThetaUnifAV) (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E]
    [StarRing (𝓞 E)] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H} {c : Coeff l} (hs : ∀ a : 𝓞 E, star a = H.bar a)
    {nΨ n' f : ℕ} {o : LamObj c nΨ n'} {La : ℝ} (hG : LamObjGood o f La) (L : LamLetters o) (hLg : L.IsGood)
    (σ : o.K₁ →+* ℂ) (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ o.xB.P.A.left) (hQ : IsPolFibre σ o.xB.P Q ψ)
    (m : Fin o.xB.P.g) (u : epsR o.K₁ ⟶ o.xB.P.A) (uC : epsR ℂ ⟶ Q.A) (hu : L.IsLetter m u)
    (hC : IsVecOver σ ψ u uC) :
    ∃ x, Arch.IsLieNormAt Q uC (RingHom.id ℂ) x ∧ (0 < La → x ≤ Real.log (La * (L.ℓ m).n σ)) := by
  have hB := hG.2.2.2.1
  have hp : IsPolFibre (algebraMap (𝓞 o.K₁) o.K₁) o.B o.xB.P o.φB :=
    (isFibreOf_iff_isPolFibre (𝓞 o.K₁) o.K₁ (algebraMap (𝓞 o.K₁) o.K₁) o.B o.xB o.φB).1 hB
  obtain ⟨h, Hh⟩ := (GlobalTheory.CM.LieMetric.exists_unique_isHerm hU hL o.K₁ o.B
    (GlobalTheory.CM.GenFib.mk o.xB.P o.φB hp o.xB.v o.xB.basis)).1
  obtain ⟨w, hw1, hw2⟩ := hLg.2.2.1 m
  obtain rfl : u = w := by
    refine Over.OverMorphism.ext (hp.2.1.1.hom_ext ?_ ((Over.w u).trans (Over.w w).symm))
    unfold LamLetters.IsLetter at hu hw1
    cases hq : L.src m with
    | inl q => rw [hq] at hu hw1; exact hu.trans hw1.symm
    | inr q => rw [hq] at hu hw1; exact hu.trans hw1.symm
  have c₁ : IsCommMonObj o.xB.P.A := o.xB.P.isAb.comm
  have ht : IsTangent u := by
    rw [(LieComb.isLieComb_iff_tanExp _ _).1 hw2]
    exact LieComb.isTangent_tanExp o.xB.basis.1 _
  obtain ⟨uu, Hm, χ, z, hA, hz, hN⟩ := exists_isLieNormAt hU Q uC (hC.isTangent hQ.2.1 ht)
  refine ⟨_, hN, fun hLa => ?_⟩
  have e := GlobalTheory.CM.LieMetric.form_eq_pi_mul_hermForm hU hL o.K₁ o.B _ h Hh σ Q ψ uu Hm χ hQ hA
    _ _ _ _ _ _ z z hw2 hw2 hC hC hz hz
  have e' : Real.pi * (hermForm Hm z z).re = (h.form σ (L.U m) (L.U m)).re := by
    rw [e, Complex.re_ofReal_mul]
  have b := (lamLen_of_isHerm hU hL E H l c nΨ n' f o La hG L hLg hp h Hh σ).2 m
  have hd := GlobalTheory.LamF.Ind.lamInd E H l c hs nΨ n' f o La hG L hLg
  have hne : L.U m ≠ 0 := fun h0 => hd (Matrix.det_eq_zero_of_row_eq_zero m (congrFun h0))
  have hpos : 0 < (h.form σ (L.U m) (L.U m)).re := by
    have := (h.posDef σ 1 ![L.U m] (by simpa [linearIndependent_unique_iff] using hne)).diag_pos (i := 0)
    exact (Complex.pos_iff.1 this).1
  rw [e']
  have := Real.log_le_log hpos b
  rw [Real.log_pow] at this
  push_cast at this
  linarith

theorem lengths_eq_norms : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (em : K₁ →+* ℂ), letI := H.starRing; Arch.IsThNormAt a.D₀.P a.D₀.rig th em (s.Tl.n em ^ 2) ∧ (∀ i, Arch.IsLieNormAt s.xΨ.P (s.xΨ.v i) em (Real.log ((s.ℓΨ i).n em))) ∧ (∀ i, Arch.IsLieNormAt s.x'.P (s.x'.v i) em (Real.log ((s.ℓ' i).n em))) ∧ ∀ (DC : Out.DegPre ℂ) (p : Out.IsPullDeg em a.D₀ DC), (∀ thC, ThBC p th thC → Arch.IsThNormAt DC.P DC.rig thC (RingHom.id ℂ) (s.Tl.n em ^ 2)) ∧ ∀ m (u : epsR K₁ ⟶ a.D₀.P.A) (uC : epsR ℂ ⟶ DC.P.A), s.L.IsLetter m u → uC.left ≫ prj p = spMap (dualMap em) ≫ u.left → ∃ x, Arch.IsLieNormAt DC.P uC (RingHom.id ℂ) x ∧ (0 < La → x ≤ Real.log (La * (s.L.ℓ m).n em)) := by
  intro hK E _ _ _ H Dw l c K₁ _ _ _ a e th jj n' La c₁ s em
  letI := H.starRing
  have hG := s.good
  have hA : KeyArchAt s.xB s.Tl s.LamL em := hG.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 em
  refine ⟨isThNormAt_of_keyArchAt hA s.xB em fun _ h => h,
    fun i => isLieNormAt_of_isVecLine (hG.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i) em,
    fun i => isLieNormAt_of_isVecLine (hG.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i) em, fun DC p => ⟨fun thC hC => ?_,
    fun m u uC hu hC => ?_⟩⟩
  · obtain ⟨hg', hn', v', hv', h⟩ := exists_keyPB p hC s.g_pos s.th_nz s.v s.basis
    exact isThNormAt_of_keyArchAt hA ⟨DC.P, hg', DC.rig, DC.rig_gen, thC, hn', v', hv'⟩ (RingHom.id ℂ) fun z hz =>
      GlobalTheory.KeyCancel.keyPB_cancel K₁ ℂ ℂ _ _ z em (RingHom.id ℂ) h (by rwa [RingHom.id_comp])
  · exact exists_letter_bound hK.theta hK.laws (fun _ => rfl) hG s.L s.L_good em DC.P (prj p) (isPolFibre_prj p)
      m u uC hu hC

end GlobalTheory.ArcCM.NormTie
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.exponentialFamily_deriv_sumsAt_period : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (laA laM : D.La → Λ.A.La) (K : Cmp Fu Λ.A Ψ.yw Ψ.pi laA laM), AnFin Λ.A → C.Φ.Rational → ∀ (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR (PowerSeries ℂ) ⟶ W.t.G) (V : Y.t.G.left.Opens) (f : Γ(Y.t.G.left, V)), DiffHyp W (fun z => Λ.ex0 (K.h.symm z)) z₀ ν v → ⊤ ≤ (v.left ≫ W.m.φ) ⁻¹ᵁ V → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∀ xF : (Fin g → ℂ) → (Sp ℂ ⟶ Y.oF.t.G.left), (∀ z, xF z ≫ Y.m0.toSABMap.φ = (Fu.ex K.i (K.Pw w) z).left ∧ xF z ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF) → SumsAt (TrivSqZeroExt.snd (valR (A := DualNumber (PowerSeries ℂ)) (v.left ≫ W.m.φ) V f)) w (fderiv ℂ (fun z => valAt' (xF z ≫ Y.m.φ) V f) 0 z₀) := by
  first | exact @GlobalTheory.ArcDeriv.deriv_sumsAt | exact GlobalTheory.ArcDeriv.deriv_sumsAt | (intros; apply GlobalTheory.ArcDeriv.deriv_sumsAt <;> assumption)
end
