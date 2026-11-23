module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle244
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryTorusNormClassesAtAllPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianIsometryBaseChange
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusCompactQuotientFiniteVolume
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle245
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle253
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle138
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle257
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle139
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle246
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle248
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
import Mathlib.NumberTheory.RamificationInertia.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix


theorem _root_.GlobalTheory.T.charpoly_unitary_eq_conjugateReciprocal : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 → ∀ γ : GRat σ J, γ.1.1.charpoly = sharp σ n γ.1.1.charpoly := by
  first | exact @GlobalTheory.TrEll.charpoly_eq_sharp | exact GlobalTheory.TrEll.charpoly_eq_sharp | (intros; apply GlobalTheory.TrEll.charpoly_eq_sharp <;> assumption)
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix


theorem _root_.GlobalTheory.T.exists_adjoinRoot_linearEquiv_of_charpoly_eq : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (P : PPol σ n) (A : Matrix (Fin n) (Fin n) E), A.charpoly = P.1 → ∃ φ : Fld P ≃ₗ[E] (Fin n → E), ∀ y, A *ᵥ φ y = φ (alpha P * y) := by
  first | exact @GlobalTheory.TrEll.exists_linearEquiv_mulVec_of_charpoly | exact GlobalTheory.TrEll.exists_linearEquiv_mulVec_of_charpoly | (intros; apply GlobalTheory.TrEll.exists_linearEquiv_mulVec_of_charpoly <;> assumption)
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix


theorem _root_.GlobalTheory.T.exists_unitaryTorus_traceForm_of_hermitian : ∀ (F E : Type) [Field F] [Field E] [CharZero E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (P : PPol σ n) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (A : Matrix (Fin n) (Fin n) E), Formalism.UG.cT (σ : E →+* E) A * J * A = J → ∀ φ : Fld P ≃ₗ[E] (Fin n → E), (∀ y, A *ᵥ φ y = φ (alpha P * y)) → ∃ x : Fld P, x ≠ 0 ∧ star' P x = x ∧ ∀ y y', Formalism.UG.hform (σ : E →+* E) J (φ y') (φ y) = Algebra.trace E (Fld P) (x * y * star' P y') := by
  first | exact @GlobalTheory.TrEll.HermTrace.exists_trace_form | exact GlobalTheory.TrEll.HermTrace.exists_trace_form | (intros; apply GlobalTheory.TrEll.HermTrace.exists_trace_form <;> assumption)
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.unitaryTorusEllipticElements_of_localLatticeIsometry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n n' : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin n') (Fin n') E) (L : Submodule (𝓞 E) (Fin n → E)) (L' : Submodule (𝓞 E) (Fin n' → E)) (v : HeightOneSpectrum (𝓞 F)) (j : GLoc σ J v ≃ₜ* GLoc σ J' v), IsLatticeConj L L' j → XSet P (Fv F v) J' = XSet P (Fv F v) J ∧ ∀ (x : plusUnits P (Fv F v)) (φ : ((Fv F v) ⊗[F] Fld P) ≃ₗ[(Fv F v) ⊗[F] E] (Fin n → (Fv F v) ⊗[F] E)) (h : IsIsom P (Fv F v) J x.1.1 φ), ∃ (φ' : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n' → Fv F v ⊗[F] E)) (h' : IsIsom P (Fv F v) J' x.1.1 φ'), gam h' = j (gam h) ∧ ∀ t, torEmb h' t = j (torEmb h t) := by
  first | exact @GlobalTheory.trEll_latticeConj_move | exact GlobalTheory.trEll_latticeConj_move | (intros; apply GlobalTheory.trEll_latticeConj_move <;> assumption)
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.finite_unitaryTorusNormClasses_at_all_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r), (∀ v : HeightOneSpectrum (𝓞 F), Finite (Cls P (Fv F v))) ∧ ∀ w : InfinitePlace F, Finite (Cls P w.Completion) := by
  first | exact @GlobalTheory.SqCls.finite_cls | exact GlobalTheory.SqCls.finite_cls | (intros; apply GlobalTheory.SqCls.finite_cls <;> assumption)
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.hermitian_isometry_base_change : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k k' : Type) [CommRing k] [Algebra F k] [CommRing k'] [Algebra F k'] (ψ : k →ₐ[F] k') (x : plusUnits P k) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h : IsIsom P k J x.1.1 φ), ∃ (x' : plusUnits P k') (φ' : (k' ⊗[F] Fld P) ≃ₗ[k' ⊗[F] E] (Fin n → k' ⊗[F] E)) (h' : IsIsom P k' J x'.1.1 φ'), x'.1.1 = Algebra.TensorProduct.map ψ (AlgHom.id F (Fld P)) x.1.1 ∧ gam h' = mapH σ J ψ (gam h) ∧ ∀ t, torEmb h' (mapH (star' P) (one₁ P) ψ t) = mapH σ J ψ (torEmb h t) := by
  first | exact @GlobalTheory.TrEll.BaseChg.exists_isom_baseChange | exact GlobalTheory.TrEll.BaseChg.exists_isom_baseChange | (intros; apply GlobalTheory.TrEll.BaseChg.exists_isom_baseChange <;> assumption)
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.unitaryTorus_compact_quotient_finite_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r), (∃ C : Set (Tor P (AF F)), IsCompact C ∧ ∀ t : Tor P (AF F), ∃ γ ∈ ratPts (star' P) (one₁ P), γ * t ∈ C) ∧ ∀ dt : Measure (Tor P (AF F)), dt.IsHaarMeasure → torVol P dt ≠ ⊤ := by
  first | exact @GlobalTheory.TorCompact.torus_compact_finiteVol | exact GlobalTheory.TorCompact.torus_compact_finiteVol | (intros; apply GlobalTheory.TorCompact.torus_compact_finiteVol <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie


theorem _root_.GlobalTheory.T.splitPlace_chart_frames_conj_maximalCompact : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → ∃ φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsIdemOf φ ε ∧ (∃ BS, GlobalTheory.SplitHecke.Frame S ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BS) ∧ ∃ BT, GlobalTheory.SplitHecke.Frame T ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BT ∧ ∃ ψ : Fv D.host.F v ≃+* w.adicCompletion D.host.E, (∀ a, Valued.v (ψ a) = Valued.v a) ∧ qV D.host.F v = qV D.host.E w ∧ ∃ κ ∈ KGL v (n := T.rank), ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.grpCo φ T BT (embV T v (e.symm x)) = κ⁻¹ * Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) x * κ := by
  first | exact @GlobalTheory.SplitChartLink.link | exact GlobalTheory.SplitChartLink.link | (intros; apply GlobalTheory.SplitChartLink.link <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.TwistTypePlaces

theorem card_quot_of_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hr : Module.finrank F E = 2) (P : HeightOneSpectrum (𝓞 E))
    (h2 : (Ideal.primesOver (P.under (𝓞 F)).asIdeal (𝓞 E)).ncard = 2) :
    Nat.card (𝓞 E ⧸ P.asIdeal) = Ideal.absNorm (P.under (𝓞 F)).asIdeal := by
  classical
  set p := (P.under (𝓞 F)).asIdeal with hp
  have hp0 : p ≠ ⊥ := (P.under (𝓞 F)).ne_bot
  have : p.IsMaximal := (P.under (𝓞 F)).isMaximal
  have : P.asIdeal.LiesOver p := ⟨by rw [hp, HeightOneSpectrum.under_asIdeal]⟩
  have hsum := Ideal.sum_ramification_inertia (𝓞 E) F E (p := p) hp0
  have hcard : (IsDedekindDomain.primesOverFinset p (𝓞 E)).card = 2 := by
    rw [← h2, ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 E), Set.ncard_coe_finset]
  have hle : ∀ Q ∈ IsDedekindDomain.primesOverFinset p (𝓞 E), 1 ≤ p.ramificationIdx' Q * p.inertiaDeg' Q := by
    intro Q hQ
    obtain ⟨hQp, hQl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 E)).1 hQ
    have h1 : 0 < p.inertiaDeg' Q := Ideal.inertiaDeg'_pos p Q
    have h2 : 0 < p.ramificationIdx' Q := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx p Q hp0]
      exact Ideal.ramificationIdx_pos (R := 𝓞 F) Q
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero h2.ne' h1.ne')
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 (by rw [hsum, hr, Finset.sum_const, hcard]; rfl)
  have hPm : P.asIdeal ∈ IsDedekindDomain.primesOverFinset p (𝓞 E) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 E)).2 ⟨P.isPrime, inferInstance⟩
  have hf : p.inertiaDeg' P.asIdeal = 1 := Nat.eq_one_of_mul_eq_one_left (heq _ hPm).symm
  have hn := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal p (P.under (𝓞 F)).isPrime hp0
  rw [hf, pow_one, Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
  exact hn

end GlobalTheory.TwistTypePlaces

namespace GlobalTheory.TwistTypePlaces

theorem under_conjPl {D : D7} (P : Pl D.host.E) :
    (Formalism.DivisionValues.conjPl P).under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := by
  have hfix : ∀ x : 𝓞 D.host.F,
      Formalism.DivisionValues.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := by
    intro x
    apply RingOfIntegers.ext
    show star ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E) = _
    exact (D.sp.cm.fixed _).2 ⟨(x : D.host.F), rfl⟩
  have hinv : ∀ z, Formalism.DivisionValues.cO D.host.E (Formalism.DivisionValues.cO D.host.E z) = z :=
    fun z => RingOfIntegers.ext (star_star (z : D.host.E))
  apply HeightOneSpectrum.ext
  ext x
  simp only [HeightOneSpectrum.under_asIdeal, Ideal.mem_comap]
  change algebraMap _ _ x ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) ↔ _
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have e : z = algebraMap _ _ x := by rw [← hinv z, hzx, hfix]
    rwa [← e]
  · intro h
    exact ⟨_, h, hfix x⟩

theorem natCast_mem_conjPl {D : D7} (P : Pl D.host.E) (n : ℕ) (h : (n : 𝓞 D.host.E) ∈ P.asIdeal) :
    (n : 𝓞 D.host.E) ∈ (Formalism.DivisionValues.conjPl P).asIdeal := by
  have := Ideal.mem_map_of_mem (Formalism.DivisionValues.cO D.host.E) h
  rwa [map_natCast] at this

theorem ncard_primesOver_two {D : D7} (P : Pl D.host.E) (h : Formalism.DivisionValues.conjPl P ≠ P) :
    (Ideal.primesOver (P.under (𝓞 D.host.F)).asIdeal (𝓞 D.host.E)).ncard = 2 := by
  rw [GlobalTheory.QuadSignLocal.ncard_primesOver]
  have hs : {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)} = {P, Formalism.DivisionValues.conjPl P} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · exact GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq
    · rintro (rfl | rfl)
      · rfl
      · exact under_conjPl P
  rw [hs, Set.ncard_pair h.symm]

theorem natCast_not_mem_of_card {E : Type} [Field E] [NumberField E] (PP : Pl E) {q g : ℕ} (hq : q.Prime) (hg : g.Prime)
    (hc : Nat.card (kP PP) = q) (hne : q ≠ g) : ((g : ℕ) : 𝓞 E) ∉ PP.asIdeal := by
  intro hm
  have hnt : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
  have hq0 : ((q : ℕ) : kP PP) = 0 := by
    have := card_nsmul_eq_zero' (G := kP PP) (x := 1)
    rwa [hc, nsmul_one] at this
  have hg0 : ((g : ℕ) : kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  obtain ⟨a, b, hab⟩ : IsCoprime (q : ℤ) (g : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hg).2 hne)
  have h1 : ((a * q + b * g : ℤ) : kP PP) = 1 := by rw [hab, Int.cast_one]
  push_cast at h1
  rw [hq0, hg0, mul_zero, mul_zero, add_zero] at h1
  exact zero_ne_one h1

end GlobalTheory.TwistTypePlaces

namespace GlobalTheory.TwistTypePlaces

theorem places_split : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ t : T, Disjoint R.Pg (R.Q t) ∧ Set.InjOn (fun PP : Pl D.host.E => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ↑(R.Pg ∪ R.Q t) ∧ ∀ PP ∈ R.Pg ∪ R.Q t, (Ideal.primesOver ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal (𝓞 D.host.E)).ncard = 2 ∧ Nat.card (kP PP) = Ideal.absNorm ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t
  have hL := hC.lev
  have hPg := hL.Pg
  have hQ := hL.Q_pl t
  have gP : ∀ PP ∈ R.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP h
    obtain ⟨k, hk⟩ := (hPg PP).1 h
    exact ⟨k, R.C.P.overP hk⟩
  have qN : ∀ PP ∈ R.Q t, ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP h k
    obtain ⟨q, hq, hc, -, hne⟩ := (hQ PP h).1
    exact natCast_not_mem_of_card PP hq (D.host.g_prime k) hc (hne k)
  have hdis : Disjoint R.Pg (R.Q t) := by
    rw [Finset.disjoint_left]
    intro PP h1 h2
    obtain ⟨k, hk⟩ := gP PP h1
    exact qN PP h2 k hk
  have cross : ∀ PP ∈ R.Pg, ∀ PP' ∈ R.Q t, PP' ≠ Formalism.DivisionValues.conjPl PP := by
    rintro PP h PP' h' rfl
    obtain ⟨k, hk⟩ := gP PP h
    exact qN _ h' k (natCast_mem_conjPl PP _ hk)
  have hnc : ∀ PP ∈ R.Pg ∪ R.Q t, ∀ PP' ∈ R.Pg ∪ R.Q t, PP' ≠ Formalism.DivisionValues.conjPl PP := by
    intro PP h PP' h' e
    rcases Finset.mem_union.1 h with h | h <;> rcases Finset.mem_union.1 h' with h' | h'
    · exact GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hPg PP h PP' h' (GlobalTheory.GoodPrimes.isConjPl_iff.2 e)
    · exact cross PP h PP' h' e
    · refine cross PP' h' PP h ?_
      rw [e, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
    · exact (hQ PP h).2 PP' h' (GlobalTheory.GoodPrimes.isConjPl_iff.2 e)
  refine ⟨hdis, ?_, ?_⟩
  · intro PP h PP' h' e
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with e' | e'
    · exact e'.symm
    · exact absurd e' (hnc PP h PP' h')
  · intro PP h
    have h2 := ncard_primesOver_two PP (fun e => hnc PP h PP h e.symm)
    exact ⟨h2, card_quot_of_two D.sp.cm.deg2 PP h2⟩

end GlobalTheory.TwistTypePlaces
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EwfMove

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem star_eC (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (σ : D.what₂.LL →+* ℂ) (g : G) :
    starRingEnd ℂ (RealDat.eC (A := A) σ g) = RealDat.eC (A := A) σ g⁻¹ := by
  unfold RealDat.eC

  rw [coeff_idemOf, coeff_idemOf, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  have h1 := (hX χ hχ).map_inv σ 1
  have h2 := (hX χ hχ).map_inv σ g⁻¹
  rw [inv_one] at h1
  simp only [map_mul, map_div₀, map_natCast]
  rw [h2, ← h1]

theorem integral_levelGroupAction_pairing_invariant {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (g0 : G0 L.Pg L.r) (μ : Measure (GA D V)) [μ.IsHaarMeasure] (𝓕 : Set (GA D V))
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (hk : ∃ κ, IsLevelLift V β L g0 κ) (F S : GA D V → ℂ)
    (hF : ∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g) (hS : ∀ γ ∈ GQ V, ∀ g, S (γ * g) = S g)
    (hi : IntegrableOn (fun g => star (F g) * S g) 𝓕 μ) :
    IntegrableOn (fun g => star (actG0 V β L g0 F g) * actG0 V β L g0 S g) 𝓕 μ ∧
      ∫ g in 𝓕, star (actG0 V β L g0 F g) * actG0 V β L g0 S g ∂μ = ∫ g in 𝓕, star (F g) * S g ∂μ := by
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  obtain ⟨hcpt, hlift⟩ := GlobalTheory.ParahoricCompact.isCompact_flag_and_lift V β L
  have hκ : hk.choose ∈ levG V β (flagL L) := hlift g0 _ hk.choose_spec
  have ha : ‖(levChi V β (flagL L) hk.choose)⁻¹‖ = 1 := by
    rw [norm_inv, GlobalTheory.norm_levChi_flagL_eq_one V β L _ hκ, inv_one]
  have hmap : Measure.map (fun g => g * hk.choose) μ = μ :=
    GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup μ _ hcpt _ hκ
  set a := (levChi V β (flagL L) hk.choose)⁻¹ with ha_def
  have haa : star a * a = 1 := by
    have : star a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
    rw [this, ha]; norm_num
  have key : (fun g => star (actG0 V β L g0 F g) * actG0 V β L g0 S g) =
      fun g => star (F (g * hk.choose)) * S (g * hk.choose) := by
    funext g
    simp only [actG0, dif_pos hk]
    rw [star_mul', ← ha_def]
    linear_combination (star (F (g * hk.choose)) * S (g * hk.choose)) * haa
  rw [key]
  exact GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ V) μ 𝓕 h𝓕 _ hmap (fun g => star (F g) * S g)
    (fun γ hγ g => by simp only [hF γ hγ g, hS γ hγ g]) hi

end GlobalTheory.EwfMove

noncomputable section

namespace GlobalTheory.EwfMove

theorem integral_eWf_move : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : ∀ ρ, lowT (R.MW i σ) ρ) (Φ : GA D (Wc D i) → ℂ), (∀ γ ∈ GQ (Wc D i), ∀ g, Φ (γ * g) = Φ g) → (∀ y : (R.HW i σ).H, IntegrableOn (fun g => star (Φ g) * (R.HW i σ).e y (fun ρ => v ρ) g) (R.fdW i) (R.νW i)) → ∀ y : (R.HW i σ).H, ∫ g in R.fdW i, star (R.eWf i σ Φ g) * (R.HW i σ).e y (fun ρ => v ρ) g ∂(R.νW i) = ∫ g in R.fdW i, star (Φ g) * (R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ) g ∂(R.νW i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hX i σ v Φ hΦ hi y
  obtain ⟨hinj, hrange, hip⟩ := hC.models.HW i σ
  obtain ⟨h1, h2⟩ := hC.models.νW i
  haveI := h1.1
  have hgW := hC.models.gW
  have hL : ∀ z : (R.HW i σ).H, ∀ γ ∈ GQ (Wc D i), ∀ g,
      (R.HW i σ).e z (fun ρ => v ρ) (γ * g) = (R.HW i σ).e z (fun ρ => v ρ) g := fun z =>
    (GlobalTheory.mult_value_left_cont_level R.θ (R.MW i σ) _ _ _
      ((hrange.le : _ ≤ R.Wall i σ) (LinearMap.mem_range_self _ z)) _).1
  have hS : ∀ (g : G) (z : (R.HW i σ).H), (R.HW i σ).e z (fun ρ => v ρ) =
      actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) ((R.HW i σ).e (R.gW i σ g⁻¹ z) (fun ρ => v ρ)) := by
    intro g z
    have e := congrArg (fun T : MMap (R.MW i σ) => T (fun ρ => v ρ)) (hgW i σ g (R.gW i σ g⁻¹ z))
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at e
    exact e
  have hper : ∀ g : G,
      IntegrableOn (fun h => star (actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) Φ h) *
        (R.HW i σ).e y (fun ρ => v ρ) h) (R.fdW i) (R.νW i) ∧
      ∫ h in R.fdW i, star (actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) Φ h) *
        (R.HW i σ).e y (fun ρ => v ρ) h ∂(R.νW i) =
      ∫ h in R.fdW i, star (Φ h) * (R.HW i σ).e (R.gW i σ g⁻¹ y) (fun ρ => v ρ) h ∂(R.νW i) := by
    intro g
    by_cases hk : ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ
    · rw [hS g y]
      exact integral_levelGroupAction_pairing_invariant _ _ _ _ _ h2 hk Φ _ hΦ (hL _) (hi _)
    · have h0 : ∀ z : (R.HW i σ).H, (R.HW i σ).e z (fun ρ => v ρ) = 0 := fun z => by
        rw [hS g z]
        simp only [actG0, dif_neg hk]
      constructor
      · simp only [h0, Pi.zero_apply, mul_zero]
        exact integrableOn_zero
      · simp only [h0, Pi.zero_apply, mul_zero]
  have eL : ∀ h, star (R.eWf i σ Φ h) * (R.HW i σ).e y (fun ρ => v ρ) h =
      ∑ g, starRingEnd ℂ (RealDat.eC (A := A) σ g) *
        (star (actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) Φ h) * (R.HW i σ).e y (fun ρ => v ρ) h) := by
    intro h
    simp only [RealDat.eWf, gaL, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, star_sum, star_mul', Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [mul_assoc]
    rfl
  have eR : ∀ h, star (Φ h) * (R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ) h =
      ∑ g, RealDat.eC (A := A) σ g * (star (Φ h) * (R.HW i σ).e (R.gW i σ g y) (fun ρ => v ρ) h) := by
    intro h

    simp only [GlobalTheory.LiftLower.projH, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    ring
  simp only [eL, eR]
  rw [integral_finsetSum _ fun g _ => ((hper g).1.const_mul _),
    integral_finsetSum _ fun g _ => ((hi (R.gW i σ g y)).const_mul _)]
  simp only [integral_const_mul, (hper _).2, star_eC hX]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => rfl)

end GlobalTheory.EwfMove
end
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical


theorem _root_.GlobalTheory.T.disjoint_Pg_Q_of_core : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ t : T, Disjoint R.Pg (R.Q t) := by
  first | exact @GlobalTheory.TwistPlaces.typePlaces_disjoint_twistPlaces | exact GlobalTheory.TwistPlaces.typePlaces_disjoint_twistPlaces | (intros; apply GlobalTheory.TwistPlaces.typePlaces_disjoint_twistPlaces <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.reductionTrivial_of_conjugatePlace_selfDual : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank), IsSelfDualC V L → ∀ β : GL (Fin V.rank) (Lev.EAf D), Formalism.L2.DIV.IsFrame β L → ∀ k : GA D V, Lev.finE V k ∈ Formalism.L2.DIV.St β → ∀ (PP PP' : Formalism.L2.DIV.Pl D.host.E), Formalism.IndefR.Lev.IsConjPl PP' PP → Formalism.L2.DIV.redFn β PP' (Lev.finE V k) = 1 → Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  first | exact @GlobalTheory.ConjPlaceRedGen.redFn_eq_one_of_conj | exact GlobalTheory.ConjPlaceRedGen.redFn_eq_one_of_conj | (intros; apply GlobalTheory.ConjPlaceRedGen.redFn_eq_one_of_conj <;> assumption)
end
