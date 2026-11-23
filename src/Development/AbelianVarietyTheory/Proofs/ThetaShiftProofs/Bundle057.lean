module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle021
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle074
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle026
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle063
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingDual
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArchimedeanUniqueness.MetricDef
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CharEqOfThetaCharEqMul
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemThetaShiftZero
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle023
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcCM.Letters

theorem exists_scaled {R : Type} [CommRing R] [IsDomain R] {D₀ : Out.DegPre R} {n : ℕ}
    {sB : ∀ T : Over (Sp R), (T ⟶ D₀.P.A) → Out.GtPt D₀ T} (h : IsSplit D₀ n sB) (r : R) {w : epsR R ⟶ D₀.P.A}
    (hw : IsTangent w) : ∃ ν, GtTanR ν ∧ Out.GtPt.IsPull (spMap (epsScaleR r)) (sB (epsR R) w) ν := by
  let sc : epsR R ⟶ epsR R := Over.homMk (spMap (epsScaleR r)) (by
    show spMap (epsScaleR r) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R))
    rw [spMap_comp_spMap]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl])
  let z : Over.mk (𝟙 (Sp R)) ⟶ epsR R := Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (by
    show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _
    rw [spMap_comp_spMap]
    have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]
    exact Spec.map_id (CommRingCat.of R))
  have hz : z ≫ sc ≫ w = 1 := by
    apply Over.OverMorphism.ext
    have e : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (epsScaleR r) =
        spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
      rw [spMap_comp_spMap]
      congr 1
      ext a <;> simp [epsScaleR]
    show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (epsScaleR r) ≫ w.left = _
    rw [← Category.assoc, e, hw]
    exact (Category.id_comp _).symm
  refine ⟨sB _ (sc ≫ w), ⟨sB _ 1, TanPart.isZero_of_isAdd (by simpa using h.2.1 _ 1 1), ?_⟩, h.2.2 _ _ sc w⟩
  have := h.2.2 _ _ z (sc ≫ w)
  rwa [hz] at this

theorem exists_kind {I J : Type} (N m : I → ℕ) (h : ∀ τ, N τ = m τ + 1) (e : (Σ b, Fin (m b)) ≃ J) :
    ∃ kind : ∀ τ, Fin (N τ) → Option J, ∀ τ, Function.Injective (kind τ) ∧ (∃ k, kind τ k = none) ∧
      ∀ j, (∃ k, kind τ k = some j) ↔ (e.symm j).1 = τ := by
  let u : ∀ τ, Fin (N τ) ≃ Option (Fin (m τ)) := fun τ => (finCongr (h τ)).trans (finSuccEquiv _)
  refine ⟨fun τ k => (u τ k).map fun i => e ⟨τ, i⟩, fun τ => ⟨?_, ⟨(u τ).symm none, by simp⟩, fun j => ⟨?_, ?_⟩⟩⟩
  · exact (Option.map_injective (e.injective.comp sigma_mk_injective)).comp (u τ).injective
  · rintro ⟨k, hk⟩
    obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.1 hk
    simp
  · rintro rfl
    exact ⟨(u _).symm (some (e.symm j).2), by simp⟩

theorem exists_section (hT : Out.SecTwistSt) {K : Type} [Field K] (P : Out.PolAV (Sp K)) :
    ∃ th : P.L.Sec, ∀ s : Sp K, ∃ x : P.A.left, P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th := by
  obtain ⟨b, hb⟩ := principalPolarisation_exists_unique_section hT P
  obtain ⟨a, -, hu⟩ := hb b
  refine ⟨b, KeyPow.exists_mem_nonzeroLocus _ b ?_⟩
  by_contra hn
  push Not at hn
  exact zero_ne_one ((hu 0 fun i => by rw [hn i, mul_zero]).trans (hu 1 fun i => by rw [hn i, mul_zero]).symm)

theorem exists_cmIn : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (ρ : 𝓞 K₁) (σ₁ : K₁ →+* ℂ) (X : GlobalTheory.CM.CMObj H K₁ ρ σ₁ (Dw.p - 1) (Dw.q - 1)) (ψ : a.D₀.P.A.left ⟶ X.B.pol.A.left) (n' : ℕ) (La c₁ : ℝ) (ξ : Module.Dual ℤ a.D₀.X) (ν₀ : E) (jj : ℤ), letI := H.starRing; 1 ≤ Dw.p → 1 ≤ Dw.q → 3 ≤ Dw.p + Dw.q → σ₁.comp (algebraMap c.F K₁) = c.F.val.toRingHom → σ₁ (ρ : K₁) = H.rt0 → (∀ j (τ : E →+* ℂ), ‖τ (X.hh j : E)‖ ≤ La ^ 2) → IsPolFibre (algebraMap (𝓞 K₁) K₁) X.B.pol a.D₀.P ψ → (∀ x, (a.oa.onB.act x).left ≫ ψ = ψ ≫ (X.B.t.act.act x).left) → 0 < n' → TauCan a.D₀ n' → Module.finrank (𝓞 E) a.D₀.X = 1 → ξ ≠ 0 → BetaAt ξ l.M' a.be ν₀ jj → ((Algebra.trace ℚ E ν₀ : ℚ) : ℝ) / 2 ≤ c₁ → ∃ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (s : CMIn a e th jj n' La c₁), s.ξ = ξ ∧ s.ν₀ = ν₀ := by
  intro hK E _ _ _ H Dw l c K₁ _ _ _ a ρ σ₁ X ψ n' La c₁ ξ ν₀ jj hp hq hpq hσ hρ hLa hψ hact hn hτ hrk hξ hβ htr
  letI := H.starRing
  obtain ⟨th, hth⟩ := exists_section hK.laws2.secTwist a.D₀.P
  obtain ⟨v, hv⟩ := KeyPow.exists_isLieBasis a.D₀.P.A a.D₀.P.smoothDim
  have hf : 0 < Module.finrank ℚ E / 2 := by
    have e := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at e
    have : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  have gB : X.B.g = Module.finrank ℚ E / 2 * (Dw.p - 1 + (Dw.q - 1)) :=
    (GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K₁ ρ X.B ⟨a.D₀.P, ψ, hψ, v, hv⟩ _ _ X.split X.typeB X.ρ_sq).2.2.2.1
  have hg : 1 ≤ a.D₀.P.g := by
    rw [hψ.1]
    show 1 ≤ X.B.g
    rw [gB]
    exact Nat.mul_pos hf (by omega)
  have hlab : ∀ τ, τ ∈ psiSet H ↔ labK c K₁ τ (H.rt : E) = (ρ : K₁) := fun τ => by
    have e : σ₁ (labK c K₁ τ (H.rt : E)) = τ (H.rt : E) := RingHom.congr_fun hσ (embF c τ (H.rt : E))
    rw [← σ₁.injective.eq_iff, e, hρ]
    rfl
  let xB : KeyIn K₁ := ⟨a.D₀.P, hg, a.D₀.rig, a.D₀.rig_gen, th, hth, v, hv⟩
  obtain ⟨oa, oaΨ, oa', xΨ, x', φΨ, φ', τΨ, τ', ℓΨ, ℓ', Tl, LamL, hoa, -, -, hgood⟩ :=
    exists_lamObjGood_of_cmObj hK.laws2.secTwist hK.theta hK.laws hK.hom E H l c (fun _ => rfl) K₁ ρ σ₁ _ _ X La hlab
      hLa xB ψ ((isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 K₁) K₁) X.B.pol xB ψ).2 hψ)
  obtain ⟨L, hL, hm⟩ := exists_lamLetters_isGood E H l c _ _ _ _ La hgood
  obtain ⟨kind, hkind⟩ := exists_kind Dw.mult L.m (fun τ => by
    unfold Datum.mult
    split_ifs with h
    · rw [(hm τ).1 h]; omega
    · rw [(hm τ).2 h]; omega) L.e
  obtain ⟨sB, hsB⟩ := GlobalTheory.ArcCM.exists_isSplit hK K₁ a.D₀ n' hn hτ.1
  have tor : ∀ τ : E →+* ℂ, ∃ ν : Out.GtPt a.D₀ (epsR K₁), GtTanR ν ∧ ν.b = Out.DegPre.zeroT a.D₀ (epsR K₁) ∧
      ∀ x, DlogTan ν x (labK c K₁ τ (cc (pairE ξ x))) := fun τ =>
    ((GlobalTheory.TorusTangent.main hK.laws.globalFns K₁ a.D₀).1 (AddMonoidHom.mk' (fun x => labK c K₁ τ (cc (pairE ξ x)))
      fun x y => by rw [(pairE_properties E a.D₀.X ξ).2.1, cc, map_add (f := _), map_add (f := _)]; rfl)).exists
  have ab : ∀ m : Fin a.D₀.P.g, ∃ ν : Out.GtPt a.D₀ (epsR K₁), GtTanR ν ∧ ∃ w : epsR K₁ ⟶ a.D₀.P.A, L.IsLetter m w ∧
      Out.GtPt.IsPull (spMap (epsScaleR ((n' : K₁)⁻¹))) (sB (epsR K₁) w) ν := fun m => by
    obtain ⟨w, hw, hc⟩ := hL.2.2.1 m
    obtain ⟨ν, h₁, h₂⟩ := exists_scaled hsB ((n' : K₁)⁻¹) (w := w) (GlobalTheory.Reg.isTangent_of_isLieComb hv.1 hc)
    exact ⟨ν, h₁, w, hw, h₂⟩
  choose et het using tor
  choose ea hea using ab
  refine ⟨fun τ k => (kind τ k).elim (et τ) ea, th,
    { B := X.B.pol, oa := oa, AΨ := (X.A true).pol, oaΨ := oaΨ, A' := (X.A false).pol, oa' := oa'
      φΨ := fun i => X.φ (Sum.inl i), φ' := fun i => X.φ (Sum.inr i)
      hΨ := fun i => X.hh (Sum.inl i), h' := fun i => X.hh (Sum.inr i)
      g_pos := hg, th_nz := hth, v := v, basis := hv, xΨ := xΨ, x' := x', φB := ψ, φΨg := φΨ, φ'g := φ'
      τΨ := τΨ, τ' := τ', ℓΨ := ℓΨ, ℓ' := ℓ', Tl := Tl, LamL := LamL
      good := hgood, act := fun x => by rw [hoa]; exact hact x
      L := L, L_good := hL, n_pos := hn, tau := hτ, sB := sB, split := hsB, rk := hrk, ξ := ξ, ξ_ne := hξ
      ν₀ := ν₀, beta := hβ, tr := htr, kind := kind, full := hkind
      tan := fun τ k => ?_, xi := fun τ k h => ?_, eta := fun τ k m h => ?_ }, rfl, rfl⟩
  · cases kind τ k with
    | none => exact (het τ).1
    | some m => exact (hea m).1
  · rw [h]; exact (het τ).2
  · rw [h]; exact (hea m).2

end GlobalTheory.ArcCM.Letters
end
end

section

noncomputable section

namespace GlobalTheory.ArcCM

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.UnramTorsion GlobalTheory.BXOf GlobalTheory.TauTwist

theorem mem_range_units_of_pow {W K : Type} [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [Field K] [Algebra W K]
    [IsFractionRing W K] {m : ℕ} (hm : 0 < m) {x : Kˣ}
    (h : x ^ m ∈ (Units.map (algebraMap W K).toMonoidHom).range) : x ∈ (Units.map (algebraMap W K).toMonoidHom).range := by
  obtain ⟨u, hu⟩ := h
  have hu' : (x : K) ^ m = algebraMap W K u := (congrArg Units.val hu).symm
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := W) (K := K) (x := (x : K)) hm
    (hu' ▸ isIntegral_algebraMap)
  have e : y ^ m = u := IsFractionRing.injective W K (by rw [map_pow, hy, hu'])
  have hyu : IsUnit y := (isUnit_pow_iff hm.ne').1 (e ▸ u.isUnit)
  exact ⟨hyu.unit, Units.ext hy⟩

variable {R : Type} [CommRing R] [IsDomain R]

theorem psiUnitOn_near_of_tauCan [IsIntegrallyClosed R] (D : DegPre R) {n : ℕ} (hn : 0 < n) (hE : D.PsiEven)
    (hB : D.TauBimult) (hT : TauCan D n) (y : D.X) (P : PrimeSpectrum R) :
    ∃ V : (Sp R).Opens, P ∈ V ∧ PsiUnitOn D y V := by
  obtain ⟨hc, hκ⟩ := hT
  choose J₀ h₀ using fun x : D.P.A.left => exists_chart D.P.isLB x
  let W := Localization.AtPrime P.asIdeal
  have : IsFractionRing W (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.asIdeal.primeCompl _ _
  have : IsIntegrallyClosed W :=
    isIntegrallyClosed_of_isLocalization W P.asIdeal.primeCompl P.asIdeal.primeCompl_le_nonZeroDivisors
  let i : W →+* FractionRing R := algebraMap W (FractionRing R)
  let φ : R →+* W := algebraMap R W
  have sq : spMap i ≫ spMap φ = jK R := by
    rw [← spMap_comp]
    exact congrArg spMap (IsScalarTower.algebraMap_eq R W (FractionRing R)).symm
  have := D.P.isAb.proper
  have : D.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.P.A.hom]; infer_instance⟩
  obtain ⟨J, hJ, eJ⟩ := exists_good_ext D.P.isLB i (IsFractionRing.injective W (FractionRing R)) J₀ h₀
  let z : (TK R).left := closedPoint (FractionRing R)
  have hJ : Good D.P.L z J := hJ
  let H : Subgroup (FractionRing R)ˣ := (Units.map (algebraMap W (FractionRing R)).toMonoidHom).range
  obtain ⟨w, hw⟩ : ∃ w : ((TK R).left.presheaf.stalk z)ˣ →* (FractionRing R)ˣ ⧸ H,
      ∀ u, w u = 1 ↔ sig (FractionRing R) u ∈ H :=
    ⟨(QuotientGroup.mk' H).comp (sig (FractionRing R)), fun _ => QuotientGroup.eq_one_iff _⟩
  have tf : ∀ (m : ℕ) u, 0 < m → w u ^ m = 1 → w u = 1 := fun m u hm e => by
    rw [← map_pow, hw] at e
    exact (hw u).2 (mem_range_units_of_pow hm ((map_pow (sig (FractionRing R)) u m) ▸ e))
  have hint : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (ψ : K → (Y ⟶ D.P.A.left)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb D.P.L ψ ε)) (r : Sp R ⟶ Y) (q : (TK R).left ⟶ Y), q = jK R ≫ r → w (val t q z J) = 1 := by
    intro Y K _ ψ ε t r q hq
    obtain ⟨u, hu⟩ := val_integral i h₀ eJ t (spMap φ ≫ r)
    have : q = spMap i ≫ spMap φ ≫ r := by rw [hq, ← Category.assoc, sq]
    subst this
    exact (hw _).2 ⟨u, Units.ext hu.symm⟩
  let p : D.X → (FractionRing R)ˣ ⧸ H := fun a => w (val (D.psi a) (𝟙 (TK R).left) z J)
  have hadd : ∀ a b, p (a + b) = p a * p b := fun a b => by
    have e₁ : val (D.tau a b) (𝟙 (TK R).left) z J ^ n ^ 2 =
        val (D.tau (n • a) (n • b)) (𝟙 (TK R).left) z J * val (canK hc a b) (𝟙 (TK R).left) z J :=
      val_tau_pow hc hB a b (𝟙 (TK R)) hJ
    rw [← unitAt_kappa hc a b hJ, hκ, map_one, _root_.one_mul] at e₁
    have e₂ : w (val (canK hc a b) (𝟙 (TK R).left) z J) = 1 :=
      (congrArg w (val_pull hJ _ _ _)).trans (hint _ _ _ _ _ (𝟙 _) _ ((Category.id_comp _).trans (Category.comp_id _).symm))
    have e₃ : w (val D.rigK (𝟙 (TK R).left) z J) = 1 :=
      (congrArg w (val_pull hJ _ _ _)).trans (hint _ _ _ _ _ (𝟙 _) _ ((Category.id_comp _).trans (Category.comp_id _).symm))
    have e₄ := tf _ _ (pow_pos hn 2) ((map_pow w _ _).symm.trans ((congrArg w e₁).trans e₂))
    rw [val_tau D a b _ hJ, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, e₃, inv_one, _root_.mul_one,
      mul_inv_eq_one, mul_inv_eq_iff_eq_mul, mul_comm] at e₄
    exact e₄
  have heven : p (-y) = p y := by
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
      (val_corr hJ (hE y) (𝟙 (TK R).left))
    have r := hint _ _ _ _ D.sym (D.c y).left (𝟙 (TK R).left ≫ D.xK y) (Category.id_comp _)
    exact ((congrArg w e).symm.trans ((map_mul _ _ _).trans ((congrArg (_ * ·) r).trans (_root_.mul_one _)))).symm
  have p0 : p 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have py : p y = 1 := tf 2 _ two_pos (by
    have := hadd y (-y)
    rw [add_neg_cancel, p0, heven] at this
    exact (pow_two _).trans this.symm)
  have hcp : spMap φ (closedPoint W) = P := PrimeSpectrum.ext (Localization.AtPrime.under_maximalIdeal (I := P.asIdeal))
  have hj : J (𝟙 (TK R).left ≫ D.xK y) = J₀ ((D.c y).left P) := by
    have h : 𝟙 (TK R).left ≫ D.xK y = spMap i ≫ spMap φ ≫ (show Sp R ⟶ D.P.A.left from (D.c y).left) := by
      rw [← Category.assoc, sq]; exact Category.id_comp _
    exact (congrArg J h).trans ((eJ _).trans (congrArg (fun q => J₀ ((D.c y).left q)) hcp))
  obtain ⟨u, hu⟩ := (hw _).1 py
  rw [val_of (D.psi y) _ z J (fun _ => J₀ ((D.c y).left P)) fun _ => hj] at hu
  have e : (psiLoc D y (J₀ ((D.c y).left P)) : FractionRing R) = algebraMap W (FractionRing R) u :=
    (congrArg Units.val hu).symm
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj P.asIdeal.primeCompl (u : W)
  refine psiUnitOn_near y P _ (h₀ _) r s ?_ s.2 ?_
  · exact (IsLocalization.AtPrime.isUnit_to_map_iff W P.asIdeal r).1 (hrs ▸ u.isUnit.mul (IsLocalization.map_units _ s))
  · rw [e, IsScalarTower.algebraMap_apply R W (FractionRing R),
      IsScalarTower.algebraMap_apply R W (FractionRing R) r, ← map_mul]
    exact congrArg _ hrs

theorem psiUnitOn_of_tauCan : Known → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (D₀ : Out.DegPre R) (n : ℕ), 0 < n → D₀.PsiEven → D₀.TauBimult → TauCan D₀ n → ∀ y, PsiUnitOn D₀ y Set.univ :=
  fun _ _ _ _ _ _ D₀ _ hn hE hB hT y =>
    GlobalTheory.PsiAbelian.psiUnitOn_of_height_one D₀ y _ fun P _ _ => psiUnitOn_near_of_tauCan D₀ hn hE hB hT y P

end GlobalTheory.ArcCM
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.arcDatum_coefficientFunctional_linear_degree : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∃ φ : sec Xo c a' n →ₗ[c.F] K₁, ∀ F, φ F = cfOf d.yF d.μ d.jj F.1) ∧ ∀ F ∈ sec Xo c a' n, cfOf d.yF d.μ d.jj F ≠ 0 → ∑ v, d.μ v = absA Dw a' := by
  first | exact @GlobalTheory.ArcCM.cfOf_linear_and_degree | exact GlobalTheory.ArcCM.cfOf_linear_and_degree | (intros; apply GlobalTheory.ArcCM.cfOf_linear_and_degree <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem len_conj_of_lieNorm (hK : Known) {K : Type} [Field K] [NumberField K] (P : Out.PolAV (Sp K))
    (v : epsR K ⟶ P.A) (hv : IsTangent v) (ℓ : MLine K) (hℓ : ℓ.Good)
    (h : ∀ σ : K →+* ℂ, Arch.IsLieNormAt P v σ (Real.log (ℓ.n σ))) (em : K →+* ℂ) :
    ℓ.n ((starRingEnd ℂ).comp em) = ℓ.n em := by
  have h1 := (GlobalTheory.ArchConj.norms_conj hK K P em _).2 v (h em)
  have h2 := (GlobalTheory.T.thetaNorm_lieNorm_unique_at_embedding hK K P _ _ _).2 v hv (h ((starRingEnd ℂ).comp em)) h1
  exact Real.log_injOn_pos (hℓ.2 _) (hℓ.2 _) h2

theorem valLine_conj : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (mo : ArcLt Dw →₀ ℕ) (n : ℕ) (em : K₁ →+* ℂ), (s.valLine mo n).n ((starRingEnd ℂ).comp em) = (s.valLine mo n).n em := by
  intro hK E _ _ _ H Dw l c K₁ _ _ _ a e th jj n' La c₁ s mo n em
  letI := H.starRing
  have tie := GlobalTheory.T.cm_metrised_line_lengths_eq_section_lie_norms hK E H Dw l c K₁ a e th jj n' La c₁ s
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hΨ, h', hT, -⟩ := s.good
  have hTl : s.Tl.n ((starRingEnd ℂ).comp em) = s.Tl.n em := by
    have h1 := (GlobalTheory.ArchConj.norms_conj hK K₁ a.D₀.P em _).1 a.D₀.rig th (tie em).1
    have h2 := (GlobalTheory.T.thetaNorm_lieNorm_unique_at_embedding hK K₁ a.D₀.P _ _ _).1 a.D₀.rig th a.D₀.rig_gen (tie ((starRingEnd ℂ).comp em)).1 h1
    exact (sq_eq_sq₀ (hT.2 _).le (hT.2 _).le).1 h2
  have hL : ∀ m, (s.L.ℓ m).n ((starRingEnd ℂ).comp em) = (s.L.ℓ m).n em := by
    intro m
    have hm := s.L_good.2.2.2 m
    rcases hq : s.L.src m with q | q
    · rw [hq] at hm
      have hm' : s.L.ℓ m = s.ℓΨ q.2 := hm
      rw [hm']
      exact len_conj_of_lieNorm hK s.xΨ.P (s.xΨ.v q.2) (s.xΨ.basis.1 q.2) _ (hΨ q.2).1
        (fun σ => (tie σ).2.1 q.2) em
    · rw [hq] at hm
      have hm' : s.L.ℓ m = s.ℓ' q.2 := hm
      rw [hm']
      exact len_conj_of_lieNorm hK s.x'.P (s.x'.v q.2) (s.x'.basis.1 q.2) _ (h' q.2).1
        (fun σ => (tie σ).2.2.1 q.2) em
  have hline : ∀ τ k, (s.line τ k).n ((starRingEnd ℂ).comp em) = (s.line τ k).n em := by
    intro τ k
    unfold CMIn.line
    rcases s.kind τ k with _ | m
    · rfl
    · exact hL m
  simp only [CMIn.valLine, MLine.tensor, MLine.pow, MLine.dual, MLine.prodPow, hTl, hline]

end GlobalTheory.ArcCM
end

section

noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem eq_at_zero_of_eq_off_zeros {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {F p q : V → ℂ}
    (hF : Continuous F) (hp : Differentiable ℂ p) (hq : Differentiable ℂ q) {v₀ : V} (h₀ : F v₀ ≠ 0)
    (h : ∀ v, F v ≠ 0 → p v = q v) : p 0 = q 0 := by
  have hl : Differentiable ℂ fun t : ℂ => t • v₀ := differentiable_id.smul_const _
  have h1 : AnalyticOnNhd ℂ (fun t : ℂ => p (t • v₀)) Set.univ := fun t _ => (hp.comp hl).analyticAt t
  have h2 : AnalyticOnNhd ℂ (fun t : ℂ => q (t • v₀)) Set.univ := fun t _ => (hq.comp hl).analyticAt t
  have h3 : ∀ᶠ t in nhds (1 : ℂ), F (t • v₀) ≠ 0 :=
    (hF.comp hl.continuous).continuousAt.eventually_ne (by simpa using h₀)
  have h4 := AnalyticOnNhd.eq_of_eventuallyEq h1 h2 (h3.mono fun t ht => h _ ht)
  simpa using congrFun h4 0

theorem isFnInRigFrame_of_isFn {D₀ : Out.DegPre ℂ} {n g : ℕ} (u : HolUnif D₀.P.A D₀.P.L n) (hr : u.IsRig D₀.rig)
    {th : D₀.P.L.Sec} {θ : (Fin n → ℂ) → ℂ} (hθ : u.IsFn th θ) {p : (Fin g → ℂ) → (Fin n → ℂ)}
    (hp : Differentiable ℂ p) (hp0 : p 0 = 0) {Q ϑ : (Fin g → ℂ) → ℂ} (hQ : Differentiable ℂ Q) (hQ0 : Q 0 = 0)
    (h : ∀ z, θ (p z) = Complex.exp (Q z) * ϑ z) :
    IsFnInRigFrame D₀ (fun z => (u.ex (p z)).left) th ϑ := by
  refine ⟨fun j z => Complex.exp (Q z) * u.fr j (p z), fun j => ?_, fun j z hz => ?_, fun j j' z hz => ?_,
    fun j hj => ?_, fun j z hz => ?_⟩
  · exact hQ.cexp.differentiableOn.mul ((u.fr_hol j).comp hp.differentiableOn fun z hz => hz)
  · exact mul_ne_zero (Complex.exp_ne_zero _) (u.fr_ne j _ hz)
  · beta_reduce
    rw [u.fr_compat j j' _ hz]
    ring
  · have e1 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
    have e2 : (u.ex 0).left = eSec D₀.P.A := by
      rw [e1, Hom.one_def, toUnit_unit, Category.id_comp]
      rfl
    beta_reduce at hj ⊢
    rw [hp0, e2] at hj
    rw [hQ0, hp0, Complex.exp_zero, _root_.one_mul]
    exact hr (fun _ => j) fun x hx => Set.mem_iInter.2 fun _ => hj hx
  · beta_reduce
    rw [hθ j _ hz, h]
    ring



theorem arc_theta : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (laA laM : D.La → Λ.A.La) (K : Cmp Fu Λ.A Ψ.yw Ψ.pi laA laM), AnFin Λ.A → ∀ lin cst (T₁ : ℝ), (∀ w : ℂ, T₁ < w.im → IsFibAt Λ.A Xo.univ.t lin cst w (Ψ.yw w) (Ψ.pi w) (Ψ.fr w)) → ∃ T₂ : ℝ, ∀ T ≥ T₂, ∀ (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (Fu.Di K.i).La) (S : Finset (Fin g)) (h : Matrix (Fin g) (Fin g) ℂ) (τ : ℂ → Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)) (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)), ThetaHyp W th σ fam → (∀ u v, (Fu.Di K.i).EF (bas u) (bas v) = -omegaStd u v) → (∀ u, Λ.ε (K.gam (bas u)).y = 0 ↔ ∀ k ∈ S, u (.inr k) = 0) → (∀ w k, h.mulVec (K.Pw w (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ h.mulVec (K.Pw w (bas (Pi.single (.inr k) 1))) = (τ w).mulVec (Pi.single k 1)) → (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂ → IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ → IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ → (∃ w fr, T < w.im ∧ IsThetaFrameAt Xo.univ.t.PP (Fu.u K.i (K.Pw w)) (fun z => (Fu.ex K.i (K.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr) → ∃ κ : ℂ, κ ≠ 0 ∧ (∀ k ∈ S, c₁ k = 0) ∧ (∀ w : ℂ, T < w.im → IsFnInRigFrame a.D₀ (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 (K.h.symm z)).b.left)) th (fun z => κ * thetaCharOff S (τ w) c₁ c₂ (h.mulVec z))) ∧ ∀ (U : Y.X.Opens) (s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)) (r : PowerSeries ℂ), ⊤ ≤ χ ⁻¹ᵁ U → s ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ U) → PullHyp W σ w₂ U s r → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∃ rw : ℂ, SumsAt r w rw ∧ ∀ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u K.i (K.Pw w)) (fun z => (Fu.ex K.i (K.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr → ∀ (z : Fin g → ℂ) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Fu.ex K.i (K.Pw w) z).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (s j) = valAt' x _ (w₁.s (fun _ => j, k)).val * (κ * rw * thetaChar (τ w) c₁ c₂ (h.mulVec z) * fr j₀ z) := by
  intro hL hL2 E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C Γ Ψ g ty Fu laA laM K hfin lin cst T₁ hfib
  obtain ⟨T₀, hT⟩ := Λ.A.exists_isConvLine
  refine ⟨max T₀ (max T₁ K.T), fun T hTT th σ fam bas S h τ c₁ c₂ w₂ w₁ w₀ hth hEF hS hP hc₁ hc₂ r₂ r₁ r₀ hex => ?_⟩
  have hT0 : T₀ ≤ T := (le_max_left _ _).trans hTT
  have hT1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hTT
  have hTK : K.T ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hTT
  obtain ⟨θ, hθ, hθ0, hfn⟩ := (ArcThetaSpaces.sections_theta hL hL2 E H D l c O β _ a Λ).2.2 th hth.1
  let bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] Λ.A.La := bas.trans (K.gam.toAddEquiv.toIntLinearEquiv)
  have hb : ∀ u, bas' u = K.gam (bas u) := fun _ => rfl
  obtain ⟨hu, hτ, d₁, d₂, -, -, hdS, ⟨Q, κ, -, hQ, hQ0, hκ, hSum, hoff⟩, huniq⟩ :=
    Λ.A.theta_comparison hT K.h.toLinearEquiv hθ hθ0 bas' (fun u v => by rw [hb, hb, K.EF_eq, hEF]) S
      (fun u => by rw [← hS, hb, map_eq_zero_iff _ Λ.ε.injective]) h τ
      (fun w k => by simpa only [hb, K.Pw_eq, ContinuousLinearEquiv.coe_toLinearEquiv] using hP w k)
  simp only [ContinuousLinearEquiv.coe_toLinearEquiv] at hSum hoff huniq
  have hSne : ∀ w : ℂ, T₀ < w.im → ∃ v, Λ.A.Sum 1 0 θ w v ≠ 0 := fun w hw => by
    obtain ⟨v, hv⟩ := Λ.A.exists_Sum_ne_zero one_ne_zero 0 hθ0 fun z =>
      AnArc.summable_term hT one_ne_zero hθ hw (0, z)
    exact ⟨_, hv⟩
  have key : ∀ w : ℂ, T < w.im → ∀ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u K.i (K.Pw w))
      (fun z => (Fu.ex K.i (K.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr →
      ∃ (lam : ℂ) (f : Λ.A.V → ℂ), lam ≠ 0 ∧ Differentiable ℂ f ∧ (∀ v, f v ≠ 0) ∧ f 0 = 1 ∧
        (∀ v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (K.h v) = f v * Ψ.fr w j v) ∧
        ∀ v, Λ.A.Sum 1 0 θ w v = lam * thetaChar (τ w) c₁ c₂ (h.mulVec (K.h v)) * f v := by
    intro w hw fr hfr
    have hw0 := hT0.trans_lt hw
    have tr : ∀ (y y' : Sp ℂ ⟶ Xo.X) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Xo.univ.t.G.left)) ϑ, y = y' →
        IsThetaFrameAt Xo.univ.t.PP y e ϑ fr → IsThetaFrameAt Xo.univ.t.PP y' e ϑ fr := by
      rintro y _ e ϑ rfl h
      exact h
    refine GlobalTheory.T.two_rigidified_theta_frames_on_fibre hL hL2 E H D l Xo Λ.A lin cst w (Ψ.yw w) (Ψ.pi w) (Ψ.fr w) g K.h _ _ fr
      (hfib w (hT1.trans_lt hw)) (K.ex_eq w (hTK.trans_lt hw)) (tr _ _ _ _ (K.u_eq w (hTK.trans_lt hw)) hfr) ?_ θ hθ
      (hSne w hw0)
    obtain ⟨z, hz⟩ := Function.ne_iff.1 (TorusAlg.thetaChar_level (hτ w hw0).1 (hτ w hw0).2 hc₁ hc₂).1
    obtain ⟨z', rfl⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hu z
    exact ⟨z', hz⟩
  obtain ⟨rfl, rfl⟩ : c₁ = d₁ ∧ c₂ = d₂ := by
    obtain ⟨w, fr, hw, hfr⟩ := hex
    obtain ⟨lam, f, hlam, hf, hf0, -, -, hfS⟩ := key w hw fr hfr
    exact huniq c₁ c₂ hc₁ hc₂ w (hT0.trans_lt hw) (fun v => lam * f v) (hf.const_mul _)
      (fun v => mul_ne_zero hlam (hf0 v)) fun v => by rw [hfS]; ring
  refine ⟨κ, hκ, hdS, fun w _ => ?_, fun U s r hU _ hpull => ?_⟩
  · have e : (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 (K.h.symm z)).b.left)) =
        fun z => (Λ.u.ex (K.h.symm z).2).left := funext fun z => Λ.ex0_b _
    rw [e]
    refine isFnInRigFrame_of_isFn Λ.u Λ.rig hfn (p := fun z => (K.h.symm z).2) K.h.symm.differentiable.snd
      (by simp) (Q := fun z => Q (K.h.symm z)) (hQ.comp K.h.symm.differentiable) (by simp [hQ0]) fun z => ?_
    rw [hoff w, ContinuousLinearEquiv.apply_symm_apply]
    ring
  · obtain ⟨T', hT'⟩ := GlobalTheory.T.arcSection_value_at_specialised_points_theta hL hL2 E H D l Xo c O β Y bF a χ W Λ C Γ Ψ th σ fam θ w₂ w₁ w₀ U s r hfin hth hθ
      hθ0 hfn r₂ r₁ r₀ hU hpull
    refine ⟨max T T', fun w hw => ?_⟩
    have hw1 : T < w.im := (le_max_left _ _).trans_lt hw
    have hw0 := hT0.trans_lt hw1
    obtain ⟨rw, hrw, hval⟩ := hT' w ((le_max_right _ _).trans_lt hw)
    refine ⟨rw, hrw, fun fr hfr z x j k j₀ hx hx' hj hj₀ => ?_⟩
    obtain ⟨v, rfl⟩ := K.h.surjective z
    obtain ⟨lam, f, hlam, hf, hf0, hf1, hfr', hfS⟩ := key w hw1 fr hfr
    obtain ⟨v₀, hv₀⟩ := hSne w hw0
    have hlk : lam = κ := by
      have := eq_at_zero_of_eq_off_zeros (AnArc.differentiable_Sum hT one_ne_zero hθ hw0).continuous
        (hf.const_mul lam) (hQ.cexp.const_mul κ) hv₀ fun v hv => by
          have h1 := hfS v
          have h2 : thetaChar (τ w) c₁ c₂ (h.mulVec (K.h v)) ≠ 0 := fun h0 => hv (by rw [h1, h0]; simp)
          refine mul_right_cancel₀ h2 ?_
          rw [← hSum w hw0 v, h1]
          ring
      simpa [hf1, hQ0] using this
    have hx2 : x ≫ Y.m0.toSABMap.φ = (Ψ.pi w v).left := hx.trans (K.ex_eq w (hTK.trans_lt hw1) v)
    have hch : ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j₀ := by
      rw [← hx2]
      exact fun p hp => Set.mem_iInter.1 (hj₀ hp).1 PUnit.unit
    rw [hval v x j k j₀ hx2 hx' hj hj₀, hfr' v j₀ hch, hfS, hlk]
    ring

end GlobalTheory.ArcPts
end
end
