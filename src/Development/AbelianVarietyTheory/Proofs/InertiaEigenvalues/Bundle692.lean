module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle640
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle669
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDeRhamPlusActionConstantsGaloisComm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle677
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle670
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnimodularBlockUpperTriangularSymmetricLevels
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.bcrisTensorLattice_to_deRham_equivariant : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL) (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (g : Gl l) (b : TW (OB l ↥(OL LL)) T), X (actB (sQ l) T g b) = actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (X b) := by
  exact @GlobalTheory.BKGal.JumpDR.X_equivariant
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.coeffDeRhamPlusAction_mul_one : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → (∀ (d d' : OD l ↥(OL LL)) (w : T.V ⊗[ℚ_[l]] Pl.R.BdR), act (d * d') w = act d (act d' w)) ∧ ∀ w : T.V ⊗[ℚ_[l]] Pl.R.BdR, act 1 w = w := by
  first | exact @GlobalTheory.BKGal.JumpDR.odAct_mul_one | exact GlobalTheory.BKGal.JumpDR.odAct_mul_one | (intros; apply GlobalTheory.BKGal.JumpDR.odAct_mul_one <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.eisenstein_mul_bijective_shifts_filtrationV : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → Function.Bijective (A (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e))) ∧ ∀ (y : T.V ⊗[ℚ_[l]] Pl.R.BdR) (j : ℤ), y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j) ↔ A (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e)) y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j + 1) := by
  first | exact @GlobalTheory.BKReal.EhatShift.bijective_and_mem_FilV_iff | exact GlobalTheory.BKReal.EhatShift.bijective_and_mem_FilV_iff | (intros; apply GlobalTheory.BKReal.EhatShift.bijective_and_mem_FilV_iff <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.exists_bcrisTensorLattice_to_deRham_map : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL), ∃ X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR, ∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b := by
  exact @GlobalTheory.BKGal.CrisTensDR.main
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_coeffDeRhamPlus_action_on_VTensorBdR : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL), ∃ A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c) := by
  first | exact @GlobalTheory.BKGal.JumpDR.exists_odAction | exact GlobalTheory.BKGal.JumpDR.exists_odAction | (intros; apply GlobalTheory.BKGal.JumpDR.exists_odAction <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.coeffDeRhamPlusAction_constants_galois_comm : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL) (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (c : ZMod a → AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : ↥LL.1))) (g : Gl l), (g : GQ l) ∈ GK (ϖ.field a) → ∀ y : T.V ⊗[ℚ_[l]] Pl.R.BdR, actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (A (ϖ.iD (thetaW a LL) ↥LL.1 (GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) c)) y) = A (ϖ.iD (thetaW a LL) ↥LL.1 (GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) c)) (actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g y) := by
  first | exact @GlobalTheory.BKGal.JumpConst.actVdR_comm_kLift | exact GlobalTheory.BKGal.JumpConst.actVdR_comm_kLift | (intros; apply GlobalTheory.BKGal.JumpConst.actVdR_comm_kLift <;> assumption)
end

section

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.WeilDeligne GlobalTheory.Pst
open GlobalTheory.BKReal IsLocalRing Formalism.BasicNotions.Examples₂.LB

namespace GlobalTheory.AinfK

theorem fK_eq_resDeg {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w)
    (hj : Induces Bw) : fK Bw.Kw = resDeg l w := by
  have hN := normV_eq_pow (hj.mem_placesOver h)
  refine Nat.pow_right_injective hl.out.two_le (le_antisymm ?_ ?_)
  · obtain ⟨-, ω, hω, -⟩ := exists_gen l (fK Bw.Kw)
    have h1 := one_lt_pow_l l (fK Bw.Kw)
    have hm : ω ∈ K0 Bw.Kw := Kunr_fK Bw.Kw ▸ IntermediateField.subset_adjoin _ _ (show ω ^ l ^ fK Bw.Kw = ω by
      rw [← Nat.sub_add_cancel h1.le, pow_succ, hω.pow_eq_one, one_mul])
    have h2 := weilToGK_frobUr hj (frob h) (a := 1) (b := 0) (actsAs_of_deg (by simp)) ⟨ω, hm.2⟩
    rw [mul_one, mul_zero, pow_zero, frobUr_pow_root _ _ (l ^ fK Bw.Kw - 1) (by omega)
      (fun hd => hl.out.not_dvd_one ((Nat.dvd_sub_iff_right h1.le (dvd_pow_self l (NeZero.ne _))).1 hd))
      (Subtype.ext hω.pow_eq_one)] at h2
    have h3 : ω = ω ^ l ^ resDeg l w :=
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 (weilToGK Bw h (frob h)).2 _ hm.1).symm.trans h2
    have h4 := one_lt_normV w
    rw [hN] at h4
    have h5 : ω ^ (l ^ resDeg l w - 1) = 1 := mul_right_cancel₀ (hω.ne_zero (by omega)) (by
      rw [← pow_succ, Nat.sub_add_cancel h4.le, one_mul, ← h3])
    have := Nat.le_of_dvd (by omega) (hω.dvd_of_pow_eq_one _ h5)
    change l ^ _ ≤ l ^ _
    omega
  · change l ^ _ ≤ l ^ _
    rw [← hN, ← card_res]
    let u : 𝓞 E →+* ↥Bw.Kw.1 :=
      (Bw.j.comp ((algebraMap E Ω).comp (algebraMap (𝓞 E) E))).codRestrict Bw.Kw.1 fun x => Bw.j_E _
    let v : 𝓞 E →+* ↥(OL Bw.Kw) := u.codRestrict (OL Bw.Kw) fun x =>
      (map_isIntegral_int u (RingOfIntegers.isIntegral x)).tower_top
    have hk : ∀ x, ((residue _).comp v) x = 0 ↔ x ∈ w.asIdeal := fun x => by
      rw [RingHom.comp_apply, residue_eq_zero_iff, mem_max, ← h x, hj.valuation_lt_one_iff]
      rfl
    have := OL_resFinite Bw.Kw
    exact Nat.card_le_card_of_injective (Ideal.Quotient.lift w.asIdeal _ fun x hx => (hk x).2 hx)
      (RingHom.lift_injective_of_ker_le_ideal _ _ fun x hx => (hk x).1 hx)

end GlobalTheory.AinfK
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix


theorem _root_.GlobalTheory.T.coeff_eq_zero_of_roots_contain_lth_roots_conjugates : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (E : Polynomial (Wq l a)), E.Monic →
    Irreducible (E.map (GlobalTheory.TameFrob.iota l a)) → ∀ z : Om l, z ≠ 0 →
    (∀ z' : Om l, Polynomial.aeval z' (minpoly (↥(Kunr l a)) z) = 0 → ∀ y : Om l, y ^ l = z' →
      (E.map (GlobalTheory.TameFrob.iotaO l a)).IsRoot y) →
    ∀ i, ¬ l ∣ i → E.coeff i = 0 := by
  first | exact @GlobalTheory.ExpandCoeff.coeff_eq_zero_of_roots | exact GlobalTheory.ExpandCoeff.coeff_eq_zero_of_roots | (intros; apply GlobalTheory.ExpandCoeff.coeff_eq_zero_of_roots <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix


theorem _root_.GlobalTheory.T.exists_algEquiv_extending_wittTiltFrobenius : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a], ∃ Φ : Om l ≃ₐ[ℚ_[l]] Om l,
    ∀ w : Wq l a, Φ (GlobalTheory.TameFrob.iotaO l a w) = GlobalTheory.TameFrob.iotaO l a (sigma l a w) := by
  first | exact @GlobalTheory.TameFrob.exists_algEquiv_iotaO_sigma | exact GlobalTheory.TameFrob.exists_algEquiv_iotaO_sigma | (intros; apply GlobalTheory.TameFrob.exists_algEquiv_iotaO_sigma <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix


theorem _root_.GlobalTheory.T.irreducible_map_unramifiedWittToFractionField_of_eisenstein : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (E : Polynomial (Wq l a)), E.Monic → 0 < E.natDegree →
    (∀ i < E.natDegree, (l : Wq l a) ∣ E.coeff i) → (∃ w : (Wq l a)ˣ, E.coeff 0 = (l : Wq l a) * w) →
    Irreducible (E.map (GlobalTheory.TameFrob.iota l a)) := by
  first | exact @GlobalTheory.TameFrob.irreducible_map_iota_of_eisenstein | exact GlobalTheory.TameFrob.irreducible_map_iota_of_eisenstein | (intros; apply GlobalTheory.TameFrob.irreducible_map_iota_of_eisenstein <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix


theorem _root_.GlobalTheory.T.norm_lt_one_of_isRoot_distinguished_witt_polynomial : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P : Polynomial (Wq l a)), P.Monic →
    (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) → ∀ x : Om l, (P.map (GlobalTheory.TameFrob.iotaO l a)).IsRoot x → ‖x‖ < 1 := by
  first | exact @GlobalTheory.RootLt.norm_lt_one_of_isRoot | exact GlobalTheory.RootLt.norm_lt_one_of_isRoot | (intros; apply GlobalTheory.RootLt.norm_lt_one_of_isRoot <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh MeasureTheory Matrix

namespace GlobalTheory.DiscreteUnit

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [Countable Γ]

theorem lintegral_lt_top {μ μ' : Measure G} [μ.IsHaarMeasure] [μ'.IsHaarMeasure] {F F' : Set G}
    (hF : IsFundamentalDomain Γ F μ) (hF' : IsFundamentalDomain Γ F' μ') {φ : G → ENNReal}
    (hφ : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) (h : ∫⁻ g in F', φ g ∂μ' < ⊤) : ∫⁻ g in F, φ g ∂μ < ⊤ := by
  have e := Measure.isMulLeftInvariant_eq_smul μ μ'
  have hF2 : IsFundamentalDomain Γ F' μ := hF'.mono (Measure.absolutelyContinuous_isHaarMeasure μ μ')
  rw [hF.setLIntegral_eq hF2 φ fun γ g => hφ γ γ.2 g, e, Measure.restrict_smul, lintegral_smul_measure]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top h

theorem integral_mul_right {μ : Measure G} [μ.IsHaarMeasure] {F : Set G} (hF : IsFundamentalDomain Γ F μ) {φ : G → ℂ}
    (hφ : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) {x : G} (hx : Measure.modularCharacter x = 1) :
    ∫ g in F, φ (g * x) ∂μ = ∫ g in F, φ g ∂μ := by
  have hm : MeasurePreserving (fun g => g * x) μ μ :=
    ⟨measurable_mul_const x, by rw [GlobalTheory.LevelUnimod.map_mul_right_eq, hx, one_smul]⟩
  have hF2 : IsFundamentalDomain Γ ((fun g => g * x) ⁻¹' F) μ :=
    hF.preimage_of_equiv hm.quasiMeasurePreserving Function.bijective_id fun γ g => mul_assoc γ.1 g x
  rw [hF.setIntegral_eq hF2 (f := fun g => φ (g * x)) fun γ g => by
    change φ (γ.1 * g * x) = _
    rw [mul_assoc, hφ γ γ.2]]
  exact hm.setIntegral_preimage_emb (MeasurableEquiv.mulRight x).measurableEmbedding φ F

theorem isUnitarisable_of_embedding {H X : Type} [Group H] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H X)
    (ι : H → G) (hι : ∀ h, Measure.modularCharacter (ι h) = 1) (f : X →ₗ[ℂ] (G → ℂ)) (hf : Function.Injective f)
    (hc : ∀ v, Continuous (f v)) (hl : ∀ v, ∀ γ ∈ Γ, ∀ g, f v (γ * g) = f v g)
    (h2 : ∀ v, ∃ (μ : Measure G) (F : Set G), μ.IsHaarMeasure ∧ IsFundamentalDomain Γ F μ ∧
      ∫⁻ g in F, ‖f v g‖ₑ ^ 2 ∂μ < ⊤)
    (hρ : ∀ h v g, f (ρ h v) g = f v (g * ι h)) : IsUnitarisable ρ := by
  obtain ⟨μ, F, hμ, hF, -⟩ := h2 0
  have hm : ∀ v, MemLp (f v) 2 (μ.restrict F) := fun v => by
    obtain ⟨μ', F', hμ', hF', h⟩ := h2 v
    have h3 := lintegral_lt_top hF hF' (fun γ hγ g => by rw [hl v γ hγ g]) h
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    · simpa using h3
    · exact (hc v).aestronglyMeasurable
  have hi : ∀ v w, Integrable (fun g => f v g * starRingEnd ℂ (f w g)) (μ.restrict F) := fun v w =>
    (hm v).integrable_mul (hm w).star
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => ∫ g in F, f v g * starRingEnd ℂ (f w g) ∂μ)
    (fun v v' w => ?_) (fun c v w => ?_) (fun v w w' => ?_) (fun c v w => ?_), fun v w => ?_, fun v hv => ?_,
    fun h v w => ?_⟩
  · rw [← integral_add (hi _ _) (hi _ _)]
    simp [add_mul]
  · simp [mul_assoc, integral_const_mul]
  · rw [← integral_add (hi _ _) (hi _ _)]
    simp [mul_add]
  · simp [mul_left_comm _ (starRingEnd ℂ c), integral_const_mul]
  · simp only [LinearMap.mk₂'ₛₗ_apply]
    rw [← integral_conj]
    simp [mul_comm]
  · simp only [LinearMap.mk₂'ₛₗ_apply, Complex.mul_conj]
    rw [integral_complex_ofReal, Complex.ofReal_re]
    have hi2 : Integrable (fun g => Complex.normSq (f v g)) (μ.restrict F) := by
      simpa [Complex.mul_conj] using (hi v v).re
    refine (integral_pos_iff_support_of_nonneg (fun g => Complex.normSq_nonneg _) hi2).2 (pos_iff_ne_zero.2 fun h0 => hv ?_)
    have ho : IsOpen (Function.support fun g => Complex.normSq (f v g)) :=
      (Complex.continuous_normSq.comp (hc v)).isOpen_support
    rw [Measure.restrict_apply ho.measurableSet] at h0
    have h4 := hF.measure_zero_of_invariant _ (fun γ => by
      ext g
      rw [Set.mem_smul_set_iff_inv_smul_mem, Function.mem_support, Function.mem_support]
      change Complex.normSq (f v ((γ⁻¹ : Γ).1 * g)) ≠ 0 ↔ _
      rw [hl v _ (γ⁻¹).2]) h0
    have h5 := Function.support_eq_empty_iff.1 (ho.measure_eq_zero_iff μ |>.1 h4)
    refine hf (funext fun g => ?_)
    rw [map_zero]
    exact Complex.normSq_eq_zero.1 (congrFun h5 g)
  · simp only [LinearMap.mk₂'ₛₗ_apply, hρ]
    exact integral_mul_right hF (φ := fun g => f v g * starRingEnd ℂ (f w g))
      (fun γ hγ g => by rw [hl v γ hγ, hl w γ hγ]) (hι h)

end General

def transInv (A : Type) [CommRing A] (n : ℕ) : GL (Fin n) A ≃* GL (Fin n) A where
  toFun g := ⟨(g⁻¹).valᵀ, g.valᵀ, by rw [← transpose_mul]; simp, by rw [← transpose_mul]; simp⟩
  invFun g := ⟨(g⁻¹).valᵀ, g.valᵀ, by rw [← transpose_mul]; simp, by rw [← transpose_mul]; simp⟩
  left_inv g := Units.ext (transpose_transpose _)
  right_inv g := Units.ext (transpose_transpose _)
  map_mul' g h := Units.ext (by
    change ((g * h)⁻¹).valᵀ = (g⁻¹).valᵀ * (h⁻¹).valᵀ
    rw [← transpose_mul, _root_.mul_inv_rev, Units.val_mul])

theorem continuous_transInv (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (n : ℕ) :
    Continuous (transInv A n) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem cornerGL_transInv {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (s : R →ₙ+* S) (g : GL (Fin n) R) :
    cornerGL n s (transInv R n g) = transInv S n (cornerGL n s g) := by
  ext i j
  change (1 : Matrix (Fin n) (Fin n) S) i j - s ((1 : Matrix (Fin n) (Fin n) R) i j) + s ((g⁻¹).val j i) =
    (1 : Matrix (Fin n) (Fin n) S) j i - s ((1 : Matrix (Fin n) (Fin n) R) j i) + s ((g⁻¹).val j i)
  simp only [Matrix.one_apply, eq_comm]

theorem modular_eq_one {k S : Type} [Field k] [Infinite k] [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] {n : ℕ}
    [LocallyCompactSpace (GL (Fin n) S)] [SecondCountableTopology (GL (Fin n) S)] (ι : GL (Fin n) k →* GL (Fin n) S)
    (h : ∀ g, ι (transInv k n g) = transInv S n (ι g)) (g : GL (Fin n) k) : Measure.modularCharacter (ι g) = 1 := by
  borelize (GL (Fin n) S)
  refine GlobalTheory.gl_character_eq_one_of_transpose_inv _ _ (Measure.modularCharacter.comp ι) (fun g g' e => ?_) g
  obtain rfl : g' = transInv _ n g := Units.ext e
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h]
  exact GlobalTheory.LevelUnimod.modular_aut _ (continuous_transInv _ n) (continuous_transInv _ n) _

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem countable_latticeGL : Countable (latticeGL E N) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin N) (Fin N) E) := inferInstanceAs (Countable (Fin N → Fin N → E))
  haveI : Countable (GL (Fin N) E) := Units.val_injective.countable
  let f : FreeGroup (Option (GL (Fin N) E)) →* GA E N :=
    FreeGroup.lift fun o => o.elim (splitCentre E N 1) (ratGL E N)
  have h : latticeGL E N ≤ f.range := sup_le
    (by rintro _ ⟨γ, rfl⟩; exact ⟨.of (some γ), FreeGroup.lift_apply_of⟩)
    (Subgroup.zpowers_le.2 ⟨.of none, FreeGroup.lift_apply_of⟩)
  haveI : Countable (FreeGroup (Option (GL (Fin N) E))) := Quot.mk_surjective.countable
  exact ((Set.countable_range f).mono h).to_subtype

theorem left_latticeGL {φ : Sm E N} (h : IsAutForm φ) (h' : IsSqInt φ.1) :
    ∀ γ ∈ latticeGL E N, ∀ g, φ.1 (γ * g) = φ.1 g := by
  let S : Subgroup (GA E N) :=
    { carrier := {γ | ∀ g, φ.1 (γ * g) = φ.1 g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy]
      inv_mem' := fun {x} hx g => by rw [← hx, mul_inv_cancel_left] }
  have : latticeGL E N ≤ S := sup_le (by
    intro x hx
    obtain ⟨γ, rfl⟩ := (show x ∈ (ratGL E N).range from hx)
    exact h.left γ) (Subgroup.zpowers_le.2 (h'.1 1))
  exact this

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem isUnitarisable_of_isLocCompGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ)
    (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : LocIrr w N),
    IsLocCompGL V w σ → IsUnitarisable σ.ρ := by
  intro E _ _ _ N V hV w σ ⟨f, h0, hf, hρ⟩
  letI : MeasurableSpace (GA E N) := borel _
  haveI : BorelSpace (GA E N) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin N → Fin N → Ad E))
  haveI : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GA E N) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GA E N) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI := countable_latticeGL (E := E) (N := N)
  haveI : Infinite (w.adicCompletion E) := .of_injective _ (algebraMap E _).injective
  have hinj : Function.Injective f := by
    rcases ((GlobalTheory.CuspRep.isIrreducible_iff _).1 σ.irred).2 (LinearMap.ker f) (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hρ, hv, map_zero]) with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exact absurd (LinearMap.ker_eq_top.1 h) h0
  refine isUnitarisable_of_embedding (Γ := latticeGL E N) σ.ρ (fun g => finGL E N (locGL E N w g)) (fun g => ?_)
    ((Sm E N).subtype.comp f) (Subtype.val_injective.comp hinj)
    (fun v => GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E N (f v) (hV.aut _ (hf v)).level)
    (fun v => left_latticeGL (hV.aut _ (hf v)) (hV.sqInt _ (hf v))) (fun v => (hV.sqInt _ (hf v)).2)
    fun g v x => congrFun (congrArg Subtype.val (hρ g v)) x
  exact modular_eq_one ((finGL E N).comp (locGL E N w))
    (fun g => (congrArg (finGL E N) (cornerGL_transInv (sLoc E w) g)).trans (cornerGL_transInv (sFin E) _)) g

end GlobalTheory.DiscreteUnit
end
