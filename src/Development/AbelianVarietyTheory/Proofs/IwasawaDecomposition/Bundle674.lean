module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle654
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelsIsHolomorphicLatticeFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle013
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle650
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle633
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle012
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Complex.Norm

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_real_independent_basis_lattice_family : ∀ (n g : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (b₀ : Fin n → ℂ), IsLatFam B K → b₀ ∈ B → ∃ (r : ℕ) (b : Fin r → Fin g → ℂ), IsLatBasis (K b₀) b := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.exists_isLatBasis_of_isLatFam | exact GlobalTheory.ShFam.Hor.LogCh.exists_isLatBasis_of_isLatFam | (intros; apply GlobalTheory.ShFam.Hor.LogCh.exists_isLatBasis_of_isLatFam <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exponentialKernels_isHolomorphicLatticeFamily : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (m g : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (ex : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ t.G)), IsOpen B → IsHolTo (B ×ˢ Set.univ) (fun q : (Fin m → ℂ) × (Fin g → ℂ) => (ex q.1 q.2).left) → (∀ b ∈ B, IsExpAt t (y b) (ex b)) → IsLatFam B (fun b => {w | ex b w = 1}) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.isLatFam_ker | exact GlobalTheory.ShFam.Hor.LogCh.isLatFam_ker | (intros; apply GlobalTheory.ShFam.Hor.LogCh.isLatFam_ker <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

noncomputable section

namespace GlobalTheory.FarTrait

section Algebra
open Polynomial

theorem exists_coefficientField (S : Type) [CommRing S] [IsLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    [CharZero (ResidueField S)] :
    ∃ Λ : Subring S, IsField Λ ∧ ∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S := by
  let T : Set (Subring S) := {Λ | ∀ x ∈ Λ, x ∈ maximalIdeal S → x = 0}
  have hbot : (⊥ : Subring S) ∈ T := by
    intro x hx hm
    obtain ⟨n, rfl⟩ := Subring.mem_bot.1 hx
    rw [← residue_eq_zero_iff, map_intCast, Int.cast_eq_zero] at hm
    simp [hm]
  obtain ⟨Λ, -, hΛ⟩ := zorn_le_nonempty₀ T (fun c hc hch y hy => by
    refine ⟨sSup c, fun x hx => ?_, fun z hz => le_sSup hz⟩
    obtain ⟨K, hK, hxK⟩ := (Subring.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).1 hx
    exact hc hK x hxK) ⊥ hbot
  have hT : ∀ x ∈ Λ, x ∈ maximalIdeal S → x = 0 := hΛ.prop
  have hF : IsField Λ := by
    refine ⟨exists_pair_ne _, mul_comm, fun {x} hx => ?_⟩
    have hu : IsUnit (x : S) := by
      by_contra h
      exact hx (Subtype.ext (hT _ x.2 h))
    let Λ' : Subring S :=
      { carrier := {s | ∃ n : ℕ, (x : S) ^ n * s ∈ Λ}
        one_mem' := ⟨0, by simp⟩
        zero_mem' := ⟨0, by simp⟩
        mul_mem' := by
          rintro a b ⟨n, hn⟩ ⟨m, hm⟩
          exact ⟨n + m, by convert Λ.mul_mem hn hm using 1; ring⟩
        add_mem' := by
          rintro a b ⟨n, hn⟩ ⟨m, hm⟩
          exact ⟨n + m, by
            convert Λ.add_mem (Λ.mul_mem (Λ.pow_mem x.2 m) hn) (Λ.mul_mem (Λ.pow_mem x.2 n) hm) using 1; ring⟩
        neg_mem' := by
          rintro a ⟨n, hn⟩
          exact ⟨n, by convert Λ.neg_mem hn using 1; ring⟩ }
    have h' : Λ' ∈ T := by
      rintro s ⟨n, hn⟩ hm
      exact (hu.pow n).mul_right_eq_zero.1 (hT _ hn (Ideal.mul_mem_left _ _ hm))
    have hle : Λ' ≤ Λ := hΛ.le_of_ge h' fun s hs => ⟨0, by simpa using hs⟩
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    exact ⟨⟨y, hle ⟨1, by rw [pow_one, hy]; exact Λ.one_mem⟩⟩, Subtype.ext hy⟩
  refine ⟨Λ, hF, fun s => ?_⟩
  letI := hF.toField
  have key : ∀ a : S, (∀ f : Λ[X], aeval a f ∈ maximalIdeal S → aeval a f = 0) → a ∈ Λ := fun a ha => by
    have h' : (aeval (R := Λ) a).toRingHom.range ∈ T := by
      rintro _ ⟨f, rfl⟩ hm
      exact ha f hm
    exact hΛ.le_of_ge h' (fun y hy => ⟨C ⟨y, hy⟩, by simp; rfl⟩) ⟨X, by simp⟩
  have hres : ∀ (a : S) (f : Λ[X]), residue S (aeval a f) = aeval (residue S a) f := fun a f =>
    (aeval_algHom_apply (IsScalarTower.toAlgHom Λ S (ResidueField S)) a f).symm
  by_cases hs : IsAlgebraic Λ (residue S s)
  · have hi := hs.isIntegral
    haveI : CharZero Λ := RingHom.charZero (algebraMap Λ (ResidueField S))
    have hsep : (minpoly Λ (residue S s)).Separable := (minpoly.irreducible hi).separable
    obtain ⟨a, ha, has⟩ := HenselianRing.is_henselian (I := maximalIdeal S)
      ((minpoly Λ (residue S s)).map (algebraMap Λ S)) ((minpoly.monic hi).map _) s
      (by rw [eval_map_algebraMap, ← residue_eq_zero_iff, hres, minpoly.aeval])
      (by
        rw [derivative_map, eval_map_algebraMap]
        have := hsep.aeval_derivative_ne_zero (minpoly.aeval Λ (residue S s))
        rw [← hres] at this
        exact (isUnit_iff_ne_zero (G₀ := ResidueField S)).2 this)
    have e : residue S a = residue S s := by rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact has
    refine ⟨a, key a fun f hf => ?_, by rw [← neg_sub]; exact neg_mem has⟩
    rw [← residue_eq_zero_iff, hres, e] at hf
    obtain ⟨q, rfl⟩ := minpoly.dvd _ _ hf
    rw [IsRoot.def, eval_map_algebraMap] at ha
    rw [map_mul, ha, zero_mul]
  · refine ⟨s, key s fun f hf => ?_, by simp⟩
    rw [← residue_eq_zero_iff, hres] at hf
    by_contra h
    exact hs ⟨f, by rintro rfl; simp at h, hf⟩

end Algebra


open MvPowerSeries GlobalTheory.CohenStructure in
theorem exists_finite_over_normal (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [CharZero S]
    [IsNoetherianRing S] [hc : IsAdicComplete (maximalIdeal S) S] :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (i : A →+* S),
      Function.Injective i ∧ i.Finite ∧ IsNoetherianRing A ∧ IsIntegrallyClosed A := by
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField S)
  rcases CharP.char_is_prime_or_zero (ResidueField S) p with h | rfl
  · obtain ⟨A, _, _, _, i, h1, h2, h3, h4, -⟩ := exists_finite_injective_of_isAdicComplete S p h
      (by rw [← residue_eq_zero_iff, map_natCast]; exact CharP.cast_eq_zero _ p) inferInstance hc
    exact ⟨A, inferInstance, inferInstance, i, h1, h2, h3, h4⟩
  haveI := CharP.charP_to_charZero (ResidueField S)
  by_cases hm : maximalIdeal S = ⊥
  · letI := (isField_iff_maximalIdeal_eq.2 hm).toField
    exact ⟨S, inferInstance, inferInstance, RingHom.id S, Function.injective_id, RingHom.Finite.id S, inferInstance,
      inferInstance⟩
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨Λ, hF, h1⟩ := exists_coefficientField S
  letI := hF.toField
  obtain ⟨n, x₀, hx₀, hd, N, hN⟩ := GlobalTheory.exists_systemOfParameters_insert S a ha0 ha
  let x : Fin (n + 1) → S := Fin.cons a x₀
  have hx : ∀ i, x i ∈ maximalIdeal S := fun i => Fin.cases ha hx₀ i
  let A := MvPowerSeries (Fin (n + 1)) Λ
  let φ : A →ₐ[Λ] S := mvEvalAdic Λ (maximalIdeal S) x hx
  letI : Algebra A S := φ.toRingHom.toAlgebra
  have : IsDomain A := isDomain_mvPowerSeries Λ (n + 1)
  have hb : maximalIdeal Λ = ⊥ := isField_iff_maximalIdeal_eq.1 hF
  have : IsAdicComplete (maximalIdeal Λ) Λ := by rw [hb]; infer_instance
  have hA := isAdicComplete_mvPowerSeries Λ (n + 1)
  have hle : (maximalIdeal A).map (algebraMap A S) ≤ maximalIdeal S := by
    refine Ideal.map_le_iff_le_comap.2 fun g hg => ?_
    have h4 := algHom_sub_constantCoeff_mem φ (K := maximalIdeal S)
      (fun j => by simpa [φ] using hx j) g
    have h5 := FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
    rw [hb, Ideal.mem_bot] at h5
    rwa [h5, map_zero, sub_zero] at h4
  have hge : maximalIdeal S ^ N ≤ (maximalIdeal A).map (algebraMap A S) := by
    refine hN.trans (Ideal.span_le.2 ?_)
    rw [← Fin.range_cons]
    rintro _ ⟨i, rfl⟩
    show x i ∈ _
    rw [← mvEvalAdic_X (A := Λ) (maximalIdeal S) x hx i]
    exact Ideal.mem_map_of_mem (algebraMap A S)
      (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp))
  have : IsHausdorff ((maximalIdeal A).map (algebraMap A S)) S :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)
  have : Module.Finite A (S ⧸ (maximalIdeal A).map (algebraMap A S)) := by
    refine finite_quotient_of_pow_le (fun s => ?_) hge
    obtain ⟨a, ha, h⟩ := h1 s
    refine ⟨C ⟨a, ha⟩, ?_⟩
    rwa [show algebraMap A S (C ⟨a, ha⟩) = a from mvEvalAdic_C _ x hx _]
  have hfin : Module.Finite A S := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)
  refine ⟨A, inferInstance, inferInstance, algebraMap A S,
    injective_of_ringKrullDim_eq (n := n + 1) ?_ (by rw [hd]; norm_cast), hfin, inferInstance,
    isIntegrallyClosed_mvPowerSeries Λ (n + 1)⟩
  rw [FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_isField hF,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]

theorem exists_factor {R W : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CharZero W] (g : R →+* W) :
    ∃ (N : Type) (_ : CommRing N) (_ : IsDomain N) (_ : IsLocalRing N) (φ : R →+* N) (g' : N →+* W),
      IsCN N ∧ IsLocalHom φ ∧ Function.Injective g' ∧ ∀ r, g' (φ r) = g r := by
  haveI := RingHom.ker_isPrime g
  let S := R ⧸ RingHom.ker g
  let k : S →+* W := RingHom.kerLift g
  have hk : Function.Injective k := RingHom.kerLift_injective g
  haveI : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) S
  haveI : IsAdicComplete (maximalIdeal S) S := CompleteFiniteExtension.isAdicComplete_of_finite_local R S
  haveI : CharZero S := RingHom.charZero k
  obtain ⟨A, _, _, i, hi, hfin, _, _⟩ := exists_finite_over_normal S
  letI : Algebra A S := i.toAlgebra
  have : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).2 hi
  have : Module.Finite A S := hfin
  let N := integralClosure S (FractionRing S)
  have hf : Module.Finite S N := finite_normalisation_of_finite_over_normal A S
  haveI : IsLocalRing N := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := S) _
  have j : Function.Injective ((algebraMap W (FractionRing W)).comp k) := (IsFractionRing.injective W _).comp hk
  let K : FractionRing S →+* FractionRing W := IsFractionRing.lift j
  have hK : ∀ s, K (algebraMap S _ s) = algebraMap W _ (k s) := IsFractionRing.lift_algebraMap j
  have hint : ∀ x : N, K x ∈ (algebraMap W (FractionRing W)).range := fun x =>
    IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.map_of_comp_eq k K (RingHom.ext fun s => (hK s).symm) x.2)
  let eW : W ≃+* (algebraMap W (FractionRing W)).range :=
    RingEquiv.ofBijective (algebraMap W (FractionRing W)).rangeRestrict
      ⟨fun a b h => IsFractionRing.injective W (FractionRing W) (congrArg Subtype.val h),
        RingHom.rangeRestrict_surjective _⟩
  let g' : N →+* W := eW.symm.toRingHom.comp ((K.comp N.val.toRingHom).codRestrict _ hint)
  have hg' : ∀ x : N, algebraMap W (FractionRing W) (g' x) = K x := fun x =>
    congrArg Subtype.val (eW.apply_symm_apply ⟨K x, hint x⟩)
  have hinj : Function.Injective g' := fun a b h =>
    Subtype.ext (K.injective ((hg' a).symm.trans ((congrArg _ h).trans (hg' b))))
  haveI : FaithfulSMul S N := (faithfulSMul_iff_algebraMap_injective S N).2 fun a b h =>
    IsFractionRing.injective S (FractionRing S) (congrArg Subtype.val h)
  haveI : IsLocalHom (Ideal.Quotient.mk (RingHom.ker g)) := IsLocalHom.of_surjective (S := S) _ Ideal.Quotient.mk_surjective
  refine ⟨N, inferInstance, inferInstance, inferInstance, (algebraMap S N).comp (Ideal.Quotient.mk _), g',
    ⟨IsNoetherianRing.of_finite S _, integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing S),
      CompleteFiniteExtension.isAdicComplete_of_finite_local S _, RingHom.charZero g'⟩, inferInstance, hinj, fun r => ?_⟩
  exact IsFractionRing.injective W (FractionRing W) ((hg' _).trans (hK _))



end GlobalTheory.FarTrait
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.GrCl GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod
open GlobalTheory.Twist (resM resM_resM)

namespace GlobalTheory.HodgeCech

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Dual

variable {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {g : ℕ}

theorem tanLin_bijective (c : VB.Chart (LieVB.omega t.G) g) (x : Sp S ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) :
    Function.Bijective (tanLin t h c.e) := by
  refine ⟨tanLin_injective t h c.e le_rfl h (c.isFrame.res le_rfl), fun a => ?_⟩
  obtain ⟨v, ⟨hv, e⟩, -⟩ := GlobalTheory.TanFibre.existsUnique_tanEv E H X t S x c.U h g c.e c.isFrame a
  exact ⟨tanOf hv, funext e⟩

def dualBasis (c : VB.Chart (LieVB.omega t.G) g) (x : Sp S ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) :
    Module.Basis (Fin g) S (TanM x t.G) :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ (tanLin_bijective t c x h))

theorem dualBasis_repr (c : VB.Chart (LieVB.omega t.G) g) (x : Sp S ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (v : TanM x t.G)
    (i : Fin g) : (dualBasis t c x h).repr v i = tanLin t h c.e v i := rfl

theorem ev_detUnit (c c' : VB.Chart (LieVB.omega t.G) g) (x : Sp S ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U)
    (hh : ⊤ ≤ x ⁻¹ᵁ (c.U ⊓ c'.U)) :
    ev x _ hh (c.isFrame.detUnit c'.isFrame inf_le_left inf_le_right).val =
      rdet ((dualBasis t c' x h').toMatrix (dualBasis t c x h)) := by
  show ev x _ hh ((c.isFrame.basis inf_le_left).det (c'.isFrame.basis inf_le_right)) = _
  rw [Module.Basis.det_apply, RingHom.map_det, rdet_self, ← Matrix.det_transpose]
  congr 1
  ext l i
  rw [Module.Basis.toMatrix_apply, dualBasis_repr, tanLin_apply, ← tanEv_resM t _ hh inf_le_right,
    sum_frMat c'.isFrame c.isFrame inf_le_right inf_le_left, tanEv_sum_smul]
  simp only [tanEv_resM t _ hh inf_le_left]
  have e : ∀ k, tanEv t (isTan_tv (dualBasis t c x h i)) h (c.e k) = if i = k then 1 else 0 := fun k => by
    rw [← tanLin_apply, ← dualBasis_repr, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [e, mul_ite, _root_.mul_one, MulZeroClass.mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

def detAff (t : SAB H X) (g : ℕ) : LB X :=
  ⟨{c : VB.Chart (LieVB.omega t.G) g // IsAffineOpen c.U}, fun c => c.1.U,
    fun c c' => c.1.isFrame.detUnit c'.1.isFrame inf_le_left inf_le_right⟩

theorem isLB_detAff (h : VB.IsVB (LieVB.omega t.G) g) : (detAff t g).IsLB := by
  refine ⟨top_le_iff.1 fun x _ => ?_, fun c => h.isLB_det.g_self c.1, fun c c' c'' => h.isLB_det.cocycle c.1 c'.1 c''.1⟩
  obtain ⟨U, e, hx, he⟩ := h x
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := U) (x := x) hx
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, _, he.res hVU⟩, hV⟩, hxV⟩

theorem lbIso_detAff (h : VB.IsVB (LieVB.omega t.G) g) : LBIso (detAff t g) (VB.det (LieVB.omega t.G) g) :=
  (VB.lbIso_det_of_frames (isLB_detAff t h) (fun c => c.1.e) (fun c => c.1.isFrame) fun _ _ => rfl).2

end Dual

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  (Y : Model Xo c β) {g : ℕ} {S : Type} [CommRing S]

theorem isAffineOpen_inf' {U V : Y.X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) := by
  have := projProper _ _ _ Y.proj
  have : Y.X.IsSeparated := ⟨by
    rw [← terminal.comp_from Y.s]
    infer_instance⟩
  exact hU.inf hV

variable {Y}

def pairDet (M : MChart Y) (a : (detAff Y.t g).ι) : Γ(Y.X, M.U ⊓ a.1.U)ˣ :=
  (isUnit_rdet_toMatrix (dualBasis Y.t a.1 (tau (isAffineOpen_inf' Y M.hU a.2)) (tau_le _ inf_le_right))
    (lieBasis M (tau (isAffineOpen_inf' Y M.hU a.2)) (tau_le _ inf_le_left))).unit

theorem ev_pairDet (M : MChart Y) (a : (detAff Y.t g).ι) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (h' : ⊤ ≤ x ⁻¹ᵁ a.1.U)
    (hh : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ a.1.U)) :
    ev x _ hh (pairDet M a).val = rdet ((dualBasis Y.t a.1 x h').toMatrix (lieBasis M x h)) := by
  have e : spMap (ev x _ hh) ≫ tau (isAffineOpen_inf' Y M.hU a.2) = x := spMap_ev x _ hh
  refine (map_rdet _ _).trans (congrArg rdet ?_)
  ext i j
  rw [Matrix.map_apply, Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply, dualBasis_repr, dualBasis_repr,
    ← tanPull_lieBasis M _ e (tau_le _ inf_le_left) h, tanLin_tanPull Y.t _ e (tau_le _ inf_le_right) h']
  rfl

variable (Y)

theorem lbIso_detAff_detOm : LBIso (detAff Y.t g) (detOm Y) := by
  refine ⟨⟨fun p => pairDet p.1 p.2⟩, fun p q => ?_⟩
  refine Eq.trans ?_ (mul_right_comm _ _ _)
  refine eq_mul_inv_of_mul_eq ?_
  refine Eq.trans ?_ (congrArg (· * _) (map_inv _ (detChg p.1 q.1)).symm)
  refine eq_inv_mul_of_mul_eq (Units.ext (ext_ev fun S _ z hz => ?_))
  have hp := le_preimage_mono inf_le_left hz
  have hq := le_preimage_mono inf_le_right hz
  have hp1 : ⊤ ≤ z ⁻¹ᵁ (p.1 : MChart Y).U := le_preimage_mono inf_le_left hp
  have hq1 : ⊤ ≤ z ⁻¹ᵁ (q.1 : MChart Y).U := le_preimage_mono inf_le_left hq
  have hp2 : ⊤ ≤ z ⁻¹ᵁ p.2.1.U := le_preimage_mono inf_le_right hp
  have hq2 : ⊤ ≤ z ⁻¹ᵁ q.2.1.U := le_preimage_mono inf_le_right hq
  refine (map_mul (ev z _ hz) _ _).trans ?_
  refine (congrArg₂ (· * ·) ((ev_res z _ hz (le_preimage_inf hp1 hq1) _).trans (ev_detChg _ _ z hp1 hq1 _))
    ((map_mul (ev z _ hz) _ _).trans (congrArg₂ (· * ·) ((ev_res z _ hz hp _).trans (ev_pairDet _ _ z hp1 hp2 hp))
      ((ev_res z _ hz (le_preimage_inf hp2 hq2) _).trans (ev_detUnit Y.t _ _ z hp2 hq2 _))))).trans
    (Eq.trans ?_ ((ev_res z _ hz hq _).trans (ev_pairDet _ _ z hq1 hq2 hq)).symm)
  rw [_root_.mul_comm, _root_.mul_comm (rdet _) (rdet _), rdet_toMatrix_mul, rdet_toMatrix_mul]

theorem lbIso_detOm_det (hO : (detOm Y).IsLB) (h : VB.IsVB (LieVB.omega Y.t.G) g) :
    LBIso (detOm Y) (VB.det (LieVB.omega Y.t.G) g) :=
  (lbIso_detAff_detOm Y).symm.trans hO (isLB_detAff Y.t h) h.isLB_det (lbIso_detAff Y.t h)

end GlobalTheory.HodgeCech
end
end

section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

theorem trace_le_of_aeval_monic_eq_zero :
    ∀ (p : Polynomial ℤ), p.Monic → ∀ n : ℕ, ∃ K : ℝ, ∀ M : Matrix (Fin n) (Fin n) ℤ,
      Polynomial.aeval M p = 0 → ((M.trace : ℤ) : ℝ) ≤ K := by
  intro p hp n
  set pC : Polynomial ℂ := p.map (Int.castRingHom ℂ) with hpC
  have hpC0 : pC ≠ 0 := (hp.map (Int.castRingHom ℂ)).ne_zero
  set B : ℝ := ∑ x ∈ pC.roots.toFinset, ‖x‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun x _ => norm_nonneg x
  refine ⟨n * B, fun M hM => ?_⟩
  set A : Matrix (Fin n) (Fin n) ℂ := M.map (Int.castRingHom ℂ) with hA
  have hAp : Polynomial.aeval A pC = 0 := by
    have e := Polynomial.aeval_algHom_apply ((Int.castRingHom ℂ).mapMatrix (m := Fin n)).toIntAlgHom M p
    rw [hM, map_zero] at e
    rw [hpC, show Int.castRingHom ℂ = algebraMap ℤ ℂ from rfl, Polynomial.aeval_map_algebraMap]
    exact e
  have htr : ((M.trace : ℤ) : ℂ) = A.trace := by
    simp [hA, Matrix.trace, Matrix.map_apply]
  have hroot : ∀ μ ∈ A.charpoly.roots, ‖μ‖ ≤ B := by
    intro μ hμ
    rcases isEmpty_or_nonempty (Fin n) with hn | hn
    · exfalso
      have hc := Polynomial.card_roots' A.charpoly
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_eq_zero] at hc
      have := Multiset.card_pos_iff_exists_mem.2 ⟨μ, hμ⟩
      omega
    have hsp : μ ∈ spectrum ℂ A :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.2 (Polynomial.isRoot_of_mem_roots hμ)
    have h1 := spectrum.subset_polynomial_aeval A pC ⟨μ, hsp, rfl⟩
    rw [hAp, spectrum.zero_eq, Set.mem_singleton_iff] at h1
    have hmem : μ ∈ pC.roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hpC0]; exact h1
    exact Finset.single_le_sum (f := fun x => ‖x‖) (fun x _ => norm_nonneg x) hmem
  have hsum : ‖A.trace‖ ≤ n * B := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    refine (norm_multiset_sum_le _).trans ?_
    refine (Multiset.sum_le_card_nsmul _ B (fun x hx => by obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.1 hx; exact hroot μ hμ)).trans ?_
    rw [Multiset.card_map, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hB0
    have := Polynomial.card_roots' A.charpoly
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
    exact_mod_cast this
  calc ((M.trace : ℤ) : ℝ) = (((M.trace : ℤ) : ℂ)).re := by simp
    _ ≤ ‖((M.trace : ℤ) : ℂ)‖ := Complex.re_le_norm _
    _ ≤ n * B := by rw [htr]; exact hsum

end GlobalTheory.RedTh
end
