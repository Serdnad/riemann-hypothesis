module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
public import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle020
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle212
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle213
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle118
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle019
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle208
import Formalism.LocalToGlobal.Columns.LevGCount
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle134
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle214
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle197
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle215
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.Hensel
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotDvdCardOfInjective
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ d : List ℤ, IsLab V P d ↔ d.length = V.rank ∧ d.Pairwise (fun a b => b ≤ a) ∧ (_root_.Formalism.DivisionValues.conjPl P = P → dualLab d = d) := by
  first | exact @GlobalTheory.LabChar.labels_char | exact GlobalTheory.LabChar.labels_char | (intros; apply GlobalTheory.LabChar.labels_char <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

open Formalism.BasicNotions NumberField Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG
open Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Act

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem substR_substR (R : Type) [CommRing R] (G G' : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R)
    (Q : XR P R) : substR P R G (substR P R G' Q) = substR P R (fun v s => G' v s * G v s) Q := by
  have hc : (substR P R G).comp (substR P R G') = substR P R (fun v s => G' v s * G v s) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨v, s, a, t⟩

    simp only [AlgHom.comp_apply, substR, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc, ← MvPolynomial.C_mul]
  exact congrArg (fun φ : XR P R →ₐ[R] XR P R => φ Q) hc

theorem natActR_natActR (R : Type) [Field R] (g g' : ∀ v, Fin (P.n' v) → GL (Fin (P.m + 1)) R) (Q : XR P R) :
    natActR P R g (natActR P R g' Q) = natActR P R (fun v s => g v s * g' v s) Q := by
  unfold natActR
  simp only [LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul, substR_substR]
  congr 1
  · rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Units.val_mul, Matrix.det_mul, mul_zpow, mul_comm]

theorem natActR_one (R : Type) [Field R] (Q : XR P R) : natActR P R (fun _ _ => 1) Q = Q := by
  have hs : substR P R (fun _ _ => 1) = AlgHom.id R (XR P R) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨v, s, a, t⟩
    simp only [substR, MvPolynomial.aeval_X, AlgHom.coe_id, id_eq, Matrix.one_apply]
    simp [ite_mul, Finset.sum_ite_eq]
  unfold natActR
  simp only [inv_one, Units.val_one, Matrix.det_one, one_zpow, Finset.prod_const_one, one_smul,
    LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  rw [hs]
  rfl

end Act

theorem invT_mul {k : Type} [Fintype k] [DecidableEq k] (A B : GL k ℂ) : invT (A * B) = invT A * invT B := by
  ext : 1
  simp only [invT, Units.val_mk, Units.val_mul, mul_inv_rev, Matrix.transpose_mul]

theorem invT_one {k : Type} [Fintype k] [DecidableEq k] : invT (1 : GL k ℂ) = 1 := by
  ext : 1
  simp [invT]

variable {p : ℕ} [Fact p.Prime]

theorem evC_crdB_actC (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ}
    (h : (X.Pj i).m + 1 = n) (Gr : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B M : GL (Fin n) D.host.E)
    (V : XR (X.Pj i) ℂ) (z : Frames Gr) (f : Fr1 D n)
    (hf : ∀ τ, f.1 τ = (atR D (M * B⁻¹) τ : Matrix (Fin n) (Fin n) ℂ) * z.1 τ) :
    evC (X.Pj i) h (posJ X D pos i) Gr (crdB (embT D) B) V z = ev1 X D pos i h (actC X D pos i h M V) f ∧
      actC X D pos i h M (actC X D pos i h M⁻¹ V) = V := by
  have hcr : ∀ τ, crdB (embT D) B τ = (atR D B⁻¹ τ : Matrix (Fin n) (Fin n) ℂ) := fun τ => rfl
  let y : Fr1 D n := ⟨fun τ => crdB (embT D) B τ * z.1 τ, fun τ => by
    rw [Matrix.det_mul, hcr]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (atR D B⁻¹ τ).isUnit).mul (z.2 τ)⟩
  refine ⟨?_, ?_⟩
  · have hz : ∀ v s, zAt (X.Pj i) h (posJ X D pos i) (crdB (embT D) B) z.1 v s =
        zAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) y.1 v s := by
      intro v s
      simp only [zAt, y, one_mul]
    have h1 : evC (X.Pj i) h (posJ X D pos i) Gr (crdB (embT D) B) V z = ev1 X D pos i h V y := by
      show (∏ v, ∏ s : Fin ((X.Pj i).n' v), (_ : ℂ)) * (_ : ℂ) = (∏ v, ∏ s : Fin ((X.Pj i).n' v), (_ : ℂ)) * (_ : ℂ)
      simp only [hz]
    have hy : IsTr (fun τ => (atR D M τ : Matrix (Fin n) (Fin n) ℂ)) y f := by
      intro τ
      rw [hf τ]
      show _ = (atR D M τ : Matrix (Fin n) (Fin n) ℂ) * (crdB (embT D) B τ * z.1 τ)
      rw [hcr, ← Matrix.mul_assoc, ← Units.val_mul]
      unfold atR
      rw [map_mul]
    have h2 := evC_natAct (X.Pj i) h (posJ X D pos i) (fun _ => 1) (fun _ => 1) (atR D M) y f hy V
    rw [h1]
    exact h2.symm
  · unfold actC
    rw [natActR_natActR]
    have he : (fun v s => hAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) (atR D M) v s *
        hAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) (atR D M⁻¹) v s) = fun _ _ => 1 := by
      funext v s
      have hm : ∀ τ, ((1 : GL (Fin n) ℂ) * atR D M τ * (1 : GL (Fin n) ℂ)⁻¹) * ((1 : GL (Fin n) ℂ) * atR D M⁻¹ τ * (1 : GL (Fin n) ℂ)⁻¹) = (1 : GL (Fin n) ℂ) := by
        intro τ
        simp only [one_mul, inv_one, mul_one, atR, ← map_mul, mul_inv_cancel, map_one]
      unfold hAt
      split_ifs
      · rw [← map_mul, hm, map_one]
      · rw [← invT_mul, ← map_mul, hm, map_one, invT_one]
    rw [he, natActR_one]

end GlobalTheory.TwV.DelA

end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace GlobalTheory.DenseUsable

theorem isSquare_neg_padic (q : ℕ) [hq : Fact q.Prime] (d : ℕ) (a : ℤ)
    (h1 : (q : ℤ) ∣ a ^ 2 + d) (h2 : ¬ (q : ℤ) ∣ 2 * a) : IsSquare (-(d : ℚ_[q])) := by
  let F : Polynomial ℤ := Polynomial.X ^ 2 + Polynomial.C (d : ℤ)
  have hF : ∀ z : ℤ_[q], Polynomial.aeval z F = z ^ 2 + d := by intro z; simp [F]
  have hF' : ∀ z : ℤ_[q], Polynomial.aeval z (Polynomial.derivative F) = 2 * z := by
    intro z; simp [F]; left; exact map_ofNat _ 2
  have hlt : ‖((a ^ 2 + d : ℤ) : ℤ_[q])‖ < 1 := (PadicInt.norm_int_lt_one_iff_dvd _).2 h1
  have hn : ‖((2 * a : ℤ) : ℤ_[q])‖ = 1 :=
    le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => h2 ((PadicInt.norm_int_lt_one_iff_dvd _).1 h))
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := (a : ℤ_[q])) (by
    rw [hF, hF']; push_cast at hn hlt; rw [hn]; simpa using hlt)
  rw [hF] at hz
  refine ⟨(z : ℚ_[q]), ?_⟩
  have : ((z ^ 2 + d : ℤ_[q]) : ℚ_[q]) = 0 := by rw [hz]; simp
  push_cast at this
  linear_combination -this

theorem intCast_mem_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (hp : (Ideal.absNorm w.asIdeal).Prime) (n : ℤ) :
    ((n : 𝓞 E) ∈ w.asIdeal ↔ ((Ideal.absNorm w.asIdeal : ℕ) : ℤ) ∣ n) := by
  set p := Ideal.absNorm w.asIdeal
  letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  have hc : Fintype.card (𝓞 E ⧸ w.asIdeal) = p := by
    rw [← Nat.card_eq_fintype_card]
    show _ = Ideal.absNorm w.asIdeal
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  let e : ZMod p ≃+* (𝓞 E ⧸ w.asIdeal) := ZMod.ringEquivOfPrime _ hp hc
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← ZMod.intCast_zmod_eq_zero_iff_dvd, map_intCast, ← map_intCast e,
    map_eq_zero_iff _ e.injective]

end GlobalTheory.DenseUsable

namespace GlobalTheory.DenseUsable

theorem exists_int_sub_mem {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (hp : (Ideal.absNorm w.asIdeal).Prime) (y : 𝓞 E) : ∃ a : ℤ, y - (a : 𝓞 E) ∈ w.asIdeal := by
  set p := Ideal.absNorm w.asIdeal
  letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  have hc : Fintype.card (𝓞 E ⧸ w.asIdeal) = p := by
    rw [← Nat.card_eq_fintype_card]
    show _ = Ideal.absNorm w.asIdeal
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  let e : ZMod p ≃+* (𝓞 E ⧸ w.asIdeal) := ZMod.ringEquivOfPrime _ hp hc
  obtain ⟨c, hc'⟩ := e.surjective (Ideal.Quotient.mk w.asIdeal y)
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective c
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hc', map_intCast, map_intCast, sub_self]

theorem usPl_of_absNorm_prime {E : Type} [Field E] [NumberField E] [IsCMField E] {d : ℕ} (hd : ImQ E d)
    (w : HeightOneSpectrum (𝓞 E)) (hp : (Ideal.absNorm w.asIdeal).Prime)
    (he : w.asIdeal.ramificationIdx ℤ = 1) (h2d : ((2 * d : ℕ) : 𝓞 E) ∉ w.asIdeal) : UsPl d w := by
  have hf := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 w).1 hp
  refine ⟨GlobalTheory.DenseInvFrob.isSplitAt_of_inertiaDeg_eq_one w hf he, fun q hq hqw => ?_⟩
  have hqw' : ((q : ℤ) : 𝓞 E) ∈ w.asIdeal := by rwa [Int.cast_natCast]
  have hpq : Ideal.absNorm w.asIdeal = q := by
    have := (intCast_mem_iff w hp q).1 hqw'
    exact (Nat.prime_dvd_prime_iff_eq hp hq).1 (Int.natCast_dvd_natCast.1 this)
  obtain ⟨-, x, hx⟩ := hd
  have hi : IsIntegral ℤ x := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hx]
    have : -(d : E) = algebraMap ℤ E (-(d : ℤ)) := by simp
    rw [this]; exact isIntegral_algebraMap
  let y : 𝓞 E := ⟨x, hi⟩
  have hy : y ^ 2 = -(d : 𝓞 E) := by
    apply RingOfIntegers.ext
    push_cast
    exact hx
  obtain ⟨a, ha⟩ := exists_int_sub_mem w hp y
  have h1 : ((q : ℤ) : ℤ) ∣ a ^ 2 + d := by
    rw [← hpq]
    refine (intCast_mem_iff w hp _).1 ?_
    have : (((a ^ 2 + d : ℤ)) : 𝓞 E) = (y - a) * (-(y + a)) + (y ^ 2 + d) := by push_cast; ring
    rw [this, hy, neg_add_cancel, add_zero]
    exact w.asIdeal.mul_mem_right _ ha
  have hnd : ¬ (q : ℤ) ∣ 2 * d := by
    intro h
    apply h2d
    have := (intCast_mem_iff w hp (2 * d)).2 (by rw [hpq]; exact h)
    simpa using this
  have hqz : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  haveI : Fact q.Prime := ⟨hq⟩
  refine isSquare_neg_padic q d a h1 fun h => ?_
  rcases hqz.dvd_or_dvd h with h' | h'
  · exact hnd (dvd_mul_of_dvd_left h' _)
  · apply hnd
    refine dvd_mul_of_dvd_right ?_ _
    have h3 : (q : ℤ) ∣ a ^ 2 := dvd_pow h' two_ne_zero
    have := (Int.dvd_add_right h3).1 h1
    exact this

end GlobalTheory.DenseUsable

namespace GlobalTheory.DenseUsable

theorem natCast_mem_of_dvd {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {n M : ℕ}
    (h : n ∣ M) (hn : (n : 𝓞 E) ∈ w.asIdeal) : (M : 𝓞 E) ∈ w.asIdeal := by
  obtain ⟨k, rfl⟩ := h
  push_cast
  exact w.asIdeal.mul_mem_right _ hn

theorem absNorm_mem_of_under_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (w u : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E))) :
    ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ∈ w.asIdeal := by
  have hu : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ∈ u.asIdeal := Ideal.absNorm_mem u.asIdeal
  have h' := congrArg HeightOneSpectrum.asIdeal h
  simp only [HeightOneSpectrum.under_asIdeal] at h'
  have hm : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal.under (𝓞 (maximalRealSubfield E)) := by
    rw [Ideal.under, Ideal.mem_comap, map_natCast]; exact hu
  rw [← h', Ideal.under, Ideal.mem_comap, map_natCast] at hm
  exact hm

end GlobalTheory.DenseUsable
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.RegAlgCharAlg

theorem expo_mul' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ χ' : HChar E) (τ : E →+* ℂ) :
    expo (χ * χ') τ = expo χ τ + expo χ' τ := by
  have h := (CG.hasInfChar_ofChar χ τ).twist χ'
  rw [CG.twist_ofChar, Multiset.map_singleton] at h
  have := h.infChar_eq
  rw [CG.infChar_ofChar] at this
  simpa using this

theorem expo_inv' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E) (τ : E →+* ℂ) :
    expo χ⁻¹ τ = -expo χ τ := by
  have := expo_mul' χ χ⁻¹ τ
  rw [mul_inv_cancel, CG.expo_one] at this
  linear_combination -this

theorem isAlgPos_of_polarizedPair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → PolarizedPair π χ →
      ∃ n : (maximalRealSubfield E →+* ℂ) → ℤ, IsAlgPos χ n := by
  intro E _ _ _ a ha π χ hreg hpol
  refine GlobalTheory.T.heckeChar_realSubfield_algebraic_of_comp_norm_integral E χ fun τ => ?_
  have hcomm : ∀ (τ : E →+* ℂ) (u : ℂ) (o : Op E a), Commute (cap (a := a) τ u) (act o) := fun τ u o => by
    cases o with
    | fin k => exact commute_cap_finRep τ u k
    | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
    | lie X => exact commute_cap_lie τ u X
  have hm : ∀ σ, π.HasInfChar σ ((CG.mk π).infChar σ) := fun σ =>
    GlobalTheory.CuspRep.hasInfChar_infChar_of_commute E a hcomm (CG.mk π) σ
  set ψ := GlobalTheory.GalOfCusp.compNorm E χ
  have h1 := (hm τ).twist ψ⁻¹
  have key := GlobalTheory.T.infChar_conjEmbedding_neg_of_invariant_pairing E a (π.twist ψ⁻¹) π hpol.dual τ _ _ h1 (hm (NumberField.ComplexEmbedding.conjugate τ))
  obtain ⟨z, hz⟩ : ∃ z, z ∈ (CG.mk π).infChar τ :=
    Multiset.card_pos_iff_exists_mem.1 (by rw [(hm τ).1]; omega)
  obtain ⟨n, hn⟩ := (hreg τ).2 z hz
  have hz' : -(z + expo ψ⁻¹ τ) ∈ (CG.mk π).infChar (NumberField.ComplexEmbedding.conjugate τ) := by
    rw [key, Multiset.map_map]
    exact Multiset.mem_map.2 ⟨z, hz, rfl⟩
  obtain ⟨n', hn'⟩ := (hreg _).2 _ hz'
  refine ⟨n + n' + ((a : ℤ) - 1), ?_⟩
  rw [expo_inv'] at hn'
  push_cast
  linear_combination hn' + hn

end GlobalTheory.RegAlgCharAlg
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem _root_.GlobalTheory.T.exists_letterCoordinates_series_onePlace_alt : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (n' : ℕ) [NeZero n'], Even n' → ∀ (B : OmBasis p n') (be : MvPowerSeries (Fin 2) (FormalGroupSystem.K0 p)), BeProp p be → ∃ bv : MvPowerSeries (ZMod n') ℂ_[p], product_zeroth_first_parts.B1 p n' bv ∧ product_zeroth_first_parts.B2 p n' bv ∧ product_zeroth_first_parts.B3 p n' bv ∧ product_zeroth_first_parts.B4 p n' bv ∧ ∀ (r0 r1 : ℕ) (U : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)), IntS p (inParam p U) → ∃ U' : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p], (∀ m, ‖MvPowerSeries.coeff m U'‖ ≤ 1) ∧ MvPowerSeries.subst (fun v : ZMod n' × Fin r0 × Fin r1 => MvPowerSeries.C (1 : ℂ_[p]) * jetLogG p n' v) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne B be U))) = U' * MvPowerSeries.subst (jetLogG p n' (β := Fin r0 × Fin r1)) (product_zeroth_first_parts.expS ℂ_[p] ((-1 : ℂ_[p]) • ∑ a : Fin r0, ∑ b : Fin r1, MvPowerSeries.subst (fun s : ZMod n' => (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) := by
  first | exact @GlobalTheory.OnePlace.exists_letterCoordinates_series_onePlace | exact GlobalTheory.OnePlace.exists_letterCoordinates_series_onePlace | (intros; apply GlobalTheory.OnePlace.exists_letterCoordinates_series_onePlace <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_conjugateModel_extremal_dual_parameter : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, s ≠ 0 → GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∃ v ∈ Submodule.span ℂ (Set.range fun g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s),
      ∃ u ∈ Submodule.span ℂ {v : M | ∃ y : Matrix (Fin n') (Fin n) L, GlobalTheory.Hk3.HoweDuality.latIdx y < GlobalTheory.Hk3.HoweDuality.latIdx x ∧ v = ρ y s},
        v - u ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} ∧ v - u ≠ 0 := by
  first | exact @GlobalTheory.Hk3.HoweG.gramClass_orbit_mod_lower | exact GlobalTheory.Hk3.HoweG.gramClass_orbit_mod_lower | (intros; apply GlobalTheory.Hk3.HoweG.gramClass_orbit_mod_lower <;> assumption)
end

section

open GlobalTheory.ColPeriod

namespace GlobalTheory.ColPeriod

theorem heckeUnit : GlobalTheory.ColPeriod.HeckeUnit :=
  fun _ _ _ _ _ _ _ _ hX hPr hμ _ _ _ _ hw hP x _ hk => GlobalTheory.CharVal.mu_unit hX hPr hμ x hk hP hw

end GlobalTheory.ColPeriod
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.FrameB.evenFrameBlock_scaling_homogeneous_polynomial : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (fd : FData X D) (c : Kc) (j : ℕ) (La' : X.Lt (j + 1)) (d : D.what₂.Tau → ℤ) (R : XspC (X.Pj (j + 1)) Kc), (∀ m ∈ R.support, ∀ τ, ¬ IsOddPos (pos.symm τ).2 → (∑ x : Var (X.Pj (j + 1)), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v)) = (posJ X D pos (j + 1)).symm τ then (m x : ℤ) else 0) = d τ) → GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') R = (∏ τ, if IsOddPos (pos.symm τ).2 then 1 else c ^ d τ) • GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.mk Kc fd j La') R := by
  intro p _ X D pos Kc _ _ _ fd c j La' d R hR
  classical
  let blk : Var (X.Pj (j + 1)) → Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v) := fun y => ⟨y.1, y.2.1⟩
  let E : (Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v)) → Kc := fun b => if IsOddPos b.2 then 1 else c
  have hf : ∀ y, GlobalTheory.FrameB.frF X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') y =
      MvPolynomial.C (E (blk y)) * GlobalTheory.FrameB.frF X Kc j (GlobalTheory.FrameB.mk Kc fd j La') y := by
    intro y
    unfold GlobalTheory.FrameB.frF GlobalTheory.FrameB.wV
    simp only [E, blk]
    split_ifs with h1 h2 h2
    · simp only [MvPolynomial.C_1, one_mul]
    · exact absurd h1 h2
    · exact absurd h2 h1
    · simp only [Matrix.smul_apply, smul_eq_mul, MvPolynomial.C_mul, Finset.mul_sum, mul_assoc]
  have hm : ∀ m ∈ R.support, (∏ y, E (blk y) ^ m y) = ∏ τ, if IsOddPos (pos.symm τ).2 then 1 else c ^ d τ := by
    intro m hmR
    rw [← Finset.prod_fiberwise Finset.univ blk, ← (posJ X D pos (j + 1)).prod_comp]
    refine Finset.prod_congr rfl fun b _ => ?_
    have hpb : pos.symm (posJ X D pos (j + 1) b) = b := pos.symm_apply_apply b
    have h2 : ∏ y ∈ Finset.univ.filter (fun y => blk y = b), E (blk y) ^ m y =
        E b ^ (∑ y ∈ Finset.univ.filter (fun y => blk y = b), m y) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun y hy => ?_
      rw [(Finset.mem_filter.1 hy).2]
    rw [h2, hpb]
    simp only [E]
    split_ifs with h1 h3 h3
    · exact one_pow _
    · exact absurd h1 h3
    · exact absurd h3 h1
    · have hd := hR m hmR (posJ X D pos (j + 1) b) (by rw [hpb]; exact h1)
      rw [Equiv.symm_apply_apply, ← Finset.sum_filter] at hd
      rw [← hd, ← Nat.cast_sum, zpow_natCast]
  unfold GlobalTheory.FrameB.tau0
  conv_lhs => rw [R.as_sum]
  conv_rhs => rw [R.as_sum]

  simp only [map_sum, Finset.smul_sum, MvPolynomial.aeval_monomial]
  refine Finset.sum_congr rfl fun m hmR => ?_
  rw [← hm m hmR]
  simp only [hf]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  ring
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.definiteUnitaryLocalComponent_splitPlace_homeomorph : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → Function.Bijective ((cLoc w).comp (locU a w).subtype) ∧ IsOpenMap ((cLoc w).comp (locU a w).subtype) ∧ Continuous ((cLoc w).comp (locU a w).subtype) := by
  first | (exact @GlobalTheory.Cong.cLoc_locU_bijective_open_continuous) | (exact GlobalTheory.Cong.cLoc_locU_bijective_open_continuous) | (intros; apply GlobalTheory.Cong.cLoc_locU_bijective_open_continuous  <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published


theorem _root_.GlobalTheory.T.isSpherical_twist_of_contragredient_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (ψ : HChar E), GlobalTheory.ContraPair.DualIsConjBy π ψ → ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → (∃ B, (CG.mk π).HasSat w B) → GlobalTheory.LGrp.IsSpherical ((π.twist ψ⁻¹).locRep w) (GlobalTheory.LFun.KGL w (n := a)) := by
  first | exact @GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy | exact GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy | (intros; apply GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy <;> assumption)
end
