module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle055
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle066
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle018
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle079
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionAutomorphySourceGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2016
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdRead.CharMul

variable {D : D7}

theorem det_int {n : ℕ} {N : Matrix (Fin n) (Fin n) (EAf D)} (h : IsIntM N) :
    N.det ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [Matrix.det_apply]
  refine Subring.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact Subring.zsmul_mem _ (Subring.prod_mem _ fun i _ => h (σ i) i) _

theorem ring_mul {R : Type} [CommRing R] {ε : R} (h : ε * ε = ε) (a b : R) :
    (1 - ε + ε * a) * (1 - ε + ε * b) = 1 - ε + ε * (a * b) := by
  linear_combination (1 - a - b + a * b) * h

theorem det_mul' {R : Type} [CommRing R] {k : ℕ} (A B : Matrix (Fin k) (Fin k) R) :
    (HMul.hMul A B).det = A.det * B.det :=
  Matrix.det_mul A B

theorem det_gl {R : Type} [CommRing R] {k : ℕ} (β : GL (Fin k) R) : β.val.det * (β⁻¹).val.det = 1 := by
  rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

theorem isUnitDet_mul {e : AE D} (he : e * e = e) {k : ℕ} {A B C : Matrix (Fin k) (Fin k) (EAf D)}
    (h : C.det = A.det * B.det) {x y : (AE D)ˣ} (hx : IsUnitDet e A x) (hy : IsUnitDet e B y) :
    IsUnitDet e C (x * y) := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, map_mul, hx1, hy1, one_mul]
  · rw [Units.val_mul, map_mul, hx2, hy2, h]
    exact ring_mul (by rw [← map_mul, he]) _ _
  · rw [mul_inv_rev, Units.val_mul, map_mul]
    exact Subring.mul_mem _ hy3 hx3

private lemma eq_lr_take_drop_of_map_fst_eq_replicate {D : D7} : ∃ Ψ : AE D ≃+* (TensorProduct D.host.F D.host.E (Ainf D.host.F)) × EAf D,
    ∀ z, infPart D z = Algebra.TensorProduct.comm D.host.F D.host.E (Ainf D.host.F) (Ψ z).1 ∧
      toEAf D z = (Ψ z).2 := by
  refine ⟨((Algebra.TensorProduct.comm D.host.F (AF D.host.F) D.host.E).trans
    (Algebra.TensorProduct.prodRight D.host.F D.host.F D.host.E (Ainf D.host.F) (Af D.host.F))).toRingEquiv,
    fun z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => exact ⟨rfl, rfl⟩
  | add z z' h1 h2 =>
    constructor
    · simp only [map_add (f := _), Prod.fst_add, h1.1, h2.1]
    · simp only [map_add (f := _), Prod.snd_add, h1.2, h2.2]

private lemma units_eq_of_res_eq_of_le_iSup {D : D7} {z z' : AE D} (hi : infPart D z = infPart D z') (ht : toEAf D z = toEAf D z') :
    z = z' := by
  obtain ⟨Ψ, hΨ⟩ := eq_lr_take_drop_of_map_fst_eq_replicate (D := D)
  apply Ψ.injective
  refine Prod.ext ((Algebra.TensorProduct.comm D.host.F D.host.E (Ainf D.host.F)).injective ?_) ?_
  · rw [← (hΨ z).1, ← (hΨ z').1, hi]
  · rw [← (hΨ z).2, ← (hΨ z').2, ht]

private lemma exists_unit_infPart_one_toEAf_eq {D : D7} {u w : EAf D} (huw : u * w = 1) :
    ∃ x : (AE D)ˣ, infPart D (x : AE D) = 1 ∧ toEAf D (x : AE D) = u ∧ toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = w := by
  obtain ⟨Ψ, hΨ⟩ := eq_lr_take_drop_of_map_fst_eq_replicate (D := D)
  have hwu : w * u = 1 := by rw [mul_comm, huw]
  refine ⟨⟨Ψ.symm (1, u), Ψ.symm (1, w), ?_, ?_⟩, ?_, ?_, ?_⟩
  · apply Ψ.injective
    simp [huw]
  · apply Ψ.injective
    simp [hwu]
  · show infPart D (Ψ.symm (1, u)) = 1
    rw [(hΨ _).1, RingEquiv.apply_symm_apply, map_one]
  · show toEAf D (Ψ.symm (1, u)) = u
    rw [(hΨ _).2, RingEquiv.apply_symm_apply]
  · show toEAf D (Ψ.symm (1, w)) = w
    rw [(hΨ _).2, RingEquiv.apply_symm_apply]

theorem exists_isUnitDet {e : AE D} (he : e * e = e) (hE : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) {k : ℕ}
    {A : Matrix (Fin k) (Fin k) (EAf D)} {v : EAf D} (hv : v ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h : A.det * v = 1) : ∃ x, IsUnitDet e A x := by
  have hε : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, he]
  obtain ⟨x, hx1, hx2, hx3⟩ := exists_unit_infPart_one_toEAf_eq (u := 1 - toEAf D e + toEAf D e * A.det)
    (w := 1 - toEAf D e + toEAf D e * v) (by rw [ring_mul hε, h, mul_one, sub_add_cancel])
  refine ⟨x, hx1, hx2, ?_⟩
  rw [hx3]
  exact Subring.add_mem _ (Subring.sub_mem _ (Subring.one_mem _) hE) (Subring.mul_mem _ hE hv)

private lemma isUnitDet_unique' {D : D7} {e : AE D} {k : ℕ} {M : Matrix (Fin k) (Fin k) (EAf D)} {x x' : (AE D)ˣ}
    (hx : IsUnitDet e M x) (hx' : IsUnitDet e M x') : x = x' :=
  Units.ext (units_eq_of_res_eq_of_le_iSup (hx.1.trans hx'.1.symm) (hx.2.1.trans hx'.2.1.symm))

private lemma unitChar_eq_inv_of_isUnitDet {D : D7} (ν : (AE D)ˣ →* Circle) {e : AE D} {k : ℕ} {M : Matrix (Fin k) (Fin k) (EAf D)}
    {x : (AE D)ˣ} (hx : IsUnitDet e M x) : unitChar ν e M = (((ν x)⁻¹ : Circle) : ℂ) := by
  have hex : ∃ x, IsUnitDet e M x := ⟨x, hx⟩
  unfold unitChar
  rw [dite_eq_left hex, isUnitDet_unique' hex.choose_spec hx]

theorem unitChar_mul : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (e : AE D), e * e = e → toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
  ∀ {k : ℕ} (N : Matrix (Fin k) (Fin k) (EAf D)) (β : GL (Fin k) (EAf D)), IsIntM β.val → IsIntM (β⁻¹).val →
  unitChar ν e (HMul.hMul N β.val) = unitChar ν e N * unitChar ν e β.val := by
  intro D ν e he hE k N β hβ hβ'
  obtain ⟨y, hy⟩ := exists_isUnitDet he hE (det_int hβ') (det_gl β)
  obtain ⟨y', hy'⟩ := exists_isUnitDet he hE (det_int hβ) (by rw [mul_comm]; exact det_gl β)
  by_cases hN : ∃ x, IsUnitDet e N x
  · obtain ⟨x, hx⟩ := hN
    rw [unitChar_eq_inv_of_isUnitDet ν (isUnitDet_mul he (det_mul' N β.val) hx hy), unitChar_eq_inv_of_isUnitDet ν hx, unitChar_eq_inv_of_isUnitDet ν hy,
      map_mul, mul_inv, Circle.coe_mul]
  · have hNβ : ¬ ∃ x, IsUnitDet e (HMul.hMul N β.val) x := by
      rintro ⟨z, hz⟩
      exact hN ⟨_, isUnitDet_mul he (by rw [det_mul', mul_assoc, det_gl, mul_one]) hz hy'⟩
    unfold unitChar
    rw [dite_eq_right hN, dite_eq_right hNβ, zero_mul]

end GlobalTheory.StdRead.CharMul

end
end

section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.StdReadFrame

theorem row_mul {R : Type} [CommRing R] {P Q : R → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hmul : ∀ x y, P x → Q y → P (x * y)) {b a : ℕ} {Y : Matrix (Fin b) (Fin a) R} {K : Matrix (Fin a) (Fin a) R}
    (hK : ∀ i j, Q (K i j)) {i : Fin b} (h : ∀ j, P (Y i j)) (j : Fin a) : P ((Y * K) i j) := by
  rw [Matrix.mul_apply]
  exact Finset.sum_induction _ P hadd h0 fun l _ => hmul _ _ (h l) (hK l j)

theorem row_mul_iff {R : Type} [CommRing R] {P Q : R → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hmul : ∀ x y, P x → Q y → P (x * y)) {b a : ℕ} (Y : Matrix (Fin b) (Fin a) R) {β : GL (Fin a) R}
    (hK : ∀ i j, Q (β.val i j)) (hK' : ∀ i j, Q ((β⁻¹).val i j)) (i : Fin b) :
    (∀ j, P ((Y * β.val) i j)) ↔ ∀ j, P (Y i j) := by
  refine ⟨fun h j => ?_, fun h j => row_mul h0 hadd hmul hK h j⟩
  have h1 := row_mul h0 hadd hmul hK' h j
  rwa [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h1

theorem topL_mul {R : Type} [CommRing R] {b a : ℕ} (Y : Matrix (Fin b) (Fin a) R) (K : Matrix (Fin a) (Fin a) R) :
    topL a (Y * K) = topL a Y * K := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases h : i.val < b
  · simp [topL, h, Matrix.mul_apply]
  · simp [topL, h]

theorem one_inv_mul {R : Type} [CommRing R] {b a : ℕ} (Y : Matrix (Fin b) (Fin a) R) :
    ((1 : GL (Fin b) R)⁻¹).val * Y = Y := by
  rw [inv_one, Units.val_one, Matrix.one_mul]

variable {D : D7}

theorem inId_zero (I : Ideal (𝓞 D.host.E)) : InId (D := D) I 0 := ⟨zero_mem _, Ideal.zero_mem _⟩

theorem inId_add {I : Ideal (𝓞 D.host.E)} (x y : EAf D) (hx : InId I x) (hy : InId I y) : InId I (x + y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  exact ⟨add_mem h1 h3, Ideal.add_mem _ h2 h4⟩

theorem inId_mul {I : Ideal (𝓞 D.host.E)} (x y : EAf D) (hx : InId I x)
    (hy : y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : InId I (x * y) := by
  obtain ⟨h1, h2⟩ := hx
  exact ⟨mul_mem h1 hy, Ideal.mul_mem_right (⟨y, hy⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) _ h2⟩

theorem frMapO_one (S T : HSp D) (β : GL (Fin S.rank) (EAf D)) (t : WO S T) :
    frMapO S T β 1 t = HMul.hMul (Matrix.of fun i j => toEAf D (t i j) : Matrix (Fin T.rank) (Fin S.rank) (EAf D)) β.val := by
  unfold frMapO
  rw [one_inv_mul]
  rfl

theorem stdFst_frame : ∀ {D : D7} (S T : HSp D) (ν : (AE D)ˣ →* Circle) (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)) (β : GL (Fin S.rank) (EAf D)),
  IsIntM β.val → IsIntM (β⁻¹).val → ∀ t : WO S T, stdFst ν e 𝔪 S T β 1 t =
    if IsHalf e t ∧ (∀ i j, toEAf D (t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
        ∀ i j, S.rank ≤ i.1 → InId 𝔪 (toEAf D (t i j)) then
      unitChar ν e (HMul.hMul (topL S.rank (Matrix.of fun i j => toEAf D (t i j))) β.val) else 0 := by
  intro D S T ν e 𝔪 β hβ hβ' t
  unfold stdFst
  rw [frMapO_one, topL_mul]
  refine if_congr (and_congr_right fun _ => and_congr ?_ ?_) rfl rfl
  · exact forall_congr' fun i => row_mul_iff (P := fun z => z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
      (Q := fun z => z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (zero_mem _) (fun _ _ => add_mem) (fun _ _ => mul_mem)
      (Matrix.of fun i j => toEAf D (t i j)) hβ hβ' i
  · refine forall_congr' fun i => ?_
    have h := row_mul_iff (P := InId (D := D) 𝔪) (Q := fun z => z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
      (inId_zero 𝔪) inId_add inId_mul (Matrix.of fun i j => toEAf D (t i j)) hβ hβ' i
    exact ⟨fun H j hi => h.1 (fun l => H l hi) j, fun H j hi => h.2 (fun l => H l hi) j⟩

end GlobalTheory.StdReadFrame
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem flat_surjective_spMap_ringOfIntegers (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') :
    Flat (spMap (RingOfIntegers.mapRingHom j)) ∧ Surjective (spMap (RingOfIntegers.mapRingHom j)) := by
  letI : Algebra (𝓞 K) (𝓞 K') := (RingOfIntegers.mapRingHom j).toAlgebra
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 K')) := by
    intro a b h
    apply RingOfIntegers.coe_injective
    apply j.injective
    exact congrArg ((↑) : 𝓞 K' → K') h
  haveI : FaithfulSMul (𝓞 K) (𝓞 K') := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : Module.Flat (𝓞 K) (𝓞 K') := inferInstance
  haveI : Algebra.IsIntegral (𝓞 K) (𝓞 K') := by
    constructor
    intro x
    exact IsIntegral.tower_top (R := ℤ) (Algebra.IsIntegral.isIntegral (R := ℤ) x)
  refine ⟨Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance), ⟨fun p => ?_⟩⟩
  let p' : PrimeSpectrum (𝓞 K) := p
  obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 K') p'.asIdeal (by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQp⟩

theorem eq_pow_of_baseChange_eq_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (A B : PAT H (Sp (𝓞 K))) (A' B' : PAT H (Sp (𝓞 K'))) (mA : SABMap A'.t A.t (spMap (RingOfIntegers.mapRingHom j)))
    (mB : SABMap B'.t B.t (spMap (RingOfIntegers.mapRingHom j))) (g : A.t.G ⟶ B.t.G) (f' : A'.t.G ⟶ B'.t.G) (n : ℕ),
    0 < n → Serre.IsLinearHom A.t.act B.t.act g → Serre.IsLinearHom A'.t.act B'.t.act f' →
    (f' ^ n).left ≫ mB.φ = mA.φ ≫ g.left →
    ∃ f : A.t.G ⟶ B.t.G, Serre.IsLinearHom A.t.act B.t.act f ∧ f ^ n = g ∧ f'.left ≫ mB.φ = mA.φ ≫ f.left := by
  intro E _ _ _ H K K' _ _ _ _ j A B A' B' mA mB g f' n hn hg hf' hfg
  have hpow : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (m : ℕ), IsMonHom (𝟙 G ^ m) := by
    intro S G _ _ m
    induction m with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))
    | succ m ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 G ^ m) (𝟙 G) ≫ μ[G]))
  have hffs : ∀ {R : Type} [CommRing R] (P : PAT H (Sp R)), IsFinite (𝟙 P.t.G ^ n).left ∧
      Flat (𝟙 P.t.G ^ n).left ∧ Surjective (𝟙 P.t.G ^ n).left := by
    intro R _ P
    exact (ChF.exists_gen_theta_tensor_and_finite_flat_surjective_pow R P.t.G P.t.PP.L
      (P.t.PP.L.pull (fst P.t.G P.t.G).left) P.ab P.t.PP.isLB P.ample (LB.isLB_pull P.t.PP.isLB _)).2 n hn
  have hepi : ∀ {S : Scheme.{0}} {X Y : Over S} (u : X ⟶ Y), Flat u.left → Surjective u.left → Epi u := by
    intro S X Y u h1 h2
    haveI : Epi ((Over.forget S).map u) := Flat.epi_of_flat_of_surjective u.left
    exact (Over.forget S).epi_of_epi_map this
  obtain ⟨hAfin, hAfl, hAsu⟩ := hffs A
  obtain ⟨-, hA'fl, hA'su⟩ := hffs A'
  have hq : QuasiCompact (𝟙 A.t.G ^ n).left := inferInstance
  obtain ⟨hflatj, hsurj⟩ := flat_surjective_spMap_ringOfIntegers K K' j
  have hker : ∀ (T : Over (Sp (𝓞 K))) (x : T ⟶ A.t.G), x ≫ (𝟙 A.t.G ^ n) = 1 → x ≫ g = 1 := by
    intro T x hx
    have hb : pullback.fst T.hom (spMap (RingOfIntegers.mapRingHom j)) ≫ T.hom =
        pullback.snd T.hom (spMap (RingOfIntegers.mapRingHom j)) ≫ spMap (RingOfIntegers.mapRingHom j) :=
      pullback.condition
    obtain ⟨eA, heA⟩ := exists_mulEquiv_of_isGrpPullback mA.cart _ _ hb
    obtain ⟨eB, heB⟩ := exists_mulEquiv_of_isGrpPullback mB.cart _ _ hb
    let prO : Over.mk (pullback.fst T.hom (spMap (RingOfIntegers.mapRingHom j)) ≫ T.hom) ⟶ T :=
      Over.homMk (pullback.fst T.hom (spMap (RingOfIntegers.mapRingHom j))) rfl
    have hE : Epi prO := by
      haveI := hflatj
      haveI := hsurj
      exact hepi prO (inferInstanceAs (Flat (pullback.fst _ _))) (inferInstanceAs (Surjective (pullback.fst _ _)))
    have hxn : x ^ n = 1 := by rw [← hx, MonObj.comp_pow, Category.comp_id]
    have hx' : eA.symm (prO ≫ x) ^ n = 1 := by
      apply eA.injective
      rw [map_pow, map_one, MulEquiv.apply_symm_apply, ← MonObj.comp_pow, hxn, MonObj.comp_one]
    have e2 : eA.symm (prO ≫ x) ≫ (f' ^ n) = 1 := by
      haveI := hf'.isMonHom
      rw [MonObj.comp_pow, ← MonObj.pow_comp, hx', MonObj.one_comp]
    have e1 : eB (eA.symm (prO ≫ x) ≫ (f' ^ n)) = prO ≫ x ≫ g := by
      apply Over.OverMorphism.ext
      rw [heB, Over.comp_left, Category.assoc, hfg, ← Category.assoc, ← heA, MulEquiv.apply_symm_apply]
      simp only [Over.comp_left, Category.assoc]
    have : prO ≫ (x ≫ g) = prO ≫ 1 := by rw [← e1, e2, map_one, MonObj.comp_one]
    exact (cancel_epi prO).1 this
  haveI := hg.isMonHom
  haveI := hpow A.t.G n
  obtain ⟨⟨ψ, hψ, hψg⟩, hEpiA⟩ := exists_monHom_factor_of_flat_surjective _ A.t.G A.t.G B.t.G (𝟙 A.t.G ^ n) g
    (hpow _ n) hg.isMonHom hAfl hAsu hq hker
  haveI := hψ
  have hψn : ψ ^ n = g := by rw [← hψg, MonObj.pow_comp, Category.id_comp]
  have hlin : Serre.IsLinearHom A.t.act B.t.act ψ := by
    refine ⟨hψ, fun c => ?_⟩
    haveI := A.t.act.hom c
    rw [← cancel_epi (𝟙 A.t.G ^ n)]
    have hc : (𝟙 A.t.G ^ n) ≫ A.t.act.act c = A.t.act.act c ≫ (𝟙 A.t.G ^ n) := by
      rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
    rw [reassoc_of% hc, hψg, reassoc_of% hψg]
    exact hg.comm c
  obtain ⟨w, hw, hwc⟩ := PairingFibre.exists_hom mA.cart mB.cart ψ
  haveI := hw
  haveI := hf'.isMonHom
  have hφ : mA.φ ≫ A.t.G.hom = A'.t.G.hom ≫ spMap (RingOfIntegers.mapRingHom j) := mA.cart.1.w
  have hpw : ∀ m : ℕ, (w ^ (m + 1)).left ≫ mB.φ = mA.φ ≫ (ψ ^ (m + 1)).left := by
    intro m
    induction m with
    | zero => rw [zero_add, pow_one, pow_one]; exact hwc
    | succ m ih =>
      rw [pow_succ w, pow_succ ψ]
      exact FamDesc.exists_mul hφ mB.cart ih hwc
  have hwn : w ^ n = f' ^ n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    apply Over.OverMorphism.ext
    apply mB.cart.1.hom_ext
    · rw [hpw m, hψn, hfg]
    · rw [Over.w, Over.w]
  have hwf : w = f' := by
    haveI := hepi (𝟙 A'.t.G ^ n) hA'fl hA'su
    rw [← cancel_epi (𝟙 A'.t.G ^ n), MonObj.pow_comp, MonObj.pow_comp, Category.id_comp, Category.id_comp, hwn]
  refine ⟨ψ, hlin, hψn, ?_⟩
  rw [← hwf]
  exact hwc

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualQuot

theorem exists_quotient_lam : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∃ (B : Over (Sp R)) (P : LB (A ⊗ B).left) (q : A ⟶ B) (hP : Fam A P), Good g B.hom ∧ FinAff B.left ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ (∀ (Y : Over (Sp R)) (a x : Y ⟶ A), evc hP.isLB a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL)) ∧ (∀ (Y : Over (Sp R)) (x y : Y ⟶ A), x ≫ q = y ≫ q ↔ GlobalTheory.MemKL A L (x * y⁻¹)) := by
  intro R _ _ A _ g hA hg L hL hamp
  obtain ⟨H, _, i, hi, hmono, hHf, hHfl, hrep⟩ := GlobalTheory.T.kernelOfLineBundle_finiteFlat_subgroupScheme R A hA L hL hamp
  obtain ⟨B, _, q, π, hB, hq, hqf, hqfl, hqs, hπ, hpb⟩ := GlobalTheory.T.exists_quotient_abelianScheme_finiteFlat_subgroup R A H i hA hi hmono hHf hHfl
  obtain ⟨P₀, hP₀, hform⟩ := GlobalTheory.T.exists_descent_mumfordBundle_quotient R A hA L hL H i hi hmono hHf hHfl hrep B q hB hq hqf hqfl hqs hpb
  have hc := hA.comm
  let c : A ⊗ B ⟶ A ⊗ B := snd A B ≫ lift (1 : B ⟶ A) (𝟙 B)
  let P : LB (A ⊗ B).left := tens P₀ (dual (P₀.pull c.left))
  have hP : P.IsLB := isLB_tens hP₀ (isLB_dual (pull_isLB hP₀ _))
  have hcls : cls P hP = cls P₀ hP₀ - GlobalTheory.CechPic.pull c.left (cls P₀ hP₀) := by
    rw [cls_tens hP₀ (isLB_dual (pull_isLB hP₀ _)), cls_dual (pull_isLB hP₀ _), cls_pull hP₀, sub_eq_add_neg]
  have hev : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ B), evc hP a t = evc hP₀ a t - evc hP₀ 1 t := by
    intro Y a t
    have e : lift a t ≫ c = lift (1 : Y ⟶ A) t := by
      simp only [c, lift_snd_assoc, comp_lift, MonObj.comp_one, Category.comp_id, lift_snd]
    simp only [evc]
    rw [hcls, map_sub, ← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, e]
  have hform' : ∀ (Y : Over (Sp R)) (a x : Y ⟶ A), evc hP a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL) := by
    intro Y a x
    rw [hev, hform, hform, _root_.one_mul]
    abel
  have h0l : Triv (ev P (1 : B ⟶ A) (𝟙 B)) := by
    rw [triv_ev_iff hP, hev, sub_self]
  have h0r : Triv (ev P (𝟙 A) (1 : A ⟶ B)) := by
    have e : (1 : A ⟶ B) = (1 : A ⟶ A) ≫ q := (MonObj.one_comp q).symm
    rw [triv_ev_iff hP, e, hform', _root_.mul_one]
    abel
  have hadd : IsAdditive P := GlobalTheory.CubeNoeth.isAdditive_of_triv_axes hA hB hP h0l h0r
  have hBsm := hB.smooth
  have hAfa := GlobalTheory.T.finiteSetsInAffineOpen_abelianScheme_relAmple R A hA L hL hamp
  refine ⟨B, P, q, ⟨hP, hadd⟩, ⟨hB.proper, GlobalTheory.T.smoothOfRelativeDimension_descends_finite_flat_surjective _ A B g q hg hBsm hqf hqfl hqs, hB.geomConnected⟩, ?_, hqf, hqfl, hqs, hform', ?_⟩
  · intro F
    classical
    obtain ⟨U, hU, hF⟩ := hAfa (F.image π.left)
    exact ⟨π.left ⁻¹ᵁ U, hU.preimage π.left, fun x hx ↦ hF _ (Finset.mem_image_of_mem _ hx)⟩
  · intro Y x y
    constructor
    · intro h
      refine (hrep Y (x * y⁻¹)).2 ⟨hpb.lift x y h ≫ fst H A, ?_⟩
      have h1 := hpb.lift_fst x y h
      rw [comp_mul, hpb.lift_snd] at h1
      rw [eq_mul_inv_iff_mul_eq, Category.assoc, h1]
    · intro h
      obtain ⟨z, hz⟩ := (hrep Y (x * y⁻¹)).1 h
      have hx : x = lift z y ≫ ((fst H A ≫ i) * snd H A) := by
        rw [comp_mul, lift_fst_assoc, lift_snd, hz, inv_mul_cancel_right]
      rw [hx, Category.assoc, hpb.w, lift_snd_assoc]

end GlobalTheory.DualQuot
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaDistribution_automorphy_source_group : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ η, IsEtaTilde D η → ∀ (of oi : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsFinWeil ψ S T ΛS ΛT (η ^ S.rank) (η ^ T.rank) of → IsInfWeil ψ θ S T oi → ∀ γ ∈ GQ S, ∀ f, IsThetaFunO ψ S T f → of (γ, 1) (oi (γ, 1) f) 0 = f 0 := by
  first | exact @GlobalTheory.DualSwap.automorphy_source | exact GlobalTheory.DualSwap.automorphy_source | (intros; apply GlobalTheory.DualSwap.automorphy_source <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.liftsAlong_smallExtension_of_dualNumber_lifting : ∀ (S : Scheme.{0}) [IsAffine S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : Over S) [Smooth U.hom] (M : LB (A ⊗ U).left), Fam A M → Inj A M → TanLift A M → SmallLift A M := by
  first | exact @GlobalTheory.DualOpen.smallLift_of_tanLift | exact GlobalTheory.DualOpen.smallLift_of_tanLift | (intros; apply GlobalTheory.DualOpen.smallLift_of_tanLift <;> assumption)
end
