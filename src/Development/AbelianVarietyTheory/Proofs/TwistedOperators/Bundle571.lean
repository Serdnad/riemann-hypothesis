module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle554
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle148
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle560
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1603
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle198
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIdentificationRespectsRealFinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle544
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle252
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle238
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle561
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle246
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Formalism.SatakeDualWeyl.StatementG
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameIdem

section General

variable {R : Type} [CommRing R] {n : ℕ}

theorem cut_mem (O : Subring R) {f f' : R} (hf : f ∈ O) (hf' : f' ∈ O) (A : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, f * A i j ∈ O) (h' : ∀ i j, f' * A i j ∈ O) (i j : Fin n) :
    ((f + f') • A + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R)) i j ∈ O := by
  have e : ((f + f') • A + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R)) i j =
      f * A i j + f' * A i j + (1 - (f + f')) * (1 : Matrix (Fin n) (Fin n) R) i j := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul]
  rw [e]
  refine O.add_mem (O.add_mem (h i j) (h' i j)) (O.mul_mem (O.sub_mem O.one_mem (O.add_mem hf hf')) ?_)
  rw [Matrix.one_apply]
  split_ifs
  · exact O.one_mem
  · exact O.zero_mem

theorem exists_cut (O : Subring R) {f f' : R} (hf : f ∈ O) (hf' : f' ∈ O) (hff : f * f = f) (hff' : f' * f' = f')
    (h0 : f * f' = 0) (A B : Matrix (Fin n) (Fin n) R) (hAB : A * B = 1) (hBA : B * A = 1)
    (hA : ∀ i j, f * A i j ∈ O) (hA' : ∀ i j, f' * A i j ∈ O)
    (hB : ∀ i j, f * B i j ∈ O) (hB' : ∀ i j, f' * B i j ∈ O) :
    ∃ Y : GL (Fin n) O, Y.1.map O.subtype = (f + f') • A + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R) ∧
      ∀ {k : Type} [CommRing k] (ρ : O →+* k), ρ ⟨f, hf⟩ = 1 →
        ∀ i j, ρ (Y.1 i j) = ρ ⟨f * A i j, hA i j⟩ := by
  have hφ : (f + f') * (f + f') = f + f' := by
    have h0' : f' * f = 0 := by rw [mul_comm, h0]
    simp only [add_mul, mul_add, hff, hff', h0, h0', add_zero, zero_add]
  let Ym : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, cut_mem O hf hf' A hA hA' i j⟩
  let Ym' : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, cut_mem O hf hf' B hB hB' i j⟩
  have hm : Ym.map O.subtype = (f + f') • A + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R) := rfl
  have hm' : Ym'.map O.subtype = (f + f') • B + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R) := rfl
  have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) O => M.map O.subtype) := by
    intro M N h
    ext i j
    exact congrFun (congrFun h i) j
  have e1 : Ym * Ym' = 1 := inj (by
    show (Ym * Ym').map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, hm, hm', GlobalTheory.CompStab.idem_mul _ hφ A B hAB, Matrix.map_one _ (map_zero _) (map_one _)])
  have e2 : Ym' * Ym = 1 := inj (by
    show (Ym' * Ym).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, hm, hm', GlobalTheory.CompStab.idem_mul _ hφ B A hBA, Matrix.map_one _ (map_zero _) (map_one _)])
  refine ⟨⟨Ym, Ym', e1, e2⟩, hm, ?_⟩
  intro k _ ρ hρ i j
  have hz : ρ ⟨f', hf'⟩ = 0 := by
    have : (⟨f, hf⟩ : O) * ⟨f', hf'⟩ = 0 := Subtype.ext h0
    have h2 := congrArg ρ this
    rwa [map_mul, hρ, one_mul, map_zero] at h2
  have hz' : ρ ⟨f' * A i j, hA' i j⟩ = 0 := by
    have : (⟨f, hf⟩ : O) * ⟨f' * A i j, hA' i j⟩ = 0 :=
      Subtype.ext (show f * (f' * A i j) = 0 by rw [← mul_assoc, h0, zero_mul])
    have h2 := congrArg ρ this
    rwa [map_mul, hρ, one_mul, map_zero] at h2
  have hd : ρ ((1 : Matrix (Fin n) (Fin n) O) i j) * 0 = 0 := mul_zero _
  have split : Ym i j = ⟨f * A i j, hA i j⟩ + ⟨f' * A i j, hA' i j⟩ +
      (1 - (⟨f, hf⟩ + ⟨f', hf'⟩)) * (1 : Matrix (Fin n) (Fin n) O) i j := by
    apply Subtype.ext
    show ((f + f') • A + (1 - (f + f')) • (1 : Matrix (Fin n) (Fin n) R)) i j = _
    have : (((1 : Matrix (Fin n) (Fin n) O) i j : O) : R) = (1 : Matrix (Fin n) (Fin n) R) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Subring.coe_add, Subring.coe_mul,
      this]
    rfl
  show ρ (Ym i j) = _
  rw [split, map_add (f := _), map_add (f := _), map_mul, map_sub, map_add (f := _), hρ, hz, hz', map_one]
  simp

end General

theorem frGL_val {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    (frGL β Y).1 = β.1 * Y.1.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 := rfl



theorem cut_mem_St_red : ∀ {D : D7} (n : ℕ) (β γ y : GL (Fin n) (EAf D)) (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → IsIntM (toEAf D e • γ.1) → IsIntM (toEAf D e • (γ⁻¹ : GL (Fin n) (EAf D)).1) → IsIntM (toEAf D (cA D e) • γ.1) → IsIntM (toEAf D (cA D e) • (γ⁻¹ : GL (Fin n) (EAf D)).1) → y.1 = β.1 * (toEAf D (e + cA D e) • γ.1 + (1 - toEAf D (e + cA D e)) • (1 : Matrix (Fin n) (Fin n) (EAf D))) * (β⁻¹ : GL (Fin n) (EAf D)).1 → y ∈ St β ∧ ∀ PP ∈ Z, ((redFn β PP y : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) = redM PP (toEAf D e • γ.1) := by
  intro D n β γ y Z e he h1 h2 h3 h4 hy
  obtain ⟨hf, hres⟩ := GlobalTheory.InnerSteps.resS_idemSum he
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hfc : toEAf D e * toEAf D (cA D e) = 0 := by rw [← map_mul, he.2, map_zero]
  have hf' : toEAf D (cA D e) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hcc]))
  obtain ⟨Y, hY, hred⟩ := exists_cut (Formalism.L2.Herm.intAf D.host.F D.host.E) hf hf'
    (by rw [← map_mul, hee]) (by rw [← map_mul, hcc]) hfc γ.1 (γ⁻¹ : GL (Fin n) (EAf D)).1
    γ.mul_inv γ.inv_mul h1 h3 h2 h4
  have hyY : y = frGL β Y := by
    have hs : toEAf D (e + cA D e) = toEAf D e + toEAf D (cA D e) := (toEAf D).map_add _ _
    refine Units.ext (hy.trans ?_)
    rw [frGL_val, hY, hs]
  subst hyY
  refine ⟨⟨Y, rfl⟩, fun PP hP => ?_⟩
  rw [redFn_frGL]
  ext i j
  have := hred (resS D.host.F PP) (hres PP hP) i j
  refine this.trans ?_
  unfold redM
  rw [dite_eq_left (h1 i j)]
  rfl

end GlobalTheory.FrameIdem

end
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

noncomputable section

namespace GlobalTheory.HalfUnit

variable {D : D7}

local notation "SI" => Formalism.L2.Herm.intAf D.host.F D.host.E

def liftI {b a : ℕ} (N : Matrix (Fin b) (Fin a) (EAf D)) (h : IsIntM N) : Matrix (Fin b) (Fin a) SI :=
  Matrix.of fun i j => ⟨N i j, h i j⟩

theorem liftI_map {b a : ℕ} (N : Matrix (Fin b) (Fin a) (EAf D)) (h : IsIntM N) :
    (liftI N h).map (SI).subtype = N := by
  ext i j
  rw [Matrix.map_apply]
  rfl

theorem isIntM_map {b a : ℕ} (X : Matrix (Fin b) (Fin a) SI) : IsIntM (X.map (SI).subtype) := fun i j => by
  rw [Matrix.map_apply]
  exact (X i j).2

open Classical in
def redE (PP : Formalism.L2.DIV.Pl D.host.E) (x : EAf D) : Formalism.L2.DIV.kP PP :=
  if h : x ∈ SI then Formalism.L2.DIV.resS D.host.F PP ⟨x, h⟩ else 0

theorem redM_apply (PP : Formalism.L2.DIV.Pl D.host.E) {b a : ℕ} (N : Matrix (Fin b) (Fin a) (EAf D)) (i : Fin b) (j : Fin a) :
    redM PP N i j = redE PP (N i j) := rfl

theorem redE_of_mem (PP : Formalism.L2.DIV.Pl D.host.E) {x : EAf D} (hx : x ∈ SI) :
    redE PP x = Formalism.L2.DIV.resS D.host.F PP ⟨x, hx⟩ := by
  unfold redE
  exact dif_pos hx

theorem redE_zero (PP : Formalism.L2.DIV.Pl D.host.E) : redE (D := D) PP 0 = 0 := by
  rw [redE_of_mem PP (Subring.zero_mem _)]
  exact map_zero (Formalism.L2.DIV.resS D.host.F PP)

theorem topL_pos {κ : Type} [Zero κ] {b a k : ℕ} (y : Matrix (Fin b) (Fin a) κ) {i j : Fin k}
    (h : i.val < b ∧ j.val < a) : topL k y i j = y ⟨i.val, h.1⟩ ⟨j.val, h.2⟩ := by
  unfold topL
  exact dif_pos h

theorem topL_neg {κ : Type} [Zero κ] {b a k : ℕ} (y : Matrix (Fin b) (Fin a) κ) {i j : Fin k}
    (h : ¬ (i.val < b ∧ j.val < a)) : topL k y i j = 0 := by
  unfold topL
  exact dif_neg h

theorem redM_map (PP : Formalism.L2.DIV.Pl D.host.E) {b a : ℕ} (X : Matrix (Fin b) (Fin a) SI) :
    redM PP (X.map (SI).subtype) = X.map (Formalism.L2.DIV.resS D.host.F PP) := by
  ext i j
  rw [redM_apply, Matrix.map_apply, Matrix.map_apply]
  exact redE_of_mem PP (X i j).2

theorem isIntM_mul {c b a : ℕ} {A : Matrix (Fin c) (Fin b) (EAf D)} {B : Matrix (Fin b) (Fin a) (EAf D)}
    (hA : IsIntM A) (hB : IsIntM B) : IsIntM (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem redM_mul (PP : Formalism.L2.DIV.Pl D.host.E) {c b a : ℕ} {A : Matrix (Fin c) (Fin b) (EAf D)}
    {B : Matrix (Fin b) (Fin a) (EAf D)} (hA : IsIntM A) (hB : IsIntM B) :
    redM PP (A * B) = redM PP A * redM PP B := by
  rw [← liftI_map A hA, ← liftI_map B hB, ← Matrix.map_mul, redM_map, redM_map, redM_map, Matrix.map_mul]

theorem isIntM_smul {b a : ℕ} {c : EAf D} (hc : c ∈ SI) {A : Matrix (Fin b) (Fin a) (EAf D)} (hA : IsIntM A) :
    IsIntM (c • A) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]
  exact Subring.mul_mem _ hc (hA i j)

theorem isIntM_adjugate {n : ℕ} {A : Matrix (Fin n) (Fin n) (EAf D)} (hA : IsIntM A) : IsIntM A.adjugate := by
  have key := isIntM_map (liftI A hA).adjugate
  rwa [← RingHom.mapMatrix_apply, RingHom.map_adjugate, RingHom.mapMatrix_apply, liftI_map] at key

theorem det_mem {n : ℕ} {A : Matrix (Fin n) (Fin n) (EAf D)} (hA : IsIntM A) : A.det ∈ SI := by
  have key := RingHom.map_det (SI).subtype (liftI A hA)
  rw [RingHom.mapMatrix_apply, liftI_map] at key
  rw [← key]
  exact ((liftI A hA).det).2

theorem topL_isIntM {m n : ℕ} {A : Matrix (Fin m) (Fin n) (EAf D)} (hA : IsIntM A) : IsIntM (topL n A) := fun i j => by
  by_cases h : i.val < m ∧ j.val < n
  · rw [topL_pos _ h]
    exact hA _ _
  · rw [topL_neg _ h]
    exact Subring.zero_mem _

theorem topL_redM (PP : Formalism.L2.DIV.Pl D.host.E) {m n : ℕ} (A : Matrix (Fin m) (Fin n) (EAf D)) :
    topL n (redM PP A) = redM PP (topL n A) := by
  ext i j
  by_cases h : i.val < m ∧ j.val < n
  · rw [topL_pos _ h, redM_apply, redM_apply, topL_pos _ h]
  · rw [topL_neg _ h, redM_apply, topL_neg _ h, redE_zero]

theorem topL_mul {m n : ℕ} (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) (EAf D)) (M : Matrix (Fin n) (Fin n) (EAf D)) :
    topL n (A * M) = topL n A * M := by
  ext i j
  have hi : i.val < m := lt_of_lt_of_le i.2 hnm
  rw [topL_pos _ ⟨hi, j.2⟩, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [topL_pos _ ⟨hi, k.2⟩]

end GlobalTheory.HalfUnit

namespace GlobalTheory.HalfUnit

theorem isUnit_res_det {D : D7} (PP : Formalism.L2.DIV.Pl D.host.E) {n : ℕ} {A : Matrix (Fin n) (Fin n) (EAf D)} (hA : IsIntM A)
    (h : IsUnit (redM PP A).det) : IsUnit (Formalism.L2.DIV.resS D.host.F PP ⟨A.det, det_mem hA⟩) := by
  have e1 : (⟨A.det, det_mem hA⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = (liftI A hA).det := by
    apply Subtype.ext
    have key := RingHom.map_det (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype (liftI A hA)
    rw [RingHom.mapMatrix_apply, liftI_map] at key
    exact key.symm
  have e2 := redM_map PP (liftI A hA)
  rw [liftI_map] at e2
  rw [e1, RingHom.map_det, RingHom.mapMatrix_apply, ← e2]
  exact h

theorem adj_eq {R : Type} [CommRing R] {n : ℕ} (A B G : Matrix (Fin n) (Fin n) R) (f w : R) (hB : B = A * G)
    (hw : A.det * w * f = f) (hfB : f • B = B) : f • G = (w • A.adjugate) * B := by
  rw [← hfB, hB, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul,
    Matrix.one_mul, smul_smul, smul_smul]
  conv_lhs => rw [← hw]
  congr 1
  ring

theorem smul_mul_fix {R : Type} [CommRing R] {a b c : ℕ} (A : Matrix (Fin a) (Fin b) R) (G : Matrix (Fin b) (Fin c) R)
    (f : R) (h : f • A = A) : f • (A * G) = A * G := by
  rw [← Matrix.smul_mul, h]

theorem mul_smul_fix {R : Type} [CommRing R] {n : ℕ} (A B G : Matrix (Fin n) (Fin n) R) (f : R) (hB : B = A * G)
    (h : f • B = B) : A * (f • G) = B := by
  rw [Matrix.mul_smul, ← hB, h]

theorem int_of_unit_tops : ∀ {D : D7} (m n : ℕ), n ≤ m → ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ (u : Matrix (Fin m) (Fin n) (EAf D)) (γ : GL (Fin n) (EAf D)), IsIntM u → IsIntM (HMul.hMul u (γ⁻¹ : GL (Fin n) (EAf D)).1) → (∀ i j, toEAf D e * u i j = u i j) → (∀ PP ∈ Z, IsUnit (topL n (redM PP u)).det) → (∀ PP ∈ Z, IsUnit (topL n (redM PP (HMul.hMul u (γ⁻¹ : GL (Fin n) (EAf D)).1))).det) → IsIntM (toEAf D e • γ.1) ∧ IsIntM (toEAf D e • (γ⁻¹ : GL (Fin n) (EAf D)).1) ∧ ∀ PP ∈ Z, topL n (redM PP (HMul.hMul u (γ⁻¹ : GL (Fin n) (EAf D)).1)) * redM PP (toEAf D e • γ.1) = topL n (redM PP u) := by
  intro D m n hnm Z e he u γ hu hv hfu hU hV
  have hUi : IsIntM (topL n u) := topL_isIntM hu
  have hVi : IsIntM (topL n (u * (γ⁻¹ : GL (Fin n) (EAf D)).1)) := topL_isIntM hv
  have hVeq : topL n (u * (γ⁻¹ : GL (Fin n) (EAf D)).1) = topL n u * (γ⁻¹ : GL (Fin n) (EAf D)).1 :=
    topL_mul hnm _ _
  have hUeq : topL n u = topL n (u * (γ⁻¹ : GL (Fin n) (EAf D)).1) * γ.1 := by
    rw [hVeq, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hfU : toEAf D e • topL n u = topL n u := by
    ext i j
    by_cases h : i.val < m ∧ j.val < n
    · rw [Matrix.smul_apply, topL_pos _ h, smul_eq_mul, hfu]
    · rw [Matrix.smul_apply, topL_neg _ h, smul_zero]
  have hfV : toEAf D e • topL n (u * (γ⁻¹ : GL (Fin n) (EAf D)).1) = topL n (u * (γ⁻¹ : GL (Fin n) (EAf D)).1) := by
    rw [hVeq]
    exact smul_mul_fix _ _ _ hfU
  obtain ⟨w, hw, hwe⟩ := GlobalTheory.T.exists_integral_inverse_at_splitPlaces_of_units Z e he _ (det_mem hUi) fun PP hPP =>
    isUnit_res_det PP hUi (by rw [← topL_redM]; exact hU PP hPP)
  obtain ⟨w', hw', hwe'⟩ := GlobalTheory.T.exists_integral_inverse_at_splitPlaces_of_units Z e he _ (det_mem hVi) fun PP hPP =>
    isUnit_res_det PP hVi (by rw [← topL_redM]; exact hV PP hPP)
  have hγ := adj_eq _ _ _ (toEAf D e) w' hUeq hwe' hfU
  have hγi := adj_eq _ _ _ (toEAf D e) w hVeq hwe hfV
  have hfγ : IsIntM (toEAf D e • γ.1) := by
    rw [hγ]
    exact isIntM_mul (isIntM_smul hw' (isIntM_adjugate hVi)) hUi
  refine ⟨hfγ, ?_, ?_⟩
  · rw [hγi]
    exact isIntM_mul (isIntM_smul hw (isIntM_adjugate hUi)) hVi
  · intro PP _
    rw [topL_redM, topL_redM, ← redM_mul PP hVi hfγ, mul_smul_fix _ _ _ _ hUeq hfU]

end GlobalTheory.HalfUnit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjAutSmooth

theorem castGA_mem {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA) : castGA e x ∈ I'.GFset ↔ x ∈ I.GFset := by
  subst e; rfl

theorem iotaX_rat {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {γ : GA D (D.sp.Y 0)} (hγ : γ ∈ GQ (D.sp.Y 0)) : iotaX X h γ ∈ X.B.I.GFset := by
  show castGA h.symm (Formalism.IndefR.RationalEmbedding.iota D γ) ∈ X.B.I.GFset
  rw [castGA_mem]
  exact (Formalism.IndefR.RationalEmbedding.iota_rat D γ).1 hγ



theorem conjMap_isAutFunSm : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, IsAutFunSm R.θ (Yc D 0) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u) := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hRI hGrp hMod hHost hιE t c ht hCL hcq Φ hΦ hrep u
  set Ψ := GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t with hΨ
  have hθ : IsInfFam R.θ := hMod.inf
  have he : GlobalTheory.RepSmooth.IsEquiv R.θ Ψ := fun τ g hg v w hw =>
    GlobalTheory.T.conjugatedIntertwiner_equivariant_realPlace hDS R F X h hRI hGrp hMod hHost hιE t c ht hCL hcq Φ hΦ hrep τ g hg v w hw
  have hs : GlobalTheory.RepSmooth.IsSob Ψ := fun τ v x =>
    GlobalTheory.T.conjugateIntertwinerValues_sobolevContinuous hDS R F X h hRI hGrp hMod hHost hιE t c ht hCL hcq Φ hΦ hrep τ v x
  have hval : ∀ v (y : GA D (Yc D 0)), Ψ v y = star (GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c v)))
      (iotaX X h (y * t⁻¹))) := fun v y => GlobalTheory.ConjRowMult.conjMap_apply X (MP R) c Φ h t v y
  have hcont : ∀ v, Continuous (Ψ v) := by
    intro v
    obtain ⟨ψ, hψ⟩ := hrep v
    have e : Ψ v = fun y : GA D (Yc D 0) => star (ψ (iotaX X h (y * t⁻¹))) := by
      funext y; exact (hval v y).trans (by rw [GlobalTheory.ConjRowMult.contRepL_spec X hψ])
    rw [e]
    exact continuous_star.comp (hψ.1.comp ((iotaX X h).continuous.comp (continuous_mul_const t⁻¹)))
  refine ⟨⟨?_, ?_, hcont u⟩, fun k τs Xs hX g => GlobalTheory.RepSmooth.smooth hθ he hs hcont u k τs Xs hX g,
    GlobalTheory.RepSmooth.zfin he hs u, ?_⟩
  · intro γ hγ g
    obtain ⟨ψ, hψ⟩ := hrep u
    rw [hval, hval, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
    congr 1
    have e2 : iotaX X h (γ * g * t⁻¹) = iotaX X h γ * iotaX X h (g * t⁻¹) := by
      exact (congrArg (iotaX X h) (mul_assoc γ g t⁻¹)).trans (map_mul (iotaX X h) γ (g * t⁻¹))
    rw [e2]; exact hψ.2.1 _ (iotaX_rat X h hγ) _
  · obtain ⟨U, hU, hUk⟩ := GlobalTheory.GoodFiniteDim.exists_open_subgroup (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))
    refine ⟨U, hU, fun k hk hkf g => ?_⟩
    obtain ⟨h1, h2⟩ := hUk k hk hkf
    rw [GlobalTheory.T.conjugatedIntertwiner_hasColumnLevel hDS R F X h hRI hGrp hMod hHost hιE t c ht hCL hcq Φ hΦ hrep u k h1 g, h2, one_mul]
  · have key : ∃ N : ℕ, ∀ v (x : GA D (Yc D 0)), ∃ C : ℝ, ∀ g ∈ GinfC (Yc D 0),
        ‖Ψ v (x * g)‖ ≤ C * normInf R.θ (Yc D 0) g ^ N := by
      rcases Nat.eq_zero_or_pos (D.sp.Y 0).rank with hn | hn
      · refine ⟨0, fun v x => ⟨‖Ψ v x‖, fun a _ => ?_⟩⟩
        have : a = 1 := Subtype.ext (Units.ext (Matrix.ext fun i => (Fin.cast hn i).elim0))
        simp [this]
      obtain ⟨hfin, hnorm⟩ := GlobalTheory.T.realPointIdentification_leastSize_linear_growth R F X h hRI hGrp hMod hιE
      obtain ⟨m, hm⟩ := GlobalTheory.T.intertwiner_continuous_representative_power_bound hDS R F X h hRI hGrp hMod hHost hιE t c ht hCL hcq Φ hΦ hrep hn
      refine ⟨m, fun v x => ?_⟩
      obtain ⟨C, hC⟩ := hm v
      obtain ⟨C', hC0, hC'⟩ := hnorm hn (iotaX X h (x * t⁻¹))
      refine ⟨|C| * C' ^ m, fun a ha => ?_⟩
      have hi2 : (iotaX X h t⁻¹).1 = 1 :=
        ((GlobalTheory.IotaReal.iotaX_real_finite R F X h hRI hGrp hMod hιE).1 t⁻¹).1 (inv_mem ht)
      have hi1 : (iotaX X h a).2 = 1 := hfin a ha
      have hc : iotaX X h a * iotaX X h t⁻¹ = iotaX X h t⁻¹ * iotaX X h a :=
        Prod.ext (by simp [Prod.fst_mul, hi2]) (by simp [Prod.snd_mul, hi1])
      have hcomm : iotaX X h (x * a * t⁻¹) = iotaX X h (x * t⁻¹) * iotaX X h a := by
        have e1 : iotaX X h (x * a * t⁻¹) = iotaX X h x * iotaX X h a * iotaX X h t⁻¹ := by
          exact (map_mul (iotaX X h) (x * a) t⁻¹).trans (congrArg (· * iotaX X h t⁻¹) (map_mul (iotaX X h) x a))
        have e2 : iotaX X h (x * t⁻¹) = iotaX X h x * iotaX X h t⁻¹ := by
          exact map_mul (iotaX X h) x t⁻¹
        rw [e1, e2, mul_assoc, hc, ← mul_assoc]
      have hp : 0 ≤ (GlobalTheory.Count.tau1 X.B.I (iotaX X h (x * t⁻¹) * iotaX X h a))⁻¹ :=
        inv_nonneg.2 ((GlobalTheory.TauLipschitz.tauLip X.B.I (by rw [h]; exact hn)).1 _).le
      have h1 := hC (iotaX X h (x * a * t⁻¹))
      rw [hcomm] at h1
      rw [hval, norm_star, hcomm]
      refine h1.trans ?_
      calc C * (GlobalTheory.Count.tau1 X.B.I (iotaX X h (x * t⁻¹) * iotaX X h a))⁻¹ ^ m
          ≤ |C| * (C' * normInf R.θ (Yc D 0) a) ^ m :=
            mul_le_mul (le_abs_self _) (pow_le_pow_left₀ hp (hC' a ha) m) (pow_nonneg hp m) (abs_nonneg _)
        _ = |C| * C' ^ m * normInf R.θ (Yc D 0) a ^ m := by rw [mul_pow, mul_assoc]
    obtain ⟨N, hN⟩ := key
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨v, hv⟩ := GlobalTheory.RepSmooth.foldr_rder he hs u l hl
    obtain ⟨C, hC⟩ := hN v x
    exact ⟨C, fun g hg => (congrArg norm (congrFun hv (x * g))).le.trans (hC g hg)⟩

end GlobalTheory.ConjAutSmooth
end
