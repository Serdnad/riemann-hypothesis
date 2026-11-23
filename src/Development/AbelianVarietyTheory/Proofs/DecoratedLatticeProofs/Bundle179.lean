module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlacePairMovesLatticeVacuumReading
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle159
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle160
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Core.Rk.DownCompare

open scoped ComplexConjugate Matrix ComplexOrder Pointwise TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff)
open GlobalTheory.Core.Rk.IP (WRep up wcoef rcoef)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lattices

open Formalism.L2.DIV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

end Lattices

variable {D : D7}

def latIn (V : HSp D) (L : Lat V) : Submodule (𝓞 D.host.E) V.V :=
  L.map (V.frame.equivFun.symm.toLinearMap.restrictScalars (𝓞 D.host.E))

theorem mem_latIn {V : HSp D} {L : Lat V} {x : V.V} : x ∈ latIn V L ↔ V.frame.equivFun x ∈ L :=
  ⟨by rintro ⟨y, hy, rfl⟩; exact (V.frame.equivFun.apply_symm_apply y).symm ▸ hy, fun h => ⟨_, h, V.frame.equivFun.symm_apply_apply x⟩⟩

theorem hT_eq (V : HSp D) (x y : V.V) :
    V.hT x y = ∑ i, ∑ j, star (V.frame.equivFun x i) * V.gram i j * V.frame.equivFun y j := by
  conv_lhs => rw [← V.frame.sum_equivFun x, ← V.frame.sum_equivFun y]

  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, HSpace.gram,
  Finset.mul_sum, starRingEnd_apply, RingHom.id_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem latIn_lat {V : HSp D} {L : Lat V} (h : IsSelfDualC V L) : Submodule.IsLattice D.host.E (latIn V L) :=
  Submodule.IsLattice.of_fg D.host.E (h.1.fg.map _)

theorem latIn_unimod {V : HSp D} {L : Lat V} (h : IsSelfDualC V L) : Formalism.HermitianLatticesTheory.IsUnimodular V.hT (latIn V L) := by
  ext y
  rw [mem_latIn, h.2]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one,
    LinearMap.restrictScalars_apply]
  constructor
  · intro hy x hx
    obtain ⟨b, hb⟩ := hy _ (mem_latIn.2 (by rwa [LinearEquiv.apply_symm_apply] : V.frame.equivFun (V.frame.equivFun.symm x) ∈ L))
    exact ⟨b, by rw [hT_eq, LinearEquiv.apply_symm_apply] at hb; exact hb⟩
  · intro hy x hx
    obtain ⟨b, hb⟩ := hy _ (mem_latIn.1 hx)
    exact ⟨b, by rw [hT_eq]; exact hb⟩

def reset (V : HSp D) (L : Lat V) (h : IsSelfDualC V L) (s : (D.host.E →+* ℂ) → ℕ × ℕ) : HSp D :=
  { V with sig := s, L0 := latIn V L, standardTuple_isLattice := latIn_lat h, baseLattice_isUnimodular := latIn_unimod h }

theorem frameLat_reset (V : HSp D) (L : Lat V) (h : IsSelfDualC V L) (s : (D.host.E →+* ℂ) → ℕ × ℕ) :
    frameLat (reset V L h s) = L := by
  ext x
  exact (mem_latIn (V := V) (L := L) (x := V.frame.equivFun.symm x)).trans (by rw [V.frame.equivFun.apply_symm_apply x]; rfl)

section Transport

variable {ψ : AddChar (AF D.host.F) ℂ} {A W : HSp D} {LA : Lat A} {LW : Lat W} (hA : IsSelfDualC A LA) (hW : IsSelfDualC W LW)
  (sA sW : (D.host.E →+* ℂ) → ℕ × ℕ)

end Transport

end GlobalTheory.Core.Rk.DownCompare

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem esymm_cons_succ_C (a : ℂ) (s : Multiset ℂ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.sum_map_mul_left]

theorem coeff_prod_one_add_C (s : Multiset ℂ) (n : ℕ) :
    ((s.map fun a => (1 + Polynomial.C a * Polynomial.X : Polynomial ℂ)).prod).coeff n = s.esymm n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, Polynomial.coeff_add,
      Polynomial.coeff_C_mul]
    cases n with
    | zero => simp [ih, Multiset.esymm]
    | succ n => rw [Polynomial.coeff_X_mul, ih, ih, esymm_cons_succ_C]

theorem esymm_add_C (s t : Multiset ℂ) (n : ℕ) :
    (s + t).esymm n = ∑ i ∈ Finset.range (n + 1), s.esymm i * t.esymm (n - i) := by
  rw [← coeff_prod_one_add_C, Multiset.map_add (f := _), Multiset.prod_add, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_prod_one_add_C]

theorem esymm_map_mul_C (c : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (s.map (fun x => c * x)).esymm k = c ^ k * s.esymm k := by
  have h := Multiset.pow_smul_esymm c k s
  simpa [smul_eq_mul] using h.symm

theorem esymm_eq_zero_of_lt (s : Multiset ℂ) {k : ℕ} (h : s.card < k) : s.esymm k = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_eq_empty k h]

theorem natCast_cpow_half (Q : ℕ) (m : ℤ) :
    (Q : ℂ) ^ ((m : ℂ) / 2) = ((Real.sqrt Q : ℝ) : ℂ) ^ m := by
  have h1 : ((Real.sqrt Q : ℝ) : ℂ) = (Q : ℂ) ^ ((1 / 2 : ℂ)) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rfl
  rw [h1, ← Complex.cpow_int_mul]
  congr 1
  ring

theorem sqrt_sq_C (Q : ℕ) : ((Real.sqrt Q : ℝ) : ℂ) ^ 2 = (Q : ℂ) := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  push_cast
  rfl

theorem esymm_string (Q : ℕ) (s z : ℂ) (hs : s ≠ 0) (hQ : s ^ 2 = (Q : ℂ)) (t : ℕ) :
    ∀ l : ℕ, ((Finset.range t).val.map fun i : ℕ => z * s ^ ((t : ℤ) - 1 - 2 * i)).esymm l =
      z ^ l * s ^ (-((l : ℤ) * ((t : ℤ) - l))) * (Formalism.L2.Col.gaussBin Q t l : ℂ) := by
  induction t with
  | zero =>
    intro l
    cases l with
    | zero => simp [Multiset.esymm, Formalism.L2.Col.gaussBin]
    | succ l => simp [Multiset.esymm, Formalism.L2.Col.gaussBin, Multiset.powersetCard_zero_right]
  | succ t ih =>
    intro l
    have hm : ((Finset.range (t + 1)).val.map fun i : ℕ => z * s ^ (((t + 1 : ℕ) : ℤ) - 1 - 2 * i)) =
        (z * s ^ (-(t : ℤ))) ::ₘ (((Finset.range t).val.map fun i : ℕ => z * s ^ ((t : ℤ) - 1 - 2 * i)).map
          fun x => s * x) := by
      rw [Finset.range_val, Finset.range_val, Multiset.range_succ, Multiset.map_cons, Multiset.map_map]
      congr 1
      · congr 1; congr 1; push_cast; ring
      · refine Multiset.map_congr rfl fun i _ => ?_
        simp only [Function.comp_apply]
        rw [mul_left_comm]
        congr 1
        rw [show (((t + 1 : ℕ) : ℤ) - 1 - 2 * i) = 1 + ((t : ℤ) - 1 - 2 * i) by push_cast; ring,
          zpow_add₀ hs, zpow_one]
    rw [hm]
    cases l with
    | zero => simp [Multiset.esymm, Formalism.L2.Col.gaussBin]
    | succ l =>
      rw [esymm_cons_succ_C, esymm_map_mul_C, esymm_map_mul_C, ih, ih, Formalism.L2.Col.gaussBin]
      push_cast
      rw [← hQ]
      have h1 : s ^ (l + 1) * s ^ (-(((l : ℤ) + 1) * ((t : ℤ) - ((l : ℤ) + 1)))) =
          s ^ (-(((l : ℤ) + 1) * ((t : ℤ) + 1 - ((l : ℤ) + 1)))) * (s ^ 2) ^ (l + 1) := by
        rw [← pow_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hs, ← zpow_add₀ hs]
        congr 1; push_cast; ring
      have h2 : s ^ (-(t : ℤ)) * s ^ l * s ^ (-((l : ℤ) * ((t : ℤ) - l))) =
          s ^ (-(((l : ℤ) + 1) * ((t : ℤ) + 1 - ((l : ℤ) + 1)))) := by
        rw [← zpow_natCast, ← zpow_add₀ hs, ← zpow_add₀ hs]
        congr 1; push_cast; ring
      linear_combination (z ^ (l + 1) * (Formalism.L2.Col.gaussBin Q t (l + 1) : ℂ)) * h1 +
        (z ^ (l + 1) * (Formalism.L2.Col.gaussBin Q t l : ℂ)) * h2

theorem map_coe_seg (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (z : ℂˣ) (t : ℕ) :
    (seg w z t).map (fun b : ℂˣ => (b : ℂ)) =
      (Finset.range t).val.map fun i : ℕ => (z : ℂ) * ((Real.sqrt (qV E w) : ℝ) : ℂ) ^ ((t : ℤ) - 1 - 2 * i) := by
  rw [seg, Multiset.map_map]
  refine Multiset.map_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, Units.val_mul, coe_npowU, npow]
  congr 1
  rw [← natCast_cpow_half]
  show ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ _ = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ _
  congr 1
  push_cast
  ring

theorem satEig_map_add_seg : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a t k : ℕ) (B : Multiset ℂˣ) (z y : ℂˣ), B.card = a → k ≤ a + t → satEig (qV E w) (a + t) (B.map (z * y⁻¹ * ·) + seg w z t) k = ∑ j ∈ Finset.range (a + 1), (if j ≤ k then (qV E w : ℂ) ^ ((a - j) * (k - j)) * (Formalism.L2.Col.gaussBin (qV E w) t (k - j) : ℂ) * ((z : ℂ) * ((Real.sqrt (qV E w) : ℂ) ^ a)⁻¹) ^ k * (((y : ℂ))⁻¹ * (Real.sqrt (qV E w) : ℂ) ^ (a + t)) ^ j else 0) * satEig (qV E w) a B j := by
  intro E _ _ w a t k B z y hB _
  have hsQ := sqrt_sq_C (qV E w)
  have hs : ((Real.sqrt (qV E w) : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0] at hsQ
    have h1 : 1 < qV E w := one_lt_absNorm w
    have : ((qV E w : ℕ) : ℂ) = 0 := by rw [← hsQ]; ring
    exact (by omega : qV E w ≠ 0) (by exact_mod_cast this)
  have hA : (B.map (z * y⁻¹ * ·)).map (fun b : ℂˣ => (b : ℂ)) =
      (B.map fun b : ℂˣ => (b : ℂ)).map fun x => ((z : ℂ) * (y : ℂ)⁻¹) * x := by
    simp [Multiset.map_map, Function.comp_def]
  have hBc : (B.map fun b : ℂˣ => (b : ℂ)).card = a := by simp [hB]
  set Q := qV E w with hQdef
  set s : ℂ := ((Real.sqrt Q : ℝ) : ℂ) with hsdef
  set F : ℕ → ℂ := fun j => (if j ≤ k then (Q : ℂ) ^ ((a - j) * (k - j)) * (Formalism.L2.Col.gaussBin Q t (k - j) : ℂ) *
    ((z : ℂ) * (s ^ a)⁻¹) ^ k * (((y : ℂ))⁻¹ * s ^ (a + t)) ^ j else 0) * satEig Q a B j with hF
  have hFa : ∀ j, a < j → F j = 0 := by
    intro j hj
    simp only [hF, satEig, esymm_eq_zero_of_lt _ (hBc ▸ hj), mul_zero]
  have hFk : ∀ j, k < j → F j = 0 := by
    intro j hj
    simp only [hF, if_neg (show ¬ j ≤ k by omega), zero_mul]
  have hR : ∑ j ∈ Finset.range (a + 1), F j = ∑ j ∈ Finset.range (k + 1), F j := by
    rw [Finset.sum_subset (Finset.range_mono (show a + 1 ≤ a + k + 1 by omega))
        (fun j _ hn => hFa j (by simp at hn; omega)),
      Finset.sum_subset (Finset.range_mono (show k + 1 ≤ a + k + 1 by omega))
        (fun j _ hn => hFk j (by simp at hn; omega))]
  rw [hR, satEig, Multiset.map_add (f := _), esymm_add_C, Finset.mul_sum, hA, map_coe_seg]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [esymm_map_mul_C, esymm_string Q s z hs hsQ t]
  by_cases hja : j ≤ a
  · simp only [hF, if_pos hjk, satEig]
    have c1 : (Q : ℂ) ^ (((k : ℂ) * (((a + t : ℕ) : ℂ) - k)) / 2) = s ^ ((k : ℤ) * ((a : ℤ) + t - k)) := by
      rw [← natCast_cpow_half]; congr 1; push_cast; ring
    have c2 : (Q : ℂ) ^ (((j : ℂ) * ((a : ℂ) - j)) / 2) = s ^ ((j : ℤ) * ((a : ℤ) - j)) := by
      rw [← natCast_cpow_half]; congr 1; push_cast; ring
    rw [c1, c2]
    have hz : ((z : ℂ) * (y : ℂ)⁻¹) ^ j * (z : ℂ) ^ (k - j) = (z : ℂ) ^ k * ((y : ℂ)⁻¹) ^ j := by
      rw [mul_pow, mul_right_comm, ← pow_add, Nat.add_sub_cancel' hjk]
    have hsI : s ^ ((k : ℤ) * ((a : ℤ) + t - k)) * s ^ (-(((k - j : ℕ) : ℤ) * ((t : ℤ) - ((k - j : ℕ) : ℤ)))) =
        (s ^ 2) ^ ((a - j) * (k - j)) * ((s ^ a)⁻¹) ^ k * (s ^ (a + t)) ^ j * s ^ ((j : ℤ) * ((a : ℤ) - j)) := by
      simp only [← pow_mul, inv_pow, ← zpow_natCast, ← _root_.zpow_neg, ← _root_.zpow_mul, ← zpow_add₀ hs]
      congr 1
      push_cast [Nat.cast_sub hja, Nat.cast_sub hjk]
      ring
    calc _ = (s ^ ((k : ℤ) * ((a : ℤ) + t - k)) * s ^ (-(((k - j : ℕ) : ℤ) * ((t : ℤ) - ((k - j : ℕ) : ℤ))))) *
          (((z : ℂ) * (y : ℂ)⁻¹) ^ j * (z : ℂ) ^ (k - j)) *
          ((Formalism.L2.Col.gaussBin Q t (k - j) : ℂ) * (B.map fun b : ℂˣ => (b : ℂ)).esymm j) := by ring
      _ = ((s ^ 2) ^ ((a - j) * (k - j)) * ((s ^ a)⁻¹) ^ k * (s ^ (a + t)) ^ j * s ^ ((j : ℤ) * ((a : ℤ) - j))) *
          ((z : ℂ) ^ k * ((y : ℂ)⁻¹) ^ j) *
          ((Formalism.L2.Col.gaussBin Q t (k - j) : ℂ) * (B.map fun b : ℂˣ => (b : ℂ)).esymm j) := by rw [hsI, hz]
      _ = _ := by rw [hsQ]; ring
  · rw [esymm_eq_zero_of_lt _ (by omega), hFa j (by omega)]
    ring

end GlobalTheory.ChainOnto
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun.DblSplit

section Pure

variable {A : Type} [CommRing A] {m ι : Type} [Fintype m] [Fintype ι] [DecidableEq m] [DecidableEq ι] (e : m ⊕ m ≃ ι)

theorem blkGL_mem_diag (a : GL m A) : blkGL e (a, a) ∈ Formalism.UG.stabGL (diagSub A e) :=
  mem_stabGL_diagSub.2 ((keepsDiag_blkMat _).2 rfl)

theorem keepsDiag_conj_iff (a : GL m A) (x : GL ι A) :
    KeepsDiag e ((blkGL e (a, a))⁻¹ * x * blkGL e (a, a)).1 ↔ KeepsDiag e x.1 := by
  rw [← mem_stabGL_diagSub, ← mem_stabGL_diagSub, Subgroup.mul_mem_cancel_right _ (blkGL_mem_diag e a),
    Subgroup.mul_mem_cancel_left _ (inv_mem (blkGL_mem_diag e a))]

theorem det_leviMat_conj (a : GL m A) {x : GL ι A} (hx : KeepsDiag e x.1) :
    (leviMat e ((blkGL e (a, a))⁻¹ * x * blkGL e (a, a)).1).det = (leviMat e x.1).det := by
  let p : Formalism.UG.stabGL (diagSub A e) := ⟨_, blkGL_mem_diag e a⟩
  let q : Formalism.UG.stabGL (diagSub A e) := ⟨x, mem_stabGL_diagSub.2 hx⟩
  change (leviGL e (p⁻¹ * q * p)).1.det = (leviGL e q).1.det
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.det_units_conj']

theorem det_quotMat_conj (a : GL m A) {x : GL ι A} (hx : KeepsDiag e x.1) :
    (quotMat e ((blkGL e (a, a))⁻¹ * x * blkGL e (a, a)).1).det = (quotMat e x.1).det := by
  have h1 := ((keepsDiag_conj_iff e a x).2 hx).det_eq
  rw [det_leviMat_conj e a hx, Units.val_mul, Units.val_mul, Matrix.det_units_conj', hx.det_eq] at h1
  have hu : IsUnit (leviMat e x.1).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
    rw [hx.det_eq] at this
    exact isUnit_of_mul_isUnit_left this
  exact (hu.mul_left_cancel h1).symm

omit [Fintype m] [Fintype ι] [DecidableEq m] [DecidableEq ι] in
theorem quotMat_map {B : Type} [CommRing B] (f : A →+* B) (M : Matrix ι ι A) :
    quotMat e (M.map f) = (quotMat e M).map f := by
  ext i j; simp [quotMat, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁]

end Pure

theorem ordL_eq_neg_log {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (x : K) :
    ordL x = -WithZero.log (Valued.v x) := by
  unfold ordL
  split_ifs with h
  · simp [h]
  · conv_rhs => rw [← WithZero.coe_unzero h]
    rfl

theorem isHermND_dbl {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) : IsHermND σ (dblGram finSumFinEquiv J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
    simp only [dblGram, blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases a with a | a <;> rcases b with b | b <;> simp [hJ.1]
  · rw [dblGram, det_blkMat]
    exact mul_ne_zero hJ.2 (by rw [Matrix.det_neg]; exact mul_ne_zero (pow_ne_zero _ (by simp)) hJ.2)

theorem exists_dbl_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L], ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E), IsSplitChart σ J L h e → ∃ f : GLoc σ Q v ≃* GL (Fin (n + n)) (w.adicCompletion E), (∀ g, g ∈ KFin σ Q L v ↔ f g ∈ KGL w (n := (n + n))) ∧ (∀ y y', f (ioH _ σ hQ (y, y')) = blkGL finSumFinEquiv (e y, e y')) ∧ (∀ g, g ∈ siegelH (Fv F v) σ Q ↔ KeepsDiag finSumFinEquiv (f g).1) ∧ ∀ p : siegelH (Fv F v) σ Q, toCompl h (aH _ σ Q p).1 = (leviMat finSumFinEquiv (f p).1).det ∧ ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → ordL (toCompl h' (aH _ σ Q p).1) = -ordL (quotMat finSumFinEquiv (f p).1).det := by
  intro F E _ _ _ _ _ σ hc n J hJ Q hQ L _ v w h hv hL e he
  have hQ' : IsHermND σ Q := hQ ▸ isHermND_dbl σ hJ
  obtain ⟨⟨a, ha, ea⟩, -⟩ := id he
  obtain ⟨τ, hτ⟩ := SplitChart.exists_splitPrime_eq hc hv h
  let φ := ConjPlace.complEquiv hc h hτ
  let β := Formalism.UG.bc (φ.symm : w.adicCompletion E →+* Fv F v) (blkGL finSumFinEquiv (a, a))
  have hβ : IsSplitBasis τ (sumLat finSumFinEquiv L L) β := by
    apply (ConjPlace.isFrameAt_iff hc h hτ β).1
    have heq : Formalism.UG.bc (φ : Fv F v →+* w.adicCompletion E) β =
        blkGL finSumFinEquiv (a, a) := by
      apply Units.ext
      exact Matrix.ext fun i j => φ.apply_symm_apply _
    rw [heq]
    exact GlobalTheory.T.isLatticeFrameAtPlace_directSum_blockDiagonal E w n L a ha
  obtain ⟨f₀, ⟨⟨b, hb, e0⟩, hK⟩⟩ :=
    ConjPlace.exists_isSplitChart_of_basis hc hQ' (isSelfDualAt_dbl hQ hL) h hτ hβ
  have hk := hb.inv_mul_mem (GlobalTheory.T.isLatticeFrameAtPlace_directSum_blockDiagonal E w n L a ha)
  have ef : ∀ g, f₀.trans (MulAut.conj (b⁻¹ * blkGL finSumFinEquiv (a, a))⁻¹) g =
      (blkGL finSumFinEquiv (a, a))⁻¹ * locMat σ Q h g * blkGL finSumFinEquiv (a, a) := fun g => by
    rw [MulEquiv.trans_apply, MulAut.conj_apply, e0]; group
  have hP : ∀ p : siegelH (Fv F v) σ Q, KeepsDiag finSumFinEquiv (locMat σ Q h p).1 := fun p =>
    (mem_siegelOf.1 p.2).map _ (toCompl h)
  refine ⟨f₀.trans (MulAut.conj (b⁻¹ * blkGL finSumFinEquiv (a, a))⁻¹), fun g => ?_, fun y y' => ?_, fun g => ?_,
    fun p => ⟨?_, fun w' h' hne => ?_⟩⟩
  · rw [MulEquiv.trans_apply, MulAut.conj_apply, inv_inv, Subgroup.mul_mem_cancel_right _ hk,
      Subgroup.mul_mem_cancel_left _ (inv_mem hk)]
    exact hK g
  · have h1 : locMat σ Q h (ioH _ σ hQ (y, y')) = blkGL finSumFinEquiv (locMat σ J h y, locMat σ J h y') :=
      bc_blkGL finSumFinEquiv (toCompl h) _ _
    rw [ef, h1, ← map_inv, ← map_mul, ← map_mul, ea, ea]
    rfl
  · rw [ef, keepsDiag_conj_iff]
    refine ⟨fun hg => hP ⟨g, hg⟩, fun hg => ?_⟩
    obtain ⟨τ, hτ⟩ := SplitChart.exists_splitPrime_eq hc hv h
    refine GlobalTheory.Core.Rk.IwSplit.mem_siegelH_of_split hc hQ hJ.2 τ (mem_stabGL_diagSub.2 ?_)
    rw [ConjPlace.locMat_eq hc h hτ] at hg
    have h2 := hg.map _ ((ConjPlace.complEquiv hc h hτ).symm : w.adicCompletion E →+* Fv F v)
    convert h2 using 1
    exact Matrix.ext fun i j => ((ConjPlace.complEquiv hc h hτ).symm_apply_apply _).symm
  · rw [ef, det_leviMat_conj _ a (hP p)]
    change toCompl h (leviMat finSumFinEquiv (matHom _ σ Q p).1).det =
      (leviMat finSumFinEquiv ((matHom _ σ Q p).1.map (toCompl h))).det
    rw [leviMat_map, RingHom.map_det, RingHom.mapMatrix_apply]
  · obtain ⟨c, hcv, -, hcc, -⟩ := ConjPlace.exists_conj_chart hc hJ hL hne h h' he
    rw [ef, det_quotMat_conj _ a (hP p)]
    have h1 : (quotMat finSumFinEquiv (locMat σ Q h p).1).det =
        toCompl h (quotMat finSumFinEquiv (matHom _ σ Q p).1).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← quotMat_map]
      rfl
    have h2 := congrArg (fun y => Valued.v (toCompl h' y)) (sigR_det_quot_mul_aH hQ hJ.2 p)
    simp only [map_mul, map_one, ← hcc, hcv] at h2
    rw [h1, ordL_eq_neg_log, ordL_eq_neg_log, eq_inv_of_mul_eq_one_right h2, WithZero.log_inv]

end GlobalTheory.LFun.DblSplit
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlacePair_moves_latticeVacuumReading : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ (ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC S ΛS' → IsSelfDualC T ΛT → IsSelfDualC T ΛT' → ∀ e, IsSplitIdem D e → ∀ (s : GA D S) (s' : GA D T), SuppAt e S s → SuppAt e T s' → ∀ x₀ y₀, IsDetAt e S s x₀ → IsDetAt e T s' y₀ → (∀ u : WO S T, u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u = actO S T s s' u₀) → ∀ A₁ A₂ : AddSubgroup (VCx D.what₂.Tau a b), (∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → (v ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ embH (tauE D) δ (toHom S T hS hT γ) ∈ A₁)) → (∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → (v ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ embH (tauE D) δ (toHom S T hS hT γ) ∈ A₂)) → (∀ z ∈ A₂, ∃ γ, z = embH (tauE D) δ (toHom S T hS hT γ)) → Formalism.L2.Th1.H.IsSelfDual (HV sc) A₂ → Formalism.L2.Th1.H.IsSemiChar (HV sc) A₁ (alV D.host.d sc) → Formalism.L2.Th1.H.IsSemiChar (HV sc) A₂ (alV D.host.d sc) → Formalism.L2.Th1.H.relIdx A₁ A₂ ≠ 0 → ∀ f, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f → xiN θ S T hS hT δ sc f ∈ Formalism.L2.Th1.H.fixedBy (HV sc) (alV D.host.d sc) A₁ → xiN θ S T hS hT δ sc (om (s, s') f) ∈ Formalism.L2.Th1.H.fixedBy (HV sc) (alV D.host.d sc) A₂ → xiN θ S T hS hT δ sc (om (s, s') f) ≠ 0 → xiN θ S T hS hT δ sc (om (s, s') f) = fun z => ((μ x₀ : ℂ))⁻¹ * (μ y₀ : ℂ) * Formalism.L2.Th1.H.inter (HV sc) (alV D.host.d sc) A₁ A₂ (xiN θ S T hS hT δ sc f) z := by
  first | exact @GlobalTheory.AdForm.SplitGen.moves_reading | exact GlobalTheory.AdForm.SplitGen.moves_reading | (intros; apply GlobalTheory.AdForm.SplitGen.moves_reading <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.halfA_components_mem_completedLattice_offPrimes : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  first | exact @GlobalTheory.HalfAComp.zmem | exact GlobalTheory.HalfAComp.zmem | (intros; apply GlobalTheory.HalfAComp.zmem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.halfB_components_mem_completedLattice_offConj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y')) - ((LinearMap.toMatrix' y').map fun r => cA D e * incA D r) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  first | exact @GlobalTheory.HalfBComp.ybmem | exact GlobalTheory.HalfBComp.ybmem | (intros; apply GlobalTheory.HalfBComp.ybmem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bessel_column_scalar_form_norm_bound : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK), ∃ C : ℝ, ∀ (ξ : X.Vpi u) (a : GA D A), ‖B.colForm T.1 ξ a‖ ≤ C * ‖ξ‖ := by
  first | exact @GlobalTheory.Core.Mi.ColBound.colForm_bound | exact GlobalTheory.Core.Mi.ColBound.colForm_bound | (intros; apply GlobalTheory.Core.Mi.ColBound.colForm_bound <;> assumption)
end
