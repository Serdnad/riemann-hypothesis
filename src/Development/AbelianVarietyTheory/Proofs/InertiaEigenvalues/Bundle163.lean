module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle151
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfAssembleMem
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle140
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle141
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.SplitEt

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]

theorem algebraMap_norm_eq_mul_star (z : E) : algebraMap F E (Algebra.norm F z) = z * star z := by
  apply GlobalTheory.JR.EtFacts.normE <;> assumption

def piCoord {ι : Type} [Fintype ι] (b : Module.Basis ι F E) (r : ℕ) :
    (Fin r → E) ≃ₗ[Fin r → F] (ι → (Fin r → F)) where
  toFun y k i := b.repr (y i) k
  invFun c i := ∑ k, c k i • b k
  map_add' y y' := by ext k i; simp
  map_smul' x y := by ext k i; simp
  left_inv y := by funext i; simp [b.sum_repr]
  right_inv c := by classical ext k i; simp [Finsupp.single_apply]

theorem norm_pi_apply (r : ℕ) (y : Fin r → E) (i : Fin r) :
    Algebra.norm (Fin r → F) y i = Algebra.norm F (y i) := by
  have h2 : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  classical
  let b := Module.finBasis F E
  let B := Module.Basis.ofEquivFun (piCoord b r)
  have hB : ∀ k, B k = fun _ => b k := by
    intro k; rw [Module.Basis.coe_ofEquivFun]; funext i; simp [piCoord, Pi.single_apply, ite_apply, ite_smul]
  have hBr : ∀ z k, B.repr z k = fun i => b.repr (z i) k := fun z k => by
    rw [Module.Basis.ofEquivFun_repr_apply]; rfl
  rw [Algebra.norm_eq_matrix_det B, Algebra.norm_eq_matrix_det b]
  rw [show (det (Algebra.leftMulMatrix B y)) i = Pi.evalRingHom (fun _ => F) i (det _) from rfl, RingHom.map_det]
  congr 1
  ext k l
  simp [RingHom.mapMatrix_apply, Algebra.leftMulMatrix_eq_repr_mul, hB, hBr]

theorem trace_pi_apply (r : ℕ) (z : Fin r → E) : Algebra.trace E (Fin r → E) z = ∑ i, z i := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun E (Fin r))]
  simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul]

end GlobalTheory.JR.SplitEt

namespace GlobalTheory.JR.SplitEt

variable (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]

theorem push_pi (r : ℕ) : Algebra.IsPushout F E (Fin r → F) (Fin r → E) := by
  refine ⟨?_⟩
  have h := IsBaseChange.finitePow (Fin r) (IsBaseChange.linearMap F E)
  have e : (IsScalarTower.toAlgHom F (Fin r → F) (Fin r → E)).toLinearMap = (Algebra.linearMap F E).compLeft (Fin r) :=
    LinearMap.ext fun _ => rfl
  rw [e]
  exact h

abbrev splitEt (r : ℕ) : Et F E :=
  haveI : LocallyCompactSpace F := Unram.lcF E
  letI : MeasurableSpace (Fin r → F) := borel (Fin r → F)
  haveI : BorelSpace (Fin r → F) := ⟨rfl⟩
  letI tL : TopologicalSpace (Fin r → E) := moduleTopology F (Fin r → E)
  letI : MeasurableSpace (Fin r → E) := borel (Fin r → E)
  haveI : BorelSpace (Fin r → E) := ⟨rfl⟩
  haveI : IsModuleTopology F (Fin r → E) := ⟨rfl⟩
  { K := Fin r → F
    L := Fin r → E
    push := push_pi F E r
    star_K := fun x => by funext i; exact Unram.star_fix (E := E) (x i)
    star_E := fun y => rfl }

end GlobalTheory.JR.SplitEt

theorem GlobalTheory.JR.exists_split_et : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), ∃ (A : Et F E) (e : A.K ≃ₐ[F] (Fin r → F)) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom 1 j ∧ ∀ y i, algebraMap F E (e (A.NL y) i) = j y i * star (j y i) := by
  intro F E _ _ _ _ _ r
  refine ⟨SplitEt.splitEt F E r, AlgEquiv.refl, LinearEquiv.refl E _, ?_, ?_⟩
  · intro y y'
    show star y ⬝ᵥ y' = Algebra.trace E (Fin r → E) (algebraMap (Fin r → F) (Fin r → E) 1 * star y * y')
    rw [map_one, one_mul, SplitEt.trace_pi_apply]
    simp [dotProduct]
  · intro y i
    show algebraMap F E (Algebra.norm (Fin r → F) y i) = y i * star (y i)
    rw [SplitEt.norm_pi_apply, SplitEt.algebraMap_norm_eq_mul_star]
end
end

section

noncomputable section
namespace GlobalTheory.DeltaInv
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam GlobalTheory.PsiShiftProof GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters

theorem root_eq {l : ℕ} [hl : Fact l.Prime] {z w : ℤ_[l]} (hz : z ^ (l - 1) = 1) (hw : w ^ (l - 1) = 1)
    (h : PadicInt.toZMod z = PadicInt.toZMod w) : z = w :=
  by
  have hn : 0 < l - 1 := Nat.sub_pos_of_lt hl.out.one_lt
  have key : (∑ i ∈ Finset.range (l - 1), z ^ i * w ^ (l - 1 - 1 - i)) * (z - w) = 0 := by
    rw [geom_sum₂_mul, hz, hw, sub_self]
  have hres : PadicInt.toZMod (∑ i ∈ Finset.range (l - 1), z ^ i * w ^ (l - 1 - 1 - i)) =
      ((l - 1 : ℕ) : ZMod l) * PadicInt.toZMod z ^ (l - 1 - 1) := by

    rw [map_sum, Finset.sum_congr rfl (g := fun _ => PadicInt.toZMod z ^ (l - 1 - 1))]
    · simp
    · intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [map_mul, map_pow, map_pow, ← h, ← pow_add]
      congr 1
      omega
  have hz0 : PadicInt.toZMod z ≠ 0 := by
    intro h0
    have h1 := congrArg PadicInt.toZMod hz
    rw [map_pow, h0, zero_pow hn.ne', map_one] at h1
    exact zero_ne_one h1
  have hl0 : ((l - 1 : ℕ) : ZMod l) ≠ 0 := by
    intro h0
    have := Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff (ZMod l) l _).mp h0)
    omega
  have hs : (∑ i ∈ Finset.range (l - 1), z ^ i * w ^ (l - 1 - 1 - i)) ≠ 0 := by
    intro h0
    apply mul_ne_zero hl0 (pow_ne_zero _ hz0)
    rw [← hres, h0, map_zero]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hs)

theorem exists_mul_pow {k : Type} [Field k] (c : k⸨X⸩) (t : k⟦X⟧) :
    ∃ (N : ℕ) (b : k⟦X⟧), (vv k * (t : k⸨X⸩)) ^ N * c = (b : k⸨X⸩) :=
  by
  refine ⟨(-c.order).toNat, PowerSeries.X ^ c.order.toNat * t ^ (-c.order).toNat * c.powerSeriesPart, ?_⟩
  have hc := LaurentSeries.single_order_mul_powerSeriesPart c
  have hN : ((-c.order).toNat : ℤ) + c.order = (c.order.toNat : ℤ) := by omega
  have hs : ∀ n : ℕ, (HahnSeries.single (1 : ℤ) (1 : k)) ^ n = HahnSeries.single (n : ℤ) 1 := by
    intro n
    rw [HahnSeries.single_pow]
    simp
  conv_lhs => arg 2; rw [← hc]
  rw [vv_eq_coe_X, map_mul, map_mul, map_pow, map_pow, HahnSeries.ofPowerSeries_X, mul_pow, hs, hs]
  calc (HahnSeries.single ((-c.order).toNat : ℤ) (1 : k) * (t : k⸨X⸩) ^ (-c.order).toNat) *
        (HahnSeries.single c.order 1 * (c.powerSeriesPart : k⸨X⸩))
      = (HahnSeries.single ((-c.order).toNat : ℤ) (1 : k) * HahnSeries.single c.order 1) *
          (t : k⸨X⸩) ^ (-c.order).toNat * (c.powerSeriesPart : k⸨X⸩) := by ring
    _ = _ := by rw [HahnSeries.single_mul_single, hN, one_mul]

theorem coeff_one_opp (k : Type) [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (z : ℤ_[l]) :
    PowerSeries.coeff 1 (onePlusPow k l z) = ZMod.castHom (dvd_refl l) k (PadicInt.toZMod z) :=
  by
  unfold onePlusPow
  rw [PowerSeries.coeff_map, PowerSeries.binomialSeries_coeff, Ring.choose_one_right, smul_eq_mul, mul_one]
  rfl

theorem main (l : ℕ) [hl : Fact l.Prime] (k : Type) [Field k] [CharP k l] (R : RingPG k l)
    (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (H : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι) :
    ∃ σ : {z : ℤ_[l] // z ^ (l - 1) = 1} → (k⸨X⸩ →+* k⸨X⸩),
      (∀ z (b : k⟦X⟧), σ z (b : k⸨X⸩) = ((GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l z.1 b : k⟦X⟧) : k⸨X⸩)) ∧
      Function.Injective σ ∧ ∀ c, (∀ z, σ z c = c) ↔ ∃ c₀, ι c₀ = c :=
  by
  have hne : l - 1 ≠ 0 := (Nat.sub_pos_of_lt hl.out.one_lt).ne'
  set σ : {z : ℤ_[l] // z ^ (l - 1) = 1} → (k⸨X⸩ →+* k⸨X⸩) :=
    fun z => GlobalTheory.PsiShiftProof.delPi k (Units.ofPowEqOne z.1 (l - 1) z.2 hne) with hσ
  have hσc : ∀ z (b : k⟦X⟧), σ z (b : k⸨X⸩) = ((GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l z.1 b : k⟦X⟧) : k⸨X⸩) := by
    intro z b
    rw [hσ, GlobalTheory.PsiShiftProof.delPi_coe]
    rfl
  have hinj : Function.Injective (fun b : k⟦X⟧ => (b : k⸨X⸩)) := HahnSeries.ofPowerSeries_injective
  have hfix : ∀ z (a : k⟦X⟧), σ z (ι (a : k⸨X⸩)) = ι (a : k⸨X⸩) := by
    intro z a
    obtain ⟨b, hb⟩ := H.2.1 a
    rw [hb, hσc, (H.2.2.1 b).2 ⟨a, hb⟩ z.1 z.2]
  have hιv : ∀ z, σ z (ι (vv k)) = ι (vv k) := by
    intro z
    rw [vv_eq_coe_X, hfix]
  have hv0 : ι (vv k) ≠ 0 := by
    exact (map_ne_zero ι).mpr (vv_ne_zero k)
  refine ⟨σ, hσc, ?_, ?_⟩
  · intro z w hzw
    have h1 := congrArg (fun f : k⸨X⸩ →+* k⸨X⸩ => f (1 + vv k)) hzw
    simp only [hσ, GlobalTheory.PsiShiftProof.del_one_add] at h1
    have h2 := congrArg (PowerSeries.coeff 1) (hinj h1)
    simp only [Units.val_ofPowEqOne, coeff_one_opp] at h2
    exact Subtype.ext (root_eq z.2 w.2 ((ZMod.castHom (dvd_refl l) k).injective h2))
  · intro c
    constructor
    · intro hc
      obtain ⟨u, hu⟩ := H.1
      obtain ⟨N, b, hb⟩ := exists_mul_pow c ((u : k⟦X⟧) * PowerSeries.X ^ (l - 2))
      have hv : vv k * (((u : k⟦X⟧) * PowerSeries.X ^ (l - 2) : k⟦X⟧) : k⸨X⸩) = ι (vv k) := by
        rw [hu, map_mul, map_pow, ← vv_eq_coe_X]
        have : l - 1 = (l - 2) + 1 := by have := hl.out.two_le; omega
        rw [this, pow_succ]
        ring
      rw [hv] at hb
      have hbinv : ∀ z : ℤ_[l], z ^ (l - 1) = 1 → GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l z b = b := by
        intro z hz
        apply hinj
        show ((GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l z b : k⟦X⟧) : k⸨X⸩) = (b : k⸨X⸩)
        have e := hσc ⟨z, hz⟩ b
        dsimp only at e
        rw [← e, ← hb, map_mul, map_pow, hc, hιv]
      obtain ⟨a, ha⟩ := (H.2.2.1 b).1 hbinv
      refine ⟨(a : k⸨X⸩) * (vv k ^ N)⁻¹, ?_⟩
      rw [map_mul, map_inv₀, map_pow, ha, ← hb]
      field_simp
    · rintro ⟨c₀, rfl⟩ z
      obtain ⟨N, b, hb⟩ := exists_mul_pow c₀ 1
      rw [map_one, mul_one] at hb
      have h1 := congrArg ι hb
      rw [map_mul, map_pow] at h1
      have h2 := congrArg (σ z) h1
      rw [map_mul, map_pow, hfix, ← h1, show σ z (ι (vv k)) = ι (vv k) from hιv z] at h2
      exact mul_left_cancel₀ (pow_ne_zero N hv0) h2

end GlobalTheory.DeltaInv
end
end

section

noncomputable section

namespace GlobalTheory.HeightsFromJumpsCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.IndefiniteRowSideFullHecke

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

end Generic


open TensorProduct in
theorem _root_.GlobalTheory.HeightsFromJumpsCompare.heightsFromJumps_iff (l : ℕ) [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) (AI : _root_.Formalism.BasicNotions.LocAinf l P)
    (H : _root_.Formalism.BasicNotions.LocHW l P) (F : _root_.Formalism.BasicNotions.LocFon l P AI H) (C : _root_.Formalism.BasicNotions.LocCmpT l P AI H F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing.HeightsFromJumps l P AI H F C ↔
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalRingStructure.HeightsFromJumps l P AI H F C :=
  Iff.rfl

end GlobalTheory.HeightsFromJumpsCompare
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

noncomputable section

namespace GlobalTheory.Per.FilLetUnram

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem act_ι (g : G) (d : V ⊗[Qp] B) :
    actVdR PD ρ g (ιV PD (LL := LL) (V := V) d) = ιV PD (LL := LL) (V := V) (actVB PD ρ g d) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp [actVdR, ιV, actVB, PD.ι_comm]

theorem mul_ι (c : K₀) (d : V ⊗[Qp] B) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (algebraMap K₀ K c)
        (ιV PD (LL := LL) (V := V) d) =
      ιV PD (LL := LL) (V := V) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c d) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp [mulVdR, ιV, mulVB, ← IsScalarTower.algebraMap_apply]

theorem ι_mem_DdRE (hs : Function.Surjective (algebraMap K₀ K)) (τ : K →ₐ[Qp] LL)
    {d : V ⊗[Qp] B} (hd : d ∈ DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))) :
    ιV PD (LL := LL) (V := V) d ∈ DdRE PD ρ τ := by
  obtain ⟨h1, h2⟩ := hd
  simp only [Dcris, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero] at h1 h2
  constructor
  · simp only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro g
    rw [act_ι, h1 g]
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero]
    intro c
    obtain ⟨c₀, rfl⟩ := hs c
    rw [mul_ι, h2 c₀, map_smul]
    rfl

theorem iSupIndep_DdRE : iSupIndep fun τ : K →ₐ[Qp] LL => DdRE PD ρ τ := by
  have h := iSupIndep.iInf
    (fun (c : K) (a : LL) => Module.End.eigenspace
      (mulVdR (Qp := Qp) (K := K) (BdR := BdR) (V := V) (LL := LL) c) a)
    (fun c => Module.End.eigenspaces_iSupIndep _)
  have h' := h.comp (f := fun τ : K →ₐ[Qp] LL => (τ : K → LL)) DFunLike.coe_injective
  refine h'.mono fun τ x hx => ?_
  have h2 := hx.2
  simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero] at h2
  simp only [Function.comp, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  exact h2

end Abstract

theorem toDR_FilLet : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (τ : K →ₐ[Qp] LL) (a : ℤ), Function.Surjective (algebraMap K₀ K) → τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = W.emb i → FildR PD T.ρ τ a = (FilCris PD T.ρ a ⊓ DcrisL PD T.ρ (W.emb i)).map (ιV PD (LL := LL) (V := T.V)) → GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.toDR (PD := PD) T (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.FilLet W T i τ a) = FildR PD T.ρ τ a := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W T i τ a hs hτ hF
  apply le_antisymm
  · rintro _ ⟨x, ⟨hx, hx'⟩, rfl⟩
    have hxD : ιV PD (LL := LL) (V := T.V) x ∈ DdRE PD T.ρ τ :=
      ι_mem_DdRE PD T.ρ hs τ (by rw [hτ]; exact hx)
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (Submodule.mem_comap.1 hx')
    have hzD : z ∈ DdRE PD T.ρ τ := by
      have : z = ιV PD (LL := LL) (V := T.V) x - y := by rw [← hyz]; abel
      rw [this]
      exact Submodule.sub_mem _ hxD hy.1
    have hz0 : z = 0 := (Submodule.disjoint_def.1 (iSupIndep_DdRE PD T.ρ τ)) z hzD hz
    rw [← hyz, hz0, add_zero]
    exact hy
  · intro y hy
    have hy' := hy
    rw [hF] at hy'
    obtain ⟨x, hx, rfl⟩ := hy'
    exact ⟨x, ⟨hx.2, Submodule.mem_comap.2 (Submodule.mem_sup_left hy)⟩, rfl⟩

end GlobalTheory.Per.FilLetUnram
end
end

section

noncomputable section

namespace GlobalTheory.AdmLoc.CycWitness

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct

section Line

variable {G Qp LL R : Type} [Group G] [Field Qp] [Field LL] [Algebra Qp LL] [CommRing R] [Algebra Qp R]

end Line

section Per

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

variable (hK : Function.Surjective (algebraMap Qp K)) (a : ℕ) (θ : G →* LLˣ)
  (hθ : ∀ g, (θ g : LL) = algebraMap Qp LL (((PD.χ g)⁻¹ ^ a : Qpˣ) : Qp))


include hK hθ

end Per

variable {l : ℕ} [Fact l.Prime]

def cycO (P : LocPrime l) (K LL : FinExt l) : ↥(GK K) →* (↥(OL LL))ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => ⟨_, GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.cyc_mem P K LL g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp) }

theorem cycO_val (P : LocPrime l) (K LL : FinExt l) (g : ↥(GK K)) :
    algebraMap ↥(OL LL) ↥LL.1 (cycO P K LL g) = algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g) := rfl

end GlobalTheory.AdmLoc.CycWitness
end
end

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.exists_fixing_actsAsFrobeniusPowerResidue : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (_h : IsPlaceOver A w)
    (K : IntermediateField E Ω) [FiniteDimensional E K], ∀ d ∈ Dec (F := E) A, ∀ j : ℕ,
      (∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (d z - z ^ (normV w ^ j)) < 1) →
      ∃ ρ : G E Ω, (∀ z ∈ K, ρ z = z) ∧ ActsAs A (normV w) (d * ρ) j 0 := by
  first | exact @GlobalTheory.GaloisLift.exists_fixing_actsAs | exact GlobalTheory.GaloisLift.exists_fixing_actsAs | (intros; apply GlobalTheory.GaloisLift.exists_fixing_actsAs <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.exists_rootOfUnity_fixed_dvd_weilGroupDegree : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (k : ℕ), 0 < k → ∃ ζ : Ω, ∀ σ : Weil h, (σ : G E Ω) ζ = ζ → (k : ℤ) ∣ deg σ := by
  first | exact @GlobalTheory.exists_fixed_dvd_deg | exact GlobalTheory.exists_fixed_dvd_deg | (intros; apply GlobalTheory.exists_fixed_dvd_deg <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.exists_finset_fixing_le_finiteIndex_weilSubgroup : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ (σ : G E Ω) (s : Finset Ω), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ s, (σ ^ m) x = x) → (∀ k : ℕ, 0 < k → ∃ ζ : Ω, ∀ σ : Weil h, (σ : G E Ω) ζ = ζ → (k : ℤ) ∣ deg σ) → (∀ M : Subgroup (Ine (F := E) A), IsOpen (M : Set (Ine (F := E) A)) → ∃ s : Finset Ω, ∀ σ : Ine (F := E) A, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ M) → ∀ H : Subgroup (Weil h), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∃ s : Finset Ω, ∀ σ : Weil h, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ H := by
  first | exact @GlobalTheory.WeilOpenFin.exists_finset_fix_le | exact GlobalTheory.WeilOpenFin.exists_finset_fix_le | (intros; apply GlobalTheory.WeilOpenFin.exists_finset_fix_le <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

theorem _root_.GlobalTheory.T.exists_smoothDual_ne_zero_at_vector : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → IsSmooth ρ → ∀ v : V, v ≠ 0 → ∃ l : Module.Dual ℂ V, l ∈ smoothPart ρ.dual ∧ l v ≠ 0 := by
  first | exact @GlobalTheory.SmoothForm.exists_smooth_form_ne_zero | exact GlobalTheory.SmoothForm.exists_smooth_form_ne_zero | (intros; apply GlobalTheory.SmoothForm.exists_smooth_form_ne_zero <;> assumption)
end
