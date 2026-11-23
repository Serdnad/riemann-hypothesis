module

public import Formalism.AlgebraicWeights.InertDatumExists
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.AlgebraicWeights.IsAlgWeight
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle397
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle110
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle111
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle121
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle399
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle128
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle048
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertSph

def Gv (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Subgroup (GAf L n) where
  carrier := {x | TrivOutside {v} x}
  mul_mem' := fun hx hy => GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hy
  one_mem' := by
    intro u _
    exact Matrix.map_one _ (map_zero _) (map_one _)
  inv_mem' := fun hx => GlobalTheory.SatInd.CosetFin.trivOutside_inv hx

def Kv (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Subgroup (GAf L n) :=
  Umax L n ⊓ Gv L n v

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_one (T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) :
    TrivOutside T (1 : GAf L n) := by
  intro u _
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem commute_of_trivOutside (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x y : GAf L n)
    (hx : TrivOutside {v} x) (hy : TrivOutside {v}ᶜ y) : Commute x y := by
  show x * y = y * x
  apply Subtype.ext; apply Units.ext
  change (((x * y : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
    (((y * x : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))
  apply GlobalTheory.SplitAdelic.mat_ext
  intro u
  rw [GlobalTheory.SplitAdelic.mul_coe, GlobalTheory.SplitAdelic.mul_coe, Matrix.map_mul, Matrix.map_mul]
  obtain rfl | hu := eq_or_ne u v
  · rw [hy _ (by simp), mul_one, one_mul]
  · rw [hx u hu, mul_one, one_mul]

theorem heckeFunI_rt {W : Type} [AddCommGroup W] [Module ℂ W] (U : Subgroup (GAf L n))
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}
    (Dv : InertDatum L n v w) (h : Formalism.UG.GU Dv.σw n → ℂ) (φ : GAf L n → W) (b : GAf L n)
    (hb : TrivOutside {v}ᶜ b) :
    heckeFunI L n U Dv h (NG.rt L n b φ) = NG.rt L n b (heckeFunI L n U Dv h φ) := by
  funext g
  show heckeFunI L n U Dv h (NG.rt L n b φ) g = heckeFunI L n U Dv h φ (g * b)
  unfold heckeFunI
  refine finsum_congr fun c => ?_
  split_ifs with hc
  · show _ • φ (g * hc.choose * b) = _ • φ (g * b * hc.choose)
    rw [mul_assoc, mul_assoc, (commute_of_trivOutside v _ _ hc.choose_spec.2 hb).eq]
  · rfl

end GlobalTheory.InertSph
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

open TensorProduct Formalism.UG

namespace GlobalTheory.OneAct

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

theorem compAt_conjAL (z : AL L) :
    compAt L v (conjAL L z) = Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
      (v.adicCompletion (maximalRealSubfield L)) (compAt L v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem compAt_mem_tensInt {z : AL L} (hz : z ∈ ALint L) :
    compAt L v z ∈ tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) := by
  have key : ALint L ≤ (tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v)).comap (compAt L v) := by
    rw [ALint, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · apply Subring.subset_closure
      left
      exact ⟨⟨(y : L), y, rfl⟩, by rw [GlobalTheory.InertUmax.compAt_tmul]; rfl⟩
    · apply Subring.subset_closure
      right
      exact ⟨⟨a v, ha v⟩, by rw [GlobalTheory.InertUmax.compAt_tmul]⟩
  exact key hz

theorem loc_mem_GU (Dv : InertDatum L n v w) (x : GAf L n) : Dv.loc x ∈ GU Dv.σw n := by
  set φ : AL L →+* w.adicCompletion L := (Dv.e : _ →+* _).comp (compAt L v) with hφdef
  have hφ : ∀ z, φ (conjAL L z) = Dv.σw (φ z) := fun z => by
    simp only [φ, RingHom.comp_apply, compAt_conjAL]
    exact Dv.comm _
  have hX : ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      conjT (conjAL L) ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := x.2
  have hX' := mul_eq_one_comm.mp hX
  set A : Matrix (Fin n) (Fin n) (w.adicCompletion L) :=
    ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map φ with hAdef
  have hA : cT Dv.σw A * A = 1 := by
    have : cT Dv.σw A = (conjT (conjAL L) ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map φ := by
      ext i j; simp [cT, conjT, A, hφ]
    rw [this, ← Matrix.map_mul, hX', Matrix.map_one _ (map_zero _) (map_one _)]
  have hloc : ((Dv.loc x : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) =
      ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) * A *
        (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) := rfl
  have hPP : cT Dv.σw ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = 1 := by
    rw [← cT_mul, Units.mul_inv, cT_one]
  have hPP' : (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = 1 :=
    Units.mul_inv _
  show cT Dv.σw ((Dv.loc x : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      antiJ (w.adicCompletion L) n *
      ((Dv.loc x : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) =
      antiJ (w.adicCompletion L) n
  rw [← Dv.Panti, hloc, cT_mul, cT_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (cT Dv.σw _) (cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L))), hPP,
    Matrix.one_mul, ← Matrix.mul_assoc (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)), hPP',
    Matrix.one_mul, ← Matrix.mul_assoc (cT Dv.σw A) A, hA, Matrix.one_mul]

theorem mem_range_of_int {K : Type} [Field K] (S : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ S)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ S) :
    g ∈ (Formalism.UG.bc (n := Fin n) S.subtype).range := by
  let M : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, h1 i j⟩
  let N : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, h2 i j⟩
  have hM : M.map S.subtype = (g : Matrix (Fin n) (Fin n) K) := by ext i j; rfl
  have hN : N.map S.subtype = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by ext i j; rfl
  have inj : Function.Injective (fun A : Matrix (Fin n) (Fin n) S => A.map S.subtype) := by
    intro A B h; ext i j; exact congrFun (congrFun h i) j
  have hMN : M * N = 1 := inj (by
    simp only [Matrix.map_mul, hM, hN, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
  have hNM : N * M = 1 := inj (by
    simp only [Matrix.map_mul, hM, hN, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
  refine ⟨⟨M, N, hMN, hNM⟩, Units.ext ?_⟩
  exact hM

theorem loc_entries_int (Dv : InertDatum L n v w) {x : GAf L n} (hx : x ∈ Umax L n) (i j : Fin n) :
    ((Dv.loc x : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈
      intL (w.adicCompletion L) := by
  have hP := GlobalTheory.InertUmax.entries_mem_of_range _ _ Dv.Pint
  have hP' := GlobalTheory.InertUmax.entries_mem_of_range _ _ (inv_mem Dv.Pint)
  have hA : ∀ k l, Dv.e (compAt L v (((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) k l)) ∈
      intL (w.adicCompletion L) := fun k l => (Dv.integ _).1 (compAt_mem_tensInt (hx k l))
  simp only [InertDatum.loc, Units.val_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _
    (Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hP' i l) (hA l k)) (hP k j)

theorem loc_mem_KU (Dv : InertDatum L n v w) {x : GAf L n} (hx : x ∈ Umax L n) :
    (⟨Dv.loc x, loc_mem_GU Dv x⟩ : GU Dv.σw n) ∈ KU Dv.σw n := by
  refine ⟨loc_mem_GU Dv x, mem_range_of_int _ _ (loc_entries_int Dv hx) ?_⟩
  have : (Dv.loc x)⁻¹ = Dv.loc x⁻¹ := by
    rw [show Dv.loc x⁻¹ = GlobalTheory.SatInd.CosetFin.locHom Dv x⁻¹ from rfl, map_inv]; rfl
  show ∀ i j, (((Dv.loc x)⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ _
  rw [this]
  exact loc_entries_int Dv (inv_mem hx)

end GlobalTheory.OneAct

theorem GlobalTheory.OneAct.heckeFunI_unit : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (dosetInd ℂ (KU Dv.σw n) 1) f = f := by
  intro L _ _ _ n v w Dv U hU W _ _ f hf
  funext g
  unfold heckeFunI
  have hone : TrivOutside {v} (1 : GAf L n) := by
    intro u _
    show ((1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L u) = 1
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hdK : ∀ y : GU Dv.σw n, y ∈ (DoubleCoset.doubleCoset (1 : GU Dv.σw n) (KU Dv.σw n : Set (GU Dv.σw n))
      (KU Dv.σw n : Set (GU Dv.σw n))) ↔ y ∈ KU Dv.σw n := by
    intro y
    rw [DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      simpa using (KU Dv.σw n).mul_mem ha hb
    · intro hy
      exact ⟨y, hy, 1, (KU Dv.σw n).one_mem, by simp⟩
  rw [finsum_eq_single _ ((1 : GAf L n) : GAf L n ⧸ U)]
  · have hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = ((1 : GAf L n) : GAf L n ⧸ U) ∧ TrivOutside {v} x :=
      ⟨1, rfl, hone⟩
    rw [dite_eq_left hc]
    obtain ⟨hx1, hx2⟩ := hc.choose_spec
    have hxU : hc.choose ∈ U := by
      have := QuotientGroup.eq.1 hx1
      simpa using this
    have hxM : hc.choose ∈ Umax L n := (hU _ hx2).1 hxU
    have hval : Dv.hval (dosetInd ℂ (KU Dv.σw n) 1) (Dv.loc hc.choose) = 1 := by
      unfold InertDatum.hval
      rw [dite_eq_left (GlobalTheory.OneAct.loc_mem_GU Dv _)]
      unfold dosetInd
      rw [Set.indicator_of_mem ((hdK _).2 (GlobalTheory.OneAct.loc_mem_KU Dv hxM))]
      rfl
    rw [hval, one_smul]
    exact congrFun (hf _ hxU) g
  · intro c hc1
    split_ifs with hc
    · obtain ⟨hx1, hx2⟩ := hc.choose_spec
      have hval : Dv.hval (dosetInd ℂ (KU Dv.σw n) 1) (Dv.loc hc.choose) = 0 := by
        unfold InertDatum.hval
        split_ifs with hm
        · unfold dosetInd
          apply Set.indicator_of_notMem
          intro hmem
          have hK := (hdK _).1 hmem
          have hxM : hc.choose ∈ Umax L n :=
            GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv _ hx2 (fun i j => GlobalTheory.SatInd.CosetFin.entries_int hK i j)
          apply hc1
          rw [← hx1]
          exact QuotientGroup.eq.2 (by simpa using (hU _ hx2).2 hxM)
        · rfl
      rw [hval, zero_smul]
    · rfl
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

namespace GlobalTheory.HeckeStab

theorem heckeFunI_mem : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (S : Submodule ℂ (GAf L n → W)), (∀ g, ∀ f ∈ S, NG.rt L n g f ∈ S) → ∀ h ∈ Hecke ℂ (KU Dv.σw n), ∀ f ∈ S, heckeFunI L n U Dv h f ∈ S := by
  classical
  intro L _ _ _ n v w Dv U hUv W _ _ S hS h hh f hf
  have hfin : Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧
      Dv.hval h (Dv.loc x) ≠ 0} :=
    GlobalTheory.T.finite_inertHecke_support_cosets L n v w Dv (GlobalTheory.T.unitary_doubleCoset_finite_left_cosets Dv.ϖ Dv.σw _ n Dv.unram) (GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv) U hUv h hh
  have key : heckeFunI L n U Dv h f = ∑ c ∈ hfin.toFinset,
      (if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
        Dv.hval h (Dv.loc hc.choose) else 0) •
      NG.rt L n (if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
        hc.choose else 1) f := by
    funext g
    unfold heckeFunI
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
    · rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
      · simp only [dif_pos hc]
        rfl
      · simp only [dif_neg hc, zero_smul]
        rfl
    · intro c hc0
      rw [Function.mem_support] at hc0
      by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
      · rw [dif_pos hc] at hc0
        rw [Set.Finite.coe_toFinset]
        refine ⟨hc.choose, hc.choose_spec.1, hc.choose_spec.2, fun h0 => hc0 ?_⟩
        rw [h0, zero_smul]
      · exact absurd (dif_neg hc) hc0
  rw [key]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hS _ f hf)

end GlobalTheory.HeckeStab
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TSetDoubleCoset

theorem trivOutside_mul {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GA L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro v hv
  have e : ((x * y : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) =
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [e, Matrix.map_mul, hx v hv, hy v hv, Matrix.mul_one]

theorem mem_GLint_of_entries {K : Type} [Field K] {n : ℕ} (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ a b, g.val a b ∈ O) (h2 : ∀ a b, (g⁻¹).val a b ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem loc_mem_GLint {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L)
    {k : GA L n} (hk : k ∈ Umax L n) :
    s.loc n k ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
  apply mem_GLint_of_entries
  · intro a b
    exact GlobalTheory.splitPlace_proj_mem_integers_of_integral s (hk a b)
  · intro a b
    rw [← map_inv]
    exact GlobalTheory.splitPlace_proj_mem_integers_of_integral s ((Umax L n).inv_mem hk a b)

theorem mem_tSet_iff : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (sp : SplitPlace L) (ϖ : (sp.v).adicCompletion (maximalRealSubfield L)) (k : ℕ), ∀ x₀ ∈ Formalism.AUTREP.tSet L n sp ϖ k, ∀ κ, κ ∈ Formalism.AUTREP.tSet L n sp ϖ k ↔ ∃ k₁, (k₁ ∈ Umax L n ∧ TrivOutside {sp.v} k₁) ∧ ∃ k₂, (k₂ ∈ Umax L n ∧ TrivOutside {sp.v} k₂) ∧ κ = k₁ * x₀ * k₂ := by
  intro L _ _ _ n sp ϖ k x₀ hx₀ κ
  obtain ⟨hx₀t, a₀, ha₀, b₀, hb₀, hx₀e⟩ := hx₀
  constructor
  · rintro ⟨hκt, a, ha, b, hb, hκe⟩
    obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc L n sp
    have hg : a * a₀⁻¹ ∈ Formalism.UG.GLint (Fin n) (sp.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring :=
      mul_mem ha (inv_mem ha₀)
    have hg' : b₀⁻¹ * b ∈ Formalism.UG.GLint (Fin n) (sp.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring :=
      mul_mem (inv_mem hb₀) hb
    refine ⟨e (a * a₀⁻¹), ⟨GlobalTheory.SplitHeckeComm.mem_Umax_of_loc sp _ (he1 _) (by rw [he2]; exact hg), he1 _⟩,
      e (b₀⁻¹ * b), ⟨GlobalTheory.SplitHeckeComm.mem_Umax_of_loc sp _ (he1 _) (by rw [he2]; exact hg'), he1 _⟩, ?_⟩
    apply GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq L n sp
    · exact hκt
    · exact trivOutside_mul (trivOutside_mul (he1 _) hx₀t) (he1 _)
    · rw [map_mul, map_mul, he2, he2]
      apply Units.ext
      simp only [Units.val_mul]
      rw [hκe, hx₀e]
      simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv_cancel_left]
  · rintro ⟨k₁, ⟨hk₁, hk₁t⟩, k₂, ⟨hk₂, hk₂t⟩, rfl⟩
    refine ⟨trivOutside_mul (trivOutside_mul hk₁t hx₀t) hk₂t, sp.loc n k₁ * a₀,
      mul_mem (loc_mem_GLint sp hk₁) ha₀, b₀ * sp.loc n k₂, mul_mem hb₀ (loc_mem_GLint sp hk₂), ?_⟩
    rw [map_mul, map_mul]
    simp only [Units.val_mul]
    rw [hx₀e]
    simp only [Matrix.mul_assoc]

end GlobalTheory.TSetDoubleCoset
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.RealUnifSplit

theorem le_exp_neg_one_of_lt {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, neg_add_cancel,
    WithZero.exp_zero]
  exact h

theorem val_sq_le {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L)
    (z : 𝓞 L) (hz : z ∈ s.w.asIdeal ^ 2) :
    Valued.v (s.i (z : L)) ≤ WithZero.exp (-2) := by
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz ?_ ?_
  · intro a ha b hb
    have ha' : Valued.v (s.i (a : L)) < 1 := (s.split_mem_ideal a).1 ha
    have hb' : Valued.v (s.i (b : L)) < 1 := (s.split_mem_ideal b).1 hb
    show Valued.v (s.i ((a : L) * (b : L))) ≤ _
    rw [map_mul, map_mul]
    calc Valued.v (s.i (a : L)) * Valued.v (s.i (b : L))
        ≤ WithZero.exp (-1) * WithZero.exp (-1) :=
          mul_le_mul' (le_exp_neg_one_of_lt ha') (le_exp_neg_one_of_lt hb')
      _ = WithZero.exp (-2) := by rw [← WithZero.exp_add]; norm_num
  · intro a b ha hb
    show Valued.v (s.i ((a : L) + (b : L))) ≤ _
    rw [map_add (f := _)]
    exact le_trans (Valuation.map_add _ _ _) (max_le ha hb)

end GlobalTheory.RealUnifSplit

theorem GlobalTheory.realUnif_split {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    ∃ y : 𝓞 L, y ∈ s.w.asIdeal ∧ y ∉ s.w.asIdeal ^ 2 ∧ Formalism.AUTREP.IsUnif L s.v (s.i (y : L)) := by
  obtain ⟨π, hπ⟩ := s.v.intValuation_exists_uniformizer
  have hv : Valued.v (s.i ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) π : 𝓞 L) : L)) =
      WithZero.exp (-1) := by
    rw [s.split_val_alg, HeightOneSpectrum.valuation_of_algebraMap, hπ]
  refine ⟨algebraMap _ (𝓞 L) π, ?_, ?_, hv⟩
  · refine (s.split_mem_ideal _).2 ?_
    rw [hv]; rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  · intro h
    have h2 := GlobalTheory.RealUnifSplit.val_sq_le s _ h
    rw [hv] at h2
    have := WithZero.exp_le_exp.1 h2
    omega
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GeoUnder

theorem exists_under_in_qPl : ∀ (D : D7) (χ : HChar D.host.E) (w : PlE D.host), (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → ¬ χ.UnrAt w → ∃ v, NG.OverPl w v ∧ v ∈ qPl D χ := by
  intro D χ w hg hχ
  have hne : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    have hint : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (hint.tower_top)
  let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) :=
    { asIdeal := w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := hne }
  refine ⟨v, rfl, ?_, w, rfl, hχ⟩
  rintro ⟨w', hw', k, hk⟩
  apply hg k
  have h1 : ((D.host.g k : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal := by
    rw [← hw']
    show algebraMap _ _ _ ∈ w'.asIdeal
    rw [map_natCast]; exact hk
  show ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
  have h2 := h1
  change algebraMap _ _ _ ∈ w.asIdeal at h2
  rwa [map_natCast] at h2

end GlobalTheory.GeoUnder
end
