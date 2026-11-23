module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle151
public import GroundTheory.GlobalFields.TateThesis.HeckeTheoremFE
public import GroundTheory.GlobalFields.IdeleGroups.LocalConditionIndex
import GroundTheory.GlobalFields.TateThesis.Bundle008
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle055
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle072
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt

@[expose] public section

section

set_option maxSynthPendingDepth 1

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors NNReal

namespace GlobalTheory.CompanionTheory.PartialZeta

noncomputable section

variable {F : Type} [Field F] [NumberField F] {χ : HeckeCharacter F}

theorem conductor_eq_top (h : standardOpenSubgroup F ≤ χ.toIdele.ker) : χ.conductor = ⊤ := by
  apply GlobalTheory.CompanionTheory.PartialZeta.conductor_eq_top_of_standardOpen <;> assumption

theorem infiniteWeight_eq_zero (h : standardOpenSubgroup F ≤ χ.toIdele.ker)
    (w : InfinitePlace F) : χ.infiniteWeight w = 0 := by
  have hp : χ.infiniteParams w = (0, 0) := by
    refine (χ.infiniteParams_unique w (p := (0, 0)) (fun _ ↦ ⟨le_rfl, by norm_num⟩) fun a ↦ ?_).symm
    have h1 : χ.infiniteComponent w a = 1 := h (infiniteEmbedding_mem_standardOpenSubgroup w a)
    simp [h1]
  rw [HeckeCharacter.infiniteWeight, hp]

theorem idealUnit_eq_one {I : Ideal (𝓞 F)} (hI : I = ⊤) (h : I ≠ ⊥) : idealUnit I h = 1 := by
  subst hI
  ext
  simp [idealUnit]

theorem finiteFourier_eq (h : χ.conductor = ⊤) {δ : (FiniteAdeleRing (𝓞 F) F)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit) :
    finiteFourier F χ.finiteTestFun ((δ⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) =
      (((NNReal.sqrt ‖discr F‖₊)⁻¹ : ℝ≥0) : ℂ) := by
  have hE : IsEmpty χ.conductorPrimes := ⟨fun v ↦ by
    have hv := χ.mem_conductorPrimes.1 v.2
    rw [h, Ideal.dvd_iff_le, top_le_iff] at hv
    exact v.1.isPrime.ne_top hv⟩
  rw [χ.finiteFourier_finiteTestFun_inv_eq hδ, Finset.univ_eq_empty, Finset.prod_empty, mul_one]

theorem discr_sqrt_mul (h : χ.conductor = ⊤) :
    (((NNReal.sqrt ‖discr F‖₊)⁻¹ : ℝ≥0) : ℂ) * (χ.discrNormConductor : ℂ) ^ (1 / 2 : ℂ) = 1 := by
  have hd : χ.discrNormConductor = |(discr F : ℝ)| := by
    rw [HeckeCharacter.discrNormConductor, h, Ideal.absNorm_top]
    simp
  have hpos : 0 < |(discr F : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero F))
  have hs : ((NNReal.sqrt ‖discr F‖₊ : ℝ≥0) : ℝ) = Real.sqrt |(discr F : ℝ)| := by
    rw [Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
  have hcp : ((|(discr F : ℝ)| : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hpos.le]
    norm_num
  have hne : ((Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hpos).ne'
  have hinv : (((NNReal.sqrt ‖discr F‖₊)⁻¹ : ℝ≥0) : ℂ) = ((Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)⁻¹ := by
    rw [← hs]
    simp
  rw [hd, hcp, hinv, inv_mul_cancel₀ hne]

theorem rootNumber_eq_coeff_different (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F)
    (h : standardOpenSubgroup F ≤ χ.toIdele.ker) :
    χ.rootNumber = χ.coeff (differentIdeal ℤ (𝓞 F)) := by
  have hc := conductor_eq_top h
  have hδ := χ.toFractionalIdeal_conductorDifferentIdele
  have hcop : IsCoprime (differentIdeal ℤ (𝓞 F)) χ.conductor := by
    rw [hc, ← Ideal.one_eq_top]
    exact isCoprime_one_right
  have hmem : ofFinite χ.conductorDifferentIdele ∈ primeToLevel χ.conductor := by
    refine mem_primeToLevel.2 ⟨toInfinite_ofFinite _, fun v hv ↦ ?_⟩
    rw [hc, Ideal.dvd_iff_le, top_le_iff] at hv
    exact absurd hv v.isPrime.ne_top
  have hval : χ.coeff (differentIdeal ℤ (𝓞 F)) =
      (χ.toIdele (ofFinite χ.conductorDifferentIdele) : ℂ) := by
    rw [χ.coeff_of_mem ⟨differentIdeal_ne_bot, hcop⟩]
    congr 1
    refine χ.idealCharacter_apply hmem _ ?_
    rw [hδ, idealUnit_eq_one hc, one_mul]
    rfl
  rw [hval, HeckeCharacter.rootNumber, HeckeCharacter.fourierConst, finiteFourier_eq hc hδ]
  simp only [infiniteWeight_eq_zero h, Int.natAbs_zero, pow_zero, Finset.prod_const_one, one_mul]
  linear_combination (χ.toIdele (ofFinite χ.conductorDifferentIdele) : ℂ) * discr_sqrt_mul hc

end

end GlobalTheory.CompanionTheory.PartialZeta
end

section

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RealMult

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK (Pos)

variable {n : ℕ}

abbrev Lt (n : ℕ) : Type := Bool × Fin n × Fin n

abbrev Ix (n : ℕ) : Type := Bool × Pos n

abbrev Cr (n : ℕ) (V : Type) : Type := Finset (Ix n) → V

def keyR (i : Ix n) : ℕ := (if i.1 then n * n else 0) + CompanionTheory.D.LK.key i.2

def sgR (i : Ix n) (A : Finset (Ix n)) : ℂ := (-1) ^ (A.filter fun j => keyR j < keyR i).card

def cp (p q r : Pos n) : ℂ :=
  (if p.1.2 = q.1.1 ∧ r.1 = (p.1.1, q.1.2) then 1 else 0) - (if q.1.2 = p.1.1 ∧ r.1 = (q.1.1, p.1.2) then 1 else 0)

section Chains

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def annR (i : Ix n) : Module.End ℂ (Cr n V) where
  toFun x := fun A => if i ∈ A then 0 else sgR i A • x (insert i A)
  map_add' x y := by funext A; by_cases h : i ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : i ∈ A <;> simp [h, smul_comm c]

def creR (i : Ix n) : Module.End ℂ (Cr n V) where
  toFun x := fun A => if i ∈ A then sgR i A • x (A.erase i) else 0
  map_add' x y := by funext A; by_cases h : i ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : i ∈ A <;> simp [h, smul_comm c]

def liftR (n : ℕ) {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') : Cr n V →ₗ[ℂ] Cr n V' :=
  T.compLeft (Finset (Ix n))

def rl (E1 E2 : Fin n → Fin n → Module.End ℂ V) (i : Ix n) : Module.End ℂ V :=
  if i.1 then E1 i.2.1.1 i.2.1.2 + E2 i.2.1.1 i.2.1.2 else E2 i.2.1.1 i.2.1.2

def torV (E1 E2 : Fin n → Fin n → Module.End ℂ V) : FreeAlgebra ℂ (Bool × Fin n) →ₐ[ℂ] Module.End ℂ V :=
  FreeAlgebra.lift ℂ fun p => if p.1 then E1 p.2 p.2 else E2 p.2 p.2

def ev2 (E1 E2 : Fin n → Fin n → Module.End ℂ V) : FreeAlgebra ℂ (Lt n) →ₐ[ℂ] Module.End ℂ V :=
  FreeAlgebra.lift ℂ fun p => if p.1 then E1 p.2.1 p.2.2 else E2 p.2.1 p.2.2

structure Pair2 (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Prop where
  gl1 : GlRel E1
  gl2 : GlRel E2
  comm : ∀ a b c d, E1 a b * E2 c d = E2 c d * E1 a b

end Chains

def Inv2 (a : FreeAlgebra ℂ (Lt n)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), Pair2 E1 E2 →
    ∀ c d, Commute (E1 c d + E2 c d) (ev2 E1 E2 a)

def LiftInv : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    Pair2 E1 E2 → (∀ a b (x y : V), inner ℂ (kF E1 E2 a b x) y = inner ℂ x (kF E1 E2 b a y)) →
    (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF E1 E2 a b w ∈ S) →
    ∀ (μ : Fin n → ℝ) (v w : V), v ≠ 0 → v ∈ hwSp E1 E2 μ → w ∈ hwSp E1 E2 μ → (∃ x ∈ alg E1 E2, x v = w) →
      ∃ a : FreeAlgebra ℂ (Lt n), Inv2 a ∧ ev2 E1 E2 a v = w

end GlobalTheory.CompanionTheory.RealMult
end
end

section

noncomputable section

open Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.PairMult

open Formalism.REAL (GlRel qdet)
open CompanionTheory.D.LK (Pos)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ}

abbrev Lt (n : ℕ) : Type := Bool × Pos n

abbrev Cq (n : ℕ) (V : Type) : Type := Finset (Lt n) → V

def keyL (l : Lt n) : ℕ := (if l.1 then 0 else (n + 1) * (n + 1)) + CompanionTheory.D.LK.key l.2

def sgL (l : Lt n) (A : Finset (Lt n)) : ℂ := (-1) ^ (A.filter fun j => keyL j < keyL l).card

section Chains

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def annq (l : Lt n) : Module.End ℂ (Cq n V) where
  toFun x := fun A => if l ∈ A then 0 else sgL l A • x (insert l A)
  map_add' x y := by funext A; by_cases h : l ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : l ∈ A <;> simp [h, smul_comm c]

def creq (l : Lt n) : Module.End ℂ (Cq n V) where
  toFun x := fun A => if l ∈ A then sgL l A • x (A.erase l) else 0
  map_add' x y := by funext A; by_cases h : l ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : l ∈ A <;> simp [h, smul_comm c]

def liftq (n : ℕ) {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') : Cq n V →ₗ[ℂ] Cq n V' :=
  T.compLeft (Finset (Lt n))

def Ts (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (p q : Fin n) : Module.End ℂ V :=
  if s then E1 p q + E2 p q else E1 p q - E2 p q

def Tl (E1 E2 : Fin n → Fin n → Module.End ℂ V) (l : Lt n) : Module.End ℂ V := Ts E1 E2 l.1 l.2.1.1 l.2.1.2

def bdq (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Cq n V) :=
  (∑ l : Lt n, (liftq n (Tl E1 E2 l) : Module.End ℂ (Cq n V)) * annq l) +
    ∑ s : Bool, ∑ t : Bool, ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
      if i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then creq ((s == t), k) * annq (t, j) * annq (s, i) else 0

def SuppQ (P : Lt n → Prop) (y : Cq n V) : Prop := ∀ A, y A ≠ 0 → ∀ l ∈ A, P l

def DegQ (j : ℕ) (y : Cq n V) : Prop := ∀ A, y A ≠ 0 → A.card = j

def adLq (s : Bool) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  ∑ t : Bool, ∑ i : Pos n, ∑ k : Pos n, CompanionTheory.RgExh.U.adC p q i k • (creq ((s == t), k) * annq (t, i))

def lFq (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  liftq n (Ts E1 E2 s p q) + adLq s p q

def c1 (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  (1 / 2 : ℂ) • (lFq E1 E2 true p q + lFq E1 E2 false p q)

def c2 (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  (1 / 2 : ℂ) • (lFq E1 E2 true p q - lFq E1 E2 false p q)

end Chains

abbrev inUL (lev : Fin n → ℕ) (l : Lt n) : Prop := lev l.2.1.1 < lev l.2.1.2

abbrev inKU (lev : Fin n → ℕ) (l : Lt n) : Prop := l.1 = true ∧ lev l.2.1.1 < lev l.2.1.2

def omQ (lev : Fin n → ℕ) : Finset (Lt n) := univ.filter fun l => l.1 = true ∧ lev l.2.1.1 < lev l.2.1.2

def topq {V : Type} [AddCommGroup V] [Module ℂ V] (lev : Fin n → ℕ) (v : V) : Cq n V := Pi.single (omQ lev) v

def IsSubL (lev : Fin n → ℕ) (S : Lt n → Prop) : Prop :=
  (∀ l, S l → inUL lev l) ∧ ∀ (s t : Bool) (i j k : Pos n), i.1.2 = j.1.1 → k.1.1 = i.1.1 → k.1.2 = j.1.2 →
    S (s, i) → S (t, j) → S ((s == t), k)

section Algebra

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def PairRel (E1 E2 : Fin n → Fin n → Module.End ℂ W) : Prop :=
  GlRel E1 ∧ GlRel E2 ∧ ∀ a b c d, Commute (E1 a b) (E2 c d)

def ev2 (E1 E2 : Fin n → Fin n → Module.End ℂ W) : FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] Module.End ℂ W :=
  FreeAlgebra.lift ℂ fun x => if x.1 then E1 x.2.1 x.2.2 else E2 x.2.1 x.2.2

def evB (lev : Fin n → ℕ) (X1 X2 : Fin n → Fin n → Module.End ℂ W) :
    FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] Module.End ℂ W :=
  FreeAlgebra.lift ℂ fun x => if lev x.2.1 = lev x.2.2 then (if x.1 then X1 x.2.1 x.2.2 else X2 x.2.1 x.2.2) else 0

def LRel (lev : Fin n → ℕ) (X1 X2 : Fin n → Fin n → Module.End ℂ W) : Prop :=
  (∀ p q r v, lev p = lev q → lev r = lev v →
    X1 p q * X1 r v - X1 r v * X1 p q = (if q = r then X1 p v else 0) - (if v = p then X1 r q else 0)) ∧
  (∀ p q r v, lev p = lev q → lev r = lev v →
    X2 p q * X2 r v - X2 r v * X2 p q = (if q = r then X2 p v else 0) - (if v = p then X2 r q else 0)) ∧
  ∀ p q r v, lev p = lev q → lev r = lev v → Commute (X1 p q) (X2 r v)

end Algebra

def Inv2 (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
    ∀ c d, Commute (E1 c d + E2 c d) (ev2 E1 E2 a)

def InvLev (lev : Fin n → ℕ) (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (X1 X2 : Fin n → Fin n → Module.End ℂ W), LRel lev X1 X2 →
    ∀ p q, lev p = lev q → Commute (X1 p q + X2 p q) (evB lev X1 X2 b)

def LiftInv : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
    (∀ a b (x y : V), ⟪kF E1 E2 a b x, y⟫_ℂ = ⟪x, kF E1 E2 b a y⟫_ℂ) →
    (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF E1 E2 a b w ∈ S) →
    ∀ v w : V, v ≠ 0 → v ∈ hwSp E1 E2 μ → w ∈ hwSp E1 E2 μ → (∃ x ∈ alg E1 E2, x v = w) →
      ∃ a, Inv2 a ∧ ev2 E1 E2 a v = w

def HCDec2 : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)), Monotone lev → Inv2 a →
    ∃ b : FreeAlgebra ℂ (Bool × Fin n × Fin n), ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 → ∀ x : V, ∃ w : Lt n → V,
        ev2 E1 E2 a x - evB lev E1 E2 b x = ∑ l : Lt n, if inUL lev l then Tl E1 E2 l (w l) else 0

def GenCOU2 : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (S : Lt n → Prop) (a b : FreeAlgebra ℂ (Bool × Fin n × Fin n)), Monotone lev → IsSubL lev S →
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
      (∀ l, S l → Commute (Tl E1 E2 l) (ev2 E1 E2 a)) ∧
      ∀ x : V, ∃ w : Lt n → V, ev2 E1 E2 a x - evB lev E1 E2 b x = ∑ l : Lt n, if inUL lev l then Tl E1 E2 l (w l) else 0) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
      ∀ (j : ℕ) (x : Cq n V), SuppQ S x → DegQ j x → bdq E1 E2 x = 0 →
        ∃ w : Cq n V, SuppQ (inUL lev) w ∧ DegQ (j + 1) w ∧
          liftq n (ev2 E1 E2 a) x - evB lev (c1 E1 E2) (c2 E1 E2) b x = bdq E1 E2 w

def TopCyc : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    PairRel E1 E2 → ∀ v : V, (∀ l, inKU lev l → Tl E1 E2 l v = 0) → bdq E1 E2 (topq lev v) = 0

def LeviRel : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    Monotone lev → PairRel E1 E2 → ∀ x : Cq n V, SuppQ (inUL lev) x →
      (∀ s p q, lev p = lev q → SuppQ (inUL lev) (lFq E1 E2 s p q x) ∧ (∀ j, DegQ j x → DegQ j (lFq E1 E2 s p q x)) ∧
        lFq E1 E2 s p q (bdq E1 E2 x) = bdq E1 E2 (lFq E1 E2 s p q x)) ∧
      ∀ p q r v, lev p = lev q → lev r = lev v →
        (c1 E1 E2 p q (c1 E1 E2 r v x) - c1 E1 E2 r v (c1 E1 E2 p q x) =
          (if q = r then c1 E1 E2 p v x else 0) - (if v = p then c1 E1 E2 r q x else 0)) ∧
        (c2 E1 E2 p q (c2 E1 E2 r v x) - c2 E1 E2 r v (c2 E1 E2 p q x) =
          (if q = r then c2 E1 E2 p v x else 0) - (if v = p then c2 E1 E2 r q x else 0)) ∧
        c1 E1 E2 p q (c2 E1 E2 r v x) = c2 E1 E2 r v (c1 E1 E2 p q x)

def InvL : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (X1 X2 : Fin n → Fin n → Module.End ℂ W)
    (L : Submodule ℂ W) (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)), LRel lev X1 X2 →
    (∀ p q, lev p = lev q → ∀ s ∈ L, (X1 p q + X2 p q) s ∈ L) →
    (∀ p q, lev p = lev q → ∀ s ∈ L, (X1 p q + X2 p q) (evB lev X1 X2 b s) = evB lev X1 X2 b ((X1 p q + X2 p q) s)) →
    ∃ b', InvLev lev b' ∧ ∀ s ∈ L, evB lev X1 X2 b' s = evB lev X1 X2 b s

def CapOne : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ),
    GlRel E → (∀ m (x : V), gelA E m x = GlobalTheory.Dec.gelfVal χ m • x) →
      ∀ Y : ℂ, qdet E (Y + ((n : ℂ) - 1) / 2) = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ V)

def DualCap : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ),
    GlRel E → (∀ m (x : V), gelA (barF E) m x = GlobalTheory.Dec.gelfVal (fun a => -χ a) m • x) →
      ∀ Y : ℂ, qdet E (Y + ((n : ℂ) - 1) / 2) = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ V)

end GlobalTheory.CompanionTheory.PairMult
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem GlobalTheory.CompanionTheory.SW.coordW_image_unit_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (u : (Fv F v ⊗[F] E)ˣ) (S : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), MeasurableSet S → coordW (Fv F v) b lam 1 M ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' S) = ((‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ : ℝ≥0∞)) ^ M * coordW (Fv F v) b lam 1 M S := by
  intro F E _ _ _ _ _ σ hσ M d b v lam hlam u S hS
  have hR := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  obtain ⟨h1, h2, h3, h4, -⟩ := id hR
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 1 M
  obtain ⟨-, hW, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lam hlam.1
  haveI := hW 1 M
  haveI : (coordW (Fv F v) b lam 1 M).Regular := by
    let K : TopologicalSpace.PositiveCompacts (Fin 1 → Fin M → Fv F v ⊗[F] E) := Classical.choice inferInstance
    exact Measure.regular_of_isAddLeftInvariant K.isCompact K.interior_nonempty K.isCompact.measure_ne_top
  have hchar : distribHaarChar (Fv F v ⊗[F] E) u = ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ := by
    haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    let bE := Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)
    let e : (Fv F v ⊗[F] E) ≃ₜ+ (Fin (Module.finrank F E) → Fv F v) :=
      { bE.equivFun.toAddEquiv with
        continuous_toFun := IsModuleTopology.continuous_of_linearMap bE.equivFun.toLinearMap
        continuous_invFun := IsModuleTopology.continuous_of_linearMap bE.equivFun.symm.toLinearMap }
    borelize (Fv F v ⊗[F] E)
    set A := Algebra.leftMulMatrix bE (u : Fv F v ⊗[F] E)
    have hdet : A.det = Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) := (Algebra.norm_eq_matrix_det bE _).symm
    have hA : IsUnit A.det := hdet ▸ u.isUnit.map (Algebra.norm (Fv F v))
    have hN : Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) ≠ 0 := (hdet ▸ hA).ne_zero
    rw [GlobalTheory.ModuNorm.distribHaarChar_eq_addEquivAddHaarChar]
    have ht := GlobalTheory.ModuLR.addEquivAddHaarChar_transport e.symm (GlobalTheory.ModuLR.mulVecCE A hA)
    have hext : ((e.symm.symm.trans (GlobalTheory.ModuLR.mulVecCE A hA)).trans e.symm) = GlobalTheory.ModuNorm.mulUnitCE u := by
      ext x
      show bE.equivFun.symm (Matrix.mulVec A (bE.equivFun x)) = (u : Fv F v ⊗[F] E) * x
      rw [show Matrix.mulVec A (bE.equivFun x) = bE.equivFun ((u : Fv F v ⊗[F] E) * x) from Algebra.leftMulMatrix_mulVec_repr bE _ x, LinearEquiv.symm_apply_apply]
    rw [hext] at ht
    rw [ht, GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE _ inferInstance inferInstance, hdet, GlobalTheory.GaugeEx.modu, dite_eq_left (hdet ▸ hA)]
    convert GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v _ hN using 2
    exact Units.ext rfl
  let U1 : (Fin M → Fv F v ⊗[F] E)ˣ := Units.map (Pi.constRingHom (Fin M) (Fv F v ⊗[F] E)).toMonoidHom u
  let U : (Fin 1 → Fin M → Fv F v ⊗[F] E)ˣ :=
    Units.map (Pi.constRingHom (Fin 1) (Fin M → Fv F v ⊗[F] E)).toMonoidHom U1
  have hc1 : distribHaarChar (Fin M → Fv F v ⊗[F] E) U1 = ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ ^ M := by
    rw [GlobalTheory.ModuPiLocal.distribHaarChar_pi (fun _ : Fin M => Fv F v ⊗[F] E) U1]
    have hU : ∀ i, Units.map (Pi.evalRingHom (fun _ : Fin M => Fv F v ⊗[F] E) i).toMonoidHom U1 = u :=
      fun i => Units.ext rfl
    simp only [hU, hchar, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hc : distribHaarChar (Fin 1 → Fin M → Fv F v ⊗[F] E) U = ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ ^ M := by
    rw [GlobalTheory.ModuPiLocal.distribHaarChar_pi (fun _ : Fin 1 => Fin M → Fv F v ⊗[F] E) U]
    have hU : ∀ i, Units.map (Pi.evalRingHom (fun _ : Fin 1 => Fin M → Fv F v ⊗[F] E) i).toMonoidHom U = U1 :=
      fun i => Units.ext rfl
    simp only [hU, hc1, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one]
  have hm : coordW (Fv F v) b lam 1 M ((fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => U • X) '' S) =
      distribHaarChar (Fin 1 → Fin M → Fv F v ⊗[F] E) U * coordW (Fv F v) b lam 1 M S := by
    open scoped Pointwise in
    exact (distribHaarChar_mul (coordW (Fv F v) b lam 1 M) U S).symm
  have himg : (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) =
      fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => U • X := rfl
  rw [himg, hm, hc]
  push_cast
  rfl
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.schwartz_bound_finite_infinite : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (Φ : Mx D m n → ℂ), Φ ∈ schwartzA θ m n → Continuous Φ ∧ ∃ (k : ℕ) (f : Fin k → SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ) (g : Fin k → (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ), (∀ i, g i ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) ∧ ∀ x, ‖Φ x‖ₑ ≤ ∑ i, ‖f i (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ₑ := by
  first | exact @GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated | exact GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated | (intros; apply GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.lie_skew_adjoint_l2 : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : GlobalTheory.CuspRep.Lie E a) (φ ψ : Sm E a) (hφ : MemL2Quotient (latticeGL E a) μ φ.1) (hψ : MemL2Quotient (latticeGL E a) μ ψ.1) (hXφ : MemL2Quotient (latticeGL E a) μ (lie E a X φ).1) (hXψ : MemL2Quotient (latticeGL E a) μ (lie E a X ψ).1), Continuous φ.1 → Continuous ψ.1 → Continuous (lie E a X φ).1 → Continuous (lie E a X ψ).1 → inner ℂ hXφ.toL2 hψ.toL2 = - inner ℂ hφ.toL2 hXψ.toL2 := by
  first | exact @GlobalTheory.CompanionTheory.LieSkew.lie_skew | exact GlobalTheory.CompanionTheory.LieSkew.lie_skew | (intros; apply GlobalTheory.CompanionTheory.LieSkew.lie_skew <;> assumption)
end
