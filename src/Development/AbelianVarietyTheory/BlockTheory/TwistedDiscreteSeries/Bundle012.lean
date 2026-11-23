module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle010
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010

@[expose] public section

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound

open Formalism.UG GlobalTheory.PRep GlobalTheory.LGrp GlobalTheory.LFun

def TrivialBound (q n : ℕ) (α : Fin (n / 2) → ℂˣ) : Prop :=
  ∀ i, ((q : ℝ) ^ 2) ^ (-(((n : ℝ) - 1) / 2)) ≤ ‖(α i : ℂ)‖ ∧ ‖(α i : ℂ)‖ ≤ ((q : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)

def SatakeBoundInert : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ),
    IsUnramInv ϖ σ q →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GU σ n) V) (α : Fin (n / 2) → ℂˣ),
      IsIrrSmooth π → IsUnitarisable π → HasSatU ϖ q π α → TrivialBound q n α

theorem bound_eq (q n : ℕ) : ((q : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) = (q : ℝ) ^ ((n : ℝ) - 1) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
  congr 1
  push_cast
  ring

def trivParam (q n : ℕ) (hq : q ≠ 0) : Fin (n / 2) → ℂˣ :=
  fun i => Units.mk0 (q : ℂ) (by exact_mod_cast hq) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ))

theorem trivial_hyp {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L}
    {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (hq : q ≠ 0) (n : ℕ) :
    IsIrrSmooth (charRep (1 : GU σ n →* ℂˣ)) ∧ IsUnitarisable (charRep (1 : GU σ n →* ℂˣ)) ∧
      HasSatU ϖ q (charRep (1 : GU σ n →* ℂˣ)) (trivParam q n hq) := by
  have hc : ∀ b : GU σ n, chiDeltaU q (fun i => (trivParam q n hq i : ℂ)) b = 1 := fun b => by
    refine Finset.prod_eq_one fun i _ => ?_
    have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    split_ifs with h
    · simp only [trivParam, Units.val_zpow_eq_zpow_val, Units.val_mk0]
      rw [← zpow_mul, ← zpow_add₀ hq']
      convert zpow_zero (q : ℂ) using 2
      ring
    · rfl
  refine ⟨⟨fun z => by simp, charRep_irreducible _⟩, charRep_unitarisable _ (by simp), ?_, fun x _ h0 => ?_⟩
  · exact (Submodule.ne_bot_iff _).2 ⟨1, GlobalTheory.LGrp.mem_fixed.2 (by simp), one_ne_zero⟩
  · refine IsSatVecU.of_map hU (ρ' := rightReg ℂ _ ℂ) (LinearMap.pi fun _ => LinearMap.id)
      (fun g y => by funext z; simp [rightReg, LinearMap.funLeft]) (fun a b e => congrFun e 1)
      (isSatVecU_of_isSphericalU hU (fun b g k _ _ => by simp [hc]) fun e => h0 (congrFun e 1))

end GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound

end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables

open MeasureTheory Formalism.UG GlobalTheory.Doubling GlobalTheory.PRep

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

abbrev GD (σ : L →+* L) (n : ℕ) : Subgroup (GL (Fin (n + n)) L) := UJ σ (dblGram finSumFinEquiv (antiJ L n))

def KD (σ : L →+* L) (n : ℕ) : Subgroup (GD σ n) := (intPts (intL L).subtype (GD σ n)).subgroupOf (GD σ n)

abbrev PD (σ : L →+* L) (n : ℕ) : Subgroup (GD σ n) := siegelOf finSumFinEquiv (GD σ n).subtype

abbrev aD (σ : L →+* L) (n : ℕ) : PD σ n →* Lˣ := aOf finSumFinEquiv (GD σ n).subtype

def io1 (σ : L →+* L) (n : ℕ) (g : GU σ n) : GD σ n := ioU σ finSumFinEquiv (J := antiJ L n) rfl (g, 1)

def IsUnr (χ : Lˣ →* ℂˣ) : Prop := ∀ u : Lˣ, Valued.v (u : L) = 1 → χ u = 1

def secVal (q : ℕ) (χ : Lˣ →* ℂˣ) (t : ℂ) (a : Lˣ) : ℂ := χ a * (q : ℂ) ^ (-(2 * (ordL (a : L) : ℂ) * t))

def IsSphSec (σ : L →+* L) (q n : ℕ) (χ : Lˣ →* ℂˣ) (s : ℂ) (Φ : GD σ n → ℂ) : Prop :=
  ∀ (p : PD σ n), ∀ k ∈ KD σ n, Φ (p * k) = secVal q χ (s + (n : ℂ) / 2) (aD σ n p)

def IsZonal {σ : L →+* L} {n : ℕ} (ϖ : L) (q : ℕ) (α : Fin (n / 2) → ℂˣ) (w : GU σ n → ℂ) : Prop :=
  IsBiInv (KU σ n) w ∧ w 1 = 1 ∧
    ∀ h ∈ Hecke ℂ (KU σ n), hAct (KU σ n) h w 1 = SatU ϖ q h fun i => (α i : ℂ)

def varX (q n : ℕ) (ε s : ℂ) : ℂ := ε * (q : ℂ) ^ (-(2 * s + n))

def varY (q : ℕ) (ε s : ℂ) : ℂ := ε * (q : ℂ) ^ (-(2 * s + 1))

def Domain {r : ℕ} (y : ℂ) (α : Fin r → ℂˣ) : Prop :=
  ‖y‖ < 1 ∧ ∀ i, ‖y‖ * ‖(α i : ℂ)‖ < 1 ∧ ‖y‖ * ‖(α i : ℂ)‖⁻¹ < 1

def closedForm (q n : ℕ) (X y : ℂ) (α : Fin (n / 2) → ℂˣ) : ℂ :=
  (∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * X)) *
    (∏ i, (1 - y * (α i : ℂ))⁻¹ * (1 - y / (α i : ℂ))⁻¹) * (if Odd n then (1 - y)⁻¹ else 1)

def stdL (q n : ℕ) (α : Fin (n / 2) → ℂˣ) (ε z : ℂ) : ℂ :=
  GlobalTheory.LFun.eulerFac (GlobalTheory.LGrp.bcParam n α) (ε * ((q ^ 2 : ℕ) : ℂ) ^ (-z))

def etaL (q k : ℕ) (z : ℂ) : ℂ := (1 - (-1) ^ k * (q : ℂ) ^ (-z))⁻¹

def dFac (q n m : ℕ) (s : ℂ) : ℂ := ∏ i ∈ Finset.range n, etaL q (m + i) (2 * s + n - i)

def UnramDoublingInert : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ),
    IsUnramInv (ϖ : L) σ q →
    ∀ [MeasurableSpace (GU σ n)] [BorelSpace (GU σ n)] (μ : Measure (GU σ n)) [μ.IsHaarMeasure],
    μ (KU σ n) = 1 →
    ∀ (χ : Lˣ →* ℂˣ), IsUnr χ → ∀ (s : ℂ) (Φ : GD σ n → ℂ), IsSphSec σ q n χ s Φ →
    ∀ (α : Fin (n / 2) → ℂˣ) (w : GU σ n → ℂ), IsZonal (ϖ : L) q α w →
      (Domain (varY q (χ ϖ) s) α →
        Integrable (fun g => Φ (io1 σ n g) * w g) μ ∧
        ∫ g, Φ (io1 σ n g) * w g ∂μ = closedForm q n (varX q n (χ ϖ) s) (varY q (χ ϖ) s) α ∧
        ∀ m : ℕ, (χ ϖ : ℂ) = (-1) ^ m →
          ∫ g, Φ (io1 σ n g) * w g ∂μ = stdL q n α (χ ϖ) (s + 1 / 2) / dFac q n m s) ∧
      (n ≤ 1 → Integrable (fun g => Φ (io1 σ n g) * w g) μ ∧ ∫ g, Φ (io1 σ n g) * w g ∂μ = 1)

theorem secVal_mul {q : ℕ} (hq : q ≠ 0) (χ : Lˣ →* ℂˣ) (t : ℂ) (a b : Lˣ) :
    secVal q χ t (a * b) = secVal q χ t a * secVal q χ t b := by
  have h : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  simp only [secVal, map_mul, Units.val_mul, P.fIwasawa_ordL_mul _ _ a.ne_zero b.ne_zero, Int.cast_add]
  rw [show -(2 * ((ordL (a : L) : ℂ) + (ordL (b : L) : ℂ)) * t) =
    -(2 * (ordL (a : L) : ℂ) * t) + -(2 * (ordL (b : L) : ℂ) * t) by ring, Complex.cpow_add _ _ h]
  ring

theorem secVal_unit (q : ℕ) {χ : Lˣ →* ℂˣ} (hχ : IsUnr χ) (t : ℂ) {a : Lˣ} (ha : Valued.v (a : L) = 1) :
    secVal q χ t a = 1 := by
  have : ordL (a : L) = 0 := by
    have h0 : Valued.v (a : L) ≠ 0 := by rw [ha]; exact one_ne_zero
    have h1 : WithZero.unzero h0 = 1 := WithZero.coe_injective (by rw [WithZero.coe_unzero, ha]; rfl)
    simp [ordL, h0, h1]
  simp [secVal, hχ a ha, this]

theorem v_aD_le {σ : L →+* L} {n : ℕ} (p : PD σ n) (hp : (p : GD σ n) ∈ KD σ n) : Valued.v (aD σ n p : L) ≤ 1 := by
  obtain ⟨-, x, hx⟩ := hp
  have e : ((GD σ n).subtype p).1 = x.1.map (intL L).subtype := by
    rw [show (GD σ n).subtype p = _ from hx.symm]; rfl
  rw [val_aOf, e, leviMat_map]
  exact (congrArg Valued.v ((intL L).subtype.map_det _).symm).le.trans (leviMat finSumFinEquiv x.1).det.2

theorem v_aD_eq {σ : L →+* L} {n : ℕ} (p : PD σ n) (hp : (p : GD σ n) ∈ KD σ n) : Valued.v (aD σ n p : L) = 1 := by
  have h := v_aD_le p⁻¹ (inv_mem hp)
  rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀,
    inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _)))] at h
  exact le_antisymm (v_aD_le p hp) h

theorem exists_isSphSec (σ : L →+* L) {q : ℕ} (hq : q ≠ 0) (n : ℕ) {χ : Lˣ →* ℂˣ} (hχ : IsUnr χ) (s : ℂ) :
    ∃ Φ, IsSphSec σ q n χ s Φ := by
  classical
  refine ⟨fun g => if h : ∃ p : PD σ n, ∃ k ∈ KD σ n, g = p * k then
    secVal q χ (s + (n : ℂ) / 2) (aD σ n h.choose) else 0, fun p k hk => ?_⟩
  have h : ∃ p' : PD σ n, ∃ k' ∈ KD σ n, (p : GD σ n) * k = p' * k' := ⟨p, k, hk, rfl⟩
  obtain ⟨k', hk', e⟩ := h.choose_spec
  have hm : ((p⁻¹ * h.choose : PD σ n) : GD σ n) ∈ KD σ n := by
    have : ((p⁻¹ * h.choose : PD σ n) : GD σ n) = k * k'⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
      exact e.symm
    rw [this]
    exact mul_mem hk (inv_mem hk')
  simp only [dif_pos h]
  rw [← mul_inv_cancel_left p h.choose, map_mul, secVal_mul hq, secVal_unit q hχ _ (v_aD_eq _ hm), mul_one]

theorem isZonal_of_isSatVecU {ϖ : L} {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv ϖ σ q) {V : Type} [AddCommGroup V]
    [Module ℂ V] {ρ : Representation ℂ (GU σ n) V} {x : V} {α : Fin (n / 2) → ℂˣ}
    (hx : GlobalTheory.LFun.IsSatVecU ϖ q ρ x α) (l : V →ₗ[ℂ] ℂ) (hl : ∀ k ∈ KU σ n, ∀ y, l (ρ k y) = l y) (h1 : l x = 1) :
    IsZonal ϖ q α fun g => l (ρ g x) := by
  refine ⟨fun a b g => ?_, by simpa using h1, fun h hh => ?_⟩
  · simp only [map_mul, Module.End.mul_apply, hl _ a.2, GlobalTheory.LGrp.mem_fixed.1 hx.2.1 _ b.2]
  · have e := congrArg l (hx.2.2 h hh)
    rw [map_smul, h1, smul_eq_mul, mul_one] at e
    rw [← e]
    refine Eq.trans (finsum_congr fun c => ?_)
      (l.toAddMonoidHom.map_finsum (GlobalTheory.LFun.finite_heckeVec (P.isCommensurated_integral_unitary_of_unramified hU n) hh ρ x)).symm
    simp

theorem isZonal_one [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (n : ℕ) :
    ∃ α : Fin (n / 2) → ℂˣ, (∀ i, (α i : ℂ) = (q : ℂ) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ))) ∧
      IsZonal (σ := σ) ϖ q α fun _ => 1 := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := hU.2.2.2.2.2.1; omega)
  refine ⟨fun i => Units.mk0 _ (zpow_ne_zero ((n : ℤ) - 1 - 2 * (i.val : ℤ)) hq), fun _ => rfl, fun _ _ _ => rfl, rfl,
    fun h hh => ?_⟩
  refine (congrFun (Final.SatakeInert L ϖ σ q n (n / 2) hU (by omega) (by omega)
    (fun i => (q : ℂ) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ))) (fun i => zpow_ne_zero _ hq) h hh
    (fun _ => 1) fun b g k _ _ => ?_) 1).trans (by simp)
  rw [mul_one, chiDeltaU]
  refine (Finset.prod_eq_one fun i _ => ?_).symm
  split_ifs
  · rw [← zpow_mul, ← zpow_add₀ hq]
    convert zpow_zero (q : ℂ) using 2
    ring
  · rfl

end GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables

end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory GlobalTheory.Doubling
open scoped TensorProduct ENNReal NNReal ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def schwartzA (θ : InfFam D) (m n : ℕ) : Submodule ℂ (Mx D m n → ℂ) :=
  Submodule.span ℂ {φ | ∃ (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
    (g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ),
      g ∈ WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∧
      φ = fun x => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))}

variable (A B : HSp D)

def cols (x y : WO A B) : WO (dblSp A) B := (Matrix.fromCols x y).submatrix id finSumFinEquiv.symm

def fstCols (w : WO (dblSp A) B) : WO A B := w.submatrix id fun j => finSumFinEquiv (Sum.inl j)

def sndCols (w : WO (dblSp A) B) : WO A B := w.submatrix id fun j => finSumFinEquiv (Sum.inr j)

def half (D : D7) : AE D := incA D (1 / 2)

def onX (x : WO A B) : WO (dblSp A) B := cols A B (half D • x) (half D • x)

def onY (y : WO A B) : WO (dblSp A) B := cols A B y (-y)

def xOf (w : WO (dblSp A) B) : WO A B := fstCols A B w + sndCols A B w

def yOf (w : WO (dblSp A) B) : WO A B := half D • (fstCols A B w - sndCols A B w)

variable {A B}

def thetaInt (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)) (μ : Measure (GA D B)) (𝓕 : Set (GA D B))
    (f₁ f₂ : WO A B → ℂ) (g₁ g₂ : GA D A) : ℝ≥0∞ :=
  ∫⁻ h in 𝓕, ‖thetaKO om g₁ h f₁ * thetaKO om g₂ h f₂‖ₑ ∂μ

abbrev ht (V : HSp D) (g : GA D V) : ℝ≥0 := AdelicU.height D.sp.cm.sig V.gram g

variable (A B)

def InRange : Prop := 1 ≤ A.rank ∧ A.rank < B.rank ∧ (Cusp.wittIndex B = 0 ∨ A.rank + Cusp.wittIndex B < B.rank)

theorem half_add_half : half D + half D = 1 := by
  rw [half, ← map_add (f := _), add_halves, map_one]

theorem fstCols_cols (x y : WO A B) : fstCols A B (cols A B x y) = x := by
  ext i j; simp [fstCols, cols]

theorem sndCols_cols (x y : WO A B) : sndCols A B (cols A B x y) = y := by
  ext i j; simp only [sndCols, cols, Matrix.submatrix_apply, Equiv.symm_apply_apply]; rfl

theorem coords (x y : WO A B) : xOf A B (onX A B x) = x ∧ yOf A B (onX A B x) = 0 ∧
    xOf A B (onY A B y) = 0 ∧ yOf A B (onY A B y) = y := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [xOf, yOf, onX, onY, fstCols_cols, sndCols_cols]
  · rw [← add_smul, half_add_half, one_smul]
  · simp
  · simp
  · rw [sub_neg_eq_add, smul_add, ← add_smul, half_add_half, one_smul]

end GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaMultiplicity

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def kernelP (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (g : GA D (Wc D i)) (h : GA D (Vc D i))
    (Φ : WO (Vc D i) (Wc D i) → ℂ) : ℂ :=
  thetaKO (R.ωP i t) h g Φ

def IsThetaMult (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
    (y : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A))) : Prop :=
  (∀ x, y x ∈ R.Wall i (sg0 D A)) ∧
    ∃ thP : LinearMap.range (R.extV i t) →ₗ[ℂ] (LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (GA D (Wc D i) → ℂ)),
      Lift.IsThetaP (R.νV i t) (R.fdV i t) (kernelP R i t) (R.ptP i t) (R.ioP i) (LinearMap.range (R.extV i t)) thP ∧
      ∀ (x : (R.HV i t).H) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ),
        y x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) =
          thP ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ v)

end

section Basic₂

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaMultiplicity

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SizeOK (D : D7) : Prop := 8 * D.R.f * D.R.r + 4 ≤ D.R.nV

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def transl (R : RealDat D A Ks) (i : Fin D.R.m) (g : G) :
    MMap (R.MW i (sg0 D A)) →ₗ[ℂ] MMap (R.MW i (sg0 D A)) :=
  postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g))

def thetaTranslates (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Set (MMap (R.MW i (sg0 D A))) :=
  {y | ∃ (g : G) (x : (R.HV i t).H), y = transl R i g (R.thF i t x)}

def SpanAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  Submodule.span ℂ (thetaTranslates R i t) = R.Wall i (sg0 D A)

def goodModel (R : RealDat D A Ks) (i : Fin D.R.m) : Submodule ℂ (R.HW i (sg0 D A)).H :=
  (R.Wat i (sg0 D A) R.triv).comap (R.HW i (sg0 D A)).e

def GoodRangeAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  LinearMap.range (R.thG i t) = goodModel R i

theorem range_eq_comap_iff {X H M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup H] [Module ℂ H] [AddCommGroup M]
    [Module ℂ M] (e : H →ₗ[ℂ] M) (f : X →ₗ[ℂ] H) (p : X →ₗ[ℂ] M) (U : Submodule ℂ M) (hinj : Function.Injective e)
    (hle : U ≤ LinearMap.range e) (hc : ∀ x, e (f x) = p x) :
    LinearMap.range f = U.comap e ↔ LinearMap.range p = U := by
  have hcomp : e ∘ₗ f = p := LinearMap.ext hc
  rw [← hcomp, LinearMap.range_comp]
  constructor
  · intro h
    rw [h, Submodule.map_comap_eq_self hle]
  · intro h
    rw [← h, Submodule.comap_map_eq_of_injective hinj]



theorem goodRangeAt_iff {R : RealDat D A Ks} (hW : R.models_HW) (hG : R.thP_thG) (i : Fin D.R.m) (t : T) :
    GoodRangeAt R i t ↔
      LinearMap.range (postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A)) ∘ₗ R.thF i t) = R.Wat i (sg0 D A) R.triv :=
  range_eq_comap_iff (R.HW i (sg0 D A)).e (R.thG i t) _ (R.Wat i (sg0 D A) R.triv) (hW i (sg0 D A)).1
    (le_of_le_of_eq inf_le_left (hW i (sg0 D A)).2.1.symm) (fun x => hG i t x)

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize

end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lattice

variable {D : D7}

def StabLat (V : HSp D) (κ : GA D V) : Prop :=
  κ ∈ GfC V ∧ gLat V κ = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E))

def LevAgrees (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (M : ℕ) (Mh : Ideal (𝓞 D.host.E)) (κ : GA D V)
    (lev : La →ₗ[𝓞 D.host.E] La) : Prop :=
  ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
    finVec V (ι (lev a)) - (finHom V κ).1.mulVec (finVec V (ι a)) = M • w

end Lattice

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

end Frames

section Statement

variable {D : D7} (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ)


include hT hj hσ in
theorem dict_mem_dom (h : GA D (T.V j σ)) : (T.dict j σ h).2 ∈ ((T.U j σ).X (T.dict j σ h).1).dom := by
  obtain ⟨_, _, _, hd⟩ := hT.dictU j hj σ hσ
  exact hd.2.2.2.1 h


end Statement

end GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix
end
end
