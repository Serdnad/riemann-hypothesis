module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle082
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle083
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.ClassNumber
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
public import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem ker_localizedTheta_eq_span_of_dvd (l : ℕ) [Fact l.Prime] (x : Per.Ainf l)
    (hx : ∀ a : Per.Ainf l, Per.θ l a = 0 ↔ x ∣ a) :
    Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) x} := by
  refine le_antisymm (fun y hy => ?_) ?_
  · obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) y
    have hy' : Per.θP l y = 0 := GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l y (by rwa [pow_one])
    have h0 : Per.θ l a = 0 := by
      have h1 := GlobalTheory.RingIface.fontaineTheta_algebraMap (l := l) a
      rw [← ha, map_mul, hy', zero_mul] at h1
      exact Subtype.ext h1.symm
    obtain ⟨c, rfl⟩ := (hx a).1 h0
    have hu : IsUnit (algebraMap (Per.Ainf l) (Per.AinfP l) ((l : ℕ) : Per.Ainf l) ^ n) :=
      (IsLocalization.Away.algebraMap_isUnit (S := Per.AinfP l) ((l : ℕ) : Per.Ainf l)).pow n
    rw [← Ideal.mul_unit_mem_iff_mem _ hu, ha, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_singleton_le_iff_mem]
    exact GlobalTheory.RingIface.alg_mem_kerP (l := l) ((hx x).2 dvd_rfl)

theorem ker_localizedTheta_eq_span_xi : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e →
    Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)} :=
  fun l _ e he => ker_localizedTheta_eq_span_of_dvd l (xi e) (theta_eq_zero_iff_xi_dvd l e he)

end GlobalTheory.MemLoc
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem dense_ker_of_bounded {A R C Q : Type} [CommRing A] [CommRing R] [CommRing C] [CommRing Q]
    (p : ℕ) (α : A →+* R) (i : R →+* C) (f : C →+* Q) (N : ℕ)
    (hd : ∀ (x : C) (r : ℕ), ∃ (s : R) (z : C), x = i s + (p : C) ^ r * z)
    (hb : ∀ x : C, ∃ a : A, (p : Q) ^ N * f x = f (i (α a)))
    (x : C) (hx : f x = 0) :
    ∃ (u : R) (z : C), f (i u) = 0 ∧ x = i u + (p : C) * z := by
  obtain ⟨s, z, rfl⟩ := hd x (N + 1)
  obtain ⟨a, ha⟩ := hb z
  refine ⟨s + (p : R) * α a, (p : C) ^ N * z - i (α a), ?_, ?_⟩
  · rw [map_add (f := _), map_mul, map_pow, map_natCast] at hx
    rw [map_add (f := _), map_mul, map_natCast, map_add (f := _), map_mul, map_natCast, ← ha, ← hx]
    ring
  · rw [map_add (f := _), map_mul, map_natCast]
    ring

theorem ev_algebraMap (l : ℕ) [Fact l.Prime] (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a :=
  GlobalTheory.RingIface.ev_alg l n a

theorem fil_dense : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → ∀ (n : ℕ) (x : Per.Acris l), j x ∈ Per.FilP l n → ∃ (u : Per.Acris0 l) (z : Per.Acris l), (u : Per.AinfP l) ∈ Per.kerP l ^ n ∧ x = algebraMap (Per.Acris0 l) (Per.Acris l) u + (l : Per.Acris l) * z := by
  intro l _ j hj n x hx
  obtain ⟨N, hN⟩ := hj.bdd n
  have h0 : ∀ u : Per.Acris0 l, ((Per.ev l n).comp j) (algebraMap (Per.Acris0 l) (Per.Acris l) u) =
      Ideal.Quotient.mk _ (u : Per.AinfP l) := fun u => by
    rw [RingHom.comp_apply, hj.on0, ev_algebraMap]
  obtain ⟨u, z, hu, hz⟩ := dense_ker_of_bounded l (algebraMap (Per.Ainf l) (Per.Acris0 l))
    (algebraMap (Per.Acris0 l) (Per.Acris l)) ((Per.ev l n).comp j) N (acris_basic l).2.2.1
    (fun y => by
      obtain ⟨a, ha⟩ := hN y
      refine ⟨a, ?_⟩
      rw [map_mul, map_pow, map_natCast] at ha
      rw [h0]
      exact ha) x ((GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l n (j x)).1 hx)
  refine ⟨u, z, ?_, hz⟩
  rw [h0] at hu
  exact Ideal.Quotient.eq_zero_iff_mem.1 hu

end GlobalTheory.MemLoc
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.fontaineTheta_eq_zero_iff_fontaineXiElement_dvd : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ a : Per.Ainf l, Per.θ l a = 0 ↔ xi e ∣ a := by
  first | exact @GlobalTheory.MemLoc.theta_eq_zero_iff_xi_dvd | exact GlobalTheory.MemLoc.theta_eq_zero_iff_xi_dvd | (intros; apply GlobalTheory.MemLoc.theta_eq_zero_iff_xi_dvd <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l, IsEps C.ε := by
  first | exact @GlobalTheory.MemLoc.core_isEps | exact GlobalTheory.MemLoc.core_isEps | (intros; apply GlobalTheory.MemLoc.core_isEps <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant : ∀ (l : ℕ) [Fact l.Prime], Function.Surjective (Per.θD l) ∧ (∀ y : Per.BdRp l, Per.θD l y = 0 ↔ y ∈ Per.FilP l 1) ∧ (∀ y : Per.BdRp l, Per.θD l y ≠ 0 → IsUnit y) ∧ (∀ a : Per.Ainf l, Per.θD l (aDp l a) = (Per.θ l a : ℂ_[l])) ∧ ∀ (g : Per.Gq l) (y : Per.BdRp l), Per.θD l (Per.σDp g y) = Per.σC g (Per.θD l y) := by
  first | exact @GlobalTheory.MemLoc.thetaD_props | exact GlobalTheory.MemLoc.thetaD_props | (intros; apply GlobalTheory.MemLoc.thetaD_props <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic : ∀ (l : ℕ) [Fact l.Prime], ∃ (ζ : ℕ → Om l) (ε : Per.Fl l), ζ 0 = 1 ∧ (∀ m, ζ (m + 1) ^ l = ζ m) ∧ ζ 1 ≠ 1 ∧ ∀ m, (rootT ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (ζ m) := by
  first | exact @GlobalTheory.MemLoc.exists_zeta_eps | exact GlobalTheory.MemLoc.exists_zeta_eps | (intros; apply GlobalTheory.MemLoc.exists_zeta_eps <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_isBdRPlusSectionOfTheta : ∀ (l : ℕ) [Fact l.Prime], ∃ o : Om l →+* Per.BdRp l, IsSec o := by
  first | exact @GlobalTheory.MemLoc.SecEx.exists_isSec | exact GlobalTheory.MemLoc.SecEx.exists_isSec | (intros; apply GlobalTheory.MemLoc.SecEx.exists_isSec <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

theorem tame_valued_int (a : 𝓞 L) :
    Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) a) = v.valuation L (algebraMap (𝓞 L) L a) :=
  ReciprocityTheory.Aut.adic_valued_algebraMap v (algebraMap (𝓞 L) L a)

theorem tame_valued_lt_one_iff (a : 𝓞 L) :
    Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) a) < 1 ↔ a ∈ v.asIdeal := by
  rw [tame_valued_int,
    HeightOneSpectrum.valuation_lt_one_iff_mem]

theorem tame_mk_eq {u : v.adicCompletion L} {a b : 𝓞 L}
    (ha : Valued.v (u - algebraMap (𝓞 L) (v.adicCompletion L) a) < 1)
    (hb : Valued.v (u - algebraMap (𝓞 L) (v.adicCompletion L) b) < 1) :
    Ideal.Quotient.mk v.asIdeal a = Ideal.Quotient.mk v.asIdeal b := by
  rw [Ideal.Quotient.eq, ← tame_valued_lt_one_iff, map_sub]
  have e : algebraMap (𝓞 L) (v.adicCompletion L) a - algebraMap (𝓞 L) (v.adicCompletion L) b =
      (u - algebraMap (𝓞 L) (v.adicCompletion L) b) - (u - algebraMap (𝓞 L) (v.adicCompletion L) a) := by
    ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hb ha)

def unitPart : (v.adicCompletion L)ˣ →* (v.adicCompletion L)ˣ where
  toFun x := x * atFin v (unif v) ^ WithZero.log (Valued.v (x : v.adicCompletion L))
  map_one' := by simp
  map_mul' x y := by
    rw [Units.val_mul, map_mul, WithZero.log_mul (by simp) (by simp), zpow_add]
    exact mul_mul_mul_comm _ _ _ _

theorem isUnitAt_unitPart (x : (v.adicCompletion L)ˣ) : IsUnitAt v (unitPart v x) := by
  have h : Valued.v ((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) =
      WithZero.exp (-1 : ℤ) := unif_spec v
  have hx : Valued.v (x : v.adicCompletion L) ≠ 0 := by simp
  show Valued.v ((x * atFin v (unif v) ^ WithZero.log (Valued.v (x : v.adicCompletion L)) :
    (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, h, ← WithZero.exp_zsmul]
  nth_rewrite 1 [← WithZero.exp_log hx]
  rw [← WithZero.exp_add]
  simp

theorem unitPart_of_isUnitAt {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) : unitPart v x = x := by
  have h : Valued.v (x : v.adicCompletion L) = 1 := hx
  show x * atFin v (unif v) ^ WithZero.log (Valued.v (x : v.adicCompletion L)) = x
  rw [h]
  simp

theorem exists_unitPart_approx (x : (v.adicCompletion L)ˣ) : ∃ a : 𝓞 L,
    Valued.v ((unitPart v x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) a) < 1 :=
  ReciprocityTheory.Aut.adic_exists_approx v _ (le_of_eq (isUnitAt_unitPart v x))

def resPart : (v.adicCompletion L)ˣ →* 𝓞 L ⧸ v.asIdeal where
  toFun x := Ideal.Quotient.mk v.asIdeal (exists_unitPart_approx v x).choose
  map_one' := by
    refine tame_mk_eq v (b := 1) (exists_unitPart_approx v 1).choose_spec ?_
    simp
  map_mul' x y := by
    rw [← map_mul]
    refine tame_mk_eq v (exists_unitPart_approx v (x * y)).choose_spec ?_
    have hx := (exists_unitPart_approx v x).choose_spec
    have hy := (exists_unitPart_approx v y).choose_spec
    set a := (exists_unitPart_approx v x).choose
    set b := (exists_unitPart_approx v y).choose
    have hu : Valued.v (unitPart v x : v.adicCompletion L) = 1 := isUnitAt_unitPart v x
    have hb : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) b) ≤ 1 := by
      rw [tame_valued_int]
      exact v.valuation_le_one b
    have e : (unitPart v (x * y) : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) (a * b) =
        (unitPart v x : v.adicCompletion L) *
          ((unitPart v y : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) b) +
        ((unitPart v x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) a) *
          algebraMap (𝓞 L) (v.adicCompletion L) b := by
      rw [map_mul, map_mul, Units.val_mul]
      ring
    rw [e]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rwa [map_mul, hu, one_mul]
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hb) hx

theorem resPart_eq {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) {a : 𝓞 L}
    (ha : Valued.v ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) a) < 1) :
    resPart v x = Ideal.Quotient.mk v.asIdeal a := by
  refine tame_mk_eq v (exists_unitPart_approx v x).choose_spec ?_
  rwa [unitPart_of_isUnitAt v hx]


open Classical in
theorem exists_tameLoc_of_residue : ∀ (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) (θ0 : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ), ∃ θ : (v.adicCompletion L)ˣ →* ℂˣ, TameLoc v θ ∧ (∀ (k : Lˣ) (y : 𝓞 L) (b : (𝓞 L ⧸ v.asIdeal)ˣ), (k : L) = (y : L) → (b : 𝓞 L ⧸ v.asIdeal) = Ideal.Quotient.mk v.asIdeal y → θ (atFin v k) = θ0 b) ∧ ∀ x, IsUnitAt v x → ∃ b, θ x = θ0 b := by
  intro L _ _ v θ0
  haveI : Finite (𝓞 L ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  refine ⟨θ0.comp (resPart v).toHomUnits, ⟨fun x => ?_, fun x hx h1 => ?_⟩, fun k y b hk hb => ?_,
    fun x _ => ⟨_, rfl⟩⟩
  · have hf : IsOfFinOrder ((θ0 ((resPart v).toHomUnits x) : ℂˣ) : ℂ) :=
      ((Units.coeHom ℂ).comp θ0).isOfFinOrder (isOfFinOrder_of_finite _)
    exact hf.norm_eq_one
  · have e : (resPart v).toHomUnits x = 1 := by
      apply Units.ext
      show resPart v x = Ideal.Quotient.mk v.asIdeal 1
      refine resPart_eq v hx ?_
      rw [map_one]
      refine lt_of_le_of_lt h1 ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    rw [MonoidHom.comp_apply, e, map_one]
  · have ek : ((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) =
        algebraMap (𝓞 L) (v.adicCompletion L) y := by
      show algebraMap L (v.adicCompletion L) (k : L) = _
      rw [hk]
      rfl
    have hy : y ∉ v.asIdeal := by
      intro hy
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hy] at hb
      haveI := v.isPrime
      exact b.ne_zero hb
    have hu : IsUnitAt v (atFin v k) := by
      show Valued.v ((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1
      rw [ek]
      refine le_antisymm ?_ (not_lt.1 fun h => hy ((tame_valued_lt_one_iff v y).1 h))
      rw [tame_valued_int]
      exact v.valuation_le_one y
    have e : (resPart v).toHomUnits (atFin v k) = b := by
      apply Units.ext
      show resPart v (atFin v k) = _
      rw [hb]
      refine resPart_eq v hu ?_
      rw [ek, sub_self, map_zero]
      exact zero_lt_one
    rw [MonoidHom.comp_apply, e]

end GlobalTheory.Mem.Chr
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr.IdlFact

variable {L : Type} [Field L] [NumberField L]

def valAt (w : HeightOneSpectrum (𝓞 L)) : Ideles L →* WithZero (Multiplicative ℤ) where
  toFun a := Valued.v ((a : AdeleRing (𝓞 L) L).2 w)
  map_one' := by
    show Valued.v (1 : w.adicCompletion L) = 1
    exact map_one _
  map_mul' a b := by
    show Valued.v ((a : AdeleRing (𝓞 L) L).2 w * (b : AdeleRing (𝓞 L) L).2 w) = _
    exact map_mul _ _ _

theorem valAt_apply (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) :
    valAt w a = Valued.v ((a : AdeleRing (𝓞 L) L).2 w) := rfl

theorem valAt_ne_zero (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) : valAt w a ≠ 0 :=
  ((Group.isUnit a).map (valAt w)).ne_zero

theorem valAt_localIdele_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    valAt v (localIdele L v x) = Valued.v (x : v.adicCompletion L) := by
  classical
  have h : ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 v = x := by
    have := Function.update_self (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
      (x : v.adicCompletion L) (fun _ => 1)
    convert this
    rfl
  rw [valAt_apply, h]

theorem valAt_localIdele_ne {v w : HeightOneSpectrum (𝓞 L)} (hw : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    valAt w (localIdele L v x) = 1 := by
  classical
  have h : ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 w = 1 := by
    have := Function.update_of_ne (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) hw
      (x : v.adicCompletion L) (fun _ => 1)
    convert this
    rfl
  rw [valAt_apply, h, map_one]

theorem finite_valAt_ne_one (a : Ideles L) : {v | valAt v a ≠ 1}.Finite := by
  have hu : IsUnit ((a : AdeleRing (𝓞 L) L).2) :=
    a.isUnit.map (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
  exact (FiniteAdeleRing.isUnit_iff.1 hu).2

open Classical in
theorem valAt_prod (S : Finset (HeightOneSpectrum (𝓞 L))) (n : HeightOneSpectrum (𝓞 L) → ℤ)
    (w : HeightOneSpectrum (𝓞 L)) :
    valAt w (∏ v ∈ S, localIdele L v (atFin v (unif v)) ^ n v) =
      WithZero.exp (-(if w ∈ S then n w else 0)) := by
  rw [map_prod]
  have h1 : ∀ v, v ≠ w → valAt w (localIdele L v (atFin v (unif v)) ^ n v) = 1 := fun v hv => by
    rw [map_zpow, valAt_localIdele_ne hv.symm, one_zpow]
  split_ifs with hw
  · rw [Finset.prod_eq_single_of_mem w hw (fun v _ hv => h1 v hv), map_zpow, valAt_localIdele_self]
    have h2 : Valued.v ((atFin w (unif w) : (w.adicCompletion L)ˣ) : w.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
      unif_spec w
    rw [h2, ← WithZero.exp_zsmul]
    simp
  · rw [Finset.prod_eq_one (fun v hv => h1 v (fun e => hw (e ▸ hv)))]
    simp

end GlobalTheory.Mem.Chr.IdlFact


open Classical in
theorem GlobalTheory.Mem.Chr.exists_prod_unif_mul_unitIdl : ∀ (L : Type) [Field L] [NumberField L] (a : Ideles L), ∃ (S : Finset (HeightOneSpectrum (𝓞 L))) (n : HeightOneSpectrum (𝓞 L) → ℤ) (u : Ideles L), u ∈ unitIdl L ∧ a = (∏ v ∈ S, localIdele L v (atFin v (unif v)) ^ n v) * u ∧ ∀ v, Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = WithZero.exp (-(if v ∈ S then n v else 0)) := by
  intro L _ _ a
  let S := (GlobalTheory.Mem.Chr.IdlFact.finite_valAt_ne_one a).toFinset
  let n : HeightOneSpectrum (𝓞 L) → ℤ := fun v => -WithZero.log (GlobalTheory.Mem.Chr.IdlFact.valAt v a)
  have hv : ∀ v, GlobalTheory.Mem.Chr.IdlFact.valAt v a = WithZero.exp (-(if v ∈ S then n v else 0)) := fun v => by
    split_ifs with h
    · simp only [n, neg_neg]
      exact (WithZero.exp_log (GlobalTheory.Mem.Chr.IdlFact.valAt_ne_zero v a)).symm
    · have : GlobalTheory.Mem.Chr.IdlFact.valAt v a = 1 := by simpa [S] using h
      rw [this]; simp
  refine ⟨S, n, (∏ v ∈ S, localIdele L v (atFin v (unif v)) ^ n v)⁻¹ * a, fun v => ?_, ?_, hv⟩
  · rw [← GlobalTheory.Mem.Chr.IdlFact.valAt_apply, map_mul, map_inv, GlobalTheory.Mem.Chr.IdlFact.valAt_prod, hv v]
    exact inv_mul_cancel₀ WithZero.exp_ne_zero
  · rw [mul_inv_cancel_left]
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.UnitIndex

variable (L : Type) [Field L] [NumberField L]

def finIdele : Neutral.B1.Ideles L →* (FiniteAdeleRing (𝓞 L) L)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

def idealHom : (FiniteAdeleRing (𝓞 L) L)ˣ →* FractionalIdeal (𝓞 L)⁰ L where
  toFun := GlobalTheory.Idele.idealOf
  map_one' := GlobalTheory.Idele.idealOf_one
  map_mul' := GlobalTheory.Idele.idealOf_mul

def classHom : Neutral.B1.Ideles L →* ClassGroup (𝓞 L) :=
  (ClassGroup.mk L).comp ((idealHom L).comp (finIdele L)).toHomUnits

theorem ker_classHom_le : (classHom L).ker ≤ unitIdl L ⊔ (Neutral.B1.diagUnits L).range := by
  intro a ha
  have h1 : ClassGroup.mk L (((idealHom L).comp (finIdele L)).toHomUnits a) = 1 := ha
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 h1
  have hx' : GlobalTheory.Idele.idealOf (finIdele L a) = FractionalIdeal.spanSingleton (𝓞 L)⁰ x := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact GlobalTheory.Idele.idealOf_ne_zero _ (hx'.trans (FractionalIdeal.spanSingleton_zero))
  have hd : finIdele L (Neutral.B1.diagUnits L (Units.mk0 x hx0)) =
      FiniteAdeleRing.unitEmbedding (𝓞 L) L (Units.mk0 x hx0) := Units.ext rfl
  have hu : a * (Neutral.B1.diagUnits L (Units.mk0 x hx0))⁻¹ ∈ unitIdl L := by
    refine (GlobalTheory.Idele.smul_eq_self_iff (finIdele L (a * (Neutral.B1.diagUnits L (Units.mk0 x hx0))⁻¹))
      (I := 1) one_ne_zero).1 ?_
    rw [GlobalTheory.Idele.smul_one_eq, map_mul, map_inv, GlobalTheory.Idele.idealOf_mul, GlobalTheory.Idele.idealOf_inv, hd,
      GlobalTheory.Idele.idealOf_unitEmbedding, hx']
    exact mul_inv_cancel₀ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx0)
  have : a = a * (Neutral.B1.diagUnits L (Units.mk0 x hx0))⁻¹ * Neutral.B1.diagUnits L (Units.mk0 x hx0) := by simp
  rw [this]
  exact Subgroup.mul_mem_sup hu ⟨_, rfl⟩


open Classical in
theorem finiteIndex_unitIdl_sup : ∀ (L : Type) [Field L] [NumberField L],
    (unitIdl L ⊔ (Neutral.B1.diagUnits L).range).FiniteIndex := by
  intro L _ _
  have : (classHom L).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  exact Subgroup.finiteIndex_of_le (ker_classHom_le L)

end GlobalTheory.Mem.UnitIndex
end
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.algebraicWeight_polyMatrix_change_of_basis : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (ι' : Type) [Fintype ι'] [DecidableEq ι'] (b' : Module.Basis ι' ℂ a.W) (P' : ι' → ι' → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → Agrees a b' P' → ∀ (τ : L →+* ℂ) (B : GL (Fin n) ℂ), evM P' (evPt τ B) = b'.toMatrix b * evM P (evPt τ B) * b.toMatrix b' := by
  first | exact @GlobalTheory.AlgWtHW.evM_change_of_basis | exact GlobalTheory.AlgWtHW.evM_change_of_basis | (intros; apply GlobalTheory.AlgWtHW.evM_change_of_basis <;> assumption)
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.algebraicWeight_polyMatrix_multiplicative : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → evM P (upt (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ))) = 1 ∧ ∀ X Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt X → IsUPt Y → evM P (upt (fun σ => X σ * Y σ)) = evM P (upt X) * evM P (upt Y) := by
  first | exact @GlobalTheory.AlgWtMul.evM_mul | exact GlobalTheory.AlgWtMul.evM_mul | (intros; apply GlobalTheory.AlgWtMul.evM_mul <;> assumption)
end
