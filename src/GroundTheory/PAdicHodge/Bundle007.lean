module

public import GroundTheory.PAdicHodge.ThetaPlus
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.RingTheory.WittVector.Compare
public import GroundTheory.PAdicHodge.TiltField
public import GroundTheory.PAdicHodge.ExtRobbaBounded
public import GroundTheory.PAdicHodge.Bundle003
public import GroundTheory.PAdicHodge.KerTheta
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Ideal WittVector IsLocalRing

theorem ringHom_ext_padicInt {p : ℕ} [Fact p.Prime] {S : Type*} [CommRing S]
    [IsHausdorff (span {(p : S)}) S] (f g : ℤ_[p] →+* S) : f = g := by
  ext x
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := span {(p : S)}) inferInstance _ fun n => ?_
  obtain ⟨c, hc⟩ := mem_span_singleton.1 (PadicInt.appr_spec n x)
  have hx : x = (x.appr n : ℤ_[p]) + (p : ℤ_[p]) ^ n * c := by rw [← hc]; ring
  have h : f x - g x = (p : S) ^ n * (f c - g c) := by
    rw [hx, map_add (f := _), map_add (f := _), map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast,
      map_natCast, map_natCast]
    ring
  rw [SModEq.zero, smul_eq_mul, mul_top, h, span_singleton_pow]
  exact Ideal.mul_mem_right _ _ (mem_span_singleton_self _)

namespace IsPerfectoidField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt 𝒪 p
local notation "𝕎𝒪♭" => WittVector p 𝒪♭
local notation "𝔹" => BDeRhamPlus 𝒪 p

def padicIntToWitt : ℤ_[p] →+* 𝕎𝒪♭ :=
  (WittVector.map (ZMod.castHom (dvd_refl p) 𝒪♭)).comp (WittVector.equiv p).symm.toRingHom

def padicIntToBDeRhamPlus : ℤ_[p] →+* 𝔹 :=
  (wittToBDeRhamPlus 𝒪 p).comp (padicIntToWitt p)

theorem isUnit_natCast_p_bDeRhamPlus : IsUnit (p : 𝔹) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p : 𝕎𝒪♭)) (p : 𝕎𝒪♭)
  have h2 := h.map (toBDeRhamPlus 𝒪 p)
  rwa [map_natCast, map_natCast] at h2

theorem isUnit_padicIntToBDeRhamPlus {x : ℤ_[p]} (hx : x ≠ 0) :
    IsUnit (padicIntToBDeRhamPlus (K := K) p x) := by
  rw [PadicInt.unitCoeff_spec hx, map_mul, map_pow, map_natCast]
  exact ((PadicInt.unitCoeff hx).isUnit.map _).mul ((isUnit_natCast_p_bDeRhamPlus (K := K) p).pow _)

def padicToBDeRhamPlus : ℚ_[p] →+* 𝔹 :=
  IsLocalization.lift (M := nonZeroDivisors ℤ_[p]) (S := ℚ_[p]) (g := padicIntToBDeRhamPlus (K := K) p)
    fun y => isUnit_padicIntToBDeRhamPlus (K := K) p (nonZeroDivisors.coe_ne_zero y)

instance algebraPadic : Algebra ℚ_[p] 𝔹 := (padicToBDeRhamPlus p).toAlgebra

theorem algebraMap_padic_coe (x : ℤ_[p]) :
    algebraMap ℚ_[p] 𝔹 (x : ℚ_[p]) = wittToBDeRhamPlus 𝒪 p (padicIntToWitt p x) :=
  IsLocalization.lift_eq (M := nonZeroDivisors ℤ_[p]) (S := ℚ_[p]) _ x

instance algebraRat : Algebra ℚ 𝔹 :=
  ((algebraMap ℚ_[p] 𝔹).comp (algebraMap ℚ ℚ_[p])).toAlgebra

end IsPerfectoidField

section Cp

variable (p : ℕ) [Fact p.Prime]

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝔹" => BDeRhamPlus 𝒪 p

theorem algebraMap_padicInt_mem_normInteger (x : ℤ_[p]) :
    algebraMap ℚ_[p] ℂ_[p] (x : ℚ_[p]) ∈ normInteger ℂ_[p] := by
  rw [mem_normInteger, norm_algebraMap', PadicInt.norm_coe]
  exact x.norm_le_one

theorem fontaineTheta_padicIntToWitt (x : ℤ_[p]) :
    ((_root_.WittVector.fontaineTheta 𝒪 p (IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p x) : 𝒪) : ℂ_[p]) =
      algebraMap ℚ_[p] ℂ_[p] (x : ℚ_[p]) := by
  let g : ℤ_[p] →+* 𝒪 :=
    ((algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom).codRestrict _
      (algebraMap_padicInt_mem_normInteger p)
  have := IsPerfectoidField.isAdicComplete (K := ℂ_[p]) p
  have h := ringHom_ext_padicInt ((_root_.WittVector.fontaineTheta 𝒪 p).comp (IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p)) g
  exact congrArg Subtype.val (RingHom.congr_fun h x)

theorem thetaBDeRhamPlusField_algebraMap (q : ℚ_[p]) :
    IsPerfectoidField.thetaBDeRhamPlusField p (algebraMap ℚ_[p] 𝔹 q) = algebraMap ℚ_[p] ℂ_[p] q := by
  have h : (IsPerfectoidField.thetaBDeRhamPlusField p).comp (algebraMap ℚ_[p] 𝔹) =
      algebraMap ℚ_[p] ℂ_[p] := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply]
    have hx : algebraMap ℤ_[p] ℚ_[p] x = (x : ℚ_[p]) := rfl
    rw [hx, IsPerfectoidField.algebraMap_padic_coe,
      IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus, fontaineTheta_padicIntToWitt]
  exact RingHom.congr_fun h q

def thetaAlgHom : 𝔹 →ₐ[ℚ_[p]] ℂ_[p] where
  toRingHom := IsPerfectoidField.thetaBDeRhamPlusField p
  commutes' := thetaBDeRhamPlusField_algebraMap p

theorem thetaAlgHom_apply (x : 𝔹) :
    thetaAlgHom p x = IsPerfectoidField.thetaBDeRhamPlusField p x := rfl

end Cp

end GroundTheory.PAdicHodge
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

section Integers

variable {K L : Type*} [NormedField K] [IsUltrametricDist K] [NormedField L] [IsUltrametricDist L]

def integerMap (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) : normInteger K →+* normInteger L :=
  φ.restrict (normInteger K) (normInteger L) fun x hx =>
    mem_normInteger.2 ((hφ x).trans_le (mem_normInteger.1 hx))

@[simp]
theorem coe_integerMap (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (x : normInteger K) :
    (integerMap φ hφ x : L) = φ x :=
  rfl

end Integers

section Tilt

variable {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [IsUltrametricDist L]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField L p]
variable (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖)

local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪L♭" => PreTilt (normInteger L) p
local notation "K♭" => FractionRing (PreTilt (normInteger K) p)
local notation "L♭" => FractionRing (PreTilt (normInteger L) p)

def modPMap : ModP (normInteger K) p →+* ModP (normInteger L) p :=
  Ideal.quotientMap _ (integerMap φ hφ) (Ideal.span_le.2 (Set.singleton_subset_iff.2 (by
    rw [SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _)))

omit [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField L p] in
theorem modPMap_mk (a : normInteger K) :
    modPMap φ hφ (Ideal.Quotient.mk (Ideal.span {(p : normInteger K)}) a) =
      Ideal.Quotient.mk (Ideal.span {(p : normInteger L)}) (integerMap φ hφ a) :=
  Ideal.quotientMap_mk


variable (p) in
def preTiltMap : 𝒪K♭ →+* 𝒪L♭ :=
  Perfection.map p (modPMap φ hφ)

theorem coeff_preTiltMap (x : 𝒪K♭) (n : ℕ) :
      Perfection.coeff (ModP (normInteger L) p) p n (preTiltMap (p := p) φ hφ x) =
      modPMap φ hφ (Perfection.coeff (ModP (normInteger K) p) p n x) :=
  Perfection.coeff_map _ _ _ _

theorem untilt_preTiltMap (x : 𝒪K♭) :
    PreTilt.untilt (preTiltMap (p := p) φ hφ x) = integerMap φ hφ (PreTilt.untilt x) := by
  let y : ℕ → normInteger K :=
    fun n => PreTilt.untilt ((frobeniusEquiv 𝒪K♭ p).symm^[n] x)
  have hy : ∀ n, y (n + 1) ^ p = y n := IsPerfectoidField.untilt_iterate_succ_pow p x
  have hx : x = IsPerfectoidField.ofCompatible p y hy :=
    IsPerfectoidField.preTilt_ext p fun n => by
      rw [IsPerfectoidField.coeff_ofCompatible, IsPerfectoidField.mk_untilt_iterate]
  have hy' : ∀ n, (integerMap φ hφ ∘ y) (n + 1) ^ p = (integerMap φ hφ ∘ y) n := fun n => by
    simp only [Function.comp_apply, ← map_pow, hy]
  have key : preTiltMap (p := p) φ hφ x = IsPerfectoidField.ofCompatible p _ hy' := by
    refine IsPerfectoidField.preTilt_ext p fun n => ?_
    rw [IsPerfectoidField.coeff_ofCompatible]
    change Perfection.coeff (ModP (normInteger L) p) p n (preTiltMap (p := p) φ hφ x) = _
    rw [coeff_preTiltMap]
    change modPMap φ hφ (PreTilt.coeff n x) = _
    rw [← IsPerfectoidField.mk_untilt_iterate, modPMap_mk]
    rfl
  rw [key, IsPerfectoidField.untilt_ofCompatible]
  rfl

theorem coe_untilt_preTiltMap (x : 𝒪K♭) :
    ((PreTilt.untilt (preTiltMap (p := p) φ hφ x) : normInteger L) : L) =
      φ ((PreTilt.untilt x : normInteger K) : K) := by
  rw [untilt_preTiltMap, coe_integerMap]

theorem preTiltMap_injective : Function.Injective (preTiltMap (p := p) φ hφ) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have h1 := coe_untilt_preTiltMap φ hφ x
  rw [hx, IsPerfectoidField.untilt_zero, ZeroMemClass.coe_zero, eq_comm,
    map_eq_zero_iff φ φ.injective] at h1
  exact (IsPerfectoidField.untilt_eq_zero_iff p).1 (Subtype.ext h1)


variable (p) in
def tiltMap : K♭ →+* L♭ :=
  IsFractionRing.map (preTiltMap_injective (p := p) φ hφ)

theorem ringHom_ext_wittVector_preTilt {f g : WittVector p 𝒪K♭ →+* normInteger L}
    (h : ∀ a, f (WittVector.teichmuller p a) = g (WittVector.teichmuller p a)) : f = g := by
  ext w
  set a : ℕ → 𝒪K♭ := fun n => ((_root_.frobeniusEquiv 𝒪K♭ p).symm ^ n) (w.coeff n)
  have hw : WittVector.teichmullerSeries a = w := WittVector.teichmullerSeries_coeff_eq w
  have hle : ∀ n : ℕ, ‖((f w : normInteger L) : L) - g w‖ ≤ ‖(p : L)‖ ^ (n + 1) := by
    intro n
    obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmullerSeries (p := p) a n
    rw [hw] at hc
    have hS : f (∑ i ∈ Finset.Iic n, WittVector.teichmuller p (a i) * (p : WittVector p 𝒪K♭) ^ i) =
        g (∑ i ∈ Finset.Iic n, WittVector.teichmuller p (a i) * (p : WittVector p 𝒪K♭) ^ i) := by

      simp only [map_sum, map_mul, map_pow, map_natCast, h]
    have hfw : f w = f (∑ i ∈ Finset.Iic n, WittVector.teichmuller p (a i) * (p : WittVector p 𝒪K♭) ^ i)
        + (p : normInteger L) ^ (n + 1) * f c := by
      rw [← map_natCast f p, ← map_pow, ← map_mul, ← hc, ← map_add (f := _), add_sub_cancel]
    have hgw : g w = g (∑ i ∈ Finset.Iic n, WittVector.teichmuller p (a i) * (p : WittVector p 𝒪K♭) ^ i)
        + (p : normInteger L) ^ (n + 1) * g c := by
      rw [← map_natCast g p, ← map_pow, ← map_mul, ← hc, ← map_add (f := _), add_sub_cancel]
    rw [hfw, hgw, hS]
    have hc1 := mem_normInteger.1 (f c).2
    have hc2 := mem_normInteger.1 (g c).2
    simp only [Subring.coe_add, Subring.coe_mul, SubmonoidClass.coe_pow, Subring.coe_natCast,
      add_sub_add_left_eq_sub, ← mul_sub, norm_mul, norm_pow]
    calc ‖(p : L)‖ ^ (n + 1) * ‖((f c : normInteger L) : L) - g c‖
        ≤ ‖(p : L)‖ ^ (n + 1) * 1 := by
          gcongr
          have := IsUltrametricDist.norm_add_le_max ((f c : normInteger L) : L) (-((g c : normInteger L) : L))
          rw [norm_neg, ← sub_eq_add_neg] at this
          exact this.trans (max_le hc1 hc2)
      _ = _ := mul_one _
  have ht : Filter.Tendsto (fun n : ℕ => ‖(p : L)‖ ^ (n + 1)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      (IsPerfectoidField.norm_natCast_lt_one (K := L) (p := p))).comp
        (Filter.tendsto_add_atTop_nat 1)
  have h0 : ‖((f w : normInteger L) : L) - g w‖ ≤ 0 := ge_of_tendsto' ht hle
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

theorem fontaineTheta_map_preTiltMap (w : WittVector p 𝒪K♭) :
    WittVector.fontaineTheta (normInteger L) p (WittVector.map (preTiltMap (p := p) φ hφ) w) =
      integerMap φ hφ (WittVector.fontaineTheta (normInteger K) p w) := by
  have := ringHom_ext_wittVector_preTilt
    (f := (WittVector.fontaineTheta (normInteger L) p).comp (WittVector.map (preTiltMap (p := p) φ hφ)))
    (g := (integerMap φ hφ).comp (WittVector.fontaineTheta (normInteger K) p)) fun a => by
      rw [RingHom.comp_apply, RingHom.comp_apply, WittVector.map_teichmuller,
        WittVector.fontaineTheta_teichmuller, WittVector.fontaineTheta_teichmuller, untilt_preTiltMap]
  exact congrArg (fun F => F w) this

end Tilt

end GroundTheory.PAdicHodge
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WittTilt

open _root_.WittVector

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => FractionRing 𝒪♭
local notation "𝔸" => Localization.Away (p : AInf K p)

variable (K p) in
def incl : AInf K p →+* WittVector p K♭ := WittVector.map (algebraMap 𝒪♭ K♭)

theorem incl_coeff (x : AInf K p) (n : ℕ) :
    (incl K p x).coeff n = algebraMap 𝒪♭ K♭ (x.coeff n) :=
  map_coeff _ _ _

theorem incl_injective : Function.Injective (incl K p) := by
  intro x y h
  ext n
  have := congrArg (fun z => z.coeff n) h
  simp only [incl_coeff] at this
  exact IsFractionRing.injective 𝒪♭ K♭ this

theorem incl_teichmuller (a : 𝒪♭) :
    incl K p (teichmuller p a) = teichmuller p (algebraMap 𝒪♭ K♭ a) :=
  map_teichmuller p _ a

theorem natCast_p_ne_zero : (p : WittVector p K♭) ≠ 0 := by
  intro h
  have := coeff_p_pow (p := p) (R := K♭) 1
  rw [pow_one, h] at this
  simp at this

theorem p_mem_nonZeroDivisors : (p : WittVector p K♭) ∈ nonZeroDivisors (WittVector p K♭) :=
  mem_nonZeroDivisors_of_ne_zero natCast_p_ne_zero

variable (K p) in
def intSubring : Subring (WittVector p K♭) := (incl K p).range

variable (K p) in
def teichLift : TeichLift p K♭ (WittVector p K♭) where
  π := p
  red := WittVector.constantCoeff
  red_surjective := constantCoeff_surjective p
  ker_red := ker_constantCoeff
  π_mem_nonZeroDivisors := p_mem_nonZeroDivisors
  isAdicComplete := inferInstance
  int := intSubring K p
  π_mem_int := ⟨p, map_natCast _ _⟩
  norm_red_le_one := by
    rintro _ ⟨y, rfl⟩
    show ‖(incl K p y).coeff 0‖ ≤ 1
    rw [incl_coeff, norm_algebraMap_preTilt]
    exact preTilt_norm_le_one _
  exists_mem_int := by
    intro a ha
    obtain ⟨b, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 ha
    refine ⟨incl K p (teichmuller p b), ⟨_, rfl⟩, ?_⟩
    show (incl K p (teichmuller p b)).coeff 0 = _
    rw [incl_coeff, teichmuller_coeff_zero]
  exists_eq_π_mul := by
    rintro _ ⟨y, rfl⟩ h0
    have h1 : y.coeff 0 = 0 := by
      have : (incl K p y).coeff 0 = 0 := h0
      rw [incl_coeff] at this
      exact (map_eq_zero_iff _ (IsFractionRing.injective 𝒪♭ K♭)).1 this
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 ((mem_span_p_iff_coeff_zero_eq_zero y).2 h1)
    exact ⟨incl K p z, ⟨z, rfl⟩, by rw [← hz, map_mul, map_natCast, mul_comm]⟩
  mem_int_of_approx := by
    intro x hx
    have hc : ∀ n, ∃ b : 𝒪♭, algebraMap 𝒪♭ K♭ b = x.coeff n := by
      intro n
      obtain ⟨y, ⟨z, rfl⟩, hy⟩ := hx (n + 1)
      have h := (mem_span_p_pow_iff_le_coeff_eq_zero _ _).1 hy
      have := (le_coeff_eq_iff_le_sub_coeff_eq_zero.2 h) n (Nat.lt_succ_self n)
      exact ⟨z.coeff n, by rw [this, incl_coeff]⟩
    choose b hb using hc
    refine ⟨WittVector.mk p b, ?_⟩
    ext n
    rw [incl_coeff, ← hb n]

@[simp] theorem teichLift_π : (teichLift K p).π = (p : WittVector p K♭) := rfl

theorem teichLift_red (x : WittVector p K♭) : (teichLift K p).red x = x.coeff 0 := rfl

theorem teich_eq (a : K♭) : (teichLift K p).teich a = teichmuller p a := by
  haveI := (teichLift K p).isAdicComplete
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := (teichLift K p).I) _ fun n => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, (teichLift K p).I_pow]
  have h := (teichLift K p).teich_sub_pow_mem a n
    (teichmuller p ((((frobeniusEquiv K♭ p).symm : K♭ →+* K♭))^[n] a))
    (by rw [teichLift_red, teichmuller_coeff_zero])
  rw [← map_pow, TeichLift.iterate_frobeniusEquiv_symm_pow] at h
  exact (teichLift K p).span_pow_anti (Nat.le_succ n) h

def tcoeff (x : AInf K p) (n : ℕ) : 𝒪♭ := ((_root_.frobeniusEquiv 𝒪♭ p).symm ^ n) (x.coeff n)

theorem tcoeff_zero (x : AInf K p) : tcoeff x 0 = x.coeff 0 := by
  simp [tcoeff]

theorem coeff_incl (x : AInf K p) (n : ℕ) :
    (teichLift K p).coeff (incl K p x) n = algebraMap 𝒪♭ K♭ (tcoeff x n) := by
  refine (teichLift K p).coeff_eq_of_mem (a := fun i => algebraMap 𝒪♭ K♭ (tcoeff x i)) ?_ n le_rfl
  have hx := (WittVector.eq_teichmullerSeries_iff (tcoeff x) x).1
    (WittVector.teichmullerSeries_coeff_eq x).symm n
  have h2 := map_dvd (incl K p) hx

  rw [map_pow, map_natCast, map_sub, map_sum] at h2
  rw [Ideal.mem_span_singleton, teichLift_π]
  convert h2 using 2
  rw [TeichLift.finSum, show Finset.range (n + 1) = Finset.Iic n by ext; simp [Nat.lt_succ_iff]]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, map_natCast, incl_teichmuller, teich_eq, teichLift_π, mul_comm]

theorem incl_mem_int (x : AInf K p) : incl K p x ∈ (teichLift K p).int := ⟨x, rfl⟩

theorem norm_coeff_incl_le_one (x : AInf K p) (n : ℕ) : ‖(teichLift K p).coeff (incl K p x) n‖ ≤ 1 :=
  (teichLift K p).mem_int_iff.1 (incl_mem_int x) n

theorem isUnit_incl_p : IsUnit (algebraMap (WittVector p K♭) (teichLift K p).B
    (incl K p (p : AInf K p))) := by
  rw [map_natCast]
  exact IsLocalization.Away.algebraMap_isUnit (teichLift K p).π

variable (K p) in
def toB : 𝔸 →+* (teichLift K p).B :=
  Localization.awayLift ((algebraMap (WittVector p K♭) (teichLift K p).B).comp (incl K p))
    (p : AInf K p) isUnit_incl_p

theorem toB_algebraMap (x : AInf K p) :
    toB K p (algebraMap (AInf K p) 𝔸 x) = algebraMap (WittVector p K♭) (teichLift K p).B (incl K p x) :=
  IsLocalization.lift_eq _ x

theorem toB_injective : Function.Injective (toB K p) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨y, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (p : AInf K p)) z
  simp only at hs
  have h1 := congrArg (toB K p) hs
  rw [map_mul, hz, zero_mul, toB_algebraMap] at h1
  have hy : y = 0 := incl_injective (TeichLift.algebraMap_injective _ (by rw [map_zero, map_zero]; exact h1.symm))
  rw [hy, map_zero] at hs
  exact (IsLocalization.map_units 𝔸 s).mul_left_eq_zero.1 hs

theorem coeffB_toB_algebraMap (x : AInf K p) :
    (teichLift K p).coeffB (toB K p (algebraMap (AInf K p) 𝔸 x)) = (teichLift K p).zcoeff (incl K p x) := by
  rw [toB_algebraMap, TeichLift.coeffB_algebraMap]

end WittTilt

end GroundTheory.PAdicHodge
end
end
