module

public import GroundTheory.PAdicHodge.Bundle007
public import GroundTheory.PAdicHodge.InstMulSemiringActionGalPlus
public import GroundTheory.PAdicHodge.Bundle011
public import GroundTheory.PAdicHodge.BdRField
public import GroundTheory.PAdicHodge.Bundle003
public import GroundTheory.PAdicHodge.ACrisBdRGalois
public import GroundTheory.PAdicHodge.ACrisFrobFixed
public import GroundTheory.PAdicHodge.FontaineLemmaPeriod
public import GroundTheory.PAdicHodge.Bundle013
import GroundTheory.PAdicHodge.Bundle009
public import GroundTheory.PAdicHodge.BdRTGalois
public import GroundTheory.PAdicHodge.Bundle008
public import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
public import GroundTheory.PAdicHodge.ThetaBDeRhamPlusFieldCycloUnitBdRZpow
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.PAdicHodge.ACrisBdR

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open _root_.WittVector

namespace ACris

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]

local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θdR" => IsPerfectoidField.thetaBDeRhamPlusField (K := K) p

theorem iterate_phiPlus_algebraMap (n : ℕ) (x : ACris K p) :
    (phiPlus K p)^[n] (algebraMap (ACris K p) (BCrisPlus K p) x) =
      algebraMap (ACris K p) (BCrisPlus K p) ((phi (K := K) (p := p))^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, phiPlus_algebraMap, Function.iterate_succ_apply']

theorem thetaField_iotaPlus_algebraMap (x : ACris K p) :
    θdR (iotaPlus K p (algebraMap (ACris K p) (BCrisPlus K p) x)) = (theta K p x : K) := by
  rw [iotaPlus_algebraMap, thetaField_iota]

theorem theta_phi_iterate_eq_zero_of_mul_eq {y : BCrisPlus K p} {a : ACris K p} {k : ℕ}
    (hya : y * algebraMap (ACris K p) (BCrisPlus K p) ((p : ACris K p) ^ k) =
      algebraMap (ACris K p) (BCrisPlus K p) a)
    (hy : ∀ n : ℕ, θdR (iotaPlus K p ((phiPlus K p)^[n] y)) = 0) (n : ℕ) :
    theta K p ((phi (K := K) (p := p))^[n] a) = 0 := by
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero, ← thetaField_iotaPlus_algebraMap, ← iterate_phiPlus_algebraMap, ← hya,
    ← RingHom.coe_pow, map_mul, map_mul, map_mul, RingHom.coe_pow, hy n, zero_mul]



theorem phiPlus_mem_span_periodT {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) {y : BCrisPlus K p}
    (hy : ∀ n : ℕ, θdR (iotaPlus K p ((phiPlus K p)^[n] y)) = 0) :
    phiPlus K p y ∈ Ideal.span {algebraMap (ACris K p) (BCrisPlus K p) (periodT hε)} := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (p : ACris K p)) y
  obtain ⟨k, hk⟩ := s.2
  simp only at hs
  rw [← hk] at hs
  have ha := theta_phi_iterate_eq_zero_of_mul_eq hs hy

  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (p_mul_phi_mem_span_mu hε hζ ha)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (mu_mem_span_periodT (K := K) hε hζ)
  have hpa : (p : ACris K p) * phi (K := K) (p := p) a = periodT hε * (c * w) := by
    rw [← hw, ← hc]; ring

  have h1 := congrArg (phiPlus K p) hs
  rw [map_mul, phiPlus_algebraMap, phiPlus_algebraMap, map_pow, map_natCast] at h1
  have hu : IsUnit (algebraMap (ACris K p) (BCrisPlus K p) ((p : ACris K p) ^ (k + 1))) :=
    IsLocalization.map_units (BCrisPlus K p)
      (⟨(p : ACris K p) ^ (k + 1), k + 1, rfl⟩ : Submonoid.powers (p : ACris K p))
  rw [Ideal.mem_span_singleton']
  refine ⟨algebraMap (ACris K p) (BCrisPlus K p) (c * w) * ↑hu.unit⁻¹, ?_⟩
  have h2 : phiPlus K p y * algebraMap (ACris K p) (BCrisPlus K p) ((p : ACris K p) ^ (k + 1)) =
      algebraMap (ACris K p) (BCrisPlus K p) (periodT hε) *
        algebraMap (ACris K p) (BCrisPlus K p) (c * w) := by
    rw [pow_succ, map_mul, ← mul_assoc, h1, ← map_mul, mul_comm (phi (K := K) (p := p) a), hpa, map_mul]
  calc algebraMap (ACris K p) (BCrisPlus K p) (c * w) * ↑hu.unit⁻¹ *
        algebraMap (ACris K p) (BCrisPlus K p) (periodT hε)
      = phiPlus K p y * algebraMap (ACris K p) (BCrisPlus K p) ((p : ACris K p) ^ (k + 1)) *
          ↑hu.unit⁻¹ := by rw [h2]; ring
    _ = phiPlus K p y := by rw [mul_assoc, IsUnit.mul_val_inv, mul_one]

end ACris

end GroundTheory.PAdicHodge
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

section AwayAction

variable {G R : Type*} [Monoid G] [CommRing R] [MulSemiringAction G R] (t : R)

def awaySMulHom (h : ∀ σ : G, IsUnit (algebraMap R (Localization.Away t) (σ • t))) (σ : G) :
    Localization.Away t →+* Localization.Away t :=
  Localization.awayLift
    ((algebraMap R (Localization.Away t)).comp (MulSemiringAction.toRingHom G R σ)) t (h σ)

variable {t} (h : ∀ σ : G, IsUnit (algebraMap R (Localization.Away t) (σ • t)))

theorem awaySMulHom_algebraMap (σ : G) (x : R) :
    awaySMulHom t h σ (algebraMap R (Localization.Away t) x) =
      algebraMap R (Localization.Away t) (σ • x) :=
  IsLocalization.lift_eq _ x

theorem awaySMulHom_comm (f : Localization.Away t →+* Localization.Away t) (F : R →+* R)
    (hf : ∀ x, f (algebraMap R (Localization.Away t) x) = algebraMap R (Localization.Away t) (F x))
    (hF : ∀ (σ : G) x, F (σ • x) = σ • F x) (σ : G) (x : Localization.Away t) :
    f (awaySMulHom t h σ x) = awaySMulHom t h σ (f x) := by
  have e : f.comp (awaySMulHom t h σ) = (awaySMulHom t h σ).comp f := by
    apply IsLocalization.ringHom_ext (Submonoid.powers t)
    refine RingHom.ext fun y => ?_
    simp only [RingHom.comp_apply]
    rw [awaySMulHom_algebraMap, hf, hf, awaySMulHom_algebraMap, hF]
  exact congrArg (fun g => g x) e

end AwayAction

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

def chiCris (σ : Gal(PadicAlgCl p/K)) : ACris ℂ_[p] p :=
  algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p)
    (IsPerfectoidField.padicIntToWitt p (cycloChar K σ : ℤ_[p]))

theorem isUnit_chiCris (σ : Gal(PadicAlgCl p/K)) : IsUnit (chiCris σ) :=
  ((cycloChar K σ).isUnit.map (IsPerfectoidField.padicIntToWitt p)).map _

theorem gal_smul_periodT (σ : Gal(PadicAlgCl p/K)) {ε : PreTilt (normInteger ℂ_[p]) p}
    (hε : PreTilt.untilt ε = 1) :
    σ • periodT hε = chiCris σ * periodT hε := by
  apply iota_injective (K := ℂ_[p]) (p := p)
  calc
    iota ℂ_[p] p (σ • periodT hε) = σ • fontaineT ε hε := by
      rw [iota_gal_smul σ, iota_periodT hε]
    _ = algebraMap ℚ_[p] _ ((cycloChar K σ : ℤ_[p]) : ℚ_[p]) * fontaineT ε hε :=
      gal_smul_fontaineT σ hε
    _ = iota ℂ_[p] p (chiCris σ * periodT hε) := by
      rw [map_mul, chiCris, iota_padicInt, iota_periodT hε]

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)

omit hp in
theorem isUnit_map_of_eq_mul {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {x c t : A}
    (h : x = c * t) (hc : IsUnit c) (ht : IsUnit (f t)) : IsUnit (f x) := by
  rw [h, map_mul]
  exact (hc.map f).mul ht

theorem isUnit_gal_smul_periodT (σ : Gal(PadicAlgCl p/K)) :
    IsUnit (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)
      (σ • algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (periodT hε))) :=
  isUnit_map_of_eq_mul (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε))
    ((gal_smul_algebraMap_plus σ _).trans
      ((congrArg (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p)) (gal_smul_periodT σ hε)).trans
        (map_mul _ _ _)))
    ((isUnit_chiCris σ).map _) (IsLocalization.Away.algebraMap_isUnit (S := BCris hε) _)

def galB (σ : Gal(PadicAlgCl p/K)) : BCris hε →+* BCris hε :=
  awaySMulHom _ (isUnit_gal_smul_periodT hε) σ

theorem galB_algebraMap (σ : Gal(PadicAlgCl p/K)) (x : BCrisPlus ℂ_[p] p) :
    galB hε σ (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) x) =
      algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) (σ • x) := by
  -- Infer the localization arguments from the unfolded action.
  delta galB
  apply @awaySMulHom_algebraMap

theorem phiB_galB (σ : Gal(PadicAlgCl p/K)) (x : BCris hε) :
    phiB hε (galB hε σ x) = galB hε σ (phiB hε x) := by
  let t := algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (periodT (K := ℂ_[p]) (p := p) hε)
  let φ := phiB (K := ℂ_[p]) (p := p) hε
  let g := galB hε σ
  have e : φ.comp g = g.comp φ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers t)
    refine RingHom.ext fun y => ?_
    change φ (g (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) y)) =
      g (φ (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) y))
    calc
      _ = φ (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) (σ • y)) :=
        congrArg (fun z : BCris hε => φ z) (galB_algebraMap hε σ y)
      _ = algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) (phiPlus ℂ_[p] p (σ • y)) :=
        phiB_algebraMap (K := ℂ_[p]) (p := p) hε (σ • y)
      _ = algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) (σ • phiPlus ℂ_[p] p y) :=
        congrArg (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) (phiPlus_gal_smul σ y)
      _ = g (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) (phiPlus ℂ_[p] p y)) :=
        (galB_algebraMap hε σ (phiPlus ℂ_[p] p y)).symm
      _ = _ := congrArg (fun z : BCris hε => g z)
        (phiB_algebraMap (K := ℂ_[p]) (p := p) hε y).symm
  exact congrArg (fun F : BCris hε →+* BCris hε => F x) e

end ACris

end GroundTheory.PAdicHodge
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

open IsLocalRing TensorProduct Module

namespace GroundTheory.PAdicHodge

variable {p : ℕ} [Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p
local notation "Fil" => IsPerfectoidField.fil ℂ_[p] p

section Algebra

variable (p) in
def algClToBdRField : PadicAlgCl p →+* 𝔹dR := (algebraMap 𝔹 𝔹dR).comp (algClToBdR p).toRingHom

instance algebraAlgClBDeRham : Algebra (PadicAlgCl p) 𝔹dR := (algClToBdRField p).toAlgebra

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem algebraMap_intermediateField_bDeRham (k : K) :
    algebraMap K 𝔹dR k = algebraMap 𝔹 𝔹dR (algClToBdR p k) := rfl

variable {K}

theorem gal_smul_algebraMap_intermediateField_bDeRham (σ : Gal(PadicAlgCl p/K)) (k : K) :
    σ • algebraMap K 𝔹dR k = algebraMap K 𝔹dR k := by
  rw [algebraMap_intermediateField_bDeRham, gal_smul_algebraMap_bDeRham, gal_smul_algClToBdR]
  congr 2
  exact AlgEquiv.commutes σ k

end Algebra

section Level

theorem bDeRham_exists_mem_fil (x : 𝔹dR) : ∃ i : ℤ, x ∈ Fil i := by
  have hx : x ∈ ⨆ i, Fil i := by
    rw [IsPerfectoidField.iSup_fil]
    exact Submodule.mem_top
  exact (Submodule.mem_iSup_of_directed _
    (IsPerfectoidField.fil_antitone ℂ_[p] p).directed_le).1 hx

theorem bDeRham_exists_not_mem_fil {x : 𝔹dR} (hx : x ≠ 0) : ∃ i : ℤ, x ∉ Fil i := by
  by_contra h
  push Not at h
  apply hx
  have : x ∈ ⨅ i, Fil i := (Submodule.mem_iInf _).2 h
  rwa [IsPerfectoidField.iInf_fil, Submodule.mem_bot] at this

theorem bDeRham_exists_level {x : 𝔹dR} (hx : x ≠ 0) : ∃ i : ℤ, x ∈ Fil i ∧ x ∉ Fil (i + 1) := by
  obtain ⟨j, hj⟩ := bDeRham_exists_not_mem_fil hx
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, x ∈ Fil z → z ≤ b := by
    refine ⟨j, fun z hz => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hj (IsPerfectoidField.fil_antitone ℂ_[p] p hlt.le hz)
  obtain ⟨i, hi, hmax⟩ := Int.exists_greatest_of_bdd hbdd (bDeRham_exists_mem_fil x)
  exact ⟨i, hi, fun h => by have := hmax _ h; omega⟩

theorem grMap_zero_algebraMap (b : 𝔹) (h : algebraMap 𝔹 𝔹dR b ∈ Fil 0) :
    IsPerfectoidField.grMap maximalIdeal_eq_span_tBdR 0 ⟨algebraMap 𝔹 𝔹dR b, h⟩ =
      thetaAlgHom p b := by
  have e : algebraMap 𝔹 𝔹dR b = algebraMap 𝔹 𝔹dR (tBdR p) ^ (0 : ℤ) * algebraMap 𝔹 𝔹dR b := by
    rw [zpow_zero, one_mul]
  have h' : algebraMap 𝔹 𝔹dR (tBdR p) ^ (0 : ℤ) * algebraMap 𝔹 𝔹dR b ∈ Fil 0 := by
    rw [← e]
    exact h
  have : (⟨algebraMap 𝔹 𝔹dR b, h⟩ : Fil 0) = ⟨_, h'⟩ := Subtype.ext e
  rw [this, IsPerfectoidField.grMap_mk, thetaAlgHom_apply]

end Level

section Invariants

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem grMap_mem_invariants {i : ℤ} (x : Fil i)
    (hx : ∀ σ : Gal(PadicAlgCl p/K), σ • (x : 𝔹dR) = x) :
    IsPerfectoidField.grMap maximalIdeal_eq_span_tBdR i x ∈ (cpTwistRep K i).invariants := by
  rw [ContRepresentation.mem_invariants]
  intro σ
  rw [← grMap_tBdR_gal_smul σ x]
  congr 1
  exact Subtype.ext (hx σ)

variable [FiniteDimensional ℚ_[p] K]

theorem mem_fil_succ_of_invariant {i : ℤ} (hi : i ≠ 0) {x : 𝔹dR} (hxi : x ∈ Fil i)
    (hx : ∀ σ : Gal(PadicAlgCl p/K), σ • x = x) : x ∈ Fil (i + 1) := by
  have h := grMap_mem_invariants K ⟨x, hxi⟩ hx
  rw [cpTwistRep_invariants_eq_bot K hi, Submodule.mem_bot] at h
  exact (IsPerfectoidField.grMap_eq_zero_iff maximalIdeal_eq_span_tBdR ⟨x, hxi⟩).1 h

theorem level_eq_zero_of_invariant {x : 𝔹dR} (hx : ∀ σ : Gal(PadicAlgCl p/K), σ • x = x)
    {i : ℤ} (hi : x ∈ Fil i) (hi' : x ∉ Fil (i + 1)) : i = 0 := by
  by_contra h
  exact hi' (mem_fil_succ_of_invariant K h hi hx)

theorem bDeRham_fixed (x : 𝔹dR) (hx : ∀ σ : Gal(PadicAlgCl p/K), σ • x = x) :
    ∃ k : K, algebraMap K 𝔹dR k = x := by
  by_cases h0 : x = 0
  · exact ⟨0, by rw [map_zero, h0]⟩
  obtain ⟨i, hi, hi'⟩ := bDeRham_exists_level h0
  obtain rfl := level_eq_zero_of_invariant K hx hi hi'
  have hinv := grMap_mem_invariants K ⟨x, hi⟩ hx
  rw [cpTwistRep_invariants_zero K] at hinv
  obtain ⟨k, hk⟩ := hinv
  refine ⟨k, ?_⟩
  rw [algebraMap_intermediateField_bDeRham]
  by_contra hne
  have hy0 : x - algebraMap 𝔹 𝔹dR (algClToBdR p k) ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hyinv : ∀ σ : Gal(PadicAlgCl p/K), σ • (x - algebraMap 𝔹 𝔹dR (algClToBdR p k)) =
      x - algebraMap 𝔹 𝔹dR (algClToBdR p k) := fun σ => by
    rw [smul_sub, hx σ, ← algebraMap_intermediateField_bDeRham,
      gal_smul_algebraMap_intermediateField_bDeRham]
  have hk0 : algebraMap 𝔹 𝔹dR (algClToBdR p k) ∈ Fil 0 :=
    (IsPerfectoidField.mem_fil_zero_iff ℂ_[p] p).2 ⟨_, rfl⟩
  have hgr0 := grMap_zero_algebraMap (algClToBdR p k) hk0
  rw [thetaAlgHom_algClToBdR] at hgr0
  have hy : x - algebraMap 𝔹 𝔹dR (algClToBdR p k) ∈ Fil 0 := Submodule.sub_mem _ hi hk0
  have hgr : IsPerfectoidField.grMap maximalIdeal_eq_span_tBdR 0
      (⟨x - algebraMap 𝔹 𝔹dR (algClToBdR p k), hy⟩ : Fil 0) = 0 := by
    have e : (⟨x - algebraMap 𝔹 𝔹dR (algClToBdR p k), hy⟩ : Fil 0) =
        ⟨x, hi⟩ - ⟨algebraMap 𝔹 𝔹dR (algClToBdR p k), hk0⟩ := rfl
    rw [e, map_sub, hgr0, ← hk, Algebra.linearMap_apply, algebraMap_intermediateField_cp, sub_self]
  have hy1 : x - algebraMap 𝔹 𝔹dR (algClToBdR p k) ∈ Fil (0 + 1) :=
    (IsPerfectoidField.grMap_eq_zero_iff maximalIdeal_eq_span_tBdR _).1 hgr
  obtain ⟨j, hj, hj'⟩ := bDeRham_exists_level hy0
  obtain rfl := level_eq_zero_of_invariant K hyinv hj hj'
  exact hj' hy1

theorem bDeRhamPlus_fixed (b : 𝔹) (hb : ∀ σ : Gal(PadicAlgCl p/K), σ • b = b) :
    ∃ k : K, algClToBdR p k = b := by
  obtain ⟨k, hk⟩ := bDeRham_fixed K (algebraMap 𝔹 𝔹dR b) fun σ => by
    rw [gal_smul_algebraMap_bDeRham, hb σ]
  exact ⟨k, IsPerfectoidField.algebraMap_bDeRham_injective hk⟩

end Invariants

section DeRham

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/K) V)

variable [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] V]



end DeRham

section Filtration

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (V : Type*) [AddCommGroup V]
  [Module ℚ_[p] V]

variable {K V}


variable [FiniteDimensional ℚ_[p] V]

variable (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/K) V)




variable [FiniteDimensional ℚ_[p] K]



end Filtration

end GroundTheory.PAdicHodge
end
end
