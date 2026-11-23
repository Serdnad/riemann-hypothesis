module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Columns.Adelic
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Formalism.LocalToGlobal.Columns.RecLevelCls
public import Formalism.LocalToGlobal.Columns.Bundle001
public import Formalism.LocalToGlobal.Columns.ColumnsProofs.ChainCounts
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.Columns.Bundle007
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.LocalToGlobal.KernelLattices.Bundle001

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.Col

namespace DetChrChi

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem isSDLat_globLat (hc : CMData F E) {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ UAd hc n) :
    IsSDLat E n (Formalism.UG.CS.globLat x (stdLat E n)) := by
  have hspan : Submodule.span E (stdLat E n : Set (Sp E n)) = ⊤ := by
    apply top_unique
    rw [← (Pi.basisFun E (Fin n)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    simpa using (single_mem_stdLat (E := E) (n := n) i 1)
  have hlat := Formalism.UG.P.csGlob_lattice (F := F) (stdLat E n)
    (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) hspan x
  have hU := globLat_unimodular hc n hx
  refine ⟨hlat.toIsLattice.fg, hlat.span_eq_top, fun y => ?_⟩
  conv_lhs => rw [← hU]
  rw [mem_dual]
  refine forall₂_congr fun z _ => ?_
  rw [Submodule.mem_one, RingHom.mem_range]
  exact Iff.rfl

end Lat

section Rep

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

end Rep

section Rel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

end Rel

end DetChrChi

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP St redAt redFn)

section Pack

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

structure RecCls (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (Lb : Submodule (𝓞 E) (Fin n → E))
    (U : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) {cls : Type} (stab : cls → Type) [∀ c, Group (stab c)]
    (lat : cls → Submodule (𝓞 E) (Fin n → E)) where
  y : cls → Formalism.UG.UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)
  y_bij : Function.Bijective (fun c : cls =>
    (Quotient.mk'' (y c) : Formalism.UG.ClassSet
      ((Formalism.UG.ratPts hc.sig J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (Formalism.UG.UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)))
      (U.subgroupOf (Formalism.UG.UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)))))
  y_lat : ∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
    x ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) (lat c) ↔
    ((((y c : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ x ∈
      Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) Lb
  stabI : ∀ c, stab c →* Formalism.UG.UJ (hc.sig : E →+* E) J
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : GL (Fin n) E) (hγ : γ ∈ Formalism.UG.UJ (hc.sig : E →+* E) J),
    (⟨γ, hγ⟩ : Formalism.UG.UJ (hc.sig : E →+* E) J) ∈ (stabI c).range ↔
      Formalism.UG.bc (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈
        U.map (MulAut.conj (y c : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))).toMonoidHom
  stabI_lat : ∀ c (γ : stab c) (x : Fin n → E),
    x ∈ lat c ↔ (((stabI c γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x) ∈ lat c

end Pack

section Dia

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG (E := E) (n := n) (SG := SG)))

theorem rla_dia_inv (c : DiaG (E := E) (ST := ST)) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : (d.dia c⁻¹).dia c = d := by
  apply Subtype.ext
  show (d.1.dia c⁻¹).dia c = d.1
  ext <;> simp [Deco.dia, ← mul_assoc]

theorem rla_dia_inv' (c : DiaG (E := E) (ST := ST)) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : (d.dia c).dia c⁻¹ = d := by
  apply Subtype.ext
  show (d.1.dia c).dia c⁻¹ = d.1
  ext <;> simp [Deco.dia, ← mul_assoc]

theorem rla_dia_inj (c : DiaG (E := E) (ST := ST)) {d d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} (h : d.dia c = d'.dia c) : d = d' := by
  rw [← rla_dia_inv' n ST SG c d, h, rla_dia_inv' n ST SG c d']

theorem DecoSet.dia_L (c : DiaG (E := E) (ST := ST)) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : (d.dia c).1.L = d.1.L := by
  show (d.1.dia c).L = d.1.L
  unfold Deco.L
  congr 1
  ext x
  simp only [Deco.dia, Set.mem_setOf_eq, Units.mul_right_eq_zero]

theorem decoOfD_ptOfD (hS : DecoPtSurj hc n ST SG) (c : DiaG (E := E) (ST := ST)) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) :
    decoOfD n ST SG c (ptOfD hc n ST SG c d : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d := by
  show (decoOf ST SG (ptOf hc n ST SG (d.dia c⁻¹) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))).dia c = d
  rw [decoOf_ptOf hc n ST SG hS (d.dia c⁻¹)]
  exact rla_dia_inv n ST SG c d

theorem rla_dia_smulH (c : DiaG (E := E) (ST := ST)) (g : UF E n × H) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : (g • d).dia c = g • d.dia c := rfl

theorem rla_cls_eq {d d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} :
    decoCls n ST SG H d = decoCls n ST SG H d' ↔ ∃ g : UF E n × H, g • d' = d := by
  constructor
  · intro h
    exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact h))
  · rintro ⟨g, hg⟩
    exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨g, hg⟩))

theorem levU_y_bijD (hS : DecoPtSurj hc n ST SG) (c₀ : DiaG (E := E) (ST := ST)) (s : DecoCl n ST SG H → DecoSet (E := E) (n := n) (ST := ST) (SG := SG))
    (hs : ∀ c, decoCls n ST SG H (s c) = c) :
    Function.Bijective (fun c : DecoCl n ST SG H =>
      (Quotient.mk'' (ptOfD hc n ST SG c₀ (s c)) : AdCl hc n ST SG H)) := by
  classical

  let Φ : DecoCl n ST SG H → DecoCl n ST SG H := fun q => Quotient.liftOn' q
    (fun d => decoCls n ST SG H (d.dia c₀⁻¹)) (fun a b hab => by
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
      rw [← hg]
      exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩)))
  let Ψ : DecoCl n ST SG H → DecoCl n ST SG H := fun q => Quotient.liftOn' q
    (fun d => decoCls n ST SG H (d.dia c₀)) (fun a b hab => by
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
      rw [← hg]
      exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩)))
  have hΦΨ : ∀ q, Φ (Ψ q) = q := by
    intro q
    induction q using Quotient.inductionOn' with
    | h d =>
      show decoCls n ST SG H ((d.dia c₀).dia c₀⁻¹) = _
      rw [rla_dia_inv' n ST SG c₀ d]
      rfl
  have hΨΦ : ∀ q, Ψ (Φ q) = q := by
    intro q
    induction q using Quotient.inductionOn' with
    | h d =>
      show decoCls n ST SG H ((d.dia c₀⁻¹).dia c₀) = _
      rw [rla_dia_inv n ST SG c₀ d]
      rfl
  have hΦ : Function.Bijective Φ := Function.bijective_iff_has_inverse.mpr ⟨Ψ, hΨΦ, hΦΨ⟩
  let s' : DecoCl n ST SG H → DecoSet (E := E) (n := n) (ST := ST) (SG := SG) := fun c => (s (Ψ c)).dia c₀⁻¹
  have hs' : ∀ c, decoCls n ST SG H (s' c) = c := by
    intro c
    calc decoCls n ST SG H (s' c) = Φ (decoCls n ST SG H (s (Ψ c))) := rfl
      _ = Φ (Ψ c) := by rw [hs (Ψ c)]
      _ = c := hΦΨ c
  have hF := levU_y_bij hc n ST SG H hS s' hs'
  have heq : (fun c : DecoCl n ST SG H => (Quotient.mk'' (ptOfD hc n ST SG c₀ (s c)) : AdCl hc n ST SG H)) =
      (fun c => (Quotient.mk'' (ptOf hc n ST SG (s' (Φ c))) : AdCl hc n ST SG H)) := by
    funext c
    show _ = (Quotient.mk'' (ptOf hc n ST SG ((s (Ψ (Φ c))).dia c₀⁻¹)) : AdCl hc n ST SG H)
    rw [hΨΦ c]
    rfl
  rw [heq]
  exact hF.comp hΦ

theorem rla_mem_stab_dia (c : DiaG (E := E) (ST := ST)) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (g : UF E n × H) :
    g ∈ MulAction.stabilizer (UF E n × H) (d.dia c) ↔ g ∈ MulAction.stabilizer (UF E n × H) d := by
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact rla_dia_inj n ST SG c (d := g • d) (d' := d) h
  · intro h
    show (g • d).dia c = d.dia c
    rw [h]

theorem rla_mem_range_stabRat (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (γ : URat hc n) :
    γ ∈ (stabRat hc n ST SG H d).range ↔ ∃ h : H, (ratHom hc n γ, h) ∈ MulAction.stabilizer (UF E n × H) d := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a.1.2, ?_⟩
    rw [rlc_ratHom_stabRat hc n ST SG H d a]
    exact a.2
  · rintro ⟨h, hmem⟩
    refine ⟨⟨(ratHom hc n γ, h), hmem⟩, ?_⟩
    apply (ratHom_bijective hc n).1
    rw [rlc_ratHom_stabRat]

theorem stabRat_rangeD (c : DiaG (E := E) (ST := ST)) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (y : UAd hc n)
    (hy : decoOfD n ST SG c (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d) (γ : URat hc n) :
    γ ∈ (stabRat hc n ST SG H d).range ↔
      Formalism.UG.bc (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E) ∈
        (levU hc n ST SG H).map (MulAut.conj (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))).toMonoidHom := by
  have hy' : decoOf ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d.dia c⁻¹ := by
    rw [← hy]
    exact (rla_dia_inv' n ST SG c _).symm
  rw [← stabRat_range hc n ST SG H (d.dia c⁻¹) y hy' γ, rla_mem_range_stabRat, rla_mem_range_stabRat]
  simp only [rla_mem_stab_dia]

theorem levU_y_latD (hS : DecoPtSurj hc n ST SG) (c : DiaG (E := E) (ST := ST)) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG))
    (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    x ∈ Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) d.1.L ↔
    ((((ptOfD hc n ST SG c d : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ x ∈
      Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) (baseLb E n ST) := by
  rw [← DecoSet.dia_L n ST SG c⁻¹ d]
  exact levU_y_lat hc n ST SG hS (d.dia c⁻¹) x

def recCls (hS : DecoPtSurj hc n ST SG) (c₀ : DiaG (E := E) (ST := ST)) (s : DecoCl n ST SG H → DecoSet (E := E) (n := n) (ST := ST) (SG := SG))
    (hs : ∀ c, decoCls n ST SG H (s c) = c) :
    RecCls hc (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST) (levU hc n ST SG H)
      (fun c => MulAction.stabilizer (UF E n × H) (s c)) (fun c => (s c).1.L) where
  y c := ptOfD hc n ST SG c₀ (s c)
  y_bij := levU_y_bijD hc n ST SG H hS c₀ s hs
  y_lat c x := levU_y_latD hc n ST SG hS c₀ (s c) x
  stabI c := stabRat hc n ST SG H (s c)
  stabI_inj c := stabRat_injective hc n ST SG H (s c)
  stabI_range c γ hγ := stabRat_rangeD hc n ST SG H c₀ (s c) _ (decoOfD_ptOfD hc n ST SG hS c₀ (s c)) ⟨γ, hγ⟩
  stabI_lat c γ x := stabRat_lat hc n ST SG H (s c) γ x

end Dia

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

namespace DetChrL

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

section Joint

open Classical

variable {X : Fields} {Pr : Primes X}

theorem conjP_vGs (hX : X.Ok) (hPr : Pr.Ok) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs) :
    HeckeExHost.conjPrime₂ P ≠ P ∧ HeckeExHost.conjPrime₂ P ∉ Pr.vGs := by
  have hmem : ∀ j, P ∈ Pr.vG j → X.conjO (Pr.piG j) ∈ P.asIdeal := fun j h => ChainCounts.mem_of_mem_divs h
  have hcomap : ∀ y : 𝓞 X.E, y ∈ (HeckeExHost.conjPrime₂ P).asIdeal ↔ X.conjO y ∈ P.asIdeal := fun y => Iff.rfl
  have hcop : ∀ j, Pr.piG j ∈ P.asIdeal → X.conjO (Pr.piG j) ∈ P.asIdeal → False := by
    intro j h1 h2
    obtain ⟨a, b, hab⟩ := hPr.piG_cop j
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
  obtain ⟨i, hi⟩ : ∃ i, P ∈ Pr.vG i := by
    rcases Finset.mem_union.1 hP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : Pr.piG i ∈ (HeckeExHost.conjPrime₂ P).asIdeal := (hcomap _).2 (hmem i hi)
    rw [h] at h1
    exact hcop i h1 (hmem i hi)
  · obtain ⟨j, hj⟩ : ∃ j, HeckeExHost.conjPrime₂ P ∈ Pr.vG j := by
      rcases Finset.mem_union.1 h with h' | h'
      · exact ⟨0, h'⟩
      · exact ⟨1, h'⟩
    have h1 : Pr.piG j ∈ P.asIdeal := by
      have := (hcomap _).1 (ChainCounts.mem_of_mem_divs hj)
      rwa [HeckeExHost.conjO_conjO'] at this
    by_cases hij : j = i
    · subst hij
      exact hcop j h1 (hmem j hi)
    · have hg1 : ((Pr.g j : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
        rw [← hPr.piG_norm j]
        exact Ideal.mul_mem_right _ _ h1
      have hg2 : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
        rw [← hPr.piG_norm i]
        exact Ideal.mul_mem_left _ _ (hmem i hi)
      have hne : Pr.g j ≠ Pr.g i := by
        have key : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
        rcases key j i hij with ⟨h0, h1'⟩ | ⟨h0, h1'⟩
        · rw [h0, h1']; exact hPr.g_ne
        · rw [h0, h1']; exact hPr.g_ne.symm
      have hcopZ : Nat.Coprime (Pr.g j) (Pr.g i) := (Nat.coprime_primes (hPr.g_prime j) (hPr.g_prime i)).2 hne
      obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * (Pr.g j : ℤ) + b * (Pr.g i : ℤ) = 1 := by
        refine ⟨Nat.gcdA (Pr.g j) (Pr.g i), Nat.gcdB (Pr.g j) (Pr.g i), ?_⟩
        have := Nat.gcd_eq_gcd_ab (Pr.g j) (Pr.g i)
        rw [hcopZ] at this
        push_cast at this
        linarith
      apply P.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : (1 : 𝓞 X.E) = (a : 𝓞 X.E) * ((Pr.g j : ℕ) : 𝓞 X.E) + (b : 𝓞 X.E) * ((Pr.g i : ℕ) : 𝓞 X.E) := by
        have := congrArg (fun z : ℤ => (z : 𝓞 X.E)) hab
        push_cast at this
        exact this.symm
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ hg1) (Ideal.mul_mem_left _ _ hg2)

end Joint

section Core

open Classical

variable {X : Fields} {Pr : Primes X} {R : Ranks}

end Core

end DetChrL

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Fr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

def DecoSet.SameOn (B : Finset (HeightOneSpectrum (𝓞 E))) (d d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : Prop := ∀ P ∈ B, d'.1.at P = d.1.at P

def DecoF.repl (p : DecoF E n ST SG Q) (d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (h : DecoSet.SameOn Q p.deco d') : DecoF E n ST SG Q :=
  ⟨(d', p.1.2), fun P x => by rw [h P.1 P.2]; exact p.2 P x⟩


open Classical in
def DecoF.mv (p : DecoF E n ST SG Q) (d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : DecoF E n ST SG Q :=
  if h : DecoSet.SameOn Q p.deco d' then p.repl d' h else p

theorem DecoF.mv_pos {p : DecoF E n ST SG Q} {d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} (h : DecoSet.SameOn Q p.deco d') : p.mv d' = p.repl d' h := by
  unfold DecoF.mv; rw [dite_eq_left h]

theorem DecoF.mv_deco {p : DecoF E n ST SG Q} {d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} (h : DecoSet.SameOn Q p.deco d') : (p.mv d').deco = d' := by
  rw [DecoF.mv_pos h]; rfl

theorem DecoSet.sameOn_up {B : Finset (HeightOneSpectrum (𝓞 E))} (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1)
    (hB : ∀ P' ∈ B, P' ≠ P.1 ∧ P' ≠ conjPrime₂ P.1) (q : 𝓞 E) {x : Sp E n} (hx : x ∈ d.1.N) : DecoSet.SameOn B d (d.up P q x) := by
  intro P' hP'
  unfold DecoSet.up
  split_ifs with hok
  · show localization₂ P'.asIdeal (upN P.1.asIdeal d.1.N x) = localization₂ P'.asIdeal d.1.N
    exact ((upN_spec d.2.lat d.2.uni P.1 hne hx).2.2.1 P' (hB P' hP').1 (hB P' hP').2).localization_eq
  · rfl

end Fr

section Yb

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem locLat_sameAt {E : Type} [Field E] [NumberField E] {n : ℕ} (SB : Finset (HeightOneSpectrum (𝓞 E))) {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : ∀ P ∈ SB, localization₂ P.asIdeal N' = localization₂ P.asIdeal N) (e : SB → ℤ) : locLat SB N' e = locLat SB N e := by
  unfold locLat
  exact iInf_congr fun P => by rw [h P.1 P.2]

theorem ybSet_sameAt {n : ℕ} {N N' : Submodule (𝓞 X.E) (Sp X.E n)} (h : ∀ P ∈ rowSG Pr sel mu, localization₂ P.asIdeal N' = localization₂ P.asIdeal N) :
    ybSet sel mu cst N' = ybSet sel mu cst N := by
  unfold ybSet
  rw [locLat_sameAt _ h, locLat_sameAt _ h]

end Yb

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem tqk_unitV_one {K : Type} [Field K] (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (h : redP P a = 1) : LocE.unitV χ a = 1 := by
  have hU : IsUnit (redP P a) := by rw [h]; exact isUnit_one
  unfold LocE.unitV
  rw [dite_eq_left hU]
  have : hU.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, h]; rfl)
  rw [this, map_one, Units.val_one]

end Gen

section Fin

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

end Fin

end Formalism.L2.Col
end
end
