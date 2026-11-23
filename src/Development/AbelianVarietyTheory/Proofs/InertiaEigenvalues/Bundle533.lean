module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws
public import Formalism.SatakeDualWeyl.StatementG
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle164
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.GoodModUnr

open GlobalTheory.IdemSupport

variable {D : D7}

theorem unrAt_of_unrPl {w : HeightOneSpectrum (𝓞 D.host.E)} {χ : (AE D)ˣ →* Circle} (h : GlobalTheory.Hk3.UnrPl w χ) :
    GlobalTheory.LFun.UnrAt χ w := by
  intro u hu
  have hΦ : Comp D (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) := by
    obtain ⟨a, b, c, d, e⟩ := (GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E))
    exact ⟨a, b, c, d, e⟩
  obtain ⟨e, f, hp⟩ := exists_isPrimeIdem hΦ w
  have hd := (of_isPrimeIdem hΦ hp).1
  have hee : e * e = e := delta_idem hΦ hd
  have hfe : f * e = e := by
    rcases hp with ⟨hi, rfl⟩ | ⟨rfl, -, -⟩
    · have ho : e * cA D e = 0 := hi.1.2.1
      linear_combination hee + ho
    · exact hee
  obtain ⟨h1, h2⟩ := (GlobalTheory.LFun.EulerTie.isUnitAt_iff w u).1 hu
  have hg : e * ((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) + (1 - e) =
      ((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) :=
    GlobalTheory.LFun.EulerTie.glue_eq_locIdele hd (GlobalTheory.LFun.EulerTie.finComp_locIdele_self w u)
  have hx : f * (((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) - 1) =
      ((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) - 1 := by
    linear_combination (((GlobalTheory.LFun.locIdele D.host.F w u : (AE D)ˣ) : AE D) - 1) * hfe + (1 - f) * hg
  have i1 := (GlobalTheory.LFun.EulerTie.locIdele_int_iff (F := D.host.F) w u).2 h1
  have i2 := (GlobalTheory.LFun.EulerTie.locIdele_int_iff (F := D.host.F) w u⁻¹).2 h2
  rw [map_inv] at i2
  have := h e f hp _ hx i1 i2
  exact (congrArg Circle.toUnits this).trans (map_one _)

theorem good_of_ne {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {f : AE D} (hf : IsFinIdem D v f) (hv : ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w.under (𝓞 D.host.F) = v) : GlobalTheory.Hk3.Good R t w := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  intro PP hPP
  have key : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v := by
    intro hu
    obtain ⟨e, f', hp⟩ := exists_isPrimeIdem hΦ PP
    obtain ⟨-, ε, hε, hf'⟩ := of_isPrimeIdem hΦ hp
    obtain ⟨ε', hε', rfl⟩ := hf
    rw [hu] at hε
    exact hv PP hPP e f' hp (by rw [hf', placeIdem_unique hε hε'])
  refine ⟨fun h => key (h ▸ hw), fun h => key ?_⟩
  rw [← hw, (isConjPl_iff PP w).1 h, under_cP]

theorem chrTh_unrAt : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1 w ∧ GlobalTheory.LFun.UnrAt (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t v f hf hv w hw
  obtain ⟨he, hm⟩ := GlobalTheory.UnrOffLevels.unrPl_of_good R F hL.lev t w (good_of_ne R t hf hv hw)
  have a := unrAt_of_unrPl (hm ((i : ℕ) + 1) (by omega) (by have := i.isLt; omega))
  have b := unrAt_of_unrPl he
  exact ⟨a, a.mul b.inv⟩

end GlobalTheory.GoodModUnr
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.Eu

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


open Classical in
def fid (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : AE D :=
  if h : ∃ f, IsFinIdem D v f then h.choose else 0

def locSet (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) : Set (GA D (Wc D i)) :=
  {g | g ∈ GfC (Wc D i) ∧ SuppF (Wc D i) (fid D v) g}

def LX (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) : Type :=
  Quotient ((QuotientGroup.leftRel (levW R i)).comap (Subtype.val : locSet R i v → GA D (Wc D i)))

theorem one_mem_locSet (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    (1 : GA D (Wc D i)) ∈ locSet R i v := by
  refine ⟨(GfC (Wc D i)).one_mem, ?_⟩
  have : Formalism.L2.Theta.mt (Wc D i) 1 = 1 := rfl
  intro a b
  simp [this]

def lx0 (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) : LX R i v :=
  Quotient.mk _ ⟨1, one_mem_locSet R i v⟩

def rep {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x : LX R i v) : GA D (Wc D i) :=
  (Quotient.out x).1


open Classical in
def Bop (R : RealDat D A Ks) (i : Fin D.R.m) (γ : GA D (Wc D i)) :
    (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H :=
  if h : ∃ B : (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H, ‖B‖ ≤ 1 ∧ ∀ x y, trPair R i γ x y = ⟪x, B y⟫_ℂ then
    h.choose else 0


open Classical in
def famProd (R : RealDat D A Ks) (i : Fin D.R.m) (F : ∀ v, LX R i v) : GA D (Wc D i) :=
  if h : {w | F w ≠ lx0 R i w}.Finite then (h.toFinset.toList.map fun w => rep (F w)).prod else 1

def Bfam (R : RealDat D A Ks) (i : Fin D.R.m) (F : ∀ v, LX R i v) :
    (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H :=
  Bop R i (famProd R i F)

def acoef (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i)))
    (𝓕 : Set (WO (Vc D i) (Wc D i))) (v : HeightOneSpectrum (𝓞 D.host.F)) (x : LX R i v) : ℂ :=
  coef R i t μ 𝓕 (rep x)

def Zop (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i)))
    (𝓕 : Set (WO (Vc D i) (Wc D i))) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H :=
  ∑' x : LX R i v, acoef R i t μ 𝓕 v x • Bop R i (rep x)

section Helpers
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem bop_one {R : RealDat D A Ks} {i : Fin D.R.m} (hTL : TransLaws R i) : Eu.Bop R i 1 = 1 := by
  have h6 : ∀ x y, trPair R i 1 x y = ⟪x, y⟫_ℂ := hTL.2.2.2.2.2
  have hex : ∃ B : (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H, ‖B‖ ≤ 1 ∧
      ∀ x y, trPair R i 1 x y = ⟪x, B y⟫_ℂ :=
    ⟨1, ContinuousLinearMap.norm_id_le, fun x y => by rw [h6]; rfl⟩
  unfold Eu.Bop
  rw [dite_eq_left hex]
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [← hex.choose_spec.2 x y, h6]
  rfl

theorem bop_norm (R : RealDat D A Ks) (i : Fin D.R.m) (γ : GA D (Wc D i)) : ‖Eu.Bop R i γ‖ ≤ 1 := by
  unfold Eu.Bop
  split_ifs with h
  · exact h.choose_spec.1
  · simp

theorem trivial_level_coset_representative_mem_level (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Eu.rep (Eu.lx0 R i v) ∈ levW R i := by
  have h := Quotient.mk_out (s := (QuotientGroup.leftRel (levW R i)).comap
    (Subtype.val : Eu.locSet R i v → GA D (Wc D i))) ⟨1, Eu.one_mem_locSet R i v⟩
  rw [Setoid.comap_rel, QuotientGroup.leftRel_apply] at h
  have h2 := h
  have h3 := (levW R i).inv_mem h2
  simpa [Eu.rep, Eu.lx0] using h3

theorem local_coefficient_trivial_level_coset {R : RealDat D A Ks} {i : Fin D.R.m} {t : T} (hLF : LevFix R i t) (hVN : VecNe R i t) {μ 𝓕}
    (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Eu.acoef R i t μ 𝓕 v (Eu.lx0 R i v) = 1 := by
  unfold Eu.acoef
  have := Model.coef_mul_lev R i t hLF μ 𝓕 1 _ (trivial_level_coset_representative_mem_level R i v)
  rw [one_mul] at this
  rw [this, Model.coef_one R i t hVN μ 𝓕 hμ]

theorem localCosetFamilyRepresentativeProd_trivial_eq_one (R : RealDat D A Ks) (i : Fin D.R.m) : Eu.famProd R i (Eu.lx0 R i) = 1 := by
  unfold Eu.famProd
  have hf : {w | Eu.lx0 R i w ≠ Eu.lx0 R i w}.Finite := by simp
  rw [dite_eq_left hf]
  have : hf.toFinset = ∅ := by simp
  rw [this]
  simp

end Helpers

end GlobalTheory.RawLift.Eu

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.CoefLeft

theorem ip_eq_of_sq {X : Type} [MeasurableSpace X] (ν : Measure X) (a b c d : X → ℂ)
    (ha : MemLp a 2 ν) (hb : MemLp b 2 ν) (hc : MemLp c 2 ν) (hd : MemLp d 2 ν)
    (h : ∀ z : ℂ, ∫⁻ x, ‖c x + z * d x‖ₑ ^ 2 ∂ν = ∫⁻ x, ‖a x + z * b x‖ₑ ^ 2 ∂ν) :
    ∫ x, star (c x) * d x ∂ν = ∫ x, star (a x) * b x ∂ν := by
  have pt : ∀ p q : ℂ, star p * q = (1/4 : ℂ) * ((((‖p + 1 * q‖ ^ 2 : ℝ)) : ℂ) - ((‖p + (-1) * q‖ ^ 2 : ℝ) : ℂ)
      + Complex.I * ((‖p + (-Complex.I) * q‖ ^ 2 : ℝ) : ℂ) - Complex.I * ((‖p + Complex.I * q‖ ^ 2 : ℝ) : ℂ)) := by
    intro p q
    have e : ∀ w : ℂ, ((‖w‖ ^ 2 : ℝ) : ℂ) = w * (starRingEnd ℂ) w := by
      intro w; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [e, map_add (f := _), map_mul, map_neg, map_one, Complex.conj_I]
    show (starRingEnd ℂ) p * q = _
    ring_nf
    try (simp only [Complex.I_sq]; ring)
  have mem : ∀ (f g : X → ℂ), MemLp f 2 ν → MemLp g 2 ν → ∀ z : ℂ,
      Integrable (fun x => (((‖f x + z * g x‖ ^ 2 : ℝ)) : ℂ)) ν := by
    intro f g hf hg z
    have h2 : MemLp (fun x => f x + z * g x) 2 ν := hf.add (hg.const_mul z)
    have : Integrable (fun x => ‖f x + z * g x‖ ^ 2) ν := by
      have := h2.integrable_norm_pow (p := 2) (by norm_num)
      simpa using this
    exact this.ofReal
  have Q : ∀ (f g : X → ℂ), MemLp f 2 ν → MemLp g 2 ν → ∀ z : ℂ,
      ∫ x, (((‖f x + z * g x‖ ^ 2 : ℝ)) : ℂ) ∂ν = (((∫⁻ x, ‖f x + z * g x‖ₑ ^ 2 ∂ν).toReal : ℝ) : ℂ) := by
    intro f g hf hg z
    rw [integral_complex_ofReal]
    congr 1
    have hm : AEStronglyMeasurable (fun x => f x + z * g x) ν :=
      (hf.add (hg.const_mul z)).aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖f x + z * g x‖ ^ 2)
      (Filter.Eventually.of_forall fun x => by simp only [Pi.zero_apply]; positivity) (hm.norm.pow 2)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have expand : ∀ (f g : X → ℂ), MemLp f 2 ν → MemLp g 2 ν →
      ∫ x, star (f x) * g x ∂ν = (1/4 : ℂ) * ((((∫⁻ x, ‖f x + 1 * g x‖ₑ ^ 2 ∂ν).toReal : ℝ) : ℂ)
        - (((∫⁻ x, ‖f x + (-1) * g x‖ₑ ^ 2 ∂ν).toReal : ℝ) : ℂ)
        + Complex.I * (((∫⁻ x, ‖f x + (-Complex.I) * g x‖ₑ ^ 2 ∂ν).toReal : ℝ) : ℂ)
        - Complex.I * (((∫⁻ x, ‖f x + Complex.I * g x‖ₑ ^ 2 ∂ν).toReal : ℝ) : ℂ)) := by
    intro f g hf hg
    simp_rw [pt (f _) (g _)]
    rw [integral_const_mul, integral_sub, integral_add, integral_sub, integral_const_mul, integral_const_mul,
      Q f g hf hg, Q f g hf hg, Q f g hf hg, Q f g hf hg]
    · exact mem f g hf hg 1
    · exact mem f g hf hg (-1)
    · exact (mem f g hf hg 1).sub (mem f g hf hg (-1))
    · exact (mem f g hf hg (-Complex.I)).const_mul _
    · exact ((mem f g hf hg 1).sub (mem f g hf hg (-1))).add ((mem f g hf hg (-Complex.I)).const_mul _)
    · exact (mem f g hf hg Complex.I).const_mul _
  rw [expand c d hc hd, expand a b ha hb, h 1, h (-1), h (-Complex.I), h Complex.I]

end GlobalTheory.RawLift.CoefLeft

namespace GlobalTheory.RawLift.CoefLeft

variable {D : D7}

theorem isThetaFunO_add_smul {S T' : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {f g : WO S T' → ℂ}
    (hf : IsThetaFunO ψ S T' f) (hg : IsThetaFunO ψ S T' g) (z : ℂ) : IsThetaFunO ψ S T' (f + z • g) := {
  quasi γ w := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hf.quasi, hg.quasi]; ring
  level := by
    obtain ⟨U₁, hU₁, h₁⟩ := hf.level
    obtain ⟨U₂, hU₂, h₂⟩ := hg.level
    refine ⟨U₁ ⊓ U₂, by rw [AddSubgroup.coe_inf]; exact hU₁.inter hU₂, fun u hu hu0 => ?_⟩
    have e1 := h₁ u hu.1 hu0
    have e2 := h₂ u hu.2 hu0
    funext w
    have e1' := congrFun e1 w
    have e2' := congrFun e2 w
    simp only [heisO, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1' e2' ⊢
    rw [← e1', ← e2']; ring_nf
  cont := hf.cont.add (hg.cont.const_smul z)
  smooth k L hL hL0 w := by
    have := (hf.smooth k L hL hL0 w).add ((hg.smooth k L hL hL0 w).const_smul z)
    simpa only [Pi.add_apply, Pi.smul_apply] using this }

theorem memLp_two_of_lintegral {X : Type} [MeasurableSpace X] {ν : Measure X} {f : X → ℂ}
    (hm : AEStronglyMeasurable f ν) (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν < ⊤) : MemLp f 2 ν := by
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine ⟨hm.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa [enorm_pow] using h

end GlobalTheory.RawLift.CoefLeft

namespace GlobalTheory.RawLift.CoefLeft

theorem aesm_of_theta {D : D7} {S T' : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {f : WO S T' → ℂ} (ν : Measure (WO S T'))
    (hf : IsThetaFunO ψ S T' f) : AEStronglyMeasurable f ν := by
  haveI : OpensMeasurableSpace (WO S T') := ⟨le_rfl⟩
  exact hf.cont.aestronglyMeasurable

theorem thetaInner_weilRep {D : D7} {S T' : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)} (hW : IsWeilDatumO ψ S T' χS χT om)
    {μ : Measure (WO S T')} {𝓕 : Set (WO S T')} (hμ : IsCovolOne (ratL T' S) μ 𝓕) (p : GA D S × GA D T')
    {u v : WO S T' → ℂ} (hu : IsThetaFunO ψ S T' u) (hv : IsThetaFunO ψ S T' v)
    (hu2 : ∫⁻ w in 𝓕, ‖u w‖ₑ ^ 2 ∂μ < ⊤) (hv2 : ∫⁻ w in 𝓕, ‖v w‖ₑ ^ 2 ∂μ < ⊤) :
    thetaIP μ 𝓕 (om p u) (om p v) = thetaIP μ 𝓕 u v := by
  have un := fun f (hf : IsThetaFunO ψ S T' f) => hW.om_unit μ 𝓕 hμ.1 hμ.2.1 p f hf
  unfold thetaIP
  refine ip_eq_of_sq (μ.restrict 𝓕) u v (om p u) (om p v)
    (memLp_two_of_lintegral (aesm_of_theta _ hu) hu2) (memLp_two_of_lintegral (aesm_of_theta _ hv) hv2)
    (memLp_two_of_lintegral (aesm_of_theta _ (hW.om_pres p u hu)) (by rw [un u hu]; exact hu2))
    (memLp_two_of_lintegral (aesm_of_theta _ (hW.om_pres p v hv)) (by rw [un v hv]; exact hv2)) (fun z => ?_)
  have := un (u + z • v) (isThetaFunO_add_smul hu hv z)
  simpa only [map_add (f := _), map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this

theorem thetaIP₂ {D : D7} {S T' : HSp D} {μ : Measure (WO S T')} {𝓕 : Set (WO S T')}
    {v : WO S T' → ℂ} (h : thetaIP μ 𝓕 v v ≠ 0) : ∫⁻ w in 𝓕, ‖v w‖ₑ ^ 2 ∂μ < ⊤ := by
  have hi : Integrable (fun w => star (v w) * v w) (μ.restrict 𝓕) := by
    by_contra hn
    exact h (integral_undef hn)
  have := hi.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at this
  simpa [enorm_mul, sq] using this

end GlobalTheory.RawLift.CoefLeft

namespace GlobalTheory.RawLift.CoefLeft



theorem coef_lev_mul : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i t, LevFix R i t → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t hfix μ 𝓕 hμ k hk g
  have hW := hL.thP.ωP i t
  have hv1 : R.ωP i t (1, k) (R.vP i t) = R.vP i t := by
    have := hfix k hk 1
    rwa [Model.pureTensor_one] at this
  have hvθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    rwa [Model.pureTensor_one] at this
  unfold coef
  by_cases h0 : thetaIP μ 𝓕 (R.vP i t) (R.vP i t) = 0
  · rw [h0, div_zero, div_zero]
  congr 1
  have e : R.ωP i t (1, k * g) = R.ωP i t (1, k) * R.ωP i t (1, g) := by rw [← map_mul]; simp
  rw [e, Module.End.mul_apply]
  have hv2 := thetaIP₂ h0
  have huθ := hW.om_pres (1, g) _ hvθ
  have hu2 : ∫⁻ w in 𝓕, ‖R.ωP i t (1, g) (R.vP i t) w‖ₑ ^ 2 ∂μ < ⊤ := by
    rw [hW.om_unit μ 𝓕 hμ.1 hμ.2.1 (1, g) _ hvθ]; exact hv2
  have key := thetaInner_weilRep hW hμ (1, k) huθ hvθ hu2 hv2
  rwa [hv1] at key

end GlobalTheory.RawLift.CoefLeft

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.level_subgroup_restricted_product_of_laws : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i, LevProd R i := by
  first | exact @GlobalTheory.LevelProduct.levProd_of_laws | exact GlobalTheory.LevelProduct.levProd_of_laws | (intros; apply GlobalTheory.LevelProduct.levProd_of_laws <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.PlaceDichotomy

theorem split_or_inert_idem : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D),
    IsFinIdem D v f → (∃ e, Formalism.L2.Theta.IsSplitIdem D e ∧ e + Formalism.L2.Theta.cA D e = f) ∨
      (∃ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E v w) := by
  intro D v f hf
  obtain ⟨ε, ⟨α, hεα, hα1, hα0⟩, rfl⟩ := hf
  haveI := v.isMaximal
  obtain ⟨⟨P, hPp, hPo⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 D.host.E)
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨P, hPp, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
  have hw : w.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hPo.over.symm
  rcases GlobalTheory.LPositivity.split_or_inert D w with hs | hi
  · left
    rw [hw] at hs
    obtain ⟨τ, -⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq (GlobalTheory.AdelicU.isCMExt_host D) hs hw
    refine ⟨GlobalTheory.EmbChart.idem τ, GlobalTheory.EmbChart.isSplitIdem_idem τ, ?_⟩
    have hα : α = GlobalTheory.AdelicU.singleFin v 1 := by
      refine FiniteAdeleRing.ext _ fun u => ?_
      change evalV D.host.F u α = evalV D.host.F u (GlobalTheory.AdelicU.singleFin v 1)
      by_cases e : u = v
      · subst e; rw [hα1, GlobalTheory.AdelicU.evalV_singleFin_self]
      · rw [hα0 u e, GlobalTheory.AdelicU.evalV_singleFin_ne e]
    rw [GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add (f := _), add_sub_cancel, hεα, hα]
    rfl
  · right
    exact ⟨w, hw ▸ hi⟩

end GlobalTheory.PlaceDichotomy
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem semiBC_of_basis : ∀ (A B : Type) [CommRing A] [CommRing B] (f : A →+* B) (M : Type) [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N) (ι : Type) (e : Module.Basis ι A M) (b : Module.Basis ι B N), (∀ i, b i = u (e i)) → SemiBC u := by
  intro A B _ _ f M _ _ N _ _ u ι e b hb Q _ _ v
  refine ⟨b.constr B (fun i => v (e i)), ?_, ?_⟩
  · intro x
    have h : (b.constr B (fun i => v (e i))).comp u = v := by
      refine e.ext fun i => ?_
      simp [LinearMap.comp_apply, ← hb, Module.Basis.constr_basis]
    exact LinearMap.congr_fun h x
  · intro w hw
    refine b.ext fun i => ?_
    rw [Module.Basis.constr_basis, hb, hw]

end GlobalTheory.BSP
end
