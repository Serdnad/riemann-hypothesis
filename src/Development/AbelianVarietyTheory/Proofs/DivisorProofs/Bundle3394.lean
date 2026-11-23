module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle642
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle717
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1647
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3140
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2790
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3085
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle690
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle092
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3389
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev.GeoCard

theorem card_ker_elt {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {w0 : Ideal (𝓞 D.F)} (hw : IsEtPlace b w0) {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (k : Type) [Field k]
    [IsAlgClosed k] (x : Sp k ⟶ S) (c : 𝓞 D.F) (hc : c ≠ 0)
    (hcw : ∀ w : Ideal (𝓞 D.F), w.IsMaximal → ((p : ℕ) : 𝓞 D.F) ∈ w → w ≠ w0 → c ∉ w) :
    Nat.card {g : Over.mk x ⟶ o.A // g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1} =
      (Algebra.norm ℤ c).natAbs ^ (D.m * D.n) := by
  obtain ⟨ℓ, hℓ1, hℓ⟩ := Nat.exists_infinite_primes (p + ringChar k + 1)
  have hℓp : ℓ ≠ p := by omega
  have hℓk : (ℓ : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k (ringChar k)]
    intro hd
    rcases (Nat.dvd_prime hℓ).1 hd with h1 | h1
    · exact CharP.ringChar_ne_one (R := k) h1
    · omega
  exact GlobalTheory.T.abelianScheme_card_kernel_eq_norm_pow S o.A o.ab D.F (o.act.toF D) k x (D.m * D.n) ℓ hℓ hℓk (GlobalTheory.T.exists_level_structure_on_torsion p D R b N S s o k x ℓ hℓ hℓp) c hc
    (GlobalTheory.T.harrisTaylor_tangent_injective_away_from_etalePlace p D R b N w0 hw S s o k x c hc hcw)

theorem card_ker_place : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (w0 : Ideal (𝓞 D.F)), IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k]
    [IsAlgClosed k] (x : Sp k ⟶ S), Nat.card {g : Over.mk x ⟶ o.A // ∀ c ∈ w0,
      g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1} = Nat.card (𝓞 D.F ⧸ w0) ^ (D.m * D.n) := by
  intro p _ D R _ b N w0 hw S s o k _ _ x
  letI : CommGroup (Over.mk x ⟶ o.A) := Hom.commGroup
  have act0 : o.act.act 0 = 1 := by
    have h := o.act.add 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  letI : Module (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) :=
    { smul := fun c g => Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c))
      one_smul := fun g => by
        show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O 1)) = g
        rw [map_one, o.act.one, Category.comp_id]; rfl
      mul_smul := fun a b g => by
        show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O (a * b))) =
          Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O b)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))
        rw [map_mul, o.act.mul, Category.assoc]
      smul_zero := fun c => by
        haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
        show Additive.ofMul ((1 : Over.mk x ⟶ o.A) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) = Additive.ofMul 1
        rw [MonObj.one_comp]
      smul_add := fun c g g' => by
        haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
        show Additive.ofMul ((g.toMul * g'.toMul) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) =
          Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) *
            (g'.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)))
        rw [MonObj.mul_comp]
      add_smul := fun a b g => by
        show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O (a + b))) =
          Additive.ofMul ((g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) *
            (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O b)))
        rw [map_add (f := _), o.act.add, MonObj.comp_mul]
      zero_smul := fun g => by
        show Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O 0)) = Additive.ofMul 1
        rw [map_zero, act0, MonObj.comp_one] }
  have hsm : ∀ (c : 𝓞 D.F) (g : Additive (Over.mk x ⟶ o.A)),
      c • g = Additive.ofMul (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) := fun _ _ => rfl
  have hmax : w0.IsMaximal := hw.1
  have hne : w0 ≠ ⊥ := by
    intro h0
    have hp : ((p : ℕ) : 𝓞 D.F) ∈ w0 := hw.2.1
    rw [h0, Ideal.mem_bot] at hp
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)

  have hdiv : ∀ c : 𝓞 D.F, c ≠ 0 → Function.Surjective (fun g : Additive (Over.mk x ⟶ o.A) => c • g) := by
    intro c hc g
    set n := Ideal.absNorm (Ideal.span {c}) with hn
    have hn0 : 0 < n := by
      rw [hn, Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hc
    have hmem : ((n : ℕ) : 𝓞 D.F) ∈ Ideal.span {c} := Ideal.absNorm_mem _
    obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp hmem
    obtain ⟨g', hg'⟩ := GlobalTheory.T.exists_pow_eq_point_of_isAbelianScheme S o.A o.ab k x n hn0 g.toMul
    refine ⟨c' • Additive.ofMul g', ?_⟩
    show c • c' • Additive.ofMul g' = g
    rw [smul_smul, mul_comm, hc', Nat.cast_smul_eq_nsmul, ← ofMul_pow, hg']
    rfl

  have hT : ∀ I : Ideal (𝓞 D.F), Nat.card (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A))
      (I : Set (𝓞 D.F))) = Nat.card {g : Over.mk x ⟶ o.A // ∀ c ∈ I,
        g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1} := by
    intro I
    refine Nat.card_congr (Equiv.subtypeEquiv Additive.toMul (fun g => ?_))
    rw [Submodule.mem_torsionBySet_iff]
    constructor
    · intro h c hc
      have := h ⟨c, hc⟩
      rw [hsm] at this
      exact this
    · intro h c
      rw [hsm]
      exact congrArg Additive.ofMul (h c.1 c.2)

  have hw0nz : w0 ∈ nonZeroDivisors (Ideal (𝓞 D.F)) := mem_nonZeroDivisors_of_ne_zero hne
  set H := orderOf (ClassGroup.mk0 ⟨w0, hw0nz⟩) with hH
  have hH0 : 0 < H := orderOf_pos _
  have hpowz : w0 ^ H ∈ nonZeroDivisors (Ideal (𝓞 D.F)) := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hne)
  have hprin : Submodule.IsPrincipal (w0 ^ H) := by
    rw [← ClassGroup.mk0_eq_one_iff hpowz]
    have : (⟨w0 ^ H, hpowz⟩ : nonZeroDivisors (Ideal (𝓞 D.F))) = ⟨w0, hw0nz⟩ ^ H := rfl
    rw [this, map_pow, hH, pow_orderOf_eq_one]
  obtain ⟨c, hcgen⟩ := hprin.principal
  have hspan : w0 ^ H = Ideal.span {c} := hcgen
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hspan
    exact pow_ne_zero _ hne hspan
  have hcw : ∀ w : Ideal (𝓞 D.F), w.IsMaximal → ((p : ℕ) : 𝓞 D.F) ∈ w → w ≠ w0 → c ∉ w := by
    intro w hwm _ hww hcw
    apply hww
    have h1 : w0 ^ H ≤ w := by rw [hspan, Ideal.span_le, Set.singleton_subset_iff]; exact hcw
    exact (hmax.eq_of_le hwm.ne_top (hwm.isPrime.le_of_pow_le h1)).symm
  have hcount := card_ker_elt hw o k x c hc0 hcw
  have hnorm : (Algebra.norm ℤ c).natAbs = Nat.card (𝓞 D.F ⧸ w0) ^ H := by
    rw [← Ideal.absNorm_span_singleton, ← hspan, map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]

  have hTH : Nat.card (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A))
      ((w0 ^ H : Ideal (𝓞 D.F)) : Set (𝓞 D.F))) = Nat.card (𝓞 D.F ⧸ w0) ^ (H * (D.m * D.n)) := by
    rw [hspan, Submodule.torsionBySet_span_singleton_eq, pow_mul, ← hnorm, ← hcount]
    refine Nat.card_congr (Equiv.subtypeEquiv Additive.toMul (fun g => ?_))
    rw [Submodule.mem_torsionBy_iff, hsm]
    exact ⟨fun h => congrArg Additive.toMul h, fun h => congrArg Additive.ofMul h⟩

  have hq : 1 < Nat.card (𝓞 D.F ⧸ w0) := by
    have hfin : Finite (𝓞 D.F ⧸ w0) := by
      apply Nat.finite_of_card_ne_zero
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ne, Ideal.absNorm_eq_zero_iff]
      exact hne
    letI := Ideal.Quotient.field w0
    exact Finite.one_lt_card

  have hTHfin : Finite (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A))
      ((w0 ^ H : Ideal (𝓞 D.F)) : Set (𝓞 D.F))) := by
    apply Nat.finite_of_card_ne_zero
    rw [hTH]
    exact pow_ne_zero _ (by omega)
  have hsub : Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F)) ≤
      Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) ((w0 ^ H : Ideal (𝓞 D.F)) : Set (𝓞 D.F)) :=
    Submodule.torsionBySet_le_torsionBySet_of_subset (Ideal.pow_le_self hH0.ne')
  have hT1fin : Finite (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F))) :=
    Finite.of_injective _ (Submodule.inclusion_injective hsub)
  letI := Ideal.Quotient.field w0
  haveI : Module.Finite (𝓞 D.F ⧸ w0)
      (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F))) :=
    Module.Finite.of_finite
  set h' := Module.finrank (𝓞 D.F ⧸ w0)
      (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F))) with hh'
  have hT1 : Nat.card (Submodule.torsionBySet (𝓞 D.F) (Additive (Over.mk x ⟶ o.A)) (w0 : Set (𝓞 D.F))) =
      Nat.card (𝓞 D.F ⧸ w0) ^ h' := Module.natCard_eq_pow_finrank
  have hall := GlobalTheory.T.card_torsionBySet_pow_of_divisible_numberField D.F _ w0 h' hmax hne hdiv hT1 H
  rw [hTH] at hall
  have he : H * (D.m * D.n) = H * h' := Nat.pow_right_injective hq hall
  have he' : h' = D.m * D.n := (Nat.eq_of_mul_eq_mul_left hH0 he).symm
  rw [← hT, hT1, he']

end GlobalTheory.UPel.HT.EtLev.GeoCard
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.archLogNormReciprocity_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.MixHt.ArchRecip := by
  first | exact @GlobalTheory.MixHt.archRecip_of_principalisation | exact GlobalTheory.MixHt.archRecip_of_principalisation | (intros; apply GlobalTheory.MixHt.archRecip_of_principalisation <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem arCalc_cycleHeights_of_analytic :
    ArchInteg → ArchRecip → GlobalTheory.Published.ArCalc ∧ GlobalTheory.Published.CycleHeights := fun hI hR =>
  have h := GlobalTheory.T.arithIntersection_forms_of_archimedean_statements hI hR
  have hC : GlobalTheory.Published.ArCalc := GlobalTheory.Published.arCalc_of_form_mix_projection h.1 h.2.1 h.2.2
  ⟨hC, GlobalTheory.Published.cycleHeights_of_arCalc hC⟩

end GlobalTheory.MixHt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyEven.LocPf

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m n : ℕ} (h : m = n)
    (y : Fin n → (epsR R ⟶ G)) (hy : IsLieBasis y) : IsLieBasis (fun i : Fin m => y (i.cast h)) := by
  subst h
  exact hy

theorem exists_away_subset {A : Type} [CommRing A] [IsDomain A] (U : Set (Sp A)) (hU : IsOpen U)
    (hgen : Set.range (spMap (algebraMap A (FractionRing A))) ⊆ U) :
    ∃ f : A, f ≠ 0 ∧ Set.range (spMap (algebraMap A (Localization.Away f))) ⊆ U := by
  obtain ⟨q⟩ : Nonempty (Sp (FractionRing A)) := inferInstance
  have hp := hgen ⟨q, rfl⟩
  obtain ⟨_, ⟨r, rfl⟩, hpr, hrU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := (spMap (algebraMap A (FractionRing A)) q : PrimeSpectrum A)) hp hU
  refine ⟨r, ?_, ?_⟩
  · rintro rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hpr (Ideal.zero_mem _)
  · rw [show Set.range (spMap (algebraMap A (Localization.Away r))) =
        ((PrimeSpectrum.basicOpen r : TopologicalSpace.Opens (PrimeSpectrum A)) : Set (PrimeSpectrum A)) from
      PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hrU

theorem mem_range_of_traits {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A]
    [Algebra.FiniteType ℤ A] (f : A) (hf : f ≠ 0) (b : Localization.Away f)
    (H : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
      IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
      ∀ (t : A →+* V), t f ≠ 0 → ∀ h : Localization.Away f →+* FractionRing V,
        h.comp (algebraMap A _) = (algebraMap V (FractionRing V)).comp t →
        ∃ w : V, h b = algebraMap V (FractionRing V) w) :
    ∃ c : A, algebraMap A (Localization.Away f) c = b := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) b
  obtain ⟨n, hn⟩ := s.2
  have hdiv : f ^ n ∣ a := by
    refine GlobalTheory.T.dvd_of_dvd_in_completeDVRs_finite_residue A a (f ^ n) (pow_ne_zero n hf) ?_
    intro V _ _ _ _ hc hfin t ht
    by_cases htf0 : t f = 0
    · cases n with
      | zero => simp
      | succ k => exact absurd (by rw [map_pow, htf0, zero_pow (Nat.succ_ne_zero k)]) ht
    have htf : t f ≠ 0 := htf0
    have hinjV := IsFractionRing.injective V (FractionRing V)
    have hu : IsUnit (((algebraMap V (FractionRing V)).comp t) f) :=
      isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ hinjV).2 htf)
    have hcomp := IsLocalization.Away.lift_comp (S := Localization.Away f) f hu
    obtain ⟨w, hw⟩ := H V hc hfin t htf _ hcomp
    have e := congrArg (IsLocalization.Away.lift (S := Localization.Away f) f hu) hs
    rw [map_mul, hw, ← RingHom.comp_apply, hcomp, ← RingHom.comp_apply, hcomp, RingHom.comp_apply,
      RingHom.comp_apply, ← map_mul] at e
    have e' := hinjV e
    refine ⟨w, ?_⟩
    rw [← e', ← hn, map_pow, mul_comm]
  obtain ⟨c, hc⟩ := hdiv
  refine ⟨c, ?_⟩
  have hsu : IsUnit (algebraMap A (Localization.Away f) (s : A)) := IsLocalization.map_units _ s
  have hn' : (s : A) = f ^ n := hn.symm
  rw [hc, map_mul] at hs
  refine (hsu.mul_left_inj).1 ?_
  rw [hs, hn', mul_comm]

end GlobalTheory.KeyEven.LocPf

namespace GlobalTheory.KeyEven.LocPf

theorem keyLoc_of_famUnit_keyTrait : ∀ κ : Rule, FamUnit κ → KeyTrait κ → KeyLoc κ := by
  intro κ hFU hKT A _ _ _ _ _ G _ _ L σ x y hG hsm hopen hsym hpol hunif hy hσ hkey
  have hkey0 := hkey
  obtain ⟨φ, -, -, -, hpb, -⟩ := hkey
  haveI : IsProper x.P.A.hom := x.P.isAb.proper
  have hab := GlobalTheory.range_subset_abLocus_of_isProper hG hpb.1
  obtain ⟨f, hf0, hfab⟩ := exists_away_subset (abLocus G) hopen hab
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  have hle : Submonoid.powers f ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing (Localization.Away f) :=
    IsLocalization.isNoetherianRing (Submonoid.powers f) (Localization.Away f) inferInstance
  haveI : IsIntegrallyClosed (Localization.Away f) :=
    isIntegrallyClosed_of_isLocalization (Localization.Away f) (Submonoid.powers f) hle
  have hinj : Function.Injective (algebraMap A (Localization.Away f)) := IsLocalization.injective _ hle
  haveI : CharZero (Localization.Away f) := charZero_of_injective_algebraMap hinj
  obtain ⟨xB, hgB, hkB⟩ := GlobalTheory.T.exists_keyDatum_abelianLocus_point A (Localization.Away f) (algebraMap A _) G L σ x.P.g y x.g_pos hG hsm hopen
    hsym hpol hy hσ hfab
  obtain ⟨u, hu⟩ := hFU (Localization.Away f) xB
  have hfu : IsUnit ((algebraMap A (FractionRing A)) f) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 hf0)
  have hc := IsLocalization.Away.lift_comp (S := Localization.Away f) f hfu
  have hpbx : KeyPB x xB (IsLocalization.Away.lift (S := Localization.Away f) f hfu) :=
    GlobalTheory.T.keyDatum_fibre_of_composable_baseChange A (Localization.Away f) (FractionRing A) (algebraMap A _) _ G L σ x.P.g y xB x hgB rfl hkB
      (by rw [hc]; exact hkey0)
  have hval := hu _ _ x hpbx
  have trait : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
      IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
      ∀ (t : A →+* V), t f ≠ 0 → ∀ h : Localization.Away f →+* FractionRing V,
        h.comp (algebraMap A _) = (algebraMap V (FractionRing V)).comp t →
        ∃ w : Vˣ, h u = algebraMap V (FractionRing V) w := by
    intro V _ _ _ _ hcomp hfin t ht h hh
    have hrange : Set.range (spMap ((algebraMap V (FractionRing V)).comp t)) ⊆ abLocus G := by
      rw [← hh]
      rintro _ ⟨p, rfl⟩
      exact hfab ⟨spMap h p, rfl⟩
    obtain ⟨xV, hgV, hkV⟩ := GlobalTheory.T.exists_keyDatum_abelianLocus_point A (FractionRing V) ((algebraMap V _).comp t) G L σ x.P.g y x.g_pos hG hsm
      hopen hsym hpol hy hσ hrange
    have hpbV : KeyPB xV xB h :=
      GlobalTheory.T.keyDatum_fibre_of_composable_baseChange A (Localization.Away f) (FractionRing V) (algebraMap A _) h G L σ x.P.g y xB xV hgB hgV hkB
        (by rw [hh]; exact hkV)
    have hvalV := hu _ h xV hpbV
    obtain ⟨L', σ', y', hiso, hy', hσ', hk'⟩ := GlobalTheory.T.keyDatum_pullback_baseChange_lieBasis A V (FractionRing V) t (algebraMap V _) G L σ xV
      (fun i => y (i.cast hgV)) hG (isLieBasis_cast hgV y hy) hσ hkV
    have hne : (spMap t ⁻¹' abLocus G).Nonempty := by
      obtain ⟨q⟩ : Nonempty (Sp (FractionRing V)) := inferInstance
      exact ⟨spMap (algebraMap V _) q, hrange ⟨q, rfl⟩⟩
    obtain ⟨D, A', U, hU⟩ := hunif V hcomp hfin (spMap t) hne
    obtain ⟨w, hw⟩ := hKT V hcomp hfin _ L' σ' xV y' (IsSemiAbelian.pullback _ G hG)
      ⟨D, A', U, LBIso.trans U.LG.isLB (pull_isLB L.isLB _) L'.isLB hU hiso⟩ hy' hσ' hk'
    exact ⟨w, hvalV.symm.trans hw⟩
  obtain ⟨c, hcu⟩ := mem_range_of_traits f hf0 (u : Localization.Away f) (fun V _ _ _ _ hcomp hfin t ht h hh => by
    obtain ⟨w, hw⟩ := trait V hcomp hfin t ht h hh
    exact ⟨w, hw⟩)
  obtain ⟨c', hcu'⟩ := mem_range_of_traits f hf0 ((u⁻¹ : (Localization.Away f)ˣ) : Localization.Away f)
    (fun V _ _ _ _ hcomp hfin t ht h hh => by
      obtain ⟨w, hw⟩ := trait V hcomp hfin t ht h hh
      refine ⟨((w⁻¹ : Vˣ) : V), ?_⟩
      rw [map_units_inv, map_units_inv, hw])
  have hcc : c * c' = 1 := hinj (by rw [map_mul, hcu, hcu', Units.mul_inv, map_one])
  refine ⟨⟨c, c', hcc, by rw [mul_comm]; exact hcc⟩, ?_⟩
  rw [hval, Units.val_mk, ← hcu, ← RingHom.comp_apply, hc]

end GlobalTheory.KeyEven.LocPf
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TraitTwist

theorem exists_bundle_data_at_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₉ : Type) [CommRing R₉] [IsDomain R₉] [IsLocalRing R₉] (ρ₉ : R →+* R₉) (G₉ : Over (Sp R₉)) [GrpObj G₉] [IsCommMonObj G₉] (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P₉ : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ₉ → IsGrpPullback G₉ G (spMap ρ₉) β₉ → Geo.Tor.IsSquare β₉ β₉₂ → IsSemiAbelian G₉ → LBIso (abelian₂ G₉ P₉.L.L) ((abelian₂ G' U'.LG.L).pull (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) → EvenOn P₉ → IsMonHom gen₉.hom → LBIso (A₉.L.pull gen₉.hom.left) (P₉.L.L.pull (pullback.fst G₉.hom (jK R₉))) → ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsLocalRing R₀) (ρ₀ : R →+* R₀) (D₀ : DegData R₀ (maximalIdeal R₀)) (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (_ : IsCommMonObj G₀) (β₀ : G₀.left ⟶ G.left) (β₀₂ : (G2 G₀).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₀) (A₀ : PolAV (Sp (FractionRing R₀))) (gen₀ : (Over.pullback (jK R₀)).obj G₀ ≅ A₀.A), FinExt ρ₀ ∧ Nonempty (IsPullDeg ρ₀ D.toPre D₀.toPre) ∧ IsGrpPullback G₀ G (spMap ρ₀) β₀ ∧ Geo.Tor.IsSquare β₀ β₀₂ ∧ IsSemiAbelian G₀ ∧ LBIso (abelian₂ G₀ P.L.L) ((abelian₂ G' U'.LG.L).pull (β₀₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P ∧ IsMonHom gen₀.hom ∧ LBIso (A₀.L.pull gen₀.hom.left) (P.L.L.pull (pullback.fst G₀.hom (jK R₀))) ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R₀ →+* W), Function.Injective φ → IsLocalHom φ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), IsGrpPullback GW G₀ (spMap φ) β → LBIso UW.LG.L (P.L.L.pull β) → Nonempty (IsPullDeg φ D₀.toPre DW.toPre) := by
  intro R _ _ _ hR D D' F A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi R₉ _ _ _ ρ₉ G₉ _ _ β₉ β₉₂ P₉ A₉ gen₉ hfin₉ hpb₉ hsq₉ hG₉ hlam₉ hev₉ hgen₉ hgl₉
  have hR₉ : Base R₉ := ⟨hfin₉.1, by
    haveI := hR.2
    exact charZero_of_injective_ringHom hfin₉.2.1⟩
  obtain ⟨D₉', U₉, hL₉, -⟩ := GlobalTheory.T.exists_uniformisation_completeLocal_evenOnTorus R₉ hR₉ G₉ P₉ hG₉ hev₉ A₉ gen₉ hgen₉ hgl₉
  obtain ⟨D₉, hD₉, hsame⟩ := GlobalTheory.T.uniformisation_pulledBackFactor_samePolarisation R hR D D' F A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi R₉ ρ₉ G₉ β₉ β₉₂ P₉ hfin₉ hpb₉ hsq₉ hG₉ hlam₉ A₉ D₉' U₉ hL₉
  obtain ⟨R₀, _, _, _, ρ, D₀, G₀, _, _, β, β₂, A₀, U₀, hfin, hD₀, hpb, hsq, hlam⟩ :=
    GlobalTheory.T.samePolarisedData_uniformise_finite_extension R₉ hR₉ D₉ D₉' A₉ G₉ hG₉ U₉ hsame
  have hG₀ : IsSemiAbelian G₀ := GlobalTheory.SiegLoc.TraitOrd.isSemiAbelian_of_isGrpPullback hpb hG₉
  obtain ⟨P, hPL, hPE⟩ := GlobalTheory.Mum.unif_evenOn R₀ hfin.1 D₀ A₀ G₀ hG₀ U₀
  obtain ⟨hfin', hD'⟩ := GlobalTheory.Mum.FinExtComp.finExt_comp_isPullDeg R R₉ R₀ ρ₉ ρ D.toPre D₉.toPre D₀.toPre hfin₉ hfin hD₉ hD₀
  have hsp : spMap (ρ.comp ρ₉) = spMap ρ ≫ spMap ρ₉ := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  refine ⟨R₀, inferInstance, inferInstance, inferInstance, ρ.comp ρ₉, D₀, G₀, inferInstance, inferInstance, β ≫ β₉, β₂ ≫ β₉₂, P, A₀, U₀.gen,
    hfin', hD', ?_, GlobalTheory.ZM.SiegPull.isSquare_comp hsq hsq₉, hG₀, ?_, hPE, U₀.gen_hom, ?_, ?_⟩
  · rw [hsp]; exact IsGrpPullback.comp hpb hpb₉
  · rw [hPL]
    rw [← hL₉] at hlam₉
    have i₁ : (abelian₂ G₀ U₀.LG.L).IsLB := LB.isLB_linComb U₀.LG.isLB _ _
    have i₂ : ((abelian₂ G₉ U₉.LG.L).pull β₂).IsLB := pull_isLB (LB.isLB_linComb U₉.LG.isLB _ _) _
    have i₃ : ((abelian₂ G' U'.LG.L).pull ((β₂ ≫ β₉₂) ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)).IsLB :=
      pull_isLB (LB.isLB_linComb U'.LG.isLB _ _) _
    exact LBIso.trans i₁ i₂ i₃ hlam (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hlam₉ β₂ (Category.assoc _ _ _))
  · rw [hPL]; exact U₀.ext
  · intro W _ _ _ hW φ hφ hloc GW _ _ βW DW AW UW hpbW hLW
    rw [hPL] at hLW
    exact GlobalTheory.T.uniformization_base_change_complete_dvr R₀ hfin.1 D₀ A₀ G₀ hG₀ U₀ W hW φ hφ hloc GW βW DW AW UW hpbW hLW

end GlobalTheory.Mum.TraitTwist
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_labelledCover_embedding_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D' : DegData R' (maximalIdeal R')) (C' : LabCover D') (E : Emb C'.π C'.G), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ E.Theta C'.P.L.L := by
  first | exact @GlobalTheory.Mum.exists_emb_of_labCover | exact GlobalTheory.Mum.exists_emb_of_labCover | (intros; apply GlobalTheory.Mum.exists_emb_of_labCover <;> assumption)
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem galTransport : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, (∀ x, a (D.lab x) = D.lab x) ∧ ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (h' : (y ≫ s) ≫ D.q = c.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab D.X D.ε (D.lift c y h) yy → IsLab D.X D.ε (D.lift c (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  intro g n F W Z i X₁ hg hn ho hi he ht hp ε₁ hd D σ s hs
  obtain ⟨a, hG, hfix⟩ := GlobalTheory.T.galois_automorphism_acts_on_deeper_level_labels g n F W Z i X₁ hg hn ho hi he ht hp ε₁ hd D σ
  exact ⟨a, hfix, fun p _ z₁ c y h h' yy hL =>
    GlobalTheory.T.thetaSetup_labelling_transport_galoisConjugate g n F W Z i X₁ hg hn ho hi he ht hp ε₁ hd D σ s hs a hG p z₁ c y h h' yy hL⟩

end GlobalTheory.Poinc
end
end
