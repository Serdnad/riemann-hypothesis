module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle375
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle437
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BigBlockCharacters
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060

@[expose] public section

section

open Matrix

noncomputable section
namespace GlobalTheory.SvNAnyChar

def scaleSnd {k : Type} [Field k] {κ : Type} (c : k) :
    (κ → k) × (κ → k) →+ (κ → k) × (κ → k) where
  toFun w := (w.1, c • w.2)
  map_zero' := by simp
  map_add' a b := by simp

@[simp] theorem scaleSnd_fst {k : Type} [Field k] {κ : Type} (c : k) (w : (κ → k) × (κ → k)) :
    (scaleSnd c w).1 = w.1 := rfl

@[simp] theorem scaleSnd_snd {k : Type} [Field k] {κ : Type} (c : k) (w : (κ → k) × (κ → k)) :
    (scaleSnd c w).2 = c • w.2 := rfl

theorem schr_mulShift_scaleSnd {k : Type} [Field k] [Invertible (2 : k)] {κ : Type} [Fintype κ]
    (ψ : AddChar k ℂ) {c : k} (hc : c ≠ 0) (w : (κ → k) × (κ → k)) (φ : (κ → k) → ℂ) :
    GlobalTheory.WeilM.schr (ψ.mulShift c) (scaleSnd c⁻¹ w) φ = GlobalTheory.WeilM.schr ψ w φ := by
  funext x
  simp only [GlobalTheory.WeilM.schr, scaleSnd_fst, scaleSnd_snd, AddChar.mulShift_apply, dotProduct_smul,
    smul_eq_mul]
  congr 2
  rw [mul_add, mul_left_comm c (⅟2), mul_inv_cancel_left₀ hc, mul_inv_cancel_left₀ hc]

theorem stoneVonNeumann_any_char :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Invertible (2 : k)] {κ : Type} [Fintype κ] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (wT wM : Matrix (Fin n) (Fin d) k →+ (κ → k) × (κ → k)),
    (∀ Y Y', (wT Y).1 ⬝ᵥ (wT Y').2 - (wT Y').1 ⬝ᵥ (wT Y).2 = 0) →
    (∀ z z', (wM z).1 ⬝ᵥ (wM z').2 - (wM z').1 ⬝ᵥ (wM z).2 = 0) →
    (∀ Y z, (wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2 = ∑ i, ∑ j, Y i j * z i j) →
    (∀ w, ∃ Y z, wT Y + wM z = w) →
    ∃ ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ),
      Set.BijOn ι (GlobalTheory.WeilM.SB (κ → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) ∧
      (∀ Y, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wT Y) φ) = fun Y' => ι φ (Y' + Y)) ∧
      (∀ z, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wM z) φ) = fun Y' => ψ0 (∑ i, ∑ j, Y' i j * z i j) * ι φ Y') := by
  intro k _ _ _ _ _ _ κ _ n d ψ0 hψ hne wT wM hT hM hTM hsurj
  obtain ⟨c, hc, hcond⟩ := GlobalTheory.CondRescale.exists_rescale_conductor_integers ψ0 hψ hne
  have hψ1 : Continuous (ψ0.mulShift c) := by
    have : (ψ0.mulShift c : k → ℂ) = fun x => ψ0 (c * x) := by
      funext x
      exact AddChar.mulShift_apply
    rw [this]
    exact hψ.comp (continuous_const.mul continuous_id)
  let S : Matrix (Fin n) (Fin d) k →+ Matrix (Fin n) (Fin d) k :=
    { toFun := fun z => c • z
      map_zero' := smul_zero c
      map_add' := smul_add c }
  have hS : ∀ z, S z = c • z := fun _ => rfl
  have hsum : ∀ (a : k) (Y z : Matrix (Fin n) (Fin d) k),
      ∑ i, ∑ j, Y i j * (a • z) i j = a * ∑ i, ∑ j, Y i j * z i j := by
    intro a Y z
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨ι, hbij, h1, h2⟩ := GlobalTheory.T.stoneVonNeumann_schwartzBruhat_transverseLagrangians (κ := κ) (n := n) (d := d) (ψ0.mulShift c) hψ1
    (fun x => by simpa only [AddChar.mulShift_apply] using hcond x)
    ((scaleSnd c⁻¹).comp wT) ((scaleSnd c⁻¹).comp (wM.comp S))
    (fun Y Y' => by
      simp only [AddMonoidHom.comp_apply, scaleSnd_fst, scaleSnd_snd, dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, hT, mul_zero])
    (fun z z' => by
      simp only [AddMonoidHom.comp_apply, scaleSnd_fst, scaleSnd_snd, dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, hM, mul_zero])
    (fun Y z => by
      simp only [AddMonoidHom.comp_apply, scaleSnd_fst, scaleSnd_snd, dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, hTM, hS, hsum, inv_mul_cancel_left₀ hc])
    (fun w => by
      obtain ⟨Y, z, h⟩ := hsurj (scaleSnd c w)
      refine ⟨Y, c⁻¹ • z, ?_⟩
      simp only [AddMonoidHom.comp_apply]
      rw [hS, smul_inv_smul₀ hc, ← map_add (f := _), h]
      exact Prod.ext rfl (inv_smul_smul₀ hc _))
  refine ⟨ι, hbij, fun Y φ hφ => ?_, fun z φ hφ => ?_⟩
  · have := h1 Y φ hφ
    rwa [AddMonoidHom.comp_apply, schr_mulShift_scaleSnd ψ0 hc] at this
  · have := h2 (c⁻¹ • z) φ hφ
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, schr_mulShift_scaleSnd ψ0 hc, hS,
      smul_inv_smul₀ hc] at this
    rw [this]
    funext Y'
    rw [AddChar.mulShift_apply, hsum, mul_inv_cancel_left₀ hc]

end GlobalTheory.SvNAnyChar
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
namespace GlobalTheory.StrataBertini

theorem isLocalization_atPrime_quotient {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime S p] (I : Ideal A) (hI : I ≤ p)
    [(p.map (Ideal.Quotient.mk I)).IsPrime] :
    IsLocalization.AtPrime (S ⧸ I.map (algebraMap A S)) (p.map (Ideal.Quotient.mk I)) := by
  constructor
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : a ∉ p := fun h => hx (Ideal.mem_map_of_mem _ h)
    simp only [Ideal.Quotient.algebraMap_quotient_map_quotient]
    exact (IsLocalization.map_units S (⟨a, ha⟩ : p.primeCompl)).map _
  · intro z
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj p.primeCompl w
    refine ⟨⟨Ideal.Quotient.mk I a, ⟨Ideal.Quotient.mk I s, ?_⟩⟩, ?_⟩
    · exact fun hs => s.2 ((Ideal.mem_quotient_iff_mem hI).1 hs)
    · simp only [Ideal.Quotient.algebraMap_quotient_map_quotient]
      rw [← map_mul, h]
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.eq, ← map_sub] at hxy
    rw [IsLocalization.mem_map_algebraMap_iff p.primeCompl S] at hxy
    obtain ⟨⟨⟨i, hi⟩, m⟩, hm⟩ := hxy
    rw [← map_mul, IsLocalization.eq_iff_exists p.primeCompl S] at hm
    obtain ⟨c, hc⟩ := hm
    refine ⟨⟨Ideal.Quotient.mk I (c * m), ?_⟩, ?_⟩
    · exact fun hs => (p.primeCompl.mul_mem c.2 m.2) ((Ideal.mem_quotient_iff_mem hI).1 hs)
    · show Ideal.Quotient.mk I (↑c * ↑m) * Ideal.Quotient.mk I a = Ideal.Quotient.mk I (↑c * ↑m) * Ideal.Quotient.mk I b
      rw [← sub_eq_zero, ← mul_sub, ← map_sub, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have : (↑c * ↑m * (a - b) : A) = ↑c * i := by linear_combination hc
      rw [this]
      exact I.mul_mem_left _ hi

end GlobalTheory.StrataBertini

namespace GlobalTheory.StrataBertini

open IsLocalRing in
theorem linearIndependent_option_cotangent {S : Type*} [CommRing S] [IsLocalRing S] {J : Type*}
    [Fintype J] (w : Option J → S) (hw : ∀ j, w j ∈ maximalIdeal S)
    (hind : LinearIndependent (ResidueField S)
      (fun j : J => ((maximalIdeal S).toCotangent ⟨w (some j), hw (some j)⟩ : CotangentSpace S)))
    (hnot : w none ∉ maximalIdeal S ^ 2 ⊔ Ideal.span (Set.range (fun j : J => w (some j)))) :
    LinearIndependent (ResidueField S)
      (fun j : Option J => ((maximalIdeal S).toCotangent ⟨w j, hw j⟩ : CotangentSpace S)) := by
  rw [linearIndependent_option]
  refine ⟨hind, fun hmem => hnot ?_⟩
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  choose b hb using fun j => IsLocalRing.residue_surjective (c j)
  have hc' : ∑ j, b j • (maximalIdeal S).toCotangent ⟨w (some j), hw (some j)⟩ =
      (maximalIdeal S).toCotangent ⟨w none, hw none⟩ := by
    rw [← hc]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.comp_apply, ← hb j, ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]
  have h0 : (maximalIdeal S).toCotangent
      (⟨w none, hw none⟩ - ∑ j, b j • ⟨w (some j), hw (some j)⟩) = 0 := by

    rw [map_sub, map_sum]
    simp only [map_smul]
    rw [hc', sub_self]
  rw [Ideal.toCotangent_eq_zero] at h0
  have h1 : w none = (w none - ∑ j, b j * w (some j)) + ∑ j, b j * w (some j) := by ring
  rw [h1]
  refine Submodule.add_mem_sup ?_ ?_
  · simpa using h0
  · exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

end GlobalTheory.StrataBertini

namespace GlobalTheory.StrataBertini

open IsLocalRing in
theorem key (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ)
    [SmoothOfRelativeDimension n q] (U : Y.Opens) (z : Fin n → Γ(Y, U)) (hfr : IsFrame (dOn q z))
    (ι : Type) [Fintype ι] (f : ι → Γ(Y, U)) (J : Finset (Fin n)) :
    ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 →
      ∀ (y : Y) (hy : y ∈ U), (∃ i, y ∈ Y.basicOpen (f i)) →
      (∀ j : J, Y.presheaf.germ U y hy (z j) ∈ maximalIdeal (Y.presheaf.stalk y)) →
      Y.presheaf.germ U y hy (∑ i, algX q U (u i) * f i) ∈ maximalIdeal (Y.presheaf.stalk y) →
      Y.presheaf.germ U y hy (∑ i, algX q U (u i) * f i) ∉
        maximalIdeal (Y.presheaf.stalk y) ^ 2 ⊔
          Ideal.span (Set.range (fun j : J => Y.presheaf.germ U y hy (z j))) := by
  have hU : IsAffineOpen U := hfr.affine
  set I : Ideal Γ(Y, U) := Ideal.span (z '' (J : Set (Fin n))) with hIdef
  letI : Algebra ℂ (Γ(Y, U) ⧸ I) := ((Ideal.Quotient.mk I).comp (algX q U)).toAlgebra
  haveI : Algebra.Smooth ℂ (Γ(Y, U) ⧸ I) := GlobalTheory.T.smooth_coordinateStratum_etaleChart Y q n U z hfr J
  obtain ⟨Q1, hQ1, hQ1u⟩ :=
    GlobalTheory.bertini_cotangent_independent ℂ (Γ(Y, U) ⧸ I) (fun i => Ideal.Quotient.mk I (f i)) 1
  have hinj : Function.Injective (Prod.snd : Fin 1 × ι → ι) :=
    fun a b h => Prod.ext (Subsingleton.elim _ _) h
  refine ⟨MvPolynomial.rename Prod.snd Q1, fun h0 => hQ1 (MvPolynomial.rename_injective _ hinj
    (by rw [h0, map_zero])), ?_⟩
  intro u hu y hy hf hz ht
  have hu' : MvPolynomial.eval (u ∘ Prod.snd) Q1 ≠ 0 := by rwa [MvPolynomial.eval_rename] at hu
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hy⟩
  set p := (hU.primeIdealOf ⟨y, hy⟩).asIdeal with hpdef
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) p := hU.isLocalization_stalk ⟨y, hy⟩
  have hgerm : ∀ a, algebraMap Γ(Y, U) (Y.presheaf.stalk y) a = Y.presheaf.germ U y hy a :=
    fun a => rfl
  have hpm : ∀ a, a ∈ p ↔ Y.presheaf.germ U y hy a ∈ maximalIdeal (Y.presheaf.stalk y) := by
    intro a
    rw [← hgerm]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Y.presheaf.stalk y) p a).symm
  have hIp : I ≤ p := Ideal.span_le.2 (by
    rintro _ ⟨j, hj, rfl⟩
    exact (hpm _).2 (hz ⟨j, hj⟩))
  haveI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIp)
  set IS := I.map (algebraMap Γ(Y, U) (Y.presheaf.stalk y)) with hISdef
  have hISm : IS ≤ maximalIdeal (Y.presheaf.stalk y) :=
    Ideal.map_le_iff_le_comap.2 (fun a ha => (hpm a).1 (hIp ha))
  haveI : Nontrivial (Y.presheaf.stalk y ⧸ IS) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hISm)
  haveI : IsLocalRing (Y.presheaf.stalk y ⧸ IS) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk IS) Ideal.Quotient.mk_surjective
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y ⧸ IS) (p.map (Ideal.Quotient.mk I)) :=
    isLocalization_atPrime_quotient p I hIp
  have hmk : ∀ a ∈ maximalIdeal (Y.presheaf.stalk y),
      Ideal.Quotient.mk IS a ∈ maximalIdeal (Y.presheaf.stalk y ⧸ IS) := by
    intro a ha
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hun
    obtain ⟨c, hc⟩ := hun.exists_right_inv
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← map_mul, ← map_one (Ideal.Quotient.mk IS), Ideal.Quotient.eq] at hc
    have h1 : a * c' ∈ maximalIdeal (Y.presheaf.stalk y) := Ideal.mul_mem_right _ _ ha
    have h2 := Ideal.sub_mem _ h1 (hISm hc)
    rw [sub_sub_cancel] at h2
    exact (maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h2)
  have hfi : ∃ i, Ideal.Quotient.mk I (f i) ∉ p.map (Ideal.Quotient.mk I) := by
    obtain ⟨i, hi⟩ := hf
    refine ⟨i, ?_⟩
    rw [Ideal.mem_quotient_iff_mem hIp, hpm]
    exact fun h => ((IsLocalRing.mem_maximalIdeal _).1 h) ((Y.mem_basicOpen _ _ hy).1 hi)
  have htR : algebraMap (Γ(Y, U) ⧸ I) (Y.presheaf.stalk y ⧸ IS)
      (∑ i, (u ∘ Prod.snd) ((0 : Fin 1), i) • Ideal.Quotient.mk I (f i)) =
      Ideal.Quotient.mk IS (Y.presheaf.germ U y hy (∑ i, algX q U (u i) * f i)) := by

    rw [← hgerm, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, map_mul, map_mul]
    rfl
  have hli := hQ1u (u ∘ Prod.snd) hu' (p.map (Ideal.Quotient.mk I)) (Y.presheaf.stalk y ⧸ IS) hfi
  have hmemR : algebraMap (Γ(Y, U) ⧸ I) (Y.presheaf.stalk y ⧸ IS)
      (∑ i, (u ∘ Prod.snd) ((0 : Fin 1), i) • Ideal.Quotient.mk I (f i)) ∈
      maximalIdeal (Y.presheaf.stalk y ⧸ IS) := by
    rw [htR]; exact hmk _ ht
  have hne := hli.ne_zero ⟨0, hmemR⟩
  rw [Ne, Ideal.toCotangent_eq_zero] at hne
  intro hmem2
  apply hne
  show algebraMap (Γ(Y, U) ⧸ I) (Y.presheaf.stalk y ⧸ IS)
      (∑ i, (u ∘ Prod.snd) ((0 : Fin 1), i) • Ideal.Quotient.mk I (f i)) ∈ _
  rw [htR]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmem2
  have hbI : b ∈ IS := by
    refine (Ideal.span_le.2 ?_) hb
    rintro _ ⟨j, rfl⟩
    exact Ideal.mem_map_of_mem (algebraMap Γ(Y, U) (Y.presheaf.stalk y)) (Ideal.subset_span ⟨j, j.2, rfl⟩)
  rw [← hab, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 hbI, add_zero]
  have hma : Ideal.Quotient.mk IS a ∈ (maximalIdeal (Y.presheaf.stalk y)).map (Ideal.Quotient.mk IS) ^ 2 := by
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ ha
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hmk) 2 hma

end GlobalTheory.StrataBertini

namespace GlobalTheory.StrataBertini

theorem bertini_strata_cotangent : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (U : Y.Opens) (z : Fin n → Γ(Y, U)), IsFrame (dOn q z) → ∀ (ι : Type) [Fintype ι] (f : ι → Γ(Y, U)), ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ (y : Y) (hy : y ∈ U), (∃ i, y ∈ Y.basicOpen (f i)) → ∀ (J : Finset (Fin n)) (h : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim (∑ i, algX q U (u i) * f i) fun j => z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : Option J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨(fun j : Option J => Y.presheaf.germ U y hy (j.elim (∑ i, algX q U (u i) * f i) fun j => z j)) j, h j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y))) := by
  intro Y _ _ q n _ U z hfr ι _ f
  choose Q hQ0 hQ using fun J : Finset (Fin n) => key Y q n U z hfr ι f J
  refine ⟨∏ J, Q J, Finset.prod_ne_zero_iff.2 fun J _ => hQ0 J, fun u hu y hy hf J h => ?_⟩
  rw [map_prod] at hu
  have huJ := Finset.prod_ne_zero_iff.1 hu J (Finset.mem_univ _)
  exact linearIndependent_option_cotangent
    (fun j : Option J => Y.presheaf.germ U y hy (j.elim (∑ i, algX q U (u i) * f i) fun j => z j)) h
    (GlobalTheory.T.linearIndependent_cotangent_of_isTopFormFrame_of_vanishing Y q n U z hfr y hy J (fun j => h (some j)))
    (hQ J u huJ y hy hf (fun j => h (some j)) (h none))

end GlobalTheory.StrataBertini
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.exists_push_sections_canonical_modification : ∀ (F : Type) [Field F] [CharZero F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (d : ℕ) [SmoothOfRelativeDimension d p] (U : Y.Opens) (M : Modif p U d) (K : CanonLB p d) (K' : CanonLB M.str d) (B : LB Y), IsProjOver p → (U : Set Y).Nonempty → B.IsLB → ∃ Ψ : H0 M.str (tens K'.bundle (B.pull M.σ)) ⊤ → H0 p (tens K.bundle B) ⊤, ∀ (z : Sp ℂ ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ M.opn → ∀ (k' : (tens K'.bundle (B.pull M.σ)).ι) (hk' : ⊤ ≤ z ⁻¹ᵁ (tens K'.bundle (B.pull M.σ)).U k') (k : (tens K.bundle B).ι) (hk : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (tens K.bundle B).U k), ∃ lam : ℂˣ, ∀ g, H0.val (z ≫ M.σ) k le_top hk (Ψ g) = lam * H0.val z k' le_top hk' g := by
  first | exact @GlobalTheory.ModifCanon.exists_push_sections | exact GlobalTheory.ModifCanon.exists_push_sections | (intros; apply GlobalTheory.ModifCanon.exists_push_sections <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.SerBase

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)

abbrev delW : Formalism.L2.Host.HChar D.host.E := (R2 p).C.delAt (Formalism.EigenvalueLevelCeiling.plc (D.plEq w))

abbrev plW : Finset (Pl D.host.E) := GlobalTheory.OnTies.placesOver (R2 p) ((R2 p).mu (D.plEq w)) (ownAt D (D.plEq w))

abbrev IsEv (u : ∀ τ, lowT ((R2 p).MW j (sg0 D p.P.A3.A)) τ) : Prop :=
  ∀ τ, (u τ : ((R2 p).MW j (sg0 D p.P.A3.A)).sm τ) = p.v₀ j (sg0 D p.P.A3.A) τ

def KerOf : Prop := ∀ ρ : Setup D.ntw, ρ.Good → RealPin p.R p.cG ρ →
  BaseOf (R2 p) j (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) ∧ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q = plW p w ∧
    ∃ ξR φ, KerDat (R2 p) j (delW p w) (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.chi ξR (plW p w)
      (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1) φ

def TraceOf : Prop := ∀ ρ : Setup D.ntw, ρ.Good → RealPin p.R p.cG ρ → ρ.LevelOf D.nexp → ∀ h P,
  ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h P = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹
    (series (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).F (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1)
      (princ (ρ.B (ex.nch.twI w) j (ex.nch.sd w))).vecBase h P)

def KerRat : Prop := ∀ χ ξR ω φ, KerDat (R2 p) j (delW p w) χ ξR (plW p w) ω φ → ∀ h ∈ GfC (Vc D j), ∀ y, InCoefLat (R2 p) j h y →
  ∀ u, IsEv p j u → ∃ x, adForm (R2 p) j x (fun τ => u τ) = singleSeries (R2 p) j ω φ h y u

def LatIo : Prop := ∀ ρ : Setup D.ntw, ρ.Good → RealPin p.R p.cG ρ → ∀ c : ℂ, c ≠ 0 →
  IsScale p.R p.v₀ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) c → ∃ u, IsEv p j u ∧ ∀ h ∈ GfC (Vc D j),
    ∀ P ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h,
      ∃ y, InCoefLat (R2 p) j h y ∧ (R2 p).ioP j (PiTensorProduct.tprod ℂ u) y = c • P

def ReadCmp : Prop := ∀ (ρ : Setup D.ntw) (hρ : ρ.Good) (e : FractionRing (ex.nch.Oe w) →+* ℂ),
  (∀ x, e (ex.nch.embW w x) = D.what₂.embLL x) →
  (∀ a : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w),
    e (algebraMap (ex.nch.Oe w) _ (algebraMap _ (ex.nch.Oe w) a)) = ρ.eOk (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) a) →
  ∀ ν : ℂ, ν ≠ 0 → ∀ rd : Can p w j, IsCan p rd → ∀ u, IsEv p j u → ∀ f x (a : ℂ),
    rdAt p w j hρ ν f = a • ν⁻¹ • adForm (R2 p) j x (fun τ => u τ) →
      f = 0 ∨ ∃ b, e b = a ∧ ((1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] f : Tgt ex w j) = b • rd x

end Point

def FlatKer : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
  (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R →
  ∀ i : Fin D.R.m, VStd D i → ∀ B : Base (Vc D i) (Wc D i), B.Good → BaseOf R i B →
  ∀ ξ ξR ω φ, KerDat R i ξ B.de.chi ξR B.de.Q ω φ → (∃ t, B.de.Q ⊆ R.Q t) → ∀ N : ℕ, N ≠ 0 →
    (∀ PP ∈ B.de.Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∃ (z : GA D (Vc D i)) (c : ℂ), IsCentAt i B.de.Q z ∧ UnitOff N c ∧
      ∀ h P, series B.F ω (princ B).vecBase h P = c • series B.F ω φ (h * z) P

def CentLat : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
  (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (Q : Finset (Pl D.host.E))
  (z : GA D (Vc D i)), IsCentAt i Q z → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∃ m : ℕ, ∀ h ∈ GfC (Vc D i), ∀ y, (InCoefLat R i h y → InCoefLat R i (h * z) ((N : ℂ) ^ m • y)) ∧
      (InCoefLat R i (h * z) y → InCoefLat R i h ((N : ℂ) ^ m • y))

def TraceRat : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
  (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → R.LUnif →
  ∀ (i : Fin D.R.m) (v₀ : (R.MW i (sg0 D A)).Vec), IsExtVec (R.MW i (sg0 D A)) v₀ →
  ∀ ξ χ ξR Q ω φ, KerDat R i ξ χ ξR Q ω φ → ∀ (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) h y
    (u : ∀ τ, lowT (R.MW i (sg0 D A)) τ), (∀ τ, (u τ : (R.MW i (sg0 D A)).sm τ) = v₀ τ) →
    ∀ x, adForm R i x (fun τ => u τ) = singleSeries R i ω φ h y u →
      ∃ x', ∀ v : ∀ τ, lowT (R.MW i (sg0 D A)) τ, adForm R i x' (fun τ => v τ) = levelTrace R i U ψ (singleSeries R i ω φ h y v)

def OwnUnit : Prop := ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl), IsUnit ((ownAt D (D.plEq w) : ℕ) : c.Oe w)

end GlobalTheory.BigOn.Exp.SerBase
end
end

section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

theorem _root_.GlobalTheory.T.runNumericalConditions_hold_along_family : ∀ x₁ : ℝ, Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x, PageNum (Fm.parT x hx ι) x₁ ∧ 3 ≤ (Fm.L x ι).sc.x ∧ ((Fm.D x ι).R.k : ℝ) * (Fm.L x ι).sc.b' ≤ (Fm.L x ι).sc.b ∧ 3 ≤ (Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 5) ∧ 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 4 ≤ (Fm.D x ι).R.nV := by
  first | exact @GlobalTheory.OntoNum.pageNum_along | exact GlobalTheory.OntoNum.pageNum_along | (intros; apply GlobalTheory.OntoNum.pageNum_along <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

theorem _root_.GlobalTheory.T.meanLogSupNorm_lowerBound_principalLevel : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ F ∈ cusp Xo c U a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → F ≠ 0 → -lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) ≤ (∑ σ : c.F →+* ℂ, Real.log (supC Xo c U (xiR D) (goodOf c σ) a n F)) / (Module.finrank ℚ c.F : ℝ) := by
  first | exact @GlobalTheory.lamSup_of_laws | exact GlobalTheory.lamSup_of_laws | (intros; apply GlobalTheory.lamSup_of_laws <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

theorem _root_.GlobalTheory.T.dividedPowerContent_detPow_depends_on_p_i_k : ∀ (p : ℕ), p.Prime → ∀ i k : ℕ, ∃ κ : ℝ, ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), v (p : C) = 1 → content v (detPow C i k) = (κ : EReal) := by
  first | exact @GlobalTheory.detPow_content_const | exact GlobalTheory.detPow_content_const | (intros; apply GlobalTheory.detPow_content_const <;> assumption)
end
