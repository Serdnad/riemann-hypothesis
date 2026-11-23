module

public import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeron
public import GroundTheory.GlobalFields.ComplexMultiplication.PrimeLocalization
public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle006
public import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
public import Mathlib.RingTheory.Frobenius
public import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityHom
public import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupAction
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.Bundle006
public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle011
public import GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimes
import GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimesIsogeny
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

namespace GroundTheory.Global

noncomputable section

open IsLocalRing WeierstrassCurve GroundTheory.Arith.Abelian

section VariableChange

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  (C : VariableChange 𝒪) [W.IsElliptic] [DecidableEq K]


omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] [W.IsElliptic] [DecidableEq K] in
theorem vcX_notMem_range {X : K} (hX : X ∉ Set.range (algebraMap 𝒪 K)) :
    vcX (C.map (algebraMap 𝒪 K)) X ∉ Set.range (algebraMap 𝒪 K) := by
  rintro ⟨a, ha⟩
  apply hX
  refine ⟨vcX' C a, ?_⟩
  rw [map_vcX', ha]
  exact vcX'_vcX _ X

theorem reducePoint_vcEquivK (P : (curveK K W).Point) :
    reducePoint K (C • W) (vcEquivK K W C P) =
      vcPoint (C.map (residue 𝒪)) (map_vc_eq_residue W C) (reducePoint K W P) := by
  rcases point_cases K W P with rfl | ⟨X, Y, h, rfl, hX⟩ | ⟨x, y, h, rfl⟩
  · rw [vcEquivK_zero, reducePoint_zero, reducePoint_zero]
    rfl
  · rw [vcEquivK_some K W C h (nonsingular_K_vc K W C h),
      reducePoint_some_notMem K (C • W) _ (vcX_notMem_range K C hX), reducePoint_some_notMem K W h hX]
    rfl
  · have n₁ := nonsingular_residue_of_isElliptic K W h.1
    have hx : vcX (C.map (algebraMap 𝒪 K)) (algebraMap 𝒪 K x) = algebraMap 𝒪 K (vcX C x) :=
      (map_vcX C (algebraMap 𝒪 K) x).symm
    have hy : vcY (C.map (algebraMap 𝒪 K)) (algebraMap 𝒪 K x) (algebraMap 𝒪 K y) =
        algebraMap 𝒪 K (vcY C x y) :=
      (map_vcY C (algebraMap 𝒪 K) x y).symm
    have h₂ : (curveK K (C • W)).Nonsingular (algebraMap 𝒪 K (vcX C x))
        (algebraMap 𝒪 K (vcY C x y)) := by
      have := nonsingular_K_vc K W C h
      rwa [hx, hy] at this
    have n₂ := nonsingular_residue_of_isElliptic K (C • W) h₂.1
    have e : vcEquivK K W C (.some _ _ h) = .some _ _ h₂ := by
      rw [vcEquivK_some K W C h (nonsingular_K_vc K W C h), Affine.Point.some.injEq]
      exact ⟨hx, hy⟩
    rw [e, reducePoint_some_integral K (C • W) h₂ n₂, reducePoint_some_integral K W h n₁, vcPoint_some,
      Affine.Point.some.injEq]
    exact ⟨map_vcX C (residue 𝒪) x, map_vcY C (residue 𝒪) x y⟩

theorem reducePoint_vcPoint {W' : WeierstrassCurve 𝒪} (hC : C • W = W') (P : (curveK K W).Point) :
    reducePoint K W' (vcPoint (C.map (algebraMap 𝒪 K)) (by rw [map_vc_eq, hC]) P) =
      vcPoint (C.map (residue 𝒪)) (by rw [map_vc_eq_residue, hC]) (reducePoint K W P) := by
  subst hC
  exact reducePoint_vcEquivK K W C P

end VariableChange

section Frobenius

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField 𝒪) p] {g : 𝒪 →+* 𝒪}

variable [IsLocalHom g]

theorem residueField_map_eq_frobenius (hg : ∀ x, residue 𝒪 (g x) = residue 𝒪 x ^ p) :
    ResidueField.map g = frobenius (ResidueField 𝒪) p := by
  ext y
  obtain ⟨x, rfl⟩ := residue_surjective y
  rw [ResidueField.map_residue, hg, frobenius_def]

theorem map_residue_eq_frobeniusTwist (hg : ∀ x, residue 𝒪 (g x) = residue 𝒪 x ^ p) :
    (W.map (residue 𝒪)).map (frobenius (ResidueField 𝒪) p) = (W.map g).map (residue 𝒪) := by
  rw [← residueField_map_eq_frobenius p hg]
  exact map_curveRed_eq W

variable [W.IsElliptic] [DecidableEq K] [DecidableEq (ResidueField 𝒪)] {G : K →+* K}
  (hG : G.comp (algebraMap 𝒪 K) = (algebraMap 𝒪 K).comp g)


include hG in
theorem reducePoint_pointMapRing_frobenius (hg : ∀ x, residue 𝒪 (g x) = residue 𝒪 x ^ p)
    (P : (curveK K W).Point) :
    reducePoint K (W.map g) (pointCongr (map_curveK_eq K K hG W)
        (pointMapRing G (W.map (algebraMap 𝒪 K)) P)) =
      pointCongr (map_residue_eq_frobeniusTwist W p hg)
        (pointMapRing (frobenius (ResidueField 𝒪) p) (W.map (residue 𝒪)) (reducePoint K W P)) := by
  rw [reducePoint_pointMapRing K K hG W P,
    pointMapRing_congr (residueField_map_eq_frobenius p hg), pointCongr_pointCongr]

end Frobenius

section NumberField

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
  (𝔓 : HeightOneSpectrum (𝓞 L)) {τ : L ≃ₐ[K] L} (hτ : IsArithFrobAt (𝓞 K) τ 𝔓.asIdeal)

include hτ in
theorem mem_localizationAt_of_isArithFrobAt {x : L} (hx : x ∈ localizationAt L 𝔓) :
    τ x ∈ localizationAt L 𝔓 :=
  (Elliptic.residue_apply_of_isArithFrobAt 𝔓 hτ hx).1

def localizationAtRingHom : localizationAt L 𝔓 →+* localizationAt L 𝔓 :=
  ((τ : L →+* L).comp (localizationAt L 𝔓).val.toRingHom).codRestrict (localizationAt L 𝔓).toSubsemiring
    fun x ↦ mem_localizationAt_of_isArithFrobAt 𝔓 hτ x.2

theorem comp_algebraMap_localizationAtRingHom :
    (τ : L →+* L).comp (algebraMap (localizationAt L 𝔓) L) =
      (algebraMap (localizationAt L 𝔓) L).comp (localizationAtRingHom 𝔓 hτ) :=
  rfl

theorem residue_localizationAtRingHom (x : localizationAt L 𝔓) :
    residue (localizationAt L 𝔓) (localizationAtRingHom 𝔓 hτ x) =
      residue (localizationAt L 𝔓) x ^ Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K)) := by
  obtain ⟨h, e⟩ := Elliptic.residue_apply_of_isArithFrobAt 𝔓 hτ x.2
  exact e

theorem residue_localizationAtRingHom_of_absNorm [NumberField K] (𝔭 : HeightOneSpectrum (𝓞 K))
    [𝔓.asIdeal.LiesOver 𝔭.asIdeal] (x : localizationAt L 𝔓) :
    residue (localizationAt L 𝔓) (localizationAtRingHom 𝔓 hτ x) =
      residue (localizationAt L 𝔓) x ^ Ideal.absNorm 𝔭.asIdeal := by
  rw [residue_localizationAtRingHom]
  congr 1
  rw [← Ideal.LiesOver.over (P := 𝔓.asIdeal) (p := 𝔭.asIdeal), Ideal.absNorm_apply,
    Submodule.cardQuot_apply]

instance : IsLocalHom (localizationAtRingHom 𝔓 hτ) := by
  refine ⟨fun x hx ↦ ?_⟩
  rw [← residue_ne_zero_iff_isUnit] at hx ⊢
  rw [residue_localizationAtRingHom] at hx
  exact fun h ↦ hx (by rw [h, zero_pow hτ.card_pos.ne'])

theorem reducePoint_pointMapRing_localizationAtRingHom [NumberField K] (𝔭 : HeightOneSpectrum (𝓞 K))
    [𝔓.asIdeal.LiesOver 𝔭.asIdeal] (p : ℕ) [Fact p.Prime] (hp : Ideal.absNorm 𝔭.asIdeal = p)
    [CharP (ResidueField (localizationAt L 𝔓)) p] (W : WeierstrassCurve (localizationAt L 𝔓))
    [W.IsElliptic] [DecidableEq L] [DecidableEq (ResidueField (localizationAt L 𝔓))]
    (P : (curveK L W).Point) :
    reducePoint L (W.map (localizationAtRingHom 𝔓 hτ))
        (pointCongr (map_curveK_eq L L (comp_algebraMap_localizationAtRingHom 𝔓 hτ) W)
          (pointMapRing (τ : L →+* L) (W.map (algebraMap (localizationAt L 𝔓) L)) P)) =
      pointCongr (map_residue_eq_frobeniusTwist W p
          (fun x ↦ by rw [residue_localizationAtRingHom_of_absNorm 𝔓 hτ 𝔭 x, hp]))
        (pointMapRing (frobenius (ResidueField (localizationAt L 𝔓)) p)
          (W.map (residue (localizationAt L 𝔓))) (reducePoint L W P)) :=
  reducePoint_pointMapRing_frobenius L W p (comp_algebraMap_localizationAtRingHom 𝔓 hτ)
    (fun x ↦ by rw [residue_localizationAtRingHom_of_absNorm 𝔓 hτ 𝔭 x, hp]) P

end NumberField

end

end GroundTheory.Global
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian IsDedekindDomain
open scoped nonZeroDivisors

section VC

variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F] {A B : WeierstrassCurve F}
  [A.IsElliptic] [B.IsElliptic]

theorem homPt_vcHom (C : VariableChange F) (hC : C • A = B) (R : A.toAffine.Point) :
    homPt (vcHom C hC) R = vcPoint C hC R := by
  have h0 : vcHom C hC ≠ 0 := fun h ↦ vcPt_ne_zero C hC (congrArg Subtype.val h)
  rw [homPt, dite_eq_right h0, Isogeny.pointHom_apply]
  exact pointMap_eq_vcPoint C hC _ (isogOfHom_val _ h0) R

variable {A' B' : WeierstrassCurve F} [A'.IsElliptic] [B'.IsElliptic]

theorem homConstSet_conj (V : VariableChange F) (hV : V • A = B) (V' : VariableChange F)
    (hV' : V' • A' = B') :
    (homConstSet A A' : Set F) =
      ((homConst B' A' (vcHom V'⁻¹ (inv_smul_eq_of_smul_eq V' hV')) *
        homConst A B (vcHom V hV)) * ·) '' homConstSet B B' := by
  set Q := vcHom V hV
  set R := vcHom V'⁻¹ (inv_smul_eq_of_smul_eq V' hV')
  set Q' := vcHom V⁻¹ (inv_smul_eq_of_smul_eq V hV)
  set R' := vcHom V' hV'
  have e1 : homConst B A Q' * homConst A B Q = 1 := homConst_vcHom_mul_inv V hV
  have e2 : homConst B' A' R * homConst A' B' R' = 1 := homConst_vcHom_mul_inv V' hV'
  ext z
  simp only [SetLike.mem_coe, Set.mem_image]
  constructor
  · intro hz
    refine ⟨homConst A' B' R' * z * homConst B A Q', homConstSet_le_mul Q' R' hz, ?_⟩
    linear_combination (homConst A B Q * homConst B A Q' * z) * e2 + z * e1
  · rintro ⟨w, hw, rfl⟩
    have := homConstSet_le_mul Q R hw
    convert this using 1
    ring

end VC

section Lattice

variable {K : Type*} [Field K] [NumberField K] (σ₀ : K →+* ℂ) (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K]

theorem latticeEnd_eq_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    periodLatticeEnd L = periodLatticeEnd L' := by
  ext α
  show (∀ l ∈ L.lattice, α * l ∈ L.lattice) ↔ (∀ l ∈ L'.lattice, α * l ∈ L'.lattice)
  rw [h]


include hK in
theorem latticeEnd_eq_cmRing_of_lattice_eq {L : PeriodPair} {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : L.lattice = idealLattice σ₀ 𝔞) : periodLatticeEnd L = cmRingOfEmbedding σ₀ := by
  exact (latticeEnd_eq_of_lattice_eq (L' := idealPeriodPair σ₀ hK 𝔞)
    (h.trans (lattice_idealPeriodPair σ₀ hK 𝔞).symm)).trans
    (latticeEnd_idealPeriodPair σ₀ hK 𝔞)


include hK in
theorem exists_unit_of_forall_mem_iff (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {c : ℂ}
    (hc : ∀ z, z ∈ idealLattice σ₀ J ↔ c * z ∈ idealLattice σ₀ J) :
    ∃ ε : (𝓞 K)ˣ, c = σ₀ (algebraMap (𝓞 K) K ε) := by
  have hP := lattice_idealPeriodPair σ₀ hK J
  have hPend : periodLatticeEnd (idealPeriodPair σ₀ hK J) = cmRingOfEmbedding σ₀ :=
    latticeEnd_idealPeriodPair σ₀ hK J
  have hne : ∃ z, z ∉ idealLattice σ₀ J := by
    by_contra h
    push Not at h
    have h1 : (Real.sqrt 2 : ℂ) * (idealPeriodPair σ₀ hK J).ω₁ ∉ (idealPeriodPair σ₀ hK J).lattice :=
      sqrt_two_mul_notMem _
    rw [hP] at h1
    exact h1 (h _)
  obtain ⟨z₀, hz₀⟩ := hne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hz₀ ((hc z₀).2 (by rw [zero_mul]; exact zero_mem _))
  have mult : ∀ d : ℂ, (∀ l ∈ idealLattice σ₀ J, d * l ∈ idealLattice σ₀ J) → d ∈ cmRingOfEmbedding σ₀ := by
    intro d hd
    rw [← hPend]
    intro l hl
    rw [hP] at hl ⊢
    exact hd l hl
  obtain ⟨a, ha⟩ := (mem_cmRing σ₀).1 (mult c fun l hl ↦ (hc l).1 hl)
  obtain ⟨b, hb⟩ := (mem_cmRing σ₀).1 (mult c⁻¹ fun l hl ↦ (hc _).2 (by
    rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]; exact hl))
  have hinj : Function.Injective (σ₀.comp (algebraMap (𝓞 K) K)) :=
    σ₀.injective.comp (IsFractionRing.injective (𝓞 K) K)
  have hab : a * b = 1 := hinj (by
    simp only [RingHom.comp_apply, map_mul, map_one]
    rw [ha, hb, mul_inv_cancel₀ hc0])
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha.symm⟩


include hK in
theorem exists_unit_pointMap_vcPoint (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L L' : PeriodPair)
    (hL : L.lattice = idealLattice σ₀ 𝔞) (hL' : L'.lattice = idealLattice σ₀ ↑(𝔟 * 𝔞))
    {A A' : WeierstrassCurve ℂ} [A.IsElliptic] [A'.IsElliptic]
    (V : VariableChange ℂ) (hV : V • weierstrassCurve L = A)
    (V' : VariableChange ℂ) (hV' : V' • weierstrassCurve L' = A') (φ : Isogeny A A')
    (hφ : (homConstSet A A' : Set ℂ) = (invConst φ * ·) '' idealLattice σ₀ 𝔟) :
    ∃ u : (𝓞 K)ˣ, ∀ z : ℂ, φ.pointMap (vcPoint V hV (toPoint L z)) =
      vcPoint V' hV' (toPoint L' (σ₀ (algebraMap (𝓞 K) K u) * z)) := by
  classical
  set Q := vcHom V hV
  set R := vcHom V'⁻¹ (inv_smul_eq_of_smul_eq V' hV')
  set c := homConst A' (weierstrassCurve L') R * homConst (weierstrassCurve L) A Q
  have hset := homConstSet_conj V hV V' hV'

  set Φ := homComp R (homComp φ.toHom Q)
  have hΦ : homConst _ _ Φ = c * invConst φ := by
    rw [homConst_homComp, homConst_homComp, homConst_toHom]
    ring
  have hc0 : c ≠ 0 := by
    intro h0
    have e := homConst_vcHom_mul_inv V' hV'
    have e' := homConst_vcHom_mul_inv V hV
    simp only [c, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · rw [h0, zero_mul] at e; exact zero_ne_one e
    · rw [h0, mul_zero] at e'; exact zero_ne_one e'
  have hΦ0 : Φ ≠ 0 := by
    intro h
    have := congrArg (homConst _ _) h
    rw [hΦ, map_zero] at this
    exact mul_ne_zero hc0 (invConst_ne_zero φ) this
  set ψ := isogOfHom Φ hΦ0
  have hψc : invConst ψ = c * invConst φ := by
    rw [← homConst_toHom, isogOfHom_toHom, hΦ]
  have hLend := latticeEnd_eq_cmRing_of_lattice_eq σ₀ hK hL
  have hL'' : L'.lattice = idealLattice σ₀ ↑(𝔟⁻¹)⁻¹ * L.lattice := by
    rw [hL', inv_inv, hL, Units.val_mul, idealLattice_mul]
  have hψ : (homConstSet (weierstrassCurve L) (weierstrassCurve L') : Set ℂ) =
      (invConst ψ * ·) '' idealLattice σ₀ ↑(𝔟⁻¹)⁻¹ := by
    rw [inv_inv, hset, hφ, Set.image_image, hψc]
    congr 1
    funext x
    ring
  obtain ⟨u, -, hu⟩ := exists_unit_of_homConstSet_eq σ₀ hK L L' hLend 𝔟⁻¹ hL'' ψ hψ
  refine ⟨u, fun z ↦ ?_⟩
  have h1 := hu z
  rw [isogOfHom_toHom, TateCharpoly.homPt_homComp, TateCharpoly.homPt_homComp, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply, homPt_vcHom, homPt_vcHom, homPt_toHom, Isogeny.pointHom_apply] at h1
  have h2 := congrArg (vcPoint V' hV') h1
  rwa [vcPoint_vcPoint_of_eq_inv V'⁻¹ V' (inv_inv V').symm] at h2

end Lattice

end

end Elliptic
end GroundTheory.Global
end
