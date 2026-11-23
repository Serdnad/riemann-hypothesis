module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle098
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimePowSmulMemValueLatticeErase
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle669
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle101
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle096
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle905
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
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
public import Mathlib.GroupTheory.IndexNSmul
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory.CoefWtLine

open Formalism.GradedWeylDivisibility


open Classical in
def blkW (ι : Type) (n : ℕ) : ι × Fin n × Fin n → ι → Fin n → ℕ :=
  fun v => Pi.single v.1 (Pi.single v.2.1 1)

theorem weight_blkW {ι : Type} [Fintype ι] {n : ℕ} (m : ι × Fin n × Fin n →₀ ℕ) (τ : ι) (a : Fin n) :
    Finsupp.weight (blkW ι n) m τ a = ∑ s : Fin n, m (τ, a, s) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Finset.sum_apply,
    Fintype.sum_prod_type, Finset.sum_eq_single τ, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [blkW]
  · intro b _ hb
    simp [blkW, hb]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [blkW, hb]
  · simp

open Classical in
theorem blockEmb_hom {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (τ : ι)
    (f : MvPolynomial (Fin n × Fin n) K) (μ : Fin n → ℕ) (hf : IsWeightedHomogeneous (rowW n n) f μ) :
    IsWeightedHomogeneous (blkW ι n) (blockEmb K τ f) (Pi.single τ μ) := by
  intro d hd
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero _ _ _ hd
  have e := hf hu
  funext τ' a
  rw [weight_blkW]
  by_cases h : τ' = τ
  · subst h
    rw [Pi.single_eq_same, ← e, GlobalTheory.LvT.KerLat.weight_rowW, rowDeg]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact Finsupp.mapDomain_apply_of_injective (fun x y hxy => (Prod.mk.inj hxy).2) u (a, s)
  · rw [Pi.single_eq_of_ne h]
    refine Finset.sum_eq_zero fun s _ => ?_
    apply Finsupp.mapDomain_notin_range
    rintro ⟨x, hx⟩
    exact h (Prod.mk.inj hx).1.symm

theorem ten_hom {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}
    (f : ι → MvPolynomial (Fin n × Fin n) K) (μ : ι → Fin n → ℕ)
    (hf : ∀ τ, IsWeightedHomogeneous (rowW n n) (f τ) (μ τ)) :
    IsWeightedHomogeneous (blkW ι n) (ten f) μ := by
  classical
  have h := IsWeightedHomogeneous.prod Finset.univ (fun τ => blockEmb K τ (f τ)) _
    (fun τ _ => blockEmb_hom τ (f τ) (μ τ) (hf τ))
  have e : μ = ∑ τ, Pi.single τ (μ τ) := (Finset.univ_sum_single μ).symm
  rw [e]
  exact h

theorem natW_antitone' {n : ℕ} (l : DomWeight n) : Antitone l.natW := fun _ _ h =>
  Int.toNat_le_toNat (sub_le_sub_right (l.anti h) _)

theorem extremal_hom (K : Type) [Field K] {n : ℕ} (l : DomWeight n) :
    IsWeightedHomogeneous (rowW n n) (extremal K n l) l.natW := by
  have h := hwRowWeight K n n le_rfl l.natW (natW_antitone' l)
  have e : (rowNu l.natW : Fin n → ℕ) = l.natW := by
    funext a
    simp [rowNu]
  rwa [e] at h

theorem weight_line : ∀ (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n), (∀ m ∈ (ten fun τ => extremal K n (lam τ) : Pol K ι n).support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a) ∧ ∀ G ∈ VV K lam, (∀ m ∈ G.support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a) → ∃ c : K, G = c • ten fun τ => extremal K n (lam τ) := by
  intro K _ ι _ n lam
  classical
  refine ⟨fun m hm τ a => ?_, fun G hG hw => ?_⟩
  · have h := ten_hom _ (fun τ => (lam τ).natW) (fun τ => extremal_hom K (lam τ)) (mem_support_iff.1 hm)
    rw [← weight_blkW, h]
  · have hGh : IsWeightedHomogeneous (blkW ι n) G (fun τ => (lam τ).natW) := by
      intro d hd
      funext τ a
      rw [weight_blkW]
      exact hw d (mem_support_iff.2 hd) τ a
    have key : VV K lam ≤ (Submodule.span K {(ten fun τ => extremal K n (lam τ) : Pol K ι n)}).comap
        (weightedHomogeneousComponent (blkW ι n) (fun τ => (lam τ).natW)) := by
      rw [← (bVVfun_spec K lam).2, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have sp := fun τ => (sSBasis K n n (lam τ).natW).choose_spec.1
      have hb : ∀ τ, IsWeightedHomogeneous (rowW n n) (ssB K (lam τ).natW (i τ)) (rowWt (i τ).1) :=
        fun τ => (sp τ).2.2 (i τ)
      have hi : IsWeightedHomogeneous (blkW ι n) (bVVfun K lam i) (fun τ => rowWt (i τ).1) := ten_hom _ _ hb
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      by_cases he : (fun τ => (lam τ).natW) = fun τ => rowWt (i τ).1
      · rw [← he] at hi
        rw [hi.weightedHomogeneousComponent_same]
        have hc : ∀ τ, ∃ c : K, ssB K (lam τ).natW (i τ) = c • extremal K n (lam τ) := fun τ => by
          refine GlobalTheory.Alc.hw_line_field K n _ (natW_antitone' _) _ ?_ ?_
          · rw [← (sp τ).2.1]
            exact Submodule.subset_span ⟨i τ, rfl⟩
          · have := hb τ
            rwa [← congrFun he τ] at this
        choose c hc using hc
        refine Submodule.mem_span_singleton.2 ⟨∏ τ, c τ, ?_⟩
        simp only [bVVfun, ten, hc, map_smul]
        exact (Finset.prod_smul _ _ _).symm
      · rw [hi.weightedHomogeneousComponent_ne _ he]
        exact zero_mem _
    have h := key hG
    rw [Submodule.mem_comap, hGh.weightedHomogeneousComponent_same] at h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
    exact ⟨c, hc.symm⟩

end GlobalTheory.CoefWtLine
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.SeamSelfDual

theorem mem_range_iff {E : Type} [Field E] (x : E) :
    x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.isIntegral_coe
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

theorem mem_one_iff {E : Type} [Field E] (x : E) :
    x ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ x := by
  rw [Submodule.mem_one, ← mem_range_iff]
  rfl

theorem isIntegral_map {E E' : Type} [Field E] [Field E'] (f : E →+* E') {x : E}
    (h : IsIntegral ℤ x) : IsIntegral ℤ (f x) :=
  h.map f.toIntAlgHom

theorem isSDLat_pi (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) :
    IsSDLat E n (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) := by
  classical
  have hm : ∀ x : Fin n → E, x ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) ↔
      ∀ i, IsIntegral ℤ (x i) := by
    intro x
    simp only [Submodule.mem_pi, Set.mem_univ, true_implies, mem_one_iff]
  have hs : ∀ i : Fin n, (Pi.single i 1 : Fin n → E) ∈
      (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) := by
    intro i
    rw [hm]
    intro j
    by_cases h : j = i
    · subst h; simpa using isIntegral_one
    · simpa [Pi.single_apply, h] using isIntegral_zero
  refine ⟨Submodule.fg_pi fun _ => ?_, ?_, fun y => ⟨fun hy x hx => ?_, fun hy => ?_⟩⟩
  · rw [Submodule.one_eq_span]
    exact Submodule.fg_span_singleton _
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    exact hs i
  · rw [mem_range_iff]
    rw [hm] at hx hy
    exact IsIntegral.sum _ fun i _ => (isIntegral_map (starRingEnd E) (hx i)).mul (hy i)
  · rw [hm]
    intro i
    have := hy _ (hs i)
    rw [mem_range_iff] at this
    have e : stdH E n (Pi.single i 1) y = y i := by
      unfold stdH
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_apply, hj]
      · simp
    rwa [e] at this

section Transport

variable {E E' : Type} [Field E] [Field E'] (f : E ≃+* E') {n : ℕ}

theorem isSDLat_image [NumberField E] [NumberField E'] [StarRing E] [StarRing E']
    (hf : ∀ x, f (star x) = star (f x)) (L : Submodule (𝓞 E) (Fin n → E)) (hL : IsSDLat E n L) :
    IsSDLat E' n (Submodule.span (𝓞 E')
      ((fun (x : Fin n → E) (i : Fin n) => f (x i)) '' (L : Set (Fin n → E)))) := by
  first
  | exact @_root_.GlobalTheory.StandardLatticeSpan.isSDLat_map
  | exact _root_.GlobalTheory.StandardLatticeSpan.isSDLat_map
  | (apply _root_.GlobalTheory.StandardLatticeSpan.isSDLat_map <;> assumption)
  | (intros; apply _root_.GlobalTheory.StandardLatticeSpan.isSDLat_map <;> assumption)
  | (intros; apply @_root_.GlobalTheory.StandardLatticeSpan.isSDLat_map <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.StandardLatticeSpan.isSDLat_map ..)

end Transport

theorem isSDLat_of_isSdLat {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (L : Submodule (𝓞 E) (Sp E n)) (hL : IsSdLat L) : IsSDLat E n L := by
  obtain ⟨h1, h2⟩ := hL
  have hspan : Submodule.span E (L : Set (Sp E n)) = ⊤ := by
    open Formalism.HermitianLatticesTheory in
    apply Submodule.dualAnnihilator_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro f hf
    let v : Sp E n := fun i => star (f (Pi.single i 1))
    have hpair : hStd E n v = f := by
      apply (Pi.basisFun E (Fin n)).ext
      intro i
      rw [Pi.basisFun_apply, hStd_apply, Finset.sum_eq_single i]
      · simp [v]
      · intro j _ hj
        simp [hj]
      · simp
    have hline (r : E) : r • v ∈ L := by
      rw [← show dual (hStd E n) L = L from h2, dualBasic_mem_dual]
      intro y hy
      have hy0 : hStd E n v y = 0 := by
        rw [hpair]
        exact (Submodule.mem_dualAnnihilator f).mp hf y (Submodule.subset_span hy)
      have hz : hStd E n y v = 0 := by
        simpa [hy0] using ((hStd_isSymm (E := E) (n := n)).eq v y).symm
      simp [hz]
    have hv : v = 0 := by
      funext i
      change v i = 0
      by_contra hi
      let coord := (LinearMap.proj i : Sp E n →ₗ[E] E).restrictScalars (𝓞 E)
      have htop : L.map coord = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact ⟨(x / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
      have : Module.Finite (𝓞 E) E := Module.finite_def.mpr (htop ▸ h1.fg.map coord)
      exact RingOfIntegers.not_isField E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
    rw [Submodule.mem_bot]
    simpa [hv] using hpair.symm
  refine ⟨h1.fg, hspan, fun y => ?_⟩
  have h3 : y ∈ L ↔ y ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) L := by
    rw [show Formalism.HermitianLatticesTheory.dual (hStd E n) L = L from h2]
  rw [h3]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, mem_one_iff, mem_range_iff]
  rfl

theorem seam_selfDual : ∀ (D : D7) (X : Fields) (s : Seam D X), s.Ok → ∀ (n : ℕ), StandardLatticesGL3.SD D (StandardLatticesGL3.stdL D n) ∧ ∀ L : Submodule (𝓞 X.E) (Sp X.E n), IsSdLat L → StandardLatticesGL3.SD D (s.lat L) := by
  intro D X s hs n
  letI := D.host.cmStar
  refine ⟨isSDLat_pi D.host.E n, fun L hL => ?_⟩
  exact isSDLat_image s.iE (fun x => (hs.2 x).trans (bridge_star_holds D.R D.host _).symm) L
    (isSDLat_of_isSdLat L hL)

end GlobalTheory.SeamSelfDual
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms.HalfReps

section Group

variable {H : Type} [AddCommGroup H] [Module ℚ H] [Module.Finite ℚ H]

theorem relIndex_nsmul (Λ : AddSubgroup H) (hΛ : Module.Finite ℤ Λ) {c : ℕ} (hc : 0 < c) :
    (Λ.map (nsmulAddMonoidHom c)).relIndex Λ ≠ 0 ∧
      (Λ.map (nsmulAddMonoidHom c)).relIndex Λ ≤ c ^ Module.finrank ℚ H := by
  have : HasUniqueDiv H := HasUniqueDiv.of_module_rat H
  have : Module.Finite ℤ Λ.toIntSubmodule := hΛ
  have : Module.Free ℤ Λ.toIntSubmodule := inferInstance
  rw [AddSubgroup.relIndex_map_nsmul]
  refine ⟨pow_ne_zero _ hc.ne', Nat.pow_le_pow_right hc ?_⟩
  have hb := (Module.finBasis ℤ Λ.toIntSubmodule).linearIndependent.map' Λ.toIntSubmodule.subtype
    (Submodule.ker_subtype _)
  have := ((LinearIndependent.iff_fractionRing ℤ ℚ).1 hb).fintype_card_le_finrank
  rw [Fintype.card_fin] at this
  exact this

theorem relIndex_of_nsmul_le (Λ B : AddSubgroup H) (hΛ : Module.Finite ℤ Λ) {c : ℕ} (hc : 0 < c)
    (hB : ∀ x ∈ B, c • x ∈ Λ) : Λ.relIndex B ≠ 0 ∧ Λ.relIndex B ≤ c ^ Module.finrank ℚ H := by
  have : HasUniqueDiv H := HasUniqueDiv.of_module_rat H
  obtain ⟨h0, h1⟩ := relIndex_nsmul Λ hΛ hc
  have hle : B.map (nsmulAddMonoidHom c) ≤ Λ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hB x hx
  rw [← AddSubgroup.relIndex_map_map_of_injective (f := nsmulAddMonoidHom c) Λ B (nsmul_right_injective hc.ne')]
  exact ⟨fun h => h0 (AddSubgroup.relIndex_eq_zero_of_le_right hle h),
    (AddSubgroup.relIndex_le_of_le_right hle h0).trans h1⟩

theorem relIndex_of_le_nsmul (Λ A B : AddSubgroup H) (hΛ : Module.Finite ℤ Λ) {c : ℕ} (hc : 0 < c)
    (hB : ∀ x ∈ Λ, c • x ∈ B) : B.relIndex (Λ ⊓ A) ≠ 0 := by
  obtain ⟨h0, -⟩ := relIndex_nsmul Λ hΛ hc
  have hle : Λ.map (nsmulAddMonoidHom c) ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    exact hB x hx
  exact fun h => h0 (AddSubgroup.relIndex_eq_zero_of_le_left hle
    (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h))

end Group

section Twist

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W]
  [IsScalarTower (𝓞 E) E W]

theorem mem_twO (M : Submodule (𝓞 E) W) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ) (y : W) :
    y ∈ twist₂ M c e ↔ ∀ Q : HeightOneSpectrum (𝓞 E), ((c : E) ^ e Q)⁻¹ • y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := by
  simp [twist₂, Submodule.mem_iInf]

theorem nsmul_mem_twO (M : Submodule (𝓞 E) W) {c : ℕ} (hc : 0 < c) {e : HeightOneSpectrum (𝓞 E) → ℤ}
    (he : ∀ Q, e Q ≤ 1) {x : W} (hx : x ∈ M) : c • x ∈ twist₂ M c e := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  refine (mem_twO M c e _).2 fun Q => GlobalTheory.ThetaMove.mem_localization_of_mem Q ?_
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ 1 - e Q by have := he Q; omega)
  have : ((c : E) ^ e Q)⁻¹ • c • x = (c ^ m) • x := by
    rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← zpow_natCast, ← hm,
      zpow_sub₀ hcE, zpow_one, div_eq_inv_mul]
  rw [this]
  exact nsmul_mem hx _

theorem nsmul_mem_of_twO (M : Submodule (𝓞 E) W) {c : ℕ} (hc : 0 < c) {e : HeightOneSpectrum (𝓞 E) → ℤ}
    (he : ∀ Q, -1 ≤ e Q) {x : W} (hx : x ∈ twist₂ M c e) : c • x ∈ M := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  refine GlobalTheory.ThetaMove.mem_of_locP fun Q => ?_
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ 1 + e Q by have := he Q; omega)
  have : c • x = (c ^ m) • ((c : E) ^ e Q)⁻¹ • x := by
    rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← zpow_natCast, ← hm,
      zpow_add₀ hcE, zpow_one, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ hcE), mul_one]
  rw [this]
  exact nsmul_mem ((mem_twO M c e x).1 hx Q) _

end Twist

theorem half_reps : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (dl : ℂ) (AA : Submodule (𝓞 E) E) (S : Finset (HeightOneSpectrum (𝓞 E))) (L : Submodule (𝓞 E) (Sp E a)) (L' : Submodule (𝓞 E) (Sp E b)) (c : ℕ), dl ≠ 0 → AA.FG → Submodule.IsFullLattice E L → Submodule.IsLattice E L' → 0 < c → Formalism.L2.Th1.H.IsReps (BC emb dl AA S L L' c) (LamC emb dl AA L L' ⊓ AC emb dl AA S L L' c) (repsOf (BC emb dl AA S L L' c) (LamC emb dl AA L L' ⊓ AC emb dl AA S L L' c)) ∧ Formalism.L2.Th1.H.IsReps (LamC emb dl AA L L') (BC emb dl AA S L L' c) (repsOf (LamC emb dl AA L L') (BC emb dl AA S L L' c)) ∧ (repsOf (LamC emb dl AA L L') (BC emb dl AA S L L' c)).card ≤ c ^ (Module.finrank ℚ E * a * b) := by
  intro E _ _ _ ι _ _ a b emb dl AA S L L' c hdl hA hL hL' hc
  have hinj := GlobalTheory.ThetaMove.embH_injective (a := a) (b := b) emb hdl
  have hfg : (perO AA L L').FG :=
    GlobalTheory.ThetaMove.VolumePos.perO_fg hA
      (GlobalTheory.ThetaMove.VolumePos.homO_fg hL.fg hL'.fg
        (Submodule.IsFullLattice.span_eq_top (self := hL)))
  have : Module.Finite (𝓞 E) (perO AA L L') := Module.Finite.iff_fg.2 hfg
  have hfin : Module.Finite ℤ (perO AA L L') := Module.Finite.trans (𝓞 E) _
  have : Module.Finite ℚ (Formalism.L2.Col.HomE E a b) := Module.Finite.trans E _
  have hrk : Module.finrank ℚ (Formalism.L2.Col.HomE E a b) = Module.finrank ℚ E * a * b := by
    rw [← Module.finrank_mul_finrank ℚ E, Module.finrank_linearMap]
    simp [mul_assoc]
  have h1 := relIndex_of_le_nsmul (perO AA L L').toAddSubgroup (halfAO S (perO AA L L') c).toAddSubgroup
    (halfBO S (perO AA L L') c).toAddSubgroup hfin hc
    (fun x hx => nsmul_mem_twO _ hc (fun Q => (GlobalTheory.ThetaMove.expS_bound S Q).2) hx)
  have h2 := relIndex_of_nsmul_le (perO AA L L').toAddSubgroup
    (halfBO S (perO AA L L') c).toAddSubgroup hfin hc
    (fun x hx => nsmul_mem_of_twO _ hc (fun Q => (GlobalTheory.ThetaMove.expS_bound S Q).1) hx)
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.map_inf _ _ _ hinj] at h1
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, hrk] at h2
  have r2 := Classical.epsilon_spec (GlobalTheory.RepsMod.exists_reps _ _ h2.1)
  refine ⟨Classical.epsilon_spec (GlobalTheory.RepsMod.exists_reps _ _ h1), r2, ?_⟩
  exact (GlobalTheory.RepsMod.card_reps _ _ _ r2).le.trans h2.2

end GlobalTheory.ColNorms.HalfReps
end

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.InertLossAdm

theorem inertPrimes_loss_log_sum_admissible : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.InertPrimeLossBound (Fm.D x i) (Fm.L x i) Fm.GK Fm.cX.err C := by
  intro eps Fm h0 h1
  obtain ⟨C1, x1, hC1, hc⟩ := GlobalTheory.ConjLossPrimes.loss_sum_primes Fm h0 h1
  obtain ⟨C2, x2, hC2, hi⟩ := GlobalTheory.OtherLoss.inertLoss_primeSum Fm h0 h1
  refine ⟨C1 + C2, max x1 x2, add_nonneg hC1 hC2, ?_⟩
  intro x hx hx1 i j hj P hP
  rw [← Finset.sum_filter_add_sum_filter_not P
    (fun p => G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)]
  have A := hc x (le_trans (le_max_left _ _) hx) hx1 i j hj (P.filter
    (fun p => G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0))
    (fun p hp => by
      rw [Finset.mem_filter] at hp
      exact ⟨(hP p hp.1).1, (hP p hp.1).2.2⟩)
  have B := hi x (le_trans (le_max_right _ _) hx) hx1 i j hj (P.filter
    (fun p => ¬ (G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)))
    (fun p hp => by
      rw [Finset.mem_filter] at hp
      exact ⟨(hP p hp.1).1, (hP p hp.1).2.1, (hP p hp.1).2.2, hp.2⟩)
  have eA : ∑ p ∈ P.filter (fun p => G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0),
      2 * Real.log (p : ℝ) * |Formalism.MainNotions.WeightDegreeSizes.EatCI (Fm.L x i) Fm.GK Fm.cX.err j p| =
      ∑ p ∈ P.filter (fun p => G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0),
      2 * Real.log (p : ℝ) * |EatC (Fm.L x i) Fm.cX.err j p| := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    unfold Formalism.MainNotions.WeightDegreeSizes.EatCI
    rw [if_pos hp.2]
  have eB : ∑ p ∈ P.filter (fun p => ¬ (G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)),
      2 * Real.log (p : ℝ) * |Formalism.MainNotions.WeightDegreeSizes.EatCI (Fm.L x i) Fm.GK Fm.cX.err j p| =
      ∑ p ∈ P.filter (fun p => ¬ (G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)),
      2 * Real.log (p : ℝ) * |EatI (Fm.L x i) Fm.GK Fm.cX.err j p| := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    unfold Formalism.MainNotions.WeightDegreeSizes.EatCI
    rw [if_neg hp.2]
  rw [eA, eB, add_mul]
  exact add_le_add A B

end GlobalTheory.InertLossAdm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.isProper_of_dvr_lift_through_finite_correspondence : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y₀ Y : Scheme.{0}) (τ : X ⟶ Sp R) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsQProjOver τ → IsFinite s → IsOpenImmersion i → IsDominant i → t ≫ τ = s ≫ τ → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i ≫ t → ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ i ≫ s) → IsProper t := by
  first | (exact @GlobalTheory.FiniteCoverProper.isProper_of_lift_through_finite) | (exact GlobalTheory.FiniteCoverProper.isProper_of_lift_through_finite) | (intros; apply GlobalTheory.FiniteCoverProper.isProper_of_lift_through_finite  <;> assumption)
end
