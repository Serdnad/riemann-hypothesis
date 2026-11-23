module

public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle002
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem KrullAkizuki.equiv :
    GroundTheory.Heights₂.Heights.Model.KrullAkizuki.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.KrullAkizuki.Statement := by
  constructor
  · rintro ⟨h₁, h₂⟩ R K L _ _ _ _ _ _ _ _ _ _ _ hR
    exact ⟨h₁ R hR K L, h₂ R hR K⟩
  · intro h
    refine ⟨fun R _ _ _ hR K _ _ _ L _ _ _ _ _ S => (h R K L hR).1 S, ?_⟩
    intro R _ _ _ hR K _ _ _
    exact (h R K K hR).2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem BlowUpChart.comap_eq_maximalIdeal {A K : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] {n : ℕ} {x : Fin n → A}
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A) {i : Fin n} (hi : x i ≠ 0)
    (P : Ideal (blowUpChart A K x i)) (hP : P.IsPrime) (hxP : algebraMap A _ (x i) ∈ P) :
    P.comap (algebraMap A (blowUpChart A K x i)) = IsLocalRing.maximalIdeal A := by
  apply le_antisymm
  · exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.comap (algebraMap A (blowUpChart A K x i)) (hK := hP)).ne_top
  · rw [← hx, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have hxi : algebraMap A K (x i) ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective A K)]
      exact hi
    have hmem : algebraMap A K (x j) / algebraMap A K (x i) ∈ blowUpChart A K x i :=
      Algebra.subset_adjoin ⟨j, rfl⟩
    have hfac : algebraMap A (blowUpChart A K x i) (x j) =
        ⟨_, hmem⟩ * algebraMap A (blowUpChart A K x i) (x i) := by
      apply Subtype.ext
      simp [div_mul_cancel₀ _ hxi]
    show algebraMap A _ (x j) ∈ P
    rw [hfac]
    exact P.mul_mem_left _ hxP

theorem BlowUpChart.equiv :
    _root_.GroundTheory.Heights₂.Heights.Model.BlowUpChart.Statement ↔
      _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.BlowUpChart.Statement := by
  constructor
  · intro h A K _ _ _ _ _ _ _ n x hx hne
    obtain ⟨i, hi, hu, -⟩ := h A K n x hx hne
    exact ⟨i, hi, hu, fun P hP hxP => BlowUpChart.comap_eq_maximalIdeal hx hi P hP hxP⟩
  · intro h A _ _ _ _ K _ _ _ n x hx hne
    obtain ⟨i, hi, hu, -⟩ := h A K n x hx hne
    have hne' : Ideal.span {algebraMap A (blowUpChart A K x i) (x i)} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact hu
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne'
    exact ⟨i, hi, hu, Q, hQ.isPrime, hle (Ideal.subset_span rfl),
      BlowUpChart.comap_eq_maximalIdeal hx hi Q hQ.isPrime (hle (Ideal.subset_span rfl))⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem cp_eq_primeWeight (p : ℕ) : cp p = GroundTheory.Heights₂.Heights.Model.primeWeight p := rfl

theorem cp_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ cp p := by
  unfold cp
  split_ifs
  · norm_num
  · have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact div_nonneg zero_le_one (by linarith)

theorem sumCp_term_nonneg (d : ℤ) {p : ℕ} (hp : p.Prime) :
    0 ≤ (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p :=
  mul_nonneg (add_nonneg (cp_nonneg hp) (by positivity))
    (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))

theorem SumCp.equiv :
    GroundTheory.Heights₂.Heights.Model.SumCp.Statement ↔ SumCp.Statement := by
  constructor
  · intro hA d hd
    obtain ⟨C, hC⟩ := hA d hd
    refine ⟨C, fun B hB S hS => ?_⟩
    have h := hC B hB S fun p hp => ⟨(hS p hp).1, Or.inl (hS p hp).2⟩
    simpa [cp_eq_primeWeight] using h
  · intro hB d hd
    obtain ⟨C, hC⟩ := hB d hd
    set T := d.natAbs.primeFactors
    set K : ℝ := ∑ p ∈ T, (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p
    have hK : 0 ≤ K := Finset.sum_nonneg fun p hp =>
      sumCp_term_nonneg d (Nat.mem_primeFactors.mp hp).1
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    refine ⟨C + K / Real.log 2, fun B hB2 S hS => ?_⟩
    have hlogB : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) hB2
    have hterm : ∀ p ∈ S, (GroundTheory.Heights₂.Heights.Model.primeWeight p +
        2 * (padicValInt p d : ℝ)) * Real.log p =
        (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p := fun p _ => by
      rw [cp_eq_primeWeight]
    have hsum : ∑ p ∈ S, (GroundTheory.Heights₂.Heights.Model.primeWeight p +
        2 * (padicValInt p d : ℝ)) * Real.log p =
        ∑ p ∈ S, (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p :=
      Finset.sum_congr rfl hterm

    have h1 : ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) ≤ B),
        (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p ≤ C * Real.log B :=
      hC B hB2 _ fun p hp => by
        obtain ⟨hpS, hpB⟩ := Finset.mem_filter.mp hp
        exact ⟨(hS p hpS).1, hpB⟩

    have h2 : ∑ p ∈ S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ B),
        (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p ≤ K := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p hp _ => ?_)
      · obtain ⟨hpS, hpB⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpp, hor⟩ := hS p hpS
        have hpd : (p : ℤ) ∣ d := hor.resolve_left hpB
        exact Nat.mem_primeFactors.mpr ⟨hpp, Int.natCast_dvd.mp hpd, Int.natAbs_ne_zero.mpr hd⟩
      · exact sumCp_term_nonneg d (Nat.mem_primeFactors.mp hp).1
    have h3 : K ≤ K / Real.log 2 * Real.log B := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hlogB hK
    have hsplit := Finset.sum_filter_add_sum_filter_not S (fun p : ℕ => (p : ℝ) ≤ B)
      (fun p => (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p)
    have : ∑ p ∈ S, (GroundTheory.Heights₂.Heights.Model.primeWeight p +
        2 * (padicValInt p d : ℝ)) * Real.log p ≤ (C + K / Real.log 2) * Real.log B := by
      rw [hsum, ← hsplit, add_mul]
      linarith
    exact this

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem MertensUpper.Iic_eq_range (n : ℕ) : Finset.Iic n = Finset.range (n + 1) := by
  ext m
  simp

theorem MertensUpper.equiv :
    GroundTheory.Heights₂.Heights.Model.MertensUpper.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.MertensUpper.Statement := by
  unfold GroundTheory.Heights₂.Heights.Model.MertensUpper.Statement
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.MertensUpper.Statement
  simp only [MertensUpper.Iic_eq_range]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

theorem FiniteIntegralClosure.alg_iff :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A]
      (K : Type) [Field K] [Algebra A K] [IsFractionRing A K]
      (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L],
      Module.Finite A (integralClosure A L)) ↔
    (∀ (A K L : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] [Field K] [Algebra A K]
      [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
      [IsScalarTower A K L], Module.Finite A (integralClosure A L)) :=
  ⟨fun h A K L _ _ _ _ _ _ _ _ _ _ _ => h A K L, fun h A _ _ _ K _ _ _ L _ _ _ _ _ => h A K L⟩

theorem finiteType_sections_of_isFiniteTypeOverZ {X : Scheme.{0}} (hX : IsFiniteTypeOverZ X)
    {U : X.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(X, U) := by
  have := hX.1
  have h1 := (toSpecZ X).finiteType_appLE (isAffineOpen_top (Spec (.of ℤ))) hU le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv).2
  have h3 := h1.comp h2
  rw [show ((toSpecZ X).appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom =
    algebraMap ℤ Γ(X, U) from RingHom.ext_int _ _] at h3
  exact RingHom.finiteType_algebraMap.mp h3

theorem FiniteIntegralClosure.scheme_of_alg
    (h : ∀ (A K L : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] [Field K]
      [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L]
      [Algebra A L] [IsScalarTower A K L], Module.Finite A (integralClosure A L)) :
    ∀ (X : Scheme.{0}) [IsIntegral X], IsFiniteTypeOverZ X →
      ∀ (L : Type) [Field L] [Algebra X.functionField L] [FiniteDimensional X.functionField L]
        (U : X.Opens), IsAffineOpen U → ∀ hU : Nonempty U,
        letI := hU
        let : Algebra Γ(X, U) L :=
          ((algebraMap X.functionField L).comp (algebraMap Γ(X, U) X.functionField)).toAlgebra
        Module.Finite Γ(X, U) (integralClosure Γ(X, U) L) := by
  intro X _ hX L _ _ _ U hUa hU
  have := hU
  have := finiteType_sections_of_isFiniteTypeOverZ hX hUa
  have := functionField_isFractionRing_of_isAffineOpen X U hUa
  let : Algebra Γ(X, U) L :=
    ((algebraMap X.functionField L).comp (algebraMap Γ(X, U) X.functionField)).toAlgebra
  have : IsScalarTower Γ(X, U) X.functionField L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact h Γ(X, U) X.functionField L

theorem genericSpecMap_closedPoint (Z : Scheme.{0}) [IsIntegral Z] (L : Type) [Field L]
    [Algebra Z.functionField L] :
    _root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L (IsLocalRing.closedPoint L) =
      genericPoint Z := by
  have h : (Spec.map (CommRingCat.ofHom (algebraMap Z.functionField L)))
      (IsLocalRing.closedPoint (CommRingCat.of L)) = IsLocalRing.closedPoint Z.functionField :=
    Spec_closedPoint
  exact (Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom (algebraMap Z.functionField L)))
    (Z.fromSpecStalk (genericPoint Z)) (IsLocalRing.closedPoint (CommRingCat.of L))).trans
    (h ▸ Scheme.fromSpecStalk_closedPoint)

theorem genericSpecMap_app_iso (Z : Scheme.{0}) [IsIntegral Z] (L : Type) [Field L]
    [Algebra Z.functionField L] (U : Z.Opens) (hη : genericPoint Z ∈ U)
    (hmem : _root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L (IsLocalRing.closedPoint L) ∈ U) :
    (_root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L).app U ≫
      ((Spec (CommRingCat.of L)).presheaf.mapIso (eqToIso
        (Scheme.preimage_eq_top_of_closedPoint_mem _ hmem).symm).op ≪≫
        Scheme.ΓSpecIso (CommRingCat.of L)).hom =
      Z.presheaf.germ U (genericPoint Z) hη ≫ CommRingCat.ofHom (algebraMap Z.functionField L) := by
  have h := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
    (CommRingCat.ofHom (algebraMap Z.functionField L)) U hmem
  exact (Scheme.germ_stalkClosedPointTo _ U hmem).symm.trans h

theorem FiniteIntegralClosure.normalization_of_scheme
    (h : ∀ (X : Scheme.{0}) [IsIntegral X], IsFiniteTypeOverZ X →
      ∀ (L : Type) [Field L] [Algebra X.functionField L] [FiniteDimensional X.functionField L]
        (U : X.Opens), IsAffineOpen U → ∀ hU : Nonempty U,
        letI := hU
        let : Algebra Γ(X, U) L :=
          ((algebraMap X.functionField L).comp (algebraMap Γ(X, U) X.functionField)).toAlgebra
        Module.Finite Γ(X, U) (integralClosure Γ(X, U) L)) :
    _root_.GroundTheory.Heights₂.Heights.Model.FiniteNormalization.Statement := by
  intro Z _ f _ _ L _ _ _
  have e : f = toSpecZ Z := specZ_hom_ext _ _
  have hX : IsFiniteTypeOverZ Z := ⟨e ▸ ‹LocallyOfFiniteType f›, e ▸ ‹QuasiCompact f›⟩
  set g := _root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L with hg
  refine { finite_app := fun U hU => ?_ }
  let := (g.app U).hom.toAlgebra
  rw [g.fromNormalization_app hU, CommRingCat.hom_comp]
  refine RingHom.Finite.comp ?_ ?_
  · exact RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (g.normalizationObjIso hU).inv).2
  refine RingHom.finite_algebraMap.2 ?_
  rcases isEmpty_or_nonempty U with hU0 | hU0
  · have hb : U = ⊥ := SetLike.coe_injective (by simpa using Set.isEmpty_coe_sort.mp hU0)
    subst hb
    have : Subsingleton (integralClosure Γ(Z, ⊥) Γ(Spec (CommRingCat.of L), g ⁻¹ᵁ ⊥)) :=
      Module.subsingleton Γ(Z, ⊥) _
    exact ⟨⟨∅, Subsingleton.elim _ _⟩⟩
  have hη : genericPoint Z ∈ U :=
    ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr (by simpa using hU0)
  have hmem : g (IsLocalRing.closedPoint L) ∈ U := by
    rw [hg, genericSpecMap_closedPoint]; exact hη
  have key := genericSpecMap_app_iso Z L U hη hmem
  let : Algebra Γ(Z, U) L :=
    ((algebraMap Z.functionField L).comp (algebraMap Γ(Z, U) Z.functionField)).toAlgebra
  let eR := ((Spec (CommRingCat.of L)).presheaf.mapIso (eqToIso
        (Scheme.preimage_eq_top_of_closedPoint_mem _ hmem).symm).op ≪≫
        Scheme.ΓSpecIso (CommRingCat.of L)).commRingCatIsoToRingEquiv
  let eA : Γ(Spec (CommRingCat.of L), g ⁻¹ᵁ U) ≃ₐ[Γ(Z, U)] L :=
    AlgEquiv.ofRingEquiv (f := eR) fun x => congrArg (fun φ => φ.hom x) key
  have hfin := h Z hX L U hU hU0
  exact Module.Finite.equiv eA.mapIntegralClosure.symm.toLinearEquiv

theorem FiniteIntegralClosure.equiv :
    (_root_.GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.Statement ∧
      _root_.GroundTheory.Heights₂.Heights.Model.FiniteNormalization.Statement) ↔
    FiniteIntegralClosure.Statement := by
  constructor
  · rintro ⟨ha, -⟩
    have hb := FiniteIntegralClosure.alg_iff.mp ha
    exact ⟨hb, FiniteIntegralClosure.scheme_of_alg hb⟩
  · rintro ⟨hb, hs⟩
    exact ⟨FiniteIntegralClosure.alg_iff.mpr hb, FiniteIntegralClosure.normalization_of_scheme hs⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
end
