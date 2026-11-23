module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

section

open MeasureTheory Pointwise

namespace GlobalTheory

theorem mem_map_conj_iff_conj_mem {G : Type} [Group G] (J : Subgroup G) (g x : G) :
    x ∈ J.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ J := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem measureReal_doubleCoset_eq_relIndex_mul :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) → ∀ g : G,
    μ.real (DoubleCoset.doubleCoset g (J : Set G) (J : Set G)) =
      ((J.map (MulAut.conj g).toMonoidHom).relIndex J : ℝ) * μ.real (J : Set G) := by
  intro G _ _ _ _ _ μ _ J hJo hJc g
  set K := J.map (MulAut.conj g).toMonoidHom with hK
  set H : Subgroup J := K.subgroupOf J with hH
  haveI : CompactSpace J := isCompact_iff_compactSpace.1 hJc
  have hKo : IsOpen (K : Set G) := by
    have : (K : Set G) = (fun x => g⁻¹ * x * g) ⁻¹' (J : Set G) := by
      ext x; rw [SetLike.mem_coe, hK, mem_map_conj_iff_conj_mem]; rfl
    rw [this]; exact hJo.preimage (by fun_prop)
  have hHo : IsOpen (H : Set J) := by
    have : (H : Set J) = Subtype.val ⁻¹' (K : Set G) := by
      ext x; simp [hH, Subgroup.mem_subgroupOf]
    rw [this]; exact hKo.preimage continuous_subtype_val
  haveI : Finite (J ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  letI : Fintype (J ⧸ H) := Fintype.ofFinite _
  let f : J ⧸ H → Set G := fun q => ((q.out : J) * g : G) • (J : Set G)
  have hcover : DoubleCoset.doubleCoset g (J : Set G) (J : Set G) = ⋃ q, f q := by
    ext x
    simp only [DoubleCoset.doubleCoset, Set.mem_mul, Set.mem_singleton_iff, Set.mem_iUnion, f,
      Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨a, ⟨j, hj, b, hb, rfl⟩, k, hk, rfl⟩
      rw [hb]
      refine ⟨(QuotientGroup.mk (⟨j, hj⟩ : J) : J ⧸ H), ?_⟩
      set o := (Quotient.out (QuotientGroup.mk (⟨j, hj⟩ : J) : J ⧸ H) : J) with ho
      have h1 : (QuotientGroup.mk o : J ⧸ H) = QuotientGroup.mk (⟨j, hj⟩ : J) := QuotientGroup.out_eq' _
      rw [QuotientGroup.eq] at h1
      have h2 : ((o : G))⁻¹ * j ∈ K := by
        have := Subgroup.mem_subgroupOf.1 (hH ▸ h1)
        simpa using this
      rw [hK, mem_map_conj_iff_conj_mem] at h2
      refine ⟨g⁻¹ * ((o : G)⁻¹ * j) * g * k, J.mul_mem h2 hk, ?_⟩
      group
    · rintro ⟨q, y, hy, rfl⟩
      exact ⟨(q.out : J) * g, ⟨(q.out : J), (q.out : J).2, g, rfl, rfl⟩, y, hy, rfl⟩
  have hdisj : Pairwise (Function.onFun Disjoint f) := by
    intro q q' hqq'
    refine Set.disjoint_left.2 ?_
    rintro x hx hx'
    simp only [f, Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe] at hx hx'
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨y', hy', hxy⟩ := hx'
    apply hqq'
    have e : ((q.out : J) : G) = (q'.out : J) * g * y' * y⁻¹ * g⁻¹ := by
      rw [hxy]; group
    have hmem : (q.out)⁻¹ * q'.out ∈ H := by
      change _ ∈ K.subgroupOf J
      rw [Subgroup.mem_subgroupOf, hK, mem_map_conj_iff_conj_mem]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [e]
      have : g⁻¹ * ((((q'.out : J) : G) * g * y' * y⁻¹ * g⁻¹)⁻¹ * (q'.out : J)) * g = y * y'⁻¹ := by group
      rw [this]
      exact J.mul_mem hy (J.inv_mem hy')
    have := (QuotientGroup.eq (s := H)).2 hmem
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
  have hmeas : ∀ q, MeasurableSet (f q) := fun q =>
    (hJo.smul ((q.out : J) * g : G)).measurableSet
  have hval : ∀ q, μ (f q) = μ (J : Set G) := fun q => measure_smul μ _ _
  have hfin : μ (J : Set G) ≠ ⊤ := (hJc.measure_lt_top).ne
  rw [hcover, measureReal_def, measure_iUnion hdisj hmeas, tsum_fintype]
  simp only [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, measureReal_def, Subgroup.relIndex,
    Subgroup.index_eq_card, Nat.card_eq_fintype_card]

end GlobalTheory
end

section

open MeasureTheory
open scoped Pointwise

namespace GlobalTheory

theorem mean_fundamentalDomain_of_le : ∀ (g : ℕ) (Λ Λ₁ : AddSubgroup (Fin g → ℂ)) (Fd D₁ : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → ℝ), Countable Λ₁ → Λ ≤ Λ₁ → IsAddFundamentalDomain Λ Fd volume → IsAddFundamentalDomain Λ₁ D₁ volume → volume Fd ≠ ⊤ → (∀ a ∈ Λ₁, ∀ z, f (z + a) = f z) → (∫ z in D₁, f z) / (volume D₁).toReal = 1 → IntegrableOn f Fd volume ∧ (∫ z in Fd, f z) / (volume Fd).toReal = 1 := by
  intro g Λ Λ₁ Fd D₁ f hc hle hFd hD₁ hfin hper hmean
  have hb : (volume D₁).toReal ≠ 0 := by
    intro h; rw [h, div_zero] at hmean; exact zero_ne_one hmean
  have hab : ∫ z in D₁, f z = (volume D₁).toReal := (div_eq_one_iff_eq hb).1 hmean
  have hint : IntegrableOn f D₁ volume := by
    by_contra h
    rw [integral_undef h] at hab; exact hb hab.symm
  have hD0 : volume D₁ ≠ 0 := fun h => hb (by simp [h])
  have hinv₁ : ∀ (γ : Λ₁) (x : Fin g → ℂ), f (γ +ᵥ x) = f x := fun γ x => by
    show f ((γ : Fin g → ℂ) + x) = f x
    rw [add_comm]; exact hper _ γ.2 x
  have hinv : ∀ (l : Λ) (x : Fin g → ℂ), f (l +ᵥ x) = f x := fun l x => by
    show f ((l : Fin g → ℂ) + x) = f x
    rw [add_comm]; exact hper _ (hle l.2) x
  let Q := Λ₁ ⧸ Λ.addSubgroupOf Λ₁
  haveI : Countable Λ := (AddSubgroup.inclusion_injective hle).countable
  haveI : Countable Q := (QuotientAddGroup.mk_surjective (s := Λ.addSubgroupOf Λ₁)).countable
  let rep : Q → Λ₁ := fun q => q.out
  have hrep : ∀ q : Q, (QuotientAddGroup.mk (rep q) : Q) = q := fun q => QuotientAddGroup.out_eq' q
  have hrepinj : Function.Injective rep := fun q q' h => by rw [← hrep q, ← hrep q', h]
  let s : Q → Set (Fin g → ℂ) := fun q => ((rep q : Λ₁) : Fin g → ℂ) +ᵥ D₁
  have hs : ∀ q, IsAddFundamentalDomain Λ₁ (s q) volume := fun q => hD₁.vadd_of_comm _
  have hsd : Pairwise (Function.onFun (AEDisjoint volume) s) := fun q q' hne => hD₁.aedisjoint (hrepinj.ne hne)
  let E := ⋃ q, s q
  have key : ∀ (l : Λ) (q : Q), l +ᵥ s q =
      ((⟨(l : Fin g → ℂ) + rep q, Λ₁.add_mem (hle l.2) (rep q).2⟩ : Λ₁) +ᵥ D₁) := by
    intro l q; ext x
    simp only [s, Set.mem_vadd_set]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨z, hz, ?_⟩
      show ((l : Fin g → ℂ) + rep q) + z = (l : Fin g → ℂ) + ((rep q : Fin g → ℂ) + z)
      abel
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(rep q : Fin g → ℂ) +ᵥ z, ⟨z, hz, rfl⟩, ?_⟩
      show (l : Fin g → ℂ) + ((rep q : Fin g → ℂ) + z) = ((l : Fin g → ℂ) + rep q) + z
      abel
  have hE : IsAddFundamentalDomain Λ E volume := by
    refine ⟨NullMeasurableSet.iUnion fun q => (hs q).nullMeasurableSet, ?_, ?_⟩
    · filter_upwards [hD₁.ae_covers] with x ⟨γ, hγ⟩
      have h1 : (QuotientAddGroup.mk (-γ) : Q) = QuotientAddGroup.mk (rep (QuotientAddGroup.mk (-γ))) :=
        (hrep _).symm
      rw [QuotientAddGroup.eq, neg_neg, AddSubgroup.mem_addSubgroupOf] at h1
      refine ⟨⟨_, h1⟩, Set.mem_iUnion.2 ⟨QuotientAddGroup.mk (-γ), ?_⟩⟩
      refine Set.mem_vadd_set.2 ⟨γ +ᵥ x, hγ, ?_⟩
      show (rep (QuotientAddGroup.mk (-γ)) : Fin g → ℂ) + ((γ : Fin g → ℂ) + x) =
        ((γ + rep (QuotientAddGroup.mk (-γ)) : Λ₁) : Fin g → ℂ) + x
      push_cast; abel
    · intro l l' hne
      simp only [Function.onFun, E, Set.vadd_set_iUnion]
      rw [AEDisjoint.iUnion_left_iff]; intro q
      rw [AEDisjoint.iUnion_right_iff]; intro q'
      rw [key, key]
      apply hD₁.aedisjoint
      intro heq
      have hv : (l : Fin g → ℂ) + rep q = l' + rep q' := congrArg Subtype.val heq
      have hqq : q = q' := by
        rw [← hrep q, ← hrep q', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
        have : ((-rep q + rep q' : Λ₁) : Fin g → ℂ) = (l : Fin g → ℂ) - l' := by
          push_cast
          calc -(rep q : Fin g → ℂ) + rep q' = -(rep q : Fin g → ℂ) + rep q' + ((l : Fin g → ℂ) + rep q - (l' + rep q')) := by
                rw [hv, sub_self, add_zero]
            _ = (l : Fin g → ℂ) - l' := by abel
        rw [this]; exact Λ.sub_mem l.2 l'.2
      subst hqq
      exact hne (Subtype.ext (add_right_cancel hv))
  have hvol : ∀ q, volume (s q) = volume D₁ := fun q => (hs q).measure_eq hD₁
  have hvolE : volume E = ∑' _ : Q, volume D₁ := by
    show volume (⋃ q, s q) = _
    rw [measure_iUnion₀ hsd fun q => (hs q).nullMeasurableSet]
    simp only [hvol]
  have hEFd : volume E = volume Fd := hE.measure_eq hFd
  haveI : Finite Q := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    exact hfin (by rw [← hEFd, hvolE]; exact ENNReal.tsum_const_eq_top_of_ne_zero hD0)
  haveI := Fintype.ofFinite Q
  have hn : (Fintype.card Q : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hintE : IntegrableOn f E volume :=
    integrableOn_finite_iUnion.2 fun q => ((hs q).integrableOn_iff hD₁ hinv₁).2 hint
  have hsi : ∀ q, ∫ z in s q, f z = ∫ z in D₁, f z := fun q => (hs q).setIntegral_eq hD₁ hinv₁
  have hIE : ∫ z in E, f z = Fintype.card Q * ∫ z in D₁, f z := by
    show ∫ z in ⋃ q, s q, f z = _
    rw [integral_iUnion_ae (fun q => (hs q).nullMeasurableSet) hsd hintE, tsum_fintype]
    simp only [hsi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine ⟨(hFd.integrableOn_iff hE hinv).2 hintE, ?_⟩
  rw [hFd.setIntegral_eq hE hinv, ← hEFd, hIE, hvolE, tsum_fintype, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, hab]
  field_simp

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory.BlockInvertibleLocal

theorem exists_linearMap_injective_add_comp {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (a c : V →ₗ[k] V) (h : LinearMap.ker a ⊓ LinearMap.ker c = ⊥) :
    ∃ x : V →ₗ[k] V, Function.Injective (a + x ∘ₗ c) := by
  set W := LinearMap.range (c ∘ₗ (LinearMap.ker a).subtype) with hWdef
  obtain ⟨R, hR⟩ := Submodule.exists_isCompl (LinearMap.range a)
  obtain ⟨W', hW⟩ := Submodule.exists_isCompl W
  have hinjK : Function.Injective (c ∘ₗ (LinearMap.ker a).subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hu' : (u : V) ∈ LinearMap.ker a ⊓ LinearMap.ker c :=
      Submodule.mem_inf.2 ⟨u.2, by simpa using hu⟩
    rw [h, Submodule.mem_bot] at hu'
    exact Subtype.ext hu'
  have h1 := LinearMap.finrank_range_of_inj hinjK
  have h2 := Submodule.finrank_add_eq_of_isCompl hR
  have h3 := LinearMap.finrank_range_add_finrank_ker a
  have hdim : Module.finrank k W = Module.finrank k R := by rw [hWdef, h1]; omega
  let e : W ≃ₗ[k] R := LinearEquiv.ofFinrankEq W R hdim
  let x : V →ₗ[k] V := LinearMap.ofIsCompl hW (R.subtype ∘ₗ e.toLinearMap) 0
  refine ⟨x, ?_⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  obtain ⟨w, hw, w', hw', hsum⟩ := Submodule.mem_sup.1 (hW.sup_eq_top ▸ Submodule.mem_top : c v ∈ W ⊔ W')
  have hxw : x (c v) = ((e ⟨w, hw⟩ : R) : V) := by
    rw [← hsum, map_add (f := _)]
    have hl := LinearMap.ofIsCompl_left_apply (φ := R.subtype ∘ₗ e.toLinearMap) (ψ := (0 : W' →ₗ[k] V)) hW ⟨w, hw⟩
    have hr := LinearMap.ofIsCompl_right_apply (φ := R.subtype ∘ₗ e.toLinearMap) (ψ := (0 : W' →ₗ[k] V)) hW ⟨w', hw'⟩
    simp only at hl hr
    rw [hl, hr]; simp
  have hv' : a v + ((e ⟨w, hw⟩ : R) : V) = 0 := by
    rw [← hxw]; simpa using hv
  have hav : a v = 0 := by
    refine Submodule.disjoint_def.1 hR.disjoint (a v) (LinearMap.mem_range_self a v) ?_
    rw [eq_neg_of_add_eq_zero_left hv']
    exact R.neg_mem (e ⟨w, hw⟩).2
  have he0 : ((e ⟨w, hw⟩ : R) : V) = 0 := by simpa [hav] using hv'
  have hw0 : w = 0 := by
    have : e ⟨w, hw⟩ = 0 := Subtype.ext he0
    have : (⟨w, hw⟩ : W) = 0 := by simpa using this
    simpa using congrArg Subtype.val this
  have hcvW : c v ∈ W := ⟨⟨v, hav⟩, rfl⟩
  have hcvW' : c v ∈ W' := by rw [← hsum, hw0, zero_add]; exact hw'
  have hcv : c v = 0 := Submodule.disjoint_def.1 hW.disjoint _ hcvW hcvW'
  have hmem : v ∈ LinearMap.ker a ⊓ LinearMap.ker c := Submodule.mem_inf.2 ⟨hav, hcv⟩
  rw [h, Submodule.mem_bot] at hmem
  exact hmem

theorem exists_isUnit_det_add_mul_of_field {k : Type} [Field k] {n : ℕ}
    (A B C D : Matrix (Fin n) (Fin n) k) (h : IsUnit (fromBlocks A B C D).det) :
    ∃ X : Matrix (Fin n) (Fin n) k, IsUnit (A + X * C).det := by
  have hinj : Function.Injective (fromBlocks A B C D).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 h)
  have hker : LinearMap.ker (toLin' A) ⊓ LinearMap.ker (toLin' C) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, toLin'_apply, toLin'_apply] at hv
    have hz : (fromBlocks A B C D) *ᵥ (Sum.elim v 0) = (fromBlocks A B C D) *ᵥ 0 := by
      rw [fromBlocks_mulVec, mulVec_zero]
      ext i <;> cases i <;> simp [hv.1, hv.2]
    have h2 := hinj hz
    rw [Submodule.mem_bot]
    funext i
    exact congrFun h2 (Sum.inl i)
  obtain ⟨x, hx⟩ := exists_linearMap_injective_add_comp _ _ hker
  refine ⟨LinearMap.toMatrix' x, ?_⟩
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  convert hx using 1
  funext v
  simp [Matrix.add_mulVec, ← Matrix.mulVec_mulVec]

theorem exists_isUnit_det_add_mul : ∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ}
    (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det := by
  intro O _ _ n A B C D h
  have h' : IsUnit (fromBlocks (A.map (IsLocalRing.residue O)) (B.map (IsLocalRing.residue O))
      (C.map (IsLocalRing.residue O)) (D.map (IsLocalRing.residue O))).det := by
    rw [← fromBlocks_map]
    have := h.map (IsLocalRing.residue O)
    rwa [RingHom.map_det] at this
  obtain ⟨Y, hY⟩ := exists_isUnit_det_add_mul_of_field _ _ _ _ h'
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin n) (Fin n) O, X.map (IsLocalRing.residue O) = Y :=
    ⟨Y.map (Function.surjInv IsLocalRing.residue_surjective), by
      ext i j; simp [Function.surjInv_eq]⟩
  refine ⟨X, ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply,
    Matrix.map_add _ (map_add _), Matrix.map_mul, hX]
  exact hY.ne_zero

end GlobalTheory.BlockInvertibleLocal
end

section

open Matrix Topology

namespace GlobalTheory

theorem exists_mul_mul_eq_one_of_le_rank {k : Type} [Field k] {m n : Type} [Fintype m] [Fintype n]
    {κ : ℕ} (x : Matrix m n k) (h : κ ≤ x.rank) :
    ∃ (A : Matrix (Fin κ) m k) (B : Matrix n (Fin κ) k), A * x * B = 1 := by
  classical
  obtain ⟨w, hw⟩ := exists_linearIndependent_of_le_finrank
    (R := k) (M := LinearMap.range x.mulVecLin) (n := κ) (by simpa only [Matrix.finrank_range_mulVecLin] using h)
  choose v hv using fun i => (w i).2
  let B : Matrix n (Fin κ) k := Matrix.of fun j i => v i j
  have hw' : LinearIndependent k (fun i => (w i : m → k)) :=
    hw.map' (LinearMap.range x.mulVecLin).subtype (Submodule.ker_subtype _)
  have hcol : (x * B).col = fun i => (w i : m → k) := by
    funext i j
    rw [← hv i]
    simp [B, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col]
  have hinj : Function.Injective (x * B).mulVec := by
    rw [Matrix.mulVec_injective_iff, hcol]
    exact hw'
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' (x * B))
    (LinearMap.ker_eq_bot.2 (fun a b hab => hinj (by simpa only [Matrix.toLin'_apply] using hab)))
  refine ⟨LinearMap.toMatrix' g, B, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  rw [Matrix.mul_assoc, this]

theorem isOpen_setOf_le_rank (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    [T1Space k] (m n : Type) [Fintype m] [Fintype n] (κ : ℕ) :
    IsOpen {x : Matrix m n k | κ ≤ x.rank} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨A, B, hAB⟩ := exists_mul_mul_eq_one_of_le_rank x hx
  refine ⟨{y | (A * y * B).det ≠ 0}, ?_, ?_, ?_⟩
  · intro y hy
    have hu : IsUnit (A * y * B) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hy)
    have h1 := Matrix.rank_of_isUnit _ hu
    rw [Fintype.card_fin] at h1
    change κ ≤ y.rank
    rw [← h1]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have hc : Continuous fun y : Matrix m n k => (A * y * B).det :=
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_det
    exact isOpen_ne.preimage hc
  · simp [hAB]

end GlobalTheory
end

section

open MeasureTheory Function
open scoped Pointwise

namespace GlobalTheory.UnfoldNormal

def conjEquiv {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (N : Subgroup H)
    (γ : H) (h1 : ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (h2 : ∀ n ∈ N, γ⁻¹ * n * γ⁻¹⁻¹ ∈ N) : N ≃ₜ* N where
  toFun n := ⟨γ * n * γ⁻¹, h1 n n.2⟩
  invFun n := ⟨γ⁻¹ * n * γ⁻¹⁻¹, h2 n n.2⟩
  left_inv n := by ext; simp [mul_assoc]
  right_inv n := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

theorem map_conj_eq_self (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (Γ N : Subgroup H) (hΓ : Countable Γ) (hNc : IsClosed (N : Set H))
    (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (𝓝 : Set N) (hκ : κ.IsHaarMeasure)
    (h𝓝 : IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ) (hfin : κ 𝓝 ≠ ⊤)
    (γ : H) (hγ : γ ∈ Γ) :
    κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ := by
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : LocallyCompactSpace N := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : Countable (Γ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Γ.subgroupOf N => (⟨(x : N), x.2⟩ : Γ)) ?_
    intro a b hab
    apply Subtype.ext; apply Subtype.ext
    simpa using congrArg Subtype.val hab
  set e := conjEquiv N γ (hN γ hγ) (hN γ⁻¹ (Γ.inv_mem hγ)) with he_def
  have hfun : (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = ⇑e := rfl
  rw [hfun]
  haveI : (κ.map e).IsHaarMeasure := e.isHaarMeasure_map κ
  have hsm : κ.map e = Measure.haarScalarFactor (κ.map e) κ • κ :=
    Measure.isMulLeftInvariant_eq_smul (κ.map e) κ
  set c := Measure.haarScalarFactor (κ.map e) κ

  have hqmp : Measure.QuasiMeasurePreserving e κ κ :=
    ⟨e.continuous.measurable.aemeasurable, by rw [hsm]; exact Measure.smul_absolutelyContinuous⟩
  have hpre : IsFundamentalDomain (Γ.subgroupOf N) (e ⁻¹' 𝓝) κ := by
    refine h𝓝.preimage_of_equiv hqmp (e := fun g : Γ.subgroupOf N =>
      (⟨⟨γ⁻¹ * (g : H) * γ⁻¹⁻¹, hN γ⁻¹ (Γ.inv_mem hγ) _ (g : N).2⟩,
        by
          show γ⁻¹ * (g : H) * γ⁻¹⁻¹ ∈ Γ
          exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) g.2) (Γ.inv_mem (Γ.inv_mem hγ))⟩ : Γ.subgroupOf N)) ?_ ?_
    · constructor
      · intro a b hab
        apply Subtype.ext; apply Subtype.ext
        have := congrArg (fun x : Γ.subgroupOf N => ((x : N) : H)) hab
        simpa using this
      · intro g
        refine ⟨⟨⟨γ * (g : H) * γ⁻¹, hN γ hγ _ (g : N).2⟩, ?_⟩, ?_⟩
        · show γ * (g : H) * γ⁻¹ ∈ Γ
          exact Γ.mul_mem (Γ.mul_mem hγ g.2) (Γ.inv_mem hγ)
        · apply Subtype.ext; apply Subtype.ext; simp [mul_assoc]
    · intro g x
      apply Subtype.ext
      simp [he_def, conjEquiv, Subgroup.smul_def, mul_assoc]
  have hmeq : κ (e ⁻¹' 𝓝) = κ 𝓝 := hpre.measure_eq h𝓝
  have hmap : κ.map e 𝓝 = κ (e ⁻¹' 𝓝) := by
    have := e.toHomeomorph.toMeasurableEquiv.map_apply (μ := κ) 𝓝
    exact this
  have hne : κ 𝓝 ≠ 0 := h𝓝.measure_ne_zero (NeZero.ne κ)
  have hc : (c : ENNReal) * κ 𝓝 = 1 * κ 𝓝 := by
    have h' : (c • κ) 𝓝 = κ 𝓝 := by rw [← hsm, hmap, hmeq]
    rw [one_mul]
    conv_rhs => rw [← h']
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hc1 : (c : ENNReal) = 1 := (ENNReal.mul_left_inj hne hfin).1 hc
  have : c = 1 := by exact_mod_cast hc1
  rw [hsm, this, one_smul]

end GlobalTheory.UnfoldNormal
end

end

section

@[expose] public section

open MeasureTheory Function
open scoped Pointwise

theorem _root_.GlobalTheory.T.haar_map_conj_normalizing_lattice_eq_self : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → κ 𝓝 ≠ ⊤ → (∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) := by
  first | exact @GlobalTheory.UnfoldNormal.map_conj_eq_self | exact GlobalTheory.UnfoldNormal.map_conj_eq_self | (intros; apply GlobalTheory.UnfoldNormal.map_conj_eq_self <;> assumption)

end
end
