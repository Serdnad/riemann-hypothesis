module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.imageRep :
    ∀ (G : Type) [Group G] (C B M : Rep ℤ G) (d : C ⟶ B) (e : B ⟶ M), Function.Exact d.hom e.hom →
      ∃ (K : Rep ℤ G) (p : C ⟶ K) (i : K ⟶ B), Function.Surjective p.hom ∧ Function.Injective i.hom ∧
        (∀ x, i.hom (p.hom x) = d.hom x) ∧ Function.Exact i.hom e.hom := by
  intro G _ C B M d e h
  have hs : Function.Surjective (Abelian.factorThruImage d).hom :=
    (Rep.epi_iff_surjective _).1 inferInstance
  have hi : Function.Injective (Abelian.image.ι d).hom :=
    (Rep.mono_iff_injective _).1 inferInstance
  have hc : ∀ x, (Abelian.image.ι d).hom ((Abelian.factorThruImage d).hom x) = d.hom x := by
    intro x
    have := congrArg (fun f : C ⟶ B => f.hom x) (Abelian.image.fac d)
    simpa using this
  refine ⟨Abelian.image d, Abelian.factorThruImage d, Abelian.image.ι d, hs, hi, hc, ?_⟩
  intro y
  rw [h y]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, hc x⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := hs z
    exact ⟨x, (hc x).symm⟩
end

section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.mapNsmul :
    ∀ (G : Type) [Group G] (A B : Rep ℤ G) (f : A ⟶ B) (g : B ⟶ A) (n j : ℕ),
      (∀ a, g.hom (f.hom a) = n • a) → Subsingleton (groupHomology B j) →
      ∀ z : groupHomology A j, n • z = 0 := by
  intro G _ A B f g n j h hB z
  have hc : groupHomology.chainsMap (MonoidHom.id G) (f ≫ g) =
      n • 𝟙 (groupHomology.inhomogeneousChains A) := by
    ext i : 1
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun c => ?_
    refine Finsupp.ext fun y => ?_
    simp [h]
  have hm : groupHomology.map (MonoidHom.id G) (f ≫ g) j = n • 𝟙 (groupHomology A j) := by
    simp only [groupHomology.map, hc]
    change (HomologicalComplex.homologyFunctor _ _ j).map _ = _
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    rfl
  have e1 : (groupHomology.map (MonoidHom.id G) (f ≫ g) j).hom z = n • z := by
    rw [hm]
    rfl
  rw [← e1, groupHomology.map_id_comp]
  have e2 : (groupHomology.map (MonoidHom.id G) f j).hom z = 0 :=
    Subsingleton.elim (α := groupHomology B j) _ _
  simp [e2]
end

section

open CategoryTheory UpperTheory.V.KH

private theorem group_homology_long_exact (k G : Type) [CommRing k] [Group G] (A B C : Rep k G)
    (f : A ⟶ B) (g : B ⟶ C) (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom)
    (hg : Function.Surjective g.hom) (j : ℕ) :
      (∃ (u : groupHomology A j →+ groupHomology B j) (v : groupHomology B j →+ groupHomology C j),
        Function.Exact u v) ∧
      (∃ (u : groupHomology B (j + 1) →+ groupHomology C (j + 1))
        (v : groupHomology C (j + 1) →+ groupHomology A j), Function.Exact u v) := by
  have h0 : f ≫ g = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact hfg.apply_apply_eq_zero x
  let X : ShortComplex (Rep k G) := ShortComplex.mk f g h0
  have hex : X.Exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful X (forget₂ (Rep k G) (ModuleCat k))]
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hfg
  have hX : X.ShortExact :=
    ShortComplex.ShortExact.mk' hex ((Rep.mono_iff_injective f).2 hf)
      ((Rep.epi_iff_surjective g).2 hg)
  have h2 := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (groupHomology.mapShortComplex₂_exact hX j)
  have h3 := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (groupHomology.mapShortComplex₃_exact hX (i := j + 1) (j := j) rfl)
  exact ⟨⟨(groupHomology.mapShortComplex₂ X j).f.hom.toAddMonoidHom,
      (groupHomology.mapShortComplex₂ X j).g.hom.toAddMonoidHom, h2⟩,
    ⟨(groupHomology.mapShortComplex₃ hX (i := j + 1) (j := j) rfl).f.hom.toAddMonoidHom,
      (groupHomology.mapShortComplex₃ hX (i := j + 1) (j := j) rfl).g.hom.toAddMonoidHom, h3⟩⟩

theorem UpperTheory.V.KH.les :
    ∀ (G : Type) [Group G] (A B C : Rep ℤ G) (f : A ⟶ B) (g : B ⟶ C),
      Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom → ∀ j : ℕ,
      (∃ (u : groupHomology A j →+ groupHomology B j) (v : groupHomology B j →+ groupHomology C j),
        Function.Exact u v) ∧
      (∃ (u : groupHomology B (j + 1) →+ groupHomology C (j + 1))
        (v : groupHomology C (j + 1) →+ groupHomology A j), Function.Exact u v) := by
  intro G _ A B C f g hf hfg hg j
  exact group_homology_long_exact ℤ G A B C f g hf hfg hg j
end

section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.maxIndep :
    ∀ (M : Type) [AddCommGroup M] [IsAddTorsionFree M] (s t : Set M), s ⊆ t →
      LinearIndepOn ℤ id s → ∃ b : Set M, s ⊆ b ∧ b ⊆ t ∧ LinearIndepOn ℤ id b ∧
        ∀ x ∈ t, ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ Submodule.span ℤ b := by
  intro M _ _ s t hst hs
  let S : Set (Set M) := {b | s ⊆ b ∧ b ⊆ t ∧ LinearIndepOn ℤ id b}
  obtain ⟨m, hsm, hmax⟩ := zorn_subset_nonempty S (by
    intro c hcS hc hne
    refine ⟨⋃₀ c, ⟨?_, ?_, ?_⟩, fun b hb => Set.subset_sUnion_of_mem hb⟩
    · obtain ⟨b, hb⟩ := hne
      exact (hcS hb).1.trans (Set.subset_sUnion_of_mem hb)
    · exact Set.sUnion_subset fun b hb => (hcS hb).2.1
    · exact linearIndepOn_sUnion_of_directed hc.directedOn fun b hb => (hcS hb).2.2)
    s ⟨subset_rfl, hst, hs⟩
  obtain ⟨-, hmt, hmi⟩ := hmax.prop
  refine ⟨m, hsm, hmt, hmi, fun x hx => ?_⟩
  by_cases hxm : x ∈ m
  · exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span hxm⟩
  have hdep : ¬ LinearIndepOn ℤ id (insert x m) := by
    intro hi
    have he := hmax.eq_of_subset
      ⟨hsm.trans (Set.subset_insert _ _), Set.insert_subset hx hmt, hi⟩ (Set.subset_insert _ _)
    exact hxm (he ▸ Set.mem_insert x m)
  rw [linearIndepOn_iff] at hdep
  push_neg at hdep
  obtain ⟨l, hl, hl0, hlne⟩ := hdep
  have hl' : Finsupp.erase x l ∈ Finsupp.supported ℤ ℤ m := by
    rw [Finsupp.mem_supported] at hl ⊢
    intro y hy
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hy
    have hyx : y ≠ x := by
      rintro rfl
      exact hy (by simp)
    rw [Finsupp.erase_ne hyx] at hy
    exact (hl (Finsupp.mem_support_iff.mpr hy)).resolve_left hyx
  have hsum : l x • x + Finsupp.linearCombination ℤ id (Finsupp.erase x l) = 0 := by
    have h1 := congrArg (Finsupp.linearCombination ℤ id) (Finsupp.single_add_erase x l)
    rw [map_add (f := _), Finsupp.linearCombination_single, hl0] at h1
    simpa using h1
  have hxne : l x ≠ 0 := by
    intro h0
    apply hlne
    have he : Finsupp.erase x l = l := by
      ext y
      by_cases hy : y = x
      · subst hy
        simp [h0]
      · simp [Finsupp.erase_ne hy]
    rw [← he]
    apply (linearIndepOn_iff.mp hmi) _ hl'
    rw [h0, zero_smul, zero_add] at hsum
    exact hsum
  refine ⟨l x, hxne, ?_⟩
  have hmem : Finsupp.linearCombination ℤ id (Finsupp.erase x l) ∈ Submodule.span ℤ m := by
    have h2 := (Finsupp.mem_span_image_iff_linearCombination ℤ (v := id) (s := m)).mpr ⟨_, hl', rfl⟩
    simpa using h2
  rw [eq_neg_of_add_eq_zero_left hsum]
  exact Submodule.neg_mem _ hmem
end

section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.fullEnum :
    ∀ (ι : Type) [Finite ι] (b : Set (ι →₀ ℤ)), LinearIndepOn ℤ id b →
      (∀ k : ι, ∃ n : ℤ, n ≠ 0 ∧ n • Finsupp.single k (1 : ℤ) ∈ Submodule.span ℤ b) →
      ∃ v : ι → (ι →₀ ℤ), LinearIndependent ℤ v ∧ Set.range v = b := by
  intro ι _ b hb hn
  have hli : LinearIndependent ℤ (fun x : b => (x : ι →₀ ℤ)) := hb
  haveI : Finite b := hli.finite
  classical
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite b
  have h1 : Fintype.card b ≤ Fintype.card ι := by
    have := hli.fintype_card_le_finrank
    rwa [Module.finrank_finsupp_self] at this
  choose n hn0 hmem using hn
  have hind : LinearIndependent ℤ (fun k : ι => n k • Finsupp.single k (1 : ℤ)) := by
    rw [linearIndependent_iff']
    intro s c hs i hi
    have := congrArg (fun f : ι →₀ ℤ => f i) hs
    simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
      Finsupp.coe_zero, Pi.zero_apply] at this
    rw [Finset.sum_eq_single i] at this
    · simp only [if_true, mul_one] at this
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h (hn0 i)
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd hi h
  let w : ι → Submodule.span ℤ b := fun k => ⟨n k • Finsupp.single k (1 : ℤ), hmem k⟩
  have hw : LinearIndependent ℤ w :=
    LinearIndependent.of_comp (Submodule.span ℤ b).subtype hind
  have h2 : Fintype.card ι ≤ Fintype.card b := by
    have := hw.fintype_card_le_finrank
    rw [finrank_span_set_eq_card hb, Set.toFinset_card] at this
    convert this
  let e : ι ≃ b := Fintype.equivOfCardEq (le_antisymm h2 h1)
  refine ⟨fun k => (e k : ι →₀ ℤ), hli.comp e e.injective, ?_⟩
  ext y
  constructor
  · rintro ⟨k, rfl⟩
    exact (e k).2
  · intro hy
    exact ⟨e.symm ⟨y, hy⟩, by simp⟩
end

section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.det_natAbs_le_prod_l1_norms :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ),
      M.det.natAbs ≤ ∏ i, ∑ k, (M i k).natAbs := by
  intro ι _ _ M
  have key : |M.det| ≤ ∏ i, ∑ k, |M i k| := by
    rw [← Matrix.det_transpose, Matrix.det_apply]
    let e : Equiv.Perm ι ↪ (ι → ι) := ⟨fun σ => ⇑σ, DFunLike.coe_injective⟩
    calc |∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, M.transpose (σ i) i|
        ≤ ∑ σ : Equiv.Perm ι, |Equiv.Perm.sign σ • ∏ i, M.transpose (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ σ : Equiv.Perm ι, ∏ i, |M i (σ i)| := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
            simp [h, Finset.abs_prod, Matrix.transpose_apply]
      _ = ∑ f ∈ (Finset.univ : Finset (Equiv.Perm ι)).map e, ∏ i, |M i (f i)| := by
          rw [Finset.sum_map]
          rfl
      _ ≤ ∑ f : ι → ι, ∏ i, |M i (f i)| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun f _ _ => Finset.prod_nonneg fun i _ => abs_nonneg _)
      _ = ∏ i, ∑ k, |M i k| := (Fintype.prod_sum (fun i k => |M i k|)).symm
  have h2 : ((M.det.natAbs : ℕ) : ℤ) ≤ ((∏ i, ∑ k, (M i k).natAbs : ℕ) : ℤ) := by
    push_cast
    simpa [Int.natCast_natAbs] using key
  exact_mod_cast h2
end
