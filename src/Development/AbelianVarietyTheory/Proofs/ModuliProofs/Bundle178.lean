module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle170
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUnifOfParts
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle063
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle176
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle177
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle125
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarisedOfVeryDenseFibres
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle172
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelChangeExtendsBaseModel
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

namespace ModelJoin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem comp_of_eq {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (m' : SABMap t'' t' g) (e : g ≫ f = h) :
    ∃ n : SABMap t'' t h, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabComp pullCubComp E H _ _ _ t t' t'' f g m m'

theorem cancel_of_eq {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (n : SABMap t'' t h) (e : g ≫ f = h) :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabCancel pullCubCancel E H _ _ _ t t' t'' f g m n

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem isOpenImmersion_away {O R : Type} [CommRing O] [CommRing R] (a : O) (b : O →+* R)
    (h : @IsLocalization.Away O _ a R _ b.toAlgebra) : IsOpenImmersion (spMap b) := by
  letI := b.toAlgebra
  exact IsOpenImmersion.of_isLocalization (R := O) (S := R) a

theorem mem_range_away {O R : Type} [CommRing O] [CommRing R] (a : O) (b : O →+* R)
    (h : @IsLocalization.Away O _ a R _ b.toAlgebra) (x : Sp O) (hx : a ∉ x.asIdeal) :
    x ∈ Set.range (spMap b) := by
  letI := b.toAlgebra
  have := PrimeSpectrum.localization_away_comap_range R a
  have h2 : (x : PrimeSpectrum O) ∈ Set.range (PrimeSpectrum.comap (algebraMap O R)) := by
    rw [this]; exact hx
  exact h2

theorem arith_base (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Algebra.FiniteType ℤ O] :
    LocallyOfFiniteType (spMap (algebraMap ℤ O)) ∧ Flat (spMap (algebraMap ℤ O)) := by
  constructor
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  · rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance

end ModelJoin

open ModelJoin

theorem exists_join_of_models : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (I : Type) [Finite I] [Nonempty I] (R : I → Type) [∀ i, CommRing (R i)] (a : I → O) (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) (C : ∀ i, Cpt c t (ω i)), IsDedFrac β → (∀ i, IsDedFrac (ω i) ∧ (ω i).comp (b i) = β ∧ @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) → Ideal.span (Set.range a) = ⊤ → Algebra.FiniteType ℤ O → IsProper t.G.hom → ∃ C' : Cpt c t β, ∀ i, ∃ (f : pullback C'.s (spMap (b i)) ⟶ (C i).X) (t₁ : SAB H (pullback C'.s (spMap (b i)))) (m₁ : SABMap t₁ C'.t (pullback.fst _ _)) (m₂ : SABMap t₁ (C i).t f), f ≫ (C i).s = pullback.snd _ _ ∧ (∀ g : U ⟶ pullback C'.s (spMap (b i)), g ≫ pullback.fst _ _ = C'.j → g ≫ f = (C i).j) ∧ ∀ y : t.G.left ⟶ t₁.G.left, y ≫ m₁.φ = C'.m.φ → y ≫ m₂.φ = (C i).m.φ := by
  intro hext E _ _ _ H U F O _ _ c t β I _ _ R _ a b ω C hβ hω hspan hft hprop
  obtain ⟨⟨hdom, hded⟩, hchar, hfrac⟩ := id hβ
  obtain ⟨X, s, jQ, f, hn, hproj, hflat, hover, hopen, hdense, hf⟩ :=
    GlobalTheory.T.exists_join_normal_projective_models E H U F O c t β I R a b ω C hβ hω hspan hchar
  have hpo : IsPreimmersion (jQ ≫ pullback.fst s (spMap β)) ∧ Flat (jQ ≫ pullback.fst s (spMap β)) ∧
      IsDominant (jQ ≫ pullback.fst s (spMap β)) ∧ QuasiCompact (jQ ≫ pullback.fst s (spMap β)) := by
    letI := β.toAlgebra
    exact (genericPart_dense_proOpen O F X U s jQ hflat hproj hopen hdense).2.2.2
  have hβp : IsPreimmersion (spMap β) := by
    letI := β.toAlgebra
    exact IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := F) (nonZeroDivisors O)
  have hfp : IsPreimmersion (pullback.fst s (spMap β)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hβp
  have hb : ∀ i, IsOpenImmersion (spMap (b i)) := fun i => isOpenImmersion_away (a i) (b i) (hω i).2.2
  have hβe : ∀ i, spMap β = spMap (ω i) ≫ spMap (b i) := fun i => by
    rw [← (hω i).2.1]; exact Spec.map_comp (CommRingCat.ofHom (b i)) (CommRingCat.ofHom (ω i))
  have hsp : IsProper s := projProper O X s hproj
  let V : I → X.Opens := fun i => (pullback.fst s (spMap (b i))).opensRange
  let e : ∀ i, pullback s (spMap (b i)) ≅ (V i).toScheme := fun i =>
    (pullback.fst s (spMap (b i))).isoOpensRange
  have he : ∀ i, (e i).hom ≫ (V i).ι = pullback.fst s (spMap (b i)) := fun i =>
    Scheme.Hom.isoOpensRange_hom_ι _
  have hcov' : ∀ x : X, ∃ i, x ∈ Set.range (pullback.fst s (spMap (b i))) := by
    intro x
    have : ∃ i, a i ∉ (s x).asIdeal := by
      by_contra hc
      push Not at hc
      refine (s x).isPrime.ne_top (top_le_iff.mp ?_)
      rw [← hspan, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hc i
    obtain ⟨i, hi⟩ := this
    refine ⟨i, ?_⟩
    rw [Scheme.Pullback.range_fst]
    exact mem_range_away (a i) (b i) (hω i).2.2 _ hi
  have hcov : ⨆ i, V i = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, hi⟩ := hcov' x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  have hw : ∀ i, (jQ ≫ pullback.fst s (spMap β)) ≫ s = (c ≫ spMap (ω i)) ≫ spMap (b i) := fun i => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hover, Category.assoc, ← hβe]
  let g : ∀ i, U ⟶ pullback s (spMap (b i)) := fun i => pullback.lift _ _ (hw i)
  have hg : ∀ i, g i ≫ pullback.fst _ _ = jQ ≫ pullback.fst s (spMap β) := fun i => pullback.lift_fst _ _ _
  choose tV mV using fun i => exists_pull ((e i).inv ≫ f i) (C i).t
  replace mV := fun i => (mV i).some
  choose t₁ k using fun i => exists_pull (e i).hom (tV i)
  replace k := fun i => (k i).some
  choose aV haV using fun i => cancel_of_eq (g := g i ≫ (e i).hom) (mV i) (C i).m (by
    rw [Category.assoc, Iso.hom_inv_id_assoc]; exact (hf i).2.1 _ (hg i))
  obtain ⟨hz₁, hz₂⟩ := arith_base O
  obtain ⟨t', a', n, hn'⟩ := GlobalTheory.T.exists_semiAbelianTriple_glue_common_genericPart hext E H X U (jQ ≫ pullback.fst s (spMap β)) t I V
    (fun i => g i ≫ (e i).hom) tV aV inferInstance
    ⟨hn, s ≫ spMap (algebraMap ℤ O), inferInstance, inferInstance⟩ hpo.1 hpo.2.1 hpo.2.2.1 hpo.2.2.2 hprop hcov
    (fun i => by rw [Category.assoc, he, hg])
  choose m₁ hm₁ using fun i => comp_of_eq (n i) (k i) (he i)
  choose m₂ hm₂ using fun i => comp_of_eq (h := f i) (mV i) (k i) (Iso.hom_inv_id_assoc _ _)
  have hab : pullback.fst s (spMap β) ⁻¹' abLocus t'.G = Set.range jQ := by
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨i, w, hw'⟩ := hcov' (pullback.fst s (spMap β) z)
      have h1 : w ∈ abLocus (t₁ i).G :=
        (abLocus_pullback abLocusOne t'.semi (m₁ i).cart.1 w).1 (by rw [hw']; exact hz)
      have h2 : f i w ∈ abLocus (C i).t.G :=
        (abLocus_pullback abLocusOne (C i).t.semi (m₂ i).cart.1 w).2 h1
      have h3 : f i w ∈ Set.range (pullback.fst (C i).s (spMap (ω i))) := by
        rw [Scheme.Pullback.range_fst]
        refine ⟨pullback.snd s (spMap β) z, (spMap (b i)).isOpenEmbedding.injective ?_⟩
        rw [← Scheme.Hom.comp_apply, ← hβe, ← Scheme.Hom.comp_apply, ← pullback.condition,
          ← Scheme.Hom.comp_apply (f i), (hf i).1, ← Scheme.Hom.comp_apply, ← pullback.condition,
          Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hw']
      obtain ⟨z', hz'⟩ := h3
      have h4 : z' ∈ Set.range (C i).jQ := by
        rw [← (C i).ab_gen]
        show _ ∈ abLocus (C i).t.G
        rw [hz']; exact h2
      obtain ⟨u, hu⟩ := h4
      obtain ⟨u', hu'⟩ := (hf i).2.2 w ⟨u, by rw [Cpt.j, Scheme.Hom.comp_apply, hu, hz']⟩
      refine ⟨u', (pullback.fst s (spMap β)).isEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hu', hw']
    · rintro _ ⟨u, rfl⟩
      exact range_subset_abLocus_of_isProper t'.semi a'.cart.1 ⟨u, Scheme.Hom.comp_apply _ _ _⟩
  refine ⟨⟨X, s, hn, hproj, hflat, jQ, hover, hopen, hdense, t', a', hab⟩, fun i => ?_⟩
  refine ⟨f i, t₁ i, m₁ i, m₂ i, (hf i).1, (hf i).2.1, fun y hy => ?_⟩
  have hmono : IsOpenImmersion (n i).φ :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (n i).cart.1.flip inferInstance
  have hy' : y ≫ (k i).φ = (aV i).φ := by
    rw [← cancel_mono (n i).φ, Category.assoc, ← hm₁, hn']; exact hy
  rw [hm₂, ← Category.assoc, hy', haV]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section

namespace GlobalTheory.VolPoly

theorem eval_eq_of_eventually {r r' : ℕ} (Ψ : MvPolynomial (Fin (r + 1)) ℚ) (Ψ' : MvPolynomial (Fin (r' + 1)) ℚ)
    (a : Fin (r + 1) → ℤ) (a' : Fin (r' + 1) → ℤ)
    (h : ∀ᶠ t : ℕ in Filter.atTop,
      MvPolynomial.eval (fun i => (((a + Pi.single (M := fun _ => ℤ) 0 (t : ℤ) : Fin (_ + 1) → ℤ) i : ℤ) : ℚ)) Ψ =
        MvPolynomial.eval (fun i => (((a' + Pi.single (M := fun _ => ℤ) 0 (t : ℤ) : Fin (_ + 1) → ℤ) i : ℤ) : ℚ)) Ψ') :
    MvPolynomial.eval (fun i => (a i : ℚ)) Ψ = MvPolynomial.eval (fun i => (a' i : ℚ)) Ψ' := by
  have key : ∀ {r : ℕ} (Ψ : MvPolynomial (Fin (r + 1)) ℚ) (a : Fin (r + 1) → ℤ), ∃ p : Polynomial ℚ,
      ∀ t : ℕ, p.eval (t : ℚ) =
        MvPolynomial.eval (fun i => (((a + Pi.single (M := fun _ => ℤ) 0 (t : ℤ) : Fin (_ + 1) → ℤ) i : ℤ) : ℚ)) Ψ := by
    intro r Ψ a
    refine ⟨MvPolynomial.aeval (fun i => Polynomial.C (a i : ℚ) + if i = 0 then Polynomial.X else 0) Ψ, fun t => ?_⟩
    rw [← Polynomial.coe_aeval_eq_eval, MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_eq_eval]
    congr 2
    funext i
    by_cases hi : i = 0 <;> simp [hi, Pi.single_apply]
  obtain ⟨p, hp⟩ := key Ψ a
  obtain ⟨p', hp'⟩ := key Ψ' a'
  have e : p = p' := by
    obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.1 h
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ ((Set.Ici_infinite t₀).image (f := fun t : ℕ => (t : ℚ)) Nat.cast_injective.injOn)
    rintro _ ⟨t, ht, rfl⟩
    show p.eval (t : ℚ) = p'.eval (t : ℚ)
    rw [hp, hp', ht₀ t ht]
  have h0 := (hp 0).symm.trans (e ▸ hp' 0)
  simpa using h0

theorem sum_monomial_add_single {r : ℕ} (a : Fin (r + 1) → ℤ) (t : ℕ) :
    ∑ i : Fin (r + 1), Polynomial.monomial (i : ℕ) ((a + Pi.single (M := fun _ => ℤ) 0 (t : ℤ) : Fin (_ + 1) → ℤ) i) =
      ∑ i : Fin (r + 1), Polynomial.monomial (i : ℕ) (a i) + (t : Polynomial ℤ) := by
  simp only [Pi.add_apply, map_add (f := _), Finset.sum_add_distrib]
  congr 1
  rw [Fin.sum_univ_succ]
  simp

theorem exists_poly_extension (g : ℕ) (A : Polynomial ℤ → Prop) (V : Polynomial ℤ → ℚ → Prop)
    (hV : ∀ F x y, V F x → V F y → x = y)
    (hΨ : ∀ r : ℕ, ∃ Ψ : MvPolynomial (Fin r) ℚ, Ψ.IsHomogeneous g ∧ ∀ a : Fin r → ℤ,
      A (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) →
        V (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) (MvPolynomial.eval (fun i => (a i : ℚ)) Ψ))
    (hA : ∀ F, ∀ᶠ t : ℕ in Filter.atTop, A (F + t)) :
    ∃ D : Polynomial ℤ → ℚ, (∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous g ∧ ∀ a : Fin r → ℤ,
      D (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) = MvPolynomial.eval (fun i => (a i : ℚ)) Φ) ∧
      ∀ F, A F → V F (D F) := by
  choose Ψ hh hΨ using hΨ
  have hF : ∀ F : Polynomial ℤ,
      ∑ i : Fin (F.natDegree + 1), Polynomial.monomial (i : ℕ) (F.coeff i) = F := fun F => by
    rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.monomial i (F.coeff i))]
    exact (F.as_sum_range).symm
  refine ⟨fun F => MvPolynomial.eval (fun i : Fin (F.natDegree + 1) => (F.coeff i : ℚ)) (Ψ _), fun r => ?_,
    fun F h => ?_⟩
  · refine ⟨MvPolynomial.aeval (Fin.snoc (α := fun _ => MvPolynomial (Fin r) ℚ) MvPolynomial.X 0) (Ψ (r + 1)), ?_,
      fun a => ?_⟩
    · have := (hh (r + 1)).aeval (n := 1) (Fin.snoc (α := fun _ => MvPolynomial (Fin r) ℚ) MvPolynomial.X 0)
        (fun i => by
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using MvPolynomial.isHomogeneous_zero _ _ _
          · simpa using MvPolynomial.isHomogeneous_X _ _)
      simpa using this
    · set F := ∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i) with hFa
      have e : ∑ i : Fin (r + 1), Polynomial.monomial (i : ℕ) (Fin.snoc (α := fun _ => ℤ) a 0 i) = F := by
        rw [Fin.sum_univ_castSucc]
        simp [hFa]
      have e₂ := eval_eq_of_eventually (Ψ (F.natDegree + 1)) (Ψ (r + 1)) (fun i => F.coeff i)
        (Fin.snoc (α := fun _ => ℤ) a 0) ((hA F).mono fun t ht => by
          have h₁ := hΨ _ ((fun i : Fin (F.natDegree + 1) => F.coeff i) + Pi.single (M := fun _ => ℤ) 0 (t : ℤ))
          have h₂ := hΨ _ (Fin.snoc (α := fun _ => ℤ) a 0 + Pi.single (M := fun _ => ℤ) 0 (t : ℤ))
          rw [sum_monomial_add_single, hF] at h₁
          rw [sum_monomial_add_single, e] at h₂
          exact hV _ _ _ (h₁ ht) (h₂ ht))
      refine e₂.trans ?_
      rw [← MvPolynomial.aeval_eq_eval, ← MvPolynomial.aeval_eq_eval, MvPolynomial.comp_aeval_apply]
      congr 2
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  · have := hΨ _ (fun i : Fin (F.natDegree + 1) => F.coeff i)
    rw [hF] at this
    exact this h

theorem relAmple_of_cls_eq {K : Type} [Field K] (P : Out.PolAV (Sp K)) {M N : LB P.A.left} (hM : M.IsLB) (hN : N.IsLB)
    (e : CechPic.cls M hM = CechPic.cls N hN) (h : Out.RelAmple P.A M) : Out.RelAmple P.A N := by
  haveI : IsProper P.A.hom := P.isAb.proper
  rw [relAmple_iff_isAmpleLB_of_isAffine P.A hM] at h
  rw [relAmple_iff_isAmpleLB_of_isAffine P.A hN]
  exact h.of_lbIso hN ((CechPic.cls_eq_iff hN hM).1 e.symm)

theorem exists_vol_poly : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A), M.IsLB → FormIs P M s → ∀ (ev : Polynomial ℤ → (P.A ⟶ P.A)), ev 1 = 𝟙 P.A → (∀ F G, ev (F + G) = ev F * ev G) → (∀ F, ev (Polynomial.X * F) = ev F ≫ s) → ∃ D : Polynomial ℤ → ℚ, (∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous P.g ∧ ∀ a : Fin r → ℤ, D (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) = MvPolynomial.eval (fun i => (a i : ℚ)) Φ) ∧ (∀ F, Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev (F)] P.L) → Vol P.A.hom (cubeLB P.A ![𝟙 P.A, ev (F)] P.L) P.g ((D F : ℚ) : ℝ)) ∧ ∀ F, ∀ᶠ t : ℕ in Filter.atTop, Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev (F + t)] P.L) ∧ IsFinite (ev (F + t)).left := by
  intro h₁ h₂ K _ _ P M s hM hs ev e₁ eadd eX
  obtain ⟨-, emul, hform, -, hdiv, hone, -⟩ := (GlobalTheory.T.polarisationForm_intPolynomial_bundles h₁ h₂ K P M s hM hs).2 ev e₁ eadd eX
  have hB : ∀ F, (cubeLB P.A ![𝟙 P.A, ev F] P.L).IsLB := fun F => LB.isLB_linComb P.isLB _ _
  let b : Polynomial ℤ →+ CechPic.Pic P.A.left := AddMonoidHom.mk' (fun F => CechPic.cls _ (hB F)) fun F G => by
    have := (CechPic.cls_eq_iff (LB.isLB_div (hB _) (hB _)) (hB _)).2 (hdiv F G)
    rw [CechPic.cls_div (hB _) (hB _)] at this
    exact (sub_eq_iff_eq_add'.1 this)
  have hb : ∀ F, b F = CechPic.cls _ (hB F) := fun _ => rfl
  have hp : ∀ n, (lbPow P.L n).IsLB := fun n => LB.isLB_linComb P.isLB _ _
  have b₁ : b 1 = 2 • CechPic.cls _ P.isLB :=
    ((CechPic.cls_eq_iff (hB 1) (hp 2)).2 hone).trans (CechPic.cls_lbPow P.isLB 2 _)
  have hA : ∀ F, ∀ᶠ t : ℕ in Filter.atTop, Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev (F + t)] P.L) := fun F => by
    have h := GlobalTheory.T.eventually_section_and_relAmple_pow_div K P P.L _ P.isLB (hB (-F)) P.ample
    have ht : Filter.Tendsto (fun t : ℕ => t * 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun t => by show t ≤ t * 2; omega) Filter.tendsto_id
    refine (ht.eventually h).mono fun t h => relAmple_of_cls_eq P (LB.isLB_div (hp _) (hB _)) (hB _) ?_ h.2
    rw [CechPic.cls_div (hp _) (hB _), CechPic.cls_lbPow P.isLB, ← hb, ← hb, map_neg, map_add (f := _), ← nsmul_one t,
      map_nsmul, b₁, mul_smul, sub_neg_eq_add, add_comm]
  obtain ⟨D, hD, hD'⟩ := exists_poly_extension P.g (fun F => Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev F] P.L))
    (fun F x => Vol P.A.hom (cubeLB P.A ![𝟙 P.A, ev F] P.L) P.g (x : ℝ))
    (fun F x y hx hy => by exact_mod_cast (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g (hB F)).2.1 _ _ hx hy)
    (fun r => by
      let φ : Fin r × ULift.{0} (Finset (Fin 2)) → (P.A.left ⟶ P.A.left) := fun p =>
        (psum P.A ![𝟙 P.A, ev (Polynomial.monomial (p.1 : ℕ) 1)] p.2.down).left
      obtain ⟨Φ, hΦ, hv⟩ := GlobalTheory.T.exists_homogeneousPolynomial_volume_pullback_combinations h₁ h₂ K P _ φ
      refine ⟨MvPolynomial.aeval (fun p : Fin r × ULift.{0} (Finset (Fin 2)) =>
        MvPolynomial.C ((-1 : ℚ) ^ (2 - p.2.down.card)) * MvPolynomial.X p.1) Φ, ?_, fun a ha => ?_⟩
      · simpa using hΦ.aeval (n := 1) (fun p : Fin r × ULift.{0} (Finset (Fin 2)) =>
          MvPolynomial.C ((-1 : ℚ) ^ (2 - p.2.down.card)) * MvPolynomial.X p.1)
          fun p => (MvPolynomial.isHomogeneous_X ℚ p.1).C_mul _
      · let ε : Fin r × ULift.{0} (Finset (Fin 2)) → ℤ := fun p => a p.1 * (-1) ^ (2 - p.2.down.card)
        have hC : (LB.LinComb P.L φ ε).IsLB := LB.isLB_linComb P.isLB _ _
        have e : CechPic.cls _ (hB (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i))) = CechPic.cls _ hC := by

          rw [← hb, map_sum, CechPic.cls_linComb P.isLB, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun i _ => ?_
          have : Polynomial.monomial (i : ℕ) (a i) = a i • Polynomial.monomial (i : ℕ) (1 : ℤ) := by
            rw [Polynomial.smul_monomial, smul_eq_mul, _root_.mul_one]
          rw [this, map_zsmul, hb]
          refine (congrArg (a i • ·) (CechPic.cls_linComb P.isLB _ _ _)).trans ?_
          simp only [Finset.smul_sum, ε, φ, mul_smul]
        have := (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g hC).2.2.1 _ _ (hB _) ((CechPic.cls_eq_iff _ _).1 e.symm)
          (hv ε (relAmple_of_cls_eq P (hB _) hC e ha))
        convert this using 2
        rw [← MvPolynomial.aeval_eq_eval, ← MvPolynomial.aeval_eq_eval, MvPolynomial.comp_aeval_apply]
        congr 2
        funext p
        simp [ε, mul_comm])
    hA
  refine ⟨D, hD, hD', fun F => (hA F).mono fun t ht => ⟨ht, ?_⟩⟩
  have hf := (GlobalTheory.FormFinite.isFinite_and_surjective_of_formIs h₁ h₂ K P _ _ (hB _) ht (hform _)).1
  rw [mul_comm, emul, Over.comp_left] at hf
  haveI : IsProper P.A.hom := P.isAb.proper
  haveI : IsSeparated ((ev 2).left ≫ P.A.hom) := by rw [Over.w]; infer_instance
  haveI : IsSeparated (ev 2).left := IsSeparated.of_comp _ P.A.hom
  exact IsFinite.of_comp _ (ev 2).left

end GlobalTheory.VolPoly

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_principallyPolarised_of_veryDense_fibres : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R) (m : Z ⊗ Z ⟶ Z) (F : Option J → (Z ⟶ Z)), VeryDense (objPrimes b Mat κ β v) → (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ φ₂ : (t'.A ⊗ t'.A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[t'.A]).left ≫ φ) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), t'.Shape Mat κ → (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ i : Option J, φ ≫ (F i).left = (i.elim (𝟙 t'.A)⁻¹ t'.act : t'.A ⟶ t'.A).left ≫ φ) → ∃ (P : Out.PolAV (Sp R)) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ P.A)), (P.g = g ∧ (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ (n ^ j) = 1) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ P.A), y ^ (n ^ j) = 1 → ∃! c : Ix g (n ^ j), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) = y)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ ψ : t'.A.left ⟶ P.A.left, (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left) := by
  first | exact @GlobalTheory.exists_polAV_of_veryDense_fibres | exact GlobalTheory.exists_polAV_of_veryDense_fibres | (intros; apply GlobalTheory.exists_polAV_of_veryDense_fibres <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

theorem _root_.GlobalTheory.T.exists_goodThetaObjectEmbeddingData : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), ∃ (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R) (Hh : Type) (_ : Finite Hh) (hh : Hh → Ix g ((n ^ j) ^ 2)) (Q : Polynomial ℚ) (d : ℕ), FibData b Mat κ β v (n ^ 2) p hh Q d := by
  first | exact @GlobalTheory.ZM.GoodFibre.exists_fibData | exact GlobalTheory.ZM.GoodFibre.exists_fibData | (intros; apply GlobalTheory.ZM.GoodFibre.exists_fibData <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.nonempty_cmModuli_of_deeper_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (Moduli D l₂) → Nonempty (Moduli D l) := by
  first | exact @GlobalTheory.ZM.moduli_of_deeper_level | exact GlobalTheory.ZM.moduli_of_deeper_level | (intros; apply GlobalTheory.ZM.moduli_of_deeper_level <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem familyUnif_of_thetaUnif : ThetaUnifAV → Out.Laws → N1c := fun hU hL =>
  GlobalTheory.familyUnif_of_parts GlobalTheory.datum_exists_period
    (GlobalTheory.PointUnif.exists_uniformisation_at_point_closed hU hL) (GlobalTheory.Moduli.exists_point_of_isPeriod hU hL) (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed hU hL)
    (GlobalTheory.exists_local_period_lift hU hL) (GlobalTheory.T.isHolTo_modulipoint_exp_of_holomorphic_periods hU hL)
    (GlobalTheory.FiniteClasses.finite_image_of_locally_constant_on_holomorphic_families GlobalTheory.SubfieldChart.exists_holomorphic_chart)
    (GlobalTheory.exists_thetaFrame_family hU hL)
    (GlobalTheory.SimMult.exists_sim_trivial_of_mult GlobalTheory.SimAlg.sim_group GlobalTheory.exists_sim_lift)

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.levelChange_extends_base_model : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), 1 ≤ D.p + D.q → ∀ (l₀ l₁ : Level H) (h : l₁.A = N) (O₀ O₁ : Type) [CommRing O₀] [CommRing O₁] (β₀ : O₀ →+* KA l₀) (β₁ : O₁ →+* KA l₁) (C : Cpt (Xo l₀).s (Xo l₀).univ.t β₀) (C₁ : Cpt (Xo l₁).s (Xo l₁).univ.t β₁) (b : O₀ →+* O₁) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (_ : C₁.Above C b r ν) (b' : RZ H n N →+* O₁) (q : C₁.X ⟶ T.Z) (hq : q ≫ T.s = C₁.s ≫ spMap b'), IsDedFrac β₀ → IsDedFrac β₁ → Algebra.FiniteType ℤ O₀ → IsFinite (spMap b) → IsFinite (pullback.lift q C₁.s hq) → C₁.j ≫ q = T.a l₁ h → l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → N.Coprime l₁.M → LevComp (Xo l₁).univ (Xo l₀).univ r ν → Surjective r → (∃ k : KA l₀ →+* KA l₁, IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k ∧ r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k ∧ β₁.comp b = k.comp β₀) → ∀ (r₀ : (Xo l₀).X ≅ (Xo l₀).X) (ν₀ : SABMap (Xo l₀).univ.t (Xo l₀).univ.t r₀.hom) (g : D.La →ₗ[𝓞 E] D.La), r₀.hom ≫ (Xo l₀).s = (Xo l₀).s → (∀ x, ((Xo l₀).univ.eta (g x)).left ≫ ν₀.φ = r₀.hom ≫ ((Xo l₀).univ.eta x).left) → C.ExtendsAut r₀ ν₀ := by
  first | exact @GlobalTheory.Models.extendsAut_of_above | exact GlobalTheory.Models.extendsAut_of_above | (intros; apply GlobalTheory.Models.extendsAut_of_above <;> assumption)
end
