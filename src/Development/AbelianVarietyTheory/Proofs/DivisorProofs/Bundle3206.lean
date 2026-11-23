module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3090
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralLinearOfDensityEqSum
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1492
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle191
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TopSelfEqLengthOfSmooth
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3151
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam

theorem exists_secT_weight_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (a : D.P.A ⟶ D.P.A) (N : ℕ) (σ₀ : LB.Sec (LB.LinComb D.P.L (K := Fin 2) ![𝟙 D.P.A.left, a.left] ![(N : ℤ), -1])) (β : D.X), β = 0 → ∃ s : SecT D a N (-1) β, ∀ (Z : Scheme.{0}) (x : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J → sval s x z J = sval σ₀ x z J := by
  intro R _ _ D a N σ₀ β hβ
  subst hβ
  have hc : (toUnit D.P.A ≫ D.c 0) = (1 : D.P.A ⟶ D.P.A) := GlobalTheory.CoordToExt.c_zero D D.P.A
  have h1 : (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c 0)).left = 𝟙 D.P.A.left := by
    rw [hc]
    have e : padd D.P.A (𝟙 D.P.A) (1 : D.P.A ⟶ D.P.A) = 𝟙 D.P.A * 1 := rfl
    rw [e, _root_.mul_one]
    rfl
  have h2 : (toUnit D.P.A ≫ D.c 0).left = (toUnit D.P.A ≫ η[D.P.A]).left := by
    rw [hc]
    rfl
  obtain ⟨d, hd⟩ := GlobalTheory.exists_sec_relation_defect D.P.A.left D.P.A.left D.P.A.left D.P.L D.P.isLB _ _ _
    ![𝟙 D.P.A.left, a.left] ![(N : ℤ), -1] (tφ D a 0) (tε N (-1)) _ _ (𝟙 _) σ₀
    (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.secZero _) (LB.oneGen D.P.L) (-1) 0 GlobalTheory.CoordToExt.isGen_one
    (fun U _ f => by
      simp only [tφ, tε, h1, h2, Fin.prod_univ_five, Fin.prod_univ_two, Fintype.prod_sum_type,
        Sum.elim_inl, Sum.elim_inr, Category.id_comp, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]
      simp
      group)
  refine ⟨d, fun Z x z J hJ => ?_⟩
  have k0 : gs x z ⊤ (0 : Γ(D.P.A.left, ⊤)) = 0 := by
    rw [gs_eq x z ⊤ (by simp)]
    first
      | (rw [map_zero, map_zero]; done)
      | simp [map_zero]
  have k1 : gs x z ⊤ (-1 : Γ(D.P.A.left, ⊤)) = -1 := by
    rw [gs_eq x z ⊤ (by simp)]
    first
      | (rw [map_neg, map_one, map_neg, map_one]; done)
      | simp [map_neg, map_one]
  rw [hd Z x z J hJ, val_one, k0, k1, Category.comp_id]
  simp

theorem exists_terms : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∀ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])), ∃ (s₀ : SecT D.toPre a N (-1) 0) (s : ∀ ν, SecT D.toPre a N (-1) (shift h h' N (-1) ν)), (∀ ν, TRel h ν s₀ (s ν)) ∧ Small (maximalIdeal R) s ∧ (∀ ν, ν ≠ 0 → Van (maximalIdeal R) (s ν) 0) ∧ (∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (s 0) x z J = sval σ₀ x z J) := by
  intro R _ _ _ hB D a a' h h' hE N hN hP σ₀
  obtain ⟨r, g, hg, hr, hfin, hval⟩ := GlobalTheory.MumInt.main R hB D a a' h h' hE N hN hP
  obtain ⟨s₀, hs₀⟩ := exists_secT_weight_zero R D.toPre a N σ₀ 0 rfl
  have h0 : shift h h' (N : ℤ) (-1) (0 : D.toPre.X) = 0 := by simp [shift]
  obtain ⟨z₀, hz₀⟩ := exists_secT_weight_zero R D.toPre a N σ₀ _ h0
  have key : ∀ ν, ∃ t : SecT D.toPre a N (-1) (shift h h' N (-1) ν), TRel h ν s₀ t ∧
      ∀ e : ℕ, r ν ∈ maximalIdeal R ^ (e + 1) → Van (maximalIdeal R) t e := by
    intro ν
    obtain ⟨u₀, hu₀, hfac⟩ := GlobalTheory.T.exists_normalised_twistedGenerator_of_factor R hB D a a' h h' hE N hN r g hg hval ν
    exact GlobalTheory.T.exists_mumfordTerm_translate_normalisedGenerator R D a h h' N s₀ ν u₀ hu₀ (r ν) hfac
  choose t ht using key
  have hz : TRel h 0 s₀ z₀ :=
    GlobalTheory.T.twisted_section_related_at_zero_shift R hB D a a' h h' hE N hN s₀ z₀ fun Z x z J hJ => (hz₀ Z x z J hJ).trans (hs₀ Z x z J hJ).symm
  classical
  let s : ∀ ν, SecT D.toPre a N (-1) (shift h h' N (-1) ν) := fun ν =>
    if hν : ν = 0 then hν.symm ▸ z₀ else t ν
  have hs0 : s 0 = z₀ := dif_pos rfl
  have hsν : ∀ ν, ν ≠ 0 → s ν = t ν := fun ν hν => dif_neg hν
  refine ⟨s₀, s, fun ν => ?_, fun e => ?_, fun ν hν => ?_, fun Z x z J hJ => ?_⟩
  · by_cases hν : ν = 0
    · subst hν
      rw [hs0]
      exact hz
    · rw [hsν ν hν]
      exact (ht ν).1
  · refine ((hfin (e + 1)).insert 0).subset fun ν hν => ?_
    by_cases h0' : ν = 0
    · exact Or.inl h0'
    · refine Or.inr fun hm => hν ?_
      rw [hsν ν h0']
      exact (ht ν).2 e hm
  · rw [hsν ν hν]
    exact (ht ν).2 0 (by rw [zero_add, pow_one]; exact hr ν hν)
  · rw [hs0]
    exact hz₀ Z x z J hJ

end GlobalTheory.TwFam
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.CycPush

theorem isProjOver_comp {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsProjOver p)
    (i : Z ⟶ X) [IsClosedImmersion i] : IsProjOver (i ≫ p) := by
  obtain ⟨N, j, hj, rfl⟩ := hp
  exact ⟨N, i ≫ j, inferInstance, by rw [Category.assoc]⟩

theorem pull_congr {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
    (A : MLine p σ) {a b : Y ⟶ X} (hab : a = b) (ha : a ≫ p = q) (hb : b ≫ p = q) :
    A.pull a ha = A.pull b hb := by
  subst hab; rfl

theorem dim_le_of_dominant : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → ∀ n : ℕ, topologicalKrullDim Y = n → ∃ m : ℕ, m ≤ n ∧ topologicalKrullDim X = m := by
  intro F _ W M _ _ p q hp hq f hπ hη n hM
  obtain ⟨N, i, hi, hcomp⟩ := hp
  obtain ⟨N', j, hj, hcomp'⟩ := hq
  haveI : IsProper (PSpace.str F N) := isProper_str F N
  haveI : IsProper (PSpace.str F N') := isProper_str F N'
  haveI : IsProper p := by rw [← hcomp]; infer_instance
  haveI : IsProper (f ≫ p) := by rw [hπ, ← hcomp']; infer_instance
  haveI : IsProper f := IsProper.of_comp f p
  have hf : LocallyOfFiniteType f := inferInstance
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint W)) isOpen_univ
  have hV : IsAffineOpen V := hV
  have hx : f (genericPoint M) ∈ V := hη ▸ hxV
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, hUV⟩ := M.isBasis_affineOpens.exists_subset_of_mem_open
    (show genericPoint M ∈ f ⁻¹ᵁ V from hx) (f ⁻¹ᵁ V).isOpen
  have hU : IsAffineOpen U := hU
  haveI : Nonempty V := ⟨⟨_, hx⟩⟩
  haveI : Nonempty U := ⟨⟨_, hy⟩⟩
  have e : U ≤ f ⁻¹ᵁ V := hUV
  let φ := Spec.preimage (hV.fromSpec ≫ p)
  have hφ : Spec.map φ = hV.fromSpec ≫ p := Spec.map_preimage _
  letI : Algebra F Γ(W, V) := φ.hom.toAlgebra
  have hftA : Algebra.FiniteType F Γ(W, V) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  letI : Algebra Γ(W, V) Γ(M, U) := (f.appLE V U e).hom.toAlgebra
  have hftB : Algebra.FiniteType Γ(W, V) Γ(M, U) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f hf ⟨V, hV⟩ ⟨U, hU⟩ e
  letI : Algebra F Γ(M, U) := (φ ≫ f.appLE V U e).hom.toAlgebra
  haveI : IsScalarTower F Γ(W, V) Γ(M, U) := IsScalarTower.of_algebraMap_eq' rfl
  have hftC : Algebra.FiniteType F Γ(M, U) := Algebra.FiniteType.trans hftA hftB
  obtain ⟨d, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq F Γ(W, V)
  have hd : topologicalKrullDim (V : Set W) = d := by
    rw [← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
      hV.range_fromSpec
  rw [GlobalTheory.OpenDim.topologicalKrullDim_open F p V ⟨_, hx⟩] at hd
  have hB : Algebra.trdeg F Γ(M, U) = n := GlobalTheory.GenFinite.trdeg_affineOpen_eq F (f ≫ p) hU ⟨_, hy⟩ n hM
  letI := (W.evaluation V _ hx).hom.toAlgebra
  have nat : f.appLE V U e ≫ M.evaluation U _ hy =
      W.evaluation V _ hx ≫ f.residueFieldMap (genericPoint M) := by
    rw [Scheme.evaluation_naturality f _ hx, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp only [Scheme.evaluation]
    rw [← Category.assoc, TopCat.Presheaf.germ_res]
  haveI := GenFiniteEtale.isFractionRing_eval W hV hη hx
  have hinj : Function.Injective (IsScalarTower.toAlgHom F Γ(W, V) Γ(M, U)) := by
    have h₃ : Function.Injective (f.appLE V U e ≫ M.evaluation U _ hy).hom := by
      rw [nat]
      exact (f.residueFieldMap (genericPoint M)).hom.injective.comp
        (IsFractionRing.injective Γ(W, V) (W.residueField (f (genericPoint M))))
    exact Function.Injective.of_comp (f := (M.evaluation U _ hy).hom) h₃
  have hle := trdeg_le_of_injective _ hinj
  rw [h₂, hB] at hle
  exact ⟨d, by exact_mod_cast hle, hd⟩

theorem cycInt_pull : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (e : ℕ) (L : Fin e → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → ∀ w : Y, topologicalKrullDim (closure ({w} : Set Y)) = e → (topologicalKrullDim (closure ({π w} : Set X)) = e → cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = π.residueDegree w * cycInt L f (π w)) ∧ (topologicalKrullDim (closure ({π w} : Set X)) ≠ e → cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = 0) := by
  intro F _ X Y p q σ hp hq π hπ e L f hf w hw
  obtain ⟨hIw, hgw, hdw, -⟩ := GlobalTheory.ClosFacts.clos_facts Y w
  obtain ⟨hIx, hgx, hdx, hfac⟩ := GlobalTheory.ClosFacts.clos_facts X (π w)
  have hη : (closι w ≫ π) (genericPoint (clos w)) = π w := by
    rw [Scheme.Hom.comp_apply, hgw]
  obtain ⟨g, hg, hgg, hgdeg, -⟩ := hfac (clos w) (closι w ≫ π) hη
  have hpX : IsProjOver (closι (π w) ≫ p) := isProjOver_comp hp _
  have hpY : IsProjOver (closι w ≫ q) := isProjOver_comp hq _
  have hgp : g ≫ closι (π w) ≫ p = closι w ≫ q := by
    rw [← Category.assoc, hg, Category.assoc, hπ]
  have hdY : topologicalKrullDim (clos w) = e := hdw.trans hw
  let L' : Fin e → MLine (closι (π w) ≫ p) σ := fun i => (L i).pull (closι (π w)) rfl
  let f' : CxPts (closι (π w) ≫ p) σ → ℝ := fun y => f (ptMap (closι (π w)) rfl σ y)
  have hf' : Measurable f' := hf.comp (PtsOver.continuous_map _ _ _).measurable

  have h1 : (closι w ≫ π) ≫ p = closι w ≫ q := by rw [Category.assoc, hπ]
  have h2 : (g ≫ closι (π w)) ≫ p = closι w ≫ q := by rw [Category.assoc, hgp]
  have hpart : ∀ ε : ℤˣ, part (fun i => ((L i).pull π hπ).pull (closι w) rfl) ε = part (fun i => (L' i).pull g hgp) ε := by
    intro ε
    have c1 := (GlobalTheory.Mix.isom_calculus F X Y p q σ π hπ).2.2.2.2.2 (clos w) (closι w ≫ q) (closι w) rfl h1
    have c2 := (GlobalTheory.Mix.isom_calculus F X (clos (π w)) p (closι (π w) ≫ p) σ (closι (π w)) rfl).2.2.2.2.2 (clos w)
      (closι w ≫ q) g hgp h2
    have e1 := GlobalTheory.Mix.part_eq_of_isom F (clos w) (closι w ≫ q) σ hpY e _ _ (fun i => c1 (L i)) ε
    have e2 := GlobalTheory.Mix.part_eq_of_isom F (clos w) (closι w ≫ q) σ hpY e _ _ (fun i => c2 (L i)) ε
    rw [e1, e2]
    congr 1
    funext i
    exact pull_congr _ hg.symm _ _
  have hfun : (fun y => (fun y => f (ptMap π hπ σ y)) (ptMap (closι w) rfl σ y)) = fun y => f' (ptMap g hgp σ y) := by
    funext y
    show f _ = f _
    congr 1
    apply Subtype.ext
    simp only [PtsOver.map_val, Category.assoc, hg]
  have hint : cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w =
      Mix.int (fun i => (L' i).pull g hgp) (fun y => f' (ptMap g hgp σ y)) := by
    simp only [cycInt, Mix.int]
    rw [hfun, hpart 1, hpart (-1)]
  refine ⟨fun hX => ?_, fun hX => ?_⟩
  · have hdX : topologicalKrullDim (clos (π w)) = e := hdx.trans hX
    have hne := GlobalTheory.DominantProjDegree.residueDegree_ne_zero_of_map_genericPoint F (clos (π w)) (clos w)
      (closι (π w) ≫ p) (closι w ≫ q) e hpX hpY hdX hdY g hgp hgg
    have hpush := (GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F (clos (π w)) (clos w) (closι (π w) ≫ p) (closι w ≫ q) σ e hpX hdX hpY g hgp
      hgg hne L' f' hf').2
    have hdeg : g.residueDegree (genericPoint (clos w)) = π.residueDegree w := by
      rw [hgdeg, GlobalTheory.CurveDegreesCompare.residueDegree_comp, GlobalTheory.ProperCut.residueDegree_of_isClosedImmersion (closι w),
        mul_one, hgw]
    rw [hint, hpush, hdeg]
    rfl
  · obtain ⟨m, hm, hdX⟩ := dim_le_of_dominant F (clos (π w)) (clos w) (closι (π w) ≫ p) (closι w ≫ q) hpX hpY g hgp
      hgg e hdY
    have hlt : m < e := lt_of_le_of_ne hm fun h => hX (by rw [← hdx, hdX, h])
    have h0 := GlobalTheory.T.mixedChernMeasure_pullback_eq_zero_of_lt_dim F (clos (π w)) (clos w) (closι (π w) ≫ p) (closι w ≫ q) σ e m hlt hpX hdX hpY g hgp hgg L'
    rw [hint]
    simp only [Mix.int, h0, integral_zero_measure, sub_zero]

end GlobalTheory.CycPush
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
open scoped ENNReal
set_option autoImplicit false
noncomputable section

theorem GlobalTheory.Mix.part_eq_zero_off_charts {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) (ε : ℤˣ) {S : Set (CxPts p σ)} (hS : MeasurableSet S)
    (h : ∀ c : AlgChart p σ D, Disjoint c.e.source S) : part L ε S = 0 := by
  have key : part L ε ≤ (part L ε).restrict Sᶜ := iSup_le fun c => by
    have e : chartMeas c.e (fun y => ENNReal.ofReal ((ε : ℤ) * dens L c y)) S = 0 := by
      rw [chartMeas_apply _ _ hS, (h c).inter_eq, image_empty, Measure.restrict_empty,
        lintegral_zero_measure]
    rw [← Measure.restrict_eq_self_of_ae_mem (s := Sᶜ) (compl_mem_ae_iff.2 e)]
    exact Measure.restrict_mono le_rfl (le_iSup (fun c : AlgChart p σ D =>
      chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * dens L c y)) c)
  refine le_antisymm ((key S).trans_eq ?_) zero_le
  rw [Measure.restrict_apply hS, inter_compl_self, measure_empty]

theorem GlobalTheory.Mix.sum_int_eq_zero_of_dens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (J : Type) [Fintype J] (a : J → ℝ) (L : J → Fin D → MLine p σ), (∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ∑ i, a i * dens (L i) c y = 0) → ∀ f : CxPts p σ → ℝ, (∀ i, Intg (L i) f) → ∑ i, a i * Mix.int (L i) f = 0 := by
  intro k _ X p σ _ D J _ a N hlin g hint
  classical
  set P : J → ℤˣ → Measure (CxPts p σ) := fun j ε => part (N j) ε with hPdef
  let ap : J → ℝ := fun j => max (a j) 0
  let an : J → ℝ := fun j => max (-a j) 0
  let μ : (J → ℝ) → (J → ℝ) → Measure (CxPts p σ) := fun u w =>
    ∑ j, (ENNReal.ofReal (u j) • P j 1 + ENNReal.ofReal (w j) • P j (-1))

  have hcont : ∀ j (c : AlgChart p σ D), ContinuousOn (fun v => dens (N j) c (c.e.symm v)) c.e.target :=
    fun j c => (GlobalTheory.T.continuousOn_mixedChernFormDensityInChart k X p σ D (N j) c).comp c.e.continuousOn_symm c.e.mapsTo_symm

  have hchart : ∀ (u w : J → ℝ) (c : AlgChart p σ D) (A : Set (CxPts p σ)), MeasurableSet A → A ⊆ c.e.source →
      μ u w A = ∫⁻ v in c.e '' A, ∑ j, (ENNReal.ofReal (u j) * ENNReal.ofReal (1 * dens (N j) c (c.e.symm v)) +
        ENNReal.ofReal (w j) * ENNReal.ofReal (-1 * dens (N j) c (c.e.symm v))) := by
    intro u w c A hA hAc
    have hsub : c.e '' A ⊆ c.e.target := fun _ ⟨y, hy, e⟩ => e ▸ c.e.map_source (hAc hy)
    have hm : ∀ j (s : ℝ), AEMeasurable (fun v => ENNReal.ofReal (s * dens (N j) c (c.e.symm v)))
        (volume.restrict (c.e '' A)) := fun j s =>
      ((((hcont j c).aemeasurable c.e.open_target.measurableSet).const_mul s).ennreal_ofReal).mono_measure
        (Measure.restrict_mono hsub le_rfl)
    have hP : ∀ j (ε : ℤˣ), P j ε A = ∫⁻ v in c.e '' A, ENNReal.ofReal ((ε : ℤ) * dens (N j) c (c.e.symm v)) :=
      fun j ε => GlobalTheory.T.mixedChernFormSignedPartMeasure_chart_apply k X p σ D (N j) ε c A hA hAc
    have hm2 : ∀ j ∈ (Finset.univ : Finset J), AEMeasurable (fun v =>
        ENNReal.ofReal (u j) * ENNReal.ofReal (1 * dens (N j) c (c.e.symm v)) +
        ENNReal.ofReal (w j) * ENNReal.ofReal (-1 * dens (N j) c (c.e.symm v))) (volume.restrict (c.e '' A)) :=
      fun j _ => ((hm j 1).const_mul _).add ((hm j (-1)).const_mul _)
    rw [lintegral_finsetSum' _ hm2]
    simp only [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [lintegral_add_left' ((hm j 1).const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hP, hP]
    simp

  set U : Set (CxPts p σ) := ⋃ c : AlgChart p σ D, c.e.source with hUdef
  have hUo : IsOpen U := isOpen_iUnion fun c => c.e.open_source
  have hzero : ∀ u w : J → ℝ, μ u w Uᶜ = 0 := by
    intro u w
    have h0 : ∀ j (ε : ℤˣ), P j ε Uᶜ = 0 := fun j ε =>
      GlobalTheory.Mix.part_eq_zero_off_charts (N j) ε hUo.measurableSet.compl fun c =>
        Set.disjoint_compl_right_iff_subset.2 (Set.subset_iUnion (fun c : AlgChart p σ D => c.e.source) c)
    simp [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.add_apply, Measure.smul_apply, h0]

  have hbal : μ ap an = μ an ap := by
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable (fun c : AlgChart p σ D => c.e.source)
      fun c => c.e.open_source
    let s : Option (AlgChart p σ D) → Set (CxPts p σ) := fun o => o.elim Uᶜ fun c => c.e.source
    refine Measure.ext_of_biUnion_eq_univ (S := insert none (some '' T)) (s := s) ((hTc.image _).insert _) ?_ ?_
    · refine Set.eq_univ_of_forall fun y => ?_
      by_cases hy : y ∈ U
      · rw [hUdef, ← hT] at hy
        obtain ⟨c, hc, hyc⟩ := Set.mem_iUnion₂.1 hy
        exact Set.mem_iUnion₂.2 ⟨some c, Set.mem_insert_of_mem _ ⟨c, hc, rfl⟩, hyc⟩
      · exact Set.mem_iUnion₂.2 ⟨none, Set.mem_insert _ _, hy⟩
    · rintro (_ | c) -
      · show (μ ap an).restrict Uᶜ = (μ an ap).restrict Uᶜ
        rw [Measure.restrict_eq_zero.2 (hzero _ _), Measure.restrict_eq_zero.2 (hzero _ _)]
      · show (μ ap an).restrict c.e.source = (μ an ap).restrict c.e.source
        ext B hB
        have hBs := hB.inter c.e.open_source.measurableSet
        rw [Measure.restrict_apply hB, Measure.restrict_apply hB, hchart _ _ c _ hBs Set.inter_subset_right,
          hchart _ _ c _ hBs Set.inter_subset_right]
        refine setLIntegral_congr_fun (GlobalTheory.ChartGlue.measurableSet_image _ hBs Set.inter_subset_right) fun v hv => ?_
        obtain ⟨y, hy, rfl⟩ := hv
        have h0 := hlin c (c.e.symm (c.e y)) (c.e.map_target (c.e.map_source hy.2))
        have := GlobalTheory.GoodMetric.ChernLin.ofReal_balance a fun j => dens (N j) c (c.e.symm (c.e y))
        rw [h0, mul_zero, mul_zero, ENNReal.ofReal_zero, zero_add, zero_add] at this
        exact this.symm

  have hI : ∀ u w : J → ℝ, (∀ j, 0 ≤ u j) → (∀ j, 0 ≤ w j) → ∫ y, g y ∂μ u w =
      ∑ j, (u j * ∫ y, g y ∂P j 1 + w j * ∫ y, g y ∂P j (-1)) := by
    intro u w hu hw
    simp only [μ]
    rw [integral_finsetSum_measure fun j _ => ((hint j).1.smul_measure ENNReal.ofReal_ne_top).add_measure
      ((hint j).2.smul_measure ENNReal.ofReal_ne_top)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_add_measure ((hint j).1.smul_measure ENNReal.ofReal_ne_top)
      ((hint j).2.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
      ENNReal.toReal_ofReal (hu j), ENNReal.toReal_ofReal (hw j), smul_eq_mul, smul_eq_mul]
  have e := congrArg (fun m : Measure (CxPts p σ) => ∫ y, g y ∂m) hbal
  rw [hI _ _ (fun j => le_max_right _ _) (fun j => le_max_right _ _),
    hI _ _ (fun j => le_max_right _ _) (fun j => le_max_right _ _)] at e
  have key : ∑ j, a j * Mix.int (N j) g =
      ∑ j, (ap j * ∫ y, g y ∂P j 1 + an j * ∫ y, g y ∂P j (-1)) -
      ∑ j, (an j * ∫ y, g y ∂P j 1 + ap j * ∫ y, g y ∂P j (-1)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have ha : ap j - an j = a j := GlobalTheory.GoodMetric.ChernLin.max_sub_max_neg (a j)
    rw [Mix.int]
    simp only [P]
    linear_combination (-(∫ y, g y ∂part (N j) 1) + ∫ y, g y ∂part (N j) (-1)) * ha
  rw [key, e, sub_self]
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixFin

theorem finite_and_intg : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∀ (L : Fin D → MLine p σ), (∀ ε : ℤˣ, IsFiniteMeasure (part L ε)) ∧ ∀ f : CxPts p σ → ℝ, Continuous f → Intg L f := by
  intro hP F _ X _ _ p σ D hX hdim L
  haveI : CharZero F := RingHom.charZero σ
  obtain ⟨Y, hY, π, hsm, hproj, -, hgen, hdeg, -⟩ :=
    GlobalTheory.T.exists_logResolution_projective_of_principalisation hP F X p D hX hdim ⊥ (fun h => by rwa [← SetLike.mem_coe, Closeds.coe_bot] at h)
  haveI := hY
  haveI : SmoothOfRelativeDimension D (π ≫ p) := hsm
  haveI := CxPts.compactSpace (p := π ≫ p) σ hproj
  haveI := CxPts.t2Space_cxPts_of_isProjOver (p := π ≫ p) σ hproj
  haveI := CxPts.secondCountableTopology_of_isProjOver (p := π ≫ p) σ hproj
  let R := AnRead.all (π ≫ p) σ D
  have key : ∀ f : CxPts p σ → ℝ, Continuous f → Intg L f := by
    intro f hf
    have hf' : Continuous (fun y => f (ptMap π rfl σ y)) := hf.comp (PtsOver.continuous_map _ _ _)
    have h1 := (GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F Y (π ≫ p) σ D R.finAtlas R.isAlgAtlas_finAtlas
      (fun i => (L i).pull π rfl) _ hf'.measurable).1
    have hI := h1.2 (mIntegrableCont _ _ (fun i => Weight.isPotential_locPot
      ((Weight.isCInf_iff_isSmooth R).1 ((L i).pull π rfl).cInf)) _ hf')
    exact ((GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F X Y p (π ≫ p) σ D hX hdim hproj π rfl hgen
      (by rw [hdeg]; exact one_ne_zero) L f hf.measurable).1).1 hI
  refine ⟨fun ε => ?_, key⟩
  have h := key (fun _ => (1 : ℝ)) continuous_const
  rcases Int.units_eq_one_or ε with rfl | rfl
  · exact (integrable_const_iff.1 h.1).resolve_left one_ne_zero
  · exact (integrable_const_iff.1 h.2).resolve_left one_ne_zero

end GlobalTheory.MixFin
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaConstants_two_levels_same_scale_at_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (y : Sp (FractionRing V) ⟶ Xo.XF c) (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing V →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : V) → Odd m' → 3 ≤ m' → IsUnit (m' : V) → HasTh₂ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m m' (spMap io ≫ y ≫ pullback.fst _ _) d d' → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d' b / a) := by
  first | exact @GlobalTheory.UMin.CmpTrait.cmp_trait | exact GlobalTheory.UMin.CmpTrait.cmp_trait | (intros; apply GlobalTheory.UMin.CmpTrait.cmp_trait <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_section_of_extends_over_complete_dvrs : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → IsSemiAbelian G → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (θ : SecAt G L (spMap (algebraMap R (FractionRing R)) ≫ χ)), (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (φ : R →+* V) (φK : FractionRing R →+* FractionRing V) (h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ), φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ → ∃ σ : SecAt G L (spMap φ ≫ χ), SecM.ofSec G (SecAt.pull G L σ (algebraMap V (FractionRing V))) = SecM.ofSec G (h ▸ SecAt.pull G L θ φK)) → ∃ σ : SecAt G L χ, SecM.ofSec G (SecAt.pull G L σ (algebraMap R (FractionRing R))) = SecM.ofSec G θ := by
  first | exact @GlobalTheory.UMin.SecExtend.exists_sec_of_extends | exact GlobalTheory.UMin.SecExtend.exists_sec_of_extends | (intros; apply GlobalTheory.UMin.SecExtend.exists_sec_of_extends <;> assumption)
end
