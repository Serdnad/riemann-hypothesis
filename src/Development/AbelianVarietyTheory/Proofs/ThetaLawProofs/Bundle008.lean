module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KoszulExactOfGradedRegular
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Mathlib.CategoryTheory.MorphismProperty.Descent
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

section

open GlobalTheory.KeyKa

theorem _root_.GlobalTheory.T.koszul_exact_inl_nonempty_of_graded_regular : ∀ (K : Type) [CommRing K] (g : ℕ) (N : ℕ → ℕ) (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) K), (∀ i i' j, j + 2 ≤ g → m i j (j + 1) * m i' (j + 1) (j + 2) = m i' j (j + 1) * m i (j + 1) (j + 2)) → (∀ (i : Fin g) (j : ℕ) (y : Fin (N (j + 1)) → K), j + 1 + i ≤ g → (m i j (j + 1)).mulVec y ∈ (⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (m i' j (j + 1)).mulVecLin) → y ∈ ⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (m i' (j + 1) (j + 2)).mulVecLin) → ∀ v : KIx g 0 N → K, (kosD m (fun _ => 0)).mulVec v = 0 → ∃ w : KIx g 0 N → K, ∀ p : (Σ I : Finset (Fin g), Fin (N I.card)), p.1 ≠ ∅ → v (.inl p) = (kosD m (fun _ => 0)).mulVec w (.inl p) := by
  first | exact @GlobalTheory.KeyKa.KosGr.koszul_exact_of_graded_regular | exact GlobalTheory.KeyKa.KosGr.koszul_exact_of_graded_regular | (intros; apply GlobalTheory.KeyKa.KosGr.koszul_exact_of_graded_regular <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyPow

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.WeierstrassCurve

theorem exists_mem_coordOpen_two {R : Type} [CommRing R] (W : WeierstrassCurve R) (s : Sp R) :
    ∃ x : scheme W, toSpec W x = s ∧ x ∈ coordOpen W 2 := by
  have : Module.Finite (Polynomial R) W.toAffine.CoordinateRing :=
    .of_basis (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine)
  have : FaithfulSMul (Polynomial R) W.toAffine.CoordinateRing :=
    ⟨fun {p q} h => by
      have e := congrArg (fun a => (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine).repr a 0)
        (h (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine 0))
      simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul] at e
      exact (mul_one p).symm.trans (e.trans (mul_one q))⟩
  obtain ⟨y, hy⟩ := Algebra.IsIntegral.comap_surjective (Polynomial R) W.toAffine.CoordinateRing
    (PrimeSpectrum.comap (Polynomial.evalRingHom 0) s)
  refine ⟨chartZ W y, ?_, (opensRange_chartZ W).le ⟨y, rfl⟩⟩
  refine (Scheme.Hom.comp_apply (chartZ W) (toSpec W) y).symm.trans ?_
  rw [chartZ_toSpec]
  change PrimeSpectrum.comap (algebraMap R W.toAffine.CoordinateRing) y = s
  rw [IsScalarTower.algebraMap_eq R (Polynomial R), PrimeSpectrum.comap_comp_apply, hy]
  have e : (Polynomial.evalRingHom (0 : R)).comp (algebraMap R (Polynomial R)) = RingHom.id R := by
    ext; simp
  exact congrArg (fun f => PrimeSpectrum.comap f s) e

end GlobalTheory.KeyPow
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.isGrpPullback_of_fpqc (S S' S'' : Scheme.{0}) (a : S' ⟶ S) (π : S'' ⟶ S') (G : Over S) [GrpObj G]
    (G' : Over S') [GrpObj G'] (G'' : Over S'') [GrpObj G''] (φ : G''.left ⟶ G'.left) (ψ : G'.left ⟶ G.left)
    (hf : Flat π) (hs : Surjective π) (hq : QuasiCompact π) (h₁ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G'' G' π φ)
    (h₂ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G'' G (π ≫ a) (φ ≫ ψ)) (w : ψ ≫ G.hom = G'.hom ≫ a) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G a ψ := by
  refine ⟨?_, ?_⟩
  · let c : G'.left ⟶ pullback G.hom a := pullback.lift ψ G'.hom w
    have hc₁ : c ≫ pullback.fst G.hom a = ψ := pullback.lift_fst _ _ _
    have hc₂ : c ≫ pullback.snd G.hom a = G'.hom := pullback.lift_snd _ _ _
    have hlow : IsPullback (φ ≫ c) G''.hom (pullback.snd G.hom a) π :=
      (IsPullback.paste_horiz_iff (IsPullback.of_hasPullback G.hom a)
        (by rw [Category.assoc, hc₂, h₁.1.w])).1 (by rw [Category.assoc, hc₁]; exact h₂.1)
    have hcov : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (φ ≫ c) :=
      ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) hlow.flip hs,
        MorphismProperty.of_isPullback (P := @Flat) hlow.flip hf⟩,
        MorphismProperty.of_isPullback (P := @QuasiCompact) hlow.flip hq⟩
    have hsq : IsPullback (𝟙 G''.left) φ (φ ≫ c) c :=
      ((IsPullback.paste_vert_iff (h₁₁ := φ) (v₁₁ := 𝟙 _) (v₁₂ := c) hlow (by simp)).1
        (by rw [Category.id_comp, hc₂]; exact h₁.1)).flip
    have hc : IsIso c :=
      MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms _)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsq hcov (inferInstanceAs (IsIso (𝟙 G''.left)))
    exact IsPullback.of_iso (IsPullback.of_hasPullback G.hom a) (asIso c).symm (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simp [IsIso.eq_inv_comp, hc₁]) (by simp [IsIso.eq_inv_comp, hc₂])
      (by simp) (by simp)
  · intro T x y x₀ y₀ hx hy
    haveI := hf
    haveI := hs
    let p : pullback T.hom π ⟶ T.left := pullback.fst T.hom π
    haveI : Epi p := Flat.epi_of_flat_of_surjective _
    let T'' : Over S'' := Over.mk (pullback.snd T.hom π)
    let q : Over.mk (T''.hom ≫ π) ⟶ T := Over.homMk p (by simp [p, T'', pullback.condition])
    let q₀ : Over.mk (T''.hom ≫ π ≫ a) ⟶ Over.mk (T.hom ≫ a) :=
      Over.homMk p (by simp [p, T'', pullback.condition_assoc])
    let x'' : T'' ⟶ G'' := Over.homMk (h₁.1.lift (p ≫ x.left) T''.hom
      (by simp [p, T'', pullback.condition])) (by simp [T''])
    let y'' : T'' ⟶ G'' := Over.homMk (h₁.1.lift (p ≫ y.left) T''.hom
      (by simp [p, T'', pullback.condition])) (by simp [T''])
    have hx'' : x''.left ≫ φ = p ≫ x.left := by simp [x'']
    have hy'' : y''.left ≫ φ = p ≫ y.left := by simp [y'']
    have k₁ := h₁.2 T'' x'' y'' (q ≫ x) (q ≫ y) (by simp [q, hx'']) (by simp [q, hy''])
    have k₂ := h₂.2 T'' x'' y'' (q₀ ≫ x₀) (q₀ ≫ y₀)
      (by simp only [Over.comp_left, Over.homMk_left, q₀]; rw [hx, reassoc_of% hx''])
      (by simp only [Over.comp_left, Over.homMk_left, q₀]; rw [hy, reassoc_of% hy''])
    rw [← cancel_epi p]
    calc p ≫ (x₀ * y₀).left = (q₀ ≫ (x₀ * y₀)).left := by simp [q₀]
      _ = ((q₀ ≫ x₀) * (q₀ ≫ y₀)).left := by rw [comp_mul]
      _ = (x'' * y'').left ≫ φ ≫ ψ := k₂
      _ = ((q ≫ x) * (q ≫ y)).left ≫ ψ := by rw [k₁, Category.assoc]
      _ = (q ≫ (x * y)).left ≫ ψ := by rw [comp_mul]
      _ = p ≫ (x * y).left ≫ ψ := by simp [q]

end GlobalTheory
end

section

namespace GlobalTheory

open MvPolynomial

theorem det_ne_zero_of_generic_linear_forms_vanish :
    ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (F : IntermediateField k K) (g N : ℕ)
    (T : Fin g × Fin N → K) (e : Fin N → K) (D : Fin g → Fin N → K),
    AlgebraicIndependent k T → Algebra.trdeg k F ≤ g → (∀ j, e j ∈ F) → (∀ a j, D a j ∈ F) →
    (∃ j, e j ≠ 0) →
    (∃ c : Fin g → Fin N → K, (∀ i, ∑ j, c i j * e j = 0) ∧
      (Matrix.of fun i a => ∑ j, c i j * D a j).det ≠ 0) →
    (∀ i, ∑ j, T (i, j) * e j = 0) → (Matrix.of fun i a => ∑ j, T (i, j) * D a j).det ≠ 0 := by
  intro k K _ _ _ F g N T e D hT hF he hD ⟨j0, hj0⟩ ⟨c, hc, hcd⟩ hTe
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by have := j0.pos; omega⟩
  let η : Fin (M + 1) → F := fun j => ⟨e j / e j0, F.div_mem (he j) (he j0)⟩
  let D' : Fin g → Fin (M + 1) → F := fun a j => ⟨D a j, hD a j⟩
  let b : Fin g × Fin (M + 1) → MvPolynomial (Fin g × Fin M) F := fun p =>
    Fin.insertNth (α := fun _ => MvPolynomial (Fin g × Fin M) F) j0
      (-∑ l : Fin M, X (p.1, l) * C (η (j0.succAbove l))) (fun l => X (p.1, l)) p.2
  let χ : (Fin g × Fin (M + 1) → K) → (MvPolynomial (Fin g × Fin M) F →ₐ[F] K) := fun v =>
    aeval fun q => v (q.1, j0.succAbove q.2)
  have hb : ∀ v : Fin g × Fin (M + 1) → K, (∀ i, ∑ j, v (i, j) * e j = 0) →
      ∀ p, χ v (b p) = v p := by
    rintro v hv ⟨i, j⟩
    refine Fin.succAboveCases j0 ?_ (fun l => ?_) j
    · have h1 := hv i
      rw [Fin.sum_univ_succAbove _ j0] at h1
      have h2 : v (i, j0) =
          -∑ l : Fin M, v (i, j0.succAbove l) * (e (j0.succAbove l) / e j0) := by
        simp only [← mul_div_assoc, ← Finset.sum_div]
        field_simp
        linear_combination h1
      rw [h2]
      simp [b, χ, η]
    · simp [b, χ]
  let Δ : MvPolynomial (Fin g × Fin M) F :=
    (Matrix.of fun i a => ∑ j, b (i, j) * C (D' a j)).det
  have hΔ : ∀ v : Fin g × Fin (M + 1) → K, (∀ i, ∑ j, v (i, j) * e j = 0) →
      χ v Δ = (Matrix.of fun i a => ∑ j, v (i, j) * D a j).det := by
    intro v hv
    rw [AlgHom.map_det]
    congr 1
    ext i a

    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
    hb v hv]
    simp [χ, D']
  have hΔ0 : Δ ≠ 0 := by
    intro h
    apply hcd
    rw [← hΔ (fun p => c p.1 p.2) hc, h, map_zero]
  have htr : Algebra.trdeg k (MvPolynomial (Fin g × Fin M) F) ≤
      Cardinal.mk (Fin g × Fin (M + 1)) := by
    have : FaithfulSMul F (MvPolynomial (Fin g × Fin M) F) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (MvPolynomial.C_injective _ _)
    rw [← trdeg_add_eq k F, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id,
      Cardinal.mk_fintype, Cardinal.mk_fintype]
    refine (add_le_add_left hF _).trans ?_
    norm_cast
    simp only [Fintype.card_prod, Fintype.card_fin]
    apply le_of_eq
    ring
  have hχ : Function.Injective (χ T).toRingHom := by
    refine injective_of_injective_comp_aeval_of_trdeg_le (k := k) b htr _ ?_
    have : (fun q : MvPolynomial (Fin g × Fin (M + 1)) k => (χ T).toRingHom (aeval b q)) =
        aeval T := by
      have h3 : ((χ T).restrictScalars k).comp (aeval b) = aeval T := by
        apply MvPolynomial.algHom_ext
        intro p
        simp [hb T hTe]
      funext q
      exact DFunLike.congr_fun h3 q
    rw [this]
    exact hT
  rw [← hΔ T hTe]
  intro h
  exact hΔ0 (hχ (by simpa using h))

end GlobalTheory
end

section

noncomputable section

open Complex Matrix

namespace GlobalTheory

open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end General

variable {g : ℕ}


open Complex Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.isSymm_phSym (x : Matrix (Fin g) (Fin g) ℂ) : (_root_.ReciprocityTheory.ChartRestriction.G.Key.phSym x).IsSymm := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym
  ext i j
  simp only [transpose_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring


open Complex Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.phSym_eq_self_of_isSymm {x : Matrix (Fin g) (Fin g) ℂ} (hx : x.IsSymm) :
    _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym x = x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym
  rw [hx.eq, ← two_smul ℂ x, smul_smul]
  norm_num


open Complex Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.differentiable_phSym_coords :
    Differentiable ℂ (fun x : Fin g → Fin g → ℂ =>
      (Matrix.of.symm (_root_.ReciprocityTheory.ChartRestriction.G.Key.phSym (Matrix.of x)) : Fin g → Fin g → ℂ)) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym
  refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
  simp only [Matrix.of_symm_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.of_apply, smul_eq_mul]
  fun_prop


open Complex Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.isOpen_phDom (g : ℕ) : IsOpen (_root_.ReciprocityTheory.ChartRestriction.G.Key.phDom g) := by
  have hc : Continuous (fun x : Fin g → Fin g → ℂ => _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym (Matrix.of x)) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym; fun_prop
  rw [isOpen_iff_mem_nhds]
  intro x hx
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phDom at hx ⊢
  have hx' : _root_.GlobalTheory.IsSiegel (_root_.ReciprocityTheory.ChartRestriction.G.Key.phSym (Matrix.of x)) := _root_.GlobalTheory.isSiegel_iff_mem_siegelH.2 hx
  have h := hc.continuousAt.eventually hx'.eventually_isSiegel
  filter_upwards [h] with y hy
  exact _root_.GlobalTheory.isSiegel_iff_mem_siegelH.1 (hy (_root_.GlobalTheory.isSymm_phSym _))

open Complex Matrix in
variable {g : ℕ} in
private theorem convex_siegelH (g : ℕ) : Convex ℝ (_root_.ReciprocityTheory.PTheta.SiegelH (Fin g)) := by
  intro A hA B hB a b ha hb hab
  rw [← _root_.GlobalTheory.isSiegel_iff_mem_siegelH] at *
  refine ⟨?_, ?_⟩
  · exact (hA.isSymm.smul a).add (hB.isSymm.smul b)
  · have hm : ((a • A + b • B).map Complex.im) = a • A.map Complex.im + b • B.map Complex.im := by
      ext i j; simp
    rw [hm]
    rcases ha.eq_or_lt with rfl | ha'
    · simp at hab; subst hab; simpa using hB.posDef
    · exact (hA.posDef.smul ha').add_posSemidef (hB.posDef.posSemidef.smul hb)


open Complex Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.convex_phDom (g : ℕ) : Convex ℝ (_root_.ReciprocityTheory.ChartRestriction.G.Key.phDom g) := by
  have hl : IsLinearMap ℝ (fun x : Fin g → Fin g → ℂ => _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym (Matrix.of x)) := by
    constructor
    · intro x y; unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym; ext i j; simp [Function.swap]; ring
    · intro c x; unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym; ext i j; simp [Function.swap]; ring
  have := (convex_siegelH g).is_linear_preimage hl
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phDom
  exact this


open Complex Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.of_symm_mem_phDom {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g)) :
    (Matrix.of.symm τ : Fin g → Fin g → ℂ) ∈ _root_.ReciprocityTheory.ChartRestriction.G.Key.phDom g := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phDom
  show _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym (Matrix.of (Matrix.of.symm τ)) ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g)
  rw [Equiv.apply_symm_apply,
    _root_.GlobalTheory.phSym_eq_self_of_isSymm (_root_.GlobalTheory.isSiegel_iff_mem_siegelH.2 hτ).isSymm]
  exact hτ

end GlobalTheory
end
end
