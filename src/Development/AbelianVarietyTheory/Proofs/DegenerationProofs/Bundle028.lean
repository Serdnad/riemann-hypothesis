module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle007
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle017
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelHasJacobianOrder
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.Ord

namespace GlobalTheory.SS.Ord

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)} in
private lemma model_isPullback_genericFibre_spMap (M : _root_.GlobalTheory.SS.Model R A) :
    IsPullback M.j A.hom M.Y.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)) := by
  have h := IsPullback.of_hasPullback M.Y.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K))
  refine IsPullback.of_iso h ((Over.forget _).mapIso M.e) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [_root_.GlobalTheory.SS.Model.j, ← Over.comp_left_assoc]
  · have := Over.w M.e.hom
    simpa using this.symm


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] in
theorem _root_.GlobalTheory.SS.Ord.isOpenImmersion_of_extends_id_of_etale :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
      [IsFractionRing R K] (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (M N : _root_.GlobalTheory.SS.Model R A)
      (U : M.Y.left.Opens) (g : U.toScheme ⟶ N.Y.left),
      _root_.GlobalTheory.SS.Extends M N (𝟙 A) U g → Etale g → IsOpenImmersion g := by
  intro R K _ _ _ _ _ _ A M N U g hE _
  haveI := M.smooth
  haveI := M.sep
  haveI := _root_.GlobalTheory.schemeTheoreticallyDominant_fractionField R K
  haveI : IsSeparated (g ≫ N.Y.hom) := by rw [hE.1]; infer_instance
  haveI : IsSeparated g := IsSeparated.of_comp g N.Y.hom
  haveI := FormallyUnramified.isOpenImmersion_diagonal g
  let ψ := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)
  let q := pullback.fst g g ≫ U.ι ≫ M.Y.hom
  let φ := pullback.fst q ψ
  haveI : IsSchemeTheoreticallyDominant φ :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback q ψ).flip
  have hU := ((isPullback_morphismRestrict M.j U).paste_vert
    (model_isPullback_genericFibre_spMap M))
  have hN := model_isPullback_genericFibre_spMap N
  have hs : (φ ≫ pullback.fst g g) ≫ U.ι ≫ M.Y.hom = pullback.snd q ψ ≫ ψ := by
    rw [Category.assoc]
    exact pullback.condition
  have hs' : (φ ≫ pullback.snd g g) ≫ U.ι ≫ M.Y.hom = pullback.snd q ψ ≫ ψ := by
    rw [← hs, ← hE.1]
    simp only [Category.assoc, pullback.condition_assoc]
  have key : ∀ (c : pullback q ψ ⟶ U) (hc : c ≫ U.ι ≫ M.Y.hom = pullback.snd q ψ ≫ ψ),
      (hU.lift c _ hc ≫ (M.j ⁻¹ᵁ U).ι) ≫ N.j = c ≫ g := by
    intro c hc
    have h2 := hE.2
    conv_rhs => rw [← hU.lift_fst c _ hc]
    rw [Category.assoc (hU.lift c _ hc) (M.j ∣_ U) g, h2]
    simp
  have hl : hU.lift _ _ hs ≫ (M.j ⁻¹ᵁ U).ι =
      hU.lift _ _ hs' ≫ (M.j ⁻¹ᵁ U).ι := by
    apply hN.hom_ext
    · rw [key _ hs, key _ hs']
      simp only [Category.assoc, pullback.condition]
    · have e1 := hU.lift_snd _ _ hs
      have e2 := hU.lift_snd _ _ hs'
      simp only [Category.assoc] at e1 e2 ⊢
      rw [e1, e2]
  have hab : φ ≫ pullback.fst g g = φ ≫ pullback.snd g g := by
    rw [← hU.lift_fst _ _ hs, ← hU.lift_fst _ _ hs', (cancel_mono _).1 hl]
  have hφ : φ = (φ ≫ pullback.fst g g) ≫ pullback.diagonal g := by
    apply pullback.hom_ext <;> simp [hab]
  have hrange : Set.range φ ⊆ Set.range (pullback.diagonal g) := by
    rintro _ ⟨z, rfl⟩
    refine ⟨(φ ≫ pullback.fst g g) z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hφ]
  have hclosed : IsClosed (Set.range (pullback.diagonal g)) :=
    (pullback.diagonal g).isClosedEmbedding.isClosed_range
  have huniv : Set.range (pullback.diagonal g) = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (IsDominant.denseRange (f := φ)).closure_eq]
    exact closure_minimal hrange hclosed
  haveI : IsIso (pullback.diagonal g) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _
      (TopologicalSpace.Opens.ext (by simpa using huniv))
  haveI : Mono g := (pullback.isIso_diagonal_iff g).mp inferInstance
  exact IsOpenImmersion.of_flat_of_mono g

end GlobalTheory.SS.Ord
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SaturatedSections

theorem exists_comb {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    {J : Type} {A : J → Type} [∀ j, CommRing (A j)] (φ : ∀ j, W →+* A j) {ϖ : W}
    (hϖ : Irreducible ϖ) (reg : ∀ j (x : A j), φ j ϖ * x = 0 → x = 0)
    {r : ℕ} (s : Fin r → ∀ j, A j)
    (ind : ∀ (c : Fin r → W) (y : ∀ j, A j), (∀ j, φ j ϖ * y j = ∑ i, φ j (c i) * s i j) →
      ∀ i, c i ∈ IsLocalRing.maximalIdeal W) (n : ℕ) :
    ∀ (t : ∀ j, A j) (c : Fin r → W), (∀ j, φ j (ϖ ^ n) * t j = ∑ i, φ j (c i) * s i j) →
      ∃ d : Fin r → W, (∀ i, c i = ϖ ^ n * d i) ∧ ∀ j, t j = ∑ i, φ j (d i) * s i j := by
  induction n with
  | zero =>
    intro t c h
    exact ⟨c, fun i => by simp, fun j => by simpa using h j⟩
  | succ n ih =>
    intro t c h
    have hc := ind c (fun j => φ j (ϖ ^ n) * t j) (fun j => by
      rw [← h j, pow_succ', map_mul, _root_.mul_assoc])
    rw [hϖ.maximalIdeal_eq] at hc
    choose c' hc' using fun i => Ideal.mem_span_singleton'.1 (hc i)
    obtain ⟨d, hd, hd'⟩ := ih t c' (fun j => by
      rw [← sub_eq_zero]
      apply reg j
      rw [mul_sub, ← _root_.mul_assoc, ← map_mul, ← pow_succ', h j, Finset.mul_sum, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hc' i, map_mul]; ring)
    exact ⟨d, fun i => by rw [← hc' i, hd i]; ring, hd'⟩

theorem existsUnique_comb {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    {J : Type} {A : J → Type} [∀ j, CommRing (A j)] (φ : ∀ j, W →+* A j) {ϖ : W}
    (hϖ : Irreducible ϖ) (reg : ∀ j (x : A j), φ j ϖ * x = 0 → x = 0)
    {r : ℕ} (s : Fin r → ∀ j, A j)
    (ind : ∀ (c : Fin r → W) (y : ∀ j, A j), (∀ j, φ j ϖ * y j = ∑ i, φ j (c i) * s i j) →
      ∀ i, c i ∈ IsLocalRing.maximalIdeal W) (t : ∀ j, A j) (a : W) (c : Fin r → W) (ha : a ≠ 0)
    (h : ∀ j, φ j a * t j = ∑ i, φ j (c i) * s i j) :
    ∃! d : Fin r → W, ∀ j, t j = ∑ i, φ j (d i) * s i j := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨d, -, hd⟩ := exists_comb φ hϖ reg s ind n t (fun i => (u⁻¹ : Wˣ) * c i) (fun j => by
    simp only [map_mul, _root_.mul_assoc, ← Finset.mul_sum, ← h j]
    rw [← _root_.mul_assoc (φ j (u⁻¹ : Wˣ)), ← map_mul, Units.inv_mul, map_one,
      _root_.one_mul])
  refine ⟨d, hd, fun d' hd' => ?_⟩
  funext i
  rw [← sub_eq_zero]
  by_contra hne
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  obtain ⟨e, he, -⟩ := exists_comb φ hϖ reg s ind (m + 1) (fun _ => 0) (fun i => d' i - d i)
    (fun j => by
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib, ← hd j, ← hd' j, sub_self,
        MulZeroClass.mul_zero])
  have h1 : ϖ ^ m * (v : W) = ϖ ^ m * (ϖ * e i) := by
    have := he i
    rw [hv] at this
    linear_combination this
  have h2 := mul_left_cancel₀ (pow_ne_zero m hϖ.ne_zero) h1
  exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (h2 ▸ v.isUnit))

noncomputable def cst {W : Type} [CommRing W] {H : Scheme.{0}} (p : H ⟶ Sp W) (U : H.Opens) :
    W →+* Γ(H, U) :=
  (p.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom

theorem cst_eq {W : Type} [CommRing W] {H : Scheme.{0}} (p : H ⟶ Sp W) (U : H.Opens) (a : W) :
    Out.resTop U (Out.scal p a) = cst p U a := rfl


set_option backward.isDefEq.respectTransparency false in
theorem eq_zero_of_cst_mul {W : Type} [CommRing W] [IsDomain W] {H : Scheme.{0}} (p : H ⟶ Sp W)
    [Flat p] (V : H.Opens) {r : W} (hr : r ≠ 0) (a : Γ(H, V)) (h : cst p V r * a = 0) :
    a = 0 := by
  have hr' : (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom r ∈ nonZeroDivisors Γ(Sp W, ⊤) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of W)).symm.commRingCatIsoToRingEquiv
    have : IsDomain Γ(Sp W, ⊤) := e.symm.toMulEquiv.isDomain
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => hr (e.injective ?_)
    rw [map_zero]; exact h0
  refine H.IsSheaf.section_ext fun x hx ↦ ?_
  obtain ⟨_, ⟨V', hV', rfl⟩, hxV, hVV : V' ≤ V⟩ :=
    H.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  refine ⟨V', hVV, hxV, ?_⟩
  have hf : (p.appLE ⊤ V' le_top).hom.Flat := p.flat_appLE (isAffineOpen_top _) hV' le_top
  letI := (p.appLE ⊤ V' le_top).hom.toAlgebra
  have : Module.Flat Γ(Sp W, ⊤) Γ(H, V') := hf
  apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(H, V')) hr'
  have h' := congrArg (H.presheaf.map (homOfLE hVV).op) h
  rw [map_mul, map_zero, cst, RingHom.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_map] at h'
  simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using h'

theorem not_mem_basicOpen_cst {W : Type} [CommRing W] [IsLocalRing W] {H : Scheme.{0}}
    (p : H ⟶ Sp W) (V : H.Opens) {r : W} (hr : r ∈ IsLocalRing.maximalIdeal W) (x : H)
    (hx : p x = IsLocalRing.closedPoint W) : x ∉ H.basicOpen (cst p V r) := by
  rw [← cst_eq, Out.resTop, Scheme.basicOpen_res, Out.scal, ← Scheme.preimage_basicOpen_top,
    basicOpen_eq_of_affine]
  rintro ⟨-, h⟩
  have h' : p x ∈ PrimeSpectrum.basicOpen r := h
  rw [hx] at h'
  exact h' hr

end GlobalTheory.SaturatedSections


open GlobalTheory.SaturatedSections in
theorem GlobalTheory.existsUnique_comb_of_independent_special_fibre : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (H : Scheme.{0}) (p : H ⟶ Sp W) [Flat p] (M : LB H), M.IsLB → ∀ (r : ℕ) (s : Fin r → LB.Sec M), (∀ c : Fin r → W, (∀ (j : M.ι) (x : H), x ∈ M.U j → p x = IsLocalRing.closedPoint W → x ∉ H.basicOpen (∑ i, Out.resTop _ (Out.scal p (c i)) * (s i).f j)) → ∀ i, c i ∈ IsLocalRing.maximalIdeal W) → ∀ t : LB.Sec M, (∃ (a : W) (c : Fin r → W), a ≠ 0 ∧ ∀ j, Out.resTop _ (Out.scal p a) * t.f j = ∑ i, Out.resTop _ (Out.scal p (c i)) * (s i).f j) → ∃! c : Fin r → W, ∀ j, t.f j = ∑ i, Out.resTop _ (Out.scal p (c i)) * (s i).f j := by
  intro W _ _ _ H p _ M _ r s ind t ⟨a, c, ha, h⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  simp only [cst_eq] at ind h ⊢
  refine existsUnique_comb (A := fun j => Γ(H, M.U j)) (fun j => cst p (M.U j)) hϖ
    (fun j x hx => eq_zero_of_cst_mul p _ hϖ.ne_zero x hx) (fun i j => (s i).f j)
    (fun c y hy => ind c fun j x _ hx => ?_) t.f a c ha h
  rw [← hy j, Scheme.basicOpen_mul]
  exact fun h => not_mem_basicOpen_cst p _ hϖ.not_isUnit x hx h.1
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TensorProduct

namespace GlobalTheory

namespace GenericEq

open GenericIso

theorem map_eq_generic (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X : Over (Sp R))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (Sg : Set (Sp R)) (hD : Dense Sg)
    (Y : Over (Sp R)) [IsSeparated Y.hom] (f g : X ⟶ Y)
    (H : ∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧
      (Over.pullback t).map f = (Over.pullback t).map g) :
    (Over.pullback (Out.jK R)).map f = (Over.pullback (Out.jK R)).map g := by
  have : IsClosedImmersion (equalizer.ι f g).left := inferInstance
  have : LocallyOfFiniteType (equalizer f g).hom := by
    rw [← Over.w (equalizer.ι f g)]; infer_instance
  have h := isIso_generic_of_dense_fibres R (equalizer f g) X (equalizer.ι f g) Sg hD
    fun x hx => by
      obtain ⟨K, _, t, ht, e⟩ := H x hx
      refine ⟨K, inferInstance, t, ht, ?_⟩
      rw [← equalizerComparison_comp_π]
      have := equalizer.ι_of_eq e
      infer_instance
  rw [← cancel_epi ((Over.pullback (Out.jK R)).map (equalizer.ι f g)), ← Functor.map_comp,
    ← Functor.map_comp, equalizer.condition]

theorem exists_smul_eq_zero {R A : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A] {D : Set (PrimeSpectrum R)} (hD : Dense D)
    (y : A) (H : ∀ x ∈ D, ∃ (K : Type) (_ : Field K) (_ : Algebra R K),
      x.asIdeal = RingHom.ker (algebraMap R K) ∧ (1 : K) ⊗ₜ[R] y = 0) :
    ∃ a : R, a ≠ 0 ∧ algebraMap R A a * y = 0 := by
  let F := Ideal.Quotient.mkₐ R (Ideal.span {y})
  have hF : Function.Surjective F := Ideal.Quotient.mkₐ_surjective _ _
  obtain ⟨a, ha0, ha⟩ := exists_pow_smul_ker_eq_zero_of_dense F hD fun x hx => by
    obtain ⟨K, _, _, hK, hy⟩ := H x hx
    refine (bijective_residueField F K x hK ⟨?_,
      Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hF⟩).1
    rw [RingHom.injective_iff_ker_eq_bot, Algebra.TensorProduct.lTensor_ker F hF,
      show RingHom.ker F = Ideal.span {y} from Ideal.mk_ker,
      Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_bot]
    exact hy
  obtain ⟨n, hn⟩ := ha y (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self y))
  exact ⟨a ^ n, pow_ne_zero _ ha0, by rw [← Algebra.smul_def]; exact hn⟩

theorem appTop_scal {R : Type} [CommRing R] {Y Z : Scheme.{0}} (q : Z ⟶ Y) (p : Y ⟶ Sp R)
    (a : R) : q.appTop.hom (Out.scal p a) = Out.scal (q ≫ p) a := by
  rfl

theorem exists_scal_mul_chart {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (X : Over (Sp R)) [LocallyOfFiniteType X.hom] {Sg : Set (Sp R)} (hD : Dense Sg)
    (u : Γ(X.left, ⊤))
    (H : ∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧
      (pullback.fst X.hom t).appTop.hom u = 0)
    (A : CommRingCat.{0}) (j : Spec A ⟶ X.left) [IsOpenImmersion j] :
    ∃ a : R, a ≠ 0 ∧ j.appTop.hom (Out.scal X.hom a * u) = 0 := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ X.hom)
  let : Algebra R A := φ.hom.toAlgebra
  have : Algebra.FiniteType R A := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hφ' : Spec.map (CommRingCat.ofHom (algebraMap R A)) = j ≫ X.hom := hφ
  obtain ⟨a, ha0, ha⟩ := exists_smul_eq_zero (R := R) hD
    ((Scheme.ΓSpecIso A).hom.hom (j.appTop.hom u)) fun x hx => by
      obtain ⟨K, _, t, ht, hu⟩ := H x hx
      obtain ⟨ψ, rfl⟩ := Spec.map_surjective t
      let : Algebra R K := ψ.hom.toAlgebra
      refine ⟨K, inferInstance, inferInstance, ?_, ?_⟩
      · have : Spec.map ψ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) = x :=
          ht.le (Set.mem_range_self _)
        rw [← this]
        rfl
      · have w := (isPullback_tensor (R := R) K A).w
        rw [hφ', ← Category.assoc] at w
        have e := congrArg (fun k => k.appTop.hom u) (pullback.lift_fst _ _ w)
        simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at e
        erw [hu, map_zero] at e
        have n := congrArg (fun k => k.hom (j.appTop.hom u)) (Scheme.ΓSpecIso_naturality
          (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
            (R := R) (A := K) (B := A)).toRingHom))
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at n
        erw [← e, map_zero] at n
        exact n.symm
  refine ⟨a, ha0, ?_⟩
  apply (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.injective
  rw [map_zero, ← ha, map_mul, map_mul, appTop_scal, ← hφ]
  congr 1
  have n := congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.ΓSpecIso_naturality φ)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at n
  refine n.trans ?_
  rw [Iso.inv_hom_id_apply]
  rfl

theorem exists_scal_mul_eq_zero (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (X : Over (Sp R)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (Sg : Set (Sp R))
    (hD : Dense Sg) (u : Γ(X.left, ⊤))
    (H : ∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧
      (pullback.fst X.hom t).appTop.hom u = 0) :
    ∃ a : R, a ≠ 0 ∧ Out.scal X.hom a * u = 0 := by
  classical
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let 𝒰 : X.left.OpenCover := X.left.affineCover.finiteSubcover
  have hc : ∀ i : 𝒰.I₀, ∃ a : R, a ≠ 0 ∧ (𝒰.f i).appTop.hom (Out.scal X.hom a * u) = 0 := by
    intro i
    obtain ⟨a, ha0, ha⟩ :=
      exists_scal_mul_chart X hD u H _ ((𝒰.X i).isoSpec.inv ≫ 𝒰.f i)
    refine ⟨a, ha0, ?_⟩
    rw [← (𝒰.X i).isoSpec.hom_inv_id_assoc (𝒰.f i), Scheme.Hom.comp_appTop,
      CommRingCat.hom_comp, RingHom.comp_apply, ha, map_zero]
  choose a ha0 ha using hc
  refine ⟨∏ i, a i, Finset.prod_ne_zero_iff.2 fun i _ => ha0 i,
    Scheme.zero_of_zero_cover _ 𝒰 fun i => ?_⟩
  obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
  have e : Out.scal X.hom (∏ i, a i) * u = Out.scal X.hom b * (Out.scal X.hom (a i) * u) := by
    rw [hb]
    simp only [Out.scal, map_mul]
    ring
  rw [e, map_mul]
  exact mul_eq_zero_of_right _ (ha i)

theorem exists_mem_of_not_mem (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (X : Over (Sp R)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (Sg : Set (Sp R))
    (hD : Dense Sg) (V : X.left.Opens) (H : ∀ x : X.left, X.hom x ∈ Sg → x ∈ V) :
    ∃ a : R, a ≠ 0 ∧ ∀ x : X.left, a ∉ (X.hom x).asIdeal → x ∈ V := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  have hC : Topology.IsConstructible ((V : Set X.left)ᶜ) :=
    (IsCompact.isConstructible (TopologicalSpace.NoetherianSpace.isCompact _) V.isOpen).compl
  obtain ⟨W, ⟨y, hy⟩, -, hW⟩ :=
    exists_isAffineOpen_disjoint_image_of_isConstructible_of_disjoint_dense X.left (Sp R) X.hom
      _ Sg hC hD (Set.disjoint_left.2 (by rintro _ ⟨x, hx, rfl⟩ h; exact hx (H x h)))
  obtain ⟨_, ⟨a, rfl⟩, hya, haW⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hy W.isOpen
  refine ⟨a, ?_, fun x hx => ?_⟩
  · rintro rfl
    exact hya (Ideal.zero_mem _)
  · by_contra hxV
    exact Set.disjoint_left.1 hW ⟨x, hxV, rfl⟩ (haW hx)

end GenericEq

open GenericEq

theorem generic_of_dense_fibres :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X : Over (Sp R)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (Sg : Set (Sp R)), Dense Sg → (∀ (Y : Over (Sp R)) [IsSeparated Y.hom] (f g : X ⟶ Y), (∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧ (Over.pullback t).map f = (Over.pullback t).map g) → (Over.pullback (Out.jK R)).map f = (Over.pullback (Out.jK R)).map g) ∧ (∀ u : Γ(X.left, ⊤), (∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧ (pullback.fst X.hom t).appTop.hom u = 0) → ∃ a : R, a ≠ 0 ∧ Out.scal X.hom a * u = 0) ∧ (∀ V : X.left.Opens, (∀ x : X.left, X.hom x ∈ Sg → x ∈ V) → ∃ a : R, a ≠ 0 ∧ ∀ x : X.left, a ∉ (X.hom x).asIdeal → x ∈ V) := by
  intro R _ _ _ X _ _ Sg hD
  exact ⟨fun Y _ f g => map_eq_generic R X Sg hD Y f g, exists_scal_mul_eq_zero R X Sg hD,
    exists_mem_of_not_mem R X Sg hD⟩

end GlobalTheory
end
