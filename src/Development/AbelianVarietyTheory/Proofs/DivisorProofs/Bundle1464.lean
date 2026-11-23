module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle802
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle263
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle530
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle097
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle167
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1370
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

noncomputable section

open GlobalTheory.QCoh.Qcqs GlobalTheory.ProjSpace

namespace GlobalTheory.GenericResidueDegree

theorem residue_generic_bijective (X : Scheme.{0}) [IsIntegral X] :
    Function.Bijective (X.residue (genericPoint X)).hom :=
  ⟨RingHom.injective (R := X.functionField) (X.residue (genericPoint X)).hom, X.residue_surjective _⟩

theorem residueDegree_eq_finrank_closure {X Y : Scheme.{0}} [IsIntegral X] (π : X ⟶ Y) (U : Y.Opens)
    (hU : IsAffineOpen U) (h : genericPoint X ∈ π ⁻¹ᵁ U) (E : Subfield X.functionField)
    (hE : E = Subfield.closure (Set.range fun s : Γ(Y, U) =>
      (X.presheaf.germ (π ⁻¹ᵁ U) (genericPoint X) h (π.app U s) : X.functionField))) :
    π.residueDegree (genericPoint X) = Module.finrank E X.functionField := by
  let e : X.functionField ≃+* X.residueField (genericPoint X) :=
    RingEquiv.ofBijective (X.residue (genericPoint X)).hom (residue_generic_bijective X)
  let ψ : Y.residueField (π (genericPoint X)) →+* X.functionField :=
    e.symm.toRingHom.comp (π.residueFieldMap (genericPoint X)).hom
  have hψ : ∀ a : Y.presheaf.stalk (π (genericPoint X)),
      ψ (Y.residue _ a) = π.stalkMap (genericPoint X) a := fun a => by
    apply e.injective
    have := congrArg (fun φ => φ.hom a) (Scheme.residue_residueFieldMap π (genericPoint X))
    exact (e.apply_symm_apply _).trans this
  have hg : ∀ s : Γ(Y, U), ψ (Y.residue _ (Y.presheaf.germ U (π (genericPoint X)) h s)) =
      X.presheaf.germ (π ⁻¹ᵁ U) (genericPoint X) h (π.app U s) := fun s => by
    rw [hψ]
    exact π.germ_stalkMap_apply U _ h s
  have hr : ψ.fieldRange = E := by
    subst hE
    refine le_antisymm ?_ (Subfield.closure_le.2 ?_)
    · rintro _ ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := Y.residue_surjective _ b
      letI := Y.presheaf.algebra_section_stalk (⟨π (genericPoint X), h⟩ : U)
      have hl := hU.isLocalization_stalk ⟨π (genericPoint X), h⟩
      obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj (hU.primeIdealOf ⟨π (genericPoint X), h⟩).asIdeal.primeCompl a
      have hu := IsLocalization.map_units (Y.presheaf.stalk (π (genericPoint X))) t
      have h1 : ψ (Y.residue _ a) * ψ (Y.residue _ (Y.presheaf.germ U (π (genericPoint X)) h t.1)) =
          ψ (Y.residue _ (Y.presheaf.germ U (π (genericPoint X)) h s)) := by
        rw [← map_mul, ← map_mul]
        exact congrArg (fun z => ψ (Y.residue _ z)) hst
      have h2 : ψ (Y.residue _ (Y.presheaf.germ U (π (genericPoint X)) h t.1)) ≠ 0 :=
        ((hu.map (Y.residue _).hom).map ψ).ne_zero
      rw [eq_div_of_mul_eq h2 h1, hg, hg]
      exact Subfield.div_mem _ (Subfield.subset_closure ⟨_, rfl⟩) (Subfield.subset_closure ⟨_, rfl⟩)
    · rintro _ ⟨s, rfl⟩
      exact ⟨_, hg s⟩
  clear hE
  subst hr
  letI := (π.residueFieldMap (genericPoint X)).hom.toAlgebra
  unfold Scheme.Hom.residueDegree
  refine Algebra.finrank_eq_of_equiv_equiv ψ.rangeRestrictFieldEquiv e.symm ?_
  ext a
  rfl

theorem residueDegree_eq_finrank_quotients : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) [IsIntegral (PSpace k D)] (π : X ⟶ PSpace k D), π ≫ PSpace.str k D = p → ∀ x : Fin (D + 1) → X.functionField, x 0 ≠ 0 → (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) → π (genericPoint X) = genericPoint (PSpace k D) → π.residueDegree (genericPoint X) = Module.finrank (Subfield.closure (Set.range (GlobalTheory.toFunctionField p) ∪ Set.range fun j : Fin D => x j.succ / x 0)) X.functionField := by
  intro k _ X _ p D _ π hπ x hx ⟨h, hj⟩ _
  refine residueDegree_eq_finrank_closure π _ (ProjSpace.isAffineOpen_chart k D 0) h _ ?_
  let g : Γ(X, π ⁻¹ᵁ ProjSpace.chart k D 0) →+* X.functionField :=
    (X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h).hom
  have hc : ∀ a : k, g ((baseRingHom (π ≫ PSpace.str k D) (π ⁻¹ᵁ ProjSpace.chart k D 0)).hom a) =
      GlobalTheory.toFunctionField p a := fun a => by
    rw [hπ]
    exact X.presheaf.germ_res_apply (homOfLE le_top) (genericPoint X) h
      (p.appTop ((Scheme.ΓSpecIso (.of k)).inv a))
  have key : ∀ q : MvPolynomial (Fin (D + 1)) k,
      g (π.app _ (MvPolynomial.aeval (R := k) (ProjSpace.ratio k D 0) q)) =
        MvPolynomial.eval₂Hom (GlobalTheory.toFunctionField p) (fun j => x j / x 0) q := fun q => by
    have e₁ := congrArg (fun t => g (t q))
      (ProjSpace.appLE_comp_aeval_ratio (φ := π) (i := 0) (hi := le_rfl))
    rw [Scheme.Hom.app_eq_appLE]
    refine e₁.trans ?_
    rw [MvPolynomial.map_eval₂Hom]
    congr 2
    · exact RingHom.ext hc
    · exact funext hj
  refine le_antisymm (Subfield.closure_le.2 ?_) (Subfield.closure_le.2 ?_)
  · rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · exact Subfield.subset_closure ⟨_, (key (MvPolynomial.C a)).trans (MvPolynomial.eval₂Hom_C _ _ _)⟩
    · exact Subfield.subset_closure ⟨_, (key (MvPolynomial.X j.succ)).trans (MvPolynomial.eval₂Hom_X' _ _ _)⟩
  · rintro _ ⟨s, rfl⟩
    obtain ⟨q, rfl⟩ := ProjSpace.aeval_ratio_surjective k D 0 s
    refine Set.mem_of_eq_of_mem (key q) ?_
    rw [SetLike.mem_coe]
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.eval₂Hom_C]
      exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    | add q q' h1 h2 =>
      rw [map_add (f := _)]
      exact Subfield.add_mem _ h1 h2
    | mul_X q j h1 =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      refine Subfield.mul_mem _ h1 ?_
      refine Fin.cases ?_ (fun j => Subfield.subset_closure (Or.inr ⟨j, rfl⟩)) j
      rw [div_self hx]
      exact Subfield.one_mem _

end GlobalTheory.GenericResidueDegree
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.GenericImage

open scoped GlobalTheory.ProjSpace

theorem map_genericPoint_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) [IsIntegral (PSpace k D)] (π : X ⟶ PSpace k D), π ≫ PSpace.str k D = p → ∀ x : Fin (D + 1) → X.functionField, x 0 ≠ 0 → (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) → Function.Injective (MvPolynomial.eval₂Hom (GlobalTheory.toFunctionField p) fun j : Fin D => x j.succ / x 0) → π (genericPoint X) = genericPoint (PSpace k D) := by
  intro k _ X _ p D _ π hπ x hx0 ⟨h, hx⟩ hinj
  set W := π ⁻¹ᵁ ProjSpace.chart k D 0 with hW
  let Φ : Γ(PSpace k D, ProjSpace.chart k D 0) →+* X.functionField :=
    (X.presheaf.germ W (genericPoint X) h).hom.comp (π.appLE (ProjSpace.chart k D 0) W le_rfl).hom
  have hconst : (X.presheaf.germ W (genericPoint X) h).hom.comp
      (GlobalTheory.QCoh.Qcqs.baseRingHom (π ≫ PSpace.str k D) W).hom = GlobalTheory.toFunctionField p := by
    subst hπ
    refine RingHom.ext fun a => ?_
    simp only [GlobalTheory.QCoh.Qcqs.baseRingHom, GlobalTheory.toFunctionField, Scheme.Hom.appLE, CommRingCat.hom_comp,
      RingHom.comp_apply]
    exact TopCat.Presheaf.germ_res_apply X.presheaf _ _ _ _
  have key : ∀ a : Γ(PSpace k D, ProjSpace.chart k D 0), a ≠ 0 → Φ a ≠ 0 := by
    intro a ha
    obtain ⟨P, rfl⟩ := ProjSpace.aeval_ratio_surjective k D 0 a
    let s : Fin (D + 1) → MvPolynomial (Fin D) k := Fin.cons 1 MvPolynomial.X
    have e1 : ∀ (A : Type) [CommRing A] (c : k →+* A) (r : Fin (D + 1) → A), r 0 = 1 →
        MvPolynomial.eval₂Hom c r P =
          MvPolynomial.eval₂Hom c (fun j : Fin D => r j.succ) (MvPolynomial.bind₁ s P) := by
      intro A _ c r hr
      rw [MvPolynomial.eval₂Hom_bind₁]
      congr 2
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [s, hr]
      · simp [s]
    have e2 : Φ (MvPolynomial.aeval (ProjSpace.ratio k D 0) P) =
        MvPolynomial.eval₂Hom (GlobalTheory.toFunctionField p) (fun j => x j / x 0) P := by
      have := congrArg (fun t => t P) (ProjSpace.appLE_comp_aeval_ratio (φ := π) (W := W) (i := 0) (hi := le_rfl))
      simp only [RingHom.comp_apply, RingHom.coe_coe] at this
      simp only [Φ, RingHom.comp_apply]
      erw [this]
      rw [MvPolynomial.map_eval₂Hom, hconst]
      congr 2
      funext j
      exact hx j
    rw [e2, e1 _ _ _ (div_self hx0)]
    intro h0
    have hQ : MvPolynomial.bind₁ s P = 0 := hinj (h0.trans (map_zero _).symm)
    apply ha
    rw [MvPolynomial.aeval_def, ← MvPolynomial.coe_eval₂Hom,
      e1 _ _ _ (by rw [ProjSpace.ratio, ProjSpace.ratioOn_self]), hQ, map_zero]
  have hmem : ∀ a : Γ(PSpace k D, ProjSpace.chart k D 0), a ≠ 0 →
      π (genericPoint X) ∈ (PSpace k D).basicOpen a := by
    intro a ha
    have h1 : genericPoint X ∈ X.basicOpen ((π.appLE (ProjSpace.chart k D 0) W le_rfl).hom a) := by
      rw [Scheme.mem_basicOpen X _ _ h]
      exact (key a ha).isUnit
    have h2 := (Scheme.basicOpen_appLE π W _ le_rfl a).le h1
    exact h2.2
  refine IsGenericPoint.eq ?_ (genericPoint_spec _)
  refine Dense.closure_eq (dense_iff_inter_open.2 fun U hU hne => ?_)
  obtain ⟨y, -, hyU, hyc⟩ := (IrreducibleSpace.isIrreducible_univ (PSpace k D)).2 U
    (ProjSpace.chart k D 0 : Set (PSpace k D)) hU (ProjSpace.chart k D 0).2
    (by simpa using hne) ⟨π (genericPoint X), trivial, h⟩
  obtain ⟨f, hf, hyf⟩ := (ProjSpace.isAffineOpen_chart k D 0).exists_basicOpen_le
    (V := ⟨U, hU⟩) ⟨y, hyU⟩ hyc
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hyf
    exact hyf
  exact ⟨_, hf (hmem f hf0), rfl⟩

end GlobalTheory.GenericImage
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.OrbitAll

open GlobalTheory.UnitLemma.Orbit

open GlobalTheory.UnitLemma Polynomial

variable {K : UQ}

theorem isIso_stSum_eq {B C : InvAlg K} {φ : B.A ≃ₐ[K.E] C.A} (h : IsIso φ) : C.stSum = B.stSum := by
  unfold InvAlg.stSum
  rw [h.finsum_eq C.N fun x u => (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K C x u).1]
  exact finsum_congr fun k => h.N_eq _

theorem isIso_kapSum_eq {B₁ B₂ C₁ C₂ : InvAlg K} {φ₁ : B₁.A ≃ₐ[K.E] C₁.A} {φ₂ : B₂.A ≃ₐ[K.E] C₂.A}
    (h₁ : IsIso φ₁) (h₂ : IsIso φ₂) : InvAlg.kapSum C₁ C₂ = InvAlg.kapSum B₁ B₂ := by
  unfold InvAlg.kapSum
  refine ((h₁.prod h₂).finsum_eq (fun x => K.eta (C₁.gramDet x.1) * (C₁.prod C₂).N x) fun x u => ?_).trans ?_
  · have e1 := (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K (C₁.prod C₂) x u).1
    have e2 := (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K C₁ x.1 (Units.map (MonoidHom.fst C₁.A C₂.A) u)).2
    exact congrArg₂ (· * ·) e2 e1
  · exact finsum_congr fun k => congrArg₂ (· * ·) (h₁.eta_eq _) ((h₁.prod h₂).N_eq _)

theorem isIso_identity {B₁ B₂ C₁ C₂ : InvAlg K} {φ₁ : B₁.A ≃ₐ[K.E] C₁.A} {φ₂ : B₂.A ≃ₐ[K.E] C₂.A}
    (h₁ : IsIso φ₁) (h₂ : IsIso φ₂) (h : InvAlg.Identity C₁ C₂) : InvAlg.Identity B₁ B₂ := by
  unfold InvAlg.Identity at h ⊢
  rwa [isIso_kapSum_eq h₁ h₂, isIso_stSum_eq h₁, isIso_stSum_eq h₂, h₁.charpoly_eq_of_isIso, h₂.charpoly_eq_of_isIso] at h

theorem prod_aeval (B₁ B₂ : InvAlg K) (f : K.O[X]) :
    aeval (B₁.prod B₂).g f = ((aeval B₁.g f, aeval B₂.g f) : B₁.A × B₂.A) :=
  Prod.ext (aeval_algHom_apply (AlgHom.fst K.O B₁.A B₂.A) (B₁.g, B₂.g) f).symm
    (aeval_algHom_apply (AlgHom.snd K.O B₁.A B₂.A) (B₁.g, B₂.g) f).symm

theorem prod_integral (B₁ B₂ : InvAlg K) (h₁ : IsIntegral K.O B₁.g) (h₂ : IsIntegral K.O B₂.g) :
    IsIntegral K.O (B₁.prod B₂).g :=
  IsIntegral.pair (x := (B₁.g, B₂.g)) h₁ h₂

theorem eq_one_of_finrank_cut (B : InvAlg K) {e : B.A} (hi : IsIdempotentElem e) (he : B.σ e = e)
    (h : Module.finrank K.E (_root_.GlobalTheory.UnitLemma.Orbit.cut B e he).A = 0) : e = 1 := by
  have : Subsingleton (B.A ⧸ Ideal.span {e}) := (Module.finrank_zero_iff (R := K.E) (M := (_root_.GlobalTheory.UnitLemma.Orbit.cut B e he).A)).1 h
  have h1 : (1 : B.A) ∈ Ideal.span {e} := Ideal.Quotient.eq_zero_iff_mem.1 (Subsingleton.elim _ _)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
  linear_combination (e - 1) * -ha + a * hi.eq

theorem finrank_cut (B : InvAlg K) {e : B.A} (hi : IsIdempotentElem e) (he : B.σ e = e) :
    Module.finrank K.E B.A = Module.finrank K.E (_root_.GlobalTheory.UnitLemma.Orbit.cut B e he).A +
      Module.finrank K.E (_root_.GlobalTheory.UnitLemma.Orbit.cut B (1 - e) (one_sub_fixed B he)).A := by
  rw [(AlgEquiv.prodQuotientOfIsIdempotentElem K.E hi hi.one_sub (by simp)
    (by simp [hi])).toLinearEquiv.finrank_eq, Module.finrank_prod]
  rfl

theorem charpoly_eq_mul_charpoly_cut (B : InvAlg K) {e : B.A} (hi : IsIdempotentElem e) (he : B.σ e = e) :
    B.P = (_root_.GlobalTheory.UnitLemma.Orbit.cut B e he).P * (_root_.GlobalTheory.UnitLemma.Orbit.cut B (1 - e) (one_sub_fixed B he)).P := by
  rw [← prod_P, (isIso_cut B hi he).charpoly_eq_of_isIso]

theorem one_orbit (B : InvAlg K) (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g)
    (h : ∀ e ∈ Algebra.adjoin K.O ({B.g} : Set B.A), e * e = e → B.σ e = e → e = 0 ∨ e = 1) :
    (∃ e ∈ Algebra.adjoin K.O ({B.g} : Set B.A), e * e = e ∧ e + B.σ e = 1) ∨
      IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A)) := by
  rcases subsingleton_or_nontrivial B.A with hs | hs
  · exact Or.inl ⟨0, zero_mem _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  by_cases hid : ∀ e : Algebra.adjoin K.O ({B.g} : Set B.A), e * e = e → e = 0 ∨ e = 1
  · have : Module.Finite K.O (Algebra.adjoin K.O ({B.g} : Set B.A)) :=
      Module.Finite.iff_fg.2 hi.fg_adjoin_singleton
    exact Or.inr (isLocalRing_of_idem (R := K.O) _ hid)
  push Not at hid
  obtain ⟨⟨e, he⟩, hee, h0, h1⟩ := hid
  have hee : e * e = e := congrArg Subtype.val hee
  have h0 : e ≠ 0 := fun h => h0 (Subtype.ext h)
  have h1 : e ≠ 1 := fun h => h1 (Subtype.ext h)
  have he' := adjoin_stable B hu hi he
  have hee' : B.σ e * B.σ e = B.σ e := by rw [← map_mul, hee]
  have hm : e * B.σ e = 0 := by
    refine (h _ (mul_mem he he') ?_ ?_).resolve_right fun h2 => h1 ?_
    · linear_combination B.σ e * B.σ e * hee + e * hee'
    · rw [map_mul, B.σ_σ, mul_comm]
    · linear_combination (1 - e) * h2 + B.σ e * hee
  refine Or.inl ⟨e, he, hee, (h _ (add_mem he he') ?_ ?_).resolve_left fun h2 => h0 ?_⟩
  · linear_combination hee + hee' + 2 * hm
  · rw [map_add (f := _), B.σ_σ, add_comm]
  · linear_combination e * h2 - hee - hm

theorem identity_integral (hL : UnitLemmaLie) (n : ℕ) : ∀ B₁ B₂ : InvAlg K,
    Module.finrank K.E B₁.A + Module.finrank K.E B₂.A = n → B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 →
    (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → InvAlg.Identity B₁ B₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B₁ B₂ hn u₁ u₂ hs i₁ i₂
  by_cases h : ∀ e ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
      e * e = e → (B₁.prod B₂).σ e = e → e = 0 ∨ e = 1
  · rcases one_orbit (B₁.prod B₂) (Prod.ext u₁ u₂) (prod_integral _ _ i₁ i₂) h with h | h
    · exact GlobalTheory.T.involutive_algebra_product_identity K B₁ B₂ u₁ u₂ hs i₁ i₂ h
    · exact GlobalTheory.T.unitLemma_local_anyResidueChar_of_lieAlgebra hL K B₁ B₂ u₁ u₂ hs i₁ i₂ h
  push Not at h
  obtain ⟨e, he, hee, hσ, h0, h1⟩ := h
  rw [Algebra.adjoin_singleton_eq_range_aeval] at he
  obtain ⟨f, hf⟩ := he
  have hf : ((aeval B₁.g f, aeval B₂.g f) : B₁.A × B₂.A) = e := (prod_aeval B₁ B₂ f).symm.trans hf
  obtain ⟨e₁, e₂⟩ := e
  obtain ⟨f₁, f₂⟩ := Prod.ext_iff.1 hf
  have j₁ : IsIdempotentElem e₁ := congrArg Prod.fst hee
  have j₂ : IsIdempotentElem e₂ := congrArg Prod.snd hee
  have s₁ : B₁.σ e₁ = e₁ := congrArg Prod.fst hσ
  have s₂ : B₂.σ e₂ = e₂ := congrArg Prod.snd hσ
  dsimp only at f₁ f₂
  have r₁ := finrank_cut B₁ j₁ s₁
  have r₂ := finrank_cut B₂ j₂ s₂
  have p₁ : Module.finrank K.E (_root_.GlobalTheory.UnitLemma.Orbit.cut B₁ e₁ s₁).A + Module.finrank K.E (_root_.GlobalTheory.UnitLemma.Orbit.cut B₂ e₂ s₂).A ≠ 0 := fun hz =>
    h1 (Prod.ext (eq_one_of_finrank_cut B₁ j₁ s₁ (Nat.add_eq_zero_iff.1 hz).1)
      (eq_one_of_finrank_cut B₂ j₂ s₂ (Nat.add_eq_zero_iff.1 hz).2))
  have p₂ : Module.finrank K.E (_root_.GlobalTheory.UnitLemma.Orbit.cut B₁ (1 - e₁) (one_sub_fixed B₁ s₁)).A +
      Module.finrank K.E (_root_.GlobalTheory.UnitLemma.Orbit.cut B₂ (1 - e₂) (one_sub_fixed B₂ s₂)).A ≠ 0 := fun hz =>
    h0 (Prod.ext
      (sub_eq_self.1 (eq_one_of_finrank_cut B₁ j₁.one_sub (one_sub_fixed B₁ s₁) (Nat.add_eq_zero_iff.1 hz).1))
      (sub_eq_self.1 (eq_one_of_finrank_cut B₂ j₂.one_sub (one_sub_fixed B₂ s₂) (Nat.add_eq_zero_iff.1 hz).2)))
  rw [charpoly_eq_mul_charpoly_cut B₁ j₁ s₁, charpoly_eq_mul_charpoly_cut B₂ j₂ s₂, mul_mul_mul_comm] at hs
  refine isIso_identity (isIso_cut B₁ j₁ s₁) (isIso_cut B₂ j₂ s₂) ?_
  refine GlobalTheory.T.involutiveAlg_identity_prod_of_unit_resultant K _ _ _ _ hs (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂) (cut_integral _ _ _ i₁)
    (cut_integral _ _ _ i₂) ?_ ?_ ?_
  · rw [← prod_P, ← prod_P] at hs ⊢
    refine val_resultant _ _ hs.of_mul_left hs.of_mul_right
      (prod_integral _ _ (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂))
      (prod_integral _ _ (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂)) f ?_ ?_
    · rw [prod_aeval, cut_aeval, cut_aeval, f₁, f₂]
      exact Prod.ext (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))
        (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))
    · rw [prod_aeval, cut_aeval, cut_aeval, f₁, f₂]
      exact Prod.ext (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self (1 - e₁))).symm
        (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self (1 - e₂))).symm
  · exact ih _ (by omega) _ _ rfl (cut_unitary _ _ _ u₁) (cut_unitary _ _ _ u₂) hs.of_mul_left
      (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂)
  · exact ih _ (by omega) _ _ rfl (cut_unitary _ _ _ u₁) (cut_unitary _ _ _ u₂) hs.of_mul_right
      (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂)

theorem identity_of_lie : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 →
    B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ := by
  intro hL K B₁ B₂ u₁ u₂ hs
  by_cases hi : IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g
  · exact identity_integral hL _ B₁ B₂ rfl u₁ u₂ hs hi.1 hi.2
  · obtain ⟨h1, h2⟩ := GlobalTheory.T.kappaSum_zero_and_stableSum_mul_zero_of_not_integral K B₁ B₂ hi
    unfold InvAlg.Identity
    rw [h1, h2, mul_zero]

end GlobalTheory.UnitLemma.OrbitAll
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem zc_eq_scL {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) :
    zc E N = lie E N (Central.scL N 1) := by
  unfold zc
  congr 1

theorem splitCentre_eq_scalar {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (t : ℝ) :
    splitCentre E N t = Matrix.GeneralLinearGroup.scalar (Fin N) (infId E (expU (t • (1 : Cinf E)))) := by
  have e : (fun _ : InfinitePlace E => (t : ℂ)) = t • (1 : Cinf E) := by
    funext w; simp
  unfold splitCentre
  rw [e]
  exact cornerGL_scalar _ _

theorem zc_comm_mem_eigen : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ), (∀ o : Op E N, zc E N * act o = act o * zc E N) ∧ zc E N ∈ Zalg E N ∧ ∀ (φ : Sm E N) (c : ℂ), zc E N φ = c • φ ↔ ∀ (t : ℝ) (g : GA E N), φ.1 (splitCentre E N t * g) = Complex.exp (c * t) * φ.1 g := by
  intro E _ _ _ N
  rw [zc_eq_scL]
  refine ⟨fun o => (Central.lie_act 1 o).eq, Central.lie_mem_Zalg 1, fun φ c => ⟨fun h t g => ?_, fun h => ?_⟩⟩
  · have e : Central.scL N (t • (1 : Cinf E)) = t • Central.scL N (1 : Cinf E) := by
      funext i j
      change Matrix.diagonal (fun _ => t • (1 : Cinf E)) i j = t • Matrix.diagonal (fun _ => (1 : Cinf E)) i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.diagonal_apply_ne _ hij]
    have h1 : lie E N (Central.scL N (t • (1 : Cinf E))) φ = (c * t) • φ := by
      rw [e, map_smul, LinearMap.smul_apply, h, mul_comm, mul_smul, Complex.coe_smul]
    have h2 := congrFun (congrArg Subtype.val (Central.rs_exp _ _ φ h1)) g
    rw [splitCentre_eq_scalar, scalar_comm]
    exact h2
  · refine Subtype.ext <| funext fun g => ?_
    have h1 := Central.hasDerivAt_scalar (1 : Cinf E) φ g
    have e : ∀ t : ℝ, φ.1 (g * Matrix.GeneralLinearGroup.scalar (Fin N) (infId E (expU (t • (1 : Cinf E))))) =
        Complex.exp (c * t) * φ.1 g := fun t => by rw [← scalar_comm, ← splitCentre_eq_scalar, h]
    simp only [e] at h1
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (c * t) * φ.1 g) (c * φ.1 g) 0 := by
      simpa using (((Complex.ofRealCLM.hasDerivAt (x := 0)).const_mul c).cexp).mul_const (φ.1 g)
    exact h1.unique h2

end GlobalTheory.ResW
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ c : AlgChart X.str σ X.dim, DifferentiableOn ℂ (c.e ∘ e.symm) (e.target ∩ e.symm ⁻¹' c.e.source) := by
  first | exact @GlobalTheory.GoodTop.holoChart_trans_algChart | exact GlobalTheory.GoodTop.holoChart_trans_algChart | (intros; apply GlobalTheory.GoodTop.holoChart_trans_algChart <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.changeOfFrame_holomorphic_invertible_holomorphicChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {y : CxPts X.str σ}, y ∈ e.source → ∀ {A A' : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → A' ∈ E.S (under y) → MContDiffAt 2 (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ) (e y) ∧ IsUnit (((A' * A⁻¹).map (ratVal · (e.symm (e y))) ())ᵀ).det ∧ ∀ᶠ x in 𝓝 (e y), ∀ η, mdbar (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ) x η = 0 := by
  first | exact @GlobalTheory.GoodTop.changeFrame_holoChart | exact GlobalTheory.GoodTop.changeFrame_holoChart | (intros; apply GlobalTheory.GoodTop.changeFrame_holoChart <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.piola_identity_wirtingerAntiholomorphic : ∀ {n : ℕ} (f : Fin n → V n → ℂ) (j : Fin n) (v : V n), (∀ i, i ≠ j → ContDiffAt ℝ 2 (f i) v) → ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) * dbar (fun x => ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) = 0 := by
  first | exact @GlobalTheory.GoodTop.piola_dbar | exact GlobalTheory.GoodTop.piola_dbar | (intros; apply GlobalTheory.GoodTop.piola_dbar <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.interPoly_eq_zero_of_isHomogeneous_ne_dim : ∀ (F : Type) [Field F] (Y : Var F) (κ : Type) (gr : κ → Y.Dv) (k : ℕ) (P : MvPolynomial κ ℝ), P.IsHomogeneous k → k ≠ Y.dim → Y.interPoly gr P = 0 := by
  first | exact @GlobalTheory.ProjVar.Var.interPoly_eq_zero_of_isHomogeneous | exact GlobalTheory.ProjVar.Var.interPoly_eq_zero_of_isHomogeneous | (intros; apply GlobalTheory.ProjVar.Var.interPoly_eq_zero_of_isHomogeneous <;> assumption)
end
