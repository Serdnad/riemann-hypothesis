module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle094
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle003

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.FormCount

section Values
variable {F : Type} [CommRing F] {X Y : Scheme.{0}}

theorem valR_appLE (x : Sp F ⟶ Y) (φ : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ φ ⁻¹ᵁ U)
    (f : Γ(X, U)) (hx : ⊤ ≤ x ⁻¹ᵁ V) : valR x V ((φ.appLE U V h).hom f) = valR (x ≫ φ) U f := by
  have hx' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := le_trans hx (x.preimage_mono h)
  rw [CrdCalc.valR_eq _ _ hx, CrdCalc.valR_eq _ _ hx', CrdCalc.valHom, CrdCalc.valHom,
    ← Scheme.Hom.appLE_comp_appLE x φ U V ⊤ h hx]
  rfl

theorem valR_scal {K : Type} [CommRing K] (ψ : K →+* F) (x : Sp F ⟶ Y) (q : Y ⟶ Sp K) (hq : x ≫ q = spMap ψ)
    (V : Y.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ V) (c : K) : valR x V (resTop V (scal q c)) = ψ c := by
  have e : valR x V (resTop V (scal q c)) =
      valR (x ≫ q) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) :=
    valR_appLE x q ⊤ V le_top _ hx
  have e' := (CrdCalc.valR_spMap ψ (𝟙 (Sp K)) ⊤ le_rfl).2 ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)
  rw [Category.comp_id] at e'
  rw [e, hq, e', CrdCalc.valR_eq _ _ le_top]
  have h : (𝟙 (Sp K) : Sp K ⟶ Sp K).appLE ⊤ ⊤ le_top = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
  congr 1
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    (((𝟙 (Sp K) : Sp K ⟶ Sp K).appLE ⊤ ⊤ le_top).hom _) = c
  rw [h]
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id_apply c

theorem wchart_le (L : LB X) (φ : Y ⟶ X) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => φ) j ≤ φ ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 X) j :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k

theorem exists_monomial (L : LB X) (φ : Y ⟶ X) (N d : ℕ) {J : Type} [Fintype J]
    (σ : J → (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (N : ℤ))).Sec) (α : J → ℕ) (hα : ∑ i, α i = d) :
    ∃ s : (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => ((N * d : ℕ) : ℤ))).Sec,
      ∀ j, s.f j = ∏ i, (φ.appLE _ _ (wchart_le L φ j)).hom ((σ i).f j) ^ α i := by
  have pull_restrict {U U' : X.Opens} {V V' : Y.Opens} (hu : U' ≤ U) (hv : V' ≤ V)
      (h : V ≤ φ ⁻¹ᵁ U) (h' : V' ≤ φ ⁻¹ᵁ U') (a : Γ(X, U)) :
      (Y.presheaf.map (homOfLE hv).op).hom ((φ.appLE U V h).hom a) =
        (φ.appLE U' V' h').hom ((X.presheaf.map (homOfLE hu).op).hom a) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have transition {Z : Scheme.{0}} (f : Z ⟶ X) (j j' : Fin 1 → L.ι) (n : ℕ) :
      ((L.LinComb (fun _ : Fin 1 => f) (fun _ => (n : ℤ))).g j j').val =
        ((f.appLE _ _ (le_inf
          (inf_le_left.trans (LB.wchart_le L (fun _ : Fin 1 => f) j 0))
          (inf_le_right.trans (LB.wchart_le L (fun _ : Fin 1 => f) j' 0)))).hom
          (L.g (j 0) (j' 0)).val) ^ n := by
    simp only [LB.LinComb, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
    rfl
  let A (j : Fin 1 → L.ι) := L.wchart (fun _ : Fin 1 => 𝟙 X) j
  let B (j : Fin 1 → L.ι) := L.wchart (fun _ : Fin 1 => φ) j
  let s (i : J) (j : Fin 1 → L.ι) : Γ(X, A j) := (σ i).f j
  let m (j : Fin 1 → L.ι) : Γ(Y, B j) := ∏ i, (φ.appLE (A j) (B j) (wchart_le L φ j)).hom (s i j) ^ α i
  refine ⟨⟨m, ?_⟩, fun _ => rfl⟩
  rintro (j : Fin 1 → L.ι) (j' : Fin 1 → L.ι)
  let U := A j ⊓ A j'
  let V := B j ⊓ B j'
  have h : V ≤ φ ⁻¹ᵁ U := fun _ hy => ⟨wchart_le L φ j hy.1, wchart_le L φ j' hy.2⟩
  let p := (φ.appLE U V h).hom
  let gX : Γ(X, U) := ((L.LinComb (fun _ : Fin 1 => 𝟙 X) (fun _ => (N : ℤ))).g j j').val
  let gY : Γ(Y, V) := ((L.LinComb (fun _ : Fin 1 => φ) (fun _ => ((N * d : ℕ) : ℤ))).g j j').val
  have hg : p gX ^ d = gY := by
    dsimp only [p, gX, gY]
    rw [transition (𝟙 X) j j' N, transition φ j j' (N * d), map_pow, ← pow_mul,
      ← CommRingCat.comp_apply]
    erw [Scheme.Hom.appLE_comp_appLE φ (𝟙 X)]
    rfl
  let leftX := (X.presheaf.map (homOfLE (inf_le_left : U ≤ A j)).op).hom
  let rightX := (X.presheaf.map (homOfLE (inf_le_right : U ≤ A j')).op).hom
  have hc (i : J) : p (leftX (s i j)) = p gX * p (rightX (s i j')) := by
    rw [← map_mul]
    exact congrArg p ((σ i).compat j j')
  change (Y.presheaf.map (homOfLE (inf_le_left : V ≤ B j)).op).hom (m j) =
    gY * (Y.presheaf.map (homOfLE (inf_le_right : V ≤ B j')).op).hom (m j')
  simp only [m, map_prod, map_pow,
    pull_restrict (inf_le_left : U ≤ A j) (inf_le_left : V ≤ B j) (wchart_le L φ j) h,
    pull_restrict (inf_le_right : U ≤ A j') (inf_le_right : V ≤ B j') (wchart_le L φ j') h]
  change (∏ i, p (leftX (s i j)) ^ α i) = gY * ∏ i, p (rightX (s i j')) ^ α i
  simp only [hc, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hα, hg]

end Values

theorem hilb_le {k J : Type} [Field k] [Fintype J] (C : Set (J → k)) (d m : ℕ) (β : Fin m → C → k)
    (h : ∀ α : J → ℕ, ∑ i, α i = d → ∃ c : Fin m → k, ∀ v : C, ∏ i, v.1 i ^ α i = ∑ l, c l * β l v) :
    hilb C d ≤ m := by
  have le : (MvPolynomial.homogeneousSubmodule J k d).map
      (LinearMap.pi fun v : C => (MvPolynomial.aeval (R := k) v.1).toLinearMap) ≤ Submodule.span k (Set.range β) := by
    rintro _ ⟨P, hP, rfl⟩

    rw [P.as_sum, map_sum]
    refine Submodule.sum_mem _ fun α hα => ?_
    have hd : ∑ i, α i = d := by
      have := MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hP hα
      rw [this]
      exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => Finsupp.notMem_support_iff.1 hi).symm
    obtain ⟨c, hc⟩ := h α hd
    refine (Submodule.mem_span_range_iff_exists_fun k).2 ⟨fun l => P.coeff α * c l, funext fun v => ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, LinearMap.pi_apply, AlgHom.toLinearMap_apply,
      MvPolynomial.aeval_monomial, Algebra.algebraMap_self, RingHom.id_apply]
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), hc v, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => _root_.mul_assoc _ _ _
  have := Module.Finite.span_of_finite k (Set.finite_range β)
  exact (Submodule.finrank_mono le).trans ((finrank_range_le_card β).trans (Fintype.card_fin m).le)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p}

theorem dim_eq (u : ρ.UTest p y₀) : u.A.g = S.g :=
  (ReciprocityTheory.ChartRestriction.G.H1.dim_unique u.A.A.hom u.A.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback u.cart.1 ρ.P.smoothDim)
    (eSec u.A.A (IsLocalRing.closedPoint _))).trans ρ.g_eq

theorem gPt_j (u : ρ.UTest p y₀) :
    gPt p ≫ spMap u.j = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem hilb_generic_le : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (J : Type) [Fintype J] (σ : J → (u.H S.N).Sec) (d : ℕ), 1 ≤ d → hilb {w : J → PadicAlgCl p | ∃ a : Sp (PadicAlgCl p) ⟶ u.G.left, a ≫ u.G.hom = gPt p ≫ spMap u.j ∧ Crd (u.H S.N) σ a w} d ≤ (S.N * d) ^ S.g := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u J _ σ d hd
  have hN : 1 ≤ S.N * d := by
    rw [ρ.N_eq]
    exact Nat.mul_pos (pow_pos (pow_pos ρ.n_prime.pos _) _) hd
  obtain ⟨b, -, hb⟩ := GlobalTheory.GenericSectionBasis.exists_secK_basis hL.1.secBaseChange u.V _ u.D u.A u.G
    u.U.toUnifPre (S.N * d) hN
  rw [← dim_eq u]
  let C := {w : J → PadicAlgCl p | ∃ a : Sp (PadicAlgCl p) ⟶ u.G.left,
    a ≫ u.G.hom = gPt p ≫ spMap u.j ∧ Crd (u.H S.N) σ a w}
  have hC : ∀ w : C, ∃ (x : Sp (PadicAlgCl p) ⟶ pullback u.G.hom (jK u.V)) (l : Fin 1 → u.U.LG.L.ι)
      (c : PadicAlgCl p), x ≫ pullback.snd _ _ = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ∧
      ⊤ ≤ x ⁻¹ᵁ LB.wchart u.U.LG.L (fun _ : Fin 1 => pullback.fst u.G.hom (jK u.V)) l ∧
      ∀ i, w.1 i = c * valR (x ≫ pullback.fst _ _) _ ((σ i).f l) := by
    rintro ⟨w, a, ha, l, c, hl, hw⟩
    obtain ⟨x, rfl, hx⟩ : ∃ x : Sp (PadicAlgCl p) ⟶ pullback u.G.hom (jK u.V), x ≫ pullback.fst _ _ = a ∧
        x ≫ pullback.snd _ _ = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) :=
      ⟨pullback.lift a _ (ha.trans (gPt_j u)), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    exact ⟨x, l, c, hx, fun y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (hl hy) k, hw⟩
  choose x l c hx hl hw using hC
  refine hilb_le C d _ (fun n w => c w ^ d * valR (x w) _ ((b n).f (l w))) fun α hα => ?_
  obtain ⟨s, hs⟩ := exists_monomial u.U.LG.L (pullback.fst u.G.hom (jK u.V)) S.N d σ α hα
  obtain ⟨e, he, -⟩ := hb s
  refine ⟨fun n => algebraMap _ _ (e n), fun w => ?_⟩
  have h := congrArg (CrdCalc.valHom (x w) _ (hl w)) ((hs (l w)).symm.trans (he (l w)))
  replace h := (map_prod _ _ _).symm.trans (h.trans (map_sum _ _ _))
  simp only [hw w, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hα]
  refine Eq.trans ?_ ((congrArg (c w ^ d * ·) h).trans ?_)
  · refine congrArg (c w ^ d * ·) (Finset.prod_congr rfl fun i _ => Eq.symm ((map_pow _ _ _).trans ?_))
    exact congrArg (· ^ α i) ((CrdCalc.valR_eq _ _ (hl w) _).symm.trans (valR_appLE _ _ _ _ _ _ (hl w)))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => Eq.trans (congrArg (c w ^ d * ·) ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ (CrdCalc.valR_eq _ _ (hl w) _).symm))) (mul_left_comm _ _ _)
  exact (CrdCalc.valR_eq _ _ (hl w) _).symm.trans (valR_scal _ (x w) _ (hx w) _ (hl w) (e n))

end GlobalTheory.ZH.FormCount
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ToImm
open GlobalTheory.ZH.CrdCalc GlobalTheory.ZH.ImmSep

theorem ext_local {T X : Scheme.{0}} (f g : T ⟶ X)
    (h : ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ T), y ≫ f = y ≫ g) : f = g :=
  ReciprocityTheory.ChartRestriction.G.TB.JGPf.ext_of_fromSpecStalk f g fun t =>
    @h (T.presheaf.stalk t) _ (T.toLocallyRingedSpace.isLocalRing t) (T.fromSpecStalk t)

theorem exists_hom_of_ringHom {X Y : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (V : Y.Opens)
    (φ : Γ(X, U) →+* Γ(Y, V)) : ∃ g : V.toScheme ⟶ X, ∀ (R : Type) [CommRing R] (y : Sp R ⟶ V.toScheme)
      (h : ⊤ ≤ (y ≫ V.ι) ⁻¹ᵁ V), ∃ h' : ⊤ ≤ (y ≫ g) ⁻¹ᵁ U,
        ∀ f, valHom (y ≫ g) U h' f = valHom (y ≫ V.ι) V h (φ f) := by
  refine ⟨V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec, fun R _ y h => ?_⟩
  have h0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have h' : ⊤ ≤ (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec) ⁻¹ᵁ U :=
    fun z _ => h0 (Set.mem_univ ((y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)) z))
  refine ⟨h', fun f => ?_⟩
  have h1 : hU.fromSpec.appLE U ⊤ h0 = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact Category.comp_id _
  have h2 : (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h' =
      hU.fromSpec.appLE U ⊤ h0 ≫ (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop :=
    (Scheme.Hom.appLE_comp_appLE (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)) hU.fromSpec
      U ⊤ ⊤ h0 le_rfl).symm
  have h3 : (y ≫ V.ι).appLE V ⊤ h = V.topIso.inv ≫ y.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE y V.ι V ⊤ ⊤ (fun x _ => x.2) le_rfl]
    erw [Scheme.Opens.ι_appLE]
    simp only [Scheme.Opens.topIso_inv]
    congr 1
  have h4 : (y ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h' =
      CommRingCat.ofHom φ ≫ (y ≫ V.ι).appLE V ⊤ h := by
    rw [h2, h1, h3, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop]
    simp only [Category.assoc]
    rw [Scheme.ΓSpecIso_naturality_assoc]
    exact Iso.inv_hom_id_assoc _ _
  unfold valHom
  rw [h4]
  rfl

def constHom {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) : k →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

theorem constHom_apply {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) (a : k) :
    constHom p U a = constFn p U a := rfl

theorem eq_zero_of_dense {Y : Scheme.{0}} [IsReduced Y] {K : Type} [Field K] {A : Type}
    (x : A → (Sp K ⟶ Y)) (hd : Dense (⋃ a, Set.range (x a))) (V : Y.Opens) (f : Γ(Y, V))
    (hf : ∀ a (h : ⊤ ≤ x a ⁻¹ᵁ V), valHom (x a) V h f = 0) : f = 0 := by
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro z hz
  obtain ⟨w, hw, hw'⟩ := hd.inter_open_nonempty _ (Y.basicOpen f).isOpen ⟨z, hz⟩
  obtain ⟨a, t, rfl⟩ := Set.mem_iUnion.1 hw'
  have h1 : ⊤ ≤ x a ⁻¹ᵁ Y.basicOpen f := fun t' _ => by
    have : t' = t := Subsingleton.elim (α := PrimeSpectrum K) _ _
    subst this
    exact hw
  have h2 : ⊤ ≤ x a ⁻¹ᵁ V := h1.trans ((x a).preimage_mono (Y.basicOpen_le f))
  have := (isUnit_valR_iff (x a) V h2 f).2 h1
  rw [valR_eq _ _ h2, hf a h2] at this
  exact (not_isUnit_zero this).elim

theorem comp_eq_of_const {k R : Type} [CommRing k] [CommRing R] {X Y : Scheme.{0}} (p : X ⟶ Sp k)
    (p' : Y ⟶ Sp k) (x : Sp R ⟶ X) (y : Sp R ⟶ Y) {U : X.Opens} {V : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ y ⁻¹ᵁ V) (e : ∀ a, valHom x U h (constFn p U a) = valHom y V h' (constFn p' V a)) :
    x ≫ p = y ≫ p' := by
  refine eq_of_valHom_eq _ _ ⊤ (isAffineOpen_top _) le_top le_top (RingHom.ext fun f => ?_)
  obtain ⟨a, rfl⟩ := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective f
  have := e a
  rw [valHom_constFn, valHom_constFn] at this
  exact this

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {p' : Y ⟶ Sp k} {H : LB X} {H' : LB Y}
  {J : Type} {s : J → H.Sec} {s' : J → H'.Sec}

theorem exists_chart [IsReduced Y] (hH : H.IsLB) (hH' : H'.IsLB) (hI : ImmBy p H s Set.univ)
    {K : Type} [Field K] {A : Type} (x : A → (Sp K ⟶ Y)) (x' : A → (Sp K ⟶ X))
    (hd : Dense (⋃ a, Set.range (x a)))
    (hx : ∀ a, x' a ≫ p = x a ≫ p' ∧ ∃ v, Crd H' s' (x a) v ∧ Crd H s (x' a) v) (i : J) :
    ∃ g : (nonzeroLocus (s' i)).toScheme ⟶ X, ∀ (R : Type) [CommRing R] [IsLocalRing R]
      (y : Sp R ⟶ (nonzeroLocus (s' i)).toScheme),
      (y ≫ g) ≫ p = (y ≫ (nonzeroLocus (s' i)).ι) ≫ p' ∧
        ∀ v, Crd H' s' (y ≫ (nonzeroLocus (s' i)).ι) v → Crd H s (y ≫ g) v := by
  obtain ⟨hA, r, hr, hc⟩ := hI.2 i (Set.mem_univ i)
  choose r' hr' using fun j =>
    (GlobalTheory.SecRatio.existsUnique_isRatio hH' (s' j) (s' i) (nonzeroLocus (s' i)) le_rfl).exists
  let ev := MvPolynomial.eval₂Hom (constHom p (nonzeroLocus (s i))) r
  let ev' := MvPolynomial.eval₂Hom (constHom p' (nonzeroLocus (s' i))) r'
  have hs : Function.Surjective ev := by
    rw [← RingHom.range_eq_top, eq_top_iff, ← hc, Subring.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩
    · exact ⟨MvPolynomial.X j, MvPolynomial.eval₂Hom_X' _ _ _⟩
  have hk : RingHom.ker ev ≤ RingHom.ker ev' := by
    intro f hf
    refine eq_zero_of_dense x hd _ _ fun a h => ?_
    obtain ⟨e, v, hv', hv⟩ := hx a
    have hu : IsUnit (v i) := (crd_isUnit_iff i hv').2 h
    have h' := (crd_isUnit_iff i hv).1 hu
    have : (valHom (x a) _ h).comp ev' = (valHom (x' a) _ h').comp ev := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) fun j => ?_
      · simp only [ev, ev', RingHom.comp_apply, MvPolynomial.eval₂Hom_C, constHom_apply,
          valHom_constFn, e]
      · simp only [ev, ev', RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
        have e := (crd_ratio hv' (hr' j) h).symm.trans (crd_ratio hv (hr j) h')
        rw [valR_eq _ _ h, valR_eq _ _ h'] at e
        exact hu.mul_right_cancel e
    have := congrArg (fun q => q f) this
    simp only [RingHom.comp_apply] at this
    rw [this, (RingHom.mem_ker).1 hf, map_zero]
  let φ := RingHom.liftOfSurjective ev hs ⟨ev', hk⟩
  have hφ : ∀ f, φ (ev f) = ev' f := fun f => RingHom.liftOfSurjective_comp_apply ev hs ⟨ev', hk⟩ f
  have hφc : ∀ a, φ (constFn p _ a) = constFn p' _ a := fun a => by
    have := hφ (MvPolynomial.C a)
    simpa only [ev, ev', MvPolynomial.eval₂Hom_C, constHom_apply] using this
  have hφr : ∀ j, φ (r j) = r' j := fun j => by
    have := hφ (MvPolynomial.X j)
    simpa only [ev, ev', MvPolynomial.eval₂Hom_X'] using this
  obtain ⟨g, hg⟩ := exists_hom_of_ringHom hA _ φ
  refine ⟨g, fun R _ _ y => ?_⟩
  have h : ⊤ ≤ (y ≫ (nonzeroLocus (s' i)).ι) ⁻¹ᵁ nonzeroLocus (s' i) := fun z _ => (y z).2
  obtain ⟨h', hv⟩ := hg R y h
  refine ⟨comp_eq_of_const p p' _ _ h' h fun a => by rw [hv, hφc], fun v hv' => ?_⟩
  obtain ⟨w, hw⟩ := crd_exists hH s (y ≫ g)
  have hu : IsUnit (v i) := (crd_isUnit_iff i hv').2 h
  have hu' : IsUnit (w i) := (crd_isUnit_iff i hw).2 h'
  have := crd_smul (hu.unit * hu'.unit⁻¹) hw
  convert this using 2 with j
  rw [crd_ratio hv' (hr' j) h, crd_ratio hw (hr j) h', valR_eq _ _ h, valR_eq _ _ h', hv, hφr,
    mul_left_comm, Units.val_mul, _root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one, IsUnit.unit_spec]

theorem exists_factor : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsReduced Y] (p : X ⟶ Sp k) (p' : Y ⟶ Sp k) (H : LB X) (H' : LB Y) (J : Type) [Fintype J] (s : J → H.Sec) (s' : J → H'.Sec), H.IsLB → H'.IsLB → ImmBy p H s Set.univ → ⨆ j, nonzeroLocus (s' j) = ⊤ → ∀ (K : Type) [Field K] (A : Type) (x : A → (Sp K ⟶ Y)) (x' : A → (Sp K ⟶ X)), Dense (⋃ a, Set.range (x a)) → (∀ a, x' a ≫ p = x a ≫ p' ∧ ∃ v, Crd H' s' (x a) v ∧ Crd H s (x' a) v) → ∃ g : Y ⟶ X, g ≫ p = p' ∧ (∀ a, x a ≫ g = x' a) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ Y) (v : J → R), Crd H' s' y v → Crd H s (y ≫ g) v := by
  intro k _ X Y _ p p' H H' J _ s s' hH hH' hI hc K _ A x x' hd hx
  choose g hg using exists_chart hH hH' hI x x' hd hx
  let 𝒰 := Y.openCoverOfIsOpenCover (fun j => nonzeroLocus (s' j)) hc
  have hcomp : ∀ i j : J, pullback.fst (nonzeroLocus (s' i)).ι (nonzeroLocus (s' j)).ι ≫ g i =
      pullback.snd (nonzeroLocus (s' i)).ι (nonzeroLocus (s' j)).ι ≫ g j := by
    intro i j
    refine ext_local _ _ fun R _ _ y => ?_
    have e : (y ≫ pullback.fst _ _) ≫ (nonzeroLocus (s' i)).ι =
        (y ≫ pullback.snd _ _) ≫ (nonzeroLocus (s' j)).ι := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    obtain ⟨a₁, b₁⟩ := hg i R (y ≫ pullback.fst _ _)
    obtain ⟨a₂, b₂⟩ := hg j R (y ≫ pullback.snd _ _)
    obtain ⟨v, hv⟩ := crd_exists hH' s' ((y ≫ pullback.fst _ _) ≫ (nonzeroLocus (s' i)).ι)
    rw [← Category.assoc, ← Category.assoc]
    exact eq_of_crd_eq k X p H J s _ hH hI R _ _ v (by rw [a₁, a₂, e]) (b₁ v hv) (b₂ v (e ▸ hv))
  have hG : ∀ i, (nonzeroLocus (s' i)).ι ≫ 𝒰.glueMorphisms g hcomp = g i :=
    fun i => 𝒰.ι_glueMorphisms g hcomp i
  have key : ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ Y),
      (y ≫ 𝒰.glueMorphisms g hcomp) ≫ p = y ≫ p' ∧
        ∀ v, Crd H' s' y v → Crd H s (y ≫ 𝒰.glueMorphisms g hcomp) v := by
    intro R _ _ y
    have : y (IsLocalRing.closedPoint R) ∈ ⨆ j, nonzeroLocus (s' j) := by rw [hc]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    have h := (top_le_iff y _).2 hi
    have hr : Set.range y ⊆ Set.range (nonzeroLocus (s' i)).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      exact h (Set.mem_univ z)
    have e := IsOpenImmersion.lift_fac (nonzeroLocus (s' i)).ι y hr
    have := hg i R (IsOpenImmersion.lift (nonzeroLocus (s' i)).ι y hr)
    rwa [← hG i, ← Category.assoc, e] at this
  refine ⟨𝒰.glueMorphisms g hcomp, ext_local _ _ fun R _ _ y => ?_, fun a => ?_,
    fun R _ _ y => (key R y).2⟩
  · rw [← Category.assoc, (key R y).1]
  · obtain ⟨e, v, hv', hv⟩ := hx a
    exact eq_of_crd_eq k X p H J s _ hH hI K _ _ v (by rw [(key K (x a)).1, e]) ((key K (x a)).2 v hv') hv

end GlobalTheory.ZH.ToImm
end
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open FrameMove ConstFam ThetaPtMove

theorem exists_frames_move_through {S S' : Scheme.{0}} {f : S' ⟶ S} {P : PolAV S} {P' : PolAV S'}
    {φ : P'.A.left ⟶ P.A.left} {w : LB.Iso P'.L (P.L.pull φ)} {T : Over S} {T' : Over S'} {h : T'.left ⟶ T.left}
    (gp : IsGrpPullback P'.A P.A f φ) (hw : w.IsGen)
    {rig : LB.Gen (P.L.pull (eSec P.A))} (hrig : rig.IsGen) {I : Type} {x : I → (T ⟶ P.A)} {x' : I → (T' ⟶ P'.A)}
    (hx : ∀ i, (x' i).left ≫ φ = h ≫ (x i).left) {n : ℕ}
    {τ : ∀ i, LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (x i).left) (fun _ => 1))}
    (H : ∀ i, IsTorsFrame P rig n (x i) (τ i)) :
    ∃ (rig' : LB.Gen (P'.L.pull (eSec P'.A)))
      (τ' : ∀ i, LB.Gen (LB.LinComb P'.L (Y := T'.left) (K := Fin 1) (fun _ => (x' i).left) (fun _ => 1))),
      rig'.IsGen ∧ GenThrough w (fun _ : PUnit => eSec P'.A) (fun _ : PUnit => eSec P.A) (fun _ => 1) rig' rig f ∧
        ∀ i, IsTorsFrame P' rig' n (x' i) (τ' i) ∧
          GenThrough w (fun _ : Fin 1 => (x' i).left) (fun _ : Fin 1 => (x i).left) (fun _ => 1) (τ' i) (τ i) h := by
  obtain ⟨rig', hrig', Hr⟩ := exists_gen_through (K := PUnit) (φ' := fun _ => eSec P'.A) (φ := fun _ => eSec P.A)
    (ε := fun _ => 1) (h := f) hw P.isLB P'.isLB (fun _ => PolBaseChange.eSec_comm gp) rig hrig
  choose τ' hτ' Hτ using fun i => exists_gen_through (φ' := fun _ : Fin 1 => (x' i).left) (h := h) hw P.isLB P'.isLB
    (fun _ => hx i) (τ i) (H i).2.1
  have ht : ∀ i (z : T'.left) J J', Good P.L z J → Good P'.L z J' →
      val (τ i) h z J = wVal w z J J' (x' i).left * val (τ' i) (𝟙 _) z J' := fun i z J J' hJ hJ' => by
    have := Hτ i _ (𝟙 _) z J J' hJ hJ'
    rwa [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at this
  have hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S')).left) (z : Z) J J', Good P.L z J → Good P'.L z J' →
      rval rig (r ≫ f) z J = wVal w z J J' (r ≫ eSec P'.A) * rval rig' r z J' := fun Z r z J J' hJ hJ' =>
    (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _)))
  exact ⟨rig', τ', hrig', Hr, fun i => ⟨isTorsFrame_move gp hw hr (hx i) (H i) (hτ' i) (ht i), Hτ i⟩⟩

theorem exists_frames_on_fibre_through : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → ∀ w : LB.Iso u.A.L (ρ.P.L.pull u.φ), w.IsGen → ∃ (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrAt (x a)), rig.IsGen ∧ GlobalTheory.ThetaPtMove.GenThrough w (fun _ : PUnit => eSec u.A.A) (fun _ : PUnit => eSec ρ.P.A) (fun _ => 1) rig ρ.rig (spMap u.yK) ∧ ∀ a, IsTorsFrame u.A rig (S.r * S.N) (x a) (e a) ∧ GlobalTheory.ThetaPtMove.GenThrough w (fun _ : Fin 1 => (x a).left) (fun _ : Fin 1 => (ρ.pt a).left) (fun _ => 1) (e a) (ρ.fr a) (spMap y₀) := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u x hx w hw
  exact exists_frames_move_through (T := baseOver (Sp S.R)) (T' := TFK (R := u.V) (PadicAlgCl p))
    u.cart hw ρ.rig_gen hx ρ.fr_tors

end GlobalTheory
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem _root_.GlobalTheory.T.psi_relation_descends_field_extension : GlobalFnsSt → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K) (hD : IsPullDeg i D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] (oa : D.OAct O) (oa' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (oa'.onB.act a).left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ (oa.onB.act a).left) → ∀ w : O, TraceFormTwistIso D' oa' w → TraceFormTwistIso D oa w := by
  first | exact @GlobalTheory.psi_relation_descend_field | exact GlobalTheory.psi_relation_descend_field | (intros; apply GlobalTheory.psi_relation_descend_field <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isoFree_perp_labelKernel_weights : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (yy : S.Gam →+ u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range), Function.Surjective yy → (∀ (a : S.Gam) (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) → S.IsoFree (S.perp yy.ker) ∧ ∃ wt : u.D.toPre.X →+ (S.perp yy.ker →+ ZMod S.N), ∀ (x : S.Gam) (α : u.D.toPre.X), yy x = QuotientAddGroup.mk α → ∀ t : S.perp yy.ker, wt α t = ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ t x) := by
  first | exact @GlobalTheory.ZH.TorusPerp.isoFree_perp_and_weights | exact GlobalTheory.ZH.TorusPerp.isoFree_perp_and_weights | (intros; apply GlobalTheory.ZH.TorusPerp.isoFree_perp_and_weights <;> assumption)
end
