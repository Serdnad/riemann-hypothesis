module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.DedekindDomain.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle154
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace CoverDenseAlt

theorem dualMap_comp_dualMap' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') : (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
  ext a <;> simp [dualMap]

theorem dualMap_comp_epsMul_ample_line_bundles {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (s : R) :
    (dualMap f).comp (GlobalTheory.CompanionTheory.Ar.epsMul s) = (GlobalTheory.CompanionTheory.Ar.epsMul (f s)).comp (dualMap f) := by
  ext a <;> simp [dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem spMap_comp_spMap_ample_line_bundles {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') : spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem tangent_vector_extends_over_integers : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (S : Scheme.{0}) (x : Sp O ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (E : Type) [AddCommGroup E] [Module O E] (M : LieModel G x E) (v : epsAt (spMap (algebraMap O K) ≫ x) ⟶ G), IsTanAt G _ v → (∀ (P : Ideal O) [P.IsMaximal] (c : Localization.AtPrime P →+* K), c.comp (algebraMap O _) = algebraMap O K → ∃ w : epsAt (spMap (algebraMap O (Localization.AtPrime P)) ≫ x) ⟶ G, IsTanAt G _ w ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ w.left) → ∃ e, (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M.pt e).left) := by
  intro O K _ _ _ _ _ S x G _ _ _ E _ _ M v hv hloc
  obtain ⟨EK, _, _, ⟨MK⟩⟩ := lieModel_exists S G K (spMap (algebraMap O K) ≫ x)
  obtain ⟨jK, hjK, -⟩ := LieBaseChange.existsUnique_semilinear_lifts S G O K (algebraMap O K) x E EK M MK
  obtain ⟨eK, rfl⟩ := MK.onto v hv
  let I : Ideal O :=
    { carrier := {a | ∃ e, jK e = algebraMap O K a • eK}
      add_mem' := by
        rintro a b ⟨e, he⟩ ⟨e', he'⟩
        exact ⟨e + e', by rw [map_add (f := _), he, he', map_add (f := _), add_smul]⟩
      zero_mem' := ⟨0, by rw [map_zero, map_zero, zero_smul]⟩
      smul_mem' := by
        rintro a b ⟨e, he⟩
        refine ⟨a • e, ?_⟩
        rw [jK.map_smulₛₗ, he, smul_eq_mul, map_mul, mul_smul] }
  suffices h1 : (1 : O) ∈ I by
    obtain ⟨e, he⟩ := h1
    rw [map_one, one_smul] at he
    refine ⟨e, ?_⟩
    rw [← he]
    exact hjK e
  by_contra h1
  obtain ⟨P, hP, hIP⟩ := I.exists_le_maximal ((Ideal.ne_top_iff_one I).2 h1)
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap O K y) := by
    intro y
    refine IsUnit.mk0 _ ?_
    intro h0
    have h2 : (y : O) = 0 := IsFractionRing.injective O K (by rw [h0, map_zero])
    exact y.2 (h2 ▸ P.zero_mem)
  let c : Localization.AtPrime P →+* K := IsLocalization.lift hunit
  have hc : c.comp (algebraMap O (Localization.AtPrime P)) = algebraMap O K := IsLocalization.lift_comp hunit
  obtain ⟨w, hw, hvw⟩ := hloc P c hc
  obtain ⟨EP, _, _, ⟨MP⟩⟩ := lieModel_exists S G (Localization.AtPrime P)
    (spMap (algebraMap O (Localization.AtPrime P)) ≫ x)
  obtain ⟨jP, hjP, -⟩ := LieBaseChange.existsUnique_semilinear_lifts S G O (Localization.AtPrime P)
    (algebraMap O (Localization.AtPrime P)) x E EP M MP
  obtain ⟨eP, rfl⟩ := MP.onto w hw
  letI : Module O EP := Module.compHom EP (algebraMap O (Localization.AtPrime P))
  haveI : IsScalarTower O (Localization.AtPrime P) EP := ⟨fun a b m => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  let β : E →ₗ[O] EP :=
    { toFun := jP
      map_add' := map_add jP
      map_smul' := fun a e => by
        rw [jP.map_smulₛₗ]
        rfl }
  have hbc : IsBaseChange (Localization.AtPrime P) β :=
    (LieProj.lie_finite_projective_baseChange S G O x E M).2.2 (Localization.AtPrime P) EP MP β
      (fun e => by
        have h2 := hjP e
        simp only [LieModel.Lifts, Category.comp_id] at h2
        exact h2)
  haveI : IsLocalizedModule P.primeCompl β :=
    (isLocalizedModule_iff_isBaseChange P.primeCompl (Localization.AtPrime P) β).2 hbc
  obtain ⟨⟨e, s⟩, hes⟩ := IsLocalizedModule.surj P.primeCompl β eP
  have hes' : jP e = algebraMap O (Localization.AtPrime P) (s : O) • eP := hes.symm
  have hmem : (s : O) ∈ I := by
    refine ⟨e, ?_⟩
    apply MK.inj
    apply Over.OverMorphism.ext
    have h1 := hjK e
    have h2 := hjP e
    simp only [LieModel.Lifts, Category.comp_id] at h1 h2
    have h3 : (MK.pt (jK e)).left = spMap (dualMap c) ≫ (MP.pt (jP e)).left := by
      rw [h1, h2, ← Category.assoc, spMap_comp_spMap_ample_line_bundles, dualMap_comp_dualMap', hc]
    rw [h3, hes', MP.smul, MK.smul, hvw, ← Category.assoc, ← Category.assoc]
    congr 1
    have h4 := spMap_comp_spMap_ample_line_bundles (GlobalTheory.CompanionTheory.Ar.epsMul (algebraMap O (Localization.AtPrime P) (s : O))) (dualMap c)
    have h5 := spMap_comp_spMap_ample_line_bundles (dualMap c) (GlobalTheory.CompanionTheory.Ar.epsMul (c (algebraMap O (Localization.AtPrime P) (s : O))))
    rw [← RingHom.comp_apply c, hc] at h5
    simp only [spMap] at h4 h5 ⊢
    rw [h4, dualMap_comp_epsMul_ample_line_bundles, h5]
    rw [← RingHom.comp_apply c, hc]
  exact s.2 (hIP hmem)

end CoverDenseAlt
end

section

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace CoverDenseAlt

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR
  ReciprocityTheory.ChartRestriction.G.DVR.FlatBC ReciprocityTheory.ChartRestriction.G

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {X X' : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of R)) (p' : X' ⟶ Spec (CommRingCat.of S)) (φ : X' ⟶ X)
  (H : IsPullback φ p' p (Spec.map (CommRingCat.ofHom (algebraMap R S))))

include H in
theorem exists_sec_of_flat_pull [Module.Flat R S] [CompactSpace X]
    (hinter : ∀ U W : X.Opens, IsAffineOpen U → IsAffineOpen W → IsAffineOpen (U ⊓ W))
    (L : LB X) (hL : L.IsLB) (σ' : LB.Sec (L.pull φ)) (y : X') (hy : y ∈ Out.nonzeroLocus σ') :
    ∃ σ : LB.Sec L, φ y ∈ Out.nonzeroLocus σ := by
  classical
  obtain ⟨n, V, c, hVa, hVc, hcov⟩ := exists_affine_chart_cover L hL
  letI instV : ∀ k, Algebra R Γ(X, V k) := fun k => (algX p (V k)).toAlgebra
  letI instW : ∀ kl : Fin n × Fin n, Algebra R Γ(X, V kl.1 ⊓ V kl.2) := fun kl => (algX p _).toAlgebra
  let δ : (∀ k, Γ(X, V k)) →ₗ[R] (∀ kl : Fin n × Fin n, Γ(X, V kl.1 ⊓ V kl.2)) :=
    { toFun := fun f kl => dfun L V c hVc f kl.1 kl.2
      map_add' := fun f g => by
        funext kl
        simp only [dfun, Pi.add_apply, map_add (f := _), mul_add]
        abel
      map_smul' := fun r f => by
        funext kl
        simp only [dfun, RingHom.id_apply, Pi.smul_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
        rw [rs_mul, rs_mul, rs_algX, rs_algX]
        ring }
  have hδ : ∀ m, δ m = 0 ↔ dfun L V c hVc m = 0 := fun m => by
    constructor
    · intro h; funext k l; exact congrFun h (k, l)
    · intro h; funext kl; exact congrFun (congrFun h kl.1) kl.2
  have hV'c : ∀ k, φ ⁻¹ᵁ V k ⊓ p' ⁻¹ᵁ ⊤ ≤ (L.pull φ).U (fun _ => c k) := fun k y hy =>
    Set.mem_iInter.2 fun _ => hVc k hy.1
  let m' : ∀ k, Γ(X', φ ⁻¹ᵁ V k ⊓ p' ⁻¹ᵁ ⊤) := fun k => rs (hV'c k) (σ'.f (fun _ => c k))
  let t : (∀ k, Γ(X, V k)) ⊗[R] S := (TensorProduct.piLeft (R := R) (N := S) (M := fun k => Γ(X, V k))).symm
    (fun k => (eTens p p' φ H (V k) (hVa k)).symm (m' k))
  have hpt : ∀ k, (TensorProduct.piLeft (R := R) (N := S) (M := fun k => Γ(X, V k))) t k =
      (eTens p p' φ H (V k) (hVa k)).symm (m' k) := fun k => by
    simp only [t, LinearEquiv.apply_symm_apply]
  have ht : δ.rTensor S t = 0 := by
    apply (TensorProduct.piLeft (R := R) (N := S) (M := fun kl : Fin n × Fin n => Γ(X, V kl.1 ⊓ V kl.2))).injective
    rw [map_zero]
    funext kl
    obtain ⟨k, l⟩ := kl
    rw [piLeft_apply_eq, ← LinearMap.rTensor_comp_apply]
    have hdec : (LinearMap.proj (k, l) : (∀ kl : Fin n × Fin n, Γ(X, V kl.1 ⊓ V kl.2)) →ₗ[R] _).comp δ =
        (rsL p (V k) (V k ⊓ V l) inf_le_left).comp (LinearMap.proj k) -
          (mulL p (V k ⊓ V l) (res (pair_le L V c hVc k l) (L.g (c k) (c l))).val).comp
            ((rsL p (V l) (V k ⊓ V l) inf_le_right).comp (LinearMap.proj l)) := by
      apply LinearMap.ext
      intro f
      rfl
    rw [hdec, LinearMap.rTensor_sub, LinearMap.sub_apply, LinearMap.rTensor_comp_apply, LinearMap.rTensor_comp_apply,
      LinearMap.rTensor_comp_apply, ← piLeft_apply_eq, ← piLeft_apply_eq, hpt, hpt]
    apply (eTens p p' φ H (V k ⊓ V l) (hinter _ _ (hVa k) (hVa l))).injective
    rw [map_sub, eTens_rs p p' φ H (V k) (V k ⊓ V l) (hVa k) _ inf_le_left, eTens_mul,
      eTens_rs p p' φ H (V l) (V k ⊓ V l) (hVa l) _ inf_le_right, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply, Pi.zero_apply, map_zero, sub_eq_zero]
    refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.fn_ext fun y hy => ?_
    have hyk : y ∈ (L.pull φ).U (fun _ => c k) := Set.mem_iInter.2 fun _ => hVc k hy.1.1
    have hyl : y ∈ (L.pull φ).U (fun _ => c l) := Set.mem_iInter.2 fun _ => hVc l hy.1.2
    have hyk' : y ∈ φ ⁻¹ᵁ V k ⊓ p' ⁻¹ᵁ ⊤ := ⟨hy.1.1, hy.2⟩
    have hyl' : y ∈ φ ⁻¹ᵁ V l ⊓ p' ⁻¹ᵁ ⊤ := ⟨hy.1.2, hy.2⟩
    have hφy : φ y ∈ V k ⊓ V l := hy.1
    simp only [m']
    rw [Geo.Tor.gs_mul _ y _ hy, Geo.Tor.gs_res _ y _ hy, Geo.Tor.gs_res _ y _ hyk', Geo.Tor.gs_res _ y _ hy,
      Geo.Tor.gs_res _ y _ hyl', Geo.Tor.gs_appLE φ _ _ _ (𝟙 _) y hy]
    erw [Category.id_comp, Geo.Tor.gs_unit _ y _ hφy, Geo.Tor.gm_res _ y _ hφy]
    erw [gs_sec (L.pull φ) σ' (fun _ => c k) (fun _ => c l) y hyk hyl,
      Geo.Tor.gm_pull_g L φ (𝟙 _) y (fun _ => c k) (fun _ => c l) hyk hyl, Category.id_comp]
  obtain ⟨x, hx⟩ := (Module.Flat.rTensor_exact S (LinearMap.exact_subtype_ker_map δ) t).1 ht
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (show φ y ∈ (⨆ k, V k : X.Opens) by rw [hcov]; trivial)
  have key : ∀ x : (LinearMap.ker δ) ⊗[R] S, y ∈ X'.basicOpen (eTens p p' φ H (V k) (hVa k)
      ((TensorProduct.piLeft (R := R) (N := S) (M := fun k => Γ(X, V k))) ((LinearMap.ker δ).subtype.rTensor S x) k)) →
      ∃ σ : LB.Sec L, φ y ∈ Out.nonzeroLocus σ := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
      intro h
      rw [map_zero, map_zero, Pi.zero_apply, (eTens p p' φ H (V k) (hVa k)).map_zero, Scheme.basicOpen_zero] at h
      exact h.elim
    | tmul m s =>
      intro h
      rw [LinearMap.rTensor_tmul, piLeft_apply_eq, LinearMap.rTensor_tmul, eTens_tmul, Scheme.basicOpen_mul] at h
      have h1 := h.1
      erw [Scheme.basicOpen_appLE] at h1
      obtain ⟨σ, hσ⟩ := exists_glue L V c hVc hL hcov m.1 ((hδ _).1 m.2)
      refine ⟨σ, GlobalTheory.basicOpen_le_nonzeroLocus σ (c k) ?_⟩
      have h2 : φ y ∈ X.basicOpen (m.1 k) := h1.2
      rw [← hσ] at h2
      simp only [ev, rs] at h2
      erw [Scheme.basicOpen_res] at h2
      exact h2.2
    | add x₁ x₂ h₁ h₂ =>
      intro h
      rw [map_add (f := _), map_add (f := _), Pi.add_apply, map_add (f := _)] at h
      rcases Scheme.basicOpen_add_le _ _ _ h with h | h
      exacts [h₁ h, h₂ h]
  apply key x
  rw [hx, hpt, RingEquiv.apply_symm_apply]
  have hyk : y ∈ φ ⁻¹ᵁ V k ⊓ p' ⁻¹ᵁ ⊤ := ⟨hk, trivial⟩
  simp only [m', rs]
  erw [Scheme.basicOpen_res]
  exact ⟨hyk, (GlobalTheory.mem_nonzeroLocus_iff_basicOpen σ' (hV'c k hyk)).1 hy⟩

end CoverDenseAlt
end
end
