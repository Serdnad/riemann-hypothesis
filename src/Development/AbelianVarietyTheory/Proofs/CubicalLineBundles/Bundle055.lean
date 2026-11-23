module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle030
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle039
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle053
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle033
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle037
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle054
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.LocModelLie

section Alg

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R K] [IsFractionRing R K]

theorem exists_ringHom : ∃ f : 𝓞 K →+* R, ∀ x, algebraMap R K (f x) = algebraMap (𝓞 K) K x := by
  have h : ∀ x : 𝓞 K, algebraMap (𝓞 K) K x ∈ (algebraMap R K).range := fun x =>
    IsIntegrallyClosed.isIntegral_iff.1 (x.isIntegral_coe.tower_top (A := R))
  let e := RingEquiv.ofBijective (algebraMap R K).rangeRestrict
    ⟨fun a b hab => IsFractionRing.injective R K (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
  refine ⟨e.symm.toRingHom.comp ((algebraMap (𝓞 K) K).codRestrict _ h), fun x => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ⟨_, h x⟩)

theorem isUnit_of_valuation_eq_one (𝔭 : HeightOneSpectrum (𝓞 K))
    (hR : ∀ r : R, 𝔭.valuation K (algebraMap R K r) ≤ 1) {r : R} (hr : 𝔭.valuation K (algebraMap R K r) = 1) :
    IsUnit r := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hu : ∀ u : Rˣ, 𝔭.valuation K (algebraMap R K u) = 1 := fun u => by
    refine eq_one_of_one_le_mul_left (hR (u : R)) (hR (u⁻¹ : Rˣ)) ?_
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have hlt : 𝔭.valuation K (algebraMap R K ϖ) ≠ 1 := fun h1 => by
    have hall : ∀ s : R, s ≠ 0 → 𝔭.valuation K (algebraMap R K s) = 1 := fun s hs => by
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs hϖ
      rw [map_mul, map_mul, map_pow, map_pow, hu, h1, one_pow, _root_.mul_one]
    obtain ⟨π, hπ⟩ := 𝔭.valuation_exists_uniformizer K
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) π
    by_cases ha : a = 0
    · rw [ha, map_zero, zero_div, map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    · rw [map_div₀, hall a ha, hall b (nonZeroDivisors.ne_zero hb), div_one, ← WithZero.exp_zero,
        WithZero.exp_inj] at hπ
      omega
  have h0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at hr
    exact zero_ne_one hr
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  rw [map_mul, map_mul, map_pow, map_pow, hu, _root_.one_mul] at hr
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simp
  · exact absurd ((pow_eq_one_iff_of_nonneg zero_le hn.ne').1 hr) hlt

theorem isLocalization [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) R K] (𝔭 : HeightOneSpectrum (𝓞 K))
    (hR : ∀ r : R, 𝔭.valuation K (algebraMap R K r) ≤ 1) : IsLocalization 𝔭.asIdeal.primeCompl R := by
  refine (isLocalization_iff _ _).2 ⟨fun s => isUnit_of_valuation_eq_one 𝔭 hR ?_, fun r => ?_, fun {x y} h => ⟨1, ?_⟩⟩
  · rw [← IsScalarTower.algebraMap_apply]
    exact 𝔭.valuation_eq_one_iff_notMem.2 s.2
  · obtain ⟨n, d, h⟩ := 𝔭.exists_primeCompl_mul_eq_of_integer _ (hR r)
    refine ⟨(n, d), IsFractionRing.injective R K ?_⟩
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, h]
  · have := congrArg (algebraMap R K) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    rw [IsFractionRing.injective (𝓞 K) K this]

end Alg

theorem exists_iso_of_models (h : HomExtDvr) (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G']
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G') (H : Over (Sp K)) [GrpObj H] {ψ : H.left ⟶ G.left}
    {ψ' : H.left ⟶ G'.left} (hψ : IsGrpPullback H G (spMap (algebraMap T K)) ψ)
    (hψ' : IsGrpPullback H G' (spMap (algebraMap T K)) ψ') :
    ∃ e : G ≅ G', IsMonHom e.hom ∧ ψ ≫ e.hom.left = ψ' := by
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso hψ (isGrpPullback_pullback G _)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hψ' (isGrpPullback_pullback G' _)
  let f := a.symm ≪≫ b
  have hf : IsMonHom f.hom := by
    change IsMonHom (a.inv ≫ b.hom)
    infer_instance
  obtain ⟨F, ⟨hF, eF⟩, -⟩ := h T K G G' hG hG' f.hom hf
  obtain ⟨F', ⟨hF', eF'⟩, -⟩ := h T K G' G hG' hG f.inv inferInstance
  refine ⟨⟨F, F', (h T K G G hG hG (𝟙 _) inferInstance).unique ⟨inferInstance, ?_⟩
      ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩,
    (h T K G' G' hG' hG' (𝟙 _) inferInstance).unique ⟨inferInstance, ?_⟩
      ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩⟩, hF, ?_⟩
  · rw [Functor.map_comp, eF, eF']
    exact f.hom_inv_id
  · rw [Functor.map_comp, eF, eF']
    exact f.inv_hom_id
  · have A : ((Over.pullback (spMap (algebraMap T K))).map F).left ≫ pullback.fst G'.hom _ =
        pullback.fst G.hom _ ≫ F.left := pullback.lift_fst _ _ _
    change ψ ≫ F.left = ψ'
    rw [← ha', Category.assoc, ← A, eF, ← hb', ← Category.assoc, ← Over.comp_left]
    congr 2
    exact a.hom_inv_id_assoc _

theorem eq_dualMapR {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (F : DualNumber R →+* DualNumber R')
    (h₁ : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) (h₂ : F DualNumber.eps = DualNumber.eps) :
    F = Chart.dualMapR f := by
  refine RingHom.ext fun x => ?_
  have e : x = algebraMap R _ x.fst + algebraMap R _ x.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  conv_lhs => rw [e, map_add (f := _), map_mul, h₁, h₁, h₂]
  ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.LocModelLie

namespace GlobalTheory.CM

open LocModelLie

theorem lieLat_of_isLocalModel : HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (hg rig hr th hth) (𝔭 : HeightOneSpectrum (𝓞 K)) (a : K) (M : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), KeyPow.IsLocalModel (F.key hg rig hr th hth) 𝔭 a M → (∀ i, ∃ s : 𝓞 K, s ∉ 𝔭.asIdeal ∧ s • M i ∈ F.lieLat) ∧ ∀ c ∈ F.lieLat, ∃ s : 𝓞 K, s ∉ 𝔭.asIdeal ∧ s • c ∈ Submodule.span (𝓞 K) (Set.range fun i => M i) := by
  intro hE K _ _ P F hg rig hr th hth 𝔭 a M
    ⟨R, _, _, _, _, _, y, th', hth', v', hv', hR, _, hM, ψ, _, _, hgg, Φ, hψ, _, _, _, hΦ₁, hΦ₂, hv⟩
  obtain ⟨f, hf⟩ := exists_ringHom (K := K) (R := R)
  letI : Algebra (𝓞 K) R := f.toAlgebra
  haveI : IsScalarTower (𝓞 K) R K := IsScalarTower.of_algebraMap_eq fun x => (hf x).symm
  haveI := isLocalization 𝔭 hR
  obtain rfl := eq_dualMapR _ Φ hΦ₁ hΦ₂
  change F.P₀.g = y.P.g at hgg
  change IsGrpPullback F.P₀.A y.P.A (spMap (algebraMap R K)) ψ at hψ
  have hc : spMap (algebraMap (𝓞 K) K) = spMap (algebraMap R K) ≫ spMap (algebraMap (𝓞 K) R) := by
    rw [IsScalarTower.algebraMap_eq (𝓞 K) R K]
    exact Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)
  have hF := F.fib.2.1.congr hc rfl
  have hp := isGrpPullback_pullback P.A (spMap (algebraMap (𝓞 K) R))
  let ψ' := hp.1.lift F.φ (F.P₀.A.hom ≫ spMap (algebraMap R K)) (by rw [hF.1.w, Category.assoc])
  have hψ' : ψ' ≫ pullback.fst _ _ = F.φ := hp.1.lift_fst _ _ _
  obtain ⟨e, he, hψe⟩ := exists_iso_of_models hE R K y.P.A _ (isSemiAbelian_of_isAbelianScheme _ y.P.isAb)
    (IsSemiAbelian.pullback _ _ (isSemiAbelian_of_isAbelianScheme _ P.isAb)) F.P₀.A hψ
    (IsGrpPullback.cancel hp (hF.congr rfl hψ'.symm) (hp.1.lift_snd _ _ _))
  have hb : IsLieBasis fun i : Fin F.P₀.g => y.v (i.cast hgg) := by
    have : ∀ (n : ℕ) (h : n = y.P.g), IsLieBasis fun i : Fin n => y.v (i.cast h) := by
      rintro _ rfl
      exact y.basis
    exact this _ _
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.lieLattice_localization_modelLieAlgebra K P F R 𝔭.asIdeal.primeCompl y.P.A (e.hom.left ≫ pullback.fst _ _) ψ _ v' M
    (((isGrpPullback_of_iso e).comp hp).congr (Category.id_comp _) rfl) hψ
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst _ _) hψe).trans hψ')) hb (fun i => ⟨hv i, hM i⟩)
  refine ⟨h₁, fun c hc => ?_⟩
  obtain ⟨b, rfl⟩ := h₂ c hc
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite 𝔭.asIdeal.primeCompl b
  refine ⟨s, s.2, ?_⟩
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨t, ht⟩ := hs i
  have : (s : 𝓞 K) • algebraMap R K (b i) • M i = t • M i := by
    have e : algebraMap (𝓞 K) K t = algebraMap (𝓞 K) K s * algebraMap R K (b i) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 K) R K t, ht, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply]
    rw [← algebraMap_smul K t, e, mul_smul, algebraMap_smul K (s : 𝓞 K)]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory

theorem isFam_extends_dedekind :
    Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (ω : R) (C : Ell H R ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (L : Submodule (𝓞 E) D.La) (ω' : K) (C' : Ell H K ω') (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp K)) (m : SABMap T'.t T.t (spMap (algebraMap R K))) (ψ' : L → (C'.P.A ⟶ T'.t.G)), EllMap C' C (algebraMap R K) φ → IsFam C' T' h L ψ' → ∃ ψ : L → (C.P.A ⟶ T.t.G), IsFam C T h L ψ ∧ ∀ a, (ψ' a).left ≫ m.φ = φ ≫ (ψ a).left := by
  intro hL hD E _ _ _ H R K _ _ _ _ _ ω C D h T L ω' C' φ T' m ψ' hφ hψ'
  have key : ∀ a : L, ∃ F : C.P.A ⟶ T.t.G, (ψ' a).left ≫ m.φ = φ ≫ F.left := fun a => by
    obtain ⟨F, -, hF, -⟩ := abelianScheme_hom_extends_dedekind_of_isGrpPullback hD R K C.P.A T.t.G C'.P.A T'.t.G
      φ m.φ C.P.isAb T.ab hφ.2.1.2.1 m.cart (ψ' a) (hψ'.1 a).isMonHom
    exact ⟨F, hF⟩
  choose ψ hψ using key
  exact ⟨ψ, GlobalTheory.T.family_identities_descend_field_to_dedekind hL E H R ω C D h T L ψ K ω' C' (algebraMap R K) φ T' m ψ'
    (IsFractionRing.injective R K) hφ hψ hψ', hψ⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.FamDesc

theorem exists_field (hT : ThetaUnifAV) (hB : Out.PolBaseChangeSt) (k : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ k] (P Q : Out.PolAV (Sp k)) {G H : Over (Sp ℂ)} [GrpObj G] [GrpObj H]
    {φ : G.left ⟶ P.A.left} {m : H.left ⟶ Q.A.left} (hP : IsGrpPullback G P.A (spMap (algebraMap k ℂ)) φ)
    (hQ : IsGrpPullback H Q.A (spMap (algebraMap k ℂ)) m) (f : G ⟶ H) [IsMonHom f] :
    ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ ∀ (k₂ : IntermediateField ℚ ℂ) (h₂ : k ≤ k₂), k₁ ≤ k₂ →
      ∀ (G₂ H₂ : Over (Sp k₂)) (φ₂ : G₂.left ⟶ P.A.left) (m₂ : H₂.left ⟶ Q.A.left) (φ₃ : G.left ⟶ G₂.left)
        (m₃ : H.left ⟶ H₂.left), φ₂ ≫ P.A.hom = G₂.hom ≫ spMap (IntermediateField.inclusion h₂).toRingHom →
        IsPullback m₂ H₂.hom Q.A.hom (spMap (IntermediateField.inclusion h₂).toRingHom) →
        φ₃ ≫ G₂.hom = G.hom ≫ spMap (algebraMap k₂ ℂ) → m₃ ≫ H₂.hom = H.hom ≫ spMap (algebraMap k₂ ℂ) →
        φ₃ ≫ φ₂ = φ → m₃ ≫ m₂ = m → ∃ f₂ : G₂ ⟶ H₂, f.left ≫ m₃ = φ₃ ≫ f₂.left := by
  obtain ⟨e, he, he'⟩ := grpPullback_iso hP (isGrpPullback_pullback P.A _)
  obtain ⟨d, hd, hd'⟩ := grpPullback_iso hQ (isGrpPullback_pullback Q.A _)
  obtain ⟨K, f₁, j, hK, -, j₁, j₂, j₃⟩ := hom_descends_to_numberField hT hB k P Q (e.inv ≫ f ≫ d.hom) inferInstance
  have : IsScalarTower ℚ k K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hfin : FiniteDimensional ℚ K := Module.Finite.trans k K
  refine ⟨K.restrictScalars ℚ, hfin, fun k₂ h₂ h₁ G₂ H₂ φ₂ m₂ φ₃ m₃ w₂ c₂ w₃ v₃ e₃ d₃ => ?_⟩
  let q : K →+* k₂ := (IntermediateField.inclusion h₁).toRingHom
  have s₁ : spMap q ≫ spMap (algebraMap k K) = spMap (IntermediateField.inclusion h₂).toRingHom :=
    (spMap_comp_spMap _ _).trans (congrArg spMap (RingHom.ext fun _ => rfl))
  have s₂ : spMap (algebraMap k₂ ℂ) ≫ spMap q = spMap K.val.toRingHom :=
    (spMap_comp_spMap _ _).trans (congrArg spMap (RingHom.ext fun _ => rfl))
  obtain ⟨i, i₁, i₂⟩ : ∃ i : G₂.left ⟶ pullback P.A.hom (spMap (algebraMap k K)),
      i ≫ pullback.fst _ _ = φ₂ ∧ i ≫ pullback.snd _ _ = G₂.hom ≫ spMap q :=
    ⟨pullback.lift φ₂ (G₂.hom ≫ spMap q) (by rw [w₂, Category.assoc, s₁]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  have fw : f₁.left ≫ pullback.snd Q.A.hom (spMap (algebraMap k K)) = pullback.snd _ _ := Over.w f₁
  have ew : e.hom.left ≫ pullback.snd P.A.hom (spMap (algebraMap k ℂ)) = G.hom := Over.w e.hom
  have w : (i ≫ f₁.left ≫ pullback.fst _ _) ≫ Q.A.hom =
      G₂.hom ≫ spMap (IntermediateField.inclusion h₂).toRingHom := by
    have h : f₁.left ≫ pullback.fst Q.A.hom (spMap (algebraMap k K)) ≫ Q.A.hom =
        pullback.snd _ _ ≫ spMap (algebraMap k K) :=
      (congrArg (f₁.left ≫ ·) pullback.condition).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) fw))
    refine (Category.assoc _ _ _).trans ((congrArg (i ≫ ·) ((Category.assoc _ _ _).trans h)).trans ?_)
    rw [← Category.assoc, i₂, Category.assoc, s₁]
  have key : φ₃ ≫ i = e.hom.left ≫ j := by
    apply pullback.hom_ext
    · exact ((Category.assoc _ _ _).trans ((congrArg (φ₃ ≫ ·) i₁).trans e₃)).trans
        ((Category.assoc _ _ _).trans ((congrArg (e.hom.left ≫ ·) j₁).trans he')).symm
    · refine ((Category.assoc _ _ _).trans ((congrArg (φ₃ ≫ ·) i₂).trans ?_)).trans
        ((Category.assoc _ _ _).trans ((congrArg (e.hom.left ≫ ·) j₂).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) ew)))).symm
      rw [← Category.assoc, w₃, Category.assoc, s₂]
  obtain ⟨f₂, hf₂⟩ : ∃ f₂ : G₂ ⟶ H₂, f₂.left ≫ m₂ = i ≫ f₁.left ≫ pullback.fst _ _ :=
    ⟨Over.homMk (c₂.lift _ G₂.hom w) (c₂.lift_snd _ _ _), c₂.lift_fst _ _ _⟩
  refine ⟨f₂, c₂.hom_ext ?_ ?_⟩
  · have r : e.hom.left ≫ (e.inv ≫ f ≫ d.hom).left = f.left ≫ d.hom.left := by
      rw [← Over.comp_left, e.hom_inv_id_assoc, Over.comp_left]
    have a₁ : (φ₃ ≫ f₂.left) ≫ m₂ = e.hom.left ≫ j ≫ f₁.left ≫ pullback.fst _ _ :=
      (Category.assoc _ _ _).trans ((congrArg (φ₃ ≫ ·) hf₂).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) key).trans (Category.assoc _ _ _))))
    rw [a₁, Category.assoc, d₃, ← hd', ← Category.assoc, ← r, Category.assoc]
    exact congrArg (e.hom.left ≫ ·) j₃.symm
  · rw [Category.assoc, Category.assoc, Over.w, v₃, w₃, ← Category.assoc, Over.w]

theorem exists_mul {S S' : Scheme.{0}} {j : S' ⟶ S} {G H : Over S} [GrpObj H] {G' H' : Over S'} [GrpObj H']
    {φ : G'.left ⟶ G.left} {m : H'.left ⟶ H.left} (w : φ ≫ G.hom = G'.hom ≫ j) (hm : IsGrpPullback H' H j m)
    {x' y' : G' ⟶ H'} {x y : G ⟶ H} (hx : x'.left ≫ m = φ ≫ x.left) (hy : y'.left ≫ m = φ ≫ y.left) :
    (x' * y').left ≫ m = φ ≫ (x * y).left := by
  let φ₀ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ w
  have h := hm.2 G' x' y' (φ₀ ≫ x) (φ₀ ≫ y) hx.symm hy.symm
  rw [← MonObj.comp_mul] at h
  rw [← h]
  rfl

end GlobalTheory.CM.FamDesc

namespace GlobalTheory.CM

open FamDesc in
theorem isFam_descends_to_numberField : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (ω : k) (C : Ell H k ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp k)) (L : Submodule (𝓞 E) D.La) (ω' : ℂ) (C' : Ell H ℂ ω') (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp ℂ)) (m : SABMap T'.t T.t (spMap (algebraMap k ℂ))) (ψ' : L → (C'.P.A ⟶ T'.t.G)), EllMap C' C (algebraMap k ℂ) φ → IsFam C' T' h L ψ' →
  ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧ ∀ (k₂ : IntermediateField ℚ ℂ) (h₂ : k ≤ k₂), k₁ ≤ k₂ → ∀ (ω₂ : k₂) (C₂ : Ell H k₂ ω₂) (φ₂ : C₂.P.A.left ⟶ C.P.A.left) (φ₃ : C'.P.A.left ⟶ C₂.P.A.left) (T₂ : PAT H (Sp k₂)) (m₂ : SABMap T₂.t T.t (spMap (IntermediateField.inclusion h₂).toRingHom)) (m₃ : SABMap T'.t T₂.t (spMap (algebraMap k₂ ℂ))),
    EllMap C₂ C (IntermediateField.inclusion h₂).toRingHom φ₂ → EllMap C' C₂ (algebraMap k₂ ℂ) φ₃ → φ₃ ≫ φ₂ = φ → m₃.φ ≫ m₂.φ = m.φ → ∃ ψ : L → (C₂.P.A ⟶ T₂.t.G), IsFam C₂ T₂ h L ψ ∧ ∀ a, (ψ' a).left ≫ m₃.φ = φ₃ ≫ (ψ a).left := by
  intro hT hL E _ _ _ H k _ ω C D h T L ω' C' φ T' m ψ' hC hF
  have hfin := D.fin
  have : Module.Finite (𝓞 E) L := inferInstance
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  have hg : AddMonoid.FG L := AddGroup.fg_iff_addMonoid_fg.1 (Module.Finite.iff_addGroup_fg.1 inferInstance)
  obtain ⟨S, hS⟩ := AddMonoid.isAddFG_iff.mp hg
  choose K hK hK' using fun a : L => @exists_field hT hL.polBaseChange k _ C.P T.pol _ _ _ _ _ _ hC.2.1.2.1 m.cart
    (ψ' a) (hF.1 a).isMonHom
  refine ⟨k ⊔ (K 0 ⊔ ⨆ a : S, K a), ?_, le_sup_left, ?_⟩
  · have := hK
    have : FiniteDimensional ℚ (⨆ a : S, K a : IntermediateField ℚ ℂ) := IntermediateField.finiteDimensional_iSup_of_finite
    infer_instance
  intro k₂ h₂ h₁ ω₂ C₂ φ₂ φ₃ T₂ m₂ m₃ e₂ e₃ eφ em
  have gen : ∀ a : L, K a ≤ k₂ → ∃ f₂ : C₂.P.A ⟶ T₂.t.G, (ψ' a).left ≫ m₃.φ = φ₃ ≫ f₂.left := fun a ha =>
    hK' a k₂ h₂ ha C₂.P.A T₂.t.G φ₂ m₂.φ φ₃ m₃.φ e₂.2.1.2.1.1.w m₂.cart.1 e₃.2.1.2.1.1.w m₃.cart.1.w eφ em
  have all : ∀ a : L, ∃ f₂ : C₂.P.A ⟶ T₂.t.G, (ψ' a).left ≫ m₃.φ = φ₃ ≫ f₂.left := by
    intro a
    have ha : a ∈ AddSubmonoid.closure (S : Set L) := hS ▸ AddSubmonoid.mem_top a
    induction ha using AddSubmonoid.closure_induction with
    | mem a ha => exact gen a (((le_iSup (fun a : S => K a) ⟨a, ha⟩).trans (le_sup_right.trans le_sup_right)).trans h₁)
    | zero => exact gen 0 ((le_sup_left.trans le_sup_right).trans h₁)
    | add a b _ _ ha hb =>
      obtain ⟨x, hx⟩ := ha
      obtain ⟨y, hy⟩ := hb
      exact ⟨x * y, by rw [hF.2.1]; exact exists_mul e₃.2.1.2.1.1.w m₃.cart hx hy⟩
  choose ψ hψ using all
  exact ⟨ψ, GlobalTheory.T.family_identities_descend_field_to_dedekind hL E H k₂ ω₂ C₂ D h T₂ L ψ ℂ ω' C' (algebraMap k₂ ℂ) φ₃ T' m₃ ψ'
    (algebraMap k₂ ℂ).injective e₃ hψ hF, hψ⟩

end GlobalTheory.CM
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

namespace GlobalTheory.LamT

theorem exists_kronecker_logOm_core : ∀ (D : D7) (T : Core D) (h : LawsCore T) (large₂ : SizeData₂ D), ∃ (_ : NeZero T.Q.H.d) (χ : DirichletCharacter ℂ T.Q.H.d), IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm D.host.E χ).re = large₂.logOm :=
  fun D T h large₂ => GlobalTheory.LamF.exists_kronecker_logOm_eq D T.Q h.pins.1 large₂

end GlobalTheory.LamT
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM

open GlobalTheory.Serre GlobalTheory.CechPic GlobalTheory.HermTensorLB

theorem isFinite_left_of_comp_eq_id {S : Scheme.{0}} {A B : Over S} [IsSeparated B.hom] (i : A ⟶ B) (r : B ⟶ A)
    (h : i ≫ r = 𝟙 A) : IsFinite i.left := by
  have : IsSeparated (r.left ≫ A.hom) := by rw [Over.w r]; infer_instance
  have : IsSeparated r.left := IsSeparated.of_comp r.left A.hom
  have : IsClosedImmersion (i.left ≫ r.left) := by
    rw [← Over.comp_left, h, Over.id_left]; infer_instance
  have : IsClosedImmersion i.left := IsClosedImmersion.of_comp i.left r.left
  infer_instance

theorem relAmple_of_kForm_pos : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (ω : R) (C : Ell H R ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (b : OAct (OK H) A) (t : Serre.IsTensor A b C.P.A C.act D.La) (N : LB A.left), IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → N.IsLB → (∃ t : LB.Gen (Theta A N), t.IsGen) → LBIso N (cubeLB A ![𝟙 A, b.act (wK H)] N) → (∀ m m', LamEq N (t.tmul m) (t.tmul m') C.P.L (C.act.act (h m m')) (𝟙 C.P.A)) → Out.RelAmple A N := by
  intro laws E _ _ _ H R _ _ ω C D ε h A _ _ b t N hK hpos hN hT hiso hlam
  obtain ⟨n, k, l, r, hn, hrl, hl⟩ := GlobalTheory.T.cmHermitianForm_sum_of_squares E H D ε h hK hpos
  obtain ⟨-, -, ⟨br, hbr, -, hbb⟩, -, -, hproj⟩ := OK_isDedekindDomain_and_projective E H
  obtain ⟨hfinM, hprojM, -⟩ := hproj D.La D.fin D.proj
  have hl' : ∀ x y, (n : OK H) * h x y = ∑ i, l x i * br (l y i) := fun x y => Subtype.ext (by
    have := hl x y
    simp only [← hbr] at this
    simpa using this)
  have hL := C.P.isLB
  obtain ⟨rig, hrig⟩ := C.P.rigid
  obtain ⟨cub⟩ := (laws.cube _ C.P ⟨C.P.L, rig, hL, hrig⟩ rfl).1
  have hΘ : ∃ t : LB.Gen (Theta C.P.A C.P.L), t.IsGen := ⟨cub.t, cub.isGen⟩
  let q := Out.powIsPowGrp C.P.A k
  let ψ := t.mapLeft (IsTensor.pow q C.act) l
  let p : Fin k → (A ⟶ C.P.A) := fun i => ψ ≫ q.pr i
  have pl : ∀ i, IsLinearHom b C.act (p i) := fun i =>
    (t.isLinearHom_mapLeft _ _).comp (isLinearHom_pr q C.act i)
  have pm : ∀ i, IsMonHom (p i) := fun i => (pl i).1
  have hp : ∀ m i, t.tmul m ≫ p i = C.act.act (l m i) := fun m i => by simp [p, ψ]
  have am := C.act.hom
  have adj : ∀ {T : Over (Sp R)} (x y : T ⟶ C.P.A) (c : OK H),
      lam (cls C.P.L hL) (x ≫ C.act.act c) y = lam (cls C.P.L hL) x (y ≫ C.act.act (br c)) := by
    intro T x y c
    have h₀ := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (C.adj c (br c) (hbr c))
    have h' := congrArg (pull (lift x y).left)
      ((cls_cube_two hL _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.comp_id] using h'
  have base : ∀ {T : Over (Sp R)} (x y : T ⟶ C.P.A) (m m' : D.La),
      lam (cls N hN) (x ≫ t.tmul m) (y ≫ t.tmul m') = lam (cls C.P.L hL) (x ≫ C.act.act (h m m')) y := by
    intro T x y m m'
    have h₀ := (cls_eq_iff (LB.isLB_linComb hN _ _) (LB.isLB_linComb hL _ _)).2 (hlam m m')
    have h' := congrArg (pull (lift x y).left)
      ((cls_cube_two hN _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.comp_id] using h'
  have key : ∀ {T : Over (Sp R)} (x y : T ⟶ A),
      n • lam (cls N hN) x y = ∑ i, lam (cls C.P.L hL) (x ≫ p i) (y ≫ p i) := by
    intro T x y
    induction x using t.induction_on with
    | one => simp only [MonObj.one_comp, lam_one_left, smul_zero, Finset.sum_const_zero]
    | mul x x' hx hx' =>
      simp only [MonObj.mul_comp, lam_mul_left hN hT, lam_mul_left hL hΘ, smul_add, hx, hx', Finset.sum_add_distrib]
    | tmul m x =>
      induction y using t.induction_on with
      | one => simp only [MonObj.one_comp, lam_one_right, smul_zero, Finset.sum_const_zero]
      | mul y y' hy hy' =>
        simp only [MonObj.mul_comp, lam_mul_right hN hT, lam_mul_right hL hΘ, smul_add, hy, hy',
          Finset.sum_add_distrib]
      | tmul m' y =>
        let φ : OK H →+ Pic T.left := AddMonoidHom.mk' (fun c => lam (cls C.P.L hL) (x ≫ C.act.act c) y) fun c d => by
          simp only [C.act.add, MonObj.comp_mul, lam_mul_left hL hΘ]
        have hφ : ∀ c d, lam (cls C.P.L hL) (x ≫ C.act.act c) (y ≫ C.act.act d) = φ (c * br d) := by
          intro c d
          have := adj (x ≫ C.act.act c) y (br d)
          rw [hbb, Category.assoc, ← C.act.mul] at this
          exact this.symm

        simp only [Category.assoc, hp, hφ, ← map_sum, ← hl', base, ← nsmul_eq_mul, map_nsmul]
        rfl
  have prim : ∀ x : A ⟶ C.P.A, lam (cls C.P.L hL) x (x ≫ C.act.act (wK H)) = pull x.left (cls C.P.L hL) := by
    intro x
    have h₀ := ((cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 C.prim).trans (cls_cube_two hL _ _ _)
    have h' := congrArg (pull x.left) h₀
    simpa only [pull_lam, Category.comp_id] using h'.symm
  have hB : (Out.boxLB C.P.L q.pr).IsLB := LB.isLB_linComb hL _ _
  have hψB := pull_isLB hB ψ.left
  have final : LBIso ((Out.boxLB C.P.L q.pr).pull ψ.left) (lbPow N n) := by
    refine (cls_eq_iff hψB (LB.isLB_linComb hN _ _)).1 ?_
    have h₀ := ((cls_eq_iff hN (LB.isLB_linComb hN _ _)).2 hiso).trans (cls_cube_two hN _ _ _)

    rw [cls_lbPow hN, cls_pull hB, cls_linComb hL, h₀, key, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Category.id_comp, (pl i).comm, prim, one_smul, ← pull_comp]
    rfl
  have hA : IsAbelianScheme A := t.isAbelianScheme C.P.isAb
  have hG : IsAbelianScheme (Out.powObj C.P.A k) := (IsTensor.pow q C.act).isAbelianScheme C.P.isAb
  have := hG.proper
  have hfin : IsFinite ψ.left := isFinite_left_of_comp_eq_id ψ ((IsTensor.pow q C.act).mapLeft t r)
    (by rw [← IsTensor.mapLeft_comp, hrl, IsTensor.mapLeft_id])
  have hid : IsFinite (𝟙 A : A ⟶ A).left := by rw [Over.id_left]; infer_instance
  have a₁ := (relAmple_finite_pow_iso _ A _ ψ _ 1 one_pos hA hG hB hfin).1 (relAmple_powObj_boxLB R C.P k)
  have a₂ := (relAmple_finite_pow_iso _ A A (𝟙 A) _ 1 one_pos hA hA hψB hid).2.2.2 _
    (LB.isLB_linComb hN _ _) final a₁
  exact (relAmple_finite_pow_iso _ A A (𝟙 A) N n hn hA hA hN hid).2.1.1 a₂

end GlobalTheory.CM
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.exists_inverse_isogeny_sum_of_cm_homs : ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A A' B : Out.PolAV (Sp (𝓞 K))) (p q : ℕ) (φ : Fin p → (A.A ⟶ B.A)) (φ' : Fin q → (A'.A ⟶ B.A)), (∀ i, IsMonHom (φ i)) → (∀ i, IsMonHom (φ' i)) → B.g = p * A.g + q * A'.g → (∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ B.A, ∃ (x : Fin p → (Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.A)) (x' : Fin q → (Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A'.A)), y = (List.ofFn fun i => x i ≫ φ i).prod * (List.ofFn fun i => x' i ≫ φ' i).prod) → ∃ (N : ℕ) (ψ : Fin p → (B.A ⟶ A.A)) (ψ' : Fin q → (B.A ⟶ A'.A)), 0 < N ∧ (∀ (Tb : Over (Sp (𝓞 K))) (x : Tb ⟶ B.A), padd B.A (psumPt fun i => x ≫ ψ i ≫ φ i) (psumPt fun i => x ≫ ψ' i ≫ φ' i) = pnsmulPt N x) ∧ ∀ (Tb : Over (Sp (𝓞 K))) (a : Fin p → (Tb ⟶ A.A)) (a' : Fin q → (Tb ⟶ A'.A)), (∀ i, padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => a' k ≫ φ' k) ≫ ψ i = pnsmulPt N (a i)) ∧ ∀ i, padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => a' k ≫ φ' k) ≫ ψ' i = pnsmulPt N (a' i) := by
  first | exact @GlobalTheory.LamF.exists_inverse_isogeny_of_sum | exact GlobalTheory.LamF.exists_inverse_isogeny_of_sum | (intros; apply GlobalTheory.LamF.exists_inverse_isogeny_of_sum <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

theorem _root_.GlobalTheory.T.mean_log_lieNormSq_eq_mean_log_eta_alt : ThetaUnifAV → Out.PolBaseChangeSt → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ₀ : K →+* ℂ), ¬ ComplexEmbedding.IsReal σ₀ → ∀ (𝔟 : ClassGroup (𝓞 K) → nonZeroDivisors (Ideal (𝓞 K))), (∀ C, ClassGroup.mk0 (𝔟 C) = C) → ∀ (M : IntermediateField ℚ ℂ) [NumberField M] (κ : K →+* M) (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) (L₀ : (𝓞 M →+* ℂ) → PeriodPair) (Q : ClassGroup (𝓞 K) → Out.PolAV (Sp (𝓞 M))) (t : ∀ C, epsR (𝓞 M) ⟶ (Q C).A) (L : ClassGroup (𝓞 K) → (𝓞 M →+* ℂ) → PeriodPair) (δ : ClassGroup (𝓞 K) → (𝓞 M)ˣ), (∀ a, (κ a : ℂ) = σ₀ a) ∧ (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L₀ s').lattice ↔ z • w' ∈ u'.Λ)) ∧ (∀ C, ((Q C).g = 1 ∧ IsLieBasis ![(t C)] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ (Q C).A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' (Q C) P' φ' → IsVecOver f' φ' (t C) v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ (Q C).A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' (Q C) P' φ' → IsVecOver s' φ' (t C) v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L C s').lattice ↔ z • w' ∈ u'.Λ))) ∧ (∀ C s, (L C s).g₂ ^ 3 - 27 * (L C s).g₃ ^ 2 = s (δ C : 𝓞 M)) ∧ (∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice ↔ ∃ a : 𝓞 K, z = c * σ₀ (a : K)) → (∃ β : ClassGroup (𝓞 K) → M, (∀ C, β C ≠ 0) ∧ (∀ a : 𝓞 K, (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ P.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) P Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ v t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![κ (a : K)] ![t₁] (v₁ ≫ f₁))) ∧ (∀ C (x : K), (∀ b ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K))) → (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ (Q C).A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) (Q C) Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ (t C) t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![β C * κ x] ![t₁] (v₁ ≫ f₁))) ∧ ∀ C, ∀ y ∈ (𝔟 C : Ideal (𝓞 K)), (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ (Q C).A.left) (ψ₁ : Q₁.A.left ⟶ P.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) (Q C) P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) P Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ (t C) v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ v t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![(β C)⁻¹ * κ (y : K)] ![t₁] (v₁ ≫ f₁))) → ∀ n : (M →+* ℂ) → ℝ, (∀ s, IsLieNormSq P v (s.comp (algebraMap (𝓞 M) M)) (n s)) → ∀ (σ : K →+* ℂ) (τ : ClassGroup (𝓞 K) → ℍ), (∀ C, IsIdealClassPoint σ C (τ C)) → (∑ s, Real.log (n s)) / Module.finrank ℚ M = (∑ C, -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)) / classNumber K := by
  first | exact @GlobalTheory.mean_log_lieNormSq_eq_mean_log_eta | exact GlobalTheory.mean_log_lieNormSq_eq_mean_log_eta | (intros; apply GlobalTheory.mean_log_lieNormSq_eq_mean_log_eta <;> assumption)
end
