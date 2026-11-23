module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle030
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle033
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle004
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle044
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OneMulConjFracOneEqInvDifferent
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalBasisDescription
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementB
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle045
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle017
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle020
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
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM

theorem IsKForm.map_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D₁ D : Datum H} {ε : ℤˣ}
    {h₁ : D₁.La → D₁.La → OK H} {h : D.La → D.La → OK H} (k₁ : IsKForm D₁ ε h₁) (k : IsKForm D ε h)
    {L : Submodule (𝓞 E) D.La} (f : D₁.La →ₗ[𝓞 E] L) (c : 𝓞 E) (hf : ∀ a b, D.EF (f a) (f b) = D₁.EF (c • a) b)
    (a b : D₁.La) : h (f a) (f b) = h₁ (c • a) b := by
  apply Subtype.ext
  have e : H.w0 • ((f a : L) : D.La) = ((f (H.w0 • a) : L) : D.La) := by rw [map_smul]; rfl
  rw [k, k₁, e, hf, hf, smul_comm c H.w0 a]

theorem exists_famLift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (D₁ D : Datum H) (ε : ℤˣ) (h₁ : D₁.La → D₁.La → OK H) (h : D.La → D.La → OK H) (T₁ T : PAT H (Sp R)) (t : IsTen C D₁ h₁ T₁) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (f : D₁.La →ₗ[𝓞 E] L) (c : 𝓞 E), IsKForm D₁ ε h₁ → IsKForm D ε h → (∀ a b, D.EF (f a) (f b) = D₁.EF (c • a) b) → IsFam C T h L ψ →
  ∃ Φ : T₁.t.G ⟶ T.t.G, Serre.IsLinearHom T₁.t.act T.t.act Φ ∧ (∀ a, t.ten.tmul a ≫ Φ = ψ (f a)) ∧ LamEq T.t.PP.L Φ Φ T₁.t.PP.L (T₁.t.act.act c) (𝟙 T₁.t.G) := by
  intro E _ _ _ H R _ ω C D₁ D ε h₁ h T₁ T t L ψ f c k₁ k hf ⟨l, hadd, hsmul, hlam⟩
  let F : D₁.La →ₗ[OK H] Serre.Pts (Serre.comapAct T.t.act (algebraMap (OK H) (𝓞 E))) C.P.A :=
    { toFun := fun a => Serre.Pts.mk _ (ψ (f a))
      map_add' := fun a b => Serre.Pts.ext (by rw [map_add (f := _)]; exact hadd _ _)
      map_smul' := fun s a => Serre.Pts.ext (by
        have e : f (s • a) = (s : 𝓞 E) • f a := f.map_smul (s : 𝓞 E) a
        rw [e]; exact hsmul _ _) }
  have hF : ∀ a, Serre.IsLinearHom C.act (Serre.comapAct T.t.act (algebraMap (OK H) (𝓞 E))) (F a).hom :=
    fun a => l (f a)
  have hm : IsMonHom (t.ten.lift F hF) := (t.ten.isLinearHom_lift F hF).isMonHom
  have ht : ∀ a, t.ten.tmul a ≫ t.ten.lift F hF = ψ (f a) := fun a => t.ten.tmul_lift F hF a
  refine ⟨t.ten.lift F hF, ⟨hm, fun s => ?_⟩, ht, ?_⟩
  · have := T₁.t.act.hom s
    have := T.t.act.hom s
    refine t.ten.hom_ext fun a => ?_
    rw [← Category.assoc, ← t.lin, ht, ← Category.assoc, ht, map_smul, hsmul]
  · refine GlobalTheory.T.tensor_pairing_identity_of_pure_tensors _ _ _ _ _ _ _ t.ten _ _ _ t.ten _ _ _ _ _ _ _ _ T.t.PP.isLB T₁.t.PP.isLB
      ⟨T.t.cub.t, T.t.cub.isGen⟩ ⟨T₁.t.cub.t, T₁.t.cub.isGen⟩ hm hm (T₁.t.act.hom c) inferInstance fun a b => ?_
    rw [ht, ht, ← t.lin, Category.comp_id]
    have e := hlam (f a) (f b)
    rw [k₁.map_eq k f c hf] at e
    exact LBIso.trans (LamCalc.cubeLB_isLB T.t.PP.isLB _) (LamCalc.cubeLB_isLB C.P.isLB _)
      (LamCalc.cubeLB_isLB T₁.t.PP.isLB _) e (LBIso.symm (t.lam (c • a) b))

end GlobalTheory.CM
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_isGrpPullback_polAV (hB : Out.PolBaseChangeSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (P : Out.PolAV S) :
    ∃ (P' : Out.PolAV S') (φ : P'.A.left ⟶ P.A.left), P'.g = P.g ∧ IsGrpPullback P'.A P.A f φ := by
  obtain ⟨P', g, hg, hd, hm, -⟩ := hB S S' f P
  refine ⟨P', g, hd, hg, fun T x y x₀ y₀ hx hy => ?_⟩
  have ex : x₀ = Out.toBase hg.w x := Over.OverMorphism.ext hx
  have ey : y₀ = Out.toBase hg.w y := Over.OverMorphism.ext hy
  rw [ex, ey, ← hm]
  rfl

theorem IsGrpPullback.id_pow_left {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (N : ℕ) :
    (𝟙 G' ^ N).left ≫ φ = φ ≫ (𝟙 G ^ N).left := by
  obtain ⟨E, hE⟩ := exists_mulEquiv_points_of_isGrpPullback S S' f G G' φ h G'
  have h1 : (E (𝟙 G')).left = φ := by rw [hE]; exact Category.id_comp _
  have h2 : E (𝟙 G' ^ N) = E (𝟙 G') ≫ 𝟙 G ^ N := by
    rw [map_pow, MonObj.comp_pow, Category.comp_id]
  rw [← hE, h2, Over.comp_left, h1]

theorem exists_inverse_isogeny_ringOfIntegers :
    ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (P P' : Out.PolAV (Sp (𝓞 K))) (Φ : P.A ⟶ P'.A), P.g = P'.g → IsMonHom Φ → (∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P'.A, ∃ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P.A, y = x ≫ Φ) → ∃ (N : ℕ) (ψ : P'.A ⟶ P.A), 0 < N ∧ IsMonHom ψ ∧ Φ ≫ ψ = 𝟙 P.A ^ N ∧ ψ ≫ Φ = 𝟙 P'.A ^ N := by
  intro hT hL hE K _ _ σ P P' Φ hg hΦ honto
  obtain ⟨Q, φ, hQ, hφ⟩ := exists_isGrpPullback_polAV hL.polBaseChange (spMap (algebraMap (𝓞 K) K)) P
  obtain ⟨Q', φ', hQ', hφ'⟩ := exists_isGrpPullback_polAV hL.polBaseChange (spMap (algebraMap (𝓞 K) K)) P'
  obtain ⟨⟨Φ₀, hΦ₀, -⟩, hmon⟩ := existsUnique_hom_of_isGrpPullback _ _ _ P.A P'.A Q.A Q'.A φ φ' hφ hφ' Φ
  have hm₀ : IsMonHom Φ₀ := hmon Φ₀ hΦ₀ hΦ
  have hs : Surjective Φ.left :=
    (GlobalTheory.OntoSurj.surjective_of_onto_complex_points (𝓞 K) (σ.comp (algebraMap (𝓞 K) K))
      (σ.injective.comp (IsFractionRing.injective (𝓞 K) K)) P'.A P.A Φ P'.isAb P.isAb honto).1
  have hpb : IsPullback φ Φ₀.left Φ.left φ' := by
    refine IsPullback.of_bot ?_ hΦ₀.symm hφ'.1
    rw [Over.w Φ₀, Over.w Φ]
    exact hφ.1
  have hs₀ : Surjective Φ₀.left := MorphismProperty.of_isPullback (P := @Surjective) hpb hs
  obtain ⟨N, ψ₀, hN, hψ₀, e₁, e₂⟩ := GlobalTheory.T.exists_inverse_isogeny_of_surjective_polAV hT hL K σ Q Q' Φ₀ (hQ.trans (hg.trans hQ'.symm)) hm₀ hs₀
  obtain ⟨ψ, hψ, eψ, -⟩ := abelianScheme_hom_extends_dedekind_of_isGrpPullback hE (𝓞 K) K P'.A P.A Q'.A Q.A φ' φ
    P'.isAb P.isAb hφ' hφ ψ₀ hψ₀
  refine ⟨N, ψ, hN, hψ, ?_, ?_⟩
  · obtain ⟨F, -, -, hF⟩ := abelianScheme_hom_extends_dedekind_of_isGrpPullback hE (𝓞 K) K P.A P.A Q.A Q.A φ φ
      P.isAb P.isAb hφ hφ (Φ₀ ≫ ψ₀) inferInstance
    refine (hF _ ?_).trans (hF _ ?_).symm
    · rw [Over.comp_left, Over.comp_left, Category.assoc, eψ, ← Category.assoc, hΦ₀, Category.assoc]
    · rw [e₁]; exact IsGrpPullback.id_pow_left hφ N
  · obtain ⟨F, -, -, hF⟩ := abelianScheme_hom_extends_dedekind_of_isGrpPullback hE (𝓞 K) K P'.A P'.A Q'.A Q'.A φ' φ'
      P'.isAb P'.isAb hφ' hφ' (ψ₀ ≫ Φ₀) inferInstance
    refine (hF _ ?_).trans (hF _ ?_).symm
    · rw [Over.comp_left, Over.comp_left, Category.assoc, hΦ₀, ← Category.assoc, eψ, Category.assoc]
    · rw [e₂]; exact IsGrpPullback.id_pow_left hφ' N

end GlobalTheory.LamF
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.exists_numberField_point_of_cmPeriodLattice : CMCurve → CMPoint → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (p q : ℕ), Nonempty (CMLat hP p q) → ∃ (K₁ : IntermediateField ℚ ℂ) (hk : KA l ≤ K₁) (y : Sp K₁ ⟶ Xo.X), FiniteDimensional ℚ K₁ ∧ y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i Pe := by
  first | exact @GlobalTheory.PointAlg.exists_numberField_point_of_cmLat | exact GlobalTheory.PointAlg.exists_numberField_point_of_cmLat | (intros; apply GlobalTheory.PointAlg.exists_numberField_point_of_cmLat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem hasPeriod_of_ellMap : Out.PolBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (M K : Type) [Field M] [NumberField M] [Field K] [NumberField K] (j : M →+* K) (ω : 𝓞 M) (ω' : 𝓞 K) (C : Ell H (𝓞 M) ω) (C' : Ell H (𝓞 K) ω') (φ : C'.P.A.left ⟶ C.P.A.left) (x : ℝ), EllMap C' C (RingOfIntegers.mapRingHom j) φ → C.HasPeriod x → C'.HasPeriod x := by
  intro hbc E _ _ _ H M K _ _ _ _ j ω ω' C C' φ x hm hx
  obtain ⟨n, hn, hmean⟩ := hx
  refine ⟨fun s => n (s.comp j), fun s => ⟨(hn _).1, fun r => ?_⟩, ?_⟩
  · rw [(GlobalTheory.T.cmCurveBaseChange_comp E H _ ω C _ ω' C' _ φ hm).2.2 _ r hbc]
    have e : (s.comp (algebraMap (𝓞 K) K)).comp (RingOfIntegers.mapRingHom j)
        = (s.comp j).comp (algebraMap (𝓞 M) M) := by
      ext a; rfl
    rw [e]
    exact (hn _).2 r
  · rw [GlobalTheory.meanLog_comp]; exact hmean

end GlobalTheory.CM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.exists_cmPoint_localModel_over_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (T : CDVR) (iK : z.K →+* T.Fr), ((∀ a : 𝓞 z.K, iK (a : z.K) ∈ Set.range (algebraMap T.V T.Fr)) → Nonempty (LocMod z T iK)) ∧ ∀ (M : LocMod z T iK) (T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∃ (M' : LocMod z T' (i.comp iK)) (n : SABMap M'.G.t M.G.t (spMap ψ)) (n' : SABMap M'.t'.t M.t'.t (spMap i)), M'.m1.φ = n'.φ ≫ M.m1.φ ∧ M'.m2.φ ≫ n.φ = n'.φ ≫ M.m2.φ := by
  first | exact @GlobalTheory.LamT.locMod_exists | exact GlobalTheory.LamT.locMod_exists | (intros; apply GlobalTheory.LamT.locMod_exists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.universalTripleFibreKeyData_baseChange_keyPullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] [Nontrivial S'] (φ : S →+* S') (x : Sp S ⟶ Xo.X) (x' : Sp S' ⟶ Xo.X) (Φ : FibKey Xo S x) (Φ' : FibKey Xo S' x') (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')), x' = spMap φ ≫ x → SecTie Φ.m Φ.th s → SecTie Φ'.m Φ'.th s' → SecBC φ 1 x x' s s' → ∃ (hg : Φ'.T.g = Φ.T.g) (v' : Fin Φ'.T.g → (epsR S' ⟶ Φ'.T.t.G)) (hv' : IsLieBasis v'), KeyPB ({ Φ' with v := v', basis := hv' } : FibKey Xo S' x').key Φ.key φ ∧ ∀ i, (v' i).left ≫ Φ'.m.φ = spMap (Formalism.L2.Pj.dualMap φ) ≫ (Φ.v (i.cast hg)).left ≫ Φ.m.φ := by
  first | exact @GlobalTheory.LamT.fibKey_keyPB | exact GlobalTheory.LamT.fibKey_keyPB | (intros; apply GlobalTheory.LamT.fibKey_keyPB <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.exists_normalized_symmetric_ample_lb : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (w w' : P.A ⟶ P.A), IsMonHom w → IsMonHom w' → w * w' = 𝟙 P.A → LamEq P.L w (𝟙 P.A) P.L (𝟙 P.A) w' →
  ∃ L' : LB P.A.left, L'.IsLB ∧ Out.Rigidified P.A L' ∧ Out.Sym P.A L' ∧ Out.RelAmple P.A L' ∧ Out.KTriv P.A L' ∧ LamEq L' (𝟙 P.A) (𝟙 P.A) P.L (𝟙 P.A) (𝟙 P.A) ∧ LBIso L' (cubeLB P.A ![𝟙 P.A, w] L') := by
  first | exact @GlobalTheory.CM.exists_normalised_polarisation | exact GlobalTheory.CM.exists_normalised_polarisation | (intros; apply GlobalTheory.CM.exists_normalised_polarisation <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.cmTensor_smoothOfRelativeDimension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (D : Datum H) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (b : OAct (OK H) A), Nonempty (Serre.IsTensor A b C.P.A C.act D.La) → SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) A.hom := by
  first | exact @GlobalTheory.CM.tensor_smoothOfRelativeDimension | exact GlobalTheory.CM.tensor_smoothOfRelativeDimension | (intros; apply GlobalTheory.CM.tensor_smoothOfRelativeDimension <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.exists_cmAdjoin_action_of_equation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (W : G ⟶ G), IsMonHom W → (W ≫ W) * (𝟙 G) ^ ((1 + H.d) / 4) = W → ∃ a : OAct (OK H) G, a.act (wK H) = W ∧ ∀ m n : ℤ, a.act ((m : OK H) + (n : OK H) * wK H) = (𝟙 G) ^ m * W ^ n := by
  first | exact @GlobalTheory.CM.exists_okAct_of_equation | exact GlobalTheory.CM.exists_okAct_of_equation | (intros; apply GlobalTheory.CM.exists_okAct_of_equation <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.exists_pat_pullback_g_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (T : PAT H S), ∃ (T' : PAT H S') (_ : SABMap T'.t T.t f), T'.g = T.g := by
  first | exact @GlobalTheory.CM.PAT.exists_pullback | exact GlobalTheory.CM.PAT.exists_pullback | (intros; apply GlobalTheory.CM.PAT.exists_pullback <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.lie_lattice_local_basis_description : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P), ∃ (n : ℕ) (r : Fin n → 𝓞 K) (M : Fin n → Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), Ideal.span (Set.range r) = ⊤ ∧ (∀ i, r i ≠ 0 ∧ (M i).det ≠ 0) ∧ (∀ c, c ∈ F.lieLat ↔ ∀ i, ∃ (k : ℕ) (a : Fin F.P₀.g → 𝓞 K), r i ^ k • c = ∑ j, a j • M i j) ∧
  ∀ i (R : Type) [CommRing R] [Algebra (𝓞 K) R] [Algebra R K] [IsScalarTower (𝓞 K) R K] (G : Over (Sp R)) [GrpObj G] (φ : G.left ⟶ P.A.left) (ψ : F.P₀.A.left ⟶ G.left), IsUnit (algebraMap (𝓞 K) R (r i)) → IsGrpPullback G P.A (spMap (algebraMap (𝓞 K) R)) φ → IsGrpPullback F.P₀.A G (spMap (algebraMap R K)) ψ → ψ ≫ φ = F.φ → ∃ e : Fin F.P₀.g → (epsR R ⟶ G), IsLieBasis e ∧ ∀ j, ∃ w, IsVecOver (algebraMap R K) ψ (e j) w ∧ IsLieComb (M i j) F.v w := by
  first | exact @GlobalTheory.CM.LieGlue.exists_cover_lieLat | exact GlobalTheory.CM.LieGlue.exists_cover_lieLat | (intros; apply GlobalTheory.CM.LieGlue.exists_cover_lieLat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.topLieVector_norm_sq_eq_gramDet : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (h : HermFam K (Fin x.P.g → K)), (GenFib.mk x.P φ hf x.v x.basis : GenFib A).IsHerm h → ∀ (T abelian₂ : MLine K) (s : K →+* ℂ), KeyArchAt x T abelian₂ s → abelian₂.n s ^ 2 = (h.gram s (fun i : Fin x.P.g => Pi.single i 1)).det.re := by
  first | exact @GlobalTheory.CM.TopLieVector.sq_eq_det_gram | exact GlobalTheory.CM.TopLieVector.sq_eq_det_gram | (intros; apply GlobalTheory.CM.TopLieVector.sq_eq_det_gram <;> assumption)
end
