module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1101
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle439
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2747
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepCongruenceElementSeparatesChartBallThickFram
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals.LieRel

open GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.Twist (resM resM_self)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO ptMap LieG dualScale)

section Lie

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [QuasiSeparated G.hom]

theorem exists_prod (l : List (LieG G)) :
    ∃ z : LieG G, z.1 = (l.map fun x => x.1).prod ∧ tangent z = (l.map tangent).sum := by
  induction l with
  | nil =>
    have h1 : ptMap (TrivSqZeroExt.fstHom R R R) ≫ (1 : specO R (DualNumber R) ⟶ G) = 1 := MonObj.comp_one _
    refine ⟨⟨1, h1⟩, rfl, ?_⟩
    have h2 := tangent_mul (G := G) ⟨1, h1⟩ ⟨1, h1⟩ (OmegaGlobal.fst_mul _ _)
    have h3 : (⟨_, OmegaGlobal.fst_mul (G := G) ⟨1, h1⟩ ⟨1, h1⟩⟩ : LieG G) = ⟨1, h1⟩ :=
      Subtype.ext (_root_.mul_one _)
    rw [h3] at h2
    simpa using h2
  | cons x l ih =>
    obtain ⟨z, hz, hz'⟩ := ih
    refine ⟨⟨_, OmegaGlobal.fst_mul x z⟩, ?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, ← hz]
    · rw [tangent_mul, hz', List.map_cons, List.sum_cons]

theorem isLieComb_of_tangent {n : ℕ} (a : Fin n → R) (v : Fin n → LieG G) (w : LieG G)
    (h : tangent w = ∑ m, cst R (a m) • tangent (v m)) : IsLieComb a (fun m => (v m).1) w.1 := by
  let u : Fin n → LieG G := fun m => ⟨_, OmegaGlobal.fst_scale (a m) (v m)⟩
  obtain ⟨z, hz, hz'⟩ := exists_prod (List.ofFn u)
  have e : w = z := tangent_injective R G (by
    rw [h, hz', List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_congr rfl fun m _ => (tangent_scale _ _ _).symm)
  refine ⟨fun m => (u m).1, fun m => ?_, ?_⟩
  · have ha : (dualScale (a m)).toRingHom = epsScaleR (a m) := by
      ext y <;> simp [dualScale, epsScaleR]
    exact congrArg (fun r => spMap r ≫ (v m).1.left) ha
  · rw [e, hz, List.map_ofFn]
    rfl

theorem exists_matrix {g : ℕ} {e e' : Fin g → Γ(omega G, ⊤)} (he : IsFrame e) (he' : IsFrame e') (v v' : Fin g → LieG G)
    (hv : ∀ j k, dualApp (tangent (v j)) le_top (e k) = if j = k then 1 else 0)
    (hv' : ∀ j k, dualApp (tangent (v' j)) le_top (e' k) = if j = k then 1 else 0) :
    ∃ M : Matrix (Fin g) (Fin g) R, (∀ j, IsLieComb (M j) (fun m => (v' m).1) (v j).1) ∧
      M.det = (Scheme.ΓSpecIso (.of R)).hom (he.detUnit he' le_rfl le_rfl : Γ(Sp R, ⊤)) := by
  refine ⟨fun j m => (Scheme.ΓSpecIso (.of R)).hom (dualApp (tangent (v j)) le_top (e' m)), fun j => ?_, ?_⟩
  · refine isLieComb_of_tangent _ _ _ (he'.dual_ext le_rfl fun k => ?_)
    rw [resM_self, dualApp_sum, LinearMap.sum_apply]
    simp only [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, LB.resG_self]
    rw [Finset.sum_congr rfl fun m _ => congrArg (cst R _ * ·) (hv' m k)]
    simp
  · have hc (j : Fin g) : dualApp (tangent (v j)) le_rfl = (he.basis le_rfl).coord j := by
      apply (he.basis le_rfl).ext
      intro k
      have hb : (he.basis le_rfl) k = e k := by rw [he.basis_apply, resM_self]
      rw [hb, hv, ← hb, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      simp only [eq_comm]
    rw [IsFrame.val_detUnit, Module.Basis.det_apply]
    refine Eq.trans ?_ (RingHom.map_det (Scheme.ΓSpecIso (.of R)).hom.hom _).symm
    congr 1
    ext j m
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, resM_self]
    exact congrArg _ (congrFun (congrArg DFunLike.coe (hc j)) (e' m))

end Lie

variable {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] [QuasiSeparated G.hom] {g : ℕ}

theorem pfr_eq (c : Chart (omega G) g) (ξ : Sp R ⟶ S) (hc : ⊤ ≤ ξ ⁻¹ᵁ c.U) :
    pfr c ξ hc = fun k => (omegaBase (isGrpPullback_pullback G ξ)).app ⊤
      (resM _ hc (QCoh.pullbackSections ξ (omega G) (le_refl (ξ ⁻¹ᵁ c.U)) (c.e k))) :=
  funext fun _ => congrArg _ (QCoh.res_pullbackSections ξ _ _ _ _).symm

theorem isFrame_pfr (c : Chart (omega G) g) (ξ : Sp R ⟶ S) (hc : ⊤ ≤ ξ ⁻¹ᵁ c.U) : IsFrame (pfr c ξ hc) := by
  rw [pfr_eq]
  exact ((c.isFrame.pullback ξ).res hc).map_iso _

theorem val_detUnit_pfr (c c' : Chart (omega G) g) (ξ : Sp R ⟶ S) (hc : ⊤ ≤ ξ ⁻¹ᵁ c.U) (hc' : ⊤ ≤ ξ ⁻¹ᵁ c'.U)
    (h : ⊤ ≤ ξ ⁻¹ᵁ (c.U ⊓ c'.U)) :
    ((isFrame_pfr c ξ hc).detUnit (isFrame_pfr c' ξ hc') le_rfl le_rfl : Γ(Sp R, ⊤)) =
      (ξ.appLE (c.U ⊓ c'.U) ⊤ h).hom (c.isFrame.detUnit c'.isFrame inf_le_left inf_le_right : Γ(S, c.U ⊓ c'.U)) := by
  have key {e e' f f' : Fin g → Γ(omega (bG G ξ), ⊤)} (he : IsFrame e) (he' : IsFrame e') (hf : IsFrame f)
      (hf' : IsFrame f') (h₁ : e = f) (h₂ : e' = f') :
      he.detUnit he' le_rfl le_rfl = hf.detUnit hf' le_rfl le_rfl := by
    subst h₁ h₂; rfl
  rw [key _ _ (((c.isFrame.pullback ξ).res hc).map_iso (omegaBase (isGrpPullback_pullback G ξ)))
    (((c'.isFrame.pullback ξ).res hc').map_iso (omegaBase (isGrpPullback_pullback G ξ))) (pfr_eq c ξ hc) (pfr_eq c' ξ hc'),
    IsFrame.detUnit_map_iso ((c.isFrame.pullback ξ).res hc) ((c'.isFrame.pullback ξ).res hc'),
    IsFrame.detUnit_res (c.isFrame.pullback ξ) (c'.isFrame.pullback ξ)]
  exact c.isFrame.val_detUnit_pullback c'.isFrame ξ inf_le_left inf_le_right h

theorem genPt_appLE [IsIntegral S] (U : S.Opens) (hU : genericPoint S ∈ U) (a : Γ(S, U)) :
    (Scheme.ΓSpecIso (.of (FF S))).hom (((genPt S).appLE U ⊤ (genPt_le U hU)).hom a) =
      S.presheaf.germ U (genericPoint S) hU a := by
  have k : ⊤ ≤ S.fromSpecStalk (genericPoint S) ⁻¹ᵁ U := genPt_le U hU
  have e : (S.fromSpecStalk (genericPoint S)).appLE U ⊤ k =
      S.presheaf.germ U _ hU ≫ (Scheme.ΓSpecIso (S.presheaf.stalk (genericPoint S))).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU]
    simp only [Category.assoc, ← Functor.map_comp]
    have e : ((homOfLE le_top).op ≫ (homOfLE k).op :
      Opposite.op (⊤ : (Spec (S.presheaf.stalk (genericPoint S))).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
    rw [e, CategoryTheory.Functor.map_id, Category.comp_id]
  have e' : (S.fromSpecStalk (genericPoint S)).appLE U ⊤ k ≫
      (Scheme.ΓSpecIso (S.presheaf.stalk (genericPoint S))).hom = S.presheaf.germ U _ hU := by
    rw [e, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congr($e' a)

theorem lieRel : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsSemiAbelian G →
    SmoothOfRelativeDimension g G.hom → ∀ (c c' : VB.Chart (LieVB.omega G) g)
    (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
    (y y' : Fin g → (epsR (KeyVals.FF S) ⟶ KeyVals.bG G (KeyVals.genPt S))),
    KeyVals.IsDual c (KeyVals.genPt S) y → KeyVals.IsDual c' (KeyVals.genPt S) y' →
    ∃ M : Matrix (Fin g) (Fin g) (KeyVals.FF S), (∀ j, IsLieComb (M j) y' (y j)) ∧
      M.det = S.presheaf.germ _ (genericPoint S) h1
        ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) := by
  intro S _ G _ _ g hG _ c c' h1 y y' ⟨hc, hy⟩ ⟨hc', hy'⟩
  choose v hv hv₁ using hy
  choose v' hv' hv₁' using hy'
  have : QuasiSeparated (bG G (genPt S)).hom :=
    MorphismProperty.of_isPullback (isGrpPullback_pullback G (genPt S)).1 inferInstance
  obtain ⟨M, hM, hd⟩ := exists_matrix (isFrame_pfr c _ hc) (isFrame_pfr c' _ hc') v v' hv₁ hv₁'
  obtain rfl : (fun j => (v j).1) = y := funext hv
  obtain rfl : (fun j => (v' j).1) = y' := funext hv'
  refine ⟨M, hM, hd.trans ?_⟩
  rw [val_detUnit_pfr c c' _ hc hc' (genPt_le _ h1)]
  exact genPt_appLE _ h1 _

end GlobalTheory.KeyVals.LieRel

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals.DualBasis

open GlobalTheory.LieVB GlobalTheory.VB
open ReciprocityTheory.ChartRestriction.G.Pdiv (LieG ptMap dualScale specO)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem fst_of_isTangent {w : epsR R ⟶ G} (hw : IsTangent w) :
    ptMap (TrivSqZeroExt.fstHom R R R) ≫ (w : specO R (DualNumber R) ⟶ G) = toUnit (specO R R) ≫ η[G] := by
  have h : (toUnit (specO R R)).left = 𝟙 (Sp R) := by
    rw [Over.toUnit_left]
    exact Spec.map_id _
  ext1
  simp only [Over.comp_left, h]
  exact hw.trans (Category.id_comp _).symm

theorem isTangent_val (x : LieG G) : IsTangent (G := G) x.1 := sec_epsZero_comp x

theorem exists_prod [QuasiSeparated G.hom] (l : List (LieG G)) :
    ∃ p : LieG G, p.1 = (l.map (·.1)).prod ∧ tangent p = (l.map tangent).sum := by
  induction l with
  | nil =>
    refine ⟨⟨1, ?_⟩, rfl, ?_⟩
    · exact comp_one _
    · refine dual_ext fun W _ s => ?_
      have e : cotMap (1 : specO R (DualNumber R) ⟶ G) (epsZero_comp ⟨1, comp_one _⟩) = 0 := cotMap_eq_zero rfl _
      rw [List.map_nil, List.sum_nil]
      exact (congr((epsIso R).hom.app W (($e).app W s))).trans (map_zero _)
  | cons x l ih =>
    obtain ⟨p, hp, hp'⟩ := ih
    refine ⟨⟨x.1 * p.1, OmegaGlobal.fst_mul x p⟩, by simp [hp], ?_⟩
    rw [tangent_mul, hp', List.map_cons, List.sum_cons]

theorem isLieComb_iff [QuasiSeparated G.hom] {n : ℕ} (a : Fin n → R) (v : Fin n → LieG G) (w : LieG G) :
    IsLieComb (G := G) a (fun i => (v i).1) w.1 ↔ tangent w = ∑ i, cst R (a i) • tangent (v i) := by
  let u : Fin n → LieG G := fun i => ⟨ptMap (dualScale (a i)) ≫ (v i).1, OmegaGlobal.fst_scale (a i) (v i)⟩
  have hu (i : Fin n) : (u i).1.left = spMap (epsScaleR (a i)) ≫ (v i).1.left := by
    have ha : (dualScale (a i)).toRingHom = epsScaleR (a i) := by
      ext y <;> simp [dualScale, epsScaleR]
    exact congrArg (fun r => spMap r ≫ (v i).1.left) ha
  obtain ⟨p, hp, hp'⟩ := exists_prod (List.ofFn u)
  rw [List.map_ofFn] at hp hp'
  rw [List.sum_ofFn] at hp'
  have hs : tangent p = ∑ i, cst R (a i) • tangent (v i) :=
    hp'.trans (Finset.sum_congr rfl fun i _ => tangent_scale (a i) (v i) _)
  constructor
  · rintro ⟨u', hu', e⟩
    obtain rfl : u' = fun i => (u i).1 := funext fun i => Over.OverMorphism.ext ((hu' i).trans (hu i).symm)
    obtain rfl : w = p := Subtype.ext (e.trans hp.symm)
    exact hs
  · intro e
    obtain rfl : w = p := tangent_injective R G (e.trans hs.symm)
    exact ⟨fun i => (u i).1, hu, hp⟩

theorem exists_dual_of_isFrame [QuasiSeparated G.hom] {n : ℕ} {e : Fin n → Γ(omega G, ⊤)} (he : IsFrame e) :
    ∃ v : Fin n → LieG G, (∀ j k, dualApp (tangent (v j)) le_top (e k) = if j = k then 1 else 0) ∧
      IsLieBasis (G := G) fun j => (v j).1 := by
  choose v hv using fun j => TangentSurj.tangent_surjective R G (he.coord j)
  refine ⟨v, fun j k => ?_, fun j => isTangent_val (v j), fun w hw => ?_⟩
  · have h := he.dualApp_coord_frame j k le_rfl
    rw [Twist.resM_self] at h
    rw [hv]
    exact h.trans (if_congr eq_comm rfl rfl)
  · have hc : Function.Bijective (cst R) := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv
    let b := he.dual.basis le_rfl
    have hb (j : Fin n) : b j = tangent (v j) := by
      rw [hv]
      exact (IsFrame.basis_apply _ _ _).trans (Twist.resM_self _ _)
    have key (a : Fin n → R) := isLieComb_iff a v ⟨w, fst_of_isTangent hw⟩
    simp only [← hb] at key
    choose a ha using fun j => hc.2 (b.repr (tangent ⟨w, fst_of_isTangent hw⟩) j)
    refine ⟨a, (key a).2 ?_, fun a' h' => funext fun j => hc.1 ?_⟩
    · simp only [ha]
      exact (b.sum_repr _).symm
    · rw [ha, (key a').1 h', b.repr_sum_self]

theorem exists_isDual : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ) (c : VB.Chart (LieVB.omega G) g) (R : Type) [CommRing R]
    (ξ : Sp R ⟶ S), IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → ⊤ ≤ ξ ⁻¹ᵁ c.U →
    ∃ y : Fin g → (epsR R ⟶ KeyVals.bG G ξ), KeyVals.IsDual c ξ y ∧ IsLieBasis y := by
  intro S G _ g c R _ ξ hG _ hc
  have h := isGrpPullback_pullback G ξ
  have : QuasiSeparated (bG G ξ).hom := MorphismProperty.of_isPullback h.1 inferInstance
  have h₁ := ((c.isFrame.pullback ξ).res hc).map_iso (omegaBase h)
  have hf : IsFrame (pfr c ξ hc) := by
    convert h₁ using 2 with k
    exact congrArg _ (QCoh.res_pullbackSections ξ _ le_rfl hc (c.e k)).symm
  obtain ⟨v, hv, hb⟩ := exists_dual_of_isFrame hf
  exact ⟨fun j => (v j).1, ⟨hc, fun j => ⟨v j, rfl, hv j⟩⟩, hb⟩

end GlobalTheory.KeyVals.DualBasis

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyValsTrans

theorem exists_refactor {X X₁ X₂ A : Scheme.{0}} {L : LB X} {M : LB A} (hL : L.IsLB) (hM : M.IsLB)
    {F₁ : X₁ ⟶ X} {F₂ : X₂ ⟶ X} {φ₁ : A ⟶ X₁} {φ₂ : A ⟶ X₂} (e : φ₁ ≫ F₁ = φ₂ ≫ F₂)
    (w₂ : LB.Iso M ((L.pull F₂).pull φ₂)) (hw₂ : PGen w₂) :
    ∃ w₁ : LB.Iso M ((L.pull F₁).pull φ₁), PGen w₁ ∧
      (∀ (z : A) (J : PUnit → L.ι) (k : M.ι), F₁ (φ₁ z) ∈ L.U (J PUnit.unit) → z ∈ M.U k →
        gw w₁ (𝟙 A) z J k = gw w₂ (𝟙 A) z J k) ∧
      ∀ {Y Y₁ Y₂ B : Scheme.{0}} {u : Y ⟶ X} {u₁ : Y₁ ⟶ X₁} {u₂ : Y₂ ⟶ X₂} {v : B ⟶ A} {h₁ : Y₁ ⟶ Y} {h₂ : Y₂ ⟶ Y}
        {g₁ : B ⟶ Y₁} {g₂ : B ⟶ Y₂} (t : LB.Gen (LB.LinComb L (fun _ : PUnit => u) (fun _ => 1)))
        (t₁ : LB.Gen (LB.LinComb (L.pull F₁) (fun _ : PUnit => u₁) (fun _ => 1)))
        (t₂ : LB.Gen (LB.LinComb (L.pull F₂) (fun _ : PUnit => u₂) (fun _ => 1)))
        (a : LB.Gen (LB.LinComb M (fun _ : PUnit => v) (fun _ => 1))),
        v ≫ φ₁ = g₁ ≫ u₁ → v ≫ φ₂ = g₂ ≫ u₂ → g₁ ≫ h₁ = g₂ ≫ h₂ →
        PMaps (L := L) (F := F₁) (idIso (L.pull F₁)) (fun _ : PUnit => u₁) (fun _ => u) (fun _ => 1) t₁ t h₁ →
        PMaps (L := L) (F := F₂) (idIso (L.pull F₂)) (fun _ : PUnit => u₂) (fun _ => u) (fun _ => 1) t₂ t h₂ →
        PMaps w₂ (fun _ : PUnit => v) (fun _ => u₂) (fun _ => 1) a t₂ g₂ →
        PMaps w₁ (fun _ : PUnit => v) (fun _ => u₁) (fun _ => 1) a t₁ g₁ := by
  have hL₁ : (L.pull F₁).IsLB := LB.isLB_pull hL _
  have hL₂ : (L.pull F₂).IsLB := LB.isLB_pull hL _
  have p₁ := (isGen_iff (L := L) (F := F₁) (idIso _)).1 (idIso_isGen hL₁)
  have p₂ := (isGen_iff (L := L) (F := F₂) (idIso _)).1 (idIso_isGen hL₂)
  obtain ⟨w, T₂⟩ := exists_comp hL₂ (idIso (L.pull F₂)) w₂ p₂ hw₂ hL hM
  have pw := T₂.pgen_comp hL₂ p₂ hw₂
  have a₂ : ∀ (z : A) (J : PUnit → L.ι) (k : M.ι), (φ₂ ≫ F₂) z ∈ L.U (J PUnit.unit) → z ∈ M.U k →
      gw w (𝟙 A) z (J PUnit.unit) k = gw w₂ (𝟙 A) z J k := fun z J k hj hk => by
    have hJ : (𝟙 A ≫ φ₂) z ∈ (L.pull F₂).U J := mem_pull.2 hj
    rw [T₂ _ (𝟙 A) z (J PUnit.unit) J k hj hJ hk]
    have : gw (L := L) (F := F₂) (idIso (L.pull F₂)) (𝟙 A ≫ φ₂) z (J PUnit.unit) J = 1 := gm_self hL₂ _ z hJ
    rw [this, _root_.one_mul]
  have b₂ : ∀ {Y Y₂ B : Scheme.{0}} {u : Y ⟶ X} {u₂ : Y₂ ⟶ X₂} {v : B ⟶ A} {h₂ : Y₂ ⟶ Y}
        {g₂ : B ⟶ Y₂} (t : LB.Gen (LB.LinComb L (fun _ : PUnit => u) (fun _ => 1)))
        (t₂ : LB.Gen (LB.LinComb (L.pull F₂) (fun _ : PUnit => u₂) (fun _ => 1)))
        (a : LB.Gen (LB.LinComb M (fun _ : PUnit => v) (fun _ => 1))),
        v ≫ φ₂ = g₂ ≫ u₂ →
        PMaps (L := L) (F := F₂) (idIso (L.pull F₂)) (fun _ : PUnit => u₂) (fun _ => u) (fun _ => 1) t₂ t h₂ →
        PMaps w₂ (fun _ : PUnit => v) (fun _ => u₂) (fun _ => 1) a t₂ g₂ →
        PMaps w (fun _ : PUnit => v) (fun _ => u) (fun _ => 1) a t (g₂ ≫ h₂) :=
    fun t t₂ a hc H H' => T₂.pmaps_comp hL₂ (fun _ => hc) H H'
  clear T₂
  generalize φ₂ ≫ F₂ = H at e w pw a₂ b₂
  subst e
  obtain ⟨w₁, T₁⟩ := exists_cancel hL (idIso (L.pull F₁)) w p₁ pw hL₁ hM
  refine ⟨w₁, T₁.pgen_cancel hL p₁ pw, fun z J k hj hk => ?_, ?_⟩
  · have hJ : (𝟙 A ≫ φ₁) z ∈ (L.pull F₁).U J := mem_pull.2 hj
    rw [← a₂ z J k hj hk, T₁ _ (𝟙 A) z (J PUnit.unit) J k hj hJ hk]
    have : gw (L := L) (F := F₁) (idIso (L.pull F₁)) (𝟙 A ≫ φ₁) z (J PUnit.unit) J = 1 := gm_self hL₁ _ z hJ
    rw [this, _root_.one_mul]
  · intro Y Y₁ Y₂ B u u₁ u₂ v h₁ h₂ g₁ g₂ t t₁ t₂ a c₁ c₂ c H₁ H₂ H
    exact T₁.pmaps_cancel hL (fun _ => c₁) H₁ (c ▸ b₂ t t₂ a c₂ H₂ H)

theorem gs_locSec {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {δ : LB S}
    {σ : (CechPic.tens L.L (δ.pull G.hom)).Sec} {i : δ.ι} {R : Type} [CommRing R] {ξ : Sp R ⟶ S}
    {t : (KeyVals.bL L ξ).L.Sec} (hξ : ⊤ ≤ ξ ⁻¹ᵁ δ.U i) (ht : KeyVals.IsLocSec σ i ξ t) {Z : Scheme.{0}}
    (q : Z ⟶ (KeyVals.bG G ξ).left) (z : Z) (J : (KeyVals.bL L ξ).L.ι) (hJ : q z ∈ (KeyVals.bL L ξ).L.U J) :
    gs q z _ (t.f J) = gs (q ≫ pullback.fst G.hom ξ) z _ (σ.f (J PUnit.unit, fun _ => i)) := by
  have hle : (KeyVals.bL L ξ).L.U J ≤
      pullback.fst G.hom ξ ⁻¹ᵁ (CechPic.tens L.L (δ.pull G.hom)).U (J PUnit.unit, fun _ => i) := by
    intro p hp
    refine ⟨mem_pull.1 hp, mem_pull.2 ?_⟩
    have e := congrArg (fun g => g p) (pullback.condition (f := G.hom) (g := ξ))
    have h2 : ξ (pullback.snd G.hom ξ p) ∈ δ.U i := hξ (show pullback.snd G.hom ξ p ∈ (⊤ : (Sp R).Opens) from trivial)
    exact e.symm ▸ h2
  rw [ht J hle]
  exact gs_appLE _ _ _ hle q z hJ _

theorem pmaps_bL {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) {R : Type} [CommRing R]
    (ξ : Sp R ⟶ S) : PMaps (L := L.L) (F := pullback.fst G.hom ξ) (idIso (L.L.pull (pullback.fst G.hom ξ))) (K := PUnit)
      (fun _ => eSec (KeyVals.bG G ξ)) (fun _ => eSec G) (fun _ => 1) (KeyVals.bL L ξ).rig L.rig (KeyVals.eb ξ) :=
  (maps_iff _ _ _ _ (KeyVals.bL L ξ).rig L.rig (KeyVals.eb ξ) (KeyVals.bL L ξ).rig
    (rigPull_le (G' := KeyVals.bG G ξ) (pullback.fst G.hom ξ) (KeyVals.eb ξ) (KeyVals.eSec_bG G ξ) L.L)
    (fun _ => rfl)).1 (idIso_maps (KeyVals.bL L ξ))

theorem keyOn_trans : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R R' K : Type) [CommRing R]
    [CommRing R'] [CommRing K] (ξ : Sp R ⟶ S) (r : R →+* R') (ξ' : Sp R' ⟶ S) (f : R' →+* K)
    (t : (KeyVals.bL L ξ).L.Sec) (y : Fin g → (epsR R ⟶ KeyVals.bG G ξ)) (t' : (KeyVals.bL L ξ').L.Sec)
    (y' : Fin g → (epsR R' ⟶ KeyVals.bG G ξ')) (x : KeyIn K) (hg : x.P.g = g),
    spMap r ≫ ξ = ξ' → ⊤ ≤ ξ ⁻¹ᵁ δ.U i → KeyVals.IsLocSec σ i ξ t → KeyVals.IsLocSec σ i ξ' t' →
    (∀ F : DualNumber R →+* DualNumber R', (∀ a, F (algebraMap R _ a) = algebraMap R' _ (r a)) →
      F DualNumber.eps = DualNumber.eps → ∀ j, (y' j).left ≫ pullback.fst G.hom ξ' = spMap F ≫ (y j).left ≫ pullback.fst G.hom ξ) →
    KeyOn f x (KeyVals.bG G ξ') (KeyVals.bL L ξ') t' (fun j => y' (j.cast hg)) →
    KeyOn (f.comp r) x (KeyVals.bG G ξ) (KeyVals.bL L ξ) t (fun j => y (j.cast hg)) := by
  intro S G _ _ g L δ σ i R R' K _ _ _ ξ r ξ' f t y t' y' x hg hξ hU ht ht' hy hK
  obtain ⟨φ', he', ψ', F', hφ', hψ', hrig', hsec', hF1, hF2, hFv⟩ := hK
  have hU' : ⊤ ≤ ξ' ⁻¹ᵁ δ.U i := by
    intro p _
    rw [← hξ]
    exact hU (show spMap r p ∈ (⊤ : (Sp R).Opens) from trivial)
  have hP := isGrpPullback_pullback G ξ
  have hP' := isGrpPullback_pullback G ξ'
  obtain ⟨m, hm, hfst, hsnd⟩ : ∃ m : (KeyVals.bG G ξ').left ⟶ (KeyVals.bG G ξ).left,
      IsGrpPullback (KeyVals.bG G ξ') (KeyVals.bG G ξ) (spMap r) m ∧ m ≫ pullback.fst G.hom ξ = pullback.fst G.hom ξ' ∧
        m ≫ (KeyVals.bG G ξ).hom = (KeyVals.bG G ξ').hom ≫ spMap r := by
    have sq : pullback.fst G.hom ξ' ≫ G.hom = (pullback.snd G.hom ξ' ≫ spMap r) ≫ ξ := by
      rw [Category.assoc, hξ]; exact pullback.condition
    refine ⟨pullback.lift _ _ sq, ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    refine IsGrpPullback.cancel hP ?_ (pullback.lift_snd _ _ _)
    rw [pullback.lift_fst, hξ]
    exact hP'
  have hφ : IsGrpPullback x.P.A (KeyVals.bG G ξ) (spMap (f.comp r)) (φ' ≫ m) := by
    rw [spMap_comp]
    exact IsGrpPullback.comp hφ' hm
  have he : eSec x.P.A ≫ φ' ≫ m = spMap (f.comp r) ≫ eSec (KeyVals.bG G ξ) := PolBaseChange.eSec_comm hφ
  have e : (φ' ≫ m) ≫ pullback.fst G.hom ξ = φ' ≫ pullback.fst G.hom ξ' := by rw [Category.assoc, hfst]
  obtain ⟨ψ, pψ, hgw, hmap⟩ := exists_refactor L.isLB x.P.isLB e ψ' ((isGen_iff ψ').1 hψ')
  have H' : PMaps ψ' (K := PUnit) (fun _ => eSec x.P.A) (fun _ => eSec (KeyVals.bG G ξ')) (fun _ => 1) x.rig
      (KeyVals.bL L ξ').rig (spMap f) :=
    (maps_iff ψ' _ _ _ x.rig (KeyVals.bL L ξ').rig (spMap f) _
      (rigPull_le (G' := x.P.A) φ' (spMap f) he' (KeyVals.bL L ξ').L) (fun _ => rfl)).1 hrig'
  have c : spMap (f.comp r) ≫ ξ = spMap f ≫ ξ' := by rw [spMap_comp, Category.assoc, hξ]
  have H := hmap L.rig (KeyVals.bL L ξ).rig (KeyVals.bL L ξ').rig x.rig he he' c (pmaps_bL L ξ) (pmaps_bL L ξ') H'
  have hD1 : ∀ a, Chart.dualMapR r (algebraMap R _ a) = algebraMap R' _ (r a) := fun a => by
    ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have hD2 : Chart.dualMapR r DualNumber.eps = DualNumber.eps := by
    ext <;> simp [Chart.dualMapR]
  refine ⟨φ' ≫ m, he, ψ, F'.comp (Chart.dualMapR r), hφ, (isGen_iff ψ).2 pψ,
    (maps_iff ψ _ _ _ x.rig (KeyVals.bL L ξ).rig (spMap (f.comp r)) _
      (rigPull_le (G' := x.P.A) (φ' ≫ m) (spMap (f.comp r)) he (KeyVals.bL L ξ).L) (fun _ => rfl)).2 H,
    ?_, fun a => ?_, ?_, fun j => ?_⟩
  · refine GlobalTheory.KeyPow.appLE_eq_of_stalk ψ t x.th ?_
    intro z J k hJ hk
    have ha : ((φ' ≫ m) ≫ pullback.fst G.hom ξ) z ∈ L.L.U (J PUnit.unit) :=
      (mem_pull (F := pullback.fst G.hom ξ)).1 hJ
    have ha' : (φ' ≫ pullback.fst G.hom ξ') z ∈ L.L.U (J PUnit.unit) := e ▸ ha
    have hJ' : φ' z ∈ (KeyVals.bL L ξ').L.U J := (mem_pull (F := pullback.fst G.hom ξ')).2 ha'
    have hW : (𝟙 x.P.A.left) z ∈ ((KeyVals.bL L ξ').L.pull φ').U (fun _ => J) ⊓ x.P.L.U k := ⟨mem_pull.2 hJ', hk⟩
    have s2 : gs (𝟙 _ ≫ φ') z _ (t'.f J) = (gw ψ' (𝟙 _) z J k).val * gs (𝟙 _) z _ (x.th.f k) := by
      have e0 := congrArg (gs (𝟙 _) z (((KeyVals.bL L ξ').L.pull φ').U (fun _ => J) ⊓ x.P.L.U k))
        (hsec' (fun _ => J) k (fun x hx => mem_pull.1 hx.1))
      exact (gs_appLE φ' _ _ _ (𝟙 _) z hW _).symm.trans (e0.trans ((gs_mul _ z _ hW _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hW _) (gs_res _ z _ hW _))))
    have e1 := gs_locSec hU ht (𝟙 _ ≫ φ' ≫ m) z J hJ
    have e2 := gs_locSec hU' ht' (𝟙 _ ≫ φ') z J hJ'
    have e3 : (𝟙 _ ≫ φ' ≫ m) ≫ pullback.fst G.hom ξ = (𝟙 _ ≫ φ') ≫ pullback.fst G.hom ξ' := by
      rw [Category.id_comp, Category.id_comp, e]
    rw [e3] at e1
    exact e1.trans (e2.symm.trans (s2.trans (congrArg (fun u : _ˣ => u.val * _) (hgw z J k ha hk).symm)))
  · rw [RingHom.comp_apply, hD1, hF1]; rfl
  · rw [RingHom.comp_apply, hD2, hF2]
  · have hv : (y' (j.cast hg)).left ≫ m = spMap (Chart.dualMapR r) ≫ (y (j.cast hg)).left := by
      refine hP.1.hom_ext ?_ ?_
      · rw [Category.assoc, hfst, Category.assoc]
        exact hy _ hD1 hD2 _
      · rw [Category.assoc, hsnd, ← Category.assoc, Over.w (y' _), Category.assoc, Over.w (y _)]
        show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
        rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
        congr 2
        exact RingHom.ext fun a => (hD1 a).symm
    rw [← Category.assoc, hFv j, Category.assoc, hv, spMap_comp, Category.assoc]

end GlobalTheory.KeyValsTrans

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

theorem _root_.GlobalTheory.T.selfDual_and_principalCongruence_orbits_of_goodLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k : U.Comp, GlobalTheory.EqCovol.IsSelfDualTr (U.X k) ∧ ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, ∃ γ' : GL (Fin r) E, IsUStab (U.X k).Gm (U.X k).Λ γ' ∧ (∀ v ∈ (U.X k).Λ, ∃ w ∈ (U.X k).Λ, (γ' : Matrix (Fin r) (Fin r) E).mulVec v - v = l.M' • w) ∧ ∃ b ∈ Bor (U.X k).Ψ r, lact γ x = rmul (lact γ' x) b := by
  first | exact @GlobalTheory.EqCovol.selfDual_and_congr_of_isUnf | exact GlobalTheory.EqCovol.selfDual_and_congr_of_isUnf | (intros; apply GlobalTheory.EqCovol.selfDual_and_congr_of_isUnf <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

theorem _root_.GlobalTheory.T.deep_congruence_element_separates_chart_ball_thick_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (M : ℕ) (x : Frame X.Ψ r), GlobalTheory.EqCovol.IsSelfDualTr X → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → 100 * ((X.Ψ.card : ℝ) * r) ^ 4 ≤ (M : ℝ) * X.firstMinimumSq x → ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → (∀ v ∈ X.Λ, ∃ w ∈ X.Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec v - v = M • w) → ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1 := by
  first | exact @GlobalTheory.ThickSep.deep_cong_chart_sep | exact GlobalTheory.ThickSep.deep_cong_chart_sep | (intros; apply GlobalTheory.ThickSep.deep_cong_chart_sep <;> assumption)
end
