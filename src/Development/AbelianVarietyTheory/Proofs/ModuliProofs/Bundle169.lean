module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnOfPowOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle091
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle156
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvr
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle166
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle167
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle031
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle168
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PicardGroup
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_principallyPolarizedCM_extension_dvr : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp V)) [GrpObj A] (tK : SAB H (Sp K)) (φ : tK.G.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback tK.G A (spMap (algebraMap V K)) φ → Out.RelAmple tK.G tK.PP.L → Out.KTriv tK.G tK.PP.L → ∃ (t : SAB H (Sp V)) (ν : SABMap tK t (spMap (algebraMap V K))) (e : t.G ≅ A), ν.φ ≫ e.hom.left = φ ∧ IsMonHom e.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  first | exact @GlobalTheory.GoodPol.exists_sab_of_generic | exact GlobalTheory.GoodPol.exists_sab_of_generic | (intros; apply GlobalTheory.GoodPol.exists_sab_of_generic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

theorem _root_.GlobalTheory.T.exists_embeddingSections_over_field : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (K : Type) [Field K] (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (w : Ix g (N' ^ 2) → K), m ^ 2 ∣ N' → 2 ≤ m → t.HasTh (𝟙 _) w → ∃ (σ : Ix g (N' ^ 2) → LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 _)))), t.Emb m (Over.mk (𝟙 _)) σ ∧ ProjRep (idealOf (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _)) (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ := by
  first | exact @GlobalTheory.ZM.EmbField.exists_emb_field | exact GlobalTheory.ZM.EmbField.exists_emb_field | (intros; apply GlobalTheory.ZM.EmbField.exists_emb_field <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_square_level_with_given_thetaPoint : Out.Laws → Out.Laws2 → ∀ (g n j : ℕ) (J : Type), n.Prime → Odd n → 2 ≤ j → ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (P : Out.PolAV (Sp R)) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ P.A)), (P.g = g ∧ (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ (n ^ j) = 1) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ P.A), y ^ (n ^ j) = 1 → ∃! c : Ix g (n ^ j), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) = y)) → VeryDense {q | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (ψ : t'.A.left ⟶ P.A.left), RingHom.ker x = q ∧ t'.HasTh (𝟙 _) (fun a => x (v a)) ∧ (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left)} → ∃ t : TObj g ((n ^ j) ^ 2) J b (spMap β), t.HasTh (𝟙 _) v ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (ψ : t'.A.left ⟶ P.A.left), t'.HasTh (𝟙 _) (fun a => x (v a)) → (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left) → TMap t' t (spMap x) := by
  first | exact @GlobalTheory.LevelTheta.exists_level_with_theta_point | exact GlobalTheory.LevelTheta.exists_level_with_theta_point | (intros; apply GlobalTheory.LevelTheta.exists_level_with_theta_point <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.LevelCover

noncomputable section

namespace GlobalTheory.LevelQuotRep

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem isSeparated_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsQProjOver f) :
    IsSeparated f := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  unfold PSpace.str
  infer_instance

theorem exists_lift_geom {W Z : Scheme.{0}} (q : W ⟶ Z) [LocallyOfFiniteType q] [Surjective q] {K : Type} [Field K]
    [IsAlgClosed K] (x : Sp K ⟶ Z) : ∃ h : Sp K ⟶ W, h ≫ q = x := by
  obtain ⟨y, -⟩ := (pullback.snd q x).surjective (IsLocalRing.closedPoint K)
  have : JacobsonSpace ↥(pullback q x) := LocallyOfFiniteType.jacobsonSpace (pullback.snd q x)
  obtain ⟨y', -, hy'⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback q x)))
    ⟨y, trivial⟩ isOpen_univ.isLocallyClosed
  have hc : IsClosed {y'} := hy'
  refine ⟨pointOfClosedPoint (pullback.snd q x) y' hc ≫ pullback.fst q x, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

theorem finite_etale_onto_spMap {K L : Type} [Field K] [Field L] [CharZero K] [CharZero L] [FiniteDimensional ℚ L]
    (k : K →+* L) : IsFinite (spMap k) ∧ Etale (spMap k) ∧ Surjective (spMap k) := by
  algebraize [k]
  have : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun x => by simp
  have hf : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  refine ⟨?_, ?_, ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩⟩
  · rw [IsFinite.SpecMap_iff]
    exact hf
  · rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
    have : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact (⟨inferInstance, inferInstance⟩ : Algebra.Etale K L)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}

theorem finiteDimensional_KA (l : Level H) : FiniteDimensional ℚ (KA l) := by
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  rcases hx with rfl | rfl
  · refine IsIntegral.of_pow two_pos ?_
    rw [H.sqrt_neg_disc_sq]
    exact (isIntegral_algebraMap (x := (H.d : ℚ))).neg
  · refine IsIntegral.of_pow l.A_pos ?_
    rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
    exact isIntegral_one

section Obj

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {b : Base l B} {b' : Base l B'} {b'' : Base l B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {o : Obj D l b s} {o' : Obj D l b' s'} {o'' : Obj D l b'' s''}

theorem obj_comp {f : S' ⟶ S} {f' : S'' ⟶ S'} (m' : ObjMap o'' o' f') (m : ObjMap o' o f) :
    Nonempty (ObjMap o'' o (f' ≫ f)) :=
  ⟨(((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o' o'').2 f f' m).1 m').choose⟩

theorem obj_cancel {f : S' ⟶ S} {e : S'' ⟶ S} (m : ObjMap o' o f) (n : ObjMap o'' o e) (g : S'' ⟶ S')
    (he : g ≫ f = e) : Nonempty (ObjMap o'' o' g) := by
  subst he
  exact ⟨(((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o' o'').2 f g m).2 n).choose⟩

theorem obj_pull_same (o : Obj D l b s) (f : S' ⟶ S) : ∃ o' : Obj D l b (f ≫ s), Nonempty (ObjMap o' o f) :=
  obj_pull E H D l _ _ b b (RingHom.id _) _ _ s _ f rfl rfl (by rw [spMap_id', Category.comp_id]) o

end Obj

variable {Xo₂ : Moduli D l₂} (Q : LevelQuot l Xo₂)

theorem exists_lowers {B : Type} [CommRing B] {b : Base l B} {T : Scheme.{0}} {t : T ⟶ Sp B} {o : Obj D l b t}
    {z : T ⟶ Q.X} (n : ObjMap o Q.univ z) (y : T ⟶ Xo₂.X) (hy : y ≫ Q.π = z) :
    ∃ mu : SABMap o.t Xo₂.univ.t y, Lowers l Xo₂.univ o.eta o.etaA y mu.φ := by
  obtain ⟨mu, hmu⟩ := sab_cancel Q.m n.toSABMap y hy
  refine ⟨mu, fun a => sec_cancel mu Q.m _ _ ?_, fun a => sec_cancel mu Q.m _ _ ?_⟩
  · rw [hmu, Q.eta, ← Category.assoc, hy]; exact n.eta a
  · rw [hmu, Q.etaA, ← Category.assoc, hy]; exact n.etaA a

theorem hom_unique {B : Type} [CommRing B] {b : Base l B} {T : Scheme.{0}} [IsReduced T] {t : T ⟶ Sp B}
    {o : Obj D l b t} {f f' : T ⟶ Q.X} (h : f ≫ Q.s = f' ≫ Q.s) (m : ObjMap o Q.univ f) (m' : ObjMap o Q.univ f') :
    f = f' := by
  have := isSeparated_of_qproj Q.qproj
  have := Q.fin
  have := Q.onto
  refine (hom_eq_iff_forall_isAlgClosed Q.s h).mpr fun K _ _ x => ?_
  obtain ⟨ox, ⟨n⟩⟩ := obj_pull_same o x
  obtain ⟨u⟩ := obj_comp n m
  obtain ⟨u'⟩ := obj_comp n m'
  obtain ⟨y, hy⟩ := exists_lift_geom Q.π (x ≫ f)
  obtain ⟨y', hy'⟩ := exists_lift_geom Q.π (x ≫ f')
  obtain ⟨mu, hmu⟩ := exists_lowers Q u y hy
  obtain ⟨mu', hmu'⟩ := exists_lowers Q u' y' hy'
  rw [← hy, ← hy']
  refine Q.fibre K y y' ox.t mu mu' ox.eta ox.etaA ?_ hmu hmu'
  rw [← Q.overK, ← Category.assoc, ← Category.assoc, hy, hy', Category.assoc, Category.assoc, h]

def baseUp : Base l (KA l₂) where
  unit := (baseKA l₂).unit
  ρ := Q.jK (baseKA l).ρ
  ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  ζ := Q.jK (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective Q.jK.injective

theorem baseKA_rho_coe (l : Level H) : (((baseKA l).ρ : KA l) : ℂ) = H.rt0 := rfl

theorem baseUp_rho_coe : (((baseUp Q).ρ : KA l₂) : ℂ) = (((baseKA l).ρ : KA l) : ℂ) := Q.jK_val (baseKA l).ρ

theorem baseUp_rho : (baseUp Q).ρ = (baseKA l₂).ρ :=
  Subtype.ext ((baseUp_rho_coe Q).trans ((baseKA_rho_coe l).trans (baseKA_rho_coe l₂).symm))

theorem baseUp_zeta (hd : l.A ∣ l₂.A) : (baseUp Q).ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := Subtype.ext (by
  rw [IntermediateField.coe_pow]
  exact (Q.jK_val _).trans (zeta_dvd l₂.A_pos hd))

theorem exists_cover (hL : Out.Laws) (hpq : 1 ≤ D.p + D.q) (hd : l.Dvd l₂) {S : Scheme.{0}} [IsReduced S]
    {s' : S ⟶ Sp (KA l)} (ob : Obj D l (baseKA l) s') :
    ∃ (S₂ : Scheme.{0}) (q : S₂ ⟶ S) (g : S₂ ⟶ Q.X) (s₂ : S₂ ⟶ Sp (KA l₂)) (o : Obj D l (baseUp Q) s₂),
      IsFinite q ∧ Etale q ∧ Surjective q ∧ g ≫ Q.s = q ≫ s' ∧ Nonempty (ObjMap o ob q) ∧
        Nonempty (ObjMap o Q.univ g) := by
  have := finiteDimensional_KA l₂
  obtain ⟨k1, k2, k3⟩ := finite_etale_onto_spMap Q.jK
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseUp Q) Q.jK _ _ s' (pullback.snd s' (spMap Q.jK))
    (pullback.fst _ _) rfl rfl pullback.condition ob
  obtain ⟨S₂, p, o₂, m, hf, he, hs, ⟨hm₁, hm₂⟩, -⟩ := GlobalTheory.T.exists_finiteEtale_deeper_level_cover hL E H D l l₂ _ (baseUp Q) (baseKA l₂) _ _ o₁ hpq hd
    (baseUp_rho Q) (baseUp_zeta Q hd.2.2)
  have hr : IsReduced S₂ := isReduced_of_smooth_of_isReduced (p ≫ pullback.fst s' (spMap Q.jK))
  obtain ⟨f₂, ⟨hf₂, ⟨u⟩⟩, -⟩ := Xo₂.rep S₂ _ hr o₂
  let o := ObjLower.lower o₂ hd (baseUp_rho Q) (baseUp_zeta Q hd.2.2)
  let mo : ObjMap o o₁ p := ⟨m, hm₁, hm₂⟩
  obtain ⟨z, hz⟩ := sab_comp u.toSABMap Q.m rfl
  refine ⟨S₂, p ≫ pullback.fst _ _, f₂ ≫ Q.π, _, o, inferInstance, inferInstance, inferInstance, ?_,
    obj_comp mo n₁, ⟨⟨z, fun a => ?_, fun a => ?_⟩⟩⟩
  · rw [Category.assoc, Q.overK, ← Category.assoc, hf₂, Category.assoc, Category.assoc, pullback.condition]
  · show (o₂.eta a ^ (l₂.M / l.M)).left ≫ z.φ = _
    rw [hz, ← Category.assoc, sec_pow u.toSABMap _ _ (u.eta a), Category.assoc, Q.eta, Category.assoc]
  · show (o₂.etaA a ^ (l₂.A / l.A)).left ≫ z.φ = _
    rw [hz, ← Category.assoc, sec_pow u.toSABMap _ _ (u.etaA a), Category.assoc, Q.etaA, Category.assoc]

end GlobalTheory.LevelQuotRep

namespace GlobalTheory


open LevelQuotRep in
theorem levelQuot_represents : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (KA l)), IsReduced S → ∀ ob : Obj D l (baseKA l) s', ∃! f : S ⟶ Q.X, f ≫ Q.s = s' ∧ Nonempty (ObjMap ob Q.univ f) := by
  intro hL hL2 E _ _ _ H D l l₂ Xo₂ Q hpq hd S s' hS ob
  refine existsUnique_of_exists_of_unique ?_
    fun f f' ⟨h, ⟨m⟩⟩ ⟨h', ⟨m'⟩⟩ => hom_unique Q (h.trans h'.symm) m m'
  obtain ⟨S₂, q, g, s₂, o, hf, he, hs, hg, ⟨mq⟩, ⟨mg⟩⟩ := exists_cover Q hL hpq hd ob
  have key : pullback.fst q q ≫ g = pullback.snd q q ≫ g := by
    have : IsReduced (pullback q q) := isReduced_of_smooth_of_isReduced (pullback.fst q q ≫ q)
    obtain ⟨oR, ⟨n⟩⟩ := obj_pull_same o (pullback.fst q q)
    obtain ⟨n₁⟩ := obj_comp n mq
    obtain ⟨n'⟩ := obj_cancel mq n₁ (pullback.snd q q) pullback.condition.symm
    obtain ⟨u⟩ := obj_comp n mg
    obtain ⟨u'⟩ := obj_comp n' mg
    exact hom_unique Q (by rw [Category.assoc, Category.assoc, hg, pullback.condition_assoc]) u u'
  have hcoeq : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ S₂), g₁ ≫ q = g₂ ≫ q → g₁ ≫ g = g₂ ≫ g := fun g₁ g₂ h => by
    have := pullback.lift g₁ g₂ h ≫= key
    rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this
  have hfac : q ≫ EffectiveEpi.desc q g hcoeq = g := EffectiveEpi.fac q g hcoeq
  refine ⟨EffectiveEpi.desc q g hcoeq, ?_, ?_⟩
  · rw [← cancel_epi q, ← Category.assoc, hfac, hg]
  · exact GlobalTheory.T.nonempty_objMap_of_finite_etale_surjective_cover hL hL2 E H D l _ _ _ _ _ _ _ _ _ _ _ _ Q.univ ob o q _ (Or.inl hS) hf he hs ⟨mq⟩
      (hfac.symm ▸ ⟨mg⟩)

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
open Classical

namespace GlobalTheory.ModelOfOutput

theorem exists_openImmersion_section {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {U : Scheme.{0}} [IsIntegral U] (g : U ⟶ Sp R) [IsSeparated g] [LocallyOfFiniteType g]
    (x : Sp K ⟶ U) [IsDominant x] (hx : x ≫ g = spMap (algebraMap R K)) :
    ∃ (W : (Sp R).Opens) (j : W.toScheme ⟶ U), Dense (W : Set (Sp R)) ∧ IsOpenImmersion j ∧ IsDominant j ∧
      j ≫ g = W.ι := by
  obtain ⟨e, he⟩ := IsGenericPointHom.fractionField R K
  obtain ⟨W, hW, j, h₁, h₂⟩ := spread_out_of_isGermInjective' (𝟙 (Sp R)) g (x := genericPoint (Sp R)) (e.inv ≫ x)
    (by rw [Category.assoc, hx, Category.comp_id, Iso.inv_comp_eq]; exact he.symm)
  rw [Category.comp_id] at h₂
  have hd : IsDominant j := by
    have : IsDominant (W.fromSpecStalkOfMem _ hW ≫ j) := h₁ ▸ inferInstance
    exact IsDominant.of_comp (W.fromSpecStalkOfMem _ hW) j
  have hr : Set.range j ⊆ Set.range (g ⁻¹ᵁ W).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    show g (j w) ∈ W
    rw [← Scheme.Hom.comp_apply, h₂]
    exact w.2
  have e₁ := IsOpenImmersion.lift_fac (g ⁻¹ᵁ W).ι j hr
  set j' := IsOpenImmersion.lift (g ⁻¹ᵁ W).ι j hr
  have : IsDominant (j' ≫ (g ⁻¹ᵁ W).ι) := e₁.symm ▸ hd
  have : IsDominant j' := IsDominant.of_comp_of_isOpenImmersion _ (g ⁻¹ᵁ W).ι
  have e₂ : j' ≫ g ∣_ W = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, e₁, h₂, Category.id_comp]
  have e₃ : g ∣_ W ≫ j = (g ⁻¹ᵁ W).ι :=
    ext_of_isDominant_of_isSeparated g (by rw [Category.assoc, h₂, morphismRestrict_ι]) j'
      (by rw [← Category.assoc, e₂, Category.id_comp, e₁])
  have : IsIso j' := ⟨g ∣_ W, e₂, by
    rw [← cancel_mono (g ⁻¹ᵁ W).ι, Category.assoc, e₁, e₃, Category.id_comp]⟩
  refine ⟨W, j, W.isOpen.dense ⟨_, hW⟩, ?_, hd, h₂⟩
  rw [← e₁]
  infer_instance

theorem flat_ratModel {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [h : GlobalTheory.ZH.ArithBase o Ω]
    (M : GlobalTheory.ZH.RatModel o Ω) : Flat M.s := by
  have := h.ded
  have := M.sep
  have : IsSchemeTheoreticallyDominant M.pt := .of_isDominant _
  have : QuasiCompact M.pt := ⟨fun U _ _ => (Set.toFinite _).isCompact⟩
  have : Flat (M.pt ≫ M.s) := by
    rw [M.pt_s]
    refine Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 ?_)
    have : FaithfulSMul o Ω := (faithfulSMul_iff_algebraMap_injective o Ω).2 h.inj
    infer_instance
  exact flat_of_schemeDominant_of_isDedekindDomain (O := CommRingCat.of o) M.pt M.s

theorem exists_zOn : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (t₀ : SAB H (Sp R)) (S : GlobalTheory.ZH.ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ t₀.G.left) (act : OAct (𝓞 E) ρ.P.A) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : GlobalTheory.ZH.ZHOut ρ M U₀ EE) (m : ℕ) (r₀ : ℤ), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → S.Over₀ M U₀ → IsOpen (abLocus Z.G) → IsGrpPullback ρ.P.A t₀.G (spMap (Subalgebra.inclusion h).toRingHom) φ → LBIso ρ.P.L (t₀.PP.L.pull φ) → (∀ a, (act.act a).left ≫ φ = φ ≫ (t₀.act.act a).left) → (letI := ρ.P.isAb.comm; ∀ a, LBIso (cubeLB ρ.P.A ![fst _ _ ≫ act.act a, snd _ _] ρ.P.L) (cubeLB ρ.P.A ![fst _ _, snd _ _ ≫ act.act (H.bar a)] ρ.P.L)) → (letI := ρ.P.isAb.comm; LBIso ρ.P.L (cubeLB ρ.P.A ![𝟙 _, act.act H.w0] ρ.P.L)) → (∀ r : ℤ, r₀ ≤ r → ∃ A : GlobalTheory.LN.AmpFrames Z.G Z.L.L (m ^ 2), A.r = r ∧ A.s = 1) → ∃ C : ZOn (spMap (algebraMap o R)) t₀ m, IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L (m ^ 2), A.r = r ∧ A.s = 1 := by
  intro _ _ E _ _ _ H o Ω _ _ _ hb R t₀ S ρ h φ act M U₀ EE Z m r₀ _ hfr hO hop hφ hL hact hadj hprim hamp
  obtain ⟨act', h₂, h₃, hact', hgood⟩ := GlobalTheory.TripleOut.exists_triple GlobalTheory.homExtension_semiAbelian_dvr o Ω S ρ M U₀ EE Z
    E H act hO hadj hprim
  let t : SAB H M.Z := SAB.mk (H := H) Z.G Z.semi act' Z.L Z.cub Z.sym h₂ h₃
  have : IsFractionRing R Ω := IsFractionRing.of_field R Ω fun y => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hfr y
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    exact (GlobalTheory.ZH.top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hO.ne)
  have ex := IsOpenImmersion.lift_fac U₀.ι M.pt hr
  set x := IsOpenImmersion.lift U₀.ι M.pt hr
  have : IsDominant (x ≫ U₀.ι) := ex.symm ▸ inferInstance
  have : IsDominant x := IsDominant.of_comp_of_isOpenImmersion _ U₀.ι
  have : Nonempty U₀.toScheme := ⟨⟨_, hO.ne.some_mem⟩⟩
  have : IsIntegral U₀.toScheme := isIntegral_of_isOpenImmersion U₀.ι
  let g : U₀.toScheme ⟶ Sp R := Z.u₀ ≫ spMap (Subalgebra.inclusion h).toRingHom
  have hx : x ≫ g = spMap (algebraMap R Ω) := by
    rw [← Category.assoc, Z.u₀_gen x ex, ← Spec.map_comp]
    rfl
  have hg : g ≫ spMap (algebraMap o R) = U₀.ι ≫ M.s := by
    refine ext_of_isDominant x ?_
    rw [← Category.assoc, hx, ← Category.assoc, ex, M.pt_s, ← Spec.map_comp]
    rfl
  have := M.sep
  have := M.lft
  have : IsSeparated (g ≫ spMap (algebraMap o R)) := hg ▸ inferInstance
  have : IsSeparated g := IsSeparated.of_comp g (spMap (algebraMap o R))
  have : LocallyOfFiniteType (g ≫ spMap (algebraMap o R)) := hg ▸ inferInstance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (spMap (algebraMap o R))
  obtain ⟨W, j, hW, hj₁, hj₂, hj⟩ := exists_openImmersion_section g x hx
  letI : (Over.pullback W.ι).Monoidal := (Over.instBraidedPullback (f := W.ι)).toMonoidal
  letI : GrpObj ((Over.pullback W.ι).obj t₀.G) := Functor.grpObjObj (F := Over.pullback W.ι)
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull GlobalTheory.laws3.cubePull W.ι t₀
  set tW : SAB H W.toScheme := ⟨(Over.pullback W.ι).obj t₀.G, IsSemiAbelian.pullback W.ι t₀.G t₀.semi,
    OAct.pullback W.ι t₀.G t₀.act, PP', cub, sym, adj, prim⟩
  clear_value tW
  have hP := (isGrpPullback_pullback ρ.P.A Z.u₀).comp hφ
  let ψ : tW.G.left ⟶ pullback ρ.P.A.hom Z.u₀ :=
    hP.1.lift m₁.φ (tW.G.hom ≫ j) (by rw [m₁.cart.1.w, Category.assoc, hj])
  have ψ₁ : ψ ≫ pullback.fst ρ.P.A.hom Z.u₀ ≫ φ = m₁.φ := hP.1.lift_fst _ _ _
  have ψ₂ : ψ ≫ pullback.snd ρ.P.A.hom Z.u₀ = tW.G.hom ≫ j := hP.1.lift_snd _ _ _
  have hψ : IsGrpPullback tW.G ((Over.pullback Z.u₀).obj ρ.P.A) j ψ :=
    hP.cancel (m₁.cart.congr hj.symm ψ₁.symm) ψ₂
  have hA : IsProper ρ.P.A.hom := GlobalTheory.ZH.isProper_hom_of_relAmple ρ.P.ample
  have hA' : IsProper tW.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) hψ.1 (inferInstanceAs (IsProper (pullback.snd ρ.P.A.hom Z.u₀)))
  have hψa : ∀ a, (tW.act.act a).left ≫ ψ = ψ ≫ ((Over.pullback Z.u₀).map (act.act a)).left := fun a => by
    have A : ((Over.pullback Z.u₀).map (act.act a)).left ≫ pullback.fst ρ.P.A.hom Z.u₀ =
      pullback.fst ρ.P.A.hom Z.u₀ ≫ (act.act a).left := pullback.lift_fst _ _ _
    have B : ((Over.pullback Z.u₀).map (act.act a)).left ≫ pullback.snd ρ.P.A.hom Z.u₀ =
      pullback.snd ρ.P.A.hom Z.u₀ := Over.w ((Over.pullback Z.u₀).map (act.act a))
    apply hP.1.hom_ext
    · calc ((tW.act.act a).left ≫ ψ) ≫ pullback.fst ρ.P.A.hom Z.u₀ ≫ φ
          = m₁.φ ≫ (t₀.act.act a).left := by rw [Category.assoc, ψ₁]; exact m₁.act a
        _ = ψ ≫ (pullback.fst ρ.P.A.hom Z.u₀ ≫ (act.act a).left) ≫ φ := by
          rw [← ψ₁]; simp only [Category.assoc, hact]
        _ = _ := by rw [← A]; simp only [Category.assoc]
    · calc ((tW.act.act a).left ≫ ψ) ≫ pullback.snd ρ.P.A.hom Z.u₀
          = tW.G.hom ≫ j := by rw [Category.assoc, ψ₂, ← Category.assoc, Over.w]
        _ = ψ ≫ ((Over.pullback Z.u₀).map (act.act a)).left ≫ pullback.snd ρ.P.A.hom Z.u₀ := by rw [B, ψ₂]
        _ = _ := (Category.assoc _ _ _).symm
  have hLW : LBIso tW.PP.L (t.PP.L.pull (ψ ≫ Z.φ)) := by
    have a₁ : LBIso tW.PP.L (t₀.PP.L.pull m₁.φ) := by
      obtain ⟨w, hw, -⟩ := m₁.lin
      exact ⟨w, hw⟩
    have a₂ : LBIso (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom Z.u₀)) (t₀.PP.L.pull m₁.φ) :=
      GenSpread.lbIso_pull_of_lbIso hL _ (by rw [Category.assoc, ψ₁])
    have a₃ : LBIso (Z.L.L.pull (ψ ≫ Z.φ)) (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom Z.u₀)) :=
      GenSpread.lbIso_pull_comp ψ rfl rfl ⟨Z.w, Z.w_gen⟩
    exact LBIso.trans tW.PP.isLB (pull_isLB t₀.PP.isLB _) (pull_isLB Z.L.isLB _) a₁
      (LBIso.trans (pull_isLB Z.L.isLB _) (pull_isLB ρ.P.isLB _) (pull_isLB t₀.PP.isLB _) a₃ a₂).symm
  obtain ⟨m₂, -⟩ := GlobalTheory.exists_sabMap_of_lbIso E H M.Z W.toScheme t tW (j ≫ U₀.ι) (ψ ≫ Z.φ)
    ⟨inferInstance, fun y _ K _ _ p _ => inferInstance⟩ (hψ.comp Z.cart)
    (fun a => by
      rw [← Category.assoc, hψa, Category.assoc, Category.assoc]
      exact congrArg (ψ ≫ ·) (hact' a)) hLW
  obtain ⟨A, hA₁, hA₂⟩ := hamp r₀ le_rfl
  have : IsDominant U₀.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact U₀.isOpen.dense hO.ne⟩
  exact ⟨⟨M.Z, M.s, GlobalTheory.IsNormalScheme.of_pred hO.normal, hO.proj, flat_ratModel M, t, Z.qproj,
    hgood (GlobalTheory.ZH.abOpen_of_isOpen_abLocus o Ω S ρ M U₀ EE Z hO hop), W, hW, j ≫ U₀.ι, inferInstance, inferInstance,
    by rw [Category.assoc, ← hg, ← Category.assoc, hj], tW, m₁, m₂, A⟩, M.integral, hA₂,
    fun r hr => hamp r (hA₁ ▸ hr)⟩

end GlobalTheory.ModelOfOutput
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.thetaGroupK_trivial_of_principal_genericFibre_dvr : Laws → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → RelAmple B M.L.L → KTriv B M.L.L := by
  first | exact @GlobalTheory.KTrivSpread.kTriv_of_generic_fibre | exact GlobalTheory.KTrivSpread.kTriv_of_generic_fibre | (intros; apply GlobalTheory.KTrivSpread.kTriv_of_generic_fibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.cubeLineBundle_adjoint_iff_hermForm_adjoint : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (f f' : P.A ⟶ P.A) (F F' : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)), u.IsAH Hm χ → IsMonHom f → IsMonHom f' → (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f') → (LBIso (cubeLB P.A ![fst P.A P.A ≫ f, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ f'] P.L) ↔ ∀ z w, hermForm Hm (F z) w = hermForm Hm z (F' w)) := by
  first | exact @GlobalTheory.HermAdjoint.lbIso_cubeLB_iff_hermForm | exact GlobalTheory.HermAdjoint.lbIso_cubeLB_iff_hermForm | (intros; apply GlobalTheory.HermAdjoint.lbIso_cubeLB_iff_hermForm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.principal_siegel_of_generic_principal_special_ample : Out.Laws → Out.Laws2 → ∀ (h k : ℕ), Odd k → 3 ≤ k → ∀ (B : Type) [CommRing B] (ζ : B) (C O : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [CommRing O] [IsLocalRing O] [Algebra O C], IsUnitBall O C → ∀ p : ℕ, p.Prime → ‖(p : C)‖ < 1 → ∀ (β : B →+* O) (c : SiegPre h k ζ (spMap β)), (∃ c' : SiegPre h k ζ (spMap (algebraMap O C) ≫ spMap β), SiegPB c' c (spMap (algebraMap O C)) ∧ c'.Principal) → Out.RelAmple (Over.mk (pullback.snd c.A.hom (spMap (IsLocalRing.residue O)))) (c.diag.pull (pullback.fst c.A.hom (spMap (IsLocalRing.residue O)))) → c.Principal := by
  first | exact @GlobalTheory.PrincipalIntegral.principal_of_generic_of_ample_special | exact GlobalTheory.PrincipalIntegral.principal_of_generic_of_ample_special | (intros; apply GlobalTheory.PrincipalIntegral.principal_of_generic_of_ample_special <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.levelLabel_extends_of_orthogonal_to_extended : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X) (s : U ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (μ₀ : SABMap o.t t j), IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsUnit (l.A : Γ(X, ⊤)) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (a : D.La), (∀ a', (∃ (W : X.Opens) (σ : W.toScheme ⟶ t.G.left), Set.range x ⊆ W ∧ σ ≫ t.G.hom = W.ι ∧ pullback.fst W.ι j ≫ σ = pullback.snd W.ι j ≫ (o.etaA a').left ≫ μ₀.φ) → (l.A : ℤ) ∣ D.EF a a') → (∃ (W : X.Opens) (σ : W.toScheme ⟶ t.G.left), Set.range x ⊆ W ∧ σ ≫ t.G.hom = W.ι ∧ pullback.fst W.ι j ≫ σ = pullback.snd W.ι j ≫ (o.etaA a).left ≫ μ₀.φ) := by
  first | exact @GlobalTheory.extends_of_orthogonal_to_extended | exact GlobalTheory.extends_of_orthogonal_to_extended | (intros; apply GlobalTheory.extends_of_orthogonal_to_extended <;> assumption)
end
