module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrimitiveCocycle
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PullSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HalfRatio

variable {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
    {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left}

theorem lamVal_change (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)) (hw : w.IsGen)
    {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) (z : Z) {J₁ J₂ : (Z ⟶ B.left) → M.ι} {J₁' J₂' : (Z ⟶ B'.left) → M'.ι}
    (h₁ : Good M z J₁) (h₂ : Good M z J₂) (h₁' : Good M' z J₁') (h₂' : Good M' z J₂') :
    lamVal w p z J₁ J₁' =
      (∏ I, gm (p ≫ β₂ ≫ PrimCocycle.lamφ B I) z (M.U (J₁ (p ≫ β₂ ≫ PrimCocycle.lamφ B I)) ⊓ M.U (J₂ (p ≫ β₂ ≫ PrimCocycle.lamφ B I)))
          (M.g (J₁ (p ≫ β₂ ≫ PrimCocycle.lamφ B I)) (J₂ (p ≫ β₂ ≫ PrimCocycle.lamφ B I))) ^ PrimCocycle.lamε I) *
      (∏ I, gm (p ≫ PrimCocycle.lamφ B' I) z (M'.U (J₁' (p ≫ PrimCocycle.lamφ B' I)) ⊓ M'.U (J₂' (p ≫ PrimCocycle.lamφ B' I)))
          (M'.g (J₁' (p ≫ PrimCocycle.lamφ B' I)) (J₂' (p ≫ PrimCocycle.lamφ B' I))) ^ PrimCocycle.lamε I)⁻¹ *
      lamVal w p z J₂ J₂' := by
  have mQ : ∀ {J : (Z ⟶ B.left) → M.ι}, Good M z J → p z ∈ LB.wchart (abelian₂ B M) (fun _ : PUnit => β₂)
      (fun _ I => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)) := fun hJ =>
    Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun I => hJ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)
  have mQ' : ∀ {J : (Z ⟶ B.left) → M.ι}, Good M z J → (p ≫ β₂) z ∈ (abelian₂ B M).U
      (fun I => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)) := fun hJ =>
    Set.mem_iInter.2 fun I => hJ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)
  have mD : ∀ {J' : (Z ⟶ B'.left) → M'.ι}, Good M' z J' → p z ∈ (abelian₂ B' M').U
      (fun I => J' (p ≫ (psum B' (x2 B') I.down).left)) := fun hJ =>
    hJ.mem (fun I : ULift (Finset (Fin 2)) => (psum B' (x2 B') I.down).left) p
  have mi : p z ∈ (LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U
      (fun _ I => J₁ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left), fun I => J₁' (p ≫ (psum B' (x2 B') I.down).left)) :=
    TopologicalSpace.Opens.mem_inf.2 ⟨mQ h₁, mD h₁'⟩
  have mj : p z ∈ (LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U
      (fun _ I => J₂ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left), fun I => J₂' (p ≫ (psum B' (x2 B') I.down).left)) :=
    TopologicalSpace.Opens.mem_inf.2 ⟨mQ h₂, mD h₂'⟩
  have e := congrArg (gm p z _) (hw (fun _ I => J₁ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left), fun I => J₁' (p ≫ (psum B' (x2 B') I.down).left))
    (fun _ I => J₂ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left), fun I => J₂' (p ≫ (psum B' (x2 B') I.down).left)))
  rw [gm_res p z _ (TopologicalSpace.Opens.mem_inf.2 ⟨mi, mj⟩), map_mul, gm_res p z _ (TopologicalSpace.Opens.mem_inf.2 ⟨mi, mj⟩)] at e
  refine e.trans (congrArg (· * _) ?_)
  have gQ := gm_linComb (abelian₂ B M) (fun _ : PUnit => β₂) (fun _ => 1) p z _ _ (mQ h₁) (mQ h₂)
  have gQ' := gm_linComb M (fun I : ULift (Finset (Fin 2)) => (psum B (x2 B) I.down).left) (fun I => (-1) ^ (2 - I.down.card)) (p ≫ β₂) z _ _ (mQ' h₁) (mQ' h₂)
  have gD := gm_linComb M' (fun I : ULift (Finset (Fin 2)) => (psum B' (x2 B') I.down).left) (fun I => (-1) ^ (2 - I.down.card)) p z _ _ (mD h₁') (mD h₂')
  rw [Fintype.prod_unique, zpow_one] at gQ
  simp only [Category.assoc] at gQ'
  erw [map_mul, map_inv, gm_res p z _ (TopologicalSpace.Opens.mem_inf.2 ⟨mi, mj⟩), gm_res p z _ (TopologicalSpace.Opens.mem_inf.2 ⟨mi, mj⟩), gQ, gQ', gD]

end GlobalTheory.HalfRatio

namespace GlobalTheory.HalfRatio
theorem ag1 {G : Type*} [CommGroup G] (a b c d : G) : (a⁻¹*b*c*d⁻¹) * (a*b⁻¹*c⁻¹*d) = 1 := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv, ofMul_one]; abel
theorem ag2 {G : Type*} [CommGroup G] (A₂ B₂ C₂ TA TDl TQl TQt : G) (h1 : TA * TDl = 1) (h2 : TQl * TQt = 1) : (TA*A₂)⁻¹ * (TQl * TDl⁻¹ * B₂) * (TQt * C₂) = A₂⁻¹ * B₂ * C₂ := by
  rw [eq_inv_of_mul_eq_one_right h1, eq_inv_of_mul_eq_one_right h2]
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv, inv_inv]; abel
end GlobalTheory.HalfRatio

namespace GlobalTheory.HalfRatio

theorem exists_unitOn (K : Type) [Field K] (z : Sp K) (r : ((Sp K).presheaf.stalk z)ˣ) :
    ∃ k : Kˣ, gm (𝟙 (Sp K)) z ⊤ (unitOn k) = r := by
  obtain ⟨U, hz, f, hf⟩ := TopCat.Presheaf.germ_exist (Sp K).presheaf r.val
  have hs : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain rfl : U = ⊤ := top_unique fun x _ => (Subsingleton.elim z x) ▸ hz
  have h0 : (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom f ≠ 0 := fun h => by
    have : f = 0 := ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply f).symm.trans
      ((congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom h).trans (map_zero _))
    rw [this, map_zero] at hf
    exact r.ne_zero hf.symm
  refine ⟨Units.mk0 _ h0, Units.ext ((gm_val _ z ⊤ trivial _).trans (Eq.trans ?_ hf))⟩
  exact congrArg ((Sp K).presheaf.germ ⊤ z hz).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply f)

theorem prod_neg {S : Scheme.{0}} {B : Over S} [GrpObj B] {T : Over S} (x y : T ⟶ B) {Z : Scheme.{0}} (κ : Z ⟶ T.left)
    {U : Type} [CommGroup U] (h : (Z ⟶ B.left) → U) : ∏ k, h (κ ≫ lamPts x y k) ^ negε k =
      (h (κ ≫ (x * y).left))⁻¹ * h (κ ≫ x.left) * h (κ ≫ y.left) * (h (κ ≫ (1 : T ⟶ B).left))⁻¹ := by
  simp only [Fin.prod_univ_four]
  simp [lamPts, negε]
end GlobalTheory.HalfRatio

namespace GlobalTheory.HalfRatio
theorem prod_tau {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a b : D.X) {U : Type} [CommGroup U]
    (h : ((TK R).left ⟶ D.P.A.left) → U) :
    ∏ k : ((PUnit ⊕ PUnit) ⊕ PUnit) ⊕ PUnit, h (𝟙 _ ≫ Sum.elim (Sum.elim (Sum.elim (fun _ => ptK (D.c (a + b))) fun _ => ptK (D.c a))
        fun _ => ptK (D.c b)) (fun _ => (toUnit (TK R)).left ≫ eSec D.P.A) k) ^
      (Sum.elim (Sum.elim (Sum.elim (fun _ => -1) fun _ => - -1) fun _ => - -1) (fun _ => -1) k : ℤ) =
      (h (ptK (D.c (a + b))))⁻¹ * h (ptK (D.c a)) * h (ptK (D.c b)) * (h ((toUnit (TK R)).left ≫ eSec D.P.A))⁻¹ := by
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Category.id_comp]
  simp
end GlobalTheory.HalfRatio

namespace GlobalTheory.HalfRatio
variable {R : Type} [CommRing R] [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R'] {Q : Data R} {ρ : R →+* R'}
  {D : DegPre R'} {e : D.X ≃+ Q.X} {β : D.P.A.left ⟶ Q.B.left} {β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left}

theorem prod_cancel (hpb : IsGrpPullback D.P.A Q.B (spMap ρ) β) (hsq : IsSquare β β₂)
    (hc : ∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) {κ : (TK R').left ⟶ (TK R).left}
    (hκ : κ ≫ jK R = jK R' ≫ spMap ρ) {a b : D.X} {x y : TK R' ⟶ D.P.A} (hx : x = toUnit (TK R') ≫ D.c a)
    (hy : y = toUnit (TK R') ≫ D.c b) {U : Type} [CommGroup U] (H : ((TK R').left ⟶ Q.B.left) → U) :
    (∏ I, H ((lift x y).left ≫ β₂ ≫ PrimCocycle.lamφ Q.B I) ^ PrimCocycle.lamε I) *
      ∏ k, H (κ ≫ lamPts (toUnit (TK R) ≫ Q.c (e a)) (toUnit (TK R) ≫ Q.c (e b)) k) ^ negε k = 1 := by
  have hT : ∀ χ, (toUnit (TK R') ≫ D.c χ).left ≫ β = κ ≫ (toUnit (TK R) ≫ Q.c (e χ)).left := fun χ => by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hc χ]
    show jK R' ≫ spMap ρ ≫ _ = κ ≫ jK R ≫ _
    rw [← Category.assoc, ← hκ, Category.assoc]
  have c0 : D.c 0 = 1 := mul_eq_left.1 ((D.c_add 0 0).symm.trans (by rw [add_zero]))
  have q0 : Q.c 0 = 1 := mul_eq_left.1 ((Q.c_add 0 0).symm.trans (by rw [add_zero]))
  have hxy : toUnit (TK R') ≫ D.c (a + b) = x * y := by
    rw [hx, hy, ← MonObj.comp_mul]; exact congrArg (toUnit (TK R') ≫ ·) (D.c_add a b)
  let T' : Over (Sp R) := Over.mk ((TK R').hom ≫ spMap ρ)
  let up : (TK R' ⟶ D.P.A) → (T' ⟶ Q.B) := fun u => Over.homMk (u.left ≫ β)
    ((Category.assoc _ _ _).trans ((congrArg (u.left ≫ ·) hpb.1.w).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ spMap ρ) (Over.w u)))))
  have f₁ : ((lift x y).left ≫ β₂) ≫ (fst Q.B Q.B).left = (up x).left :=
    (Category.assoc _ _ _).trans ((congrArg ((lift x y).left ≫ ·) hsq.1).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun q : TK R' ⟶ D.P.A => q.left ≫ β) (lift_fst x y))))
  have f₂ : ((lift x y).left ≫ β₂) ≫ (snd Q.B Q.B).left = (up y).left :=
    (Category.assoc _ _ _).trans ((congrArg ((lift x y).left ≫ ·) hsq.2).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun q : TK R' ⟶ D.P.A => q.left ≫ β) (lift_snd x y))))
  have hP : ((lift x y).left ≫ β₂) ≫ (G2 Q.B).hom = T'.hom :=
    (congrArg (_ ≫ ·) (Over.w (fst Q.B Q.B)).symm).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ Q.B.hom) f₁).trans (Over.w (up x))))
  have hl : (lift (up x) (up y)).left = (lift x y).left ≫ β₂ := by
    have : lift (up x) (up y) = (Over.homMk _ hP : T' ⟶ G2 Q.B) :=
      CartesianMonoidalCategory.hom_ext _ _ ((lift_fst _ _).trans (Over.OverMorphism.ext f₁.symm))
        ((lift_snd _ _).trans (Over.OverMorphism.ext f₂.symm))
    exact congrArg (fun q : T' ⟶ G2 Q.B => q.left) this
  have ux : (up x).left = κ ≫ (toUnit (TK R) ≫ Q.c (e a)).left := hx ▸ hT a
  have uy : (up y).left = κ ≫ (toUnit (TK R) ≫ Q.c (e b)).left := hy ▸ hT b
  have uxy : (up x * up y).left = κ ≫ (toUnit (TK R) ≫ Q.c (e a) * toUnit (TK R) ≫ Q.c (e b)).left := by
    refine (hpb.2 _ x y (up x) (up y) rfl rfl).trans ?_
    rw [← hxy, hT, map_add (f := _), Q.c_add, MonObj.comp_mul]
  have u1 : (1 : T' ⟶ Q.B).left = κ ≫ (1 : TK R ⟶ Q.B).left := by
    have h : up 1 * up 1 = up 1 := Over.OverMorphism.ext ((hpb.2 _ 1 1 (up 1) (up 1) rfl rfl).trans
      (congrArg (fun q : TK R' ⟶ D.P.A => q.left ≫ β) (_root_.mul_one 1)))
    have h' := hT 0
    rw [map_zero, c0, q0, MonObj.comp_one, MonObj.comp_one] at h'
    rw [← mul_eq_left.1 h]; exact h'
  have h := PrimCocycle.prod_lam (up x) (up y) H
  have h₀ : (∏ I, H ((lift x y).left ≫ β₂ ≫ PrimCocycle.lamφ Q.B I) ^ PrimCocycle.lamε I) = _ :=
    Eq.trans (Finset.prod_congr rfl fun I _ => congrArg (fun q => H q ^ PrimCocycle.lamε I)
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ PrimCocycle.lamφ Q.B I) hl.symm))) h
  rw [h₀, prod_neg _ _ κ H, ← ux, ← uy, ← uxy, ← u1, _root_.mul_comm]
  exact ag1 _ _ _ _

theorem ratio_indep (w : letI := D.P.isAb.comm; LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂))
    (hpb : IsGrpPullback D.P.A Q.B (spMap ρ) β) (hsq : IsSquare β β₂) (hw : w.IsGen)
    (hc : ∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) {κ : (TK R').left ⟶ (TK R).left}
    (hκ : κ ≫ jK R = jK R' ≫ spMap ρ) {a b : D.X} {x y : TK R' ⟶ D.P.A} (hx : x = toUnit (TK R') ≫ D.c a)
    (hy : y = toUnit (TK R') ≫ D.c b) :
    letI := D.P.isAb.comm
    ∀ z J₁ J₁' J₂ J₂', Good Q.M.L z J₁ → Good D.P.L z J₁' → Good Q.M.L z J₂ → Good D.P.L z J₂' →
      (val (D.tau a b) (𝟙 _) z J₁')⁻¹ * lamVal w (lift x y).left z J₁ J₁' * val (Q.tau (e a) (e b)) κ z J₁ =
      (val (D.tau a b) (𝟙 _) z J₂')⁻¹ * lamVal w (lift x y).left z J₂ J₂' * val (Q.tau (e a) (e b)) κ z J₂ := by
  letI := D.P.isAb.comm
  have hxy : toUnit (TK R') ≫ D.c (a + b) = x * y := by
    rw [hx, hy, ← MonObj.comp_mul]; exact congrArg (toUnit (TK R') ≫ ·) (D.c_add a b)
  intro z J₁ J₁' J₂ J₂' h₁ h₁' h₂ h₂'
  rw [GlobalTheory.UU.val_change (DVR.tau_isGen D a b) (𝟙 _) h₁' h₂', lamVal_change w hw _ z h₁ h₂ h₁' h₂',
    GlobalTheory.UU.val_change (Q.tau_gen _ _) κ h₁ h₂]
  refine ag2 _ _ _ _ _ _ _ ?_ ?_
  · refine (congrArg₂ (· * ·) ?_ (PrimCocycle.prod_lam x y
      fun q => gm q z (D.P.L.U (J₁' q) ⊓ D.P.L.U (J₂' q)) (D.P.L.g (J₁' q) (J₂' q)))).trans (ag1 _ _ _ _)
    have e₁ : ptK (D.c (a + b)) = (x * y).left := congrArg (fun q : TK R' ⟶ D.P.A => q.left) hxy
    have e₂ : (toUnit (TK R')).left ≫ eSec D.P.A = (1 : TK R' ⟶ D.P.A).left := rfl
    have e₃ : ptK (D.c a) = x.left := hx ▸ rfl
    have e₄ : ptK (D.c b) = y.left := hy ▸ rfl
    have gen : ∀ (U : Type) [CommGroup U] (H : ((TK R').left ⟶ D.P.A.left) → U),
        (H (ptK (D.c (a + b))))⁻¹ * H (ptK (D.c a)) * H (ptK (D.c b)) * (H ((toUnit (TK R')).left ≫ eSec D.P.A))⁻¹ =
        (H (x * y).left)⁻¹ * H x.left * H y.left * (H (1 : TK R' ⟶ D.P.A).left)⁻¹ := fun U _ H =>
      congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg (fun q => (H q)⁻¹) e₁) (congrArg H e₃))
        (congrArg H e₄)) (congrArg (fun q => (H q)⁻¹) e₂)
    exact (prod_tau D a b fun q => gm q z (D.P.L.U (J₁' q) ⊓ D.P.L.U (J₂' q)) (D.P.L.g (J₁' q) (J₂' q))).trans
      (gen _ fun q => gm q z (D.P.L.U (J₁' q) ⊓ D.P.L.U (J₂' q)) (D.P.L.g (J₁' q) (J₂' q)))
  · exact prod_cancel hpb hsq hc hκ hx hy fun q => gm q z (Q.M.L.U (J₁ q) ⊓ Q.M.L.U (J₂ q)) (Q.M.L.g (J₁ q) (J₂ q))

theorem ratio_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (β : D.P.A.left ⟶ Q.B.left) (β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left) (w : letI := D.P.isAb.comm; LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂)), IsGrpPullback D.P.A Q.B (spMap ρ) β → IsSquare β β₂ → w.IsGen → (∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) → ∀ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ → ∀ a b, ∃ k : (FractionRing R')ˣ, ∀ z J J', Good Q.M.L z J → Good D.P.L z J' → val (D.tau a b) (𝟙 _) z J' * gm (𝟙 (TK R').left) z ⊤ (unitOn k) = (letI := D.P.isAb.comm; lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J') * val (Q.tau (e a) (e b)) κ z J := by
  intro R _ _ R' _ _ Q ρ D e β β₂ w hpb hsq hw hc κ hκ a b
  letI := D.P.isAb.comm
  have indep := ratio_indep w hpb hsq hw hc hκ (a := a) (b := b) rfl rfl
  have hs : Subsingleton (TK R').left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R')))
  let z₀ : (TK R').left := (⊥ : PrimeSpectrum (FractionRing R'))
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.UU.exists_good_pt Q.M.isLB z₀
  obtain ⟨J₀', hJ₀'⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z₀
  obtain ⟨k, hk⟩ := exists_unitOn (FractionRing R') z₀ ((val (D.tau a b) (𝟙 _) z₀ J₀')⁻¹ *
    lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z₀ J₀ J₀' * val (Q.tau (e a) (e b)) κ z₀ J₀)
  refine ⟨k, fun z J J' hJ hJ' => ?_⟩
  obtain rfl : z = z₀ := Subsingleton.elim _ _
  have hk' : gm (𝟙 (TK R').left) z₀ ⊤ (unitOn k) = _ := hk.trans (indep _ _ _ _ _ hJ₀ hJ₀' hJ hJ')
  rw [hk', _root_.mul_assoc, mul_inv_cancel_left]
end GlobalTheory.HalfRatio
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleCover

variable {X : Scheme.{0}} (U : X.Opens) (hU : U = ⊤)

noncomputable def backTop : X ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι (𝟙 X) (by
    rw [Scheme.Opens.range_ι, hU]; exact Set.subset_univ _)

theorem backTop_ι : backTop U hU ≫ U.ι = 𝟙 X := IsOpenImmersion.lift_fac _ _ _

theorem backTop_apply (y : X) : U.ι (backTop U hU y) = y :=
  congrArg (fun g : X ⟶ X => g y) (backTop_ι U hU)

instance : IsIso (backTop U hU) :=
  ⟨⟨U.ι, backTop_ι U hU, by rw [← cancel_mono U.ι, Category.assoc, backTop_ι, Category.comp_id, Category.id_comp]⟩⟩

end GlobalTheory.AmpleCover

namespace GlobalTheory.AmpleCover

variable {S : Scheme.{0}} (A : Over S) (L : LB A.left) (N : ℕ)

theorem gm_pow_congr {y : A.left} {r : A.left ⟶ A.left} (hr : r = 𝟙 A.left) (a b : L.ι) :
    gm (𝟙 A.left) y (L.U a ⊓ L.U b) (L.g a b) ^ N = gm r y (L.U a ⊓ L.U b) (L.g a b) ^ N := by
  subst hr; rfl

def chartPullPowTop :
    ChartPull (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 A.left) fun _ => (N : ℤ)) (powOver A L ⊤ N)
      (backTop (A.hom ⁻¹ᵁ ⊤) (by simp)) where
  idx j := fun _ => (j : Fin 1 → L.ι) 0
  le j y hy := Set.mem_iInter.2 fun _ => by
    have e := backTop_apply (A.hom ⁻¹ᵁ ⊤) (by simp) y
    have hy' : y ∈ L.U ((j : Fin 1 → L.ι) 0) := Set.mem_iInter.1 hy 0
    show (A.hom ⁻¹ᵁ ⊤).ι (backTop (A.hom ⁻¹ᵁ ⊤) (by simp) y) ∈ L.U ((j : Fin 1 → L.ι) 0)
    rw [e]; exact hy'
  g y j j' hj hj' := by
    have hb : ∀ (i : Fin 1 → L.ι), y ∈ L.U (i 0) →
        backTop (A.hom ⁻¹ᵁ ⊤) (by simp) y ∈ (powOver A L ⊤ N).U (fun _ => i 0) := fun i hi =>
      Set.mem_iInter.2 fun _ => by
        have e := backTop_apply (A.hom ⁻¹ᵁ ⊤) (by simp) y
        show (A.hom ⁻¹ᵁ ⊤).ι (backTop (A.hom ⁻¹ᵁ ⊤) (by simp) y) ∈ L.U (i 0)
        rw [e]; exact hi
    refine (gm_linComb L _ _ (𝟙 _) y j j' hj hj').trans (Eq.trans ?_
      (gm_linComb L (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ ⊤).ι) (fun _ => 1) _ y _ _
        (hb j (Set.mem_iInter.1 hj 0)) (hb j' (Set.mem_iInter.1 hj' 0))).symm)
    rw [Fintype.prod_unique]
    simp only [backTop_ι, Category.id_comp, zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      zpow_natCast]
    exact gm_pow_congr A L N (backTop_ι _ _) _ _

end GlobalTheory.AmpleCover


open GlobalTheory.AmpleCover in
theorem GlobalTheory.AmpleCover.exists_affine_cover_secM : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∃ (k : ℕ) (I : Type) (s : I → SecM (𝟙 P₀.A.left) P₀.L k), 1 ≤ k ∧ ⨆ i, Out.nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) ∧ ((Out.nonzeroLocus (s i) : P₀.A.left.Opens) : Set P₀.A.left).Nonempty := by
  intro K _ P₀
  obtain ⟨N, hN, M, s, hcov, hs⟩ := P₀.ample ⊤ (isAffineOpen_top _)
  have hT : P₀.A.hom ⁻¹ᵁ ⊤ = ⊤ := by simp
  let a := chartPullPowTop P₀.A P₀.L N
  have loc : ∀ i, Out.nonzeroLocus (GlobalTheory.chartSec a (s i)) = backTop _ hT ⁻¹ᵁ Out.nonzeroLocus (s i) := fun i =>
    GlobalTheory.nonzeroLocus_chartSec a (s i) fun y j hj => by
      have h0 : (P₀.A.hom ⁻¹ᵁ ⊤).ι (backTop _ hT y) ∈ P₀.L.U ((j : Fin N → P₀.L.ι) ⟨0, hN⟩) :=
        Set.mem_iInter.1 hj ⟨0, hN⟩
      rw [backTop_apply] at h0
      exact ⟨fun _ => (j : Fin N → P₀.L.ι) ⟨0, hN⟩, Set.mem_iInter.2 fun _ => h0⟩
  refine ⟨N, {i : Fin (M + 1) // ((Out.nonzeroLocus (GlobalTheory.chartSec a (s i)) : P₀.A.left.Opens) : Set P₀.A.left).Nonempty},
    fun i => GlobalTheory.chartSec a (s i.1), hN, ?_, fun i => ⟨?_, i.2⟩⟩
  · refine eq_top_iff.2 fun y _ => ?_
    have hy : backTop _ hT y ∈ ⨆ i, Out.nonzeroLocus (s i) := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    have hy' : y ∈ Out.nonzeroLocus (GlobalTheory.chartSec a (s i)) := by rw [loc]; exact hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, y, hy'⟩, hy'⟩
  · show IsAffineOpen (Out.nonzeroLocus (GlobalTheory.chartSec a (s i.1)))
    rw [loc]
    exact (hs i.1).1.preimage _
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecValLC

theorem valR_def' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR x U f = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ h).hom f) := by
  unfold valR; rw [dite_eq_left h]

theorem valR_mul' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f g : Γ(X, U)) :
    valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_def' x U h, map_mul]

theorem valR_map' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valR x V ((X.presheaf.map (homOfLE e).op).hom f) = valR x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := h.trans (x.preimage_mono e)
  rw [valR_def' x V h, valR_def' x U hU]
  have := Scheme.Hom.map_appLE x h (homOfLE e).op
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
    ((X.presheaf.map (homOfLE e).op ≫ x.appLE V ⊤ h).hom f) = _
  rw [this]

theorem valR_id_app {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ ((𝟙 X) ⁻¹ᵁ U)) (f : Γ(X, U)) :
    valR x ((𝟙 X) ⁻¹ᵁ U) ((Scheme.Hom.app (𝟙 X) U).hom f) = valR x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := h
  rw [valR_def' x _ h, valR_def' x U hU]
  congr 1

theorem valR_pow' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) (n : ℕ) :
    valR x U (f ^ n) = valR x U f ^ n := by
  simp only [valR_def' x U h, map_pow]

theorem secM_valR_transition : ∀ (X : Scheme.{0}) (L : LB X) (k : ℕ) (σ : SecM (𝟙 X) L k) (F : Type) [Field F] (ξ : Sp F ⟶ X) (j j' : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j → ⊤ ≤ ξ ⁻¹ᵁ L.U j' → valR ξ _ (σ.f fun _ => j) = valR ξ (L.U j ⊓ L.U j') (L.g j j').val ^ k * valR ξ _ (σ.f fun _ => j') := by
  intro X L k σ F _ ξ j j' hj hj'
  set LC := LB.LinComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => (k:ℤ)) with hLC
  have hW : ∀ i : L.ι, L.U i ≤ LC.U (fun _ => i) :=
    fun i x hx => Set.mem_iInter.2 fun _ => hx
  have h1 : ⊤ ≤ ξ ⁻¹ᵁ (LC.U (fun _ => j) ⊓ LC.U (fun _ => j')) := by
    intro x hx
    exact ⟨hW j (hj hx), hW j' (hj' hx)⟩
  have h2 : ⊤ ≤ ξ ⁻¹ᵁ ((𝟙 X) ⁻¹ᵁ (L.U j ⊓ L.U j')) := fun x hx => ⟨hj hx, hj' hx⟩
  have hle : LC.U (fun _ => j) ⊓ LC.U (fun _ => j') ≤ (𝟙 X) ⁻¹ᵁ (L.U j ⊓ L.U j') :=
    le_inf (inf_le_left.trans (LB.wchart_le L _ _ 0)) (inf_le_right.trans (LB.wchart_le L _ _ 0))
  have hg : ((LC.g (fun _ => j) (fun _ => j') : Γ(X, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))ˣ) :
      Γ(X, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))) =
      (X.presheaf.map (homOfLE hle).op).hom ((Scheme.Hom.app (𝟙 X) (L.U j ⊓ L.U j')).hom
        (L.g j j' : Γ(X, L.U j ⊓ L.U j'))) ^ k := by
    show Units.val (∏ _i : Fin 1, (res _ (pullU (𝟙 X) _ (L.g j j'))) ^ (k:ℤ)) = _
    rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
    rfl
  have hc := σ.compat (fun _ => j) (fun _ => j')
  have := congrArg (valR ξ _) hc
  rw [valR_map' _ _ h1, valR_mul' _ _ h1, valR_map' _ _ h1] at this
  rw [this, hg, valR_pow' _ _ h1, valR_map' _ _ h1, valR_id_app _ _ h2]

end GlobalTheory.SecValLC
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecThroughIso


open ReciprocityTheory.ChartRestriction.G.DVR in
theorem gs_appLE {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) {U : X.Opens} {V : Y.Opens}
    (h : V ≤ g ⁻¹ᵁ U) (hz : f z ∈ V) (x : Γ(X, U)) :
    gs f z V ((g.appLE U V h).hom x) = gs (f ≫ g) z U x := by
  have e : (g.appLE U V h).hom x = (Y.presheaf.map (homOfLE h).op).hom ((g.app U).hom x) := rfl
  rw [e, gs_res f z h hz, gs_pull f g z U (h hz)]

theorem exists_sec_of_genIso : ∀ (Y X₁ X₂ : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)), w.IsGen → L₁.IsLB → L₂.IsLB → ∀ (π : X₁ ⟶ Y), π ≫ f₁ = 𝟙 X₁ → f₁ ≫ π = 𝟙 Y → ∀ (k : ℕ) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))), ∃ σ' : SecM (𝟙 X₁) L₁ k, (∀ (y : Y) (i : L₂.ι) (j : L₁.ι), f₂ y ∈ L₂.U i → f₁ y ∈ L₁.U j → gs (𝟙 Y) y _ (s.f fun _ => i) = (gs (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)).val) ^ k * gs f₁ y _ (σ'.f fun _ => j)) := by
  intro Y X₁ X₂ L₁ L₂ f₁ f₂ w hw h1 h2 π hπ hπ' k s
  let ε : Fin 1 → ℤ := fun _ => (k : ℤ)
  let u := isoInv (ReciprocityTheory.ChartRestriction.G.DVR.flatIso L₁ L₂ f₁ f₂ w ε)
  have hu : u.IsGen := isoInv_isGen (ReciprocityTheory.ChartRestriction.G.DVR.flatIso_isGen L₁ L₂ f₁ f₂ w hw ε)
  let t := ReciprocityTheory.ChartRestriction.G.DVR.secOfIso s hu (LB.isLB_linComb h1 (fun _ : Fin 1 => f₁) ε) (LB.isLB_linComb h2 (fun _ : Fin 1 => f₂) ε)
  refine ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.pullSecLC L₁ (fun _ => f₁) (fun _ => 𝟙 X₁) ε π (fun _ => hπ) t, ?_⟩
  intro y i j hy2 hy1

  have hyA : y ∈ (LB.LinComb L₁ (fun _ : Fin 1 => f₁) ε).U (fun _ => j) := Set.mem_iInter.2 fun _ => hy1
  have hyB : y ∈ (LB.LinComb L₂ (fun _ : Fin 1 => f₂) ε).U (fun _ => i) := Set.mem_iInter.2 fun _ => hy2
  have hyAB : y ∈ (LB.LinComb L₁ (fun _ : Fin 1 => f₁) ε).U (fun _ => j) ⊓ (LB.LinComb L₂ (fun _ : Fin 1 => f₂) ε).U (fun _ => i) := ⟨hyA, hyB⟩
  have hyw : y ∈ (LB.div (L₂.pull f₂) (L₁.pull f₁)).U (fun _ => i, fun _ => j) :=
    ⟨Set.mem_iInter.2 fun _ => hy2, Set.mem_iInter.2 fun _ => hy1⟩

  have s1 : gs f₁ y _ ((ReciprocityTheory.ChartRestriction.G.PullbackSections.pullSecLC L₁ (fun _ => f₁) (fun _ => 𝟙 X₁) ε π (fun _ => hπ) t).f fun _ => j) =
      gs (𝟙 Y) y _ (t.f fun _ => j) := by
    show gs f₁ y _ ((π.appLE _ _ _).hom _) = _
    rw [gs_appLE f₁ π y _ (show f₁ y ∈ _ from Set.mem_iInter.2 fun _ => by simpa using hy1), hπ']

  have s2 : gs (𝟙 Y) y _ (t.f fun _ => j) = gs (𝟙 Y) y _ (ReciprocityTheory.ChartRestriction.G.DVR.isoCand u s (fun _ => j) (fun _ => i)) := by
    rw [← ReciprocityTheory.ChartRestriction.G.DVR.secOfIso_spec s hu _ _ (fun _ => j) (fun _ => i)]
    exact (gs_res (𝟙 Y) y inf_le_left hyAB _).symm

  have s3 : gs (𝟙 Y) y _ (ReciprocityTheory.ChartRestriction.G.DVR.isoCand u s (fun _ => j) (fun _ => i)) =
      ((gm (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j))) ^ (-(k : ℤ))).val * gs (𝟙 Y) y _ (s.f fun _ => i) := by
    unfold ReciprocityTheory.ChartRestriction.G.DVR.isoCand
    rw [gs_mul (𝟙 Y) y _ hyAB, gs_unit (𝟙 Y) y _ hyAB, gs_res (𝟙 Y) y inf_le_right hyAB]
    congr 2
    rw [map_inv, gm_res (𝟙 Y) y _ hyAB]
    show (gm (𝟙 Y) y _ (res _ ((ReciprocityTheory.ChartRestriction.G.DVR.flatIso L₁ L₂ f₁ f₂ w ε).s ((fun _ => j), (fun _ => i))))⁻¹)⁻¹ = _
    have hyBA : y ∈ ((LB.LinComb L₂ (fun _ : Fin 1 => f₂) ε).div (LB.LinComb L₁ (fun _ : Fin 1 => f₁) ε)).U ((fun _ => i), (fun _ => j)) := ⟨hyB, hyA⟩
    have hyAB' : y ∈ ((LB.LinComb L₁ (fun _ : Fin 1 => f₁) ε).div (LB.LinComb L₂ (fun _ : Fin 1 => f₂) ε)).U ((fun _ => j), (fun _ => i)) := hyAB
    rw [map_inv, inv_inv]
    erw [gm_res (𝟙 Y) y _ hyBA]
    show gm (𝟙 Y) y _ (∏ q : Fin 1, res (ReciprocityTheory.ChartRestriction.G.DVR.flat_le L₁ L₂ f₁ f₂ ((fun _ => j), (fun _ => i)) q) (w.s (fun _ => i, fun _ => j)) ^ (-ε q)) = _
    rw [Fin.prod_univ_one]
    erw [map_zpow, gm_res (𝟙 Y) y _ hyAB']
    rfl
  rw [s1, s2, s3, gs_unit (𝟙 Y) y _ hyw, ← _root_.mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, _root_.one_mul]

end GlobalTheory.SecThroughIso
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.isRaynaudFourierTerm_sub_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (k : ℕ) (α : Q.X) (σ σ' : Q.SecB k α) (τ τ' : SecM Y.q.left Q.P.L k) (e : R), IsTerm Y k α σ τ → IsTerm Y k α σ' τ' → IsTerm Y k α (σ' - constFn Q.P.A.hom ⊤ e • σ) (τ' - constFn Y.H.hom ⊤ e • τ) := by
  first | exact @GlobalTheory.HeatTermLin.isTerm_sub_smul | exact GlobalTheory.HeatTermLin.isTerm_sub_smul | (intros; apply GlobalTheory.HeatTermLin.isTerm_sub_smul <;> assumption)
end
