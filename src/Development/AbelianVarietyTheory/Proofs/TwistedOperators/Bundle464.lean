module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle410
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFramesDifferByUnit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1993
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridge
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkLie

open GlobalTheory.IntRebase

section Gen

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {G G' : Over X0} [GrpObj G] [GrpObj G']

theorem smT_post' (a : S) (v : overAt x0 (DualNumber S) ⟶ G) (φ : G ⟶ G') :
    _root_.GlobalTheory.IntRebase.smT x0 a (v ≫ φ) = _root_.GlobalTheory.IntRebase.smT x0 a v ≫ φ := (Category.assoc _ _ _).symm

theorem smT_comm (a b : S) (v : overAt x0 (DualNumber S) ⟶ G) :
    _root_.GlobalTheory.IntRebase.smT x0 a (_root_.GlobalTheory.IntRebase.smT x0 b v) = _root_.GlobalTheory.IntRebase.smT x0 b (_root_.GlobalTheory.IntRebase.smT x0 a v) := by
  rw [_root_.GlobalTheory.IntRebase.smT_smT, _root_.GlobalTheory.IntRebase.smT_smT, _root_.mul_comm]

theorem tan_image (q : S) (v : overAt x0 (DualNumber S) ⟶ G) (h0 : _root_.GlobalTheory.IntRebase.smT x0 0 v = 1) (φ : G ⟶ G') [IsMonHom φ] :
    _root_.GlobalTheory.IntRebase.smT x0 0 (_root_.GlobalTheory.IntRebase.smT x0 q (v ≫ φ)) = 1 := by
  rw [smT_comm, smT_post', h0, MonObj.one_comp, _root_.GlobalTheory.IntRebase.smT_one']

theorem smT_natCast (v : overAt x0 (DualNumber S) ⟶ G) (h0 : _root_.GlobalTheory.IntRebase.smT x0 0 v = 1) (n : ℕ) :
    _root_.GlobalTheory.IntRebase.smT x0 (n : S) v = v ^ n := by
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [Nat.cast_succ, _root_.GlobalTheory.IntRebase.smT_add x0 v h0, ih, _root_.GlobalTheory.IntRebase.smT_unit, pow_succ]

theorem comp_id_pow {P : Over X0} (v : P ⟶ G) (n : ℕ) : v ≫ (𝟙 G ^ n) = v ^ n := by
  have h := map_pow (IntRebase.preHom (G := G) v) (𝟙 G) n
  have h2 : IntRebase.preHom (G := G) v (𝟙 G) = v := Category.comp_id v
  rw [h2] at h
  exact h

variable [IsCommMonObj G] [IsCommMonObj G']

theorem combT_image {m : ℕ} (q : S) (v : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (a : Fin m → S) (φ : G ⟶ G')
    [IsMonHom φ] : _root_.GlobalTheory.IntRebase.smT x0 q (_root_.GlobalTheory.IntRebase.combT x0 v a ≫ φ) = _root_.GlobalTheory.IntRebase.combT x0 (fun j => _root_.GlobalTheory.IntRebase.smT x0 q (v j ≫ φ)) a := by
  let ph : (overAt x0 (DualNumber S) ⟶ G) →* (overAt x0 (DualNumber S) ⟶ G') :=
    { toFun := fun v => v ≫ φ
      map_one' := MonObj.one_comp φ
      map_mul' := fun u w => MonObj.mul_comp u w φ }
  have h : _root_.GlobalTheory.IntRebase.combT x0 v a ≫ φ = ∏ j, _root_.GlobalTheory.IntRebase.smT x0 (a j) (v j) ≫ φ :=
    map_prod ph (fun j => _root_.GlobalTheory.IntRebase.smT x0 (a j) (v j)) Finset.univ
  rw [h, _root_.GlobalTheory.IntRebase.smT_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← smT_post', smT_comm]

theorem mul_eq_one_of_pair {m : ℕ} (p : ℕ) (q : S) (hq : q * p = 1) (U : Fin m → (overAt x0 (DualNumber S) ⟶ G))
    (U' : Fin m → (overAt x0 (DualNumber S) ⟶ G')) (hU' : ∀ j, _root_.GlobalTheory.IntRebase.smT x0 0 (U' j) = 1)
    (huniq : ∀ i (a b : Fin m → S), U' i = _root_.GlobalTheory.IntRebase.combT x0 U' a → U' i = _root_.GlobalTheory.IntRebase.combT x0 U' b → a = b)
    (F : G ⟶ G') (F' : G' ⟶ G) [IsMonHom F] (hF : F' ≫ F = 𝟙 _ ^ (p ^ 2)) (k k' : Matrix (Fin m) (Fin m) S)
    (hk : ∀ i, _root_.GlobalTheory.IntRebase.smT x0 q (U i ≫ F) = _root_.GlobalTheory.IntRebase.combT x0 U' (fun j => k j i))
    (hk' : ∀ i, _root_.GlobalTheory.IntRebase.smT x0 q (U' i ≫ F') = _root_.GlobalTheory.IntRebase.combT x0 U (fun j => k' j i)) : k * k' = 1 := by
  ext j i
  have h1 : _root_.GlobalTheory.IntRebase.smT x0 q (_root_.GlobalTheory.IntRebase.smT x0 q (U' i ≫ F') ≫ F) = U' i := by
    rw [← smT_post', Category.assoc, hF, comp_id_pow, ← smT_natCast x0 _ (hU' i), _root_.GlobalTheory.IntRebase.smT_smT, _root_.GlobalTheory.IntRebase.smT_smT]
    have e : q * q * ((p ^ 2 : ℕ) : S) = 1 := by
      push_cast
      linear_combination (q * p + 1) * hq
    rw [e, _root_.GlobalTheory.IntRebase.smT_unit]
  rw [hk', combT_image, funext hk, _root_.GlobalTheory.IntRebase.combT_combT x0 U' hU'] at h1
  have h2 := congrFun (huniq i _ _ h1.symm (_root_.GlobalTheory.IntRebase.combT_single x0 U' hU' i).symm) j
  rw [Matrix.one_apply, Matrix.mul_apply]
  rw [Pi.single_apply] at h2
  exact h2

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_coords {V Fr : Type} [CommRing V] [Field Fr] [Algebra V Fr] (io : c.F →+* Fr) {G G' : SAB H (Sp V)}
    (τ : E →+* ℂ) (F : G.G ⟶ G'.G) [IsMonHom F] (hF : ∀ a, G.act.act a ≫ F = F ≫ G'.act.act a) (q : V) {m : ℕ}
    (ub' : Fin m → (epsOver V V ⟶ G'.G))
    (hb : ∀ w : epsOver V V ⟶ G'.G, IsTan w → IsEigV c io G' τ w → ∃! a : Fin m → V, IsComb ub' a w)
    (w : epsOver V V ⟶ G.G) (ht : IsTan w) (he : IsEigV c io G τ w) :
    ∃ a : Fin m → V, IsComb ub' a (_root_.GlobalTheory.IntRebase.kapI ≫ _root_.GlobalTheory.IntRebase.smT (𝟙 (Sp V)) q ((IntRebase.kap ≫ w) ≫ F)) := by
  refine (hb _ (_root_.GlobalTheory.IntRebase.isTan_kapI _ (tan_image _ q _ (_root_.GlobalTheory.IntRebase.smT_zero_kap w ht) F)) ?_).exists
  refine (_root_.GlobalTheory.IntRebase.isEigV_kapI_iff io G' τ _).2 fun a z hz => ?_
  have h1 := (_root_.GlobalTheory.IntRebase.isEigV_kapI_iff io G τ (IntRebase.kap ≫ w)).1 (by rw [_root_.GlobalTheory.IntRebase.kapI_kap_assoc]; exact he) a z hz
  rw [← smT_post', Category.assoc (IntRebase.kap ≫ w), ← hF, ← Category.assoc (IntRebase.kap ≫ w), h1, ← smT_post', smT_comm]

theorem lie_lattice_onto : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (I : IntData Xo c T io y.1) (I' : IntData Xo c T io y'.1) (f : Fib Xo (xOf y) ⟶ Fib Xo (xOf y')) (F : I.G.G ⟶ I'.G.G) (F' : I'.G.G ⟶ I.G.G) (p : ℕ) (v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)), IsUnit (p : T.V) → IsMonHom F → IsMonHom F' → Ext I.m1 I.m2 I'.m1 I'.m2 f F → F ≫ F' = 𝟙 _ ^ (p ^ 2) → F' ≫ F = 𝟙 _ ^ (p ^ 2) → (∀ a, I.G.act.act a ≫ F = F ≫ I'.G.act.act a) → (∀ a, I'.G.act.act a ≫ F' = F' ≫ I.G.act.act a) → letI := io.toAlgebra; (∀ τ j, IsLieImageH p f.left (y.1.u τ j) (v τ j)) → ∃ k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, (∀ τ, IsUnit (k τ).det) ∧ ∀ τ i, IsCombAt y'.1.x (y'.1.u τ) (fun j => algebraMap T.V T.Fr (k τ j i)) (v τ i) := by
  intro E _ _ _ H Dw l Xo c T io y y' I I' f F F' p v hp hF hF' hExt _ hFF hl hl'
  let _ := io.toAlgebra
  intro hv
  obtain ⟨q, hq⟩ := hp.exists_left_inv
  choose k hk using fun τ i => exists_coords io τ F hl q (I'.ub τ) (I'.basis τ) (I.ub τ i) (I.tan τ i) (I.eig τ i)
  choose k' hk' using fun τ i => exists_coords io τ F' hl' q (I.ub τ) (I.basis τ) (I'.ub τ i) (I'.tan τ i) (I'.eig τ i)
  refine ⟨fun τ => Matrix.of fun j i => k τ i j, fun τ => ?_, fun τ i => ?_⟩
  · refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun j i => k' τ i j) ?_
    refine mul_eq_one_of_pair (𝟙 (Sp T.V)) p q hq (fun i => IntRebase.kap ≫ I.ub τ i) (fun i => IntRebase.kap ≫ I'.ub τ i)
      (fun i => _root_.GlobalTheory.IntRebase.smT_zero_kap _ (I'.tan τ i)) ?_ F F' hFF _ _ (fun i => (_root_.GlobalTheory.IntRebase.isComb_iff _ _ _).1 (hk τ i))
      (fun i => (_root_.GlobalTheory.IntRebase.isComb_iff _ _ _).1 (hk' τ i))
    intro i a b ha hb
    have ha' := (_root_.GlobalTheory.IntRebase.isComb_iff (I'.ub τ) a _).2 ha
    have hb' := (_root_.GlobalTheory.IntRebase.isComb_iff (I'.ub τ) b _).2 hb
    rw [_root_.GlobalTheory.IntRebase.kapI_kap_assoc] at ha' hb'
    exact (I'.basis τ _ (I'.tan τ i) (I'.eig τ i)).unique ha' hb'
  · obtain ⟨ψ, -, hψ, hg⟩ := hExt
    obtain ⟨u, hu1, hu2⟩ := I.lift τ i
    choose u' hu1' hu2' using I'.lift τ
    obtain ⟨w, hw1, hw2, hw3⟩ := hv τ i
    have hqp : algebraMap T.V T.Fr q = (p : T.Fr)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_natCast (algebraMap T.V T.Fr), ← map_mul, hq, map_one]
    have hov : u ≫ I.t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      apply GlobalTheory.IntLie.spMap_frac_cancel (V := T.V)
      rw [Category.assoc, ← I.m2.cart.1.w, ← Category.assoc, hu2, Category.assoc, Over.w (I.ub τ i)]
      show spMap _ ≫ spMap _ = _
      rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂]
      show spMap ((dualMap (algebraMap T.V T.Fr)).comp (algebraMap T.V (DualNumber T.V))) = _
      rw [GlobalTheory.IntLie.dualMap_alg]
    have h := GlobalTheory.IntLie.comb_generic I'.m1 I'.m2 (I'.ub τ) u' hu2' _
      (spMap (epsMul (algebraMap T.V T.Fr q)) ≫ u ≫ ψ.left) (by
        simp only [Over.comp_left, _root_.GlobalTheory.IntRebase.kapI, IntRebase.kap, _root_.GlobalTheory.IntRebase.smT_left, Over.homMk_left, Category.id_comp, Category.assoc]
        rw [hψ, ← Category.assoc u, hu2, Category.assoc, ← Category.assoc, ← Category.assoc (spMap _) (spMap _),
          GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.dualMap_epsMul]) (k τ i) (hk τ i)
    let g : I.t'.G.left ⟶ pullback Xo.univ.t.G.hom (xOf y) := pullback.lift I.m1.φ I.t'.G.hom I.m1.cart.1.w
    let g' : I'.t'.G.left ⟶ pullback Xo.univ.t.G.hom (xOf y') := pullback.lift I'.m1.φ I'.t'.G.hom I'.m1.cart.1.w
    have hgg := hg g g' (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _)
    have hw : w = u ≫ g := by
      apply pullback.hom_ext
      · rw [hw1, Category.assoc, pullback.lift_fst, hu1]
      · rw [hw2, Category.assoc, pullback.lift_snd, hov]
    have hg' : g' ≫ pullback.fst _ _ = I'.m1.φ := pullback.lift_fst _ _ _
    have hvv : v τ i = (spMap (epsMul (algebraMap T.V T.Fr q)) ≫ u ≫ ψ.left) ≫ I'.m1.φ := by
      rw [hw3, hqp, hw, ← hg', Category.assoc, Category.assoc, Category.assoc, ← Category.assoc ψ.left, ← hgg,
        Category.assoc]
    rw [funext hu1', ← hvv] at h
    exact h

end GlobalTheory.HkLie
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

theorem mem_transKer_of_geometric
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (T : Type) [CommRing T] [IsReduced T] (x x' : Sp T ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (a : Over.mk x ⟶ Xo.univ.t.G)
    (hΨ : Ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (hk : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx x₁ ⟶ Gx x₁'),
      IsFib χ Ψ Ψ₁ → ∃ b ∈ transKer Xo.univ.t.G Ψ₁, b.left = spMap χ ≫ a.left) :
    a ∈ transKer Xo.univ.t.G Ψ := by
  have := Xo.univ.t.semi.smooth
  have := Xo.univ.t.semi.separated
  have : Smooth (fst (Over.mk x) Xo.univ.t.G).left := by
    show Smooth (pullback.fst x Xo.univ.t.G.hom)
    infer_instance
  have : IsSeparated (fst (Over.mk x') Xo.univ.t.G).left := by
    show IsSeparated (pullback.fst x' Xo.univ.t.G.hom)
    infer_instance
  have : IsReduced (Over.mk x).left := (affine_isReduced_iff _).2 ‹IsReduced T›
  have : IsReduced (Gx x) := GlobalTheory.isReduced_of_smooth_of_isReduced (fst (Over.mk x) Xo.univ.t.G).left
  have hT : ∀ {Y : Scheme.{0}} (y : Y ⟶ Xo.X) (c : Over.mk y ⟶ Xo.univ.t.G),
      (translT Xo.univ.t.G c).left ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk y) Xo.univ.t.G).left :=
    fun y c => by rw [← Over.comp_left, translT, lift_fst]
  rw [mem_transKer]
  refine hom_ext_of_geometric_points (Gx x) (Gx x') (Sp T) (fst (Over.mk x') Xo.univ.t.G).left _ _
    (by rw [Category.assoc, hΨ, hT]) fun Ω _ _ q => ?_
  let φ : CommRingCat.of T ⟶ CommRingCat.of Ω := Spec.preimage (q ≫ (fst (Over.mk x) Xo.univ.t.G).left)
  let χ : T →+* Ω := φ.hom
  have hχ : spMap χ = q ≫ (fst (Over.mk x) Xo.univ.t.G).left := Spec.map_preimage _
  obtain ⟨Ψ₁, pm, pm', hp, hp', hc, h1⟩ :=
    exists_isFib χ (x₁ := spMap χ ≫ x) (x₁' := spMap χ ≫ x') rfl rfl Ψ hΨ
  obtain ⟨b, hb, hba⟩ := hk Ω χ _ _ Ψ₁ ⟨pm, pm', hp, hp', hc, h1⟩
  let q₁ : Sp Ω ⟶ Gx (spMap χ ≫ x) := ReciprocityTheory.ChartRestriction.G.PullbackSections.gxLift (spMap χ ≫ x) (𝟙 _)
    (q ≫ (snd (Over.mk x) Xo.univ.t.G).left)
    (by rw [Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.gx_w x, ← Category.assoc, ← hχ, Category.id_comp])
  have hq₁ : q₁ ≫ pm = q := by
    refine ReciprocityTheory.ChartRestriction.G.PullbackSections.gx_ext x _ _ ?_ ?_
    · rw [Category.assoc, hp.2.2, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.gxLift_fst, Category.id_comp, hχ]
    · rw [Category.assoc, hp.2.1, ReciprocityTheory.ChartRestriction.G.PullbackSections.gxLift_snd]
  let pmO : Over.mk (spMap χ ≫ x) ⊗ Xo.univ.t.G ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk pm (by
    rw [← Over.w (fst (Over.mk x) Xo.univ.t.G), ← Over.w (fst (Over.mk (spMap χ ≫ x)) Xo.univ.t.G),
      ← Category.assoc, hp.2.2]
    rfl)
  let φo : Over.mk (spMap χ ≫ x) ⟶ Over.mk x := Over.homMk (spMap χ) rfl
  have hb' : b = φo ≫ a := Over.OverMorphism.ext hba
  have hpf : pmO ≫ fst (Over.mk x) Xo.univ.t.G = fst _ Xo.univ.t.G ≫ φo := Over.OverMorphism.ext hp.2.2
  have hps : pmO ≫ snd (Over.mk x) Xo.univ.t.G = snd _ Xo.univ.t.G := Over.OverMorphism.ext hp.2.1
  have tp : ∀ {Y : Over Xo.X} (c : Y ⟶ Xo.univ.t.G),
      translPt Xo.univ.t.G c = (fst Y Xo.univ.t.G ≫ c) * snd Y Xo.univ.t.G := fun _ => rfl
  have key : translT Xo.univ.t.G b ≫ pmO = pmO ≫ translT Xo.univ.t.G a := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, translT, lift_fst, lift_fst_assoc, hpf]
    · simp only [Category.assoc, translT, lift_snd, lift_snd_assoc, hps, tp, MonObj.comp_mul, reassoc_of% hpf, hb']
  have keyL : (translT Xo.univ.t.G b).left ≫ pm = pm ≫ (translT Xo.univ.t.G a).left :=
    congrArg (fun f => f.left) key
  rw [← hq₁, Category.assoc, Category.assoc, ← reassoc_of% keyL, ← hc, reassoc_of% (mem_transKer.1 hb)]

end GlobalTheory.HeckeEx
end
end

section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx.QFin

section Lemmas

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem mulVec_mul (g h : GL (Fin r) E) (v : Fin r → E) :
    ((g * h : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v =
      (g : Matrix (Fin r) (Fin r) E) *ᵥ ((h : Matrix (Fin r) (Fin r) E) *ᵥ v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem mulVec_inv_mulVec (g : GL (Fin r) E) (v : Fin r → E) :
    ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((g : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := by
  rw [← mulVec_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_mulVec_inv (g : GL (Fin r) E) (v : Fin r → E) :
    (g : Matrix (Fin r) (Fin r) E) *ᵥ (((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := by
  rw [← mulVec_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

variable {X X' : Data E r} {N : ℕ}

theorem qmatch_stab_mul {a g : GL (Fin r) E} (h : QMatch X X' N a) (hg : IsUStab X'.Gm X'.Λ g) :
    QMatch X X' N (g * a) := by
  refine ⟨h.psi, h.p0, h.xi, fun u v => ?_, fun v hv => ?_, fun w hw => ?_⟩
  · rw [mulVec_mul, mulVec_mul, hg.1, h.iso]
  · rw [mulVec_mul, ← Matrix.mulVec_smul]
    exact (hg.2 _).1 (h.lat v hv)
  · rw [mul_inv_rev, mulVec_mul]
    exact h.lat' _ ((hg.2 _).2 (by rw [mulVec_mulVec_inv]; exact hw))

def InL (X' : Data E r) (N : ℕ) (a : GL (Fin r) E) (v : Fin r → E) : Prop :=
  (N : E)⁻¹ • ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) ∈ X'.Λ

theorem inL_transfer (hN : 0 < N) {a a' : GL (Fin r) E} (h' : QMatch X X' N a')
    (hP : ∀ v ∈ X.Λ, InL X' N a' v → InL X' N a v) {w : Fin r → E} (hw : w ∈ X'.Λ) :
    ((a * a'⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w ∈ X'.Λ := by
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have key : ∀ g : GL (Fin r) E, (N : E)⁻¹ • ((g : Matrix (Fin r) (Fin r) E) *ᵥ
      ((N : E) • (((a'⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w))) =
      (g : Matrix (Fin r) (Fin r) E) *ᵥ (((a'⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) := by
    intro g
    rw [Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hN', one_smul]
  have h1 := hP _ (h'.lat' w hw) (by unfold InL; rw [key, mulVec_mulVec_inv]; exact hw)
  unfold InL at h1
  rw [key] at h1
  rw [mulVec_mul]
  exact h1

theorem isUStab_of_inL (hN : 0 < N) {a a' : GL (Fin r) E} (h : QMatch X X' N a) (h' : QMatch X X' N a')
    (hP : ∀ v ∈ X.Λ, InL X' N a v ↔ InL X' N a' v) : IsUStab X'.Gm X'.Λ (a * a'⁻¹) := by
  refine ⟨fun x y => ?_, fun x => ⟨fun hx => inL_transfer hN h' (fun v hv => (hP v hv).2) hx, fun hx => ?_⟩⟩
  · rw [mulVec_mul, mulVec_mul, h.iso, ← h'.iso, mulVec_mulVec_inv, mulVec_mulVec_inv]
  · have := inL_transfer hN h (fun v hv => (hP v hv).1) hx
    rwa [mulVec_mul, mulVec_mul, mulVec_inv_mulVec, mulVec_mulVec_inv] at this

end Lemmas

theorem finite_reps (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ)
    (hN : 0 < N) : ∃ S : Finset (GL (Fin r) E), (∀ s ∈ S, QMatch X X' N s) ∧
      ∀ a, QMatch X X' N a → ∃ s ∈ S, ∃ b ∈ X'.Γ, a = b * s := by
  classical
  have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set A := X.Λ.toAddSubgroup
  have hfg : A.FG := by
    haveI : Module.Finite (𝓞 E) X.Λ := Module.Finite.iff_fg.2 X.Λ_fg
    haveI : Module.Finite ℤ X.Λ := Module.Finite.trans (𝓞 E) X.Λ
    exact (AddGroup.fg_iff_addSubgroup_fg _).1 (Module.Finite.iff_addGroup_fg.1 this)
  haveI : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
  set K := (nsmulAddMonoidHom (α := A) (N * N)).range
  haveI : K.FiniteIndex := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg A (mul_ne_zero hN.ne' hN.ne')
  haveI : Fintype (Set (A ⧸ K)) := Fintype.ofFinite _
  let f : GL (Fin r) E → Set (A ⧸ K) := fun a =>
    (QuotientAddGroup.mk : A → A ⧸ K) '' {v | InL X' N a (v : Fin r → E)}
  have hf : ∀ a, QMatch X X' N a → ∀ v : A,
      (QuotientAddGroup.mk v : A ⧸ K) ∈ f a ↔ InL X' N a (v : Fin r → E) := by
    intro a ha v
    constructor
    · rintro ⟨v', hv', he⟩
      obtain ⟨u, hu⟩ := QuotientAddGroup.eq.1 he
      have hv : (v : Fin r → E) = (v' : Fin r → E) + ((N : E) * N) • (u : Fin r → E) := by
        have := congrArg (fun z : A => (z : Fin r → E)) hu
        simp only [nsmulAddMonoidHom_apply, AddSubgroup.coe_add, AddSubgroup.coe_neg,
          AddSubgroup.coe_nsmul] at this
        rw [← Nat.cast_mul, Nat.cast_smul_eq_nsmul, this]
        abel
      show InL X' N a (v : Fin r → E)
      have hv'' : InL X' N a (v' : Fin r → E) := hv'
      unfold InL at hv'' ⊢
      rw [hv, Matrix.mulVec_add, Matrix.mulVec_smul, smul_add, smul_smul, ← _root_.mul_assoc,
        inv_mul_cancel₀ hN0, _root_.one_mul]
      exact X'.Λ.add_mem hv'' (ha.lat _ u.2)
    · intro h
      exact ⟨v, h, rfl⟩
  let rep : Set (A ⧸ K) → GL (Fin r) E := fun T =>
    if h : ∃ a, QMatch X X' N a ∧ f a = T then h.choose else 1
  obtain ⟨S0, hS0⟩ := X'.Γ_index
  refine ⟨((Finset.univ ×ˢ S0).image fun p => p.2⁻¹ * rep p.1).filter (QMatch X X' N),
    fun s hs => (Finset.mem_filter.1 hs).2, fun a ha => ?_⟩
  have hex : ∃ a', QMatch X X' N a' ∧ f a' = f a := ⟨a, ha, rfl⟩
  have hrep : rep (f a) = hex.choose := dif_pos hex
  obtain ⟨ha', hfa⟩ := hex.choose_spec
  have hP : ∀ v ∈ X.Λ, InL X' N hex.choose v ↔ InL X' N a v := by
    intro v hv
    rw [← hf _ ha' ⟨v, hv⟩, ← hf a ha ⟨v, hv⟩, hfa]
  obtain ⟨s, hs, hsΓ⟩ := hS0 _ (isUStab_of_inL hN ha' ha hP)
  have hq := qmatch_stab_mul ha (X'.Γ_stab _ hsΓ)
  have e : s⁻¹ * (hex.choose * a⁻¹) * a = s⁻¹ * hex.choose := by group
  rw [e] at hq
  refine ⟨s⁻¹ * hex.choose, Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(f a, s),
    Finset.mem_product.2 ⟨Finset.mem_univ _, hs⟩, ?_⟩, hq⟩, (s⁻¹ * (hex.choose * a⁻¹))⁻¹,
    X'.Γ.inv_mem hsΓ, by group⟩
  show s⁻¹ * rep (f a) = s⁻¹ * hex.choose
  rw [hrep]

end GlobalTheory.HeckeEx.QFin
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

theorem translT_comp_isCan : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x} (c : Over.mk x ⟶ Xo.univ.t.G) (c₁ : Over.mk x₁ ⟶ Xo.univ.t.G), IsCan χ pm → c₁.left = spMap χ ≫ c.left → (translT Xo.univ.t.G c₁).left ≫ pm = pm ≫ (translT Xo.univ.t.G c).left := by
  intro E _ _ _ H Dw l Xo T Ω _ _ χ x x₁ pm c c₁ h hc
  have hw : pm ≫ (Over.mk x ⊗ Xo.univ.t.G).hom = (Over.mk x₁ ⊗ Xo.univ.t.G).hom := by
    rw [← Over.w (snd (Over.mk x) Xo.univ.t.G), ← Over.w (snd (Over.mk x₁) Xo.univ.t.G), ← Category.assoc, h.2.1]
  let P : Over.mk x₁ ⊗ Xo.univ.t.G ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk pm hw
  let Φ : Over.mk x₁ ⟶ Over.mk x := Over.homMk (spMap χ) h.1.symm
  have hPf : P ≫ fst (Over.mk x) Xo.univ.t.G = fst (Over.mk x₁) Xo.univ.t.G ≫ Φ :=
    Over.OverMorphism.ext (by simpa [P, Φ] using h.2.2)
  have hPs : P ≫ snd (Over.mk x) Xo.univ.t.G = snd (Over.mk x₁) Xo.univ.t.G :=
    Over.OverMorphism.ext (by simpa [P] using h.2.1)
  have hΦ : Φ ≫ c = c₁ := Over.OverMorphism.ext (by simpa [Φ] using hc.symm)
  have key : translT Xo.univ.t.G c₁ ≫ P = P ≫ translT Xo.univ.t.G c := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, hPf, translT, translT, lift_fst, lift_fst_assoc]
      exact hPf.symm
    · rw [Category.assoc, Category.assoc, hPs, translT, translT, lift_snd, lift_snd, translPt, translPt,
        comp_lift_assoc, reassoc_of% hPf, hPs, hΦ]
  have := congrArg CommaMorphism.left key
  simpa [P] using this

end GlobalTheory.HeckeEx
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.SmallDatLat

theorem latPtS_le_closure_and_selfDual : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j),
    Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram → Γ.W.J = _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e → ∀ v : Pl D.host.F,
      GlobalTheory.SmallDat.latPtS t e v ≤ AddSubgroup.closure (GlobalTheory.SmallDat.genPtS t e v) ∧
      ∀ z : GlobalTheory.SmallDat.PtS G i j, At (evFin D.host.F v) z → (z ∈ GlobalTheory.SmallDat.latPtS t e v ↔ ∀ γ ∈ GlobalTheory.SmallDat.latPtS t e v, W.ψ (GlobalTheory.SmallDat.sympS Γ z γ) = 1) := by
  intro D T L sc G μ₀ hL W t i j e Γ hW₁ hWW v
  have s0 := (node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).sd
  have s1 := (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have s2 := (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  refine ⟨GlobalTheory.BigDatLat.le_of_gen (GlobalTheory.SmallDat.maps t e) v _ (fun _ => Iff.rfl) _
    (fun u hu => AddSubgroup.subset_closure (Or.inl ⟨u, hu, rfl⟩))
    fun ε hε u hu h1 h2 => AddSubgroup.subset_closure (Or.inr ⟨hu, ε, hε, h1, h2⟩), fun z hz => ?_⟩
  exact GlobalTheory.BigDatLat.mem_iff_char (GlobalTheory.SmallDat.maps t e) v _ s0 s1 (isSelfDualC_neg s2) s0 (fun _ => Iff.rfl) W.ψ_std
    (GlobalTheory.SmallDat.sympS Γ) (GlobalTheory.SmallDat.sympS_eq t e Γ hW₁ hWW) hz

end GlobalTheory.SmallDatLat

end
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_equiv_piExteriorTensor_blockLevi : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (τ : GlobalTheory.SmGL.IrrRep (GlobalTheory.SmGL.Levi k c)), ∃ s : ∀ j, GlobalTheory.SmGL.IrrRep (GL (c j) k), Nonempty (τ.ρ.Equiv (GlobalTheory.SmGL.piTensor fun j => (s j).ρ)) := by
  first | exact @GlobalTheory.LeviFactor.exists_equiv_piTensor_levi | exact GlobalTheory.LeviFactor.exists_equiv_piTensor_levi | (intros; apply GlobalTheory.LeviFactor.exists_equiv_piTensor_levi <;> assumption)
end
