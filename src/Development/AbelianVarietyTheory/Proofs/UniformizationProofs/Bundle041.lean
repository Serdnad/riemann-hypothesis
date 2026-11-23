module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Sites.Fpqc
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifLinear

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem one_pG {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} :
    (1 : T ⟶ thickObj R I e G).left ≫ g.pG.left = T.hom ≫ thick R I e ≫ eSec D.P.A :=
  (congrArg CommaMorphism.left (TorusCoord.im_one g (T := T))).trans (Category.assoc _ _ _)

theorem comp_q_eq_iff {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (y : T ⟶ thickObj R I e G) :
    y ≫ g.q = toUnit T ≫ η[thickObj R I e D.P.A] ↔
      y.left ≫ g.pG.left = T.hom ≫ thick R I e ≫ eSec D.P.A := by
  have := g.q_hom
  have h1 : (1 : T ⟶ thickObj R I e G) ≫ g.q = toUnit T ≫ η[thickObj R I e D.P.A] :=
    MonObj.one_comp _
  rw [← h1, ← one_pG g]
  refine ⟨fun h => congrArg CommaMorphism.left (TorusCoord.im_congr g h), fun h => ?_⟩
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)

omit [IsDomain R] [GrpObj G] [IsCommMonObj G] in
theorem comp_fstG_hom {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (y : T ⟶ thickObj R I e G) {W : Scheme.{0}} (s : Spec (CommRingCat.of R) ⟶ W) :
    y.left ≫ (fstG I e G).left ≫ G.hom ≫ s = T.hom ≫ thick R I e ≫ s := by
  rw [← Over.w y, Category.assoc]
  exact congrArg (y.left ≫ ·) (pullback.condition_assoc s)

theorem map_pG (a : G ⟶ G) (b : D.P.A ⟶ D.P.A)
    (h : (Over.pullback (thick R I e)).map a ≫ g.q = g.q ≫ (Over.pullback (thick R I e)).map b) :
    ((Over.pullback (thick R I e)).map a).left ≫ g.pG.left = g.pG.left ≫ b.left := by
  have A : ((Over.pullback (thick R I e)).map b).left ≫ pullback.fst D.P.A.hom (thick R I e) =
      pullback.fst D.P.A.hom (thick R I e) ≫ b.left := pullback.lift_fst _ _ _
  have h' := congrArg (fun f => f.left ≫ pullback.fst D.P.A.hom (thick R I e)) h
  simp only [Over.comp_left, Category.assoc, A] at h'
  exact h'.trans (Category.assoc _ _ _).symm

theorem appTop_of_torusEndOf {S : Scheme.{0}} {X : Type} [AddCommGroup X] {h : X → X}
    {t : splitTorus S X ⟶ splitTorus S X} (ht : TorusEndOf X h t) (χ : X) :
    t.left.appTop.hom (charUnit S X χ).val = (charUnit S X (h χ)).val := by
  rw [SplitTorus.charUnit_val]
  exact (SplitTorus.res_pullU_charUnit t χ _).symm.trans (congrArg Units.val (ht χ))

theorem identification_linear : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (Φ : D'.toPre.P.A ≅ D.toPre.P.A), (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U'.gt e).t x) r z J') → ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (ιD : D.toPre.OAct O) (ιD' : D'.toPre.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O) (ιG : RingAct G O), U.OLinear O ιD ιA ιG → U'.OLinear O ιD' ιA' ιG → (∀ (a : O) (y : D'.toPre.X), xe (a • y) = a • xe y) ∧ ∀ a, ιD'.onB.act a ≫ Φ.hom = Φ.hom ≫ ιD.onB.act a := by
  intro R _ _ _ I hR D D' A A' G _ _ _ U U' Φ hΦ xe hval O _ _ _ _ ιD ιD' ιA ιA' ιG hl hl'
  obtain ⟨hN, -, -, hc⟩ := hR
  have hI : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  refine ⟨?_, fun a => ?_⟩
  · have hI' : I ^ (0 + 1) ≠ ⊤ := fun h => by
      rw [zero_add, pow_one] at h
      rw [h, top_le_iff, Ideal.jacobson_eq_top_iff] at hI
      exact bot_ne_top hI
    have : Nontrivial (R ⧸ I ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 hI'
    have : Nonempty (Spec (CommRingCat.of (R ⧸ I ^ (0 + 1)))) :=
      inferInstanceAs (Nonempty (PrimeSpectrum (R ⧸ I ^ (0 + 1))))
    have k' := (comp_q_eq_iff (U'.gt 0) _).1 (U'.gt 0).isKernel.w
    have k : (U'.gt 0).i.left ≫ (U.gt 0).pG.left =
        (splitTorus _ D'.toPre.X).hom ≫ thick R I 0 ≫ eSec D.toPre.P.A := by
      refine Eq.trans ?_ (one_pG (U.gt 0))
      rw [← hΦ]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Φ.hom.left)
        (k'.trans (one_pG (U'.gt 0)).symm)).trans (Category.assoc _ _ _))
    obtain ⟨τ, hτ⟩ : ∃ τ, τ ≫ (U.gt 0).i = (U'.gt 0).i :=
      ⟨_, (U.gt 0).isKernel.lift_fst _ _ ((comp_q_eq_iff (U.gt 0) _).2 k)⟩
    have hchar : ∀ x, τ.left.appTop.hom (charUnit _ D.toPre.X (xe x)).val =
        (charUnit _ D'.toPre.X x).val := fun x => by
      apply TopCat.Presheaf.section_ext (Scheme.sheaf _) ⊤
      intro z hz
      obtain ⟨J, hJ⟩ := TLinPf.idx_exists D.toPre.P.L D.toPre.P.isLB z
      obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D'.toPre.P.L D'.toPre.P.isLB z
      have v := hval 0 _ (U'.gt 0).i.left z J J' hJ hJ' (k.trans (comp_fstG_hom _ _).symm)
        (k'.trans (comp_fstG_hom _ _).symm) x
      have v₁ := (TorusCoord.val_torus_point_and_translate R I D.toPre 0 G (U.gt 0) _ τ 1 z J hJ
        (xe x)).1
      have v₂ := (TorusCoord.val_torus_point_and_translate R I D'.toPre 0 G (U'.gt 0) _ (𝟙 _) 1 z J'
        hJ' x).1
      rw [hτ] at v₁
      rw [Category.id_comp] at v₂
      have w := congrArg Units.val (v₁.symm.trans (v.trans v₂))
      rw [Geo.Tor.gm_val _ z ⊤ trivial, Geo.Tor.gm_val _ z ⊤ trivial] at w
      exact w
    intro a y
    obtain ⟨t, ht, hi⟩ := hl.i_lin 0 (star a)
    obtain ⟨t', ht', hi'⟩ := hl'.i_lin 0 (star a)
    have : Mono (U.gt 0).i :=
      (MorphismProperty.monomorphisms _).of_isPullback (U.gt 0).isKernel.flip
        (inferInstanceAs (Mono η[thickObj R I 0 D.toPre.P.A]))
    have ht₀ : t' ≫ τ = τ ≫ t := by
      rw [← cancel_mono (U.gt 0).i, Category.assoc, Category.assoc, ← hi, hτ, ← hi',
        ← Category.assoc, hτ]
    have h := congrArg (fun f => f.left.appTop.hom (charUnit _ D.toPre.X (xe y)).val) ht₀
    simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h
    rw [hchar, appTop_of_torusEndOf ht, appTop_of_torusEndOf ht', star_star,
      ← xe.apply_symm_apply (a • xe y), hchar, SplitTorus.charUnit_val,
      SplitTorus.charUnit_val] at h
    rw [SplitTorus.chi_injective h, xe.apply_symm_apply]
  · have := D'.toPre.P.isAb.smooth
    have := D'.toPre.P.isAb.geomConnected
    have := D.toPre.P.isAb.proper
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I hI D'.toPre.P.A).2 D.toPre.P.A _ _ fun n => ?_
    have := (U'.gt n).q_flat
    have := (U'.gt n).q_surj
    have := (U'.gt n).q_affine
    have e₁ := map_pG (U.gt n) _ _ (hl.q_lin n a)
    have e₂ := map_pG (U'.gt n) _ _ (hl'.q_lin n a)
    have hE : Epi (U'.gt n).q.left := inferInstance
    refine (cancel_epi (U'.gt n).q.left).1 ?_
    refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.assoc _ _ _))
    change (U'.gt n).pG.left ≫ _ = (U'.gt n).pG.left ≫ _
    have e₃ := hΦ n
    generalize (U'.gt n).pG.left = p', (U.gt n).pG.left = p at e₁ e₂ e₃ ⊢
    rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← Category.assoc, e₃, ← e₁, ← e₃, ← e₂]
    exact Category.assoc _ _ _

end GlobalTheory.UnifLinear
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory


open CoordCompare TorusCoord in
theorem gtCoord_end_ratio_descends : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a : thickObj R I e G ⟶ thickObj R I e G) (aB : D.P.A ⟶ D.P.A) (h : D.X → D.X) (t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ splitTorus _ D.X), IsMonHom a → TorusEndOf D.X h t → g.i ≫ a = t ≫ g.i → a ≫ g.q = g.q ≫ (Over.pullback (thick R I e)).map aB → ∀ χ : D.X, ∃ u : LB.Gen (LB.LinComb D.P.L (Y := (thickObj R I e D.P.A).left) (fun k => pullback.fst D.P.A.hom (thick R I e) ≫ Sum.elim (D.Oφ (𝟙 _) (h χ)) (D.Oφ aB χ) k) (Sum.elim Oε Oinvε)), u.IsGen ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.P.L z J → val (g.t χ) (x ≫ a.left) z J = val (g.t (h χ)) x z J * val u (x ≫ g.q.left) z J := by
  intro R _ _ I D e G _ _ g a aB h t ha ht hi hq χ
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hp : (Over.map (thick R I e)).map a ≫ g.pG = g.pG ≫ aB := by
    refine Over.OverMorphism.ext ?_
    have h1 : a.left ≫ g.q.left = g.q.left ≫ ((Over.pullback (thick R I e)).map aB).left :=
      congrArg (fun q => q.left) hq
    have h2 : ((Over.pullback (thick R I e)).map aB).left ≫ pullback.fst D.P.A.hom (thick R I e) =
        pullback.fst D.P.A.hom (thick R I e) ≫ aB.left := pullback.lift_fst _ _ _
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)))
  have e₁ : ∀ k, a.left ≫ D.Oφ g.pG χ k =
      g.q.left ≫ pullback.fst D.P.A.hom (thick R I e) ≫ D.Oφ aB χ k := fun k =>
    (WeightPf.Oφ_comp ((Over.map (thick R I e)).map a) g.pG χ k).trans
      ((congrArg (D.Oφ · χ k) hp).trans
        ((WeightPf.Oφ_comp g.pG aB χ k).symm.trans (Category.assoc _ _ _)))
  have e₂ : ∀ k, D.Oφ g.pG (h χ) k =
      g.q.left ≫ pullback.fst D.P.A.hom (thick R I e) ≫ D.Oφ (𝟙 _) (h χ) k := fun k =>
    (congrArg (D.Oφ · (h χ) k) (Category.comp_id g.pG).symm).trans
      ((WeightPf.Oφ_comp g.pG (𝟙 _) (h χ) k).symm.trans (Category.assoc _ _ _))
  obtain ⟨u, hu, hu'⟩ := exists_gen D.P.isLB
    (φ' := fun k => g.q.left ≫ pullback.fst D.P.A.hom (thick R I e) ≫
      Sum.elim (D.Oφ (𝟙 _) (h χ)) (D.Oφ aB χ) k) (ε' := Sum.elim Oε Oinvε)
    (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
      refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) (Finset.prod_congr rfl fun k _ => ?_)
      · exact congrArg₂ (· ^ ·) (congrArg f (e₂ k)) (show -Oinvε k = Oε k by fin_cases k <;> rfl)
      · exact congrArg (fun ψ => f ψ ^ Oinvε k) (e₁ k))
    (LB.mulGen D.P.L _ _ _ _ (LB.invGen D.P.L _ _ (g.t (h χ))) (LB.pullGen D.P.L _ _ (g.t χ) a.left))
    (mulGen_isGen _ _ _ _ _ _ _ (invGen_isGen _ _ _ _ (g.t_gen _)) (pullGen_isGen _ _ _ _ (g.t_gen χ) _))
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.P.L z J →
      val u r z J = (val (g.t (h χ)) r z J)⁻¹ * val (g.t χ) (r ≫ a.left) z J := fun Z r z J hJ =>
    (hu' Z r z J hJ).trans ((Geo.Tor.val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (Geo.Tor.val_inv _ _) (Geo.Tor.val_pull hJ _ _ _)))
  obtain ⟨v, hv₁, hv₂⟩ := exists_gen_of_val_eq D.P.isLB _ _ g.q.left u hu (fun Z r r' z J hJ hr => by
    rw [hv Z r z J hJ, hv Z r' z J hJ]
    have hw : r ≫ (thickObj R I e G).hom = r' ≫ (thickObj R I e G).hom := by
      rw [← Over.w g.q, reassoc_of% hr]
    let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (r' ≫ (thickObj R I e G).hom)
    let b : Z' ⟶ thickObj R I e G := Over.homMk r hw
    let b' : Z' ⟶ thickObj R I e G := Over.homMk r' rfl
    obtain ⟨τ, hτ⟩ := exists_torus g b b' (Over.OverMorphism.ext hr)
    have hτa : b ≫ a = ((τ ≫ t) ≫ g.i) * (b' ≫ a) := by
      rw [hτ, MonObj.mul_comp, Category.assoc, hi, Category.assoc]
    have v₁ := val_torus g (h χ) (Z := Z') hJ τ b'
    have v₂ := val_torus g χ (Z := Z') hJ (τ ≫ t) (b' ≫ a)
    rw [← hτ] at v₁
    rw [← hτa] at v₂
    have v₀ : gm (τ ≫ t).left z ⊤ (charUnit _ D.X χ) = gm τ.left z ⊤ (charUnit _ D.X (h χ)) :=
      (gm_pull τ.left t.left z ⊤ trivial _).symm.trans
        ((gm_res τ.left z (V := ⊤) (U := t.left ⁻¹ᵁ ⊤) (fun _ _ => trivial) trivial _).symm.trans (congrArg _ (ht χ)))
    refine (congrArg₂ (fun s s' => s⁻¹ * s') v₁ v₂).trans ?_
    rw [v₀, mul_inv, _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul]
    rfl)
  refine ⟨v, hv₁, fun Z x z J hJ => ?_⟩
  rw [hv₂ Z x z J hJ, hv Z x z J hJ, mul_inv_cancel_left]

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ArcPsiOn

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull

theorem genRel_iff_val {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} (hM : M.IsLB) (hM₀ : M₀.IsLB)
    {φ : B ⟶ B₀} (w : LB.Iso M (M₀.pull φ)) {pt : PUnit → (Sp F ⟶ B)} {pt₀ : PUnit → (Sp F ⟶ B₀)} {ε : PUnit → ℤ}
    (t : LB.Gen (LB.LinComb M pt ε)) (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)) (x : F) (z : Sp F) :
    GenRel w t t₀ x ↔ pt PUnit.unit ≫ φ = pt₀ PUnit.unit ∧ ∀ J₀ J, Good M₀ z J₀ → Good M z J →
      (om w z J₀ J (pt PUnit.unit) ^ ε PUnit.unit * val t (𝟙 _) z J).val = toStk z x * (val t₀ (𝟙 _) z J₀).val := by
  rw [genRel_iff w t t₀ x z]
  constructor
  · rintro ⟨hp, H⟩
    refine ⟨hp _, fun J₀ J hJ₀ hJ => ?_⟩
    have e := H (fun k => J (pt k)) (fun k => J₀ (pt k ≫ φ)) (fun k => hJ₀ (pt k ≫ φ)) (fun k => hJ (pt k))
    rw [Fintype.prod_unique] at e
    rw [val_of t _ z J (fun k => J (pt k)) (fun k => by rw [Category.id_comp]),
      val_of t₀ _ z J₀ (fun k => J₀ (pt k ≫ φ)) (fun k => by rw [Category.id_comp, hp])]
    exact e
  · rintro ⟨hp, H⟩
    refine ⟨fun _ => hp, fun j j₀ h₀ h₁ => ?_⟩
    obtain ⟨J, hJ, eJ⟩ := exists_good M hM z pt j (fun _ _ _ => rfl) h₁
    obtain ⟨J₀, hJ₀, eJ₀⟩ := exists_good M₀ hM₀ z (fun k => pt k ≫ φ) j₀ (fun _ _ _ => rfl) h₀
    have e := H J₀ J hJ₀ hJ
    rw [val_of t _ z J j (fun k => by rw [Category.id_comp]; exact eJ k),
      val_of t₀ _ z J₀ j₀ (fun k => by rw [Category.id_comp, ← eJ₀ k]; exact congrArg J₀ hp.symm), om, eJ,
      eJ₀ PUnit.unit] at e
    rw [Fintype.prod_unique]
    exact e

theorem exists_unit_basicOpen {R : Type} [CommRing R] (u : R) :
    ∃ c : Γ((TW (R := R) (PrimeSpectrum.basicOpen u)).left, ⊤)ˣ, ∀ (F : Type) [Field F] (r : R →+* F)
      (z : Sp F ⟶ (TW (R := R) (PrimeSpectrum.basicOpen u)).left),
      z ≫ (TW (R := R) (PrimeSpectrum.basicOpen u)).hom = specOf r → ∀ (p : Sp F) (n : ℤ),
      (gm z p ⊤ (c ^ n)).val = toStk p (r u ^ n) := by
  let U : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen u
  let s : Γ(Spec (CommRingCat.of R), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom u
  have hc : IsUnit ((U.ι.app ⊤).hom s) := by
    apply U.toScheme.toRingedSpace.isUnit_of_isUnit_germ
    intro y hy
    have : y ∈ U.toScheme.basicOpen ((U.ι.app ⊤).hom s) := by
      rw [← Scheme.preimage_basicOpen]
      show U.ι y ∈ (Spec (CommRingCat.of R)).basicOpen s
      rw [basicOpen_eq_of_affine]
      exact y.2
    exact (Scheme.mem_basicOpen _ _ y hy).1 this
  refine ⟨hc.unit, fun F _ r z hz p n => ?_⟩
  have e : (gm z p ⊤ hc.unit).val = toStk p (r u) := by
    have e₁ : (gm z p ⊤ hc.unit).val = gs (z ≫ U.ι) p ⊤ s :=
      (gs_unit z p ⊤ trivial hc.unit).symm.trans (gs_pull z U.ι p ⊤ trivial s)
    have hz' : z ≫ U.ι = specOf r := hz
    rw [e₁, hz', gs_eq _ p ⊤ trivial]
    have nat := congrArg (fun q => q.hom u) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom r))
    exact congrArg ((Sp F).presheaf.germ ⊤ p trivial).hom nat.symm
  have h0 : r u ≠ 0 := fun h => by
    rw [h, map_zero] at e
    exact (gm z p ⊤ hc.unit).ne_zero e
  have e' : Units.map (toStk p).toMonoidHom (Units.mk0 _ h0) = gm z p ⊤ hc.unit := Units.ext e.symm
  refine (congrArg Units.val ((map_zpow (gm z p ⊤) hc.unit n).trans ((congrArg (· ^ n) e'.symm).trans
    (map_zpow _ _ n).symm))).trans ?_
  show toStk p _ = _
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]

theorem val_scale' {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (scaleGen c t) r z J = gm r z ⊤ c * val t r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ (hJ.mem φ r) _) rfl)

variable {O' R : Type} [CommRing O'] [IsDomain O'] [CommRing R] [IsDomain R] {D₀ : DegPre O'} {D : DegPre R}

theorem exists_gen_on (f : O' →+* R) (u : R) {φ : D.P.A.left ⟶ D₀.P.A.left} (w : LB.Iso D.P.L (D₀.P.L.pull φ))
    (hw : w.IsGen) (y : D₀.X) (x : D.X) (hc : (D.c x).left ≫ φ = spMap f ≫ (D₀.c y).left)
    (hy : PsiUnitOn D₀ y Set.univ) (n : ℤ) :
    ∃ s : LB.Gen (LB.LinComb D.P.L (K := PUnit)
        (fun _ => (toUnit (TW (R := R) (PrimeSpectrum.basicOpen u)) ≫ D.c x).left) (fun _ => -1)), s.IsGen ∧
      ∀ (F : Type) [Field F] (r : R →+* F) (z : Sp F ⟶ (TW (R := R) (PrimeSpectrum.basicOpen u)).left),
        z ≫ (TW (R := R) (PrimeSpectrum.basicOpen u)).hom = specOf r → ∀ j : Sp F ⟶ (TK O').left,
        j ≫ jK O' = specOf r ≫ spMap f →
        GenRel w (LB.pullGen _ _ _ s z) (LB.pullGen _ _ _ (D₀.psi y) j) (r u ^ n) := by
  obtain ⟨t, ht, H⟩ := (psiUnitOn_univ_iff D₀ y).1 hy
  obtain ⟨c, hcu⟩ := exists_unit_basicOpen u
  have hψ : (toUnit (TW (R := R) (PrimeSpectrum.basicOpen u)) ≫ D.c x).left ≫ φ =
      ((TW (R := R) (PrimeSpectrum.basicOpen u)).hom ≫ spMap f) ≫ (D₀.c y).left := by
    show ((TW (R := R) (PrimeSpectrum.basicOpen u)).hom ≫ (D.c x).left) ≫ φ = _
    rw [Category.assoc, hc, Category.assoc]
  obtain ⟨a, ha, va⟩ := exists_down_om hw D₀.P.isLB D.P.isLB (K := PUnit)
    (φ' := fun _ => (toUnit (TW (R := R) (PrimeSpectrum.basicOpen u)) ≫ D.c x).left)
    ((TW (R := R) (PrimeSpectrum.basicOpen u)).hom ≫ spMap f) (fun _ => hψ) t ht
  refine ⟨scaleGen (c ^ n) a, scaleGen_isGen _ _ ha, fun F _ r z hz j hj => ?_⟩
  have p : Sp F := (default : PrimeSpectrum F)
  have hzj : z ≫ (TW (R := R) (PrimeSpectrum.basicOpen u)).hom ≫ spMap f = j ≫ jK O' := by
    rw [← Category.assoc, hz, hj]
  refine (genRel_iff_val D.P.isLB D₀.P.isLB w _ _ _ p).2 ⟨?_, fun J₀ J hJ₀ hJ => ?_⟩
  · show (z ≫ (toUnit (TW (R := R) (PrimeSpectrum.basicOpen u)) ≫ D.c x).left) ≫ φ = j ≫ jK O' ≫ (D₀.c y).left
    rw [Category.assoc, hψ, ← Category.assoc, hzj, Category.assoc]
  · have e := va _ z p J₀ J hJ₀ hJ
    rw [Fintype.prod_unique, hzj, ← val_pull hJ₀, val_corr hJ₀ H] at e
    rw [val_pull hJ, val_pull hJ₀, Category.id_comp, Category.id_comp, val_scale' _ _ _ hJ, e, ← hcu F r z hz p n,
      ← Units.val_mul, mul_left_comm]

theorem val_eq_of_genRel {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} (hM : M.IsLB) (hM₀ : M₀.IsLB)
    {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} {pt pt' : PUnit → (Sp F ⟶ B)} {pt₀ : PUnit → (Sp F ⟶ B₀)} {ε : PUnit → ℤ}
    {t : LB.Gen (LB.LinComb M pt ε)} {t' : LB.Gen (LB.LinComb M pt' ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} {x : F}
    (hp : pt PUnit.unit = pt' PUnit.unit) (h : GenRel w t t₀ x) (h' : GenRel w t' t₀ x) (z : Sp F) {J} (hJ : Good M z J) :
    val t (𝟙 _) z J = val t' (𝟙 _) z J := by
  obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' hM₀ z
  have e := ((genRel_iff_val hM hM₀ w _ _ _ z).1 h).2 J₀ J hJ₀ hJ
  have e' := ((genRel_iff_val hM hM₀ w _ _ _ z).1 h').2 J₀ J hJ₀ hJ
  rw [hp, ← e'] at e
  exact mul_left_cancel (Units.ext e)

theorem corr_of_geom (U : (Spec (CommRingCat.of R)).Opens) (hU : (U : Set (Spec (CommRingCat.of R))).Nonempty)
    (x : D.X) (s : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (toUnit (TW U) ≫ D.c x).left) (fun _ => -1)))
    (F : Type) [Field F] [Algebra (FractionRing R) F]
    (H : ∀ z : Sp F ⟶ (TW U).left, z ≫ (TW U).hom = jFK (R := R) F ≫ jK R → ∀ p J, Good D.P.L p J →
      val s z p J = val (D.psi x) (jFK (R := R) F) p J) :
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ s (jK R ∣_ U)) (LB.pullGen D.P.L _ _ (D.psi x) (jK R ⁻¹ᵁ U).ι) := by
  have sep : D.P.A.left.IsSeparated := by
    have := D.P.isAb.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from D.P.A.hom]
    infer_instance
  obtain ⟨lam, hl⟩ : ∃ lam : Sp F ⟶ (jK R ⁻¹ᵁ U).toScheme, lam ≫ (jK R ⁻¹ᵁ U).ι = jFK (R := R) F :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact TauPull.jK_mem _ U hU), IsOpenImmersion.lift_fac _ _ _⟩
  have hκ : (lam ≫ jK R ∣_ U) ≫ U.ι = jFK (R := R) F ≫ jK R := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hl]
  have p : Sp F := (default : PrimeSpectrum F)
  have hss : Subsingleton (Spec (CommRingCat.of (FractionRing R))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  refine TauPull.corr_of_dense D.P.isLB lam p (fun V ⟨y, hy⟩ => ?_) fun J hJ => ?_
  · rw [show lam p = y from Subtype.ext (Subsingleton.elim _ _)]
    exact hy
  · rw [val_pull hJ, val_pull hJ, hl]
    exact H _ hκ p J hJ

end GlobalTheory.ArcPsiOn


open GlobalTheory.ArcPsiOn GlobalTheory.ArcPull ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem GlobalTheory.arcWit_psiOn_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (Dm : Geo.Tor.Datum H) (l : Geo.Tor.Level H) (Xo : Geo.Tor.Moduli Dm l) (c : Geo.Tor.Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Geo.Tor.Model Xo c β) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : Geo.Tor.ArcIn Dm l β O' b) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (f : O' →+* R), Function.Injective f → ∀ (u : R), u ≠ 0 → ∀ (χ : Geo.Tor.Sp R ⟶ Y.X) (W : Geo.Tor.ArcWit Y a I f u χ), ∃ ψW : PsiOn W.P.D.toPre (PrimeSpectrum.basicOpen u), ∀ (F : Type) [Field F] [Algebra (FractionRing O') F] (r : R →+* F) (z : Spec (CommRingCat.of F) ⟶ (TW (R := R) (PrimeSpectrum.basicOpen u)).left), z ≫ (TW (R := R) (PrimeSpectrum.basicOpen u)).hom = specOf r → (∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) = r (f x)) → ∀ y, Geo.Tor.GenRel W.w (LB.pullGen _ _ _ (ψW.psi (W.e y)) z) (LB.pullGen _ _ _ (a.D₀.psi y) (jFK (R := O') F)) (r u ^ (a.be y y / 2)) := by
  intro E _ _ _ H Dm l Xo c O _ β Y O' _ _ b a R _ _ I f hf u hu χ W
  obtain ⟨-, s2, -, -, s5, s6⟩ := W.spec
  choose s hs H using fun x : W.P.D.toPre.X => exists_gen_on f u W.w s2 (W.e.symm x) x
    (by simpa only [LinearEquiv.apply_symm_apply] using s5 (W.e.symm x)) (a.gen _)
    (a.be (W.e.symm x) (W.e.symm x) / 2)
  refine ⟨⟨s, hs, fun x => ?_⟩, fun F _ _ r z hz hr y => ?_⟩
  · let F := AlgebraicClosure (FractionRing R)
    letI : Algebra (FractionRing O') F := ((algebraMap (FractionRing R) F).comp (fracMap hf)).toAlgebra
    have hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
        algebraMap (FractionRing R) F (algebraMap R _ (f x)) := fun x =>
      congrArg (algebraMap (FractionRing R) F) (fracMap_algebraMap hf x)
    refine corr_of_geom _ ⟨⟨⊥, Ideal.isPrime_bot⟩, hu⟩ x (s x) F fun z hz p J hJ => ?_
    have hj : jFK (R := R) F ≫ jK R = specOf ((algebraMap (FractionRing R) F).comp (algebraMap R _)) :=
      (spMap_comp _ _).symm
    have k := H x F _ z (hz.trans hj) (jFK (R := O') F) ((spMap_comp _ _).symm.trans
      ((congrArg spMap (RingHom.ext hF)).trans (spMap_comp f _)))
    have k' := (s6 F _ hF rfl).1 (W.e.symm x)
    rw [LinearEquiv.apply_symm_apply] at k'
    have e := val_eq_of_genRel W.P.D.toPre.P.isLB a.D₀.P.isLB (by
      show z ≫ (TW (R := R) (PrimeSpectrum.basicOpen u)).hom ≫ (W.P.D.toPre.c x).left =
        jFK (R := R) F ≫ jK R ≫ (W.P.D.toPre.c x).left
      rw [← Category.assoc, hz, Category.assoc]) k k' p hJ
    rwa [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at e
  · have k := H (W.e y) F r z hz (jFK (R := O') F) ((spMap_comp _ _).symm.trans
      ((congrArg spMap (RingHom.ext hr)).trans (spMap_comp f r)))
    rw [LinearEquiv.symm_apply_apply] at k
    exact k
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianDim

theorem exists_relDim_of_connected {S : Scheme.{0}} [ConnectedSpace S] (B : Over S) [GrpObj B]
    (hB : IsAbelianScheme B) : ∃ g, SmoothOfRelativeDimension g B.hom := by
  have := hB.smooth
  have := hB.geomConnected
  have : ConnectedSpace B.left := (GroupConn.connectedSpace_group S B).1
  obtain ⟨x⟩ : Nonempty B.left := inferInstance
  exact exists_dim_of_preconnected B.hom x

theorem connectedSpace_spec_of_isLocalRing (A : Type) [CommRing A] [IsLocalRing A] :
    ConnectedSpace (Spec (CommRingCat.of A)) := by
  show ConnectedSpace (PrimeSpectrum A)
  rw [connectedSpace_iff_univ]
  refine ⟨⟨IsLocalRing.closedPoint A, trivial⟩, ?_⟩
  intro u v hu hv huv ⟨x, _, hx⟩ ⟨y, _, hy⟩
  have hc : IsLocalRing.closedPoint A ∈ u ∪ v := huv trivial
  rcases hc with h | h
  · exact ⟨y, trivial, (IsLocalRing.specializes_closedPoint y).mem_open hu h, hy⟩
  · exact ⟨x, trivial, hx, (IsLocalRing.specializes_closedPoint x).mem_open hv h⟩

theorem exists_relDim : ∀ (A : Type) [CommRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B], IsAbelianScheme B → ∃ g, SmoothOfRelativeDimension g B.hom := by
  intro A _ _ B _ hB
  have := connectedSpace_spec_of_isLocalRing A
  exact exists_relDim_of_connected B hB

end GlobalTheory.AbelianDim
end
