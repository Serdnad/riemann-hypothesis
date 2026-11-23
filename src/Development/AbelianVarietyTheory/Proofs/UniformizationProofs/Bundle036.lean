module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle030
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPullDeg

@[expose] public section

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcData

theorem unit_ext_field {K F : Type} [Field K] [Field F] (ρ : Sp F ⟶ Sp K) (z : Sp F) {U : (Sp K).Opens}
    {a b : Γ(Sp K, U)ˣ} (h : ρ z ∈ U → gm ρ z U a = gm ρ z U b) : a = b := by
  have sK : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  by_cases hz : ρ z ∈ U
  · obtain rfl : U = ⊤ := top_le_iff.1 fun y _ => by rw [Subsingleton.elim y (ρ z)]; exact hz
    have e := congrArg Units.val (h hz)
    rw [gm_val ρ z ⊤ hz, gm_val ρ z ⊤ hz] at e
    have hK : IsField Γ(Sp K, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)
    letI := hK.toField
    exact Units.ext (RingHom.injective
      (((Sp F).presheaf.germ (ρ ⁻¹ᵁ ⊤) z hz).hom.comp (ρ.app ⊤).hom) e)
  · exact unit_ext fun y hy => absurd (by rw [Subsingleton.elim (ρ z) y]; exact hy) hz

variable {R : Type} [CommRing R] [IsDomain R]

theorem mapsAt_of_genRel {D D' : DegPre R} {B₀ : Scheme.{0}} {M₀ : LB B₀} (hM₀ : M₀.IsLB) {φ : D.P.A.left ⟶ B₀}
    {Φ : D'.P.A.left ⟶ D.P.A.left} {w : LB.Iso D.P.L (M₀.pull φ)} {wD : LB.Iso D'.P.L (D.P.L.pull Φ)}
    {w' : LB.Iso D'.P.L (M₀.pull (Φ ≫ φ))} (T : Tri w wD w') {F : Type} [Field F] (ρ : Sp F ⟶ (TK R).left)
    (x : D'.X) (y : D.X) (hx : D'.xK x ≫ Φ = D.xK y) {pt₀ : PUnit → (Sp F ⟶ B₀)}
    (t₀ : LB.Gen (LB.LinComb M₀ pt₀ (fun _ => -1))) (s : F)
    (h : GenRel w (LB.pullGen _ _ _ (D.psi y) ρ) t₀ s) (h' : GenRel w' (LB.pullGen _ _ _ (D'.psi x) ρ) t₀ s) :
    ∃ b : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => D'.xK x ≫ Φ) (fun _ => -1)),
      GeneratorPullback.MapsAt D.P.L D'.P.L (J := PUnit) (fun _ => Φ) wD (D'.xK x) (-1) (D'.psi x) b ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J), Good D.P.L z J → val b r z J = val (D.psi y) r z J := by
  obtain ⟨b, -, vb⟩ := exists_gen D.P.isLB (K' := PUnit) (φ' := fun _ => D'.xK x ≫ Φ) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) hx.symm) (D.psi y) (D.psi_gen y)
  refine ⟨b, fun jN jL => ?_, vb⟩
  have z : Sp F := (default : PrimeSpectrum F)
  refine unit_ext_field (K := FractionRing R) ρ z fun hz => ?_
  have mN : Φ (D'.xK x (ρ z)) ∈ D.P.L.U (jN PUnit.unit) := mem_pull.1 hz.1
  have mL : D'.xK x (ρ z) ∈ D'.P.L.U jL := hz.2
  have hp : (ρ ≫ D'.xK x) ≫ Φ = ρ ≫ D.xK y := by rw [Category.assoc, hx]
  have mN' : (ρ ≫ D.xK y) z ∈ D.P.L.U (jN PUnit.unit) := by rw [← hp]; exact mN
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB z (K := PUnit) (fun _ => ρ ≫ D.xK y) jN (fun _ _ _ => rfl)
    (fun _ => mN')
  obtain ⟨j₀, hj₀⟩ := exists_chart hM₀ (φ (Φ (D'.xK x (ρ z))))
  have hj₀' : φ ((ρ ≫ D.xK y) z) ∈ M₀.U j₀ := by rw [← hp]; exact hj₀
  have e := ((genRel_iff w _ t₀ s z).1 h).2 jN (fun _ => j₀) (fun _ => hj₀') (fun _ => mN')
  have e' := ((genRel_iff w' _ t₀ s z).1 h').2 (fun _ => jL) (fun _ => j₀) (fun _ => hj₀) (fun _ => mL)
  have E := Units.ext (e.trans e'.symm)
  rw [Fintype.prod_unique, Fintype.prod_unique, T _ (ρ ≫ D'.xK x) z j₀ (jN PUnit.unit) jL hj₀ mN mL, hp, mul_zpow,
    _root_.mul_assoc] at E
  have E' := mul_left_cancel E
  have a₁ := gm_pullGen D.P.L (fun _ : PUnit => D.xK y) _ (D.psi y) ρ (𝟙 _) z jN (Set.mem_iInter.2 fun _ => mN')
  have a₂ := gm_pullGen D'.P.L (fun _ : PUnit => D'.xK x) _ (D'.psi x) ρ (𝟙 _) z (fun _ => jL)
    (Set.mem_iInter.2 fun _ => mL)
  rw [Category.id_comp] at a₁ a₂
  have v := vb _ ρ z J hJ
  rw [val_of b ρ z J jN (fun k => by rw [hx]; exact eJ k), val_of (D.psi y) ρ z J jN eJ] at v
  refine (gm_res _ z _ hz _).trans (v.trans (a₁.symm.trans (E'.trans (Eq.symm ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ ((gm_res _ z _ hz _).trans a₂.symm)))))))
  exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull ρ _ z _ hz _))

theorem exists_isPullDeg_id (D D' : DegPre R) {S₀ : Scheme.{0}} {A₀ : Over S₀} [GrpObj A₀] {M₀ : LB A₀.left}
    (hM₀ : M₀.IsLB) (rig₀ : LB.Gen (M₀.pull (eSec A₀))) {f : Sp R ⟶ S₀} {φ : D.P.A.left ⟶ A₀.left}
    {φ' : D'.P.A.left ⟶ A₀.left} (p : IsGrpPullback D.P.A A₀ f φ) (p' : IsGrpPullback D'.P.A A₀ f φ')
    (w : LB.Iso D.P.L (M₀.pull φ)) (w' : LB.Iso D'.P.L (M₀.pull φ')) (g : PGen w) (g' : PGen w')
    (r : PMaps w (K := PUnit) (fun _ => eSec D.P.A) (fun _ => eSec A₀) (fun _ => 1) D.rig rig₀ f)
    (r' : PMaps w' (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec A₀) (fun _ => 1) D'.rig rig₀ f)
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ φ' = (D.c (xe x)).left ≫ φ)
    (Wo : (Spec (CommRingCat.of R)).Opens) (hWo : genericPoint (Spec (CommRingCat.of R)) ∈ Wo) (ψW : PsiOn D Wo)
    {F : Type} [Field F] (ρ : Sp F ⟶ (TK R).left)
    (hψ : ∀ x, ∃ (pt₀ : PUnit → (Sp F ⟶ A₀.left)) (t₀ : LB.Gen (LB.LinComb M₀ pt₀ (fun _ => -1))) (s : F),
      GenRel w (LB.pullGen _ _ _ (D.psi (xe x)) ρ) t₀ s ∧ GenRel w' (LB.pullGen _ _ _ (D'.psi x) ρ) t₀ s) :
    ∃ hD : IsPullDeg (RingHom.id R) D D',
      (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) ≫ φ = φ' ∧ (∀ x, hD.xe x = xe x) ∧
      ∃ w₁ : LB.Iso D'.P.L (M₀.pull ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) ≫ φ)),
        HEq w₁ w' ∧ Tri w hD.w w₁ := by
  have hs := specOf_id R
  have hsf : specOf (RingHom.id R) ≫ f = f := by rw [hs, Category.id_comp]
  obtain ⟨e, me, he⟩ := grpPullback_iso p'
    (((isGrpPullback_pullback D.P.A (specOf (RingHom.id R))).comp p).congr hsf rfl)
  rw [← Category.assoc] at he
  subst he
  have gp : IsGrpPullback D'.P.A D.P.A (specOf (RingHom.id R))
      (e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback D.P.A (specOf (RingHom.id R)))).congr
      (Category.id_comp _) rfl
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) =
      specOf (RingHom.id R) ≫ eSec D.P.A := (cubeMapOf gp).e_comm
  obtain ⟨wD, T⟩ := exists_cancel hM₀ w w' g g' D.P.isLB D'.P.isLB
  have hc' : ∀ x, (D'.c x).left ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) =
      (D.c (xe x)).left := fun x => by
    apply p.1.hom_ext
    · rw [Category.assoc]; exact hc x
    · rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w, Over.w, hs]; exact Category.comp_id _
  obtain ⟨gW, hgW⟩ : ∃ gW : (TK R).left ⟶ (TW Wo).left, gW ≫ Wo.ι = jK R :=
    ⟨IsOpenImmersion.lift Wo.ι (jK R) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hy : jK R y = genericPoint (Spec (CommRingCat.of R)) := by
        rw [genericPoint_eq_bot_of_affine]
        apply PrimeSpectrum.ext
        show Ideal.comap (algebraMap R (FractionRing R)) (PrimeSpectrum.asIdeal y) = ⊥
        rw [@Ideal.eq_bot_of_prime _ _ (PrimeSpectrum.asIdeal y) (PrimeSpectrum.isPrime y)]
        exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))
      show jK R y ∈ Wo
      rw [hy]; exact hWo), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ Wo).toScheme, lam ≫ (jK R ⁻¹ᵁ Wo).ι = 𝟙 _ ∧
      lam ≫ (jK R ∣_ Wo) = gW :=
    ⟨(isPullback_morphismRestrict (jK R) Wo).lift _ _ (hgW.trans (Category.id_comp _).symm),
      (isPullback_morphismRestrict (jK R) Wo).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) Wo).lift_fst _ _ _⟩
  refine ⟨⟨e, me, wD, (isGen_iff _).2 (T.pgen_cancel hM₀ g g'), hE, ?_, xe,
    fun x => (hc' x).trans (by rw [hs, Category.id_comp]), Wo, ψW, gW, hgW.trans (by rw [hs, Category.comp_id]),
    fun x => ?_⟩, rfl, fun _ => rfl, w', HEq.rfl, T⟩
  · refine (maps_iff wD _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf (RingHom.id R)) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf (RingHom.id R)) hE D.P.L) (fun _ => rfl)).2 ?_
    exact T.pmaps_cancel hM₀ (fun _ => hE) r (by rw [hsf]; exact r')
  · obtain ⟨pt₀, t₀, s, h, h'⟩ := hψ x
    obtain ⟨b, hb, vb⟩ := mapsAt_of_genRel hM₀ T ρ x (xe x)
      ((Category.assoc _ _ _).trans (congrArg (jK R ≫ ·) (hc' x))) t₀ s h h'
    refine ⟨b, hb, corr_of_val D.P.isLB fun y J hJ => (vb _ _ y J hJ).trans ?_⟩
    have v := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) lam).trans (val_pull hJ _ _ _))
    rw [l₁, l₂] at v
    exact v.symm.trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])).symm

end GlobalTheory.ArcData

namespace GlobalTheory

theorem arcWit_data_iso : Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ'), ∃ (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre), ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ ∧ (∀ x, hD.xe (W.e x) = W'.e x) ∧ ∃ w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)), HEq w₁ W.w ∧ Tri W'.w hD.w w₁) := by
  intro h5 E _ _ _ H D l c₀ c k _ bF a O O' _ _ β β' Y Y' χ χ' W W'
  obtain ⟨s1, s2, s3, -, s5, s6⟩ := W.spec
  obtain ⟨t1, t2, t3, -, t5, t6⟩ := W'.spec
  obtain ⟨Wo, hWo, ⟨ψW⟩⟩ := h5.psiOnExists _ _ (admissibleBase_powerSeries k) W'.P.D
  let F := AlgebraicClosure (FractionRing (PowerSeries k))
  let κ : k →+* F := ((algebraMap (FractionRing (PowerSeries k)) F).comp (algebraMap (PowerSeries k) _)).comp
    (PowerSeries.C (R := k))
  letI : Algebra (FractionRing k) F := (IsFractionRing.lift (K := FractionRing k) (g := κ) κ.injective).toAlgebra
  have ha : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C (R := k) x)) :=
    fun x => IsFractionRing.lift_algebraMap (K := FractionRing k) (g := κ) κ.injective x
  have k₁ := (s6 F _ ha rfl).1
  have k₂ := (t6 F _ ha rfl).1
  let xe : W.P.D.toPre.X ≃+ W'.P.D.toPre.X := W.e.symm.toAddEquiv.trans W'.e.toAddEquiv
  have hxe : ∀ y, xe (W.e y) = W'.e y := fun y => congrArg W'.e (W.e.symm_apply_apply y)
  obtain ⟨hD, h₁, h₂, h₃⟩ := ArcData.exists_isPullDeg_id W'.P.D.toPre W.P.D.toPre a.D₀.P.isLB a.D₀.rig t1 s1 W'.w W.w
    ((isGen_iff _).1 t2) ((isGen_iff _).1 s2)
    ((maps_iff W'.w _ (fun _ => eSec a.D₀.P.A) _ W'.P.D.toPre.rig a.D₀.rig _ _
      (rigPull_le W'.φ _ W'.he a.D₀.P.L) (fun _ => rfl)).1 t3)
    ((maps_iff W.w _ (fun _ => eSec a.D₀.P.A) _ W.P.D.toPre.rig a.D₀.rig _ _
      (rigPull_le W.φ _ W.he a.D₀.P.L) (fun _ => rfl)).1 s3)
    xe (fun x => by
      obtain ⟨y, rfl⟩ := W.e.surjective x
      rw [hxe]
      exact (s5 y).trans (t5 y).symm) Wo hWo ψW (F := F) (jFK (R := PowerSeries k) F) (fun x => by
      obtain ⟨y, rfl⟩ := W.e.surjective x
      rw [hxe]
      exact ⟨_, _, _, k₂ y, k₁ y⟩)
  exact ⟨hD, h₁, fun x => (h₂ _).trans (hxe x), h₃⟩

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PsiWZeroPull

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TauPull GlobalTheory.DegPull

section OnW

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem rel_on (ψW : PsiOn D W) (hW : (W : Set (Spec (CommRingCat.of R))).Nonempty) {K : Type} [Fintype K]
    {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb D.P.L φ ε)) (a b : D.X)
    (h : LB.Gen.Corr D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (D.tau a b) (LB.pullGen D.P.L _ _ u (D.xK a)))
      (LB.mulGen D.P.L _ _ _ _ (D.psi a) D.rigK)) :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (ψW.tau a b) (LB.pullGen D.P.L _ _ u (cP D (TW W) a).left))
      (LB.mulGen D.P.L _ _ _ _ (ψW.psi a) (D.rigW W)) := by
  have sep : D.P.A.left.IsSeparated := by
    have := D.P.isAb.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from D.P.A.hom]
    infer_instance
  obtain ⟨lam, hl⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact jK_mem y W hW), IsOpenImmersion.lift_fac _ _ _⟩
  have hκ : (lam ≫ jK R ∣_ W) ≫ W.ι = jK R := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hl, Category.id_comp]
  let κ : TK R ⟶ TW W := Over.homMk (lam ≫ jK R ∣_ W) hκ
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  have red : IsReduced (TW W).left := inferInstanceAs (IsReduced W.toScheme)
  refine corr_of_dense D.P.isLB κ.left z (fun V hV => ?_) fun J hJ => ?_
  · have h₁ : jK R z ∈ W.ι ''ᵁ V := jK_mem z _ (hV.image _)
    obtain ⟨y, hy, e⟩ := h₁
    have e' : W.ι y = W.ι (κ.left z) := e.trans (congrArg (fun q => q z) hκ).symm
    rw [← W.ι.isOpenEmbedding.injective e']
    exact hy
  · have vψ : ∀ χ, val (ψW.psi χ) κ.left z J = val (D.psi χ) (𝟙 _) z J := fun χ => by
      have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq χ) lam).trans (val_pull hJ _ _ _))
      rw [hl] at this
      exact this
    have vρ : val (D.rigW W) κ.left z J = val D.rigK (𝟙 _) z J := by
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      rw [Category.id_comp]
      exact congrArg (fun q => val D.rig q z J) hκ
    have vτ : ∀ a b, val (ψW.tau a b) κ.left z J = val (D.tau a b) (𝟙 _) z J := fun a b => by
      rw [val_tauW ψW _ hJ, val_tau _ hJ, vψ, vψ, vψ, vρ]
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ h (𝟙 _)).trans (val_mul hJ _ _ _))
    refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    rw [vτ, vψ, vρ, ← e]
    refine congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
    refine congrArg (fun q => val u q z J) ?_
    rw [Category.id_comp]
    exact congrArg (fun q => q.left) (comp_cP D κ a)

end OnW

theorem prod_four {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (f : A ⟶ A) (x : T ⟶ A) {U : Type}
    [CommGroup U] (k : (T.left ⟶ A.left) → U) :
    ∏ i : Fin 4, k (x.left ≫ (![(padd A (𝟙 _) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left] : Fin 4 → _) i) ^
      (![1, -2, -1, 2] : Fin 4 → ℤ) i =
      k (x * (x ≫ f)).left * (k x.left ^ 2)⁻¹ * (k (x ≫ f).left)⁻¹ * k (1 : T ⟶ A).left ^ 2 := by
  rw [Fin.prod_univ_four]
  show k (x ≫ (𝟙 A * f)).left ^ (1 : ℤ) * k (x ≫ 𝟙 A).left ^ (-2 : ℤ) * k (x ≫ f).left ^ (-1 : ℤ) *
    k (x ≫ 1).left ^ (2 : ℤ) = _
  rw [MonObj.comp_mul, MonObj.comp_one, Category.comp_id, zpow_one, zpow_neg_one, zpow_neg, zpow_ofNat, zpow_ofNat]

section Pull

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}


theorem traceFormTwistIso_of_pullback (hD : IsPullDeg φ D D') {O : Type} [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X]
    (ιD : D.OAct O) (ιD' : D'.OAct O) (hx : ∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y)
    (hact : ∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a))
    (w0 : O) (h : TraceFormTwistIso D ιD w0) : TraceFormTwistIso D' ιD' w0 := by
  obtain ⟨u, hu, hn, hrel⟩ := h
  have gp := pull_grp hD
  let Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  have ha : (ιD'.onB.act w0).left ≫ Φ = Φ ≫ (ιD.onB.act w0).left := by
    have a₂ : ((Over.pullback (specOf φ)).map (ιD.onB.act w0)).left ≫ pullback.fst D.P.A.hom (specOf φ) =
        pullback.fst _ _ ≫ (ιD.onB.act w0).left := pullback.lift_fst _ _ _
    show _ ≫ hD.e.hom.left ≫ _ = (hD.e.hom.left ≫ _) ≫ _
    rw [← Category.assoc, ← Over.comp_left, hact, Over.comp_left, Category.assoc, a₂, Category.assoc]
  have hψ : ∀ k : Fin 4, (![(padd D'.P.A (𝟙 _) (ιD'.onB.act w0)).left, 𝟙 D'.P.A.left, (ιD'.onB.act w0).left,
      (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → _) k ≫ Φ =
      Φ ≫ (![(padd D.P.A (𝟙 _) (ιD.onB.act w0)).left, 𝟙 D.P.A.left, (ιD.onB.act w0).left,
      (toUnit D.P.A ≫ η[D.P.A]).left] : Fin 4 → _) k := by
    have p1 : (pushPt gp.1.w (𝟙 D'.P.A)).left = Φ := Category.id_comp _
    intro k
    fin_cases k
    · have m : pushPt gp.1.w (𝟙 D'.P.A * ιD'.onB.act w0) =
          pushPt gp.1.w (𝟙 D'.P.A) * pushPt gp.1.w (ιD'.onB.act w0) := map_mul (pushHom gp D'.P.A) _ _
      have q : pushPt gp.1.w (ιD'.onB.act w0) = pushPt gp.1.w (𝟙 D'.P.A) ≫ ιD.onB.act w0 :=
        Over.OverMorphism.ext (by rw [Over.comp_left, p1]; exact ha)
      have m' : pushPt gp.1.w (𝟙 D'.P.A * ιD'.onB.act w0) =
          pushPt gp.1.w (𝟙 D'.P.A) ≫ (𝟙 D.P.A * ιD.onB.act w0) := by
        rw [m, q, MonObj.comp_mul, Category.comp_id]
      have := congrArg (fun q => q.left) m'
      simp only [Over.comp_left, p1] at this
      exact this
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact ha
    · have m : pushPt gp.1.w (1 : D'.P.A ⟶ D'.P.A) = pushPt gp.1.w (𝟙 D'.P.A) ≫ (1 : D.P.A ⟶ D.P.A) := by
        rw [MonObj.comp_one]; exact map_one (pushHom gp D'.P.A)
      have := congrArg (fun q => q.left) m
      simp only [Over.comp_left, p1] at this
      exact this
  obtain ⟨u', hu', pmu⟩ := exists_pmaps ((isGen_iff hD.w).1 hD.w_gen) D.P.isLB D'.P.isLB Φ hψ u hu
  have vu : ∀ {T : Over (Spec (CommRingCat.of R'))} (x : T ⟶ D'.P.A) (z : T.left) J J', Good D.P.L z J →
      Good D'.P.L z J' → ∀ Ω : (T ⟶ D'.P.A) → (T.left.presheaf.stalk z)ˣ,
      (∀ x, Ω x = gw hD.w x.left z (J (x.left ≫ Φ)) (J' x.left)) → val u (x.left ≫ Φ) z J =
        Ω (x * (x ≫ ιD'.onB.act w0)) * (Ω x ^ 2)⁻¹ * (Ω (x ≫ ιD'.onB.act w0))⁻¹ * Ω 1 ^ 2 * val u' x.left z J' :=
    fun x z J J' hJ hJ' Ω hΩ => by
      rw [hΩ, hΩ, hΩ, hΩ]
      exact (pmaps_val hψ pmu x.left z hJ hJ').trans (congrArg₂ (· * ·)
        (prod_four (ιD'.onB.act w0) x (fun q => gw hD.w q z (J (q ≫ Φ)) (J' q))) rfl)
  refine ⟨u', hu', corr_of_val D'.P.isLB fun y J' hJ' => ?_, fun a => corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
    have := ιD'.onB.hom w0
    have e := vu (1 : 𝟙_ _ ⟶ D'.P.A) y J J' hJ hJ' _ (fun _ => rfl)
    have e₁ : (1 : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ D'.P.A).left = eSec D'.P.A := Category.id_comp _
    have b := val_corr hJ hn (specOf φ)
    rw [val_pull hJ, val_one, ← hD.he] at b
    rw [MonObj.one_comp, _root_.mul_one, e₁] at e
    rw [val_pull hJ', val_one, Category.id_comp]
    have e' := congrArg Additive.ofMul (b.symm.trans e)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
    let Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ :=
      fun x => gw hD.w x.left y (J (x.left ≫ Φ)) (J' x.left)
    have vψ : ∀ χ, val (hD.psiW.psi (hD.xe χ)) hD.g y J = (Ω (cP D' _ χ))⁻¹ * val (D'.psi χ) (𝟙 _) y J' :=
      fun χ => val_psiW hD hJ hJ' χ
    have vρ : val (D.rigW hD.W) hD.g y J = Ω 1 * val D'.rigK (𝟙 _) y J' := by
      have pm := (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
        (rigPull_le Φ (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig
      have a₂ : ((TK R').hom ≫ specOf φ) ≫ eSec D.P.A = (1 : TK R' ⟶ D'.P.A).left ≫ Φ :=
        congrArg (fun q => q.left) (map_one (pushHom gp (TK R'))).symm
      have e := pm _ (TK R').hom y (fun _ => J ((1 : TK R' ⟶ D'.P.A).left ≫ Φ))
        (fun _ => J' (1 : TK R' ⟶ D'.P.A).left) (fun _ => hJ _) (fun _ => hJ' _)
      rw [Fintype.prod_unique, zpow_one] at e
      have b₁ : hD.g ≫ (toUnit (TW hD.W)).left = (TK R').hom ≫ specOf φ := hD.g_comm
      have b₂ : 𝟙 _ ≫ (toUnit (TK R')).left = (TK R').hom := Category.id_comp _
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
      rw [b₁, b₂]
      exact (val_of _ _ y J _ (fun _ => congrArg J a₂)).trans e
    have cW : hD.g ≫ (cP D (TW hD.W) (hD.xe a)).left = (cP D' (TK R') a).left ≫ Φ := by
      have hx : (cP D' (TK R') a).left ≫ Φ = jK R' ≫ specOf φ ≫ (D.c (hD.xe a)).left := by
        rw [← hD.c_pr a, ← Category.assoc]; rfl
      rw [hx, ← Category.assoc (jK R'), ← hD.g_comm, Category.assoc]; rfl
    have cl : cP D' (TK R') a ≫ ιD'.onB.act w0 = cP D' (TK R') (w0 • a) := by
      rw [cP, cP, ιD'.c_lin, Category.assoc]
    have key := (val_mul hJ _ _ _).symm.trans ((val_corr hJ
      (rel_on hD.psiW ⟨_, (hD.g y).2⟩ u _ _ (hrel (hD.xe a))) hD.g).trans (val_mul hJ _ _ _))
    rw [val_pull hJ, cW, vu (cP D' (TK R') a) y J J' hJ hJ' Ω (fun _ => rfl), cl, val_tauW _ _ hJ, ← hx, ← map_add (f := _),
      vψ, vψ, vψ, vρ, cPoint_add] at key
    refine (val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
    have b : val (LB.pullGen D'.P.L _ _ u' (D'.xK a)) (𝟙 _) y J' = val u' (cP D' (TK R') a).left y J' := by
      rw [val_pull hJ', Category.id_comp]; rfl
    rw [b, val_tau _ hJ']
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul key
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at e' ⊢
    linear_combination (norm := abel) e'

end Pull

end PsiWZeroPull

theorem traceFormTwistIso_of_overPullback : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R')
    (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X]
    [Module O D'.X] (ιD : D.OAct O) (ιD' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) →
    (∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a)) →
    ∀ w0 : O, Geo.Tor.TraceFormTwistIso D ιD w0 → Geo.Tor.TraceFormTwistIso D' ιD' w0 :=
  fun _ _ _ _ _ _ _ _ _ hD _ _ _ _ _ ιD ιD' hx hact w0 h => PsiWZeroPull.traceFormTwistIso_of_pullback hD ιD ιD' hx hact w0 h

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DegCompare

open GlobalTheory.PsiInPull GlobalTheory.PsiInPow

section Generic

variable {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (z : Z)

variable {L : LB X} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)

end Generic

variable {R : Type} [CommRing R] [IsDomain R]

variable (D : DegPre R)

section Values

variable {D} {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J : (Z ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
include hJ

theorem val_tau (a b : D.X) : val (D.tau a b) r z J =
    val (D.psi (a + b)) r z J * (val (D.psi a) r z J)⁻¹ * (val (D.psi b) r z J)⁻¹ * (val D.rigK r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem val_tau_symm (a b : D.X) : val (D.tau a b) r z J = val (D.tau b a) r z J := by
  rw [val_tau r hJ, val_tau r hJ, add_comm b a, mul_right_comm (val (D.psi (a + b)) _ z J)]

end Values

end GlobalTheory.DegCompare
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.expansion_extensionField_total : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w.IsGen → (∀ s : Fam D.toPre F k, ∃ t, U.toUnifPre.ExpandsF F k w t s) ∧ ∀ t, ∃ s : Fam D.toPre F k, U.toUnifPre.ExpandsF F k w t s := by
  first | exact @GlobalTheory.expandsF_total | exact GlobalTheory.expandsF_total | (intros; apply GlobalTheory.expandsF_total <;> assumption)
end
