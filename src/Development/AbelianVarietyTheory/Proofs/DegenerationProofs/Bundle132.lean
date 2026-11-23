module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle062
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle085
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericSectionExtendsNormal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle119
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle122
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle124
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationValuesIntOfAdmissibleBase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PowerSeries.Ideal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
public import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ClosedPol

theorem exists_fibre_pull (laws : Laws) {S S' Z Z' : Scheme.{0}} {j : Z ⟶ S} {j' : Z' ⟶ S'} {f : S' ⟶ S} {ψ : Z' ⟶ Z}
    (sq : ψ ≫ j = j' ≫ f) {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) (A : PolAV Z)
    (gen : (Over.pullback j).obj G ≅ A.A) [IsMonHom gen.hom]
    (hA : LBIso (A.L.pull gen.hom.left) (L.pull (pullback.fst G.hom j))) :
    ∃ (A' : PolAV Z') (gen' : (Over.pullback j').obj ((Over.pullback f).obj G) ≅ A'.A),
      IsMonHom gen'.hom ∧ LBIso (A'.L.pull gen'.hom.left) ((L.pull (pullback.fst G.hom f)).pull
        (pullback.fst ((Over.pullback f).obj G).hom j')) := by
  obtain ⟨A', g, hg, -, mul, t, ht⟩ := laws.polBaseChange _ _ ψ A
  have pg : IsGrpPullback A'.A A.A ψ g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    obtain rfl : x₀ = toBase hg.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = toBase hg.w y := Over.OverMorphism.ext hy
    exact (congrArg (fun a => a.left) (mul T x y)).symm⟩
  have : IsMonHom gen.symm.hom := inferInstanceAs (IsMonHom gen.inv)
  have h₂ := (pg.comp ((isGrpPullback_of_iso gen.symm).comp (isGrpPullback_pullback G j))).congr
    ((congrArg _ (Category.id_comp _)).trans sq) rfl
  obtain ⟨gen', hgen', e⟩ := grpPullback_iso ((isGrpPullback_pullback _ j').comp
    (isGrpPullback_pullback G f)) h₂
  have hi : gen.inv.left ≫ gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, gen.inv_hom_id, Over.id_left]
  refine ⟨A', gen', hgen', LBIso.trans (LB.isLB_pull A'.isLB _) (LB.isLB_pull (LB.isLB_pull A.isLB g) gen'.hom.left)
    (LB.isLB_pull (LB.isLB_pull hL _) _) ?_ ?_⟩
  · exact LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl) (LBIso.symm ⟨t, ht⟩)
  · refine LBIso.chartPull (h := gen'.hom.left ≫ g ≫ gen.inv.left)
      (chartPullLinComb A.L g _ (fun _ : PUnit => gen.hom.left) _ _ fun _ => ?_)
      (chartPullLinComb L _ _ (fun _ : PUnit => pullback.fst G.hom j) _ _ fun _ => ?_) hA
    · rw [Category.assoc, Category.assoc, hi, Category.comp_id]
    · rw [Category.assoc, Category.assoc]
      exact e.symm

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem exists_generic_square {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]
    (φ : R →+* V) (hφ : Function.Injective φ) :
    ∃ ψ : Spec (CommRingCat.of (FractionRing V)) ⟶ Spec (CommRingCat.of (FractionRing R)),
      ψ ≫ jK R = jK V ≫ spMap φ := by
  have gen : ∀ (K F : Type) [Field K] [Field F] [Algebra R K] [IsFractionRing R K] (g : R →+* F),
      Function.Injective g → ∃ ψ : K →+* F, ψ.comp (algebraMap R K) = g := fun K F _ _ _ _ g hg =>
    ⟨IsFractionRing.lift hg, RingHom.ext fun x => IsFractionRing.lift_algebraMap hg x⟩
  obtain ⟨ψ, hψ⟩ := gen (FractionRing R) (FractionRing V) ((algebraMap V (FractionRing V)).comp φ)
    ((IsFractionRing.injective V (FractionRing V)).comp hφ)
  exact ⟨spMap ψ, (spMap_comp _ ψ).trans ((congrArg spMap hψ).trans (spMap_comp φ _).symm)⟩

theorem exists_desc_pull {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G : Over S} {G' : Over S'}
    [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {F : G'.left ⟶ G.left} (pF : IsGrpPullback G' G f F)
    (Q : TQ G X) {P : CP G} (D : Q.Desc P) {P' : CP G'} {hw w} (k : IsCPMap P' P f F hw w) :
    ∃ (Q' : TQ G' X) (D' : Q'.Desc P') (β : Q'.B.left ⟶ Q.B.left), IsGrpPullback Q'.B Q.B f β ∧
      LBIso D'.M.L.L (D.M.L.L.pull β) := by
  obtain ⟨Q₀, hQ⟩ := exists_tq_baseChange _ _ _ X _ _ F pF Q
  obtain ⟨β, eβ, pβ⟩ := TQ.exists_isGrpPullback _ _ _ X _ _ F pF Q Q₀ hQ
  obtain ⟨M₀, v, hv⟩ := exists_pull (hw := pβ.1.w) D.M
    (fun Z x y => Over.OverMorphism.ext (pβ.2 Z x y _ _ rfl rfl).symm)
  obtain ⟨w₄, -, k₄⟩ := D.map.exists_comp k (by rw [Category.assoc, Over.w, hw, Category.comp_id])
  obtain ⟨w₅, k₅⟩ := cpMap_congr ((Category.comp_id _).trans (Category.id_comp _).symm) eβ.symm k₄
    (by rw [Category.assoc, pβ.1.w, Over.w_assoc, Category.id_comp])
  have := Q₀.q_hom
  obtain ⟨w₆, k₆, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ P' _ _ _ Q₀.q.left (by simp) _ hv).2
    (toBase_mul_of_isMonHom Q₀.q _) w₅ k₅
  exact ⟨Q₀, ⟨M₀, w₆, k₆⟩, β, pβ, v, hv.gen⟩

theorem exists_fourth {S S' Z Z' : Scheme.{0}} {t : Z ⟶ S} {t' : Z' ⟶ S'} {f : S' ⟶ S} {b : Z' ⟶ Z}
    (sq : b ≫ t = t' ≫ f) {G : Over S} {G' : Over S'} {H : Over Z} {H' : Over Z'} [GrpObj G] [IsCommMonObj G]
    [GrpObj G'] [IsCommMonObj G'] [GrpObj H] [IsCommMonObj H] [GrpObj H'] [IsCommMonObj H']
    {F : G'.left ⟶ G.left} {c : H.left ⟶ G.left} {c' : H'.left ⟶ G'.left} (pF : IsGrpPullback G' G f F)
    (pc : IsGrpPullback H G t c) (pc' : IsGrpPullback H' G' t' c') {P : CP G} {P' : CP G'} {N : CP H} {N' : CP H'}
    {h₁ w₁ h₂ w₂ h₃ w₃} (k₁ : IsCPMap P' P f F h₁ w₁) (k₂ : IsCPMap N P t c h₂ w₂) (k₃ : IsCPMap N' P' t' c' h₃ w₃) :
    ∃ (E : H'.left ⟶ H.left) (pE : IsGrpPullback H' H b E) (w : _), IsCPMap N' N b E pE.1.w w := by
  have p := pc'.comp pF
  have w : (c' ≫ F) ≫ G.hom = (H'.hom ≫ b) ≫ t := p.1.w.trans (by rw [Category.assoc, sq])
  have e₁ := pc.1.lift_fst _ _ w
  have e₂ := pc.1.lift_snd _ _ w
  have p' := p.congr sq.symm e₁.symm
  have pE := pc.cancel p' e₂
  obtain ⟨w₄, -, k₄⟩ := k₁.exists_comp k₃ p.1.w
  obtain ⟨w₅, k₅⟩ := cpMap_congr sq.symm e₁.symm k₄ p'.1.w
  obtain ⟨w₆, k₆, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ N' _ _ _ _ e₂ _ k₂).2
    (fun Z x y => Over.OverMorphism.ext (pE.2 Z x y _ _ rfl rfl).symm) w₅ k₅
  exact ⟨_, pE, w₆, k₆⟩

theorem exists_trait (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (I : Ideal R) {k : Type}
    [Field k] (a : R ⧸ I ^ (0 + 1) →+* k) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V)
      (b : R ⧸ I ^ (0 + 1) →+* V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)), CDVR V ∧ Function.Injective φ ∧
      RingHom.ker a = RingHom.ker b ∧ spMap b ≫ thick R I 0 = thick V _ 0 ≫ spMap φ := by
  have := RingHom.ker_isPrime a
  obtain ⟨V, _, _, _, φ, hV, hφ, hm⟩ := exists_cdvr R ((RingHom.ker a).comap (Ideal.Quotient.mk _))
  have hm' : (IsLocalRing.maximalIdeal V ^ (0 + 1)).comap φ = (RingHom.ker a).comap (Ideal.Quotient.mk _) := by
    rw [← hm, zero_add, pow_one]
  have le : I ^ (0 + 1) ≤ (IsLocalRing.maximalIdeal V ^ (0 + 1)).comap φ := fun r hr => by
    rw [hm', Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hr]
    exact zero_mem _
  refine ⟨V, _, ‹_›, ‹_›, φ, Ideal.quotientMap (IsLocalRing.maximalIdeal V ^ (0 + 1)) φ le, hV, hφ,
    Ideal.ext fun y => ?_, ?_⟩
  · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← Ideal.mem_comap, ← hm', RingHom.mem_ker, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem]
    rfl
  · rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk]



theorem main : Laws → Laws2 → Laws3 → USt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (T : TowerR I P X) (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (0 + 1)))), RelAmple ((Over.pullback x).obj (T.l 0).Q.B) ((T.l 0).D.M.L.L.pull (pullback.fst _ x)) ∧ KTriv ((Over.pullback x).obj (T.l 0).Q.B) ((T.l 0).D.M.L.L.pull (pullback.fst _ x)) := by
  intro laws _ _ hU R _ _ _ I ⟨⟨hN, _⟩, _, hc, _⟩ G _ _ P hG ⟨w, _, hw, _, _, prim, _⟩ A gen hgen hA X _ _ _ T k _ x
  obtain ⟨a, rfl⟩ : ∃ a : R ⧸ I ^ (0 + 1) →+* k, spMap a = x := ⟨(Spec.preimage x).hom, Spec.map_preimage x⟩
  obtain ⟨V, _, _, _, φ, b, hV, hφ, hab, sq⟩ := exists_trait R I a
  obtain ⟨ψ, sq'⟩ := exists_generic_square φ hφ
  obtain ⟨A', gen', hgen', hA'⟩ := exists_fibre_pull laws sq' P.L.isLB A gen hA
  obtain ⟨P', wP, hP', H⟩ := exists_cp_pull _ _ (spMap φ) G ((Over.pullback (spMap φ)).obj G) _ _
    (toBase_mul_pullback G (spMap φ)) P
  have prim' := prim_pull (spMap φ) prim
  rw [← hP'] at hA' prim'
  obtain ⟨P₀, w₀, H₀⟩ := exists_isLevelCP (IsLocalRing.maximalIdeal V) 0 P'
  obtain ⟨wl, hl⟩ := (T.l 0).lev
  obtain ⟨F, pF, w₃, k₃⟩ := exists_fourth (G := G) (G' := (Over.pullback (spMap φ)).obj G) (H := thickObj R I 0 G)
    (H' := thickObj V (IsLocalRing.maximalIdeal V) 0 ((Over.pullback (spMap φ)).obj G)) (P := P) (P' := P')
    (N := (T.l 0).Pe) (N' := P₀) sq (isGrpPullback_pullback G (spMap φ))
    (isGrpPullback_pullback G (thick R I 0)) (isGrpPullback_pullback _ (thick V (IsLocalRing.maximalIdeal V) 0)) H hl H₀
  obtain ⟨Q₀, D₀, β, pβ, hβ⟩ := exists_desc_pull pF (T.l 0).Q (T.l 0).D k₃
  have hG' : IsSemiAbelian ((Over.pullback (spMap φ)).obj G) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hG.comm; infer_instance
    · have := hG.smooth; change Smooth (pullback.snd G.hom (spMap φ)); infer_instance
    · have := hG.separated; change IsSeparated (pullback.snd G.hom (spMap φ)); infer_instance
    · have := hG.quasiCompact; change QuasiCompact (pullback.snd G.hom (spMap φ)); infer_instance
    · have := hG.geomConnected; change GeometricallyConnected (pullback.snd G.hom (spMap φ)); infer_instance
    · intro Ω _ _ q
      obtain ⟨E⟩ := hG.fibres Ω (q ≫ spMap φ)
      let em := (Functor.mapMonNatIso (Over.pullbackComp q (spMap φ)) ≪≫ Functor.mapMonCompIso).app (Mon.mk G)
      let e : (Over.pullback (q ≫ spMap φ)).obj G ≅ (Over.pullback q).obj ((Over.pullback (spMap φ)).obj G) := (Mon.forget _).mapIso em
      haveI : IsMonHom e.hom := by
        show IsMonHom em.hom.hom
        infer_instance
      letI := E.grpB
      haveI := E.q_hom
      haveI := E.i_hom
      exact ⟨{ X := E.X
               addCommGroup := E.addCommGroup
               free := E.free
               finite := E.finite
               B := E.B
               grpB := E.grpB
               isAbelian := E.isAbelian
               q := e.inv ≫ E.q
               q_hom := inferInstance
               q_flat := by rw [Over.comp_left]; have := E.q_flat; have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv; infer_instance
               q_surjective := by rw [Over.comp_left]; have := E.q_surjective; have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv; infer_instance
               q_quasiCompact := by rw [Over.comp_left]; have := E.q_quasiCompact; have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv; infer_instance
               i := E.i ≫ e.hom
               i_hom := inferInstance
               isKernel := by refine IsPullback.of_iso E.isKernel (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp }⟩
  have ev := GlobalTheory.T.exists_even_cubical_trivialisation_specialFibre laws V hV A' _ hG' gen' hgen' P' ((Over.pullback (spMap φ)).map w) inferInstance
    prim' X Q₀ P₀ ⟨w₀, H₀⟩
  obtain ⟨wA, hwA⟩ := hA'
  have pol := pol_dvr laws hU
    { cdvr := hV, semi := hG', gen := gen', gen_hom := hgen', P := P', wA := wA, wA_gen := hwA, X := X, Q₀ := Q₀,
      P₀ := P₀, lev₀ := ⟨w₀, H₀⟩, even₀ := ev } D₀
  have : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  let _ : Field (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := Ideal.Quotient.field _
  exact pol_of_ker_eq a b hab _ (T.l 0).Q.isAb (T.l 0).D.M.L.isLB Q₀.B pβ D₀.M.L.isLB hβ pol

end GlobalTheory.ClosedPol

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.exists_place_centred_closed_point_detects_units : ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (ϖ : O'), ArcBase O' ϖ → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁), Function.Injective g → g.Finite → ∀ P : Set (ValuationSubring (AlgebraicClosure (FractionRing R₁))), (∀ S ∈ P, ∀ r : R₁, algebraMap (FractionRing R₁) _ (algebraMap R₁ _ r) ∈ S) → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (φ : R₁ →+* V) (gam : FractionRing R₁ →+* FractionRing V), (∀ r, gam (algebraMap R₁ _ r) = algebraMap V _ (φ r)) → ∀ σ : AlgebraicClosure (FractionRing R₁) →+* AlgebraicClosure (FractionRing V), (∀ x, σ (algebraMap (FractionRing R₁) _ x) = algebraMap (FractionRing V) _ (gam x)) → ∃ S ∈ P, ∀ x (y : FractionRing V), σ x = algebraMap (FractionRing V) _ y → (x ∈ S ↔ y ∈ Set.range (algebraMap V (FractionRing V)))) → ∃ S₀ ∈ P, ∀ x, (∀ S ∈ P, x ∈ S) → S₀.valuation x = 1 → ∀ S ∈ P, S.valuation x = 1 := by
  first | exact @GlobalTheory.CentredPlace.exists_place_detecting_units | exact GlobalTheory.CentredPlace.exists_place_detecting_units | (intros; apply GlobalTheory.CentredPlace.exists_place_detecting_units <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.LN.ArcExtends

theorem exists_lift_finite {K : Type} [Field K] {Z X : Scheme.{0}} (π : Z ⟶ X) [IsFinite π] [Surjective π]
    (x : Sp K ⟶ X) : ∃ (L : Type) (_ : Field L) (σ : K →+* L) (z : Sp L ⟶ Z), σ.Finite ∧ z ≫ π = spMap σ ≫ x := by
  have : CompactSpace ↥(pullback π x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd π x)
  obtain ⟨p, -⟩ := (pullback.snd π x).surjective (default : PrimeSpectrum K)
  obtain ⟨q, -, hq⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback π x)) ⟨p, trivial⟩
  have := isClosed_singleton_iff_isClosedImmersion.mp hq
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((pullback π x).fromSpecResidueField q ≫ pullback.snd π x)
  have hf : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  refine ⟨(pullback π x).residueField q, inferInstance, φ.hom,
    (pullback π x).fromSpecResidueField q ≫ pullback.fst π x, (IsFinite.SpecMap_iff φ).1 hf, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← hφ]
  rfl

theorem spMap_jK {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {g : R →+* R'}
    {gam : FractionRing R →+* FractionRing R'} (h : ∀ r, gam (algebraMap R _ r) = algebraMap R' _ (g r)) :
    spMap gam ≫ jK R = jK R' ≫ spMap g := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext h)

theorem finite_fractionRing {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] {g : R →+* R₁}
    {gam : FractionRing R →+* FractionRing R₁} (h : ∀ r, gam (algebraMap R _ r) = algebraMap R₁ _ (g r))
    (hg : g.Finite) : gam.Finite := by
  letI := g.toAlgebra
  letI := gam.toAlgebra
  have : Module.Finite R R₁ := hg
  have : IsScalarTower R (FractionRing R) (FractionRing R₁) := IsScalarTower.of_algebraMap_eq fun r => (h r).symm
  have : FaithfulSMul R R₁ := (faithfulSMul_iff_algebraMap_injective R R₁).2 fun a b e =>
    IsFractionRing.injective R (FractionRing R) (gam.injective (by
      rw [h, h]; exact congrArg _ e))
  show Module.Finite (FractionRing R) (FractionRing R₁)
  exact Module.Finite.of_isLocalization R R₁ (nonZeroDivisors R)

theorem exists_normalisation (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [CharZero R] (hc : IsAdicComplete (IsLocalRing.maximalIdeal R) R) {R₁ : Type} [CommRing R₁] [IsDomain R₁] {g : R →+* R₁}
    {gam : FractionRing R →+* FractionRing R₁} (h : ∀ r, gam (algebraMap R _ r) = algebraMap R₁ _ (g r))
    (hg : g.Finite) {L : Type} [Field L] {σ : FractionRing R₁ →+* L} (hσ : σ.Finite) :
    ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (_ : IsNoetherianRing R₂)
      (_ : IsIntegrallyClosed R₂) (_ : CharZero R₂) (g₂ : R₁ →+* R₂) (f : L →+* FractionRing R₂),
      (∀ r, (f.comp σ) (algebraMap R₁ _ r) = algebraMap R₂ _ (g₂ r)) ∧ (g₂.comp g).IsIntegral := by
  letI := (σ.comp gam).toAlgebra
  letI := ((σ.comp gam).comp (algebraMap R (FractionRing R))).toAlgebra
  have : IsScalarTower R (FractionRing R) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional (FractionRing R) L := hσ.comp (finite_fractionRing h hg)
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.integralClosure_finite_local_of_isAdicComplete R hc L
  have hR : ∀ r, algebraMap R L r = σ (algebraMap R₁ _ (g r)) := fun r => congrArg σ (h r)
  have hi : ∀ r : R₁, (σ.comp (algebraMap R₁ (FractionRing R₁))) r ∈ integralClosure R L := fun r => by
    obtain ⟨p, hp, e⟩ := hg.to_isIntegral r
    refine ⟨p, hp, ?_⟩
    have e' := congrArg (σ.comp (algebraMap R₁ (FractionRing R₁))) e
    rw [Polynomial.hom_eval₂, map_zero] at e'
    rw [← e']
    congr 1
    exact RingHom.ext hR
  have hinj : Function.Injective (algebraMap R L) :=
    (σ.comp gam).injective.comp (IsFractionRing.injective R (FractionRing R))
  have : CharZero L := charZero_of_injective_algebraMap hinj
  let g₂ : R₁ →+* integralClosure R L := (σ.comp (algebraMap R₁ (FractionRing R₁))).codRestrict _ hi
  refine ⟨integralClosure R L, inferInstance, inferInstance, h₂, h₃, h₄, inferInstance, g₂,
    (FractionRing.algEquiv (integralClosure R L) L).symm.toRingHom, fun r => ?_, ?_⟩
  · exact (FractionRing.algEquiv (integralClosure R L) L).symm.commutes (g₂ r)
  · have e : g₂.comp g = algebraMap R (integralClosure R L) := RingHom.ext fun r => Subtype.ext (hR r).symm
    rw [e]
    exact (RingHom.finite_algebraMap.2 h₁).to_isIntegral

theorem arcBase_complete {O' : Type} [CommRing O'] [IsDomain O'] {ϖ : O'} (h : ArcBase O' ϖ) :
    ∃ _ : IsLocalRing O', IsPrincipalIdealRing O' ∧ IsAdicComplete (IsLocalRing.maximalIdeal O') O' := by
  rcases h with ⟨hF, -⟩ | ⟨hD, hi, hc⟩
  · letI := hF.toField
    refine ⟨inferInstance, inferInstance, ?_⟩
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  · refine ⟨inferInstance, inferInstance, ?_⟩
    rwa [hi.maximalIdeal_eq]

theorem polAt_moduli {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {K : Type} [Field K]
    (y : Sp K ⟶ Xo.XF c) : PolAt Y.t (y ≫ Y.j) := by
  have hm : IsGrpPullback Y.oF.t.G Y.t.G Y.j Y.m.φ := Y.m.cart
  have hp := isGrpPullback_pullback Y.t.G (y ≫ Y.j)
  let ψ : ((Over.pullback (y ≫ Y.j)).obj Y.t.G).left ⟶ Y.oF.t.G.left :=
    hm.1.lift (pullback.fst Y.t.G.hom (y ≫ Y.j)) (pullback.snd Y.t.G.hom (y ≫ Y.j) ≫ y)
      (by rw [Category.assoc]; exact pullback.condition)
  have e₁ : ψ ≫ Y.m.φ = pullback.fst Y.t.G.hom (y ≫ Y.j) := hm.1.lift_fst _ _ _
  have hq : IsGrpPullback ((Over.pullback (y ≫ Y.j)).obj Y.t.G) Y.oF.t.G y ψ :=
    IsGrpPullback.cancel hm (hp.congr rfl e₁.symm) (hm.1.lift_snd _ _ _)
  obtain ⟨w, hw, -⟩ := Y.m.lin
  have hI : LBIso (Y.oF.t.PP.L.pull ψ) (Y.t.PP.L.pull (pullback.fst Y.t.G.hom (y ≫ Y.j))) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Y.oF.t.PP.L ψ ψ rfl)
      (chartPullSame Y.t.PP.L _ _ _ ψ fun _ => e₁.symm) ⟨w, hw⟩
  have := Y.oF.proper
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) hq.1 Y.oF.proper,
    amplePt _ K y _ _ ψ hq _ _ Y.oF.t.PP.isLB (pull_isLB Y.t.PP.isLB _) hI.symm Y.oF.ample Y.oF.ktriv⟩

theorem exists_extension : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → ∀ (m : ℕ) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (t : SAB H Z) (_ : SABMap t Y.t π), IsFinite π → Surjective π → Nonempty (AmpFrames t.G t.PP.L (m ^ 2)) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c) (gam : FractionRing (PowerSeries O') →+* FractionRing R₁), (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap R₁ _ (g r)) → g.Finite → IsIntegrallyClosed R₁ → ∀ y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, spMap gam ≫ y = y₁ → y ≫ Y.j ≫ Y.s = jK _ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b → (∃ θ, IsFrame Y.t.G Y.t.PP.L 1 (y₁ ≫ Y.j) (fun _ : Fin 1 => θ)) → (∃ (n : ℕ) (f : Fin n → _), IsFrame Y.t.G Y.t.PP.L (m ^ 2) (y₁ ≫ Y.j) f) → ∃ χ : Sp (PowerSeries O') ⟶ Y.X, jK _ ≫ χ = y ≫ Y.j := by
  intro hL hL₂ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a ϖ hO m Z π t mt hfin hsurj ⟨Am⟩ R₁ _ _ g y₁ gam hgam hg _ y hy hs
    ⟨θ₁, hθ₁⟩ ⟨n, f₁, hf₁⟩
  obtain ⟨_, _, hc⟩ := arcBase_complete hO
  have : CharZero (PowerSeries O') := charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))
  obtain ⟨L, _, σ, z, hσ, hz⟩ := exists_lift_finite π (y₁ ≫ Y.j)
  obtain ⟨R₂, _, _, _, _, _, hch, g₂, f, hf, hint⟩ :=
    exists_normalisation (PowerSeries O') ReciprocityTheory.P1.isAdicComplete_ps hgam hg hσ
  have hx : (spMap f ≫ z) ≫ π = spMap (f.comp σ) ≫ y₁ ≫ Y.j := by
    rw [Category.assoc, hz, spMap_comp, Category.assoc]
  have hP := polAt_moduli Y y₁
  obtain ⟨θ, hθ, bθ⟩ := GlobalTheory.T.sectionFrames_move_to_cover_and_ringExtension hL hL₂ E H _ Z Y.t t π mt R₁ R₂ g₂ _ hf _ _ hx hP 1 1 _ hθ₁
  obtain ⟨ff, hff, bff⟩ := GlobalTheory.T.sectionFrames_move_to_cover_and_ringExtension hL hL₂ E H _ Z Y.t t π mt R₁ R₂ g₂ _ hf _ _ hx hP (m ^ 2) n _ hf₁
  obtain ⟨θ', rfl⟩ : ∃ θ', θ = fun _ : Fin 1 => θ' := ⟨θ 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hab : Set.range (spMap f ≫ z) ⊆ abLocus t.G := by
    rintro _ ⟨p, rfl⟩
    refine (abLocus_pullback abLocusOne Y.t.semi mt.cart.1 _).1 (abLocusOne _ Y.t.G Y.t.semi _ _ hP.1 ?_)
    exact ⟨spMap (f.comp σ) p, (congrArg (fun q => q p) hx).symm⟩
  obtain ⟨e, he, hE⟩ := GlobalTheory.FrameGen.exists_gen_of_frames Z t.G t.PP.L t.PP.isLB (m ^ 2) Am Am.A rfl R₂ _ hab θ' n ff hθ hff bθ bff hch
  have := projProper _ _ _ Y.proj
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (π ≫ Y.s)
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated (π ≫ Y.s)
  have hG : ∀ r, ((f.comp σ).comp gam) (algebraMap (PowerSeries O') _ r) = algebraMap R₂ _ ((g₂.comp g) r) := fun r =>
    (congrArg (f.comp σ) (hgam r)).trans (hf _)
  have hx' : (spMap f ≫ z) ≫ π = spMap ((f.comp σ).comp gam) ≫ y ≫ Y.j := by
    rw [hx, ← hy, spMap_comp gam]
    simp only [Category.assoc]
  obtain ⟨χ₂, hχ₂⟩ := GlobalTheory.ExtLB.exists_extension Z Am.A Am.isLB Am.ample R₂ _ e he fun V _ _ _ hV φ gV hgV => by
    have := hV.1
    obtain ⟨χ, hχ, -⟩ := val_exists (π ≫ Y.s) (spMap gV ≫ spMap f ≫ z)
      (spMap φ ≫ spMap (g₂.comp g) ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b) (by
        rw [Category.assoc, ← Category.assoc (spMap f ≫ z), hx', Category.assoc, Category.assoc, hs,
          ← Category.assoc (spMap _) (jK _), spMap_jK hG, Category.assoc, ← Category.assoc (spMap gV), spMap_jK hgV,
          Category.assoc])
    exact ⟨χ, hχ.symm, hE V hV φ gV hgV χ hχ.symm⟩
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.extension_descends_of_isIntegral _ R₂ _ _ hG hint Y.X (y ≫ Y.j) (χ₂ ≫ π)
    (by rw [← Category.assoc, hχ₂, hx'])
  exact ⟨χ, hχ⟩

end GlobalTheory.LN.ArcExtends
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.integralGauge_values_are_valuationUnits : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (S : ValuationSubring F), (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S) → ∀ (N : NumD F) (ν : NumOf D F N), ν.Integral S → (∀ x y u, S.valuation (N.θ x y u : F) = 1) ∧ (∀ x, S.valuation (N.σ x : F) = 1) ∧ (∀ x, N.th x ∈ S) ∧ ((∀ y, PsiUnitOn D y Set.univ) → ∀ χ, S.valuation (N.ψ χ : F) = 1) := by
  first | exact @GlobalTheory.Ex.UnitVal.integral_values | exact GlobalTheory.Ex.UnitVal.integral_values | (intros; apply GlobalTheory.Ex.UnitVal.integral_values <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.twist_tx_ev_eq_map_arc_root_alt : ∀ (O C : Type) [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (φ : PowerSeries O →+* C), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (t u rm rj : Cˣ) (m j : ℕ), Odd m → 0 < j → (t : C) = φ PowerSeries.X → t ^ j = rm → t ^ (m ^ 2) = rj → rm ^ (m ^ 2) = u → ∀ (N₀ : NumD O) (N : NumD C) (I : NumD.Hom (φ.comp PowerSeries.C) N₀ N) (k : ℕ) (be₀ : LinearMap.BilinForm ℤ N₀.X) (β : N.Form k), (∀ y z, β.be (I.e y) (I.e z) = be₀ y z) → ∀ (p₀ : N₀.QT (m ^ 2)) (p₁ : N.QT (m ^ 2)) (p : (N.twist β u).QT (m ^ 2)), p₁.1.1.toAdd = I.e p₀.1.1.toAdd → I.Rel p₀.1.2 p₁.1.2 → TwRel β u rm p₁ p → (N.twist β u).tx m p = I.lam * φ (N₀.arcTx (((m ^ 2 * j : ℕ) : ℤ) • be₀) m p₀) ∧ ∀ (q₀ : N₀.QT j) (q₁ : N.QT j) (q : (N.twist β u).QT j), q₁.1.1.toAdd = I.e q₀.1.1.toAdd → I.Rel q₀.1.2 q₁.1.2 → TwRel β u rj q₁ q → ∀ s : ℕ, (m : ℤ) ^ 2 * (((m ^ 2 * j : ℕ) : ℤ) * be₀ q₀.1.1.toAdd q₀.1.1.toAdd) ≤ s → (t : C) ^ s * (N.twist β u).ev m p q.1.2 = (I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) * φ (N₀.arcEv (((m ^ 2 * j : ℕ) : ℤ) • be₀) m p₀ q₀ s) := by
  first | exact @GlobalTheory.Ex.RootSum.twist_tx_ev_eq_map_arc_root | exact GlobalTheory.Ex.RootSum.twist_tx_ev_eq_map_arc_root | (intros; apply GlobalTheory.Ex.RootSum.twist_tx_ev_eq_map_arc_root <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.exists_complete_isAlgClosed_cExt' : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (K : Type) [Field K] [Algebra (FractionRing W) K] [Algebra.IsAlgebraic (FractionRing W) K], ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (gam : K →+* C), (∀ x, gam (algebraMap (FractionRing W) K x) = algebraMap (FractionRing W) C x) ∧ CExt W (IsLocalRing.maximalIdeal W) C := by
  first | exact @GlobalTheory.Ex.exists_complete_isAlgClosed_cExt | exact GlobalTheory.Ex.exists_complete_isAlgClosed_cExt | (intros; apply GlobalTheory.Ex.exists_complete_isAlgClosed_cExt <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.qval_add_of_tower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (I : TateIsoQ D D₀ oa F) (N : NumD F) (ν : NumOf D₀ F N) (q : ∀ n : ℕ, D.La → N.QT n), (∀ g, ∃! c, ν.Pt g c) → (∀ g g' g'' c c' c'', ν.Pt g c → ν.Pt g' c' → ν.Pt g'' c'' → (GtPtF.IsAdd g g' g'' ↔ c'' = c * c')) → (∀ k, (∀ p : QkPt D₀ F k, ∃! q, ν.QPt p q) ∧ ∀ (p p' : QkPt D₀ F k) q q', ν.QPt p q → ν.QPt p' q' → (QkPt.Equiv D₀ F p p' ↔ N.QEq q q')) → (∀ n a, ν.QPt (I.ev n a) (q n a)) → (∀ n, 0 < n → ∀ a b, N.QEq (q n a * q n b) (q n (a + b))) ∧ ∀ n m, 0 < n → 0 < m → ∀ a (p : N.QT n), p.1.1 = (q (n * m) a).1.1 → p.1.2 = (q (n * m) a).1.2 ^ m → N.QEq p (q n a) := by
  first | exact @GlobalTheory.NestQVal.qval_add_tower | exact GlobalTheory.NestQVal.qval_add_tower | (intros; apply GlobalTheory.NestQVal.qval_add_tower <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.twist_tx_nsmul_eq_of_odd : ∀ (C : Type) [NormedField C] (N : NumD C) (La : Type) [AddCommGroup La] (q : ∀ n : ℕ, La → N.QT n), (∀ n, 0 < n → ∀ a b, N.QEq (q n a * q n b) (q n (a + b))) → (∀ n m, 0 < n → 0 < m → ∀ a (p : N.QT n), p.1.1 = (q (n * m) a).1.1 → p.1.2 = (q (n * m) a).1.2 ^ m → N.QEq p (q n a)) → ∀ (k : ℕ) (β : N.Form k) (u : Cˣ) (r : ℕ → Cˣ), Roots u r → ∀ (n m : ℕ), Odd n → Odd m → ∀ (x : La) (p'' : (N.twist β u).QT ((n * m) ^ 2)) (p : (N.twist β u).QT (m ^ 2)), TwRel β u (r ((n * m) ^ 2)) (q _ (n • x)) p'' → TwRel β u (r (m ^ 2)) (q _ x) p → (N.twist β u).tx (n * m) p'' = (N.twist β u).tx m p := by
  first | exact @GlobalTheory.Ex.twist_tx_nest | exact GlobalTheory.Ex.twist_tx_nest | (intros; apply GlobalTheory.Ex.twist_tx_nest <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.twist_tx_coset_norm_ge_alt : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] (N : NumD C) (k : ℕ) (β : N.Form k) (u r : Cˣ) (qf : QuadraticMap ℤ N.X ℝ) (n g j : ℕ), n.Prime → Odd n → ‖(n : C)‖ = 1 → 1 ≤ j → ‖(u : C)‖ < 1 → r ^ ((n ^ j) ^ 2) = u → (N.twist β u).Int qf → (∀ y, qf y = -Real.log ‖(u : C)‖ * ((β.be y y : ℝ) / 2)) → N.Tors n g → ∀ (La : Type) [AddCommGroup La] (q : La → N.QT ((n ^ j) ^ 2)), (∀ a : La, n • a = 0 → a = 0) → (∀ a b, N.QEq (q a * q b) (q (a + b))) → (∀ a b, N.QEq (q a) (q b) ↔ ∃ e, a = b + (n ^ j) ^ 2 • e) → (∀ p, ∃ a, N.QEq (q a) p) → ∀ p : La → (N.twist β u).QT ((n ^ j) ^ 2), (∀ x, TwRel β u r (q x) (p x)) → (∃ x, 1 ≤ ‖(N.twist β u).tx (n ^ j) (p x)‖) ∧ ∀ x, ∃ h, ‖(u : C)‖ ^ (β.be (q x).1.1.toAdd (q x).1.1.toAdd).toNat ≤ ‖(N.twist β u).tx (n ^ j) (p (x + n ^ (j - 1) • h))‖ := by
  first | exact @GlobalTheory.twist_tx_coset_norm_ge | exact GlobalTheory.twist_tx_coset_norm_ge | (intros; apply GlobalTheory.twist_tx_coset_norm_ge <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.degenerationValues_int_of_admissibleBase : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (C : Type) [NormedField C] [IsUltrametricDist C] [Algebra (FractionRing R) C], CExt R I C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∃ q, N.Int q := by
  first | exact @GlobalTheory.Ex.IntVal.main | exact GlobalTheory.Ex.IntVal.main | (intros; apply GlobalTheory.Ex.IntVal.main <;> assumption)
end
