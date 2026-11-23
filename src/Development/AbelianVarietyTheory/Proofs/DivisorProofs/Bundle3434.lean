module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3088
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3426
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedMembersClassSumsDeeperLevels
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3432
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle211
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3422
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle905
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3302
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1862
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3427
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem descend_of_emb : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (E : Emb M.π G'), E.Theta P'.L.L → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (P : GlobalTheory.UU.CP G) (β : G'.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback G' G M.π β ∧ LBIso P'.L.L (P.L.L.pull β) := by
  intro R _ _ _ hR M G' _ _ hG' P' E hθ
  have : IsNoetherianRing R := hR.1
  have : IsIntegrallyClosed R := hR.2.2.1
  have hs : Surjective M.π := (Modif.appTop_bijective_surjective R M).2
  obtain ⟨N, fU, l, hl, hf⟩ := GlobalTheory.T.exists_smooth_model_near_closedFibre_embedding R hR M G' hG' E
  have hN : N.Law := GlobalTheory.T.mul_descends_near_closed_fibre_of_embedding R hR M G' hG' E N fU l hl hf
  obtain ⟨G, i1, i2, β, i, hG, hβ, hi, hu⟩ := GlobalTheory.T.semiAbelian_descends_of_descends_near_closedFibre R hR M.S M.π M.proper hs M.integral G' hG' N hN
  obtain ⟨θ, O, hO, hθO⟩ := GlobalTheory.T.exists_open_thetaNonvanishing_descendedGroup R M.S M.π hs G' E N fU l hl hf P'.L.L hθ G β i hβ.1.w hi hu
  obtain ⟨L, hL, hLi⟩ := GlobalTheory.T.cubicalBundle_modification_descends_to_group R hR M G' hG' P' G β hG hβ θ O hO hθO
  obtain ⟨P, rfl⟩ := GlobalTheory.T.exists_cp_descent' R hR M G' hG' P' G β hG hβ L hL hLi
  exact ⟨G, i1, i2, P, β, hG, hβ, hLi⟩

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart

theorem exists_lowBase_of_trait : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ a a', c (a + a') = c a * c a') → ∃ (L : LowBase (zetaAway n) n) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (κ : L.W →+* V') (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)), L.h = PB.g ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b ∧ ∃ (B' : Over (Sp V')) (_ : GrpObj B') (β' : B'.left ⟶ PB.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 PB.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsGrpPullback B' PB.A (spMap f) β' ∧ IsGrpPullback B' L.T.B (spMap κ) β'' ∧ IsSquare β' β₂ ∧ IsSquare β'' β₂' ∧ LBIso ((abelian₂ PB.A PB.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') ∧ ∀ a : Fin L.T.r → ℤ, ∃ x : Sp V' ⟶ B'.left, x ≫ B'.hom = 𝟙 _ ∧ x ≫ β' = spMap f ≫ (c (e a)).left ∧ x ≫ β'' = spMap κ ≫ (L.T.c₀ ((n : ℤ) • a)).left := by
  intro n hn ho V _ _ _ hV hd b PB r c hc
  obtain ⟨F, V₁, _, _, _, f₁, v, hs, hV₁, hd₁, hi₁, hf₁, hl₁, β₁, β₁₂, hp₁, hq₁, hL₁, hc₁⟩ :=
    GlobalTheory.T.exists_fibrePower_point_finite_extension_dvr n hn ho V hV hd b PB r c hc
  obtain ⟨L, V', _, _, _, f, κ, e, hh, hV', hd', hi, hf, hl, hκ, hb, B', _, β', β'', β₂, β₂', hp, hp', hq, hq', hL, hx⟩ :=
    GlobalTheory.T.siegelFibrePower_point_lifts_to_lower_base n hn ho PB.g F r V₁ hV₁ hd₁ (f₁.comp b) v hs
  have es : spMap (f.comp f₁) = spMap f ≫ spMap f₁ := by
    rw [spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hl' : IsLocalHom (f.comp f₁) := RingHom.isLocalHom_comp f f₁
  refine ⟨L, V', inferInstance, inferInstance, inferInstance, f.comp f₁, κ, e, hh, hV', hd', hi.comp hi₁,
    hf.comp hf₁, hl', hκ, ?_, B', inferInstance, β' ≫ β₁, β'', β₂ ≫ β₁₂, β₂', ?_, hp', isSquare_comp hq hq₁, hq', ?_, ?_⟩
  · rw [hb, RingHom.comp_assoc]
  · rw [es]
    exact hp.comp hp₁
  · have h1 : LBIso ((LowChart.siegAt F v _ hs).P.pull β₂) ((abelian₂ PB.A PB.L).pull (β₂ ≫ β₁₂)) :=
      lbIso_pull_comp hL₁ β₂ rfl
    exact LBIso.trans (pull_isLB (LB.isLB_linComb PB.isLB _ _) _) (pull_isLB (LowChart.siegAt F v _ hs).isLB _)
      (pull_isLB (LB.isLB_linComb L.T.M.isLB _ _) _) h1.symm hL
  · intro a
    obtain ⟨x, h1, h2, h3⟩ := hx a
    refine ⟨x, h1, ?_, h3⟩
    rw [← Category.assoc, h2, Category.assoc, hc₁, es, Category.assoc]

end GlobalTheory.TChart
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChart

theorem exists_model_of_charts : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∃ (Y : Model Xo c (RingHom.id c.F)) (ε : Y.X ≅ S), Y.j ≫ ε.hom = j ∧ Y.s = ε.hom ≫ π ≫ zs ∧ ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → Nonempty (SABMap C.t Y.t (ξ ≫ ε.inv)) := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hsi Z zs i OZ N d J S π j _ BD hU hSep hPre
  obtain ⟨oF, ⟨m0⟩⟩ := GlobalTheory.LevelQuotRep.obj_pull_same Xo.univ
    (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
  obtain ⟨G, _, _, e, hGs, hGp, hGab, hGc⟩ := GlobalTheory.T.exists_semiAbelian_descent_of_toricCharts_corrected_sep Xo c φ hpq hfan hsi zs i OZ N d J π j BD hU hSep hPre oF.t m0.toSABMap
  obtain ⟨t, htab, ⟨mt⟩, htc⟩ := GlobalTheory.T.exists_triple_on_descended_group Xo c φ hpq hfan hsi zs i OZ N d J π j BD hU hSep hPre oF.t m0.toSABMap G e hGs hGp hGc
  obtain ⟨⟨-, -, -, -, hiz, -, -⟩, -, -, -, ⟨hNB, hproj, -, hjd, hji, -, -, -⟩, -⟩ := hU
  have eid : spMap (RingHom.id c.F) = 𝟙 _ := by simp [spMap]
  have hid : IsIso (spMap (RingHom.id c.F)) := by rw [eid]; infer_instance
  let g := pullback.fst (π ≫ zs) (spMap (RingHom.id c.F))
  have hg : IsIso g := inferInstance
  let jQ : Xo.XF c ⟶ pullback (π ≫ zs) (spMap (RingHom.id c.F)) := j ≫ inv g
  have hjQ : jQ ≫ g = j := by simp [jQ]
  have hab : abLocus t.G = Set.range j := htab.trans hGab
  let Y : Model Xo c (RingHom.id c.F) :=
    { X := S
      s := π ≫ zs
      normal := (GlobalTheory.isNormalScheme_iff S).1 hNB.1
      proj := hproj
      flat := inferInstance
      jQ := jQ
      jQ_over := by
        rw [← cancel_mono (spMap (RingHom.id c.F)), Category.assoc, ← pullback.condition, ← Category.assoc, hjQ,
          ← Category.assoc, hji, hiz, eid, Category.comp_id]
      jQ_open := inferInstance
      jQ_dense := by
        have hc : (⇑jQ) = (⇑(inv g)) ∘ ⇑j := by
          funext x
          simp [jQ]
        have h1 : DenseRange (⇑(inv g)) := (inv g).surjective.denseRange
        show DenseRange (⇑jQ)
        rw [hc]
        exact h1.comp hjd (inv g).continuous
      t := t
      oF := oF
      m0 := m0
      m := hjQ ▸ mt
      ab_gen := by
        show g ⁻¹' abLocus t.G = Set.range jQ
        rw [hab]
        ext x
        constructor
        · rintro ⟨y, hy⟩
          refine ⟨y, ?_⟩
          have h2 : (inv g) (g x) = x := by
            rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
          rw [← h2, ← hy]
          simp [jQ]
        · rintro ⟨y, rfl⟩
          refine ⟨y, ?_⟩
          rw [← Scheme.Hom.comp_apply, hjQ] }
  refine ⟨Y, Iso.refl S, ?_, ?_, ?_⟩
  · show (jQ ≫ g) ≫ 𝟙 S = j
    rw [hjQ, Category.comp_id]
  · show π ≫ zs = 𝟙 S ≫ π ≫ zs
    rw [Category.id_comp]
  · intro k _ m n C hC ξ hξ
    have := htc C hC ξ hξ
    simpa using this

end GlobalTheory.UChart
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.HomotopyInv

variable {R : Type} [CommRing R]

attribute [local instance] Polynomial.algebra

theorem eqv_baseChange (q : ℕ) (A : Type) [CommRing A] (i : ℤ) (A' : Type) [CommRing A']
    (s : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A))
    (h : Eqv _ (spMap (Polynomial.C : A' →+* Polynomial A')) (tw q i)) :
    Eqv _ (sch.map (pullback.map (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ 𝟙 _) s (𝟙 _) s
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) := by
  first
  | exact @_root_.GlobalTheory.PolynomialPushoutEquivalence.main
  | exact _root_.GlobalTheory.PolynomialPushoutEquivalence.main
  | (apply _root_.GlobalTheory.PolynomialPushoutEquivalence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialPushoutEquivalence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialPushoutEquivalence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialPushoutEquivalence.main ..)

theorem homotopy_invariance_etale : GlobalTheory.EtC.C4 := by
  intro q _ A _ hq i
  have hqΓ : IsUnit ((q : ℕ) : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  refine GlobalTheory.T.etC_b3 q (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)))
    (𝟙 (Spec (CommRingCat.of A))) hqΓ i ?_
  intro A' _ s hA'
  refine eqv_baseChange q A i A' s ?_
  have hq' : IsUnit (q : A') := by simpa using hq.map (Spec.preimage s).hom
  exact GlobalTheory.T.homotopyInvariance_tateTwist_strictlyHenselian q A' hA' hq' i

end GlobalTheory.EtC.HomotopyInv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.uniformisedMembers_classSums_deeper_levels : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (x₀ : X₁.S.Gam) (Φ : VPre (id : ℤ → ℤ) g W (X₁.M.Z.presheaf.stalk z₁)) (lab : Φ.Q → X₁.S.Gam) [IsDomain (X₁.M.Z.presheaf.stalk z₁)], IsGeo X₁ z₁ act x₀ Φ lab → Φ.ClassSums (X₁.S.r * X₁.S.N) := by
  first | exact @GlobalTheory.Poinc.Sep.DeepSums.classSums_deeper | exact GlobalTheory.Poinc.Sep.DeepSums.classSums_deeper | (intros; apply GlobalTheory.Poinc.Sep.DeepSums.classSums_deeper <;> assumption)
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

theorem _root_.GlobalTheory.T.exists_kodairaSpencer_of_logDerivation_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → ∀ D : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ i, D (bdParam k m d i) ∈ Ideal.span {bdParam k m d i}) → ∃ Θ, IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ := by
  first | exact @GlobalTheory.LogKSChart.exists_isKS_of_logDer | exact GlobalTheory.LogKSChart.exists_isKS_of_logDer | (intros; apply GlobalTheory.LogKSChart.exists_isKS_of_logDer <;> assumption)
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

theorem _root_.GlobalTheory.T.isConstAlong_of_kodairaSpencer_zero_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ Θ, IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ → (∀ a b, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (Θ a b) ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∃ c : ℚ, c ≠ 0 ∧ IsConstAlong P.D.toPre (bdParam k m d) gam ρ (fun i => (c : k) * MvPowerSeries.constantCoeff (q i)) := by
  first | exact @GlobalTheory.KSConst.isConstAlong_of_ks_zero | exact GlobalTheory.KSConst.isConstAlong_of_ks_zero | (intros; apply GlobalTheory.KSConst.isConstAlong_of_ks_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.thetaConstantBundle_pow_eight_iso_detHodge_pow_four : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (S : ZH.ThetaSys o Ω) (ρ : S.Real) (M : ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZH.ZHOut ρ M U₀ EE), 1 ≤ S.g → S.Over₀ M U₀ → IsOpen (abLocus Zh.G) → ∀ (δ : LB M.Z) (t : S.Gam → δ.Sec), δ.IsLB → (⨆ a, nonzeroLocus (t a)) = ⊤ → ZM.SecCoord δ t M.pt S.th → LBIso (lbPow δ 8) (lbPow (GlobalTheory.SiegelTor.hodge Zh.G S.g) 4) := by
  first | exact @GlobalTheory.KeyZh.key_zh | exact GlobalTheory.KeyZh.key_zh | (intros; apply GlobalTheory.KeyZh.key_zh <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.deeperLevelValues_eq_classSums_prescribedNorms : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∃ t : (Fin 8 → c.T.D.toPre.X) → X₁.S.HH X₁.M z₁ → PadicAlgCl p, (∀ μ κ, ‖t μ κ‖ ≤ Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ (∀ μ, ∃ κ, ‖t μ κ‖ = Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset (Fin 8 → c.T.D.toPre.X), ∀ S : Finset (Fin 8 → c.T.D.toPre.X), (∀ μ ∈ S, ∀ u, CongMod D.m (μ u) (ν u)) → (∀ μ ∈ S₀, (∀ u, CongMod D.m (μ u) (ν u)) → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (U κ * GSum.part D z₁ z₂ a κ) - ∑ μ ∈ S, t μ κ‖ ≤ δ := by
  first | exact @GlobalTheory.Poinc.GSumCls.main | exact GlobalTheory.Poinc.GSumCls.main | (intros; apply GlobalTheory.Poinc.GSumCls.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.exists_principal_zarhin_object_of_siegKerBy : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)), z.Principal ∧ IsRAct z.A act ∧ Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act ∧ ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z act := by
  first | (exact @GlobalTheory.ZarhinFam.exists_zarhin_object) | (exact GlobalTheory.ZarhinFam.exists_zarhin_object) | (intros; apply GlobalTheory.ZarhinFam.exists_zarhin_object  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlueLie

section Core

variable {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀]



theorem core (hA : IsAbelianScheme A₀) {O : Type} [CommRing O] (act : O → (A₀ ⟶ A₀)) [∀ c, IsMonHom (act c)]
    (ρ' : O →+* Module.End k (HdR A₀)) (hρ' : ∀ c h, ρ' c h = push (dp0 k) (𝟙 _) (act c) h)
    (ω : O) (r : k) {a : ℕ} (χ : Fin a → O → k) (hχ : ∀ i i', i ≠ i' → ∃ c, χ i c ≠ χ i' c)
    {d : ℕ} (hd : 0 < d) (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀))
    (E' : Fin d → Submodule (TrivSqZeroExt k k)
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀))
    (hE : ∀ j e, e ∈ E' j ↔ (fstC A₀ e ∈ Fil A₀ ∧ (sndC A₀ e : HdR A₀) - f j (fstC A₀ e) ∈ Fil A₀))
    (hlift : ∀ j, ∀ x ∈ Fil A₀, ∃ e ∈ E' j, fstC A₀ e = x ∧ (sndC A₀ e : HdR A₀) = f j x)
    (hstab : ∀ j c, ∀ e ∈ E' j,
      push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (act c) e ∈ E' j)
    (hlie : ∀ j e, push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (act ω) e -
        algebraMap k (TrivSqZeroExt k k) r • e ∈ E' j →
      ∃ w : Fin a → Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀,
        (∀ i c, push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (act c) (w i) -
          algebraMap k (TrivSqZeroExt k k) (χ i c) • w i ∈ E' j) ∧ e - ∑ i, w i ∈ E' j)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (he : push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)
        (act ω) e - algebraMap k (TrivSqZeroExt k (Fin d → k)) r • e ∈ GlobalTheory.HTGlue.glueFil A₀ f) :
    ∃ w : Fin a → Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k)))
        (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀,
      (∀ i c, push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)
          (act c) (w i) - algebraMap k (TrivSqZeroExt k (Fin d → k)) (χ i c) • w i ∈ GlobalTheory.HTGlue.glueFil A₀ f) ∧
        e - ∑ i, w i ∈ GlobalTheory.HTGlue.glueFil A₀ f := by
  rw [push_sub_mem_glueFil_iff] at he
  obtain ⟨he1, he2⟩ := he

  choose ee hee1 hee2 using fun j : Fin d ↦ exists_of_coords (V := k) hA (fstC A₀ e)
    (LinearMap.proj j ∘ₗ sndC A₀ e)
  have hEj : ∀ j, push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (act ω) (ee j) -
      algebraMap k (TrivSqZeroExt k k) r • ee j ∈ E' j := fun j ↦ by
    rw [push_sub_mem_iff (f j) (E' j) (hE j), hee1, hee2]
    exact ⟨he1, he2 j⟩
  choose W hW1 hW2 using fun j ↦ hlie j (ee j) (hEj j)
  have hα := fun j i c ↦ (push_sub_mem_iff (f j) (E' j) (hE j) _ _ _).1 (hW1 j i c)
  have hs : ∀ j, fstC A₀ e - ∑ i, fstC A₀ (W j i) ∈ Fil A₀ ∧
      ((LinearMap.proj j ∘ₗ sndC A₀ e : HdR A₀) - ∑ i, (sndC A₀ (W j i) : HdR A₀)) -
        f j (fstC A₀ e - ∑ i, fstC A₀ (W j i)) ∈ Fil A₀ := fun j ↦ by
    have := (sub_sum_mem_iff (f j) (E' j) (hE j) _ _).1 (hW2 j)
    rwa [hee1, hee2] at this

  have hfstab : ∀ j c, ∀ x ∈ Fil A₀,
      push (dp0 k) (𝟙 _) (act c) (f j x) - f j (push (dp0 k) (𝟙 _) (act c) x) ∈ Fil A₀ := by
    intro j c x hx
    obtain ⟨e1, he1E, h1, h2⟩ := hlift j x hx
    have := ((push_mem_iff (f j) (E' j) (hE j) (act c) e1).1 (hstab j c e1 he1E)).2
    rwa [h1, h2] at this

  let j₀ : Fin d := ⟨0, hd⟩
  have hFst : ∀ c, ∀ x ∈ Fil A₀, ρ' c x ∈ Fil A₀ := fun c x hx ↦ by rw [hρ']; exact push_mem_Fil _ hx
  have hglue : ∀ j i, fstC A₀ (W j i) - fstC A₀ (W j₀ i) ∈ Fil A₀ := fun j ↦
    GlobalTheory.T.components_mem_of_sum_mem_distinct_eigencharacters_mod k (HdR A₀) O ρ' (Fil A₀) hFst a χ hχ (fun i ↦ fstC A₀ (W j i) - fstC A₀ (W j₀ i))
      (fun i c ↦ by
        rw [hρ', map_sub, smul_sub, sub_sub_sub_comm]; exact sub_mem (hα j i c).1 (hα j₀ i c).1)
      (by
        rw [Finset.sum_sub_distrib]
        have := sub_mem (hs j₀).1 (hs j).1
        convert this using 1
        abel)

  choose w hw1 hw2 using fun i ↦ exists_of_coords (V := Fin d → k) hA (fstC A₀ (W j₀ i))
    (LinearMap.pi fun j ↦ (sndC A₀ (W j i) : HdR A₀) + f j (fstC A₀ (W j₀ i) - fstC A₀ (W j i)))
  refine ⟨w, fun i c ↦ ?_, ?_⟩
  · rw [push_sub_mem_glueFil_iff, hw1, hw2]
    refine ⟨(hα j₀ i c).1, fun j ↦ ?_⟩
    rw [LinearMap.proj_pi]
    have hδ : fstC A₀ (W j₀ i) - fstC A₀ (W j i) ∈ Fil A₀ := by
      have := neg_mem (hglue j i); rwa [neg_sub] at this
    have := add_mem (hα j i c).2 (hfstab j c _ hδ)
    convert this using 1
    simp only [map_add (f := _), map_sub, map_smul, smul_add, smul_sub]
    abel
  · rw [sub_sum_mem_glueFil_iff]
    simp only [hw1, hw2, LinearMap.proj_pi]
    refine ⟨(hs j₀).1, fun j ↦ ?_⟩
    convert (hs j).2 using 1

    simp only [Finset.sum_add_distrib, map_sub, map_sum, Finset.sum_sub_distrib]
    abel

end Core



theorem lie_glueFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ), 0 < d → ∀ (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ (E' : Fin d → Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A)), (∀ j, ∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A), IsCompl (E' j) M) → (∀ j, ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ E' j, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl o₀.A).Corr e y) → (∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ E' j, ∀ c, e ((GlobalTheory.FODef.constMorV k k o₀.A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f j x c)) → (∀ j (c : D.O), ∀ e ∈ E' j, (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (c)) (e)) ∈ E' j) → (∀ j, ∀ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (e)) - ((algebraMap k (TrivSqZeroExt k k)).comp tk) b.ρ • e ∈ E' j → ∃ w : Fin D.a → Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - ((algebraMap k (TrivSqZeroExt k k)).comp tk) (b.t i c) • w i ∈ E' j) ∧ e - ∑ i, w i ∈ E' j) → ∀ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (e)) - ((algebraMap k (TrivSqZeroExt k (Fin d → k))).comp tk) b.ρ • e ∈ GlobalTheory.HTGlue.glueFil o₀.A f → ∃ w : Fin D.a → Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - ((algebraMap k (TrivSqZeroExt k (Fin d → k))).comp tk) (b.t i c) • w i ∈ GlobalTheory.HTGlue.glueFil o₀.A f) ∧ e - ∑ i, w i ∈ GlobalTheory.HTGlue.glueFil o₀.A f := by
  intro p _ D R _ b N k _ _ tk s o₀ _ d hd f E' hcompl hred hlift hstab hlie e he
  haveI hact : ∀ c : 𝓞 D.F, IsMonHom (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) := fun c ↦ o₀.act.hom _
  have L1j := fun j ↦ GlobalTheory.T.dualNumber_hodge_summand_eq_graph_coordinates k o₀.A o₀.ab (f j) (E' j) (hcompl j) (hred j) (hlift j)
  have hχ : ∀ i i', i ≠ i' → ∃ c : 𝓞 D.F, tk (b.t i c) ≠ tk (b.t i' c) := by
    intro i i' hii'
    by_contra hcon
    push_neg at hcon
    have hle : Ideal.span (Set.range fun x ↦ b.t i x - b.t i' x) ≤ RingHom.ker tk := by
      rw [Ideal.span_le]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, hcon x, sub_self]
    have h1 : (1 : R) ∈ RingHom.ker tk := hle (b.comax i i' hii' ▸ Submodule.mem_top)
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have hlift' : ∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ E' j, fstC o₀.A e = x ∧ (sndC o₀.A e : HdR o₀.A) = f j x := by
    intro j x hx
    obtain ⟨e1, he1, h⟩ := hlift j x hx
    refine ⟨e1, he1, ?_, ?_⟩ <;> ext c
    · rw [fstC_apply, h c, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    · rw [sndC_apply, h c, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  exact core o₀.ab (fun c : 𝓞 D.F ↦ o₀.act.act (algebraMap (𝓞 D.F) D.O c))
    ((GlobalTheory.HTCount.crysAct o₀).comp (algebraMap (𝓞 D.F) D.O)) (fun _ _ ↦ rfl) D.ω (tk b.ρ)
    (fun i c ↦ tk (b.t i c)) hχ hd f E' L1j hlift' (fun j c e he ↦ hstab j _ e he) hlie e he

end GlobalTheory.HTGlueLie
end
end
