module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThickIsoOfIsPullDeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTermBasis
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle059
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle104
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameVal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pmaps_rig_of_thick_compat {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {I : Ideal R} (hI : I ≠ ⊤) {D D' : DegData R I} {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    (U : UnifPre I D A G) (U' : UnifPre I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre)
    (j : ∀ e : ℕ, thickObj R I e G' ⟶ thickObj R I e G) (hj : ∀ e, IsMonHom (j e))
    {F : G'.left ⟶ G.left} (he : eSec G' ≫ F = eSec G)
    (wL : LB.Iso U'.LG.L (U.LG.L.pull F)) (hw : wL.IsGen)
    (H : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι)
      (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈
        D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
      (fstG I e G).left ((j e).left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' →
      Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') =
        Geo.Tor.gw (U.w e) (r ≫ (j e).left) z jM (fun _ => jL) *
          Geo.Tor.gw wL (r ≫ (fstG I e G').left) z jL jL') :
    PMaps wL (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) U'.LG.rig U.LG.rig (𝟙 _) := by
  refine AbelianPartIso.pmaps_of_thickenings hI U.LG.isLB U'.LG.isLB wL hw _ _ he _ U'.LG.rigGen _ U.LG.rigGen
    fun e z p q hp hq => ?_
  have hs := Geo.Tor.specOf_id R
  have hB : eSec D'.toPre.P.A ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
      eSec D.toPre.P.A := hD.he.trans ((congrArg (· ≫ _) hs).trans (Category.id_comp _))
  have hje : eSec (thickObj R I e G') ≫ (j e).left = eSec (thickObj R I e G) :=
    congrArg Over.Hom.left (hj e).one_hom
  obtain ⟨m, hm⟩ := Geo.Tor.exists_chart D.toPre.P.isLB ((UnitValue.thU R I e ≫ eSec D.toPre.P.A) z)
  obtain ⟨m', hm'⟩ := Geo.Tor.exists_chart D'.toPre.P.isLB ((UnitValue.thU R I e ≫ eSec D'.toPre.P.A) z)
  have hm₂ : (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)))
      ((UnitValue.thU R I e ≫ eSec D'.toPre.P.A) z) ∈ D.toPre.P.L.U m :=
    (congrArg (fun g => (UnitValue.thU R I e ≫ g) z ∈ D.toPre.P.L.U m) hB).mpr hm
  have e₁ := UnitValue.wv_rig U e z m p hm hp
  have e₂ := UnitValue.wv_rig U' e z m' q hm' hq
  have e₃ := (Geo.Tor.maps_iff hD.w _ (fun _ => eSec D.toPre.P.A) _ D'.toPre.rig D.toPre.rig
    (specOf (RingHom.id R)) _ (rigPull_le _ _ hD.he D.toPre.P.L) (fun _ => rfl)).1 hD.w_rig _
    (UnitValue.thU R I e) z (fun _ => m) (fun _ => m') (fun _ => hm₂) (fun _ => hm')
  have e₄ := H e _ (eSec (thickObj R I e G')) z m m' p q
    ((congrArg (fun g => (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) (g z) ∈
      D.toPre.P.L.U m) (UnitValue.eSec_pGl U' e)).mpr hm₂)
    ((congrArg (fun g => g z ∈ D'.toPre.P.L.U m') (UnitValue.eSec_pGl U' e)).mpr hm')
    ((congrArg (fun g => g z ∈ U.LG.L.U p)
      (((congrArg (· ≫ (fstG I e G).left) hje)).trans (UnitValue.eSec_fGl (G := G) e))).mpr hp)
    ((congrArg (fun g => g z ∈ U'.LG.L.U q) (UnitValue.eSec_fGl (G := G') e)).mpr hq)
  have ht : UnitValue.thU R I e ≫ specOf (RingHom.id R) = UnitValue.thU R I e :=
    (congrArg (_ ≫ ·) hs).trans (Category.comp_id _)
  rw [UnitValue.eSec_pGl U' e, UnitValue.eSec_fGl (G := G') e, hje] at e₄
  rw [ht, Fintype.prod_unique, zpow_one] at e₃
  exact mul_left_cancel (e₁.trans (e₃.trans ((congrArg _ e₂.symm).trans ((mul_assoc _ _ _).symm.trans
    ((congrArg (· * _) e₄).trans (mul_assoc _ _ _))))))

theorem exists_iso_isPullUnif_of_isPullDeg : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre), ∃ (ψ : G' ≅ G) (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G), IsMonHom ψ.hom ∧ IsMonHom bc.hom ∧ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.hom.left ∧ IsPullUnif (RingHom.id R) hD bc U U' := by
  intro hL hL2 R _ _ _ I hR hI D D' A A' G G' _ _ _ _ hG hG' U U' hD
  obtain ⟨j, hj⟩ := exists_thick_iso_of_isPullDeg hL.globalFns R I hR hI D D' A A' G G' hG hG' U U' hD
  obtain ⟨ΦK, wK, hK⟩ := GlobalTheory.T.exists_genericFibreIso_of_compatible_thickenings hL hL2 R I hR hI D D' A A' G G' hG hG' U U' hD j hj
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.generic_iso_extends_semiAbelian_dvr_inducing_formal hL hL2 R I hR hI D D' A A' G G' hG hG' U U' hD j hj ΦK wK hK
  obtain ⟨wL, hwL, H⟩ := GlobalTheory.T.exists_bundleIso_extending_generic_alt hL hL2 R I hR hI D D' A A' G G' hG hG' U U' hD j hj ΦK wK hK ψ hψ
  obtain ⟨hm, -, hf⟩ := hψ
  have hs := Geo.Tor.specOf_id R
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso ((isGrpPullback_of_iso ψ).congr hs.symm rfl)
    (isGrpPullback_pullback G (specOf (RingHom.id R)))
  have hbc' : bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.hom.left := hbc
  have he₀ : eSec G' ≫ ψ.hom.left = eSec G := congrArg Over.Hom.left hm.one_hom
  have he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) =
      specOf (RingHom.id R) ≫ eSec G :=
    (congrArg (_ ≫ ·) hbc').trans (he₀.trans ((congrArg (· ≫ _) hs).trans (Category.id_comp _)).symm)
  have hI' : I ≠ ⊤ := hI ▸ (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hr := pmaps_rig_of_thick_compat hI' U.toUnifPre U'.toUnifPre hD (fun e => (j e).hom) (fun e => (hj e).1)
    he₀ wL hwL H
  refine ⟨ψ, bc, hm, mbc, hbc', (isPullUnif_iff_stalks R R I I _ D D' hD A A' G G' bc U U').2
    ⟨pullCongr hbc'.symm wL, (isGen_iff _).2 (pgen_pullCongr _ ((isGen_iff _).1 hwL)), he, ?_, fun e =>
      ⟨(j e).hom.left, (hf e).symm.trans (congrArg (_ ≫ ·) hbc'.symm), (hj e).2.2,
        fun Z r z jM jM' jL jL' h₁ h₂ h₃ h₄ => ?_⟩⟩⟩
  · refine (Geo.Tor.maps_iff _ _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (specOf (RingHom.id R)) _
      (rigPull_le _ _ he U.LG.L) (fun _ => rfl)).2 (pmaps_pullCongr _ ?_)
    exact (congrArg (PMaps wL (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) U'.LG.rig U.LG.rig)
      hs).mpr hr
  · rw [gw_pullCongr]
    refine H e Z r z jM jM' jL jL' h₁ h₂ ?_ h₄
    rw [hbc'] at h₃
    exact (congrArg (fun g => g (r z) ∈ U.LG.L.U jL) (hf e)).mp h₃

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace UnifBaseChange

theorem exists_secScal_one {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Z ⟶ Y) (φ' : K → (Z ⟶ X)) (hφ : φ' = fun k => h ≫ φ k) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ t : LB.Sec (LB.LinComb L φ' ε), GeneratorPullback.SecScal L φ' ε t φ ε s h 1 := by
  subst hφ
  refine ⟨DVR.pullSec L φ ε s h, fun j₁ j₂ hco => ?_⟩
  obtain rfl : j₁ = j₂ := funext fun k => hco (Sum.inl k) (Sum.inr k) rfl
  rw [resTop, map_one, _root_.one_mul]
  exact (DVR.rs_rs _ _ _).symm

theorem scal_one {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) :
    scal p (1 : R) = 1 := by
  unfold scal
  rw [map_one, map_one]

end UnifBaseChange


open UnifBaseChange ExpandsLinear in
theorem unifBaseChange :
    PolBaseChangeSt → GlobalFnsSt → SecBaseChangeSt → DVR.TwistBaseChangeStatement → UnifBaseChangeSt := by
  intro hP hG hS hT R R' _ _ _ _ I I' hR hR' φ hI D A G _ _ hsa U W hW hη G' _ _ bc hbc A' hg eA heA hwA
    L' wL he hwL hrig
  obtain ⟨D', hD, -, hgD⟩ := exists_degData_isPullDeg hP hG R R' I I' φ hI D W hW hη
  obtain ⟨U', wL', hL, hgen, hw, hlev⟩ := exists_unifPre_pull hG R R' I I' φ D D' hD A A' G G' bc hI hbc
    U.toUnifPre eA heA hwA L' wL he hwL hrig
  subst hL
  obtain rfl := eq_of_heq hw
  haveI := hsa.geomConnected
  haveI := hsa.quasiCompact
  haveI : GeometricallyConnected G'.hom := by
    rw [← Over.w bc.hom]
    have : IsIso bc.hom.left := ((Over.forget _).mapIso bc).isIso_hom
    have : GeometricallyConnected ((Over.pullback (specOf φ)).obj G).hom :=
      inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (specOf φ)))
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso (fst := bc.hom.left) (f := ((Over.pullback (specOf φ)).obj G).hom) (g := 𝟙 _)
        ⟨(Category.comp_id _).symm⟩) this
  haveI := hR.1
  haveI := hR'.1
  have hexp : ∀ k : ℕ, 1 ≤ k → U'.ExpBij k := by
    intro k hk
    obtain ⟨-, hd⟩ := FamDim.finrank_fam hG hP hT R D.toPre D.tau_bimult (psiOnExists R I hR D) (FractionRing R) k hk
    obtain ⟨hfin, hd'⟩ := FamDim.finrank_fam hG hP hT R' D'.toPre D'.tau_bimult (psiOnExists R' I' hR' D')
      (FractionRing R') k hk
    have hdA := finrank_fam_of_expBij hS R I hR D A G U.toUnifPre k hk (U.expand k hk)
    have hrk : D'.toPre.rank = D.toPre.rank := hD.xe.toIntLinearEquiv.finrank_eq
    refine ExpansionCriterion.expBij_of_onto hS R' I' hR' D' A' G' U' k hk hfin (by rw [hd', hrk, hgD, ← hd, hdA, hg]) fun F₀ => ?_
    obtain ⟨n, F, f, F', f', hF, hspan⟩ := T.exists_integral_families_span_pullDegeneration hP hG hT R R' I hR φ D D'.toPre hD k hk
    have hb : ∀ i, ∃ b : U'.SecK k, U'.Expands k b (F' i) := by
      intro i
      obtain ⟨σ, hσ⟩ := exists_sec_expandsAt_of_integral_family R I hR D A G U.toUnifPre k (fun F => ((U.expand k hk).2 F).exists) (F i) (f i)
        (hF i).1
      obtain ⟨σ', hσ', -⟩ := SecPull.existsUnique_secPull _ _ _ _ U.LG.L U'.LG.L _ U.LG.isLB U'.LG.isLB wL' hwL
        (Fin 1) (fun _ => 𝟙 G'.left) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))
        (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (fun _ => by rw [Category.id_comp, Category.comp_id]) σ
      obtain ⟨b, hb⟩ := exists_secScal_one U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => (k : ℤ))
        (pullback.fst G'.hom (jK R')) (fun _ => pullback.fst G'.hom (jK R'))
        (funext fun _ => (Category.comp_id _).symm) σ'
      refine ⟨b, 1, one_ne_zero, σ', f' i, by rw [scal_one]; exact hb,
        fun α => by rw [scal_one]; exact (hF i).2.1 α, fun e => ?_⟩
      obtain ⟨h, hh⟩ := hlev e
      exact expandsAt_transport R R' I I' D D' A A' G G' U.toUnifPre U' _ hD.w hD.xe _ wL' hD.w_gen hwL
        (ExpGTrans.famφB_pull hD) e e k h ⟨hh.1, hh.2⟩ σ σ' (f i) (f' i) hσ' (hF i).2.2 (hσ e)
    choose b hb using hb
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hspan ▸ Submodule.mem_top : F₀ ∈ _)
    exact ⟨secComb (fun i => scal (pullback.snd G'.hom (jK R')) (c i)) b,
      expands_linear R' I' hR' D' A' G' U' k n b F' c _ hb fun _ => rfl⟩
  exact ⟨D', hD, ⟨U', hexp⟩, rfl, hgen,
    (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U ⟨U', hexp⟩).2 ⟨wL', hwL, he, hrig, hlev⟩⟩

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.SmallZero
open CoefBasic SmallPoint

theorem le_of_sumV_sub {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {f g : Ix → F}
    (h : SumV v (fun i => f i - g i) 0) (i₀ i₁ : Ix) (q : ℚ) (hf : ∀ i, i ≠ i₀ → (q : WithTop ℚ) ≤ v (f i))
    (hg : ∀ i, i ≠ i₁ → (q : WithTop ℚ) ≤ v (g i)) : (q : WithTop ℚ) ≤ v (f i₀ - g i₁) := by
  classical
  obtain ⟨S, hS⟩ := h q
  have h₁ := hS (insert i₀ (insert i₁ S)) ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _))
  have m₀ : i₀ ∈ insert i₀ (insert i₁ S) := Finset.mem_insert_self _ _
  have m₁ : i₁ ∈ insert i₀ (insert i₁ S) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have h₂ : (q : WithTop ℚ) ≤ v (∑ i ∈ (insert i₀ (insert i₁ S)).erase i₀, f i) :=
    v.map_le_sum fun i hi => hf i (Finset.ne_of_mem_erase hi)
  have h₃ : (q : WithTop ℚ) ≤ v (∑ i ∈ (insert i₀ (insert i₁ S)).erase i₁, g i) :=
    v.map_le_sum fun i hi => hg i (Finset.ne_of_mem_erase hi)
  rw [Finset.sum_sub_distrib, ← Finset.add_sum_erase _ f m₀, ← Finset.add_sum_erase _ g m₁, zero_sub,
    v.map_neg] at h₁
  have := v.map_le_add (v.map_le_sub h₁ h₂) h₃
  convert this using 2
  ring

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ (k : ℕ), 1 ≤ k → ∀ (d o : GtPtF D.toPre F) (l : D.toPre.X → ℚ), o.IsZero → GtV hϖ hv d l → (∀ m, |l m| ≤ Q m) → (∀ (n j : ℕ), 1 ≤ n → j = k * n → ∀ (w₁ : Frm D.toPre F j o.b), FrmOne w₁ → ∃ w : Frm D.toPre F j d.b, w.IsGen ∧ ∀ S₁ S₂ : Fam D.toPre F j, ¬ SumV v (coef S₂ o w₁) 0 → ∀ α, SumV v (fun χ => coef S₁ d w χ * coef S₂ o w₁ (α - χ) - coef S₂ d w χ * coef S₁ o w₁ (α - χ)) 0) → d.IsZero := by
  intro hL hT hVR hTW hUU V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv k hk d o l ho hl hlQ H
  have hdb : d.b = 1 := SmallPoint.main hL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv k hk d o l ho hl hlQ H
  have I := GlobalTheory.UT.CoefVal.main hL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv
  have I' := GlobalTheory.UT.CoefUnit.exists_fam_coef_val hL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have K := GlobalTheory.UT.gt_onto_divisible_kernel hL V (maximalIdeal V) hA D F
  have hob : o.b = 1 := ((isZero_iff o).1 ho).1
  obtain ⟨l', hl', -⟩ := (I d).1
  have hll : ∀ χ, l χ = l' χ := by
    obtain ⟨w, hw⟩ := (coef_basic V D.toPre F 4 d).1
    obtain ⟨ω, hω, -⟩ := (I d).2.1 4 w hw
    have le : ∀ l₁ l₂, GtV hϖ hv d l₁ → GtV hϖ hv d l₂ → ∀ χ, l₁ χ ≤ l₂ χ := fun l₁ l₂ h₁ h₂ χ => by
      obtain ⟨s, hs, -, e⟩ := I' 4 le_rfl d w l₂ ω hw h₂ hω χ
      have := ((I d).2.2.2.2.2.2 4 (by omega) w s hw).2 l₁ ω 0 h₁ hω hs χ
      rw [e, WithTop.coe_le_coe] at this
      linarith
    exact fun χ => le_antisymm (le _ _ hl hl' χ) (le _ _ hl' hl χ)
  have hlow : ∀ m, -(Q m : ℚ) ≤ l' m := fun m => hll m ▸ (abs_le.1 (hlQ m)).1
  obtain ⟨t, ht, -⟩ := K.2.2.2.1 d hdb
  have hto : IsTor 1 o := ⟨hob, fun χ z J hJ => by
    rw [((isZero_iff o).1 ho).2 χ z J hJ, MonoidHom.one_apply, Units.val_one, Units.val_one, cst_eq, map_one]⟩
  have hadd : o.IsAdd d d := (K.2.2.2.2 1 t o d d hto ht).2 (by rwa [_root_.one_mul])
  have hQ0 : ∀ m, (0 : ℚ) ≤ Q m := fun m => (abs_nonneg _).trans (hlQ m)
  have A : ∀ (κ₀ : D.toPre.X) (n j : ℕ), 4 ≤ n → j = k * n →
      (((j : ℚ) - 1 - 2 * Q κ₀ : ℚ) : WithTop ℚ) ≤ v ((t (Multiplicative.ofAdd κ₀)).val - 1) := by
    intro κ₀ n j hn hj
    have hj4 : 4 ≤ j := hj ▸ le_trans hn (Nat.le_mul_of_pos_left _ hk)
    have hj1 : 1 ≤ j := by omega
    have hj0 : (0 : ℚ) < j := by exact_mod_cast hj1
    have hj1' : (1 : ℚ) ≤ j := by exact_mod_cast hj1
    obtain ⟨w₁, hw₁⟩ := (coef_basic V D.toPre F j o).2.1 hob
    obtain ⟨w', hw'⟩ := (coef_basic V D.toPre F j d).2.1 hdb
    obtain ⟨w, hw, Hw⟩ := H n j (by omega) hj w₁ hw₁
    obtain ⟨c, hc0, vc, ec⟩ := ((coef_basic V D.toPre F j d).2.2 w' hw'.1).2.2.1 w hw
    have et := ((coef_basic V D.toPre F j o).2.2 w₁ hw₁.1).2.2.2 t d d w' ht hadd
      (fun z J hJ => (hw'.2 z J hJ).trans (hw₁.2 z J hJ).symm)
    obtain ⟨ω, hcω⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hc0)
    have hω : GenV hϖ hv w ω := by
      obtain ⟨φ₀, hφ, t₀, ht₀, x, hx, e⟩ := (I d).2.2.1 j w' hw' hdb
      refine ⟨φ₀, hφ, t₀, ht₀, c * x, by rw [v.map_mul, hx, ← hcω]; simp, fun z J hJ => ?_⟩
      rw [vc z J hJ, e z J hJ, cst_eq, cst_eq, cst_eq, map_mul, _root_.mul_assoc]
    have hω₁ := (I o).2.2.1 j w₁ hw₁ hob
    obtain ⟨S₁, n₁, -, e₁⟩ := I' j hj4 o w₁ 0 0 hw₁.1 (gtV_zero ho) hω₁ κ₀
    obtain ⟨S₂, n₂, z₂, e₂⟩ := I' j hj4 o w₁ 0 0 hw₁.1 (gtV_zero ho) hω₁ 0
    rw [Pi.zero_apply, add_zero, add_zero] at e₁ e₂
    rw [QForm.Q_zero hϖ D hQ, Int.cast_zero, zero_div] at e₂
    have hQj : ∀ mu, (Q (j • mu) : ℚ) / j = j * Q mu := fun mu => by
      rw [Q_nsmul hϖ hQ]; push_cast; field_simp
    have hQs : ∀ mu, (Q κ₀ : ℚ) / j + j * Q mu - Q mu - Q κ₀ ≤ (Q (κ₀ + j • mu) : ℚ) / j := fun mu => by
      have h0 := hQ0 (mu + κ₀)
      have : (Q (κ₀ + j • mu) : ℚ) / j = Q κ₀ / j + j * Q mu + (Q (mu + κ₀) - Q mu - Q κ₀) := by
        rw [q_shift hϖ hQ, QForm.bOf]; push_cast; field_simp; ring
      linarith
    have bo : ∀ S : Fam D.toPre F j, NuGe D Q F v j S 0 → ∀ χ,
        (((Q χ : ℚ) / j : ℚ) : WithTop ℚ) ≤ v (coef S o w₁ χ) := fun S hS χ => by
      have := ((I o).2.2.2.2.2.2 j hj1 w₁ S hw₁.1).2 0 0 0 (gtV_zero ho) hω₁ hS χ
      rwa [Pi.zero_apply, add_zero, add_zero, zero_add] at this
    have bd : ∀ S : Fam D.toPre F j, NuGe D Q F v j S 0 → ∀ χ,
        (((Q χ : ℚ) / j + l' χ + ω : ℚ) : WithTop ℚ) ≤ v (coef S d w χ) := fun S hS χ => by
      have := ((I d).2.2.2.2.2.2 j hj1 w S hw).2 l' ω 0 hl' hω hS χ
      rwa [zero_add] at this
    have hQ1 : ∀ mu : D.toPre.X, mu ≠ 0 → (1 : ℚ) ≤ Q mu := fun mu h => by
      exact_mod_cast QForm.Q_pos hϖ D hQ h
    have z₂' : ∀ (g : GtPtF D.toPre F) (u : Frm D.toPre F j g.b) (χ), (¬ ∃ mu, χ = j • mu) → coef S₂ g u χ = 0 :=
      fun g u χ e => coef_zero S₂ g u (z₂ χ fun mu h => e ⟨mu, by rw [h, zero_add]⟩)
    have hne : ¬ SumV v (coef S₂ o w₁) 0 := fun h => by
      have := le_of_sumV h 0 1 fun χ hχ => by
        by_cases e : ∃ mu, χ = j • mu
        · obtain ⟨mu, rfl⟩ := e
          refine le_trans (WithTop.coe_le_coe.2 ?_) (bo S₂ n₂ _)
          have := hQ1 mu fun e => hχ (by rw [e, smul_zero])
          rw [hQj]
          nlinarith
        · rw [z₂' o w₁ χ e, v.map_zero]; exact le_top
      rw [e₂, WithTop.coe_le_coe] at this
      linarith
    have key := le_of_sumV_sub (Hw S₁ S₂ hne κ₀) κ₀ 0 (ω + (Q κ₀ : ℚ) / j + ((j : ℚ) - 1 - 2 * Q κ₀))
      (fun χ hχ => by
        by_cases e : ∃ mu, κ₀ - χ = j • mu
        · obtain ⟨mu, e⟩ := e
          obtain rfl : χ = κ₀ + j • (-mu) := by rw [smul_neg, ← e]; abel
          have h1 := hQ1 (-mu) fun e => hχ (by rw [e, smul_zero, add_zero])
          rw [v.map_mul, e]
          refine le_trans ?_ (add_le_add (bd S₁ n₁ _) (bo S₂ n₂ _))
          rw [← WithTop.coe_add, WithTop.coe_le_coe, hQj, ← QForm.Q_neg hϖ D hQ mu, map_add (f := _), map_nsmul, nsmul_eq_mul]
          have h2 := hQs (-mu)
          have h3 := hlow κ₀
          have h4 := mul_le_mul_of_nonneg_left (hlow (-mu)) hj0.le
          have h5 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hj1')
          nlinarith
        · rw [z₂' o w₁ _ e, MulZeroClass.mul_zero, v.map_zero]; exact le_top)
      (fun χ hχ => by
        by_cases e : ∃ mu, χ = j • mu
        · obtain ⟨mu, rfl⟩ := e
          have h1 := hQ1 mu fun e => hχ (by rw [e, smul_zero])
          rw [v.map_mul, sub_eq_add_neg κ₀, ← smul_neg]
          refine le_trans ?_ (add_le_add (bd S₂ n₂ _) (bo S₁ n₁ _))
          rw [← WithTop.coe_add, WithTop.coe_le_coe, hQj, map_nsmul, nsmul_eq_mul]
          have h2 := hQs (-mu)
          rw [QForm.Q_neg hϖ D hQ mu] at h2
          have h3 := hQ0 κ₀
          have h4 := mul_le_mul_of_nonneg_left (hlow mu) hj0.le
          have h5 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hj1')
          nlinarith
        · rw [z₂' d w _ e, MulZeroClass.zero_mul, v.map_zero]; exact le_top)
    rw [sub_self, sub_zero, ec, ec, et, et, ofAdd_zero, map_one, Units.val_one,
      show c * ((t (Multiplicative.ofAdd κ₀)).val * coef S₁ o w₁ κ₀) * coef S₂ o w₁ 0 -
        c * (1 * coef S₂ o w₁ 0) * coef S₁ o w₁ κ₀ =
        c * coef S₁ o w₁ κ₀ * coef S₂ o w₁ 0 * ((t (Multiplicative.ofAdd κ₀)).val - 1) by ring,
      v.map_mul, v.map_mul, v.map_mul, ← hcω, e₁, e₂, ← WithTop.coe_add, ← WithTop.coe_add, add_zero,
      WithTop.coe_add (ω + (Q κ₀ : ℚ) / j)] at key
    exact (WithTop.add_le_add_iff_left WithTop.coe_ne_top).1 key
  have B : ∀ κ₀, (t (Multiplicative.ofAdd κ₀)).val = 1 := fun κ₀ => by
    by_contra hx
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 (sub_ne_zero.2 hx))
    obtain ⟨n, hn⟩ := exists_nat_gt (q + 1 + 2 * Q κ₀)
    have e := A κ₀ (n + 4) _ (by omega) rfl
    rw [← hq, WithTop.coe_le_coe] at e
    have : ((n + 4 : ℕ) : ℚ) ≤ ((k * (n + 4) : ℕ) : ℚ) := by exact_mod_cast Nat.le_mul_of_pos_left _ hk
    push_cast at this e
    linarith
  refine (isZero_iff d).2 ⟨hdb, fun χ z J hJ => Units.ext ?_⟩
  rw [ht.2 χ z J hJ, B, cst_eq, map_one, Units.val_one]

end GlobalTheory.UT.SmallZero
end
end
