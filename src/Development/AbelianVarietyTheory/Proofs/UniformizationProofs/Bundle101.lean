module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle081
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle088
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle099
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymmetricFramePhiPowOrderEqId
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle116
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShiftedNormalisation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle096
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle086
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle098
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AddClosure

theorem addB_of_pull {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (f₀ : ∀ α, SecBT D (𝟙_ _) 1 α) (s₀ : Raw D F 1) (r : R) {n : ℕ}
    (f f' : Fin n → ∀ α, SecBT D (𝟙_ _) 2 α) (s s' : Fin n → Raw D F 2)
    (h₀ : PullB D F (toUnit _) 1 f₀ s₀) (h : ∀ i, PullB D F (toUnit _) 2 (f i) (s i))
    (h' : ∀ i, PullB D F (toUnit _) 2 (f' i) (s' i)) (hB : AddB D (𝟙_ _) f₀ r f f') :
    AddB D (TF (R := R) F) s₀ r s s' := by
  intro T ρ x y z J hJ
  obtain ⟨h1, h2⟩ := hB T (ρ ≫ toUnit _) x y z J hJ
  have e₀ := fun α w => GlobalTheory.pullB_values R D F _ _ 1 f₀ s₀ h₀ α T ρ w z J hJ
  have e := fun i α w => GlobalTheory.pullB_values R D F _ _ 2 (f i) (s i) (h i) α T ρ w z J hJ
  have e' := fun i α w => GlobalTheory.pullB_values R D F _ _ 2 (f' i) (s' i) (h' i) α T ρ w z J hJ
  refine ⟨fun a b α β ha hb => ?_, fun α β hn => ?_⟩
  · refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) ((h1 a b α β ha hb).trans ?_)
    · exact congrArg₂ (· * ·) (e i α x) (e' i β y)
    · exact congrArg _ (congrArg₂ (· * ·) (e₀ a _).symm (e₀ b _).symm)
  · refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (h2 α β hn)
    exact congrArg₂ (· * ·) (e i α x) (e' i β y)

theorem main : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s₀ : Raw D (Kbar V) 1), U.PullG (Kbar V) (toUnit _) 1 θ th → PullB D (Kbar V) (toUnit _) 1 f s₀ → ∃ (r : V) (n : ℕ) (t t' : Fin n → LB.Sec (LPow A.A A.L ((2 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s s' : Fin n → Raw D (Kbar V) 2), r ≠ 0 ∧ (∀ i, U.ExpF (Kbar V) 2 (t i) (s i) ∧ U.ExpF (Kbar V) 2 (t' i) (s' i)) ∧ AddA A (TFK (R := V) (Kbar V)) th t t' ∧ AddB D (TF (R := V) (Kbar V)) s₀ r s s') := by
  intro hL hL2 V _ _ _ hV D A G _ _ U θ f hθ th s₀ hth hs₀
  obtain ⟨r, n, σ, σ', hr, hG⟩ := GlobalTheory.T.exists_integral_addition_formula_group V hV D A G U θ
  have hexp := GlobalTheory.BaseExpansionExists.main hL hL2 V hV D A G U 2 (by norm_num)
  choose g hg using hexp
  obtain ⟨hpG, hpB⟩ := GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 2
  choose pt hpt using fun σ => (hpG σ).exists
  choose ps hps using fun f => (hpB f).exists
  have hB := GlobalTheory.T.additionFormula_coefficients_abelian_square hL.globalFns V hV D A G U θ f r n σ σ' (fun i => g (σ i)) (fun i => g (σ' i)) hG hθ.1
    (fun i => ⟨hg _, hg _⟩)
  refine ⟨r, n, fun i => pt (σ i), fun i => pt (σ' i), fun i => ps (g (σ i)), fun i => ps (g (σ' i)), hr,
    fun i => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact GlobalTheory.expF_of_pull V D _ A G U (Kbar V) 2 _ _ _ _ (hg _) (hpt _) (hps _)
  · exact GlobalTheory.expF_of_pull V D _ A G U (Kbar V) 2 _ _ _ _ (hg _) (hpt _) (hps _)
  · exact GlobalTheory.AddGeneric.addA_of_addG V D _ A G U (Kbar V) θ r n σ σ' th _ _ hr hG hth (fun i => ⟨hpt _, hpt _⟩)
  · exact addB_of_pull D (Kbar V) f s₀ r _ _ _ _ hs₀ (fun i => hps _) (fun i => hps _) hB

end GlobalTheory.AddClosure
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.endU_twist_of_iso : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (E : EndU U) (F : Type) [Field F] [Algebra (FractionRing R) F] (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left] ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])), β.IsGen → LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ β (eSec G)) (LB.oneGen U.LG.L) → ∀ (w₀ : W0 U) (ρ), NormW U w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') (v : U.SecGF F k) (v' : U.SecGF F k'), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) v → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k' (snd (TFK (R := R) F) A.A).left (U.genF F).left t' (UnifPre.gFK (G := G) F) (𝟙 _) v' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ (y : (UnifPre.GF (G := G) F).left) (J), Good U.LG.L y J → sval v' (𝟙 _) y J = sval v (TFK (R := R) F ◁ (Over.pullback (jK R)).map E.aG).left y J * (val β (UnifPre.gFK (G := G) F) y J * val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (UnifPre.gFK (G := G) F ≫ G.hom) y J ^ ((k' : ℤ) - k)).val := by
  first | exact @GlobalTheory.UT.TwistCompare.twist_through_iso | exact GlobalTheory.UT.TwistCompare.twist_through_iso | (intros; apply GlobalTheory.UT.TwistCompare.twist_through_iso <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.rosatiAdjoint_abelianPart_and_classifying_map_linear : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ E E' : EndU U.toUnifPre, LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → RosatiAdj A.A A.L E.aA E'.aA ∧ RosatiAdj D.toPre.P.A D.toPre.P.L E.aB E'.aB ∧ (∀ χ, D.toPre.c (E.h χ) = D.toPre.c χ ≫ E'.aB) ∧ ∀ χ, D.toPre.c (E'.h χ) = D.toPre.c χ ≫ E.aB := by
  first | exact @GlobalTheory.UT.rosatiAdj_and_c_linear_of_endU | exact GlobalTheory.UT.rosatiAdj_and_c_linear_of_endU | (intros; apply GlobalTheory.UT.rosatiAdj_and_c_linear_of_endU <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.symmetricFrame_phi_pow_order_eq_id : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) (w : Frm D.toPre F N p.g.b), TXFrame N p w → ∀ ss : Fin (N + 1) → Fam D.toPre F N, (∀ i : Fin N, PhiRel D.toPre F N p w (ss i.castSucc) (ss i.succ)) → ss (Fin.last N) = ss 0 := by
  first | exact @GlobalTheory.UT.PhiOrder.main | exact GlobalTheory.UT.PhiOrder.main | (intros; apply GlobalTheory.UT.PhiOrder.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.PhiProj

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem val_scale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (c : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) :
    val (scaleGen c t) r z J = gm r z ⊤ c * val t r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)

def cUnit (ζ : F) (hζ : ζ ≠ 0) : Γ((TF (R := R) F).left, ⊤)ˣ :=
  ((Ne.isUnit hζ).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).unit

theorem phiRel_of_ratio (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k) {w w' : Frm D F k p.g.b} (hw : w.IsGen)
    (hw' : w'.IsGen) (c : F) (hc : c ≠ 0)
    (hv : ∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cst F z c * (val w (𝟙 _) z J).val)
    (s t : Fam D F k) (h : PhiRel D F k p w s t) : PhiRel D F k p w' s (c • t) := by
  have hcorr : LB.Gen.Corr D.P.L _ _ _ _ w' (scaleGen (cUnit (R := R) c hc) w) :=
    corr_of_val D.P.isLB fun z J hJ => Units.ext (by
      rw [hv z J hJ, val_scale hJ, Units.val_mul]
      exact congrArg₂ (· * ·) (gs_unit _ z ⊤ trivial (cUnit (R := R) c hc)) rfl)
  refine (phiRel_iff hG p w' hw' s _).2 fun a β hβ T ρ z J hJ => ?_
  have h1 := (phiRel_iff hG p w hw s t).1 h a β hβ T ρ z J hJ
  have hu : gs (ρ.left ≫ (fst (TF (R := R) F) D.P.A).left) z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) =
      (gm (ρ ≫ fst (TF (R := R) F) D.P.A).left z ⊤ (cUnit (R := R) c hc)).val :=
    gs_unit _ z ⊤ trivial (cUnit (R := R) c hc)
  rw [sval_smul c t β ρ.left z hJ, h1, val_mul hJ, val_mul hJ, val_corr hJ hcorr, val_scale hJ, hu]
  simp only [Units.val_mul]
  ring

theorem exists_scaled {k : ℕ} {b : TF (R := R) F ⟶ D.P.A} {w : Frm D F k b} (hw : w.IsGen) (c : F) (hc : c ≠ 0) :
    ∃ w' : Frm D F k b, w'.IsGen ∧
      ∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cst F z c * (val w (𝟙 _) z J).val := by
  refine ⟨scaleGen (cUnit (R := R) c hc) w, scaleGen_isGen _ w hw, fun z J hJ => ?_⟩
  rw [val_scale hJ, Units.val_mul]
  exact congrArg₂ (· * ·) (gs_unit _ z ⊤ trivial (cUnit (R := R) c hc)).symm rfl

theorem phiRel_of_equiv (hG : GlobalFnsSt) {k : ℕ} {p p' : QkPt D F k} (he : QkPt.Equiv D F p p')
    {w : Frm D F k p.g.b} (hw : w.IsGen) : ∃ w' : Frm D F k p'.g.b, w'.IsGen ∧
      ∀ s t, PhiRel D F k p w s t → PhiRel D F k p' w' s t := by
  obtain ⟨z, hy, h, hι, ha⟩ := he
  obtain ⟨w', hw', hv⟩ := GlobalTheory.exists_shifted_normalisation k p.g z p'.g.b
    (ha.1.trans (congrArg (p.g.b * ·) hι.1)) w hw
  refine ⟨w', hw', fun s t => ?_⟩
  rw [phiRel_iff hG p w hw, phiRel_iff hG p' w' hw']
  intro H α β hβ T ρ x J hJ
  rw [← GlobalTheory.phi_value_shift hG k p.g h p'.g z hι ha w w' hv s α T ρ x J hJ]
  exact H (α + k • z) β (by rw [← hβ, hy]; abel) T ρ x J hJ

theorem phiRel_zero (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k) (w : Frm D F k p.g.b) (hy : p.y = 0)
    (hg : p.g.IsZero) (hw : FrmOne w) (s : Fam D F k) : PhiRel D F k p w s s := by
  have hb : p.g.b = 1 := hg.1
  have hcorr : LB.Gen.Corr D.P.L _ _ _ _ w (LB.oneGen D.P.L) :=
    corr_of_val D.P.isLB fun z J hJ => (hw.2 z J hJ).trans (val_one _).symm
  refine (phiRel_iff hG p w hw.1 s s).2 fun α β hβ T ρ z J hJ => ?_
  obtain rfl : α = β := by rw [← hβ, hy, add_zero]
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have e₁ : ρ ≫ DegPre.trPt D F p.g.b = ρ := by rw [hb, H1.trPt_one, Category.comp_id]
  have e₂ : uVal D F k α p.g.b ρ z J = 1 := by
    have e : ρ ≫ fst (TF (R := R) F) D.P.A ≫ p.g.b = 1 := by rw [hb, MonObj.comp_one, MonObj.comp_one]
    rw [uVal, e, C.face₃, inv_one, _root_.mul_one]
    exact Finset.prod_eq_one fun _ _ => C.face₂ _ _
  rw [e₁, e₂, val_mul hJ, val_corr hJ (hg.2 α), val_corr hJ hcorr, val_one, _root_.mul_one, _root_.mul_one,
    Units.val_one, _root_.mul_one]

theorem bijective_of_pow {F V : Type} [Field F] [AddCommGroup V] [Module F V] (Φ : V →ₗ[F] V) {k : ℕ} (hk : 1 ≤ k)
    {c : F} (hc : c ≠ 0) (h : ∀ s, (Φ ^ k) s = c • s) : Function.Bijective Φ := by
  obtain ⟨k, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  constructor
  · intro a b hab
    have : (Φ ^ (k + 1)) a = (Φ ^ (k + 1)) b := by
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, hab]
    rw [h, h] at this
    exact smul_right_injective V hc this
  · intro b
    refine ⟨(Φ ^ k) (c⁻¹ • b), ?_⟩
    rw [← Module.End.mul_apply, ← pow_succ', h, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem phi_projective : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∃ Φ : ∀ (p : QkPt D.toPre F k), Frm D.toPre F k p.g.b → (Fam D.toPre F k →ₗ[F] Fam D.toPre F k), (∀ p w, w.IsGen → Function.Bijective (Φ p w) ∧ ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ p w s) ∧ (∀ p w, w.IsGen → ∀ c : F, c ≠ 0 → ∃ w', w'.IsGen ∧ Φ p w' = c • Φ p w) ∧ (∀ p w w', w.IsGen → w'.IsGen → ∃ c : F, c ≠ 0 ∧ Φ p w' = c • Φ p w) ∧ (∀ p p' w, w.IsGen → QkPt.Equiv D.toPre F p p' → ∃ w', w'.IsGen ∧ Φ p' w' = Φ p w) ∧ (∀ p p' p'' w w', w.IsGen → w'.IsGen → QkAdd p p' p'' → ∃ w'', w''.IsGen ∧ Φ p'' w'' = Φ p w ∘ₗ Φ p' w') ∧ ∀ p w, p.y = 0 → p.g.IsZero → FrmOne w → Φ p w = LinearMap.id := by
  intro hL R _ _ _ I _ D F _ _ _ k hk
  have hG : GlobalFnsSt := hL.1.globalFns
  have ex : ∀ (p : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b), ∃ Φ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k,
      w.IsGen → ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s := fun p w => by
    by_cases hw : w.IsGen
    · obtain ⟨Φ, h⟩ := phiFun_of_globalFns hG R I D F k hk p w hw
      exact ⟨Φ, fun _ => h⟩
    · exact ⟨0, fun h => (hw h).elim⟩
  choose Φ hΦ using ex
  have rel : ∀ p w, w.IsGen → ∀ s, PhiRel D.toPre F k p w s (Φ p w s) := fun p w hw s => (hΦ p w hw s _).2 rfl
  refine ⟨Φ, fun p w hw => ⟨?_, hΦ p w hw⟩, fun p w hw c hc => ?_, fun p w w' hw hw' => ?_,
    fun p p' w hw he => ?_, fun p p' p'' w w' hw hw' hadd => ?_, fun p w hy hg hw => ?_⟩
  · obtain ⟨c, hc, hcs⟩ := H1.phiPow_core hG p w hw
    refine bijective_of_pow (Φ p w) hk hc fun s => ?_
    have h := hcs (fun i => (Φ p w ^ (i : ℕ)) s) (fun i => by
      rw [hΦ p w hw]
      simp only [Fin.val_succ, Fin.val_castSucc, pow_succ', Module.End.mul_apply])
    rw [isSmul_iff] at h
    simpa only [Fin.val_last, Fin.val_zero, pow_zero, Module.End.one_apply] using h
  · obtain ⟨w', hw', hv⟩ := exists_scaled hw c hc
    exact ⟨w', hw', LinearMap.ext fun s =>
      ((hΦ p w' hw' s _).1 (phiRel_of_ratio hG p hw hw' c hc hv s _ (rel p w hw s))).symm⟩
  · obtain ⟨c, hc, hv⟩ := CoefBasic.exists_frame_ratio hw hw'
    exact ⟨c, hc, LinearMap.ext fun s =>
      ((hΦ p w' hw' s _).1 (phiRel_of_ratio hG p hw hw' c hc hv s _ (rel p w hw s))).symm⟩
  · obtain ⟨w', hw', h⟩ := phiRel_of_equiv hG he hw
    exact ⟨w', hw', LinearMap.ext fun s => ((hΦ p' w' hw' s _).1 (h s _ (rel p w hw s))).symm⟩
  · obtain ⟨q, hy, hg, he⟩ := hadd
    obtain ⟨w₂, hw₂, h₂⟩ := GlobalTheory.ThetaMul.phi_mul_core hG p p' q hy hg w w' hw hw'
    obtain ⟨w'', hw'', h⟩ := phiRel_of_equiv hG he hw₂
    exact ⟨w'', hw'', LinearMap.ext fun s =>
      ((hΦ p'' w'' hw'' s _).1 (h s _ (h₂ s _ _ (rel p' w' hw' s) (rel p w hw _)))).symm⟩
  · exact LinearMap.ext fun s => ((hΦ p w hw.1 s s).1 (phiRel_zero hG p w hy hg hw s)).symm

end GlobalTheory.UT.PhiProj
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.TwistKer

theorem cls_twist_pull {S : Scheme.{0}} (B : Over S) [GrpObj B] {L O : LB B.left} (hL : L.IsLB) (hO : O.IsLB)
    {T : Over S} (x : T ⟶ B) (h : (LB.div (translDiff B L x) (O.pull (snd T B).left)).IsLB)
    (h' : (LB.div (translDiff B L (𝟙 B)) (O.pull (snd B B).left)).IsLB) :
    CechPic.cls _ h = CechPic.pull (x ▷ B).left (CechPic.cls _ h') := by
  have e₁ : (x ▷ B).left ≫ (snd B B).left = (snd T B).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  have e₂ : (x ▷ B).left ≫ (lift (fst B B ≫ 𝟙 B) (snd B B) ≫ μ[B]).left =
      (lift (fst T B ≫ x) (snd T B) ≫ μ[B]).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_lift, Category.comp_id, whiskerRight_snd, whiskerRight_fst]
  have hx : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _
  have h1 : (translDiff B L (𝟙 B)).IsLB := LB.isLB_linComb hL _ _
  rw [CechPic.cls_div hx (pull_isLB hO _), CechPic.cls_div h1 (pull_isLB hO _), map_sub,
    CechPic.cls_pull hO, CechPic.cls_pull hO, ← CechPic.pull_comp, e₁]
  congr 1
  refine (CechPic.cls_linComb hL _ _ hx).trans ?_
  refine Eq.trans ?_ (congrArg (CechPic.pull (x ▷ B).left) (CechPic.cls_linComb hL _ _ h1)).symm
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_add (f := _), map_zsmul,
    ← CechPic.pull_comp, e₁, e₂]

theorem exists_closed_twist_kernel : GlobalFnsSt → ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ L O : LB B.left, L.IsLB → O.IsLB → ∃ (H : Over (Spec (CommRingCat.of R))) (j : H ⟶ B), IsClosedImmersion j.left ∧ (∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ B), (∀ p : (T).left, ∃ U : (T).left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff B L x) (O.pull (snd (T) B).left)).pull ((fst (T) B).left ⁻¹ᵁ U).ι)) ↔ ∃ y : T ⟶ H, y ≫ j = x) := by
  intro hG R _ B _ hB hP L O hL hO
  have hF : (LB.div (translDiff B L (𝟙 B)) (O.pull (snd B B).left)).IsLB :=
    LB.isLB_div (LB.isLB_linComb hL _ _) (pull_isLB hO _)
  obtain ⟨H, j, hj, h⟩ := GlobalTheory.T.exists_closedSubscheme_locallyTrivial_product_lineBundle hG R B B hB hP _ hF
  refine ⟨H, j, hj, fun T x => Iff.trans ?_ (h T x)⟩
  have hx : (LB.div (translDiff B L x) (O.pull (snd T B).left)).IsLB :=
    LB.isLB_div (LB.isLB_linComb hL _ _) (pull_isLB hO _)
  refine forall_congr' fun p => exists_congr fun U => and_congr Iff.rfl ?_
  refine (CechPic.cls_eq_zero_iff (pull_isLB hx _)).symm.trans
    (Iff.trans ?_ (CechPic.cls_eq_zero_iff (pull_isLB (pull_isLB hF _) _)))
  rw [CechPic.cls_pull hx, CechPic.cls_pull (pull_isLB hF _), CechPic.cls_pull hF, cls_twist_pull B hL hO x hx hF]

end GlobalTheory.UU.TwistKer
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU.TorsionCount

theorem card_torsion_points_unconditional :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) :=
  GlobalTheory.T.card_torsion_points_abelianVariety GlobalTheory.laws_without_cohomology.1 GlobalTheory.laws_without_cohomology.2.1

end GlobalTheory.UU.TorsionCount
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifPowAdm

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Comb

variable {K : Type} [CommRing K] {Y Y' : Scheme.{0}}

def cstHom (π : Y ⟶ Spec (CommRingCat.of K)) (W : Y.Opens) : K →+* Γ(Y, W) :=
  (Y.presheaf.map (homOfLE le_top).op).hom.comp
    (π.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

theorem res_cstHom (π : Y ⟶ Spec (CommRingCat.of K)) {W W' : Y.Opens} (h : W' ≤ W) (c : K) :
    (Y.presheaf.map (homOfLE h).op).hom (cstHom π W c) = cstHom π W' c :=
  SecOps.resTop_res h _

def IsComb (π : Y ⟶ Spec (CommRingCat.of K)) {M : LB Y} {Λ : Type} [Fintype Λ] (s : LB.Sec M) (c : Λ → K)
    (t : Λ → LB.Sec M) : Prop :=
  ∀ jj, s.f jj = ∑ l, cstHom π (M.U jj) (c l) * (t l).f jj

variable (π : Y ⟶ Spec (CommRingCat.of K)) {M : LB Y} {Λ Λ' : Type} [Fintype Λ] [Fintype Λ']

theorem exists_isComb (c : Λ → K) (t : Λ → LB.Sec M) : ∃ s, IsComb π s c t :=
  ⟨⟨fun jj => ∑ l, cstHom π (M.U jj) (c l) * (t l).f jj, fun i j => by

    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, (t l).compat, res_cstHom, map_mul, res_cstHom, mul_left_comm]⟩, fun _ => rfl⟩

variable {π}

theorem IsComb.trans {s : LB.Sec M} {c : Λ → K} {t : Λ → LB.Sec M} {d : Λ → Λ' → K} {u : Λ' → LB.Sec M}
    (h : IsComb π s c t) (h' : ∀ l, IsComb π (t l) (d l) u) : IsComb π s (fun a => ∑ l, c l * d l a) u := by
  intro jj
  rw [h jj]

  simp only [h' _ jj, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
  exact Finset.sum_comm

theorem IsComb.unique {s s' : LB.Sec M} {c : Λ → K} {t : Λ → LB.Sec M}
    (h : IsComb π s c t) (h' : IsComb π s' c t) : s = s' :=
  SecOps.sec_ext fun jj => (h jj).trans (h' jj).symm

end Comb

section Box

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {LG : LB G.left} {LG' : LB G'.left}

end Box

section Exp

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ)

theorem expands_comb {Λ : Type} [Fintype Λ] {c : Λ → FractionRing R} {s : Λ → U.SecK k}
    {E : Λ → Fam D.toPre (FractionRing R) k} {s₀ : U.SecK k} (h : ∀ l, U.Expands k (s l) (E l))
    (h₀ : IsComb (pullback.snd G.hom (jK R)) s₀ c s) : U.Expands k s₀ (∑ l, c l • E l) := by
  have e := (Fintype.equivFin Λ).symm
  rw [← e.sum_comp]
  exact ExpandsFracLinear.main R I D A G U k _ (fun l => c (e l)) (fun l => s (e l)) (fun l => E (e l)) s₀
    (fun l => h _) (fun jj => (h₀ jj).trans (e.sum_comp _).symm)

theorem expands_functional (hR : AdmBase R I) {s : U.SecK k} {E E' : Fam D.toPre (FractionRing R) k}
    (h : U.Expands k s E) (h' : U.Expands k s E') : E = E' := by
  have h₀ : U.Expands k SecOps.secZero (∑ l : Fin 2, (![1, -1] : Fin 2 → FractionRing R) l • ![E, E'] l) :=
    expands_comb U k (s := fun _ => s) (fun l => by fin_cases l; exacts [h, h']) (fun jj => by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_neg, map_one, neg_mul, add_neg_cancel]
      rfl)
  have h₁ := GlobalTheory.ExpZero.main R I D A G U k hR _ _ (fun _ => rfl) h₀
  rw [Fin.sum_univ_two] at h₁
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at h₁
  exact add_neg_eq_zero.1 h₁

theorem expBij_of_basis (hR : AdmBase R I) {Λ : Type} [Fintype Λ]
    (b : Module.Basis Λ (FractionRing R) (Fam D.toPre (FractionRing R) k)) (σ : Λ → U.SecK k)
    (hσ : ∀ l, U.Expands k (σ l) (b l)) (hspan : ∀ s, ∃ c, IsComb (pullback.snd G.hom (jK R)) s c σ) :
    U.ExpBij k := by
  refine ⟨fun s => ?_, fun E => ?_⟩
  · obtain ⟨c, hc⟩ := hspan s
    exact ⟨_, expands_comb U k hσ hc, fun E hE => expands_functional U k hR hE (expands_comb U k hσ hc)⟩
  · obtain ⟨s, hs⟩ := exists_isComb (pullback.snd G.hom (jK R)) (b.equivFun E) σ
    refine ⟨s, ?_, fun t ht => ?_⟩
    · have := expands_comb U k hσ hs
      rwa [b.sum_equivFun] at this
    · obtain ⟨c, hc⟩ := hspan t
      have e := expands_functional U k hR ht (expands_comb U k hσ hc)
      have e' : b.equivFun E = c := by rw [e, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
      exact hc.unique (e' ▸ hs)

end Exp

end GlobalTheory.UnifPowAdm
end
end
