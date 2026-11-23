module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle029
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsBiadditiveSeriesJetEqOfBiadditiveJet
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle017
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle024
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle028
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.EvalStandardPointsThree
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsActionGauge
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGoodConst
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle018
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RelatedMap
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle022
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSeriesSubstPointsStandardThree
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvGermEvThreePoints
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvRegaugedSecondLawFamily
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
import Mathlib.Geometry.Euclidean.Volume.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.constantCoeff_invariantPolyOperator_jetEq : ∀ (k : Type) [CommRing k] (d n : ℕ) (F : Fin d → PS k 2 d) (Ix : Type) [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k) (P : MvPolynomial Ix k) (m : ℕ) (f g : PS k n d), P.totalDegree ≤ m → JEq m f g → MvPowerSeries.constantCoeff (DpolyN F cp u P f) = MvPowerSeries.constantCoeff (DpolyN F cp u P g) := by
  first | exact @GlobalTheory.ChartCmp.constantCoeff_DpolyN_jEq | exact GlobalTheory.ChartCmp.constantCoeff_DpolyN_jEq | (intros; apply GlobalTheory.ChartCmp.constantCoeff_DpolyN_jEq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.firstPartialLaw_push_along_tripleMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (ph : PS V 3 d), IsChartG t (𝟙 (Sp V)) d F act tg uv x → FamPh1 t (𝟙 (Sp V)) d x F ph e → FamPh1 t' (𝟙 (Sp V)) d x' F ph e' := by
  first | exact @GlobalTheory.famPh1_push | exact GlobalTheory.famPh1_push | (intros; apply GlobalTheory.famPh1_push <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.secondPartialLaw_push_along_tripleMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (ph : PS V 3 d), IsChartG t (𝟙 (Sp V)) d F act tg uv x → FamPh2 t (𝟙 (Sp V)) d x F ph e → FamPh2 t' (𝟙 (Sp V)) d x' F ph e' := by
  first | exact @GlobalTheory.PushSecondLaw.famPh2_push | exact GlobalTheory.PushSecondLaw.famPh2_push | (intros; apply GlobalTheory.PushSecondLaw.famPh2_push <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.exists_biadditive_series_jetEq_of_biadditiveJet : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (m : ℕ), 2 ≤ m → ∀ g : PS k 2 d, Biadd m B k g → ∃ g' : PS k 2 d, (∀ m', Biadd m' B k g') ∧ JEq m g g' := by
  first | exact @GlobalTheory.ChartBilin.exists_biadd_jEq | exact GlobalTheory.ChartBilin.exists_biadd_jEq | (intros; apply GlobalTheory.ChartBilin.exists_biadd_jEq <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.JetSer

namespace GlobalTheory.JetRoad

theorem rosIdSt : RosIdSt := by
  intro S G _ _ h2 h3 Lr c O _ _ act u hu T z J hJ
  have a := GlobalTheory.RosatiCube.rosati_cubical_additive S G h2 h3 Lr c O act u hu T z J hJ
  have b := GlobalTheory.rosatiGen_one_mul_star S G h2 h3 Lr c O act u hu T z J hJ
  exact ⟨a.1, a.2.1, b.1, b.2.1, a.2.2, b.2.2⟩

theorem jetRoad : JetAlgSt ∧ RepSt ∧ LawSt ∧ MapSt ∧ DLinSt ∧ ActSt ∧ TwoChartSt ∧ SerSt ∧
    SerExSt ∧ FBOfSt ∧ HMulSt ∧ GermExSt ∧ IntTransSt ∧ ChartBCSt := by
  have hJ : JetAlgSt := jetAlg
  have hR : RepSt := repSt_of_jetAlgSt hJ
  have hL : LawSt := lawSt_of hJ hR
  have hM : MapSt := (GlobalTheory.JetMap.mapSt_and_dLinSt hJ hR).1
  have hD : DLinSt := (GlobalTheory.JetMap.mapSt_and_dLinSt hJ hR).2
  have hA : ActSt := GlobalTheory.ChartAction.actSt_of hJ hR hM
  have hT : TwoChartSt := twoChart_of_rep_map hJ hR hM
  have hS : SerSt := serSt_of_jetAlgSt hJ
  have hE : SerExSt := serEx hJ hR hS
  exact ⟨hJ, hR, hL, hM, hD, hA, hT, hS, hE,
    FBOf.fbOf hJ hR hL hM hA hS hE valSer rosIdSt,
    FrameChange.hMul hJ hR hT hS hE,
    GlobalTheory.GermExist.germ_exists_unique hJ hR hS hE,
    IntTrans.intTrans GlobalTheory.canonGauge_independence_all.2.2.2 GlobalTheory.exists_formalBiext_map,
    GlobalTheory.ChartBaseChange.chartBaseChange hJ hS⟩

end GlobalTheory.JetRoad
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.frame_firstPartialLaw_iff_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (mp.cm.thetaPull t.PP.L t.cub.t) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (F : Fin d → PS S 2 d) (ph1 : PS S 3 d), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ m, homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x' m = jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2) * jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)) → ((∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)]) (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])) (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))) ↔ (∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (LB.pullGen t'.PP.L (thφ t'.G (x3 t'.G)) thε t'.cub.t (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 3)) (lift (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 3)) (jptG t' (𝟙 (Sp S)) d x' m (2 : Fin 3)))).left) (scaleGenG t' _ _ (unitΓ u) (LB.mulGen t'.PP.L _ _ _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)]) (LB.mulGen t'.PP.L _ _ _ _ (LB.invGen t'.PP.L _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])) (LB.invGen t'.PP.L _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))))))) := by
  first | exact @GlobalTheory.frame_first_partial_law_iff_pullback | exact GlobalTheory.frame_first_partial_law_iff_pullback | (intros; apply GlobalTheory.frame_first_partial_law_iff_pullback <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory.PrimDown

theorem exists_down_id {X₀ X' Y : Scheme.{0}} {L : LB X₀} {L' : LB X'} {F : X' ⟶ X₀} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) : ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (y : Y) p q, y ∈ LB.wchart L (fun k => φ' k ≫ F) p → y ∈ LB.wchart L' φ' q →
        gm (𝟙 Y) y _ (a.s q) = (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ (y : Y) p,
      y ∈ LB.wchart L (fun k => φ' k ≫ F) p → y ∈ LB.wchart L' φ' q →
      gm (𝟙 Y) y _ s = (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
    intro q
    have hv : ∀ (y : Y) p, y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm (𝟙 Y) y _ ((u p q)⁻¹ * res inf_le_left (t.s p)) =
          (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) :=
      fun y p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹) (hu p q _ _ y hz)))
        (gm_res _ y _ hz _))
    obtain ⟨s, hs⟩ := glue_unit _ (fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q) (fun _ => inf_le_right)
      (fun y hy => by
        choose p hp using fun k => exists_chart hL (F (φ' k y))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) (fun p => (u p q)⁻¹ * res inf_le_left (t.s p))
      (fun p p' y hy => by
        rw [hv y p hy.1, hv y p' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          trF_self hL' _ ε (𝟙 Y) y hy.1.2, gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, inv_one, _root_.mul_one, mul_inv,
          _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun y p h₁ h₂ => ?_⟩
    have hz : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res _ y inf_le_right hz s).symm.trans ((congrArg (gm _ y _) (hs p)).trans (hv y p hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun y p q h₁ h₂ => hs q y p h₁ h₂⟩
  choose p hp using fun k => exists_chart hL (F (φ' k y))
  have m : y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
  refine (hs j y p m hj).trans (Eq.trans ?_ (congrArg _ (hs j' y p m hj')).symm)
  rw [pw_trans hw φ' ε (𝟙 Y) y m m hj hj', trF_self hL _ ε (𝟙 Y) y m, _root_.one_mul, mul_inv, inv_inv, _root_.mul_assoc]

theorem exists_down_all {X₀ X' Y : Scheme.{0}} {L : LB X₀} {L' : LB X'} {F : X' ⟶ X₀} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
          gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) =
            pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
  obtain ⟨a, ha, hv⟩ := exists_down_id hw hL hL' t ht
  obtain ⟨t₁, -, hu⟩ := exists_up hw hL hL' a ha
  have e : ∀ p, t.s p = t₁.s p := fun p => unit_ext fun y hy => by
    choose q hq using fun k => exists_chart hL' (φ' k y)
    have m : y ∈ LB.wchart L' φ' q := Set.mem_iInter.2 hq
    refine Eq.trans ?_ (hu _ (𝟙 Y) y p q hy m).symm
    exact (mul_inv_cancel_left _ _).symm.trans (congrArg _ (hv y p q hy m).symm)
  exact ⟨a, ha, fun Z r z p q hp hq => (congrArg (gm r z _) (e p)).trans (hu Z r z p q hp hq)⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem prod_eSec {X0 : Scheme.{0}} (t : SAB H X0) {U : Type} [CommGroup U]
    (h : ((𝟙_ (Over X0)).left ⟶ t.G.left) → U) :
    ∏ k, h (eSec t.G ≫ primφ t k) ^ primε k = h (eSec t.G) := by
  have hpt : ∀ I : ULift.{0} (Finset (Fin 2)), eSec t.G ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I =
      (psum t.G ![1, η[t.G] ≫ t.act.act H.w0] I.down).left := by
    intro I
    simp only [cφG, eSec, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · exact (Category.comp_id _).trans (GermB.eta_one t.G)
    · rfl
  rw [Fintype.prod_sum_type]
  simp only [primφ, primε, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, zpow_neg,
    Finset.prod_inv_distrib, zpow_one]
  have z := (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ cε 2 I) (hpt I)).trans
    (GermB.cube_one_left t (fun p => h p.left) (η[t.G] ≫ t.act.act H.w0))
  exact (congrArg (fun u => h (eSec t.G) * u⁻¹) z).trans (by rw [inv_one, _root_.mul_one])

end GlobalTheory.PrimDown

namespace GlobalTheory

theorem primG_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 X1 : Scheme.{0}) (t : SAB H X0) (t' : SAB H X1) (f : X1 ⟶ X0) (mp : SABMap t' t f) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ wP : PrimTyG t, IsPrimG t wP → ∃ wP' : PrimTyG t', IsPrimG t' wP' ∧ (∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun k => primφ t' k ≫ mp.φ) primε), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (LB.pullGen t.PP.L _ _ wP mp.φ) ∧ LB.Gen.Maps (LB.linCombIso w (primφ t') primε) wP' (flatGen t.PP.L mp.φ _ _ c₁)) := by
  intro E _ _ _ H X0 X1 t t' f mp w hw wP hP
  have hL := t.PP.isLB
  have hL' := t'.PP.isLB
  obtain ⟨c₁, hc₁, hcc⟩ := ChartPrimTrPf.exists_reindex t.PP.L (φ := fun k => mp.φ ≫ primφ t k)
    (φ' := fun k => primφ t' k ≫ mp.φ) (funext fun k => ChartPrimTrPf.primφ_comm mp k) primε
    (LB.pullGen t.PP.L (primφ t) primε wP mp.φ) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hP.1 _)
  obtain ⟨a, ha, R⟩ := PrimDown.exists_down_all ((isGen_iff w).1 hw.1) hL hL' c₁ hc₁
  refine ⟨a, ⟨ha, corr_of_val hL' fun y J' hJ' => ?_⟩, c₁, hcc, ChartPrimTrPf.maps_flat w _ _ a c₁ R⟩
  choose J hJ using fun χ : (𝟙_ (Over X1)).left ⟶ t.G.left => exists_chart hL (χ y)
  have hJ : Good t.PP.L y J := hJ
  have pm := (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig mp.cm.e _
    (rigPull_le mp.cm.F mp.cm.e mp.cm.e_comm t.PP.L) (fun _ => rfl)).1 hw.2
  have e₁ := pm _ (𝟙 _) y (fun _ => J (eSec t'.G ≫ mp.φ)) (fun _ => J' (eSec t'.G)) (fun _ => hJ _) (fun _ => hJ' _)
  rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp] at e₁
  have e₂ : val c₁ (eSec t'.G) y J =
      gw w (eSec t'.G) y (J (eSec t'.G ≫ mp.φ)) (J' (eSec t'.G)) * val a (eSec t'.G) y J' := by
    refine (R _ (eSec t'.G) y _ _ (hJ.mem _ _) (hJ'.mem _ _)).trans (congrArg₂ (· * ·) ?_ rfl)
    refine Eq.trans ?_ (PrimDown.prod_eSec t' (fun q => gw w q y (J (q ≫ mp.φ)) (J' q)))
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Category.assoc]
  have e₃ : val c₁ (eSec t'.G) y J = val (L := t.PP.L) (φ := fun _ : PUnit => eSec t.G) (ε := fun _ => 1)
      t.PP.rig mp.cm.e y J := by
    refine (val_corr hJ hcc _).trans ((val_pull hJ _ _ _).trans ?_)
    refine Eq.trans ?_ (val_corr hJ hP.2 _)
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    exact congrArg (fun r => val (L := t.PP.L) (φ := primφ t) (ε := primε) wP r y J) mp.cm.e_comm
  have e₄ := (val_of (L := t.PP.L) (φ := fun _ : PUnit => eSec t.G) (ε := fun _ => 1) t.PP.rig mp.cm.e y J
    (fun _ => J (eSec t'.G ≫ mp.φ)) (fun _ => congrArg J mp.cm.e_comm.symm)).trans e₁
  have e₅ := mul_left_cancel (e₂.symm.trans (e₃.trans e₄))
  refine (val_pull hJ' _ _ _).trans ?_
  rw [Category.id_comp]
  refine e₅.trans ?_
  exact (val_of (L := t'.PP.L) (φ := fun _ : PUnit => eSec t'.G) (ε := fun _ => 1) t'.PP.rig (𝟙 _) y J' _
    (fun _ => by rw [Category.id_comp])).symm

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.RigOriginPull

theorem val_tie {X₁ X₂ Y Z : Scheme.{0}} {K : Type} [Fintype K] {L : LB X₁} {L' : LB X₂} {F : X₂ ⟶ X₁}
    (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X₂)) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε))
    (c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε))
    (h : LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L F φ' ε c)) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X₁) → L.ι} {J' : (Z ⟶ X₂) → L'.ι} (hJ : Good L z J) (hJ' : Good L' z J') :
    val c r z J = (∏ k, Geo.Tor.gw w (r ≫ φ' k) z (J ((r ≫ φ' k) ≫ F)) (J' (r ≫ φ' k)) ^ ε k) * val a r z J' := by
  have H := (maps_iff w φ' (fun k => φ' k ≫ F) ε a c (𝟙 Y) (flatGen L F φ' ε c)
    (fun j x hx => wchart_pull_le L F φ' j hx) (fun j => ?_)).1 h Z r z (fun k => J ((r ≫ φ' k) ≫ F))
    (fun k => J' (r ≫ φ' k)) (fun k => hJ ((r ≫ φ' k) ≫ F)) (fun k => hJ' (r ≫ φ' k))
  · rw [Category.comp_id] at H
    exact (val_of c r z J _ (fun k => by rw [Category.assoc])).trans H
  · refine unit_ext fun y hy => ?_
    have hyV : (𝟙 Y : Y ⟶ Y) y ∈ ((L.pull F).LinComb φ' ε).U j := hy
    have hyU : (𝟙 Y : Y ⟶ Y) ((𝟙 Y : Y ⟶ Y) y) ∈ LB.wchart L (fun k => φ' k ≫ F) (fun k => j k ⟨⟩) :=
      wchart_pull_le L F φ' j hy
    refine (gm_res (𝟙 Y) y _ hyV _).trans ?_
    refine Eq.trans ?_ (gm_res (𝟙 Y) y _ hyV _).symm
    have e := gm_pull (𝟙 Y) (𝟙 Y) y _ hyU (c.s fun k => j k ⟨⟩)
    rw [Category.comp_id] at e
    exact e.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem prod_prim (t : SAB H X0) {T : Over X0} {M : Type} [CommGroup M] (h : (T.left ⟶ t.G.left) → M) :
    ∏ k, h ((1 : T ⟶ t.G).left ≫ primφ t k) ^ primε k = h (1 : T ⟶ t.G).left := by
  have hpt : ∀ I : ULift.{0} (Finset (Fin 2)), (1 : T ⟶ t.G).left ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I =
      (psum t.G ![1, (1 : T ⟶ t.G) ≫ t.act.act H.w0] I.down).left := by
    intro I
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · exact Category.comp_id (1 : T ⟶ t.G)
    · rfl
  have hc : ∏ I, h ((1 : T ⟶ t.G).left ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I) ^ cε 2 I = 1 :=
    (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ cε 2 I) (hpt I)).trans
      (GermB.cube_one_left t (fun p => h p.left) _)
  rw [Fintype.prod_sum_type]
  simp only [primφ, primε, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, zpow_neg,
    Finset.prod_inv_distrib, zpow_one]
  exact (congrArg (fun q => h (1 : T ⟶ t.G).left * q⁻¹) hc).trans (by rw [inv_one, _root_.mul_one])

theorem prod_cube_left (t : SAB H X0) {T T' : Over X0} {M : Type} [CommGroup M] (h : (T'.left ⟶ t.G.left) → M)
    (u : T' ⟶ T) (a b : T ⟶ t.G) (ha : u ≫ a = 1) :
    ∏ I, h (u.left ≫ cφG t ![a, b] I) ^ cε 2 I = 1 := by
  have hpt : ∀ I : ULift.{0} (Finset (Fin 2)), u.left ≫ cφG t ![a, b] I = (psum t.G ![1, u ≫ b] I.down).left := by
    intro I
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · exact ha
    · rfl
  exact (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ cε 2 I) (hpt I)).trans
    (GermB.cube_one_left t (fun p => h p.left) _)

end GlobalTheory.RigOriginPull


open GlobalTheory.RigOriginPull in

theorem GlobalTheory.rigOrigin_iff_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (wP : PrimTyG t) (wP' : PrimTyG t'), wP.IsGen → wP'.IsGen → (∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun k => primφ t' k ≫ mp.φ) primε), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (LB.pullGen t.PP.L _ _ wP mp.φ) ∧ LB.Gen.Maps (LB.linCombIso w (primφ t') primε) wP' (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (act : 𝓞 E → Fin d → PS S 1 d), (homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S) ≫ x' 0 = 1) → (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → (Rig0G t x0 d x act e wP ↔ Rig0G t' (𝟙 (Sp S)) d x' act e' wP') := by
  intro E _ _ _ H X0 t S _ x0 t' mp w hrig d x x' hx e e' _ _ htie wP wP' _ _ hP act h0 _
  obtain ⟨c, hc₁, hc₂⟩ := htie 0
  obtain ⟨cP, hP₁, hP₂⟩ := hP
  have hL := t.PP.isLB
  have hL' := t'.PP.isLB
  have pm := (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig mp.cm.e _
    (rigPull_le mp.cm.F mp.cm.e mp.cm.e_comm t.PP.L) (fun _ => rfl)).1 hrig.2
  let o : Sp S ⟶ t'.G.left := (1 : overAt (𝟙 (Sp S)) S ⟶ t'.G).left
  have key : ∀ (y : Sp S) (J : (Sp S ⟶ t.G.left) → t.PP.L.ι) (J' : (Sp S ⟶ t'.G.left) → t'.PP.L.ι),
      Good t.PP.L y J → Good t'.PP.L y J' →
      val (LB.pullGen t.PP.L _ _ (eLG t x0 d x act e wP 0)
          (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) (𝟙 (Sp S)) y J =
        Geo.Tor.gw w o y (J (o ≫ mp.φ)) (J' o) *
          val (LB.pullGen t'.PP.L _ _ (eLG t' (𝟙 (Sp S)) d x' act e' wP' 0)
            (Formalism.L2.Pj.homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) (𝟙 (Sp S)) y J' ∧
      val (rigT t.G t.PP.L t.PP.rig (overAt x0 S) 1) (𝟙 (Sp S)) y J =
        Geo.Tor.gw w o y (J (o ≫ mp.φ)) (J' o) *
          val (rigT t'.G t'.PP.L t'.PP.rig (overAt (𝟙 (Sp S)) S) 1) (𝟙 (Sp S)) y J' := by
    intro y J J' hJ hJ'
    constructor
    · let A := Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)
      let A' := Formalism.L2.Pj.homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)
      let σ : Jet S (Fin 2 × Fin d) 0 →ₐ[S] Jet S (Fin 1 × Fin d) 0 := jetSubstP 0 fun p : Fin 2 × Fin d =>
        (![fun j => X ((0 : Fin 1), j), fun j => psIn d 0 ![0] (act H.w0 j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2
      have ho : (𝟙 (Sp S) ≫ A'.left) ≫ (x' 0).left = o :=
        (congrArg (· ≫ (x' 0).left) (Category.id_comp _)).trans (congrArg (fun q => q.left) h0)
      have ho' : (𝟙 (Sp S) ≫ A.left) ≫ (x 0).left = o ≫ mp.φ := by
        rw [← ho, ← hx 0]
        exact (Category.assoc _ _ _).symm
      have p₁ : val wP ((𝟙 (Sp S) ≫ A.left) ≫ (x 0).left) y J =
          Geo.Tor.gw w o y (J (o ≫ mp.φ)) (J' o) * val wP' ((𝟙 (Sp S) ≫ A'.left) ≫ (x' 0).left) y J' := by
        rw [ho, ho']
        refine (val_pull hJ wP mp.φ o).symm.trans ((val_corr hJ hP₁ o).symm.trans
          ((val_tie w _ _ wP' cP hP₂ o y hJ hJ').trans (congrArg₂ (· * ·) ?_ rfl)))
        exact prod_prim t' (T := overAt (𝟙 (Sp S)) S) (fun q => Geo.Tor.gw w q y (J (q ≫ mp.φ)) (J' q))
      have hu : (A' ≫ Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ) ≫ jptG t' (𝟙 (Sp S)) d x' 0 (0 : Fin 2) = 1 := by
        have hid : σ.comp (jetCopy d 0 (0 : Fin 2)) = AlgHom.id S _ := by
          apply GermD.jet_hom_ext
          rintro ⟨i, j⟩
          obtain rfl : i = 0 := Subsingleton.elim _ _
          simp [σ, jetSubstP, jetCopy, GermD.jetMap_mk]
        rw [jptG, Category.assoc, ← Category.assoc (Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ), GermD.homAt_comp, hid,
          GermD.homAt_id, Category.id_comp]
        exact h0
      have p₂ : val (e 0) ((𝟙 (Sp S) ≫ A.left) ≫ (Formalism.L2.Pj.homAt x0 σ).left) y J =
          val (e' 0) ((𝟙 (Sp S) ≫ A'.left) ≫ (Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ).left) y J' := by
        have q : (𝟙 (Sp S) ≫ A'.left) ≫ (Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ).left =
            (A' ≫ Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ).left := congrArg (· ≫ _) (Category.id_comp _)
        have q' : (𝟙 (Sp S) ≫ A.left) ≫ (Formalism.L2.Pj.homAt x0 σ).left =
            (A' ≫ Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ).left := q
        rw [q, q']
        refine (val_corr hJ hc₁ _).symm.trans ((val_tie w _ _ (e' 0) c hc₂ _ y hJ hJ').trans ?_)
        exact (congrArg₂ (· * ·) (prod_cube_left t' (fun q => Geo.Tor.gw w q y (J (q ≫ mp.φ)) (J' q)) _ _ _ hu)
          rfl).trans (_root_.one_mul _)
      refine (val_pull hJ _ _ _).trans ((val_mul hJ _ _ _).trans ((congrArg₂ (· * ·)
        ((val_pull hJ _ _ _).trans p₁) ((val_pull hJ _ _ _).trans p₂)).trans ((_root_.mul_assoc _ _ _).trans
          (congrArg₂ (· * ·) rfl (Eq.symm ?_)))))
      exact (val_pull hJ' _ _ _).trans ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ' _ _ _)
        (val_pull hJ' _ _ _)))
    · refine (GermB.val_rigT _ _ _ _ _ y J hJ).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl
        (GermB.val_rigT _ _ _ _ _ y J' hJ').symm))
      have b : (𝟙 (Sp S) ≫ (overAt (𝟙 (Sp S)) S).hom) ≫ mp.cm.e = 𝟙 (Sp S) ≫ (overAt x0 S).hom := by
        rw [mp.base]
        simp
      have a₁ : (𝟙 (Sp S) ≫ (overAt (𝟙 (Sp S)) S).hom) ≫ eSec t'.G = o :=
        congrArg (· ≫ eSec t'.G) (Category.id_comp _)
      have a₂ : (𝟙 (Sp S) ≫ (overAt x0 S).hom) ≫ eSec t.G = o ≫ mp.φ := by
        rw [← b, ← a₁, Category.assoc, ← mp.cm.e_comm]
        exact (Category.assoc _ _ _).symm
      have q := pm _ (𝟙 (Sp S) ≫ (overAt (𝟙 (Sp S)) S).hom) y (fun _ => J (o ≫ mp.φ)) (fun _ => J' o)
        (fun _ => (congrArg (fun r => (r ≫ mp.φ) y ∈ t.PP.L.U (J (o ≫ mp.φ))) a₁).mpr (hJ _))
        (fun _ => (congrArg (fun r => r y ∈ t'.PP.L.U (J' o)) a₁).mpr (hJ' _))
      rw [Fintype.prod_unique, zpow_one, b, a₁] at q
      exact (val_of _ _ y J _ (fun _ => congrArg J a₂)).trans (q.trans (congrArg₂ (· * ·) rfl
        (val_of _ _ y J' _ (fun _ => congrArg J' a₁)).symm))
  constructor
  · intro h
    refine corr_of_val hL' fun y J' hJ' => ?_
    choose J hJ using fun χ : Sp S ⟶ t.G.left => exists_chart hL (χ y)
    obtain ⟨k₁, k₂⟩ := key y J J' hJ hJ'
    exact mul_left_cancel (k₁.symm.trans ((val_corr hJ h _).trans k₂))
  · intro h
    refine corr_of_val hL fun y J hJ => ?_
    choose J' hJ' using fun χ : Sp S ⟶ t'.G.left => exists_chart hL' (χ y)
    obtain ⟨k₁, k₂⟩ := key y J J' hJ hJ'
    exact k₁.trans ((congrArg₂ (· * ·) rfl (val_corr hJ' h _)).trans k₂.symm)
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem canonGauge_of_log : LogSt → CanonGaugeSt := fun hlog =>
  have hcob := FormalCocycle.exists_coboundary_of_symm_cocycle hlog ChartInv.exists_isInvPair
  have huniq := AdditiveSeries.eq_zero_of_additive_of_pderiv
  canonGauge_of_steps exists_formalBiext_map exists_regauge
    (GaugeFirstLaw.exists_gauge_first_law hcob huniq)
    (SecondLawGauge.exists_gauge_second_law hcob huniq)
    (ActionGauge.exists_action_gauge
      (derivation_inner_of_reduced_order SepIdem.exists_separability_element))
    SymGauge.exists_gauge_of_symmetry

end GlobalTheory
end
