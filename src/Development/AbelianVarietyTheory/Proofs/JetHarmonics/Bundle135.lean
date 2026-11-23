module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle129
public import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle130
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle040
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle049
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle128
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle013
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupExistsOfInterlaced
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle067
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle018
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle007
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle104
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.KaSmallNonpos
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002

@[expose] public section

section

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace GlobalTheory

theorem capelliParam_mem_int_add_half : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ), inWb k r z → 0 < Tz k r z → Q.IsType k r z π u → ∀ i ∈ Finset.Icc 1 k, ∃ m : ℤ, u i = (m : ℝ) + ((k : ℝ) - 1) / 2 := by
  intro k r Wp _ _ _ z π u hz hT hπ i hi
  obtain ⟨u₀, h₀⟩ := GlobalTheory.besType_hcParam k r Wp z π u hz hT hπ
  have ha := (GlobalTheory.BesselMapCompare.isHCParam_of_isHCTypeW h₀).2
  rw [Finset.mem_Icc] at hi
  have h1 := GlobalTheory.SupNonzero.prod_eq hπ h₀ (-(u i : ℂ))
  have h2 : ∏ s : Fin k, (-(u i : ℂ) + (u (s.val + 1) : ℂ)) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨i - 1, by omega⟩) ?_
    have : i - 1 + 1 = i := by omega
    simp [this]
  rw [h2] at h1
  obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.1 h1
  have e : u i = u₀ t := by exact_mod_cast neg_add_eq_zero.1 ht
  obtain ⟨m, hm⟩ := ha t
  exact ⟨m, by rw [e]; linarith⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

theorem _root_.GlobalTheory.T.depthAtTwo_of_unscaled_depth_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Dw : ℕ → Datum H) (Xo : ∀ j, Moduli (Dw j) l) (c : Coeff l) [StarRing (𝓞 E)] (Dd : DepData E) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs) (Nd : NumDatum), (∀ v j, O.E v j = EAt (Xo := Xo (ι j)) (c := c) (LL := K) Dd v (ι j)) → (∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j)) → O.T = ((Dd.Q.T : ℕ) : ℝ) → (O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) → PiSplit (H := H) Dd → LeafPage O → ContentEqualsDatumContent N Nd ι → TiePrimes O Nd → (∀ (la : HeightOneSpectrum (𝓞 c.F)), resCharOf la ∈ O.sm → ∀ j, ∃ B : ℝ, O.T * B ≤ O.sC j ∧ nuWAt (Xo := Xo (ι j)) (c := c) Dd la (ι j) ≤ (((ramOverZ la : ℝ) * B : ℝ) : EReal)) → LeafDepth2 N O := by
  first | exact @GlobalTheory.RunDepth.leafDepthTwo_of_unscaled_bound | exact GlobalTheory.RunDepth.leafDepthTwo_of_unscaled_bound | (intros; apply GlobalTheory.RunDepth.leafDepthTwo_of_unscaled_bound <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

theorem _root_.GlobalTheory.T.thetaDepth_le_scaled_rule_value : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), w.LastPos → ∀ (s : 𝓞 (recB h.toLawsCore).KO), s ≠ 0 → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la), ∀ f ∈ T.th j w, (recPJ h j hj).depth s w la y ≤ (((vLa la ((s : 𝓞 T.Q.c.F) : T.Q.c.F) : ℤ) : ℝ) : EReal) + vAtV y f := by
  first | exact @GlobalTheory.DepthRule.depth_le_scaled_value | exact GlobalTheory.DepthRule.depth_le_scaled_value | (intros; apply GlobalTheory.DepthRule.depth_le_scaled_value <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.WeightOnDatum

theorem weight_on_datum : ∀ (D : D7) (T : Core D), T.Q.Pins → ∀ (j : ℕ), InR D j → ∀ w : WeightFamilies.Wt D j, Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) = WeightAlgebra.DF w ∧ DomW (T.Q.Dw j) (wtA w) ∧ (w.LastPos → Formalism.L2.Pj.LastPos (T.Q.Dw j) (wtA w) ∧ 1 ≤ WeightAlgebra.DF w) ∧ (∀ τ, (T.Q.Dw j).mult τ ≤ D.R.r) ∧ Fintype.card (Lt1 (T.Q.Dw j)) ≤ 2 * D.R.f * D.R.r ∧ 1 ≤ D.R.f ∧ 1 ≤ D.R.r ∧ Module.finrank ℚ D.host.E = 2 * D.R.f := by
  intro D T hP j hj w
  obtain ⟨hDF, -, hPsi, hN, hwt⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q hP j hj w
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  obtain ⟨hp, hq, -⟩ := hP.2.2.2 j hj
  have hm2 := D.R.two_le_m
  have hk5 := D.R.m_add_three_le_k
  have hj1 := hj.1
  have hj2 := hj.2
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]; omega
  have hf : 1 ≤ D.R.f := by
    have := D.R.m_le_f
    unfold Ranks.f Ranks.n
    omega
  have hp0 : 0 < (D.R.sigW j).1 := by
    simp only [Ranks.sigW]; omega
  have hlast : w.LastPos → ∀ t, 1 ≤ w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ := fun hw t =>
    hw t _ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)
  refine ⟨hDF, ?_, fun hw => ⟨?_, ?_⟩, fun τ => ?_, ?_, hf, by omega, hfr⟩
  · intro τ i i' h
    exact (dom_wtA w).1 τ h
  · intro τ hτ _
    obtain ⟨t, rfl⟩ := (hPsi τ).1 hτ
    have hmult : (T.Q.Dw j).mult (DV.tauEmb D t) = (D.R.sigW j).1 := by
      unfold Datum.mult
      have hτ' : (DV.tauEmb D t) (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hτ
      rw [if_pos hτ', hp]
    rw [hmult, (hwt t _).1]
    unfold ext0
    rw [dite_eq_left (by omega)]
    exact hlast hw t
  · have ht : Nonempty D.what₂.Tau := by
      by_cases h : InPsi T.Q.H D.host.φ₀
      · obtain ⟨t, -⟩ := (hPsi _).1 h
        exact ⟨t⟩
      · obtain ⟨t, -⟩ := (hN _).1 h
        exact ⟨t⟩
    obtain ⟨t⟩ := ht
    unfold WeightAlgebra.DF WeightAlgebra.degP
    refine le_trans ?_ (Finset.single_le_sum (f := fun τ => (∑ i, w.aP τ i) + ∑ i, w.aM τ i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
    refine le_trans ?_ (Nat.le_add_right _ _)
    exact le_trans (hlast hw t) (Finset.single_le_sum (f := fun i => w.aP t i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
  · rw [← hr, Datum.mult]
    split_ifs <;> omega
  · refine card_Lt1_le_finrank_mul.trans ?_
    rw [hfr, hr]

end GlobalTheory.WeightOnDatum
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.OneGenerator

theorem transport_level {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {t : SAB H (Sp V)}
    (P : PELUnif (maximalIdeal V) t) {F : Type} [Field F] [Algebra (FractionRing V) F] {n m : ℕ} (h : n = m)
    (θ r₀ r : Fam P.D.toPre F n) (p : QkPt P.D.toPre F n)
    (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε n))) (ζ : F)
    (x : TFK (R := V) F ⟶ P.A.A) (hx : P.ToA F n p x) (hw : w.IsGen) (hf : FinOrd P.D F n p w ζ)
    (hΦ : PhiRel P.D.toPre F n p w θ r₀) (hs : Fam.IsSmul P.D.toPre F ζ r₀ r) :
    ∃ (θ' r₀' r' : Fam P.D.toPre F m) (p' : QkPt P.D.toPre F m)
      (w' : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p'.g.b) (DegPre.lineε m))),
      HEq θ θ' ∧ P.ToA F m p' x ∧ w'.IsGen ∧ FinOrd P.D F m p' w' ζ ∧ PhiRel P.D.toPre F m p' w' θ' r₀' ∧
        Fam.IsSmul P.D.toPre F ζ r₀' r' ∧ HEq r r' := by
  subst h
  exact ⟨θ, r₀, r, p, w, HEq.rfl, hx, hw, hf, hΦ, hs, HEq.rfl⟩

end GlobalTheory.OneGenerator

namespace GlobalTheory


open OneGenerator in
theorem descent_one_generator : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso → letI := H.starRing; ∀ (a a' : 𝓞 E) (g g' : ℕ), 1 ≤ g → 1 ≤ g' → Nat.Coprime g g' → a * star a = (g : 𝓞 E) → a' * star a' = (g' : 𝓞 E) → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [IsAlgClosed F] (θ : Fam P.D.toPre F 1) (θα : Fam P.D.toPre F (1 * g')), PullAl P.D F P.oD a' 1 g' θ θα → ∀ (pb : QkPt P.D.toPre F (1 * g')) (wb : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F pb.g.b) (DegPre.lineε (1 * g')))) (ζb : F) (xb : TFK (R := V) F ⟶ P.A.A) (tb₀ tb : Fam P.D.toPre F (1 * g')), P.ToA F (1 * g') pb xb → xb ≫ P.oA.act (star a') = 1 → wb.IsGen → ζb ≠ 0 → FinOrd P.D F (1 * g') pb wb ζb → PhiRel P.D.toPre F (1 * g') pb wb θα tb₀ → Fam.IsSmul P.D.toPre F ζb tb₀ tb → ∀ (p : QkPt P.D.toPre F (1 * g' * g)) (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε (1 * g' * g)))) (ζ : F) (x : TFK (R := V) F ⟶ P.A.A), w.IsGen → ζ ≠ 0 → FinOrd P.D F (1 * g' * g) p w ζ → P.ToA F (1 * g' * g) p x → x ≫ P.oA.act (star a) = 1 → ∀ (s₂ t₀ r : Fam P.D.toPre F (1 * g' * g)), PullAl P.D F P.oD a (1 * g') g tb s₂ → PhiRel P.D.toPre F (1 * g' * g) p w s₂ t₀ → Fam.IsSmul P.D.toPre F ζ t₀ r → ∃ (θα₂ : Fam P.D.toPre F (1 * (g' * g))) (p₂ : QkPt P.D.toPre F (1 * (g' * g))) (w₂ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p₂.g.b) (DegPre.lineε (1 * (g' * g))))) (ζ₂ : F) (x₂ : TFK (R := V) F ⟶ P.A.A) (r₀ r₂ : Fam P.D.toPre F (1 * (g' * g))), PullAl P.D F P.oD (a * a') 1 (g' * g) θ θα₂ ∧ P.ToA F (1 * (g' * g)) p₂ x₂ ∧ x₂ ≫ P.oA.act (star (a * a')) = 1 ∧ w₂.IsGen ∧ ζ₂ ≠ 0 ∧ FinOrd P.D F (1 * (g' * g)) p₂ w₂ ζ₂ ∧ PhiRel P.D.toPre F (1 * (g' * g)) p₂ w₂ θα₂ r₀ ∧ Fam.IsSmul P.D.toPre F ζ₂ r₀ r₂ ∧ HEq r r₂ := by
  intro hL _ _ _ V _ _ _ _ E _ _ _ H t P hT
  letI := H.starRing
  intro a a' g g' hg hg' hco haa haa' F _ _ _ θ θα hθ pb wb ζb xb tb₀ tb hxb hxba hwb hζb hfb hΦb hsb
    p w ζ x hw hζ hf hx hxa s₂ t₀ r hs₂ hΦ hr
  have hk : 1 ≤ 1 * g' := by omega
  have hkN : 1 ≤ 1 * g' * g := Nat.mul_pos hk hg
  obtain ⟨π, -, hπ⟩ := PullLin.exists_pull_linearMap hL V P.D F (𝓞 E) P.oD H.w0 P.w0 a g (1 * g') hg hk haa
  have key : ∃ (p₂ : QkPt P.D.toPre F (1 * g' * g))
      (w₂ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p₂.g.b) (DegPre.lineε (1 * g' * g))))
      (ζ₂ : F) (x₂ : TFK (R := V) F ⟶ P.A.A) (r₀ : Fam P.D.toPre F (1 * g' * g)),
      P.ToA F (1 * g' * g) p₂ x₂ ∧ x₂ ≫ P.oA.act (star (a' * a)) = 1 ∧ w₂.IsGen ∧ ζ₂ ≠ 0 ∧
        FinOrd P.D F (1 * g' * g) p₂ w₂ ζ₂ ∧ PhiRel P.D.toPre F (1 * g' * g) p₂ w₂ (π θα) r₀ ∧
        Fam.IsSmul P.D.toPre F ζ₂ r₀ r := by
    by_cases h0 : θα = 0
    · obtain ⟨Φ, hΦ'⟩ := phiFun_of hL V _ P.D F (1 * g') hk pb wb hwb
      have e₀ : tb = 0 := by
        rw [(DVR.isSmul_iff _ _ _).1 hsb, (hΦ' _ _).1 hΦb, h0, map_zero, smul_zero]
      have e₁ : s₂ = π θα := by rw [(hπ _ _).1 hs₂, e₀, h0]
      refine ⟨p, w, ζ, x, t₀, hx, ?_, hw, hζ, hf, e₁ ▸ hΦ, hr⟩
      have := P.oA.hom (star a')
      rw [star_mul', P.oA.map_mul, ← Category.assoc, hxa, MonObj.one_comp]
    · obtain ⟨p₂, x₂, w₂, ζ₂, t₂, k₁, k₂, k₃, k₄, k₅⟩ := operator_on_pullback_eq_sum hL E H V t P hT a a' g g'
        hg hg' hco haa haa' F θα tb (π θα) s₂ t₀ r h0 ((hπ _ _).2 rfl) hs₂ 1 (fun _ => 1) (fun _ => pb)
        (fun _ => xb) (fun _ => wb) (fun _ => ζb) (fun _ => tb)
        ⟨fun _ => hxb, fun _ => hxba, fun _ => ⟨hwb, hζb, hfb⟩, fun _ => ⟨tb₀, hΦb, hsb⟩, by simp⟩
        p x w ζ hx hxa hw hζ hf hΦ hr
      obtain ⟨r₀, l₁, l₂⟩ := k₄ 0
      have e : r = t₂ 0 := by simpa using k₅
      exact ⟨p₂ 0, w₂ 0, ζ₂ 0, x₂ 0, r₀, k₁ 0, k₂ 0, (k₃ 0).1, (k₃ 0).2.1, (k₃ 0).2.2, l₁, e ▸ l₂⟩
  obtain ⟨p₂, w₂, ζ₂, x₂, r₀, k₁, k₂, k₃, k₄, k₅, k₆, k₇⟩ := key
  obtain ⟨θ', r₀', r', p', w', m₁, m₂, m₃, m₄, m₅, m₆, m₇⟩ :=
    transport_level P (Nat.mul_assoc 1 g' g) (π θα) r₀ r p₂ w₂ ζ₂ x₂ k₁ k₃ k₅ k₆ k₇
  have hc := pullAl_comp hL V P.D F (𝓞 E) P.oD H.w0 P.w0 a a' g g' 1 hg hg' le_rfl haa haa' θ θα (π θα) θ' hθ
    ((hπ _ _).2 rfl) m₁
  rw [_root_.mul_comm a' a] at hc k₂
  exact ⟨θ', p', w', ζ₂, x₂, r₀', r', hc, m₂, k₂, m₃, k₄, m₄, m₅, m₆, m₇⟩

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem mem_span_boxFam : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ S : Fam D'.toPre F k, S ∈ Submodule.span F {S' | ∃ s : Fin j → Fam D.toPre F k, IsBoxFam pD F k S' s} := by
  intro hL hL₂ _ _ V _ _ _ _ j D D' pD F _ _ k hk S
  obtain ⟨hf, hd⟩ := FamDimension.finrank_fam (D := D.toPre) (F := F) hL.globalFns hL₂.secTwist D.tau_bimult hk
  obtain ⟨hf', hd'⟩ := FamDimension.finrank_fam (D := D'.toPre) (F := F) hL.globalFns hL₂.secTwist D'.tau_bimult hk
  obtain ⟨hr, hg⟩ := rank_and_g_of_isPowDeg V j D.toPre D'.toPre pD
  let b := Module.finBasis F (Fam D.toPre F k)
  choose b' hb' using fun a : Fin j → Fin (Module.finrank F (Fam D.toPre F k)) =>
    BoxFamily.exists_isBoxFam hL.globalFns V j D.toPre D'.toPre pD F k (fun i => b (a i))
  have hi : LinearIndependent F b' :=
    boxFam_linearIndependent V j D.toPre D'.toPre pD F k _ b b.linearIndependent b' hb'
  have hc : Fintype.card (Fin j → Fin (Module.finrank F (Fam D.toPre F k))) =
      Module.finrank F (Fam D'.toPre F k) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hd, hd', hr, hg, ← pow_mul, ← mul_add, mul_comm]
  have ht : Submodule.span F (Set.range b') = ⊤ := hi.span_eq_top_of_card_eq_finrank' hc
  have hS : S ∈ Submodule.span F (Set.range b') := ht ▸ Submodule.mem_top
  refine Submodule.span_mono ?_ hS
  rintro _ ⟨a, rfl⟩
  exact ⟨_, hb' a⟩

end GlobalTheory
end
