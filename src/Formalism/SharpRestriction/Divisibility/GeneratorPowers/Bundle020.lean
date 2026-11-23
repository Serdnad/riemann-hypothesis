module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle014
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqGlue
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle018
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle012
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
public import Mathlib.RingTheory.PowerSeries.Exp
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FormalGroupLinearSecond
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle017
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)
open IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

namespace BoxTuple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def BoxTup (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (Q : P.D.toPre.X → ℤ)
    (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F] (v : AddValuation F (WithTop ℚ)) (g g' : ℕ) (π : 𝓞 E)
    {n : ℕ} {D' : DegData T.V (maximalIdeal T.V)} {A' : PolAV (Spec (CommRingCat.of T.Fr))} {G' : Over (Sp T.V)}
    [GrpObj G'] [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n}
    (pG : IsPowGrp G' C.I.G.G n) {U' : Unif (maximalIdeal T.V) D' A' G'} (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E))
    (s : Fam D'.toPre F g') (s₂ : Fam D'.toPre F (g' * g)) (p : QkPt D'.toPre F (g' * g))
    (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (g' * g))))
    (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (g' * g))
    (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F n (chD C.ch)) : Prop :=
  NuGe D' (sumQ pD.xe Q) F v g' s 0 ∧
  PullAl D' F oD' (star π) g' g s s₂ ∧
  (w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D' F (g' * g) p w ζ) ∧
  QkToAkU U'.toUnifPre F (g' * g) p x ∧ (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) ∧
  PhiRel D'.toPre F (g' * g) p w s₂ t₀ ∧ Fam.IsSmul D'.toPre F ζ t₀ t ∧
  U'.toUnifPre.ExpandsG F (g' * g) σ' t ∧
  IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h

end BoxTuple

open BoxTuple

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqChart

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem epsMul_zero {S : Type} [CommRing S] :
    epsMul (0 : S) = (algebraMap S (DualNumber S)).comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · first
    | simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
    | (simp [epsMul]; rfl)
  · first
    | simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
    | (simp [epsMul]; rfl)

theorem epsMul_one {S : Type} [CommRing S] : epsMul (1 : S) = RingHom.id (DualNumber S) := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;> simp [epsMul]

theorem fst_comp_tan {S : Type} [CommRing S] (d : ℕ) (j : Fin d) :
    (TrivSqZeroExt.fstHom S S S).comp
      (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) = jetAug := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  first
  | (simp only [AlgHom.comp_apply, Formalism.L2.Pj.jetTan, Formalism.L2.Pj.jetAug, Formalism.L2.Pj.liftJet, Ideal.Quotient.liftₐ_apply,
      Ideal.Quotient.mkₐ_eq_mk, AlgHom.coe_toRingHom]
     erw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk]
     by_cases h : i = (0, j) <;> simp [h])
  | (show TrivSqZeroExt.fst ((MvPolynomial.aeval _) (MvPolynomial.X i)) = (MvPolynomial.aeval _) (MvPolynomial.X i)
     by_cases h : i = (0, j) <;> simp [h])

theorem comp_one_gen {X : Scheme.{0}} {Y Z M : Over X} [GrpObj M] (f : Y ⟶ Z) : f ≫ (1 : Z ⟶ M) = 1 := by
  first
  | simp
  | (rw [MonObj.Hom.one_def, MonObj.Hom.one_def, ← Category.assoc]; congr 1; exact toUnit_unique _ _)
  | simp [MonObj.Hom.one_def]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]

theorem tan_eq (y : FrPt Xo c S) (x : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G) (hx : IsExpChart y x)
    (j : Fin (dL Dw)) :
    (homAt y.x (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left =
      y.u ((ltIdx Dw).symm j).1 ((ltIdx Dw).symm j).2 := by
  obtain ⟨u, hu, hprod⟩ := hx.tan ((ltIdx Dw).symm j)
  have hj : ltIdx Dw ((ltIdx Dw).symm j) = j := Equiv.apply_symm_apply _ _
  have hone : ∀ i, i ≠ j → u i = 1 := by
    intro i hi
    have e : u i = homAt y.x (Algebra.ofId S (DualNumber S)) ≫
        (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] S) ≫ x 1) := by
      apply Over.OverMorphism.ext
      simp only [hu i, hj, if_neg hi, epsMul_zero, ← fst_comp_tan (dL Dw) i]
      simp only [Over.comp_left, Formalism.L2.Pj.homAt, Over.homMk_left]
      simp only [spMap, ← Category.assoc]
      congr 1
      simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    rw [e, hx.zero 1, comp_one_gen]
  have huj : (u j).left = (homAt y.x (jetTan ((0 : Fin 1), j) :
      Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left := by
    simp [hu j, hj, epsMul_one, spMap, CommRingCat.ofHom_id, Spec.map_id]
  rw [← hprod, ← huj]
  congr 1
  rw [List.prod_ofFn]
  exact (Finset.prod_eq_single j (fun i _ hi => hone i hi) (fun h => absurd (Finset.mem_univ j) h)).symm

theorem expUniqTan : ExpUniqTanSt := by
  intro E _ _ _ H Dw l Xo c S _ _ _ y x x' hx hx'
  refine ExpUniqGlue.expUniq E H Dw l Xo c S y (dL Dw) x x' ⟨hx.trunc, hx.law⟩ ⟨hx'.trunc, hx'.law⟩ ?_
  intro j
  apply Over.OverMorphism.ext
  rw [tan_eq y x hx j, tan_eq y x' hx' j]

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqChart
end
end

section

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

theorem tan_coef {V K : Type} [CommRing V] [CommRing K] [Algebra V K] {d : ℕ} (j : Fin d) :
    (jetTan ((0 : Fin 1), j) : Jet K (Fin 1 × Fin d) (0 + 1) →ₐ[K] DualNumber K).toRingHom.comp
      (jetCoef (algebraMap V K) (Fin 1 × Fin d) 1) = (dualMap (algebraMap V K)).comp
      (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    show MvPolynomial.aeval _ (MvPolynomial.map _ (MvPolynomial.C r)) = dualMap _ (MvPolynomial.aeval _ (MvPolynomial.C r))
    rw [MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.aeval_C]
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · intro s
    show MvPolynomial.aeval _ (MvPolynomial.map _ (MvPolynomial.X s)) = dualMap _ (MvPolynomial.aeval _ (MvPolynomial.X s))
    rw [MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    split_ifs <;> ext <;> simp [dualMap]


theorem chartJetTan_holds : ChartJetTanSt Xo c := by
  intro T io y I d FT actT tgT uvecT xT hb hc hu
  letI := io.toAlgebra
  have hid : IsGrpPullback I.G.G I.G.G (𝟙 _) (𝟙 _) := ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy =>
    (mul_left_congr (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _)) (hy.trans (Category.comp_id _))).trans
      (Category.comp_id _).symm⟩
  let D : Fin d → (epsR T.V ⟶ I.G.G) := fun j => Over.homMk (Formalism.L2.Pj.homAt (𝟙 (Sp T.V))
    (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left
    ((Over.w _).trans (Category.comp_id _))
  let D' : Fin d → (epsR T.Fr ⟶ I.t'.G) := fun j => Over.homMk (spMap ((jetTan ((0 : Fin 1), j) :
    Jet T.Fr (Fin 1 × Fin d) (0 + 1) →ₐ[T.Fr] DualNumber T.Fr) : _ →+* _) ≫ JetTr.xL I xT 1) (by
      rw [Category.assoc, JetTr.xL_snd]; exact spMap_comp_alg _)
  have hD : ∀ j, (D' j).left ≫ I.m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (D j).left := fun j => by
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (JetTr.xL_fst I xT 1)).trans ((Category.assoc _ _ _).symm.trans
      (Eq.trans (congrArg (· ≫ (xT 1).left) ?_) (Category.assoc _ _ _))))
    exact (JetTr.spMap_comp' _ _).trans ((congrArg spMap (tan_coef j)).trans (JetTr.spMap_comp' _ _).symm)
  choose u' h₁ h₂ using I.lift
  have ho : ∀ τ i, u' τ i ≫ I.t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := fun τ i => by
    have : Mono (spMap (algebraMap T.V T.Fr)) := by
      have := IsPreimmersion.of_isLocalization (S := T.Fr) (nonZeroDivisors T.V)
      exact inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))))
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← I.m2.cart.1.w, ← Category.assoc, h₂, Category.assoc,
      Over.w]
    exact (JetTr.spMap_comp' _ _).trans ((congrArg spMap (RingHom.ext fun r => by
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])).trans (JetTr.spMap_comp' _ _).symm)
  let U' : Lt1 Dw → (epsR T.Fr ⟶ I.t'.G) := fun ℓ => Over.homMk (u' ℓ.1 ℓ.2) (ho _ _)
  have cb : ∀ ℓ, IsLieComb (fun i => algebraMap T.V T.Fr (uvecT ℓ i)) D' (U' ℓ) := fun ℓ =>
    Chart.comb_baseChange _ I.m2.cart (w := Over.homMk (I.ub ℓ.1 ℓ.2).left (Over.w (I.ub ℓ.1 ℓ.2)))
      ((Chart.comb_push hid _ D _).2 (by simp only [Category.comp_id]; exact hu ℓ)) hD (h₂ _ _)
  intro ℓ
  obtain ⟨u, a₁, a₂⟩ := (Chart.comb_push I.m1.cart _ _ _).1 (cb ℓ)
  exact ⟨u, fun i => (a₁ i).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)), a₂.trans (h₁ _ _)⟩


theorem chartJetBasis_holds (hF : FrTanBasisSt Xo c) : ChartJetBasisSt Xo c := by
  intro T io y I d FT actT tgT uvecT xT hb hc hu
  letI := io.toAlgebra
  have hid : IsGrpPullback I.G.G I.G.G (𝟙 _) (𝟙 _) := ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy =>
    (mul_left_congr (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _)) (hy.trans (Category.comp_id _))).trans
      (Category.comp_id _).symm⟩
  let D : Fin d → (epsR T.V ⟶ I.G.G) := fun j => Over.homMk (Formalism.L2.Pj.homAt (𝟙 (Sp T.V))
    (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left
    ((Over.w _).trans (Category.comp_id _))
  let D' : Fin d → (epsR T.Fr ⟶ I.t'.G) := fun j => Over.homMk (spMap ((jetTan ((0 : Fin 1), j) :
    Jet T.Fr (Fin 1 × Fin d) (0 + 1) →ₐ[T.Fr] DualNumber T.Fr) : _ →+* _) ≫ JetTr.xL I xT 1) (by
      rw [Category.assoc, JetTr.xL_snd]; exact spMap_comp_alg _)
  have hD : ∀ j, (D' j).left ≫ I.m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (D j).left := fun j => by
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (JetTr.xL_fst I xT 1)).trans ((Category.assoc _ _ _).symm.trans
      (Eq.trans (congrArg (· ≫ (xT 1).left) ?_) (Category.assoc _ _ _))))
    exact (JetTr.spMap_comp' _ _).trans ((congrArg spMap (tan_coef j)).trans (JetTr.spMap_comp' _ _).symm)
  choose u' h₁ h₂ using I.lift
  have ho : ∀ τ i, u' τ i ≫ I.t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := fun τ i => by
    have : Mono (spMap (algebraMap T.V T.Fr)) := by
      have := IsPreimmersion.of_isLocalization (S := T.Fr) (nonZeroDivisors T.V)
      exact inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))))
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← I.m2.cart.1.w, ← Category.assoc, h₂, Category.assoc,
      Over.w]
    exact (JetTr.spMap_comp' _ _).trans ((congrArg spMap (RingHom.ext fun r => by
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])).trans (JetTr.spMap_comp' _ _).symm)
  let U' : Lt1 Dw → (epsR T.Fr ⟶ I.t'.G) := fun ℓ => Over.homMk (u' ℓ.1 ℓ.2) (ho _ _)
  have cb : ∀ ℓ, IsLieComb (fun i => algebraMap T.V T.Fr (uvecT ℓ i)) D' (U' ℓ) := fun ℓ =>
    Chart.comb_baseChange _ I.m2.cart (w := Over.homMk (I.ub ℓ.1 ℓ.2).left (Over.w (I.ub ℓ.1 ℓ.2)))
      ((Chart.comb_push hid _ D _).2 (by simp only [Category.comp_id]; exact hu ℓ)) hD (h₂ _ _)
  have := I.G.semi.smooth
  have := I.t'.semi.smooth
  let tg : Fin d → (epsR T.V ⟶ I.G.G) := fun j => Over.homMk (tgT j) ((hb.1 j).1.trans (Category.comp_id _))
  have ttg : ∀ j, IsTangent (tg j) := fun j => (Chart.tan_push hid _).2 (by simp only [Category.comp_id]; exact (hb.1 j).2)
  have tD : ∀ j, IsTangent (D j) := fun j => (Chart.tan_push hid _).2 (by
    have e := congrArg (fun q => q.left) (hc.zero 1)
    refine Eq.trans ?_ (e.trans ?_)
    · rw [Category.comp_id]
      refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (xT 1).left) ((JetTr.spMap_comp' _ _).trans (congrArg spMap ?_)))
      apply Ideal.Quotient.ringHom_ext
      apply MvPolynomial.ringHom_ext
      · intro r
        show (MvPolynomial.aeval _ (MvPolynomial.C r) : DualNumber T.V).fst = MvPolynomial.aeval _ (MvPolynomial.C r)
        rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]; rfl
      · intro s
        show (MvPolynomial.aeval _ (MvPolynomial.X s) : DualNumber T.V).fst = MvPolynomial.aeval _ (MvPolynomial.X s)
        rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
        split_ifs <;> rfl
    · exact congrArg (· ≫ _) (show Spec.map (CommRingCat.ofHom (RingHom.id T.V)) ≫ 𝟙 _ = 𝟙 _ by simp))
  have eD : tg = D := funext fun j => Chart.eq_of_comb_single tD (ttg j) j
    ((Chart.comb_push hid _ D _).2 (by simp only [Category.comp_id]; exact hc.tan j))
  have bD : IsLieBasis D := eD ▸ ⟨ttg, fun w hw => by
    have := hb.2 w.left ⟨(Over.w w).trans (Category.comp_id _).symm, by
      simpa only [Category.comp_id] using (Chart.tan_push hid w).1 hw⟩
    simp only [Chart.comb_push hid, Category.comp_id]
    exact this⟩
  have bD' : IsLieBasis D' := Chart.isLieBasis_baseChange _ I.m2.cart bD hD
  let e := Fintype.equivFin (Lt1 Dw)
  have bU : IsLieBasis fun i => U' (e.symm i) := ⟨fun i => (Chart.tan_push I.m1.cart _).2
    ((congrArg (_ ≫ ·) (h₁ _ _)).trans (y.1.tan _ _).2), fun w hw => by
      obtain ⟨a, ha, hq⟩ := hF T.Fr y.1 (w.left ≫ I.m1.φ) ⟨Over.w (pushPt I.m1.cart.1.w w), (Chart.tan_push I.m1.cart w).1 hw⟩
      have k : ∀ b, IsLieComb b (fun i => U' (e.symm i)) w ↔ IsCombAt y.1.x (fun i => y.1.u (e.symm i).1 (e.symm i).2) b
          (w.left ≫ I.m1.φ) := fun b => (Chart.comb_push I.m1.cart _ _ _).trans (exists_congr fun u => and_congr_left'
        (forall_congr' fun i => Eq.congr_right (congrArg (_ ≫ ·) (h₁ _ _))))
      refine ⟨fun i => a (e.symm i), (k _).2 ha, fun b hb' => ?_⟩
      have := hq (fun ℓ => b (e ℓ)) (by simpa only [e, Equiv.apply_symm_apply] using (k b).1 hb')
      funext i; rw [← this]; simp⟩
  intro v
  obtain ⟨a, ha, hq⟩ := Chart.coords_basis bD' bU _ (fun i => cb (e.symm i)) v
  refine ⟨fun ℓ => a (e ℓ), fun j => (Fintype.sum_equiv e _ _ fun ℓ => by simp).trans (ha j), fun b hb' => ?_⟩
  have := hq (fun i => b (e.symm i)) fun j => (Fintype.sum_equiv e.symm _ _ fun i => rfl).trans (hb' j)
  funext ℓ; rw [← this]; simp

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA

open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

variable {R : Type} [CommRing R]

theorem coeff_eq_of_psJet {ι : Type} [Fintype ι] [DecidableEq ι] {D : ℕ} {a b : MvPowerSeries ι R}
    (h : psJet D a = psJet D b) {e : ι →₀ ℕ} (he : e.degree ≤ D) :
    MvPowerSeries.coeff e a = MvPowerSeries.coeff e b := by
  have h' : Ideal.Quotient.mk (orig R ι ^ (D + 1)) (psTrunc D a) =
      Ideal.Quotient.mk (orig R ι ^ (D + 1)) (psTrunc D b) := h
  have hm := Ideal.Quotient.eq.mp h'
  have h0 := coeff_eq_zero_of_mem hm (show e.degree < D + 1 by omega)
  rw [MvPolynomial.coeff_sub, coeff_psTrunc D a e he, coeff_psTrunc D b e he] at h0
  exact sub_eq_zero.mp h0

theorem psJet_subst_congr {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] (D : ℕ)
    (a : σ → MvPowerSeries τ R) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) {f g : MvPowerSeries σ R}
    (h : psJet D f = psJet D g) : psJet D (MvPowerSeries.subst a f) = psJet D (MvPowerSeries.subst a g) := by
  rw [psJet_subst D a ha f, psJet_subst D a ha g, h]

def psJetM {ι : Type} [Fintype ι] [DecidableEq ι] (D : ℕ) : MvPowerSeries ι R →* Jet R ι D where
  toFun := psJet D
  map_one' := psJet_one D
  map_mul' := psJet_mul D

theorem psJet_prod_congr {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] (D : ℕ)
    {f g : κ → MvPowerSeries ι R} (h : ∀ b, psJet D (f b) = psJet D (g b)) :
    psJet D (∏ b, f b) = psJet D (∏ b, g b) := by
  change psJetM D (∏ b, f b) = psJetM D (∏ b, g b)
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun b _ => h b

theorem subst_exp {σ τ : Type} [Finite σ] [Algebra ℚ R] (a : σ → MvPowerSeries τ R)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (g : MvPowerSeries σ R)
    (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.subst a (PowerSeries.subst g (PowerSeries.exp R)) =
      PowerSeries.subst (MvPowerSeries.subst a g) (PowerSeries.exp R) := by
  exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp a ha hg

end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2b

open MvPolynomial Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

theorem bal_of {P : MvPolynomial (Fin 2 × Fin d) S} {m : ℕ} (hm : 2 ≤ m) (B A Ab : Fin d → Fin d → S)
    (h2 : P - 1 ∈ Io S (Fin 2 × Fin d) ^ 2) (h3 : P - 1 - bil B ∈ Io S (Fin 2 × Fin d) ^ 3)
    (aW0 aB1 : Fin d → MvPolynomial (Fin 2 × Fin d) S)
    (hW0 : ∀ i, aW0 i - lin A (0 : Fin 2) i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hB1 : ∀ i, aB1 i - lin Ab (1 : Fin 2) i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hbal : ev2 P aW0 (xs S d 1) - ev2 P (xs S d 0) aB1 ∈ Io S (Fin 2 × Fin d) ^ (m + 1)) :
    Matrix.transpose (Matrix.of A) * Matrix.of B = Matrix.of B * Matrix.of Ab := by
  set W := P - 1 with hWdef
  set h := bil B with hhdef
  have hhI : h ∈ Io S (Fin 2 × Fin d) ^ 2 := bil_mem B
  have hh : h.IsHomogeneous 2 := bil_hom B
  have hmj : ∀ {p : MvPolynomial (Fin 2 × Fin d) S}, p ∈ Io S _ ^ (m + 1) → p ∈ Io S _ ^ (2 + 1) :=
    fun hp => Ideal.pow_le_pow_right (by omega) hp
  have hsq : ∀ {p : MvPolynomial (Fin 2 × Fin d) S}, p ∈ Io S _ ^ 2 → p ∈ Io S _ :=
    fun hp => Ideal.pow_le_self two_ne_zero hp
  have hPW : ∀ (u v : Fin d → MvPolynomial (Fin 2 × Fin d) S), ev2 P u v = 1 + ev2 W u v := by
    intro u v; rw [hWdef, eval_pair_sub, eval_pair_one]; ring
  have hTr : ∀ (u v : Fin d → MvPolynomial (Fin 2 × Fin d) S), (∀ i, u i ∈ Io S _) → (∀ i, v i ∈ Io S _) →
      ev2 W u v - ev2 h u v ∈ Io S _ ^ (2 + 1) := by
    intro u v hu hv
    rw [← eval_pair_sub]
    exact aeval_mem_pow _ (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv]) _ h3
  have hRep : ∀ (u v u' v' : Fin d → MvPolynomial (Fin 2 × Fin d) S), (∀ i, u i ∈ Io S _) →
      (∀ i, v i ∈ Io S _) → (∀ i, u' i ∈ Io S _) → (∀ i, v' i ∈ Io S _) → (∀ i, u i - u' i ∈ Io S _ ^ 2) →
      (∀ i, v i - v' i ∈ Io S _ ^ 2) → ev2 h u v - ev2 h u' v' ∈ Io S _ ^ (2 + 1) := by
    intro u v u' v' hu hv hu' hv' huu hvv
    exact aeval_sub_mem_pow _ _ (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv])
      (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu', hv'])
      (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [huu, hvv]) 2 h hhI
  have hx : ∀ (k : Fin 2) (i : Fin d), xs S d k i ∈ Io S (Fin 2 × Fin d) := fun k i => xs_mem k i
  have hl : ∀ (M : Fin d → Fin d → S) (k : Fin 2) (i : Fin d), lin M k i ∈ Io S (Fin 2 × Fin d) :=
    fun M k i => lin_mem M k i
  have haW0 : ∀ i, aW0 i ∈ Io S _ := fun i => by
    have := add_mem (hsq (hW0 i)) (hl A 0 i); simpa using this
  have haB1 : ∀ i, aB1 i ∈ Io S _ := fun i => by
    have := add_mem (hsq (hB1 i)) (hl Ab 1 i); simpa using this
  have hb1 : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) = ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) := by
    have k : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) ∈
        Io S _ ^ (2 + 1) := by
      have e : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) =
          (ev2 P aW0 (xs S d 1) - ev2 P (xs S d 0) aB1) -
          (ev2 W aW0 (xs S d 1) - ev2 h aW0 (xs S d 1)) + (ev2 W (xs S d 0) aB1 - ev2 h (xs S d 0) aB1) -
          (ev2 h aW0 (xs S d 1) - ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2))) +
          (ev2 h (xs S d 0) aB1 - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2))) := by
        rw [hPW, hPW]; ring
      rw [e]
      exact add_mem (sub_mem (add_mem (sub_mem (hmj hbal) (hTr _ _ haW0 (hx 1))) (hTr _ _ (hx 0) haB1))
        (hRep _ _ _ _ haW0 (hx 1) (hl A 0) (hx 1) hW0 (fun i => by simp)))
        (hRep _ _ _ _ (hx 0) haB1 (hx 0) (hl Ab 1) (fun i => by simp) hB1)
    exact sub_eq_zero.1 (eq_zero_of_isHomogeneous
      ((eval_pair_homogeneous hh _ _ (lin_hom A 0) (xs_hom 1)).sub (eval_pair_homogeneous hh _ _ (xs_hom 0) (lin_hom Ab 1))) k)
  ext i0 l0
  have hc := congrArg (AddMonoidAlgebra.coeff · (sil i0 l0)) hb1
  rw [hhdef, eval_pair_bilinear, eval_pair_bilinear, coeff_linL, coeff_linR] at hc
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  exact hc

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2b
end
end
