module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3401
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle799
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013

@[expose] public section

section

namespace GlobalTheory.SiegJoin

theorem chartSt5_holds : ChartSt5 :=
  fun g hg φ h₁ h₂ n hn ho F Z z i OZ d S π j _ BD hM hB =>
    ⟨GlobalTheory.T.smoothOfRelativeDimension_blowAt_comp g hg φ h₁ h₂ n hn ho F Z z i OZ d S π j BD hM hB,
      GlobalTheory.T.exists_preChart_siegel_normalizedBlowup g hg φ h₁ h₂ n hn ho F Z z i OZ d S π j BD hM hB⟩

end GlobalTheory.SiegJoin
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart

theorem uPre_of_boundary {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (hpq : 1 ≤ Dw.p + Dw.q)
    (hφ : IsPolFan H.bar (min Dw.p Dw.q) φ) (hns : NoSelfInt H.bar (min Dw.p Dw.q) φ)
    {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData)
    {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S)
    (hP : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD) (hS : SepB Xo c φ j)
    (x : S) (hx : x ∉ Set.range j) : UPre Xo c φ j BD d x :=
  GlobalTheory.T.exists_tripleChart_unitary_boundary_pointRigid Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS x hx

end GlobalTheory.UChart
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.exists_rep_principalSiegel_adjoint_orderAction : ∀ (h' M : ℕ), 1 ≤ h' → 3 ≤ M → Odd M → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (eO : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range eO) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d₀ → ∑ i, ∑ j, W i j • (eO j * bar (eO i)) = (d₀ : O) → ∃ (H : Scheme.{0}) (sH : H ⟶ Sp (cycAway M)) (zH : SiegPre h' M (zetaAway M) sH) (actH : O → (zH.A ⟶ zH.A)), zH.Principal ∧ IsRAct zH.A actH ∧ Adj zH.A zH.P bar actH ∧ IsQProjOver sH ∧ IsLocallyNoetherian H ∧ ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), z.Principal → IsRAct z.A act → Adj z.A z.P bar act → ∃! g : S ⟶ H, g ≫ sH = t ∧ ActPB z act zH actH g := by
  first | (exact @GlobalTheory.ActSieg.exists_rep) | (exact GlobalTheory.ActSieg.exists_rep) | (intros; apply GlobalTheory.ActSieg.exists_rep  <;> assumption)
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

theorem inv_sch (q : ℕ) (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) : Inv q (sch.obj U) := by
  intro U' ⟨f⟩
  simpa using hU.map f.appTop.hom

theorem pbf_disc : ∀ (q : ℕ) [NeZero q] (N : ℕ) (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)),
    Inv q (disc.obj F) → PBF q V := by
  intro q _ N F V hF n i
  obtain ⟨J, ψ, hJ, hinj, he⟩ := GlobalTheory.T.exists_injective_cochainModel_trivialProjectiveBundle q N i
  have key := GlobalTheory.T.injectiveComplexMap_quasiIso_of_unit_schemes q (fun j : Fin N => res (ZMod q) (tw q (i - (j : ℕ)))) J (fun j => 2 * ((j : ℕ) : ℤ)) ψ 0
    (fun j => inferInstanceAs ((injectiveResolution (tw q (i - (j : ℕ)))).cochainComplex.IsStrictlyGE 0)) hJ
    (fun j m => inferInstanceAs (Injective ((injectiveResolution (tw q (i - (j : ℕ)))).cochainComplex.X m))) hinj
    (by
      intro U hU m
      obtain ⟨e, he'⟩ := he (yoneda.obj U) (inv_sch q U hU) m
      have hs := GlobalTheory.T.etaleCohomology_projectiveBundle_formula q U (trivV N (sch.obj U)) (inv_sch q U hU) m i
      have hcomp : (fun a : ∀ j : Fin N, Ht q (sch.obj U) (m - 2 * (j : ℕ)) (i - (j : ℕ)) =>
          ∑ j : Fin N, ((cup q (pull _ (pullback.fst (trivV N (sch.obj U)) (PGL.pr N)) _ _ (a j))
            (cpow q (c1 q (pullback.snd (trivV N (sch.obj U)) (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) :
              Ht q _ m i)) = e ∘ (fun a => ∑ j, cpost _ (ψ j) (m - 2 * (j : ℕ)) m (by omega) (a j)) :=
        funext fun a => (he' a).symm
      rw [hcomp] at hs
      exact (Function.Bijective.of_comp_iff' e.bijective _).1 hs)
    F hF n
  obtain ⟨e, he'⟩ := he F hF n
  rw [GlobalTheory.T.discrete_glBundle_eq_trivialGLBundle N F V]
  have hcomp : pbfMap q (trivV N (disc.obj F)) n i =
      e ∘ (fun a => ∑ j, cpost _ (ψ j) (n - 2 * (j : ℕ)) n (by omega) (a j)) :=
    funext fun a => (he' a).symm
  rw [hcomp]
  exact e.bijective.comp key

end GlobalTheory.EtC

end
end
