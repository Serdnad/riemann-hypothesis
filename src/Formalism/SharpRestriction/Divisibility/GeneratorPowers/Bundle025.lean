module

import Formalism.SharpRestriction.Divisibility.GeneratorPowers.EvalSinglePointId
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle018
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTieAlg
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle020
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.HarmInvB
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle023
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSEqJetMap
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ExpLaw
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpOfPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
  Formalism.L2.Pj CIndFrFix
open ReciprocityTheory.ChartRestriction.G.TB.LogPf (logOf)

def HarmKillJetSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l)
    (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (k n D : ℕ)
    (g g' : Fin n → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (β : Matrix (Fin (dL Dw)) (Fin (dL Dw)) S),
    (∀ i j, β i j ≠ 0 → ((ltIdx Dw).symm j).1 = ComplexEmbedding.conjugate ((ltIdx Dw).symm i).1) →
    (∀ b, psJet D (g' b) =
      psJet D (g b * PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β) (PowerSeries.exp S))) →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      (∀ m ∈ P.support, m.degree ≤ D) →
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g' b) (colOf m b) =
        ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g b) (colOf m b)

namespace HarmInvPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

theorem tie_val (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : IsExpOf C.B.G.F C.uvec φ) (k : ℕ) {n : ℕ} (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S)
    (P : MvPolynomial (LtN Dw n) c.F) :
    chartVal C k f P = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
      ∏ b, expVal (compL φ (f b * FB.expS S ((k : S) • C.B.hL S C.h H.w0))) (colOf m b) := by

  have hFK : C.B.FK S = C.B.G.F := by
    funext i
    first
      | simp [FB.FK, FGLaw.mapF]
      | (ext n; simp [FB.FK, FGLaw.mapF, MvPowerSeries.coeff_map])
  have hφ' : IsExpOf (C.B.FK S) C.uvec φ := by
    rw [hFK]
    exact hφ
  unfold chartVal
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  exact tie_alg (C.B.FK S) C.uvec φ hφ' (colOf m b) _

theorem cc_diagL {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB S d O) (w0 : O) (cc : Fin d → Fin d → S) :
    MvPowerSeries.constantCoeff (diagL B w0 cc) = 0 := by
  apply Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3.const_diagL <;> assumption

end HarmInvPf


open HarmInvPf in
theorem harmInv_of_kill (hK : HarmKillJetSt) (hA : ExpActOfSt) : HarmInvSt := by
  intro E _ _ _ H Dw l Xo c _ hs S _ _ _ y C cc hsym hbal k n D f f' hj a P hP hD
  obtain ⟨h0, h1, hadd⟩ := HarmInvB.logOf_props C.B.G
  obtain ⟨ε, hinv, htr⟩ := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.formal_exp_law S C.d C.B.G (fun i => logOf C.B.G i) h0 h1 hadd
  have hφ := isExpOf_expPhi C.B.G C.uvec (fun i => logOf C.B.G i) ε h1 hinv htr
  set φ := ExpOf.expPhi C.uvec ε with hφdef
  set t : Fin 1 × Fin (dL Dw) → S := fun q => algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 H.w0) with ht
  have hta : ∀ q, MvPowerSeries.constantCoeff
      (t q • (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) = 0 :=
    fun q => by rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
  have hact : ∀ j, MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act H.w0 j) =
      MvPowerSeries.subst (fun q => t q • (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) (φ j) :=
    fun j => hA E H Dw l Xo c S y C φ hφ H.w0 j
  have hcd : MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (diagL C.B H.w0 cc) =
      ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) (HarmInvB.qβ cc C.uvec t) := by
    have e := HarmInvB.compL_diagL C.B H.w0 cc C.uvec ε hinv _ hta hact
    rw [HarmInvB.quad_form] at e
    exact e
  have hφs : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin C.d => φ p.2) :=
    HarmInvB.hasSubst0 fun p => hφ.const p.2
  have hccd : MvPowerSeries.constantCoeff ((k : S) • diagL C.B H.w0 cc) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, cc_diagL, mul_zero]
  set EL := FB.expS S ((k : S) • C.B.hL S C.h H.w0) with hEL
  have hjet : ∀ b, psJet D (compL φ (f' b * EL)) = psJet D (compL φ (f b * EL) *
      PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) (HarmInvB.qβ cc C.uvec t))
        (PowerSeries.exp S)) := by
    intro b
    have e1 : psJet D (f' b * EL) = psJet D (f b * expP ((k : S) • diagL C.B H.w0 cc) * EL) := by
      rw [FBIdJet.psJet_mul, hj b, ← FBIdJet.psJet_mul]
    have e2 := HarmInvA.psJet_subst_congr D (fun p : Fin 1 × Fin C.d => φ p.2) (fun p => hφ.const p.2) e1
    have e3 : MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2)
        (f b * expP ((k : S) • diagL C.B H.w0 cc) * EL) = compL φ (f b * EL) *
          PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) (HarmInvB.qβ cc C.uvec t))
            (PowerSeries.exp S) := by
      rw [MvPowerSeries.subst_mul hφs, MvPowerSeries.subst_mul hφs, expP,
        HarmInvA.subst_exp _ (fun p => hφ.const p.2) _ hccd, MvPowerSeries.subst_smul hφs, hcd, compL,
        MvPowerSeries.subst_mul hφs]
      ring
    exact e2.trans (congrArg (psJet D) e3)
  have hβ : ∀ i j, HarmInvB.qβ cc C.uvec t i j ≠ 0 →
      ((ltIdx Dw).symm j).1 = ComplexEmbedding.conjugate ((ltIdx Dw).symm i).1 := by
    intro i j hne
    refine hbal ((ltIdx Dw).symm i) ((ltIdx Dw).symm j) fun h0' => hne ?_
    have e : HarmInvB.qβ cc C.uvec t i j = (∑ a, ∑ b, cc a b * C.uvec ((ltIdx Dw).symm i) a *
        C.uvec ((ltIdx Dw).symm j) b) * t (0, j) := by
      simp only [HarmInvB.qβ, Finset.sum_mul]
    rw [e, h0', zero_mul]
  rw [tie_val C φ hφ k f' P, tie_val C φ hφ k f P]
  exact hK E H Dw l c S k n D (fun b => compL φ (f b * EL)) (fun b => compL φ (f' b * EL))
    (HarmInvB.qβ cc C.uvec t) hβ hjet a P hP hD

theorem harmInv_of (hA : ExpActOfSt) : HarmInvSt :=
  harmInv_of_kill (fun _ _ _ _ _ _ _ c _ _ _ _ k n D g g' β hβ hj a P hP hD =>
    HarmInvC.harm_kill_jet c k n D g g' β hβ hj a P hP hD) hA

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG

open MvPowerSeries NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {S : Type} [CommRing S] (c : Coeff l) [Algebra c.F S]

theorem const_actPS (a : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) : constantCoeff (actPS (Dw := Dw) (S := S) c a q) = 0 := by
  simp [actPS]

theorem hasSubst_actPS (a : 𝓞 E) : HasSubst (actPS (Dw := Dw) (S := S) c a) :=
  hasSubst_of_constantCoeff_zero (fun q => const_actPS c a q)

theorem actPS_comp (u v : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) :
    subst (actPS (Dw := Dw) (S := S) c v) (actPS (Dw := Dw) (S := S) c u q) = actPS (Dw := Dw) (S := S) c (u * v) q := by
  have hv := hasSubst_actPS (Dw := Dw) (S := S) c v
  have e : actPS (Dw := Dw) (S := S) c u q =
      algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 u) • MvPowerSeries.X q := rfl
  rw [e, subst_smul hv, subst_X hv]
  simp only [actPS, smul_smul, map_mul]

theorem φa_mul {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (u v : 𝓞 E) (j : Fin d) :
    subst (actPS (Dw := Dw) c v) (φa c φ u j) = φa c φ (u * v) j := by
  simp only [φa]
  rw [subst_comp_subst_apply (hasSubst_actPS c u) (hasSubst_actPS c v)]
  congr 1
  funext q
  exact actPS_comp c u v q

theorem φa_one {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) : φa c φ 1 = φ := by
  have e : actPS (Dw := Dw) (S := S) c 1 = MvPowerSeries.X := by
    funext q
    simp [actPS]
  funext j
  simp only [φa, e, subst_self, id]

theorem actPS_add (u v : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) :
    actPS (Dw := Dw) (S := S) c u q + actPS (Dw := Dw) (S := S) c v q = actPS (Dw := Dw) (S := S) c (u + v) q := by
  simp only [actPS, map_add (f := _), add_smul]

theorem const_φa {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (hφ : ∀ j, constantCoeff (φ j) = 0)
    (u : 𝓞 E) (j : Fin d) : constantCoeff (φa c φ u j) = 0 :=
  ExpGF.const_substPS _ (fun q => const_actPS c u q) _ (hφ j)

theorem law_φa {d : ℕ} {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {uvec : Lt1 Dw → Fin d → S}
    {φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S} (hφ : IsExpOf F uvec φ) (u v : 𝓞 E) (j : Fin d) :
    subst (fun p : Fin 2 × Fin d => φa c φ (![u, v] p.1) p.2) (F j) = φa c φ (u + v) j := by
  let b : Fin 2 × Fin (dL Dw) → MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
    fun p => actPS (Dw := Dw) (S := S) c (![u, v] p.1) ((0 : Fin 1), p.2)
  have hb : HasSubst b := hasSubst_of_constantCoeff_zero (fun p => const_actPS c _ _)
  have hX : ∀ i : Fin 2, HasSubst (fun q : Fin 1 × Fin (dL Dw) =>
      (MvPowerSeries.X (i, q.2) : MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) :=
    fun i => hasSubst_of_constantCoeff_zero (fun q => by simp)
  have hA : HasSubst (fun p : Fin 2 × Fin d => atPt p.1 (φ p.2)) :=
    hasSubst_of_constantCoeff_zero (fun p => ExpGF.const_substPS _ (fun q => by simp) _ (hφ.const p.2))
  have hS : HasSubst (fun q : Fin 1 × Fin (dL Dw) =>
      (MvPowerSeries.X ((0 : Fin 2), q.2) + MvPowerSeries.X ((1 : Fin 2), q.2) :
        MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) :=
    hasSubst_of_constantCoeff_zero (fun q => by simp)
  have key := congrArg (MvPowerSeries.subst b) (hφ.hom j)
  rw [subst_comp_subst_apply hA hb, subst_comp_subst_apply hS hb] at key
  have e1 : (fun p : Fin 2 × Fin d => MvPowerSeries.subst b (atPt p.1 (φ p.2))) =
      fun p => φa c φ (![u, v] p.1) p.2 := by
    funext ⟨i, k⟩
    simp only [atPt, φa]
    rw [subst_comp_subst_apply (hX i) hb]
    congr 1
    funext ⟨q1, q2⟩
    rw [subst_X hb]
    have h1 : q1 = 0 := Subsingleton.elim _ _
    subst h1
    rfl
  have e2 : (fun q : Fin 1 × Fin (dL Dw) => MvPowerSeries.subst b
      (MvPowerSeries.X ((0 : Fin 2), q.2) + MvPowerSeries.X ((1 : Fin 2), q.2) :
        MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) = actPS (Dw := Dw) (S := S) c (u + v) := by
    funext ⟨q1, q2⟩
    have h1 : q1 = 0 := Subsingleton.elim _ _
    subst h1
    rw [subst_add hb, subst_X hb, subst_X hb]
    exact actPS_add c u v _
  rw [e1, e2] at key
  exact key

theorem act_φa {d : ℕ} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
    {φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S} (hφ : ∀ j, constantCoeff (φ j) = 0)
    (hact : ∀ a j, subst (fun p : Fin 1 × Fin d => φ p.2) (act a j) = subst (actPS (Dw := Dw) c a) (φ j))
    (a u : 𝓞 E) (j : Fin d) :
    subst (fun p : Fin 1 × Fin d => φa c φ u p.2) (act a j) = φa c φ (a * u) j := by
  have hP : HasSubst (fun p : Fin 1 × Fin d => φ p.2) :=
    hasSubst_of_constantCoeff_zero (fun p => hφ p.2)
  have h := subst_comp_subst_apply hP (hasSubst_actPS (Dw := Dw) (S := S) c u) (act a j)
  rw [hact a j] at h
  exact h.symm.trans (φa_mul c φ a u j)

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
end
end
