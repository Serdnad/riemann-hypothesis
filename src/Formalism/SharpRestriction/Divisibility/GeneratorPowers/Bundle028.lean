module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle026
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ScaleGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle027
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GmHomAt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle025
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSEqJetMap
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSTrunc
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace CIndNab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

theorem thExpr_eq (hU : ThExprUniqSt) [StarRing (𝓞 E)] (nab nab' : NabV Xo c) (h : IsNab Xo c nab)
    (h' : IsNab Xo c nab') {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ}
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x))) :
    thExpr Xo c nab y P F = thExpr Xo c nab' y P F := by
  letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  have key : ∀ (K : ℤ) (k : ℕ), K = (k : ℤ) →
      ∀ G : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x)),
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y K (G b) (colOf m b) =
        ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab' y K (G b) (colOf m b) := by
    rintro K k rfl G
    exact hU E H Dw l Xo c nab nab' h h' S y k n G a P hP
  unfold thExpr
  congr 1
  exact key _ (l.M ^ 2) (Nat.cast_pow l.M 2).symm F

theorem thValAt_iff (hU : ThExprUniqSt) [StarRing (𝓞 E)] (nab nab' : NabV Xo c) (h : IsNab Xo c nab)
    (h' : IsNab Xo c nab') {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ}
    (x : Fin n → Dw.La) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n)
    (v : S) : ThValAt Xo c nab y x P v ↔ ThValAt Xo c nab' y x P v := by
  constructor
  · rintro ⟨S', i1, i2, φ, y', F, hff, hmap, hvt, hv⟩
    exact ⟨S', i1, i2, φ, y', F, hff, hmap, hvt, hv.trans (thExpr_eq Xo c hU nab nab' h h' y' a P hP F)⟩
  · rintro ⟨S', i1, i2, φ, y', F, hff, hmap, hvt, hv⟩
    exact ⟨S', i1, i2, φ, y', F, hff, hmap, hvt, hv.trans (thExpr_eq Xo c hU nab nab' h h' y' a P hP F).symm⟩

end CIndNab


open CIndNab in
theorem nabUniq_of_chartIndep2 (hC : ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) : NabUniq Xo c := by
  intro _ nab nab' h h' a n _
  have hU := thExprUniq_of_chartIndep2 hC
  refine Set.ext fun f => ⟨?_, ?_⟩
  · rintro ⟨x, P, hP, hf⟩
    exact ⟨x, P, hP, fun p y => (thValAt_iff Xo c hU nab nab' h h' y x a P hP _).1 (hf p y)⟩
  · rintro ⟨x, P, hP, hf⟩
    exact ⟨x, P, hP, fun p y => (thValAt_iff Xo c hU nab nab' h h' y x a P hP _).2 (hf p y)⟩

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGK

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
  Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

theorem expS_actPS {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (g : MvPowerSeries (Fin 1 × Fin d) S)
    (hg : MvPowerSeries.constantCoeff g = 0) (k : 𝓞 E) :
    MvPowerSeries.subst (actPS (Dw := Dw) (S := S) c k) (Germ.FB.expS S (-(compL φ g))) =
      Germ.FB.expS S (-(compL (φa c φ k) g)) := by
  have hb : MvPowerSeries.HasSubst (actPS (Dw := Dw) (S := S) c k) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => by simp [actPS]
  have ha : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => φ p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => hφ p.2
  have h0 : MvPowerSeries.constantCoeff (-(compL φ g)) = 0 := by
    rw [map_neg, ExpGB.const_compL φ hφ g, hg, neg_zero]
  have hcomp : MvPowerSeries.subst (actPS (Dw := Dw) (S := S) c k) (-(compL φ g)) =
      -(compL (φa c φ k) g) := by
    rw [← MvPowerSeries.coe_substAlgHom hb, map_neg, MvPowerSeries.coe_substAlgHom hb]
    unfold compL φa
    rw [MvPowerSeries.subst_comp_subst_apply ha hb]
  unfold Germ.FB.expS PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero h0).const hb]
  simp only [hcomp]

theorem val_e (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (hact : ∀ a j, MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
      MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j))
    (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)))
    (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ)
    (hτc : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (τ m) (eL y C.d C.x C.B.A.act C.e C.wP m))
    (m : ℕ) (z : (jO y (dL Dw) m 1).left)
    (J : ((jO y (dL Dw) m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) (hJ : Good Xo.univ.t.PP.L z J) :
    val (ExpGA.eG C φ τ u m) (𝟙 _) z J =
      gm (𝟙 _) z ⊤ (unitΓ (u m)) *
        (val C.wP ((ptm C ![φ] m).left ≫ (C.x m).left) z J *
          val (C.e m) (ptm C ![φ, φa c φ H.w0] m).left z J) := by
  have hX : actP (Dw := Dw) (S := S) c 1 = fun p => MvPolynomial.X p := by
    funext p
    simp [actP]
  have hid : jetSubstP m (actP (Dw := Dw) (S := S) c 1) = AlgHom.id S _ := by
    rw [hX]
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp [jetSubstP, jetMap, liftJet, Ideal.Quotient.lift_mk, MvPolynomial.aeval_X_left] <;> rfl
  have hP : actPS (Dw := Dw) (S := S) c 1 = MvPowerSeries.X := by
    funext q
    simp [actPS]
  have hφ1 : φa c φ 1 = φ := by
    funext j
    simp only [φa, hP]
    exact congrFun MvPowerSeries.subst_self (φ j)
  have hu : Units.map (AlgHom.id S (Jet S (Fin 1 × Fin (dL Dw)) m)).toMonoidHom (u m) = u m :=
    Units.ext rfl
  have h1 := val_eAt C φ hφ hact τ u hτc m 1 z J hJ
  rw [hφ1, _root_.mul_one] at h1
  unfold eAt at h1
  rw [val_pull, hid, homAt_id, Over.id_left, Category.comp_id, hu] at h1
  exact h1
  exact hJ

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGK
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH

attribute [local instance] Over.cartesianMonoidalCategory

section Help

variable {S : Type} [CommRing S] {d n : ℕ}

private theorem subst_rename_lemma {σ τ υ R : Type} [CommRing R] [Finite σ] [Finite τ]
    (a : σ → MvPowerSeries υ R) (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ρ : τ → σ)
    (q : MvPolynomial τ R) :
    MvPowerSeries.subst a ((MvPolynomial.rename ρ q : MvPolynomial σ R) : MvPowerSeries σ R) =
      MvPowerSeries.subst (fun t => a (ρ t)) (q : MvPowerSeries τ R) := by
  have h1 : MvPowerSeries.HasSubst a := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero ha
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
  have h2 : MvPowerSeries.HasSubst (fun t => a (ρ t)) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun t => ha (ρ t))
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun t => ha (ρ t))
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun t => by rw [ha (ρ t)]; exact IsNilpotent.zero)
  rw [← MvPowerSeries.coe_substAlgHom h1, ← MvPowerSeries.coe_substAlgHom h2]
  erw [MvPowerSeries.substAlgHom_coe, MvPowerSeries.substAlgHom_coe, MvPolynomial.aeval_rename]
  rfl

theorem cc_psIn (m : ℕ) (i : Fin n) (g : MvPowerSeries (Fin 1 × Fin d) S) (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPolynomial.constantCoeff (psIn d m ![i] g) = 0 := by
  simp only [psIn, MvPolynomial.constantCoeff_rename, ExpGB.cc_psTrunc', hg]

theorem psJet_subst_psIn {ι' : Type} [Fintype ι'] [DecidableEq ι'] (m : ℕ) (i : Fin n)
    (Q : Fin n × Fin d → MvPowerSeries ι' S) (hQ : ∀ p, MvPowerSeries.constantCoeff (Q p) = 0)
    (g : MvPowerSeries (Fin 1 × Fin d) S) :
    psJet m (MvPowerSeries.subst Q ((psIn d m ![i] g : MvPolynomial (Fin n × Fin d) S) : MvPowerSeries (Fin n × Fin d) S)) =
      psJet m (MvPowerSeries.subst (fun p : Fin 1 × Fin d => Q (i, p.2)) g) := by
  simp only [psIn]
  rw [subst_rename_lemma Q hQ, ExpGF.psJet_subst_trunc m _ (fun _ => hQ _) g]
  congr 1
  congr 1
  funext p
  simp

end Help


theorem adVal : AdValSt := by
  intro E _ _ _ H Dw l Xo c _ S _ _ _ y C φ hφ hx hact a' wL hrel m u0 u1 z J hJ
  have hφ0 : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0 := hφ.const
  obtain ⟨u, hu, hc⟩ := hrel m
  let P : Fin 2 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S := ![φa c φ u0, φa c φ u1]
  have hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0 := by
    rw [Fin.forall_fin_two]
    exact ⟨fun j => const_φa c φ hφ0 u0 j, fun j => const_φa c φ hφ0 u1 j⟩
  let Q : Fin 2 × Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S := fun p => P p.1 p.2
  have hQ : ∀ p, MvPowerSeries.constantCoeff (Q p) = 0 := fun p => hP p.1 p.2
  have hQs : MvPowerSeries.HasSubst Q := MvPowerSeries.hasSubst_of_constantCoeff_zero hQ
  have hQ0 : ∀ j, Q ((0 : Fin 2), j) = φa c φ u0 j := fun j => rfl
  have hQ1 : ∀ j, Q ((1 : Fin 2), j) = φa c φ u1 j := fun j => rfl

  have hpt : (ptm C P m).left ≫ (lift (jpt y C.d C.x m (0 : Fin 2)) (jpt y C.d C.x m (1 : Fin 2))).left =
      (xExp y C φ m).left ≫ (lift (Xo.univ.t.act.act u0) (Xo.univ.t.act.act u1)).left := by
    have hPe : (fun k => φa c φ ((![u0, u1] : Fin 2 → 𝓞 E) k)) = P := by
      funext k
      refine Fin.cases rfl (fun k' => ?_) k
      rw [Fin.fin_one_eq_zero k']
      rfl
    have e0 := ptm_jpt C φ hφ0 hx m ![u0, u1] 0
    have e1 := ptm_jpt C φ hφ0 hx m ![u0, u1] 1
    rw [hPe] at e0 e1
    rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, e0, e1]
    rfl

  let σa : Fin 2 × Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S := fun p =>
    (![fun j => psIn C.d m ![0] (C.B.A.act a' j), fun j => MvPolynomial.X ((1 : Fin 2), j)] :
      Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2
  let σb : Fin 2 × Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S := fun p =>
    (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a') j)] :
      Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2
  have ea0 : ∀ j, σa ((0 : Fin 2), j) = psIn C.d m ![0] (C.B.A.act a' j) := fun j => rfl
  have ea1 : ∀ j, σa ((1 : Fin 2), j) = MvPolynomial.X ((1 : Fin 2), j) := fun j => rfl
  have eb0 : ∀ j, σb ((0 : Fin 2), j) = MvPolynomial.X ((0 : Fin 2), j) := fun j => rfl
  have eb1 : ∀ j, σb ((1 : Fin 2), j) = psIn C.d m ![1] (C.B.A.act (H.bar a') j) := fun j => rfl
  have hσa : ∀ k, MvPolynomial.constantCoeff (σa k) = 0 := by
    rintro ⟨i, j⟩
    revert j
    revert i
    rw [Fin.forall_fin_two]
    exact ⟨fun j => by rw [ea0]; exact cc_psIn m 0 _ (C.B.A.const a' j), fun j => by rw [ea1]; simp⟩
  have hσb : ∀ k, MvPolynomial.constantCoeff (σb k) = 0 := by
    rintro ⟨i, j⟩
    revert j
    revert i
    rw [Fin.forall_fin_two]
    exact ⟨fun j => by rw [eb0]; simp, fun j => by rw [eb1]; exact cc_psIn m 1 _ (C.B.A.const (H.bar a') j)⟩
  have hcc : ∀ (σ : Fin 2 × Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S), (∀ k, MvPolynomial.constantCoeff (σ k) = 0) →
      ∀ i j, MvPowerSeries.constantCoeff (MvPowerSeries.subst Q ((σ (i, j) : MvPolynomial _ S) :
        MvPowerSeries (Fin 2 × Fin C.d) S)) = 0 := by
    intro σ hσ i j
    refine const_substPS Q hQ _ ?_
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
    exact hσ (i, j)
  have hPa : ∀ i j, MvPowerSeries.constantCoeff
      ((![φa c φ (a' * u0), φa c φ u1] : Fin 2 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) i j) = 0 := by
    rw [Fin.forall_fin_two]
    exact ⟨fun j => const_φa c φ hφ0 _ j, fun j => const_φa c φ hφ0 _ j⟩
  have hPb : ∀ i j, MvPowerSeries.constantCoeff
      ((![φa c φ u0, φa c φ (H.bar a' * u1)] : Fin 2 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) i j) = 0 := by
    rw [Fin.forall_fin_two]
    exact ⟨fun j => const_φa c φ hφ0 _ j, fun j => const_φa c φ hφ0 _ j⟩
  have hma : (ptm C P m).left ≫ (homAt y.x (jetSubstP m σa)).left = (ptm C ![φa c φ (a' * u0), φa c φ u1] m).left := by
    rw [← Over.comp_left, ptm_subst C P hP m σa hσa]
    refine congrArg Over.Hom.left (ptm_congr C (hcc σa hσa) hPa m ?_)
    rw [Fin.forall_fin_two]
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [ea0, psJet_subst_psIn m 0 Q hQ]
      exact congrArg (psJet m) (act_φa c hφ0 hact a' u0 j)
    · rw [ea1, MvPolynomial.coe_X, MvPowerSeries.subst_X hQs, hQ1]
      rfl
  have hmb : (ptm C P m).left ≫ (homAt y.x (jetSubstP m σb)).left =
      (ptm C ![φa c φ u0, φa c φ (H.bar a' * u1)] m).left := by
    rw [← Over.comp_left, ptm_subst C P hP m σb hσb]
    refine congrArg Over.Hom.left (ptm_congr C (hcc σb hσb) hPb m ?_)
    rw [Fin.forall_fin_two]
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [eb0, MvPolynomial.coe_X, MvPowerSeries.subst_X hQs, hQ0]
      rfl
    · rw [eb1, psJet_subst_psIn m 1 Q hQ]
      exact congrArg (psJet m) (act_φa c hφ0 hact (H.bar a') u1 j)
  have va : val (pe y C.d C.x C.e m ![fun j => psIn C.d m ![0] (C.B.A.act a' j), fun j => MvPolynomial.X ((1 : Fin 2), j)])
      (ptm C P m).left z J = val (C.e m) (ptm C ![φa c φ (a' * u0), φa c φ u1] m).left z J :=
    (show _ = val (C.e m) ((ptm C P m).left ≫ (homAt y.x (jetSubstP m σa)).left) z J from val_pull hJ _ _ _).trans
      (congrArg (fun r => val (C.e m) r z J) hma)
  have vb : val (pe y C.d C.x C.e m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a') j)])
      (ptm C P m).left z J = val (C.e m) (ptm C ![φa c φ u0, φa c φ (H.bar a' * u1)] m).left z J :=
    (show _ = val (C.e m) ((ptm C P m).left ≫ (homAt y.x (jetSubstP m σb)).left) z J from val_pull hJ _ _ _).trans
      (congrArg (fun r => val (C.e m) r z J) hmb)
  have vw : val (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (jpt y C.d C.x m (0 : Fin 2)) (jpt y C.d C.x m (1 : Fin 2))).left)
      (ptm C P m).left z J =
      val (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (Xo.univ.t.act.act u0) (Xo.univ.t.act.act u1)).left)
        (xExp y C φ m).left z J := by
    rw [val_pull hJ, val_pull hJ, hpt]
  have hg : gm (ptm C P m).left z ⊤ (unitΓ u) =
      gm (𝟙 _) z ⊤ (unitΓ (Units.map (jetSubstPS (m := m) Q).toMonoidHom u)) :=
    ExpGI.gm_homAt _ z u
  have h1 := val_corr hJ hc (ptm C P m).left
  rw [val_mul hJ, ExpGD.val_scale' _ _ _ _ _ z J hJ, va, vb, vw, hg] at h1
  refine ⟨Units.map (jetSubstPS (m := m) Q).toMonoidHom u, ?_, ?_⟩
  · show jetSubstPS (m := m) Q (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (atP P (C.B.ad a'))
    rw [hu, jetSubstPS_psJet m Q hQ]
    rfl
  · rw [← _root_.mul_assoc, eq_mul_inv_iff_mul_eq]
    exact h1

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ
end
end
