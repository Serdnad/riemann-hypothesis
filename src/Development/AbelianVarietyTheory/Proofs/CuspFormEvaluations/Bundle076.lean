module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefChangeTypingsEquivOfValueWD
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle019
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle094
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle074
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle075
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle011

@[expose] public section

section

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.GalTw

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CoefChangeCompare (Natural FromT ValueWD map_trans evR_spec evR_not evR_map)

namespace Rule

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {ta : c.F ≃+* c.F}

theorem fixes_symm (h : Fixes c ta) : Fixes c ta.symm :=
  ⟨fun τ a => by rw [RingEquiv.symm_apply_eq, h.emb], fun a => by rw [RingEquiv.symm_apply_eq, h.base]⟩

def twHom (ta : c.F ≃+* c.F) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) : Tw ta S →ₐ[c.F] Tw ta T :=
  { φ.toRingHom with commutes' := fun a => φ.commutes (ta a) }

def untwHom {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] Tw ta T) : Tw ta.symm S →ₐ[c.F] T :=
  { φ.toRingHom with
    commutes' := fun a => (φ.commutes (ta.symm a)).trans
      (congrArg (algebraMap c.F T) (ta.apply_symm_apply a)) }

theorem fromT_tw_test (h : Fixes c ta) (hA : AllTest Xo c) (p : TRing c.F) (y : FrPt Xo c p.R) :
    FromT (twPt h y) := by
  haveI : IsReduced (Tw ta p.R) := ((GlobalTheory.reduced_finiteType_iff_testRing c.F).2 p).2
  exact hA _ _

theorem fromT_of_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (hy : FromT y) (hm : FrMap φ y z) : FromT z := by
  obtain ⟨p, ψ, y₀, h₀⟩ := hy
  exact ⟨p, _, y₀, map_trans ψ φ h₀ hm⟩

theorem frMap_tw (h : Fixes c ta) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (hm : FrMap φ y z) :
    FrMap (twHom ta φ) (twPt h y) (twPt h z) := hm

theorem fromT_of_tw (h : Fixes c ta) (hA : AllTest Xo c) {S : Type} [CommRing S] [Algebra c.F S]
    {y : FrPt Xo c S} (hy : FromT (twPt h y)) : FromT y := by
  obtain ⟨p, φ, y₀, h₀⟩ := hy
  have h₁ : FrMap (untwHom φ) (twPt (fixes_symm h) y₀) y := h₀
  exact fromT_of_map (fromT_tw_test (fixes_symm h) hA p y₀) h₁

theorem evR_galRul (h : Fixes c ta) (hWD : ValueWD Xo c) (hA : AllTest Xo c) {f : Rul Xo c} (hf : Natural c f)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    evR Xo c (galRul h f) y = (evR Xo c f (twPt h y)).val := by
  by_cases hy : FromT y
  · obtain ⟨q, φ, y₀, hm, e⟩ := evR_spec hy
    rw [e, evR_map hWD hf (fromT_tw_test h hA q y₀) (frMap_tw h hm)]
    rfl
  · rw [evR_not hy, evR_not (fun h' => hy (fromT_of_tw h hA h'))]
    rfl

theorem galRul_mem_sec (h : Fixes c ta) (hWD : ValueWD Xo c) (hA : AllTest Xo c) (hB : BorChartF Xo c)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) : galRul h f ∈ sec Xo c a n := by
  refine ⟨fun p q φ y z hm => ?_, fun q t y y' hb => ?_⟩
  · exact evR_map hWD hf.1 (fromT_tw_test h hA p y) (frMap_tw h hm)
  · have hb' : FrBor (S := Tw ta q.R) t (twPt h y) (twPt h y') := hb
    have h3 : evR Xo c f (twPt h y') = _ * evR Xo c f (twPt h y) :=
      wtAll_of_borChart hB (ex Dw a n) hf.1 hf.2 (Tw ta q.R) _ _ _ (fromT_tw_test h hA q y)
        (fromT_tw_test h hA q y') hb'
    exact h3

end Rule

theorem galRul_sec_val_semilinear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, galRul h f ∈ sec Xo c a n ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), evR Xo c (galRul h f) y = (evR Xo c f (twPt h y)).val) ∧ (∀ (t : c.F) (f g : Rul Xo c), galRul h (t • f + g) = ta t • galRul h f + galRul h g) ∧ ∀ (c₀ : Coeff l) (hle : c₀.F ≤ c.F), (∀ x : c₀.F, ta (incF c₀ c hle x) = incF c₀ c hle x) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (as : Fin m → c.F) (fs : Fin m → Rul Xo c₀), ∀ f ∈ sec Xo c a n, IsBC hle f as fs → IsBC hle (galRul h f) (fun i => ta (as i)) fs := by
  intro E _ _ _ H Dw l Xo c ta h
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hc := GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c
  have hWD : ValueWD Xo c := evalWD_fr (frChartF_of hc)
  have hA : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  have hB : BorChartF Xo c := borChartF_of_cover hc
  refine ⟨fun a n f hf => ⟨Rule.galRul_mem_sec h hWD hA hB hf, fun S _ _ y => Rule.evR_galRul h hWD hA hf.1 y⟩,
    fun t f g => ?_, ?_⟩
  · funext p y
    have h1 : evR Xo c (t • f + g) (twPt h y) =
        algebraMap c.F (Tw ta p.R) t * evR Xo c f (twPt h y) + evR Xo c g (twPt h y) := by
      unfold evR
      rw [evalAt_add, evalAt_smul]
    refine h1.trans ?_
    rw [Algebra.smul_def]
    rfl
  · intro c₀ hle hfix a n m as fs f hf hbc S _ A _ ho y
    letI : Algebra c₀.F (Tw ta S) := A
    have ho' : AlgOver c₀ c hle (Tw ta S) := fun x =>
      (congrArg (algebraMap c.F S) (hfix x)).trans (ho x)
    rw [Rule.evR_galRul h hWD hA hf.1 y]
    exact hbc (Tw ta S) ho' (twPt h y)

end GlobalTheory.GalTw
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaNullValue_existsUnique_natural_linear : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (N : ℕ), Odd N → (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (p : ptO Xo y.x ⟶ Xo.univ.t.G), p ^ (N ^ 2) = 1 → ∃! w, IsNullVal Xo c N y p w) ∧ (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap ψ y z → ∀ (p : ptO Xo y.x ⟶ Xo.univ.t.G) (p' : ptO Xo z.x ⟶ Xo.univ.t.G), p'.left = spMap ψ.toRingHom ≫ p.left → ∀ w, IsNullVal Xo c N y p w → IsNullVal Xo c N z p' (ψ w)) ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (t : Ix Dw → Sˣ), FrBor t y y' → ∀ (p : ptO Xo y.x ⟶ Xo.univ.t.G) (p' : ptO Xo y'.x ⟶ Xo.univ.t.G), p'.left = p.left → ∀ w, IsNullVal Xo c N y p w → IsNullVal Xo c N y' p' ((t none : Sˣ) * w) := by
  first | exact @GlobalTheory.nullValue_existsUnique_natural_linear | exact GlobalTheory.nullValue_existsUnique_natural_linear | (intros; apply GlobalTheory.nullValue_existsUnique_natural_linear <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.Shares

section Ev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def rulEv (U : Unf Xo c σ r)
    (hT : ∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x)) :
    Rul Xo c →+* ((Σ k : U.Comp, (U.X k).dom) → ℂ) where
  toFun f y := rdU U f y.1 y.2.1
  map_zero' := by funext y; rw [map_zero]; rfl
  map_add' f g := by funext y; rw [map_add (f := _)]; rfl
  map_mul' f g := by funext y; rw [rdU_mul]; rfl
  map_one' := by
    funext y
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.rdU_apply_dom U 1 y.1 y.2]
    have e : evR Xo c 1 (U.un y.1 y.2) = 1 := evalAt_one _ _ _ (hT y.1 y.2)
    rw [e]
    rfl

end Ev

def sumParts (R M : Type) [CommRing R] [AddCommMonoid M] :
    AddMonoidAlgebra R M →+* R :=
  (AddMonoidAlgebra.lift R R M 1).toRingHom

theorem sumParts_single (R M : Type) [CommRing R] [AddCommMonoid M] (m : M) (f : R) :
    sumParts R M (AddMonoidAlgebra.single m f) = f := by
  simp [sumParts]

theorem sumParts_smul (K R M : Type) [Field K] [CommRing R] [Algebra K R] [AddCommMonoid M] (a : K)
    (x : AddMonoidAlgebra R M) : sumParts R M (a • x) = a • sumParts R M x := by
  rw [← algebraMap_smul R a x, ← algebraMap_smul R a (sumParts R M x)]
  exact map_smul (AddMonoidAlgebra.lift R R M 1) _ _


set_option synthInstance.maxHeartbeats 200000 in
theorem exists_isRdgU : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)), ∃ (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e := by
  intro D T h j hj n
  have hT := h.unTest j hj T.σ₀ T.good_σ₀
  have hU : IsUnf (T.U j T.σ₀) := h.unf j hj T.σ₀ T.good_σ₀
  let ev : AddMonoidAlgebra (T.R j) (Deg D j) →+* (DomPt T j → ℂ) :=
    (rulEv (T.U j T.σ₀) hT).comp (sumParts (T.R j) (Deg D j))
  have hev : ∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) (y : DomPt T j),
      ev (incG deg (cutR T.C j) u F) y = rdR h j F y.1 y.2.1 := by
    intro u F y
    show rulEv (T.U j T.σ₀) hT (sumParts (T.R j) (Deg D j) (AddMonoidAlgebra.single (deg u) F.1)) y = _
    rw [sumParts_single]
    rfl
  have hsm : ∀ (a : T.Q.c.F) (F : AddMonoidAlgebra (T.R j) (Deg D j)), ev (a • F) = T.σ₀ a • ev F := by
    intro a F
    funext y
    show rdU (T.U j T.σ₀) (sumParts (T.R j) (Deg D j) (a • F)) y.1 y.2.1 =
      T.σ₀ a • rdU (T.U j T.σ₀) (sumParts (T.R j) (Deg D j) F) y.1 y.2.1
    rw [sumParts_smul, map_smulₛₗ]
    rfl
  have hind : ∀ (u : WeightFamilies.Wt D j) (m : ℕ) (F : Fin m → cutR T.C j u),
      LinearIndependent T.Q.c.F F → LinearIndependent ℂ fun i => ev (incG deg (cutR T.C j) u (F i)) := by
    intro u m F hF
    have hb := hF.map' (cutR T.C j u).subtype (Submodule.ker_subtype _)
    have hs : ∀ i, (F i).1 ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n := fun i =>
      cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) (wtA u) u.n (cutR_le T.C j u (F i).2)
    have hli : LinearIndependent ℂ (fun i => rdU (T.U j T.σ₀) (F i).1) :=
      (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.abelianSchemeLaws_all.1.secBaseChange _ _ _ _ _ _ T.σ₀ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀))
        ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU) (wtA u) u.n).1 m (fun i => (F i).1) hs hb
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro g hg
    refine hli g ?_
    funext k x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hx : x ∈ ((T.U j T.σ₀).X k).dom
    · have h1 := congrFun hg ⟨k, ⟨x, hx⟩⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => congrArg (fun z => g i * z) (hev u (F i) ⟨k, ⟨x, hx⟩⟩).symm
    · refine Finset.sum_eq_zero fun i _ => ?_
      have : rdU (T.U j T.σ₀) (F i).1 k x = 0 := dif_neg hx
      rw [this, mul_zero]
  exact ⟨⟨DomPt T j, T.σ₀, ev, hsm, hind⟩, Equiv.refl _, fun _ => rfl, hev⟩

end GlobalTheory.Shares
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem _root_.GlobalTheory.T.cuspForm_vanishing_at_points_mul_pow_mem_span : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → ∀ k : ℕ, ∀ g ∈ R.sp (addL wF wL k) Set.univ, (∀ q, g (xs q) = 0) → ∃ m : ℕ, R.s w t 0 ^ (m + 1) * g ∈ R.deep w t (addL wF wL (k + m)) 1 := by
  first | exact @GlobalTheory.Shares.VanDiv.vanishing_division | exact GlobalTheory.Shares.VanDiv.vanishing_division | (intros; apply GlobalTheory.Shares.VanDiv.vanishing_division <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldBC

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
  Formalism.BasicNotions

theorem actLev_of_le {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {G : Type} [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La))
    (hL : ActLev (Xo := Xo) c lev) : ActLev (Xo := Xo) c' lev := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g S _ _ y
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    obtain ⟨z, hz⟩ := hL.total g S (y.res hle h)
    exact ⟨z.ext hle h, hz⟩
  · intro g S _ _ y y₁ y₂ h₁ h₂
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    exact hL.func g S (y.res hle h) (y₁.res hle h) (y₂.res hle h) h₁ h₂
  · intro S _ _ y
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    exact hL.one S (y.res hle h)
  · intro g g' S _ _ y y₁ y₂ h₁ h₂
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    exact hL.mul g g' S (y.res hle h) (y₁.res hle h) (y₂.res hle h) h₁ h₂
  · intro g S T _ _ _ _ φ y y' z z' h₀ h₁ h₂
    letI := resAlg hle S
    letI := resAlg hle T
    have hS : AlgOver c c' hle S := fun _ => rfl
    have hT : AlgOver c c' hle T := fun _ => rfl
    let ψ : S →ₐ[c.F] T := { φ.toRingHom with commutes' := fun x => φ.commutes _ }
    exact hL.nat g S T ψ (y.res hle hS) (y'.res hle hS) (z.res hle hT) (z'.res hle hT) h₀ h₁ h₂
  · intro g S _ _ t y y' z z' h₀ h₁ h₂
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    exact hL.bor g S t (y.res hle h) (y'.res hle h) (z.res hle h) (z'.res hle h) h₀ h₁ h₂

theorem actLev_and_actBC (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (G : Type) [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La))
    (hL : ActLev (Xo := Xo) c lev) :
    ActLev (Xo := Xo) c' lev ∧ ActBC hle (actLev (Xo := Xo) c lev) (actLev (Xo := Xo) c' lev) :=
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hc := fun c => GlobalTheory.Frames.chartCoverF_of_secBaseChange hS D.host.E H Dw l Xo c
  ⟨actLev_of_le hle lev hL, actBC_of hle lev (evalWD_fr (frChartF_of (hc c))) (evalWD_fr (frChartF_of (hc c'))) hL
    (actLev_of_le hle lev hL)⟩

end GlobalTheory.FieldBC
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortValue

theorem finite_levelQuotient {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)
    (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have hp := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at hp
    have := l.three_le
    omega
  haveI : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  haveI := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem map_weighted_finsum {F S₁ S₂ T Q : Type} [Field F] [CommRing S₁] [CommRing S₂] [CommRing T]
    [Algebra F S₁] [Algebra F S₂] [Algebra F T] [Finite Q] (ψ₁ : S₁ →ₐ[F] T) (ψ₂ : S₂ →ₐ[F] T)
    (k : F) (w : Q → F) (A₁ : Q → S₁) (A₂ : Q → S₂) (h : ∀ q, ψ₁ (A₁ q) = ψ₂ (A₂ q)) :
    ψ₁ (algebraMap F S₁ k * ∑ᶠ q, algebraMap F S₁ (w q) * A₁ q) =
      ψ₂ (algebraMap F S₂ k * ∑ᶠ q, algebraMap F S₂ (w q) * A₂ q) := by
  haveI := Fintype.ofFinite Q

  simp only [finsum_eq_sum_of_fintype, map_mul, map_sum, AlgHom.commutes, h]

end GlobalTheory.ShortValue

namespace GlobalTheory

theorem shortThetaValue_existsUnique_natural : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (w : (Fin n → LevQ Dw l) → c.F) (β : c.F), (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃! v, ShortValAt Xo c nab w Λ β N P y v) ∧ ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ v0 v, ShortValAt Xo c nab w Λ β N P y0 v0 → ShortValAt Xo c nab w Λ β N P y v → φ v0 = v := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab n Λ N hU hT hN a P hP w β
  haveI := ShortValue.finite_levelQuotient Dw l
  have cmp := GlobalTheory.T.shortThetaSum_eq_of_witnesses_common_algebra hL hC E H Dw l Xo c nab hnab n Λ N hU hT hN a P hP
  have nat : ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
      (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ v0 v, ShortValAt Xo c nab w Λ β N P y0 v0 →
      ShortValAt Xo c nab w Λ β N P y v → φ v0 = v := by
    intro S T _ _ _ _ φ y0 y hφ v0 v h0 h1
    obtain ⟨S1, _, _, φ1, y1, z1, tp1, F1, hf1, hm1, hz1, hg1, ht1, hu1, e1⟩ := h0
    obtain ⟨S2, _, _, φ2, y2, z2, tp2, F2, hf2, hm2, hz2, hg2, ht2, hu2, e2⟩ := h1
    obtain ⟨U, _, _, ψ2, ψ1, hc, -, hinj⟩ :=
      exists_faithfullyFlat_pushout c.F S S2 S1 (φ2.comp φ) φ1 hf1
    have key := cmp S y0 S1 φ1 y1 z1 tp1 F1 S2 (φ2.comp φ) y2 z2 tp2 F2 hm1
      (FramedBaseChange.trans φ φ2 hφ hm2) hz1 hg1 ht1 hu1 hz2 hg2 ht2 hu2 U ψ1 ψ2 hc.symm
    have hinj2 : Function.Injective φ2 := hf2.injective
    apply hinj2
    apply hinj
    have e0 : ψ2 (φ2 (φ v0)) = ψ1 (φ1 v0) := AlgHom.congr_fun hc v0
    rw [e0, e1, e2]
    exact ShortValue.map_weighted_finsum ψ1 ψ2 _ w _ _ key
  refine ⟨fun S _ _ y => ?_, nat⟩
  obtain ⟨S1, _, _, φ1, y1, z1, tp1, F1, hf1, hm1, hz1, hg1, ht1, hu1⟩ :=
    GlobalTheory.T.exists_faithfullyFlat_cover_shortThetaValue_data hL E H Dw l Xo c n Λ N hU hT hN S y
  obtain ⟨v, hv, -⟩ := existsUnique_preimage_of_faithfullyFlat c.F S S1 φ1 hf1
    (algebraMap c.F S1 (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ *
        ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ *
        ((N : c.F) ^ P.totalDegree)⁻¹) *
      ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F S1 (w q) *
        ∑ i, ∑ m ∈ P.support, algebraMap c.F S1 (P.coeff m) *
          ∏ b, nab y1 ((N : ℤ) ^ 2) (F1 q i b) (colOf m b))
    (fun T _ _ ψ1 ψ2 hc => ShortValue.map_weighted_finsum ψ1 ψ2 _ w _ _
      (cmp S y S1 φ1 y1 z1 tp1 F1 S1 φ1 y1 z1 tp1 F1 hm1 hm1 hz1 hg1 ht1 hu1 hz1 hg1 ht1 hu1 T ψ1 ψ2 hc))
  have hv' : ShortValAt Xo c nab w Λ β N P y v :=
    ⟨S1, _, _, φ1, y1, z1, tp1, F1, hf1, hm1, hz1, hg1, ht1, hu1, hv⟩
  exact ⟨v, hv', fun v' h' => nat S S (AlgHom.id c.F S) y y (FramedBaseChange.refl y) v' v h' hv'⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem thExpr_tmul_lemma (hL : Laws) (hC : ChartIndepSt2) {E : Type} [Field E] [NumberField E]
    [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    [StarRing (𝓞 E)] {nab : NabV Xo c} (hnab : IsNab Xo c nab) {S : Type} [CommRing S]
    [Algebra c.F S] (y : FrPt Xo c S) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (x : Fin n → Dw.La)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n)
    {S1 : Type} [CommRing S1] [Algebra c.F S1] [Algebra S S1] (φ1 : S →ₐ[c.F] S1)
    (hφ1 : ∀ s, φ1 s = algebraMap S S1 s) (y1 : FrPt Xo c S1)
    (F1 : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y1.x)))
    (h1 : FrMap φ1 y y1)
    (hF1 : ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y1.s
      (levPt Xo y1.x (x b)) (F1 b))
    {S2 : Type} [CommRing S2] [Algebra c.F S2] [Algebra S S2] (φ2 : S →ₐ[c.F] S2)
    (hφ2 : ∀ s, φ2 s = algebraMap S S2 s) (y2 : FrPt Xo c S2)
    (F2 : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y2.x)))
    (h2 : FrMap φ2 y y2)
    (hF2 : ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y2.s
      (levPt Xo y2.x (x b)) (F2 b)) :
    TensorProduct.tmul S (thExpr Xo c nab y1 P F1) (1 : S2) =
      TensorProduct.tmul S (1 : S1) (thExpr Xo c nab y2 P F2) := by
  letI : Algebra c.F (TensorProduct S S1 S2) :=
    ((algebraMap S (TensorProduct S S1 S2)).comp (algebraMap c.F S)).toAlgebra
  let χ1 : S1 →ₐ[S] TensorProduct S S1 S2 := Algebra.TensorProduct.includeLeft
  let χ2 : S2 →ₐ[S] TensorProduct S S1 S2 := Algebra.TensorProduct.includeRight

  let ψ1 : S1 →ₐ[c.F] TensorProduct S S1 S2 :=
    { χ1.toRingHom with
      commutes' := fun r => by
        show χ1 (algebraMap c.F S1 r) = algebraMap S (TensorProduct S S1 S2) (algebraMap c.F S r)
        rw [← φ1.commutes r, hφ1]
        exact χ1.commutes _ }
  let ψ2 : S2 →ₐ[c.F] TensorProduct S S1 S2 :=
    { χ2.toRingHom with
      commutes' := fun r => by
        show χ2 (algebraMap c.F S2 r) = algebraMap S (TensorProduct S S1 S2) (algebraMap c.F S r)
        rw [← φ2.commutes r, hφ2]
        exact χ2.commutes _ }
  have hcomp : ψ1.comp φ1 = ψ2.comp φ2 := by
    ext s
    show χ1 (φ1 s) = χ2 (φ2 s)
    rw [hφ1, hφ2, χ1.commutes, χ2.commutes]
  exact GlobalTheory.T.thetaExpression_eq_of_witnesses hL hC E H Dw l Xo c nab hnab S y a n x P hP S1 φ1 y1 F1 S2 φ2 y2 F2 h1 hF1 h2 hF2
    (TensorProduct S S1 S2) ψ1 ψ2 hcomp

theorem thValTot_of_chartIndep : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ThValTot Xo c nab := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab S _ _ y a n x P hP

  obtain ⟨S', _, _, φ, y', F, hff, hy', hF⟩ := GlobalTheory.T.exists_faithfullyFlat_cover_level_sections hL E H Dw l Xo c S y n x
  letI : Algebra S S' := φ.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat S S' := hff
  have hφ : ∀ s, φ s = algebraMap S S' s := fun _ => rfl

  have htmul := thExpr_tmul_lemma hL hC hnab y x hP φ hφ y' F hy' hF φ hφ y' F hy' hF
  obtain ⟨v, hv⟩ := (Algebra.IsEffective.of_faithfullyFlat S S' (thExpr Xo c nab y' P F)).mp
    (by rw [Algebra.TensorProduct.includeLeftSubRight_apply, htmul, sub_self])
  refine ⟨v, ⟨S', inferInstance, inferInstance, φ, y', F, hff, hy', hF, hv⟩, ?_⟩

  rintro w ⟨S2, _, _, φ2, y2, F2, hff2, hy2, hF2, hw⟩
  letI : Algebra S S2 := φ2.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat S S2 := hff2
  have h12 := thExpr_tmul_lemma hL hC hnab y x hP φ hφ y' F hy' hF φ2 (fun _ => rfl) y2 F2 hy2 hF2
  have hv' : φ v = thExpr Xo c nab y' P F := hv
  rw [← hv', ← hw, hφ, Algebra.TensorProduct.tmul_one_eq_one_tmul] at h12
  have h3 : algebraMap S S2 v = algebraMap S S2 w :=
    Module.FaithfullyFlat.tensorProduct_mk_injective (A := S) (B := S') S2 h12
  exact (FaithfulSMul.algebraMap_injective S S2 h3).symm

end GlobalTheory
end
