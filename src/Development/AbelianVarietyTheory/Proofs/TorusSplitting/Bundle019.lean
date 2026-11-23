module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle189
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle124
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle187
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle071
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle029
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsPerfectTraceIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsSymmetricFrameAndTerms
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle071
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle001
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.EtaVal
open GlobalTheory.UT GlobalTheory.TorusExt GlobalTheory.UT.ThetaConstVal

attribute [local instance] gtGroup

theorem le_val_thetaConst : GlobalTheory.UT.AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, GlobalTheory.UT.NormW U.toUnifPre w₀ ρ → ∀ (th : GlobalTheory.UT.SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → NuGe D Q F v 1 ϑ 0 → ∀ (m : ℕ), Odd m → ∀ (p : QkPt D.toPre F (m ^ 2)) x t c, QkToAkU U.toUnifPre F (m ^ 2) p x → GlobalTheory.UT.ThC A ρ m th x t c → ∀ q : ℚ, (∀ χ, q ≤ (Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v c := by
  obtain ⟨hL, h₁, h₂, h₃, h₄⟩ := GlobalTheory.lawsAndExpansions
  intro V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th ϑ hE hP m hm p x t c hx hT q hq
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨w, hw⟩ := (GlobalTheory.UT.SymFrame.main hL V _ hA D F (m ^ 2) hm.pow p).1
  obtain ⟨κ, hκ⟩ := exists_kap D.toPre hL.1.mulPull m
  obtain ⟨w', hw', e⟩ := exists_frm D.toPre m p.g.b (m • p.g).b (nsmul_b m p.g) w hw.1 κ hκ.1
  have hg : GtPtF.IsNsmul m p.g (m • p.g) := (isNsmul_iff_eq _ _ _).2 rfl
  have s := (GlobalTheory.UT.ThetaSum.theta_const_sum hL V _ hA D A G hG U F w₀ ρ hN th ϑ hE m hm p x t c hx hT w hw _ hg κ hκ w' hw' e).1
  obtain ⟨-, -, a⟩ := (GlobalTheory.UT.TxVal.main hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv).2 m hm.pos p w hw _ hg κ hκ w' hw' e
  exact le_of_sumV (AdicValSum.main V ϖ hϖ F v hv _ _ _ s).1 fun χ =>
    (WithTop.coe_le_coe.2 (hq χ)).trans (a ϑ hP χ)

end GlobalTheory.EtaVal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem eq_zero_of_mul_eq_zero_of_reading_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : _root_.Formalism.L2.PjFree.Unf Xo c σ r), _root_.Formalism.L2.PjFree.GoodEmb c σ → _root_.Formalism.L2.PjFree.IsUnf U → ∀ (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (f g : Rul Xo c), Dom a n → Dom a' n' → f ∈ sec Xo c a n → g ∈ sec Xo c a' n' → (∀ k, ∃ x ∈ (U.X k).dom, rdU U f k x ≠ 0) → f * g = 0 → g = 0 := by
  intro E _ _ _ H Dw l Xo c σ r U _ hU a a' n n' f g ha ha' hf hg hne hfg
  refine (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.firstFiveLaws.1.secBaseChange
    E H Dw l Xo c σ r U hU a' n').2 g hg fun k => ?_
  obtain ⟨x0, hx0, hx0ne⟩ := hne k
  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero (FourierCoefficientDomain.isOpen_dom _)
    (GlobalTheory.frames_isConnected E r (U.X k)).isPreconnected (hU.2.2.2.2.1 a n ha f hf k).1
    (hU.2.2.2.2.1 a' n' ha' g hg k).1 (fun y hy => ?_) hx0 hx0ne
  have hmul : rdU U (f * g) k y = rdU U f k y * rdU U g k y := by
    simp only [_root_.Formalism.L2.PjFree.rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hy]
    exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (U.un k ⟨y, hy⟩)
  have h0 : rdU U (f * g) k y = 0 := by
    rw [hfg, map_zero]
    rfl
  exact hmul.symm.trans h0

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem nonempty_comp_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : _root_.Formalism.L2.PjFree.Unf Xo c σ r), _root_.Formalism.L2.PjFree.GoodEmb c σ → _root_.Formalism.L2.PjFree.IsUnf U → 1 ≤ r → Nonempty U.Comp := by
  intro E _ _ _ H Dw l Xo c σ r U _ hU hr
  obtain ⟨y⟩ := GlobalTheory.nonempty_frPt_complex GlobalTheory.closing_of_abelianSchemeLaws
    GlobalTheory.firstFiveLaws.2.1.secTwist E H Dw l Xo c (hU.1 ▸ hr) σ
  obtain ⟨k, -⟩ := hU.2.2.1 y
  exact ⟨k⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

namespace GlobalTheory.EtaAn

theorem log_card_comp_le_of_rows : ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D), (2 ≤ large₂.sc.L ∧ Real.log D.R.r ≤ large₂.sc.L ∧ Real.log D.host.rdE ≤ 2 * large₂.sc.L ∧ Real.log D.R.f ≤ 2 * large₂.sc.L ∧ (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧ 16 ≤ D.R.f) → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → Real.log (Fintype.card (T.U j σ).Comp) ≤ 41 * zBase large₂ ^ 2 := by
  intro D T h large₂ ⟨h2, hrL, hrd, hf, hg, h16⟩ j hj σ hσ
  obtain ⟨ξ, AA, hsk, hne, hFG, hA, hdual⟩ := PerfectTrace.exists_perfect_trace_ideal D
  obtain ⟨-, -, hM, -, -, hfin, hJ⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨-, hr, -⟩ := hJ j hj
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hfd : FD.fdeg D.host.E = D.R.f := by
    unfold FD.fdeg; rw [hfin]; omega
  have hfR : (0 : ℝ) < D.R.f := by exact_mod_cast (by omega : 0 < D.R.f)
  have hdisc : 0 < |((NumberField.discr D.host.E : ℤ) : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have hdE : Real.log (FD.dE D.host.E) ≤ 4 * FD.fdeg D.host.E * large₂.sc.L := by
    unfold Formalism.BasicNotions.Host.rdE at hrd
    rw [Real.log_rpow hdisc, hfin, one_div_mul_eq_div, div_le_iff₀ (by push_cast; positivity)] at hrd
    push_cast at hrd
    rw [hfd]
    unfold FD.dE
    linarith
  have hML : Real.log T.Q.l.M' ≤ 30 * large₂.sc.L := by
    rw [hM, hMg]
    have h0 := hg 0
    have h1 := hg 1
    have a := (D.host.g_prime 0).pos
    have b := (D.host.g_prime 1).pos
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast a.ne') (by exact_mod_cast b.ne')]
    linarith
  have key := GlobalTheory.log_card_comp_unf_le GlobalTheory.QNorm.hasseNormSt GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1
    D.host.E _ _ _ (T.Q.Xo j) T.Q.c σ D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hr hσ ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ hσ))
    ξ AA hsk hne hFG hA hdual large₂.sc.L (by rw [hfd]; exact h16) h2 hdE hrL
    (by rw [hfd]; exact hf) hML
  rw [hfd] at key
  exact key

end GlobalTheory.EtaAn
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

theorem exists_qkPt_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] (G : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) G), P.TorsionIso → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (N : ℕ), 1 ≤ N → ∀ (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (ev : M → (TFK (R := V) F ⟶ P.A.A)), (∀ a b, ev (a + b) = ev a * ev b) → (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ (letI := H.starRing; P.oA.act o : P.A.A ⟶ P.A.A)) → (∀ a, ev a ^ N = 1) → (∀ u, u ^ N = 1 → ∃ a, ev a = u) → ∃ pt : M → QkPt P.D.toPre F N, (∀ a, P.ToA F N (pt a) (ev a)) ∧ ∀ (n : ℕ) (z : Fin n → M), Submodule.span (𝓞 E) (Set.range z) = ⊤ → ∀ a : P.D.toPre.X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range fun b => (pt (z b)).y), ∃ t : P.D.toPre.X, a = u + N • t := by
  intro E _ _ _ H V _ _ _ _ hc G P hT F _ _ _ N hN M _ _ ev hadd hsm hpow hsurj
  letI := H.starRing
  open GlobalTheory.TorusExt in
  obtain ⟨f, hto, hon, heq, hfa, hfs, -⟩ := hT F N hN
  have hB := P.D.tau_bimult
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  letI := GlobalTheory.TorusExt.gtGroup P.D.toPre F
  let iotaLocal : P.D.toPre.X →+ GtPtF P.D.toPre F := AddMonoidHom.mk'
    (fun x => (GlobalTheory.TorusExt.exists_iota (F := F) hB x).choose) (by
      intro x x'
      obtain ⟨b, v⟩ := (GlobalTheory.TorusExt.isIota_iff_val _ _).1 (GlobalTheory.TorusExt.exists_iota (F := F) hB x).choose_spec
      obtain ⟨b', v'⟩ := (GlobalTheory.TorusExt.isIota_iff_val _ _).1 (GlobalTheory.TorusExt.exists_iota (F := F) hB x').choose_spec
      obtain ⟨b'', v''⟩ := (GlobalTheory.TorusExt.isIota_iff_val _ _).1 (GlobalTheory.TorusExt.exists_iota (F := F) hB (x + x')).choose_spec
      refine (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 ((GlobalTheory.TorusExt.isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', cPoint_add], fun χ y J hJ => ?_⟩)
      have sym01 (a b c : TF (R := V) F ⟶ P.D.toPre.P.A) :
          th P.D.toPre y J a b c = th P.D.toPre y J b a c := by
        have e := (val_corr hJ P.D.toPre.cub.cubeSymmetric_swap_first (lift a (lift b c)).left).trans
          (val_cub P.D.toPre.cub (lift a (lift b c)) hJ _ _ _)
        refine e.trans ?_
        congr 1 <;> simp [x3]
      have sym12 (a b c : TF (R := V) F ⟶ P.D.toPre.P.A) :
          th P.D.toPre y J a b c = th P.D.toPre y J a c b := by
        have e := (val_corr hJ P.D.toPre.cub.cubeSymmetric_swap_last (lift a (lift b c)).left).trans
          (val_cub P.D.toPre.cub (lift a (lift b c)) hJ _ _ _)
        refine e.trans ?_
        congr 1 <;> simp [x3]
      rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', sym01, sym12]
      exact tau_mul (𝟙 (TF (R := V) F)) hJ hB x x' χ)
  have hi (x : P.D.toPre.X) : GtPtF.IsIota x (iotaLocal x) := (GlobalTheory.TorusExt.exists_iota hB x).choose_spec
  have hn (p : QkPt P.D.toPre F N) : N • p.g = iotaLocal p.y := by
    obtain ⟨h, hn, hi'⟩ := p.eq
    exact ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hn).symm.trans (GlobalTheory.TorusExt.isIota_unique hi' (hi p.y))
  choose pt hpt using fun a => hon (ev a) (hpow a)
  refine ⟨pt, fun a => (hto _ _).2 (hpt a).symm, fun n z hz y => ?_⟩
  have yadd : ∀ a b, ∃ t : P.D.toPre.X, (pt (a + b)).y = (pt a).y + (pt b).y + N • t := fun a b => by
    let q : QkPt P.D.toPre F N := ⟨(pt a).y + (pt b).y, (pt a).g + (pt b).g,
      iotaLocal ((pt a).y + (pt b).y), (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 (by
        rw [nsmul_add, hn, hn, map_add]), hi _⟩
    have e := hfa _ _ _ (show QkAdd (pt a) (pt b) q from
      ⟨q, rfl, (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl, qk_equiv_refl hB q⟩)
    rw [hpt, hpt, ← hadd, ← hpt] at e
    obtain ⟨t, ht, -⟩ := (heq _ _).1 e
    exact ⟨t, ht⟩
  have ysm : ∀ (o : 𝓞 E) a, ∃ t : P.D.toPre.X, (pt (o • a)).y = o • (pt a).y + N • t := fun o a => by
    obtain ⟨q, hq⟩ := qkAct_exists hG hB P.oD o (pt a)
    obtain ⟨r, hr, hact, he⟩ := hq
    have e := hfs _ _ _ (show QkAct P.oD o (pt a) r from ⟨r, hr, hact, qk_equiv_refl hB r⟩)
    rw [hpt, ← hsm, ← hpt] at e
    obtain ⟨t, ht, -⟩ := (heq _ _).1 e
    exact ⟨t, by simpa [hr] using ht⟩
  have key : ∀ m ∈ Submodule.span (𝓞 E) (Set.range z),
      ∃ u ∈ Submodule.span (𝓞 E) (Set.range fun b => (pt (z b)).y), ∃ t : P.D.toPre.X, (pt m).y = u + N • t := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact ⟨_, Submodule.subset_span ⟨b, rfl⟩, 0, by rw [smul_zero, add_zero]⟩
    | zero =>
      obtain ⟨t, ht⟩ := ysm 0 0
      rw [zero_smul, zero_smul] at ht
      exact ⟨0, Submodule.zero_mem _, t, ht⟩
    | add a b _ _ ha hb =>
      obtain ⟨u, hu, t, ht⟩ := ha
      obtain ⟨u', hu', t', ht'⟩ := hb
      obtain ⟨s, hs⟩ := yadd a b
      exact ⟨u + u', Submodule.add_mem _ hu hu', t + t' + s, by
        rw [hs, ht, ht', smul_add, smul_add]; abel⟩
    | smul o a _ ha =>
      obtain ⟨u, hu, t, ht⟩ := ha
      obtain ⟨s, hs⟩ := ysm o a
      exact ⟨o • u, Submodule.smul_mem _ o hu, o • t + s, by
        rw [hs, ht, smul_add, smul_add, smul_comm o N t, add_assoc]⟩
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨g, hg⟩ := (GlobalTheory.UT.gt_onto_divisible_kernel GlobalTheory.firstFiveLaws V _ hA P.D F).2.1 N hN
    (iotaLocal y)
  let p : QkPt P.D.toPre F N :=
    ⟨y, g, iotaLocal y, hg, hi y⟩
  have hp : f p ^ N = 1 := by
    obtain ⟨w, hw⟩ := P.U.ext
    exact ((hto p _).2 rfl w hw).1
  obtain ⟨m, hm⟩ := hsurj _ hp
  obtain ⟨s, hs, -⟩ := (heq (pt m) p).1 ((hpt m).trans hm)
  obtain ⟨u, hu, t, ht⟩ := key m (hz ▸ Submodule.mem_top)
  refine ⟨u, hu, t + s, ?_⟩
  have hs' : y = (pt m).y + N • s := hs
  rw [hs', ht, smul_add, add_assoc]

end GlobalTheory.EtaVal
end
