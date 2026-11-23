module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle113
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle229
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle112
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle115
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle114
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyGroupAlgebraCentreLatticeAction
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle422
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLocalCongruenceLengthEqRationalLength
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle421
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle388
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle402
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle401
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatFinrankKs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthInvariantsLtTop
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle424
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.Divisibility.Bundle001
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily

@[expose] public section

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.HCChar

theorem sum_subgroup {G : Type} [Group G] [Fintype G] (P : Subgroup G) (Φ : P → ℂ) :
    ∑ p : P, Φ p = ∑ x : G, if h : x ∈ P then Φ ⟨x, h⟩ else 0 := by
  have e := Finset.sum_subtype (F := (inferInstance : Fintype P)) (Finset.univ.filter (· ∈ P)) (p := (· ∈ P))
    (by simp) (fun x => if h : x ∈ P then Φ ⟨x, h⟩ else 0)
  rw [Finset.sum_filter] at e
  refine (Eq.trans ?_ e.symm).trans ?_
  · apply Finset.sum_congr rfl; intro a _; simp [dif_pos a.2]
  · apply Finset.sum_congr rfl; intro x _; split_ifs <;> rfl

theorem toG_val {g m : ℕ} [Fact g.Prime] {M : Mt g m} (h : IsUnit M) : ((toG M : Gn g m) : Mt g m) = M := by
  unfold toG; rw [dif_pos h]; rfl

theorem card_ker_eq_sum {P M : Type} [Group P] [Fintype P] [Group M] (π : P →* M) :
    (Nat.card π.ker : ℂ) = ∑ p : P, if π p = 1 then (1 : ℂ) else 0 := by
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [MonoidHom.mem_ker]

def blocks {g : ℕ} [Fact g.Prime] (a b n : ℕ) (P : Subgroup (Gn g n))
    (hP : ∀ x, x ∈ P ↔ InPar a (x : Mt g n))
    (hunit : ∀ x : Gn g n, InPar a (x : Mt g n) → IsUnit (tl a (x : Mt g n)) ∧ IsUnit (br a b (x : Mt g n)))
    (hmul : ∀ x y : Mt g n, InPar a x → InPar a y →
      tl a (x * y) = tl a x * tl a y ∧ br a b (x * y) = br a b x * br a b y) :
    P →* Gn g a × Gn g b :=
  MonoidHom.mk' (fun p => (toG (tl a ((p : Gn g n) : Mt g n)), toG (br a b ((p : Gn g n) : Mt g n)))) (by
    intro p q
    have hp := (hP p).1 p.2
    have hq := (hP q).1 q.2
    have hpq := (hP (p * q)).1 (p * q).2
    have hm := hmul _ _ hp hq
    have e1 : (((p * q : P) : Gn g n) : Mt g n) = ((p : Gn g n) : Mt g n) * ((q : Gn g n) : Mt g n) := rfl
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · show ((toG (tl a (((p * q : P) : Gn g n) : Mt g n)) : Gn g a) : Mt g a) =
        ((toG (tl a ((p : Gn g n) : Mt g n)) * toG (tl a ((q : Gn g n) : Mt g n)) : Gn g a) : Mt g a)
      have hu : IsUnit (tl a (((p : Gn g n) : Mt g n) * ((q : Gn g n) : Mt g n))) := by
        rw [hm.1]; exact (hunit _ hp).1.mul (hunit _ hq).1
      rw [Units.val_mul, e1, toG_val hu, toG_val (hunit _ hp).1, toG_val (hunit _ hq).1, hm.1]
    · show ((toG (br a b (((p * q : P) : Gn g n) : Mt g n)) : Gn g b) : Mt g b) =
        ((toG (br a b ((p : Gn g n) : Mt g n)) * toG (br a b ((q : Gn g n) : Mt g n)) : Gn g b) : Mt g b)
      have hu : IsUnit (br a b (((p : Gn g n) : Mt g n) * ((q : Gn g n) : Mt g n))) := by
        rw [hm.2]; exact (hunit _ hp).2.mul (hunit _ hq).2
      rw [Units.val_mul, e1, toG_val hu, toG_val (hunit _ hp).2, toG_val (hunit _ hq).2, hm.2])

theorem hc_isChar_and_res_decomp : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b →
    (∀ (α : Gn g a → ℂ) (β : Gn g b → ℂ), IsChar α → IsChar β → IsChar (hc a b α β n)) ∧
    ∀ χ : Gn g n → ℂ, IsChar χ → ∃ L : List ((Gn g a → ℂ) × (Gn g b → ℂ)),
      (∀ p ∈ L, IsIrr p.1 ∧ IsIrr p.2) ∧ ∀ x y, res a b χ x y = (L.map fun p => p.1 x * p.2 y).sum := by
  intro g _ a b n hn
  obtain ⟨⟨P, hP⟩, -, hunit, hmul, hcard, hPcard⟩ := GlobalTheory.GLm.ParBasic.par_basic g a b n hn
  obtain ⟨π, hπv⟩ : ∃ π : P →* Gn g a × Gn g b,
      ∀ p : P, π p = (toG (tl a ((p : Gn g n) : Mt g n)), toG (br a b ((p : Gn g n) : Mt g n))) :=
    ⟨blocks a b n P hP hunit hmul, fun _ => rfl⟩
  have hπ : ∀ (x : Gn g n) (hx : x ∈ P) (h₁ : Gn g a) (h₂ : Gn g b),
      π ⟨x, hx⟩ = (h₁, h₂) ↔ (tl a (x : Mt g n) = h₁ ∧ br a b (x : Mt g n) = h₂) := by
    intro x hx h₁ h₂
    have hu := hunit x ((hP x).1 hx)
    rw [hπv]
    rw [Prod.mk.injEq, Units.ext_iff, Units.ext_iff, toG_val hu.1, toG_val hu.2]
  have hsum : ∀ (f : Gn g n → ℂ) (h₁ : Gn g a) (h₂ : Gn g b),
      ∑ p : P, (if π p = (h₁, h₂) then f p else 0) =
        ∑ x : Gn g n, if InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = h₁ ∧ br a b (x : Mt g n) = h₂ then f x else 0 := by
    intro f h₁ h₂
    rw [sum_subgroup]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ P
    · rw [dif_pos hx]
      have hx' := (hP x).1 hx
      by_cases h : tl a (x : Mt g n) = h₁ ∧ br a b (x : Mt g n) = h₂
      · rw [if_pos ((hπ x hx h₁ h₂).2 h), if_pos ⟨hx', h⟩]
      · rw [if_neg (fun e => h ((hπ x hx h₁ h₂).1 e)), if_neg (fun e => h e.2)]
    · rw [dite_eq_right hx, if_neg (fun e => hx ((hP x).2 e.1))]
  have hNP : (Nat.card P : ℂ) = ((Finset.univ.filter fun p : Gn g n => InPar a (p : Mt g n)).card : ℂ) := by
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1; ext x; simp [hP]
  refine ⟨?_, ?_⟩
  · intro α β hα hβ
    have hφ : IsChar (fun p : P => α (π p).1 * β (π p).2) :=
      GlobalTheory.GLm.isChar_comp_hom_and_mul.2 P _ _
        (GlobalTheory.GLm.isChar_comp_hom_and_mul.1 P _ ((MonoidHom.fst _ _).comp π) α hα)
        (GlobalTheory.GLm.isChar_comp_hom_and_mul.1 P _ ((MonoidHom.snd _ _).comp π) β hβ)
    obtain ⟨V, hV⟩ := GlobalTheory.GLm.IndChar.isChar_induced (Gn g n) P _ hφ
    refine ⟨V, fun x => (hV x).trans ?_⟩
    unfold hc hcT
    dsimp only
    rw [hNP]
    refine congrArg (fun t : ℂ => (((Finset.univ.filter fun p : Gn g n => InPar a (p : Mt g n)).card : ℂ)⁻¹) * t) ?_
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y⁻¹ * x * y ∈ P
    · rw [dif_pos hy, if_pos ((hP _).1 hy), hπv]
    · rw [dite_eq_right hy, if_neg (fun e => hy ((hP _).2 e))]
  · intro χ hχ
    have hsurj : Function.Surjective π := by
      rintro ⟨h₁, h₂⟩
      have hpos : 0 < (Finset.univ.filter fun x : Gn g n =>
          InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = (h₁ : Mt g a) ∧ br a b (x : Mt g n) = (h₂ : Mt g b)).card := by
        rw [hcard]; exact pow_pos (Fact.out : g.Prime).pos _
      obtain ⟨x, hx⟩ := Finset.card_pos.1 hpos
      rw [Finset.mem_filter] at hx
      have hxP := (hP x).2 hx.2.1
      refine ⟨⟨x, hxP⟩, ?_⟩
      exact (hπ x hxP h₁ h₂).2 hx.2.2
    have hχP : IsChar (fun p : P => χ p) := GlobalTheory.GLm.isChar_comp_hom_and_mul.1 P _ P.subtype χ hχ
    have hΨ := GlobalTheory.GLm.isChar_fibre_mean P (Gn g a × Gn g b) π _ hsurj hχP
    obtain ⟨L, hL, hLs⟩ := GlobalTheory.T.exists_irr_pairs_char_prod_eq_sum (Gn g a) (Gn g b) _ hΨ
    refine ⟨L, hL, fun x y => ?_⟩
    rw [← hLs x y]
    have hker : (Nat.card π.ker : ℂ) = (g : ℂ) ^ (a * b) := by
      rw [card_ker_eq_sum, Prod.one_eq_mk]
      refine Eq.trans ?_ ((hsum (fun _ => 1) 1 1).trans ?_)
      · apply Finset.sum_congr rfl; intro p _; split_ifs <;> rfl
      rw [Finset.sum_boole, hcard 1 1]
      push_cast; rfl
    unfold res
    rw [hker]
    refine congrArg (fun t : ℂ => ((g : ℂ) ^ (a * b))⁻¹ * t) ?_
    convert (hsum χ x y).symm using 2
    split_ifs <;> rfl

end GlobalTheory.GLq.HCChar
end
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.map_gamma_eq_deltaPi_teichmuller : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], (∃ γ : (S.W H).Gam, ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) ∧ ∀ a, PowerSeries.map (algebraMap S.O k) ((S.W H).γ₀ γ a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l (PowerSeries.map (algebraMap S.O k) a)) ∧ ∃ e : {δ // δ ∈ (S.W H).DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}, ∀ δ a, PowerSeries.map (algebraMap S.O k) ((S.W H).γ₀ δ.1 a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map (algebraMap S.O k) a) := by
  first | exact @GlobalTheory.RedAct.gamma_action_reduction | exact GlobalTheory.RedAct.gamma_action_reduction | (intros; apply GlobalTheory.RedAct.gamma_action_reduction <;> assumption)
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

theorem _root_.GlobalTheory.T.sum_localCongruenceLength_eq_rationalLength : ∀ (D : D7) (M : MtFam D) (T : NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl), 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → HeckeStdTw T.B → LatStable T.B j w → ZRat D (D.what₂.muTw w) j → (∀ i ∈ D.nd.locs j w, SpecPr D i) → D.what₂.etaJ j w = etaRat D (D.what₂.muTw w) j w := by
  first | exact @GlobalTheory.EtaJoinSum.sum_etaLoc_eq_etaRat | exact GlobalTheory.EtaJoinSum.sum_etaLoc_eq_etaRat | (intros; apply GlobalTheory.EtaJoinSum.sum_etaLoc_eq_etaRat <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

theorem _root_.GlobalTheory.T.trace_rankRPart_eq_trace_baseChangeTriple : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (a : D.nd.Loc) (π : D.nd.X a) (ρ : Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a)) (s : D.ntw.Sig (D.ntw.twOf a)) (Sg : List (Part D.naut.CG)), GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D a π ρ → HasParamX D.nd D.naut a π Sg → GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsTriple D a s Sg → ∀ g, ((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)).trace = D.ntw.twist₂ a ((D.ntw.rhoS _ s g : GL (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))).trace := by
  first | exact @GlobalTheory.TripleTrace.trace_eq | exact GlobalTheory.TripleTrace.trace_eq | (intros; apply GlobalTheory.TripleTrace.trace_eq <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

theorem _root_.GlobalTheory.T.nonempty_groupAlgebraCentreLatticeAction : ∀ D : D7, (∀ i, Nonempty (Sec D i)) → ZLStable D → CenInt D → OnMtPreservesTypeV D → Nonempty (CenO D) := by
  first | exact @GlobalTheory.CenOAct.cenO_nonempty | exact GlobalTheory.CenOAct.cenO_nonempty | (intros; apply GlobalTheory.CenOAct.cenO_nonempty <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.heckeStableLocalLattice_of_rationalIntegrality : ∀ (D : D7) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M) (Q : D.what₂.places.Pl → Finset (PlE D.host)), (∀ i, D.nd.Q i = Q (D.nd.w i)) → (∀ j h1 h2 w, D.what₂.muAt w ≠ D.what₂.mu0 → LatInt D M (Q w) j h1 h2 w) → ∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → GlobalTheory.EtaJoin.LatStable Tn.B j w := by
  first | exact @GlobalTheory.LatTied.latStable_tied | exact GlobalTheory.LatTied.latStable_tied | (intros; apply GlobalTheory.LatTied.latStable_tied <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX

theorem blockAndTorsionExponentBounds_canonicalHubData : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D), GlobalTheory.HubX.Canon L HW R X → 1 ≤ L.sc.L → ∀ c : ℝ, 120 ≤ c → GlobalTheory.HubX.CondCB L X c ∧ KillingConditions.ConstantColumnBound L X c := by
  intro D L HW R X hX hL c hc
  have ht : 1 ≤ D.R.t := D.R.t_odd.pos
  have hn : 1 ≤ D.R.n := D.R.ord_pos
  have hnV : 1 ≤ D.R.nV := by
    show 1 ≤ D.R.r + D.R.t
    omega
  have htR : (1 : ℝ) ≤ D.R.t := by exact_mod_cast ht
  have hnR : (1 : ℝ) ≤ D.R.n := by exact_mod_cast hn
  have hnVR : (1 : ℝ) ≤ D.R.nV := by exact_mod_cast hnV
  have hN : 1 ≤ 4 * D.R.n * D.R.nV := by
    have := Nat.mul_le_mul hn hnV
    nlinarith
  have hb : L.sc.b = Real.exp L.sc.L := rfl
  have hLg : Formalism.MainNotions.TwistedPlaces.large₂ L = L.sc.L := rfl
  have hL0 : (0 : ℝ) ≤ L.sc.L := by linarith
  refine ⟨?_, ?_⟩
  · intro i _ _ _
    have hl : 2 ≤ D.nd.l i := (D.nd.lPrime i).out.two_le
    rw [hX.cB]
    have h := GlobalTheory.HubLoc.cBnum_le_thirty (D.nd.l i) D.R.t (4 * D.R.n * D.R.nV) L.sc.L hl ht hN hL
    simp only [cBof, hb, hLg]
    push_cast at h
    have hp : (0 : ℝ) ≤ (D.R.t : ℝ) * D.R.n * D.R.nV * L.sc.L := by positivity
    nlinarith
  · intro i _ _ _ _ u _
    have hl : 2 ≤ D.nd.l i := (D.nd.lPrime i).out.two_le
    rw [hX.c0]
    have h := GlobalTheory.HubLoc.torsionExponent_le_twentyFive_mul (D.nd.l i) (4 * D.R.n * D.R.nV) L.sc.L hl hN hL
    simp only [c0of, hOf, hb, hLg]
    push_cast at h ⊢
    have hp : (0 : ℝ) ≤ (D.R.n : ℝ) * D.R.nV * L.sc.L := by positivity
    nlinarith

end GlobalTheory.HubX
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX

theorem window_cLL_of_jumps_level_one (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (l h r n v : ℕ)
    [CharZero S.Qp] [FiniteDimensional S.Qp S.K] (hl : l.Prime)
    (hcard : Nat.card (S.K →ₐ[S.Qp] S.LL) = finrank S.Qp S.K) (hn : finrank S.Qp S.K ≤ n) (hr : 1 ≤ r)
    (hv : v ≤ LocalSituation.mN l 1 (h + h) - 1)
    (hU : ∀ τ : S.K →ₐ[S.Qp] S.LL, ∃ U : Finset ℤ, U.card ≤ r ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) ∧
      ∀ a, IsJumpV S.PD Y.ρ τ a → a ∈ U) :
    (∀ a ∈ LocalSituation.Jset S Y, -(h : ℤ) ≤ a ∧ a ≤ h) ∧
      LocalSituation.cLL l (LocalSituation.mN l 1 (h + h)) v (LocalSituation.Jset S Y) 0 1 ≤ 5 + Nat.log l (2 * h) + n * r * (4 + 2 * Nat.log l (2 * h)) := by
  classical
  choose U hUc hUb hUj using hU
  have hpos : 0 < finrank S.Qp S.K := finrank_pos
  have hfin : Finite (S.K →ₐ[S.Qp] S.LL) := Nat.finite_of_card_ne_zero (by omega)
  letI : Fintype (S.K →ₐ[S.Qp] S.LL) := Fintype.ofFinite _
  have hsub : LocalSituation.Jset S Y ⊆ ((Finset.univ.biUnion U : Finset ℤ) : Set ℤ) := by
    intro a ha
    obtain ⟨τ, hτ⟩ := GlobalTheory.HubLoc.jump_of_total S.PD Y.ρ hcard a ha
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨τ, Finset.mem_univ _, hUj τ a hτ⟩)
  have hb : ∀ u ∈ Finset.univ.biUnion U, -(h : ℤ) ≤ u ∧ u ≤ h := by
    intro u hu
    obtain ⟨τ, -, hτ⟩ := Finset.mem_biUnion.1 hu
    exact hUb τ u hτ
  have hc : (Finset.univ.biUnion U).card ≤ n * r := by
    refine (Finset.card_biUnion_le_card_mul _ _ r fun τ _ => hUc τ).trans (Nat.mul_le_mul_right _ ?_)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
    exact hn
  exact ⟨fun a ha => hb a (Finset.mem_coe.1 (hsub ha)),
    GlobalTheory.HubLoc.cLL_unit_interval_le l h (n * r) v _ _ hl (Nat.mul_pos (by omega) hr) hsub hc hb hv⟩

theorem cH0all_le_of_jumps_at_embeddings : ∀ (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hs : Good K 1 LL) (h r n : ℕ) (T : LocLat (LocalSituation.sit LT HW l (AI l) K 1 LL hs).G (LocalSituation.sit LT HW l (AI l) K 1 LL hs).Qp (LocalSituation.sit LT HW l (AI l) K 1 LL hs).LL (LocalSituation.sit LT HW l (AI l) K 1 LL hs).O), K.1 ≤ MaximalUnramifiedExtension l → finrank ℚ_[l] ↥K.1 ≤ n → 1 ≤ r → (∀ τ, ∃ U : Finset ℤ, U.card ≤ r ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) ∧ ∀ a, IsJumpV (LocalSituation.sit LT HW l (AI l) K 1 LL hs).PD T.ρ τ a → a ∈ U) → (∀ a ∈ LocalSituation.Jset (LocalSituation.sit LT HW l (AI l) K 1 LL hs) T, -(h : ℤ) ≤ a ∧ a ≤ h) ∧ GlobalTheory.HubX.invariantsCountConstant LT HW AI l K 1 LL hs h h T ≤ 5 + Nat.log l (2 * h) + n * r * (4 + 2 * Nat.log l (2 * h)) := by
  intro LT HW AI l _ K LL hs h r n T hK hn hr hU
  have hl : l.Prime := Fact.out

  have hK1 : K.1 ≤ Ks K 1 := GlobalTheory.HubLoc.le_Ks_one_of_Kur K hK
  have hsplit : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ LL.1 := by
    intro τ x
    have e := hs.2.2.2 ((τ.liftNormal (Om l)).comp (Ks K 1).val) ⟨x.1, hK1 x.2⟩
    have e2 : τ.liftNormal (Om l) (algebraMap ↥K.1 (Om l) x) = algebraMap (Om l) (Om l) (τ x) :=
      AlgHom.liftNormal_commutes τ (Om l) x
    have e3 : ((τ.liftNormal (Om l)).comp (Ks K 1).val) ⟨x.1, hK1 x.2⟩ = τ x := e2
    rwa [e3] at e
  have hcard : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 := GlobalTheory.HubLoc.card_emb K LL hsplit
  have := K.2
  have hm : 0 < LocalSituation.mN l 1 (h + h) := by unfold LocalSituation.mN; omega
  obtain ⟨h1, h2⟩ := GlobalTheory.HubLoc.padicValNat_finrank_Ks l K
  have e1 := h1 _ hm
  have e2 := h2 hK
  have hv : padicValNat l (finrank ℚ_[l] ↥(Ks K (LocalSituation.mN l 1 (h + h)))) - padicValNat l (finrank ℚ_[l] ↥K.1) ≤
      LocalSituation.mN l 1 (h + h) - 1 := by omega
  haveI : CharZero (LocalSituation.sit LT HW l (AI l) K 1 LL hs).Qp := (inferInstance : CharZero ℚ_[l])
  haveI : FiniteDimensional (LocalSituation.sit LT HW l (AI l) K 1 LL hs).Qp (LocalSituation.sit LT HW l (AI l) K 1 LL hs).K :=
    (inferInstance : FiniteDimensional ℚ_[l] ↥K.1)
  exact window_cLL_of_jumps_level_one (LocalSituation.sit LT HW l (AI l) K 1 LL hs) T l h r n _ hl hcard hn hr hv hU

end GlobalTheory.HubX
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.LengthH0Bound

theorem toNat_div_le (A B : ℕ∞) (r c : ℕ) (h : A ≤ (r : ℕ∞) * (c : ℕ∞) * B) :
    ((A.toNat : ℚ) / (B.toNat : ℚ)) ≤ (r : ℚ) * c := by
  rcases eq_or_ne B ⊤ with hB | hB
  · rw [hB, ENat.toNat_top, Nat.cast_zero, div_zero]; positivity
  obtain ⟨b, rfl⟩ := ENat.ne_top_iff_exists.mp hB
  have h' : A ≤ ((r * c * b : ℕ) : ℕ∞) := by push_cast; exact h
  obtain ⟨a, ha, hle⟩ := ENat.le_natCast_iff.mp h'
  subst ha
  rw [ENat.toNat_coe, ENat.toNat_coe]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [Nat.cast_zero, div_zero]; positivity
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast hle

theorem lenUnit_le_of_kill {O : Type} [CommRing O] [IsDomain O] (k p c : ℕ)
    (hp : algebraMap O (FractionRing O) (p : O) ≠ 0) (W : Submodule O (KOG O k))
    (hW : ∀ x ∈ W, (p : O) ^ c • x = 0) :
    lenUnit (O := O) p ↥W ≤ (k : ℚ) * c := by
  have hlen := length_le_of_killed (LL := FractionRing O) (stdG O (FractionRing O) k) _
    (GlobalTheory.FiniteTwistInvariants.stdG_eq_span k) (p : O) hp c W hW
  exact toNat_div_le _ _ k c hlen

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

theorem locM_entry {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (g : ↥(GK Bw.Kw)) (i j : Fin k) :
    Br.locM Bw M g i j = Br.toLLK Bw (algebraMap O (FractionRing O) (M (Br.ι Bw g) i j)) := by
  rw [Br.toLLK_alg]; rfl

theorem vecS_mulVec' {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (g : ↥(GK Bw.Kw)) (u : Fin k → FractionRing O) :
    Br.vecS Bw k ((mapM (algebraMap O (FractionRing O)) M (Br.ι Bw g)).mulVec u) =
      (Br.locM Bw M g).mulVec (Br.vecS Bw k u) := by
  funext i
  change Br.toLLK Bw (∑ j, algebraMap O (FractionRing O) (M (Br.ι Bw g) i j) * u j) =
    ∑ j, Br.locM Bw M g i j * Br.toLLK Bw (u j)

  simp only [map_sum, map_mul, locM_entry]



theorem phi_eq_zero {k : ℕ} (z : KOG O k) (hz : Br.phi Bw k z = 0) : z = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change (Submodule.Quotient.mk (Br.vecS Bw k y) :
    (Fin k → Br.LLw Bw) ⧸ stdG (Br.Ow Bw) (Br.LLw Bw) k) = 0 at hz
  rw [Submodule.Quotient.mk_eq_zero] at hz
  obtain ⟨b, hb⟩ := hz
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨fun j => Bw.eO.symm (b j), funext fun j => ?_⟩
  apply (Br.toLLK Bw).injective
  have hbj := congrFun hb j
  simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply] at hbj ⊢
  rw [Br.toLLK_alg, RingEquiv.apply_symm_apply]
  exact hbj



theorem actD_phi {Γ : Type} [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) O) (f : ↥Gw →* Γ)
    (gK : ↥(GK Bw.Kw)) (x : KOG O k) :
    actD (Br.lat Bw (M.comp f)) gK (Br.phi Bw k x) = Br.phi Bw k ((WKG M).comp f (Br.ι Bw gK) x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h := vecS_mulVec' Bw (M.comp f) gK y
  change (Submodule.Quotient.mk (((Br.locM Bw (M.comp f)) gK).mulVec (Br.vecS Bw k y)) :
      (Fin k → Br.LLw Bw) ⧸ stdG (Br.Ow Bw) (Br.LLw Bw) k) =
    Submodule.Quotient.mk (Br.vecS Bw k
      (((mapM (algebraMap O (FractionRing O)) (M.comp f)) (Br.ι Bw gK)).mulVec y))
  rw [h]


set_option synthInstance.maxHeartbeats 400000 in
theorem inv_killed {Γ : Type} [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) O) (f : ↥Gw →* Γ) (p c : ℕ)
    (h : ∀ y : (Fin k → Br.LLw Bw) ⧸ stdG (Br.Ow Bw) (Br.LLw Bw) k,
      (∀ gK, actD (Br.lat Bw (M.comp f)) gK y = y) → ((p : Br.Ow Bw) ^ c) • y = 0) :
    ∀ x ∈ Representation.invariants ((WKG M).comp f), (p : O) ^ c • x = 0 := by
  intro x hx
  have hfix : ∀ gK, actD (Br.lat Bw (M.comp f)) gK (Br.phi Bw k x) = Br.phi Bw k x := by
    intro gK
    rw [actD_phi, hx (Br.ι Bw gK)]
  have hk := h _ hfix
  apply phi_eq_zero Bw
  rw [LinearMap.map_smulₛₗ]
  simp only [map_pow, map_natCast]
  exact hk


include Bw in
theorem natCast_ne_zero : algebraMap O (FractionRing O) ((l : ℕ) : O) ≠ 0 := by
  intro h
  have h2 := congrArg (Br.toLLK Bw) h
  rw [map_natCast, map_natCast, map_zero] at h2
  have hQ : ((l : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  apply hQ
  apply (algebraMap ℚ_[l] (Br.LLw Bw)).injective
  rw [map_natCast, map_zero]
  exact h2

end Bridge



theorem main : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (u : HeightOneSpectrum (𝓞 D.host.E)) (hu : u ∈ placesOver D.host.E (D.nd.l i)) (s : ℕ)
    (hs : Good (D.nbr i u hu).Kw s (D.nbr i u hu).LL)
    (hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u))) g v) (c : ℕ),
    let S := LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i u hu).Kw s (D.nbr i u hu).LL hs;
    ∀ T : LocLat S.G S.Qp S.LL S.O, T = GlobalTheory.HubX.wLat D i ρ π u hu hc →
    (∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) → ((LocalSituation.ell S : S.O) ^ c) • x = 0) →
    (Br.h0W i u ρ π : ℝ) ≤ (D.R.r : ℝ) * c := by
  intro D HW i ρ π u hu s hs hc c S T hT hkill
  subst hT
  have hp : LocalSituation.ell S = D.nd.l i := (D.loc (D.nd.l i)).PD_p _
  have hK := inv_killed (D.nbr i u hu) (WpO D.nd i ρ π) (decS D.nd u) (D.nd.l i) c (fun y hy => by
    have := hkill y hy
    rwa [hp] at this)
  have hq := lenUnit_le_of_kill D.R.r (D.nd.l i) c (natCast_ne_zero (D.nbr i u hu)) _ hK
  exact_mod_cast hq

end GlobalTheory.LengthH0Bound
end
end

section


theorem _root_.GlobalTheory.T.parabolicInduction_comp_generalLinearGroupMapOfFieldEquiv : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), Continuous i → Continuous i.symm → (∀ x : kˣ, GlobalTheory.SplitWeil.nabs k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SplitWeil.nabs k x) → ∀ {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)), Nonempty (Representation.Equiv ((GlobalTheory.SmGL.multiProd e σ).comp (Matrix.GeneralLinearGroup.map (n := n) i.symm.toRingHom)) (GlobalTheory.SmGL.multiProd e fun a => (σ a).comp (Matrix.GeneralLinearGroup.map (n := m a) i.symm.toRingHom))) := by
  first | exact @GlobalTheory.IndField.multiProd_comp_glMap | exact GlobalTheory.IndField.multiProd_comp_glMap | (intros; apply GlobalTheory.IndField.multiProd_comp_glMap <;> assumption)
end
