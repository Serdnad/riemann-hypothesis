module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2823
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3096
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.ProjCurve

section SlopeTestRemainingChoices

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k}


open GlobalTheory.TwistTop in
theorem refines_trans {N L M : HermLB p} {π : N.B.ι → L.B.ι} {π' : L.B.ι → M.B.ι}
    (h : Refines N L π 0) (h' : Refines L M π' 0) : Refines N M (fun c => π' (π c)) 0 := by
  refine ⟨fun c => (h.le c).trans (h'.le _), ?_, ?_⟩
  · intro Z r z c c' hc hc'
    exact (h.g Z r z c c' hc hc').trans (h'.g Z r z _ _ (h.le _ hc) (h.le _ hc'))
  · intro σ c y hy
    rw [h.φ σ c y hy, h'.φ σ _ y (ptsIn_mono (h.le _) hy)]
    simp


open GlobalTheory.TwistTop in
theorem exists_refines_of_eq {N L L' : HermLB p} {π : N.B.ι → L.B.ι} (h : Refines N L π 0) (e : L = L') :
    ∃ π' : N.B.ι → L'.B.ι, Refines N L' π' 0 := by
  subst e
  exact ⟨π, h⟩

theorem pull_congr (L : HermLB p) {q : Y ⟶ Sp k} {f f' : Y ⟶ X} (e : f = f') (hf : f ≫ p = q)
    (hf' : f' ≫ p = q) : L.pull f hf = L.pull f' hf' := by
  subst e
  rfl

theorem isClosed_of_ne_generic {Z : Scheme.{0}} [IsIntegral Z] (hd : topologicalKrullDim Z = 1) {z : Z}
    (hz : z ≠ genericPoint Z) : IsClosed ({z} : Set Z) := by
  rcases Order.krullDim_le_one_iff.1 (show Order.krullDim (IrreducibleCloseds Z) ≤ 1 from hd.le)
    ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ with h | h
  · refine isClosed_of_closure_subset fun w hw => ?_
    have h₁ : (⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩ : IrreducibleCloseds Z) ≤
        ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ :=
      closure_minimal (Set.singleton_subset_iff.2 hw) isClosed_closure
    have h₂ : z ∈ closure {w} := h h₁ (subset_closure rfl)
    exact ((specializes_iff_mem_closure.2 h₂).antisymm (specializes_iff_mem_closure.2 hw)).eq
  · exact absurd (IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@h
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (Set.subset_univ _)))
      (genericPoint_spec Z)) hz

theorem log_card_residueField {W Z : Scheme.{0}} (g : W ⟶ Z) (w : W) [Finite (W.residueField w)] :
    Real.log (Nat.card (W.residueField w)) =
      (g.residueDegree w : ℝ) * Real.log (Nat.card (Z.residueField (g w))) := by
  letI := (g.residueFieldMap w).hom.toAlgebra
  have : Finite (Z.residueField (g w)) := Finite.of_injective _ (g.residueFieldMap w).hom.injective
  have : Module.Finite (Z.residueField (g w)) (W.residueField w) := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := Z.residueField (g w)) (V := W.residueField w), Nat.cast_pow,
    Real.log_pow]
  rfl

end SlopeTestRemainingChoices


open GlobalTheory.TwistTop in
theorem main : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ),
    IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ),
    L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ y : Y, CharZero Γ(clo y, ⊤) → HasDim y 1 →
    h' y = (π.residueDegree y : ℝ) * h (π y) := by
  intro k _ X Y p q D E hX hY π hπ L h h' H H' y hc hy
  have hAX := isAmb_of_isArithVar hX
  have hAY := isAmb_of_isArithVar hY
  have := hAX.isNoetherian
  have := hAY.isNoetherian
  obtain ⟨g, hgc, hgη, hgdeg⟩ := GlobalTheory.T.exists_dominant_restriction_pointClosures X Y π y
  have D₁ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q hAY
  have D₂ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hAX

  have hdW : topologicalKrullDim (clo y) = 1 := by
    have h₁ := (D₁.2.2.2.2.1 (clo y) (cloι y) (genericPoint (clo y)) 1).1 (by rw [cloι_genericPoint]; exact hy)
    have h₂ := (D₁.2.2.2.2.2 (clo y) 1).1 h₁
    rw [h₂]
    rfl

  have hcZ : CharZero Γ(clo (π y), ⊤) := g.appTop.hom.charZero

  obtain ⟨m, hm⟩ := D₂.1
  obtain ⟨d', -, hd'⟩ := hm (π y)
  have hdZ' : topologicalKrullDim (clo (π y)) = d' :=
    (D₂.2.2.2.2.2 (clo (π y)) d').1 ((D₂.2.2.2.2.1 (clo (π y)) (cloι (π y)) _ d').1
      (by rw [cloι_genericPoint]; exact hd'))
  obtain ⟨hle, hiff⟩ := GlobalTheory.T.pointClosureDim_le_and_residueDegree_ne_zero_iff k X Y p q hAX hAY π hπ y 1 d' hy hd'
  have hd1 : d' = 1 := by
    have h0 : d' ≠ 0 := by
      rintro rfl
      exact hX.dim_ne_zero (cloι (π y)) hcZ (hdZ'.trans (by rfl))
    omega
  subst hd1
  have hdZ : topologicalKrullDim (clo (π y)) = 1 := hdZ'.trans (by rfl)
  have hdeg : π.residueDegree y ≠ 0 := hiff.2 rfl
  have hdegη : g.residueDegree (genericPoint (clo y)) = π.residueDegree y := by
    rw [hgdeg, cloι_genericPoint]
  have hW : IsArithVar (cloι y ≫ q) 0 := hY.of_isClosedImmersion (cloι y) hc hdW
  have hZ : IsArithVar (cloι (π y) ≫ p) 0 := hX.of_isClosedImmersion (cloι (π y)) hcZ hdZ

  obtain ⟨r, hr⟩ := exists_isRatSec (L.restr (cloι (π y))).isLB
  have hg' : g ≫ cloι (π y) ≫ p = cloι y ≫ q := by
    rw [← Category.assoc, hgc, Category.assoc, hπ]
  have hr' := MultPull.isRatSec_pull_map g (hgη ▸ specializes_rfl : g (genericPoint (clo y)) ⤳ genericPoint _) hr

  have h₁ : (cloι y ≫ π) ≫ p = cloι y ≫ q := by rw [Category.assoc, hπ]
  have h₂ : (g ≫ cloι (π y)) ≫ p = cloι y ≫ q := by rw [hgc, h₁]
  obtain ⟨ρ, hρ⟩ := exists_refines_of_eq (L.refines_pull_pull π hπ (cloι y) rfl h₁)
    (pull_congr L hgc.symm h₁ h₂)
  have hρ' := refines_trans hρ (L.refines_pull_comp (cloι (π y)) rfl g hg' h₂)

  have e₁ := H'.point (clo y) (cloι y) hc hdW _ (hρ'.isRatSec hr')
  rw [cloι_genericPoint] at e₁
  have e₂ : ((L.pull π hπ).restr (cloι y)).curveDeg (hρ'.isRatSec hr') =
      ((L.restr (cloι (π y))).pull g hg').curveDeg hr' := by
    unfold HermLB.curveDeg
    rw [hρ'.div hr']
    refine congrArg _ (finsum_congr fun σ => finsum_congr fun z => hρ'.logNorm hr' (mem_offSupp.2 ?_))
    rw [under_eq_genericPoint hW z]
    exact CartierDiv.genericPoint_notMem_supp _

  have e₃ := H.point (clo (π y)) (cloι (π y)) hcZ hdZ r hr
  rw [cloι_genericPoint] at e₃

  have a₁ := GlobalTheory.ArchDimZero.main k (clo y) (cloι y ≫ q) hW ((L.restr (cloι (π y))).pull g hg')
    ((L.restr (cloι (π y))).pull g hg') _ hr'
  have a₂ := GlobalTheory.T.archimedeanIntegral_pull_mul_degree k (clo (π y)) (clo y) (cloι (π y) ≫ p) (cloι y ≫ q) 0 hZ hW g hg' hgη
    (hdegη ▸ hdeg) (L.restr (cloι (π y))) (L.restr (cloι (π y))) r hr
  have a₃ := GlobalTheory.ArchDimZero.main k (clo (π y)) (cloι (π y) ≫ p) hZ (L.restr (cloι (π y)))
    (L.restr (cloι (π y))) r hr

  have f₁ := GlobalTheory.T.finsum_mult_pullback_rationalSection_pushforward k (clo (π y)) (clo y) (cloι (π y) ≫ p) (cloι y ≫ q) (hAX.sub _) (hAY.sub _) g hg' hgη
    (L.restr (cloι (π y))).B (L.restr (cloι (π y))).isLB r hr (fun z => Real.log (Nat.card ((clo (π y)).residueField z)))
  have f₂ : ∑ᶠ w, ((((L.restr (cloι (π y))).pull g hg').div hr').mult w : ℝ) *
      Real.log (Nat.card ((clo y).residueField w)) =
      ∑ᶠ w, ((((L.restr (cloι (π y))).pull g hg').div hr').mult w : ℝ) *
      ((g.residueDegree w : ℝ) * Real.log (Nat.card ((clo (π y)).residueField (g w)))) := by
    refine finsum_congr fun w => ?_
    by_cases hw : (((L.restr (cloι (π y))).pull g hg').div hr').mult w = 0
    · rw [hw, Int.cast_zero, zero_mul, zero_mul]
    have hne : w ≠ genericPoint (clo y) := fun e =>
      CartierDiv.genericPoint_notMem_supp _ (e ▸ CartierDiv.mem_supp_of_mult_ne_zero hw)
    have := hW.finite_residueField (isClosed_of_ne_generic hdW hne)
    rw [log_card_residueField g w]
  rw [e₁, e₂, e₃]
  unfold HermLB.curveDeg
  rw [← a₁, ← a₃, f₂]
  rw [hdegη] at f₁ a₂
  rw [a₂]
  erw [f₁]
  ring

end GlobalTheory.ProjCurve
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

open GlobalTheory.TwistTop

namespace GlobalTheory.ProjStep

theorem archInt_refines {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {N L : HermLB p} {ρ : N.B.ι → L.B.ι} (h : Refines N L ρ 0) {r : L.B.ι → X.functionFieldˣ}
    (hr : IsRatSec L.B r) (e : ℕ) :
    N.archInt N e (h.isRatSec hr) = L.archInt L e hr := by
  unfold HermLB.archInt
  rw [h.div hr]
  refine finsum_congr fun σ => ?_
  rw [h.chernInt]
  exact Weight.chernInt_congr (isOpen_offSupp _).measurableSet fun y hy => h.logNorm hr hy

end GlobalTheory.ProjStep

namespace GlobalTheory.ProjStep

theorem main : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ), L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ (y : Y) (e : ℕ), CharZero Γ(clo y, ⊤) → HasDim y (e + 1 + 1) → (∀ w : Y, HasDim w (e + 1) → h' w = (π.residueDegree w : ℝ) * h (π w)) → h' y = (π.residueDegree y : ℝ) * h (π y) := by
  intro k _ X Y p q D E hX hY π hπ L h h' H H' y e hc hy hrec
  have hAX : IsAmb p := isAmb_of_isArithVar hX
  have hAY : IsAmb q := isAmb_of_isArithVar hY
  have := hX.isNoetherian
  have := hY.isNoetherian
  obtain ⟨hbdX, -, -, -, hsubX, hgenX⟩ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hAX
  obtain ⟨-, -, -, -, hsubY, hgenY⟩ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q hAY
  obtain ⟨g, hgc, hgη, hgdeg⟩ := GlobalTheory.T.exists_dominant_restriction_pointClosures X Y π y

  have hdW : topologicalKrullDim (clo y) = ((e + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    refine (hgenY (clo y) (e + 1 + 1)).1 ((hsubY (clo y) (cloι y) _ _).1 ?_)
    rw [cloι_genericPoint]; exact hy
  have hcZ : CharZero Γ(clo (π y), ⊤) := g.appTop.hom.charZero
  have hg1 : g ≫ cloι (π y) ≫ p = cloι y ≫ q := by
    rw [← Category.assoc, hgc, Category.assoc, hπ]
  have hC : (g ≫ cloι (π y)) ≫ p = cloι y ≫ q := by rw [Category.assoc]; exact hg1
  have hη' : g (genericPoint (clo y)) ⤳ genericPoint (clo (π y)) := hgη ▸ specializes_rfl
  have happ (w : clo y) : π (cloι y w) = cloι (π y) (g w) := by
    have := congrArg (fun f : clo y ⟶ X => f w) hgc
    simpa using this.symm
  have hδ : g.residueDegree (genericPoint (clo y)) = π.residueDegree y := by
    rw [hgdeg, cloι_genericPoint]

  obtain ⟨r, hr⟩ := exists_isRatSec (L.restr (cloι (π y))).isLB
  have hr1 := MultPull.isRatSec_pull_map g hη' hr
  have ref1 : Refines (L.pull (g ≫ cloι (π y)) hC)
      ((L.restr (cloι (π y))).pull g hg1) (fun c _ => c) 0 := by
    refine { le := ?_, g := ?_, φ := ?_ }
    · intro c z hz
      exact Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun a => Set.mem_iInter.1 hz a
    · intro W s z c c' hc hc'
      have h₁ : (s ≫ g) z ∈ (L.B.pull (cloι (π y))).U c := Set.mem_iInter.2 fun a => Set.mem_iInter.1 hc a
      have h₂ : (s ≫ g) z ∈ (L.B.pull (cloι (π y))).U c' := Set.mem_iInter.2 fun a => Set.mem_iInter.1 hc' a
      have h₃ : s z ∈ ((L.B.pull (cloι (π y))).pull g).U (fun _ => c) := Set.mem_iInter.2 fun _ => h₁
      have h₄ : s z ∈ ((L.B.pull (cloι (π y))).pull g).U (fun _ => c') := Set.mem_iInter.2 fun _ => h₂
      have e₁ := gm_pull_g (L.B.pull (cloι (π y))) g s z (fun _ => c) (fun _ => c') h₃ h₄
      have e₂ := gm_pull_g L.B (cloι (π y)) (s ≫ g) z c c' h₁ h₂
      have e₃ := gm_pull_g L.B (g ≫ cloι (π y)) s z c c' hc hc'
      rw [← Category.assoc] at e₃
      exact e₃.trans (e₁.trans e₂).symm
    · intro σ c z hz
      refine ((L.φ σ).pull_φ (g ≫ cloι (π y)) hC c z).trans (Eq.symm ((add_zero _).trans ?_))
      refine (((L.restr (cloι (π y))).φ σ).pull_φ g hg1 (fun _ => c) z).trans (((L.φ σ).pull_φ (cloι (π y)) rfl _ _).trans ?_)
      exact congrArg _ (Subtype.ext (Category.assoc _ _ _))
  have hrC := ref1.isRatSec hr1
  obtain ⟨ρ, ref2⟩ : ∃ ρ, Refines ((L.pull π hπ).restr (cloι y)) (L.pull (g ≫ cloι (π y)) hC) ρ 0 := by
    have key : ∀ (f : clo y ⟶ X) (hf : f ≫ p = cloι y ≫ q), f = cloι y ≫ π →
        ∃ ρ, Refines ((L.pull π hπ).restr (cloι y)) (L.pull f hf) ρ 0 := by
      rintro f hf rfl
      refine ⟨fun c => c PUnit.unit, { le := ?_, g := ?_, φ := ?_ }⟩
      · intro c z hz
        exact Set.mem_iInter.2 fun a => Set.mem_iInter.1 (Set.mem_iInter.1 hz PUnit.unit) a
      · intro W s z c c' hc hc'
        have h₁ := Set.mem_iInter.1 hc PUnit.unit
        have h₂ := Set.mem_iInter.1 hc' PUnit.unit
        refine (gm_pull_g _ (cloι y) s z c c' hc hc').trans ((gm_pull_g _ π (s ≫ cloι y) z _ _ h₁ h₂).trans ?_)
        refine Eq.trans ?_ (gm_pull_g _ (cloι y ≫ π) s z (c PUnit.unit) (c' PUnit.unit)
          (Set.mem_iInter.2 fun a => Set.mem_iInter.1 h₁ a) (Set.mem_iInter.2 fun a => Set.mem_iInter.1 h₂ a)).symm
        rw [Category.assoc]
      · intro σ c z hz
        refine (((L.pull π hπ).φ σ).pull_φ (cloι y) rfl c z).trans (((L.φ σ).pull_φ π hπ _ _).trans ?_)
        refine Eq.trans ?_ (((L.φ σ).pull_φ (cloι y ≫ π) hf (c PUnit.unit) z).symm.trans (add_zero _).symm)
        exact congrArg _ (Subtype.ext (Category.assoc _ _ _))
    exact key _ hC hgc
  have hrA := ref2.isRatSec hrC
  obtain ⟨-, hrecW⟩ := H'.recursion_one (cloι y) hc (by omega : 1 ≤ e + 1) hdW hrA
  rw [cloι_genericPoint] at hrecW
  have ediv : ((L.pull π hπ).restr (cloι y)).div hrA = (((L.restr (cloι (π y))).pull g hg1)).div hr1 :=
    (ref2.div hrC).trans (ref1.div hr1)
  have earch : ((L.pull π hπ).restr (cloι y)).archInt ((L.pull π hπ).restr (cloι y)) (e + 1) hrA =
      ((L.restr (cloι (π y))).pull g hg1).archInt ((L.restr (cloι (π y))).pull g hg1) (e + 1) hr1 :=
    (archInt_refines ref2 hrC (e + 1)).trans (archInt_refines ref1 hr1 (e + 1))
  have hsum : ∑ᶠ w, ((((L.pull π hπ).restr (cloι y)).div hrA).mult w : ℝ) * h' (cloι y w) =
      (π.residueDegree y : ℝ) * ∑ᶠ z, (((L.restr (cloι (π y))).div hr).mult z : ℝ) * h (cloι (π y) z) := by
    rw [ediv, ← hδ]
    refine Eq.trans (finsum_congr fun w => ?_) (GlobalTheory.T.finsum_mult_pullback_rationalSection_pushforward k (clo (π y)) (clo y) (cloι (π y) ≫ p) (cloι y ≫ q)
      (hAX.sub _) (hAY.sub _) g hg1 hgη (L.restr (cloι (π y))).B (L.restr (cloι (π y))).isLB r hr
      (fun z => h (cloι (π y) z)))
    by_cases hm : ((((L.restr (cloι (π y))).pull g hg1)).div hr1).mult w = 0
    · have hm' : ((((L.restr (cloι (π y))).pull g hg1)).div hr1).mult w = 0 := hm
      rw [hm, Int.cast_zero, zero_mul]
      exact (mul_eq_zero_of_left (Int.cast_eq_zero.2 hm) _).symm
    · have hco := CartierDiv.coheight_eq_one_of_mult_ne_zero hm
      have hd1 := ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k (clo y) (cloι y ≫ q) (hAY.sub _) (e + 1) hdW).1 w).1 hco
      have hd2 := (hsubY (clo y) (cloι y) w (e + 1)).2 hd1
      rw [hrec _ hd2, happ, hgdeg]
      rfl

  obtain ⟨m, hm⟩ := hbdX
  obtain ⟨d', -, hd'⟩ := hm (π y)
  obtain ⟨hle, hiff⟩ := GlobalTheory.T.pointClosureDim_le_and_residueDegree_ne_zero_iff k X Y p q hAX hAY π hπ y (e + 1 + 1) d' hy hd'
  have hdZ : topologicalKrullDim (clo (π y)) = (d' : WithBot ℕ∞) := by
    refine (hgenX (clo (π y)) d').1 ((hsubX (clo (π y)) (cloι (π y)) _ _).1 ?_)
    rw [cloι_genericPoint]; exact hd'
  have hWv := hY.of_isClosedImmersion (cloι y) hc hdW
  rw [hsum, earch] at hrecW
  by_cases h0 : π.residueDegree y = 0
  ·
    have hlt : d' < e + 1 + 1 := lt_of_le_of_ne hle fun h1 => hiff.2 h1.symm h0
    have hd0 : d' ≠ 0 := fun h2 => hX.dim_ne_zero (cloι (π y)) hcZ (by rw [hdZ, h2]; rfl)
    obtain ⟨e0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
    have hZv0 := hX.of_isClosedImmersion (cloι (π y)) hcZ (e := e0) hdZ
    have hzero (σ : k →+* ℂ) (ε : ℤˣ) :
        (((L.restr (cloι (π y))).pull g hg1).φ σ).chernPart (e + 1) ε = 0 :=
      GlobalTheory.T.chernForm_topPower_pullback_smaller_dim_eq_zero k (clo (π y)) (clo y) (cloι (π y) ≫ p) (cloι y ≫ q) e0 (e + 1) hZv0 hWv (by omega) g hg1 hgη
        (L.restr (cloι (π y))) σ ε
    have harch0 : ((L.restr (cloι (π y))).pull g hg1).archInt ((L.restr (cloι (π y))).pull g hg1) (e + 1) hr1 = 0 := by
      unfold HermLB.archInt Weight.chernInt
      simp [hzero]
    rw [harch0, h0] at hrecW
    rw [hrecW, h0]
    simp
  ·
    have hde : d' = e + 1 + 1 := (hiff.1 h0).symm
    subst hde
    have hZv := hX.of_isClosedImmersion (cloι (π y)) hcZ hdZ
    obtain ⟨-, hrecZ⟩ := H.recursion_one (cloι (π y)) hcZ (by omega : 1 ≤ e + 1) hdZ hr
    rw [cloι_genericPoint] at hrecZ
    have hpa := GlobalTheory.T.archimedeanIntegral_pull_mul_degree k (clo (π y)) (clo y) (cloι (π y) ≫ p) (cloι y ≫ q) (e + 1) hZv hWv g hg1 hgη
      (hδ ▸ h0) (L.restr (cloι (π y))) (L.restr (cloι (π y))) r hr
    rw [hδ] at hpa
    rw [hrecW, hpa, hrecZ]
    ring

end GlobalTheory.ProjStep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.E8Endomorphism

open GlobalTheory.Poinc.Sep.EndCompat

theorem lattice_of_charMap {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (S a a' : Matrix (Fin 8) (Fin 8) ℤ)
    (hS : S.transpose = S) (hSa : S * a' = a.transpose * S) (c : Fin 8 → (X →+ Y)) (e : Y ≃+ (Fin 8 → X))
    (hT : ∀ y, ∑ v, c v (∑ u, S v u • e y u) = y) (h : Y →+ Y) (hh : ∀ u χ, h (c u χ) = ∑ v, a' u v • c v χ)
    (y : Y) : e (h y) = fun u => ∑ v, a u v • e y v := by
  have hM' : a'.transpose * S = S * a := by
    have := congrArg Matrix.transpose hSa
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hS] at this
  have hM : ∀ w u, ∑ v, a' v w * S v u = ∑ x, S w x * a x u := fun w u => by
    have := congrFun (congrFun hM' w) u
    simpa [Matrix.mul_apply] using this
  have key : ∀ x : Fin 8 → X, ∑ v, c v (∑ u, S v u • x u) = e.symm x := by
    intro x
    conv_rhs => rw [← hT (e.symm x)]
    simp
  apply e.symm.injective
  rw [AddEquiv.symm_apply_apply, ← key]
  conv_lhs => rw [← hT y]

  simp only [map_sum, map_zsmul, hh, Finset.smul_sum, smul_smul]
  have L : ∀ f : Fin 8 → Fin 8 → Fin 8 → Y, ∑ v, ∑ u, ∑ w, f v u w = ∑ w, ∑ u, ∑ v, f v u w := fun f => by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun u _ => Finset.sum_comm]
    rw [Finset.sum_comm]
  calc ∑ v, ∑ u, ∑ w, (S v u * a' v w) • c w (e y u)
      = ∑ w, ∑ u, ∑ v, (S v u * a' v w) • c w (e y u) := L (fun v u w => (S v u * a' v w) • c w (e y u))
    _ = ∑ w, ∑ u, (∑ v, a' v w * S v u) • c w (e y u) := by
        refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun v _ => by rw [mul_comm]
    _ = ∑ w, ∑ u, (∑ x, S w x * a x u) • c w (e y u) := by simp only [hM]
    _ = ∑ w, ∑ x, ∑ u, (S w x * a x u) • c w (e y u) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_smul

theorem endU_lattice_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (a a' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ E' : GlobalTheory.UT.EndU U'.toUnifPre, (∀ u, E'.aA ≫ pr u = (List.ofFn fun v => pr v ^ a' u v).prod) → ∀ y, e (E'.h y) = fun u => ∑ v, a u v • e y v := by
  intro R _ _ _ hB hDVR G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniqA hL pG hpG hpGc c hc e he a a' haa' E' hE' y
  have hCN : GlobalTheory.TorRef.IsCN R := ⟨hB.1.1, hB.1.2.2.1, hB.1.2.2.2, hB.2⟩
  haveI : IsNoetherianRing R := hCN.1
  haveI : IsIntegrallyClosed R := hCN.2.1
  haveI := E'.homG
  haveI := U.gen_hom
  have hstep : ∀ u, E'.aG ≫ pG u = (List.ofFn fun v => pG v ^ a' u v).prod := by
    intro u
    haveI := hpG u
    have hR : IsMonHom (List.ofFn fun v => pG v ^ a' u v).prod := by
      refine isMonHom_of_mul _ fun T x z => ?_
      have key : ∀ w : T ⟶ G', w ≫ (List.ofFn fun v => pG v ^ a' u v).prod = ∏ v, (w ≫ pG v) ^ a' u v := fun w => by
        rw [← List.prod_ofFn]
        exact map_ofFn_prod (preH w) pG (a' u)
      rw [key, key, key, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      haveI := hpG v
      rw [MonObj.mul_comp, mul_zpow]
    obtain ⟨F0, -, huniq⟩ := GlobalTheory.semiAbelianHomExtension_holds.fractionField R (FractionRing R) G' G hG' hG
      ((Over.pullback (jK R)).map (E'.aG ≫ pG u))
    refine (huniq _ ⟨inferInstance, rfl⟩).trans (huniq _ ⟨hR, ?_⟩).symm
    rw [← cancel_mono U.gen.hom]
    have e1 : (Over.pullback (jK R)).map (E'.aG ≫ pG u) ≫ U.gen.hom =
        U'.gen.hom ≫ (List.ofFn fun v => pr v ^ a' u v).prod := by
      rw [Functor.map_comp, Category.assoc, hpGc u, ← Category.assoc, E'.ext, Category.assoc, hE' u]
    rw [e1]
    calc (Over.pullback (jK R)).map (List.ofFn fun v => pG v ^ a' u v).prod ≫ U.gen.hom
        = ((postH U.gen.hom U.gen_hom).comp (pullH (jK R) G' G)) (List.ofFn fun v => pG v ^ a' u v).prod := rfl
      _ = (List.ofFn fun v => ((postH U.gen.hom U.gen_hom).comp (pullH (jK R) G' G)) (pG v) ^ a' u v).prod :=
          map_ofFn_prod _ pG (a' u)
      _ = (List.ofFn fun v => preH U'.gen.hom (pr v) ^ a' u v).prod :=
          congrArg (fun z : Fin 8 → _ => (List.ofFn fun v => z v ^ a' u v).prod) (funext hpGc)
      _ = preH U'.gen.hom (List.ofFn fun v => pr v ^ a' u v).prod := (map_ofFn_prod _ pr (a' u)).symm
      _ = U'.gen.hom ≫ (List.ofFn fun v => pr v ^ a' u v).prod := rfl
  have hEC := GlobalTheory.Poinc.Eq8.endChar_endU R hCN D' A' G' hG' U' E'
  have hh := GlobalTheory.T.characterMap_of_integral_matrix_action R hCN D A G hG U D' A' G' hG' U' pG hpG c hc a' E'.aG E'.h E'.homG hEC hstep
  exact lattice_of_charMap (W + W.transpose) a a' (by rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm])
    haa' c e he E'.h hh y

end GlobalTheory.Poinc.E8Endomorphism
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.coordinateMap_etale_near_properFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (E : Emb M.π G') (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), a ≫ b = X.ι ≫ E.f → ∀ (x : P') (y : E.Y.left), E.j y = b x → (b ≫ PSpace.str R E.N) x = closedPoint R → ∀ (W0 : (PSpace R E.N).Opens) (g : ℕ) (τ0 : W0.toScheme ⟶ 𝔸(Fin g; Sp R)) (O : E.Y.left.Opens) (e : O.toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) (spMap (residue R))), y ∈ O → (O : Set E.Y.left) ⊆ E.j ⁻¹' W0 → τ0 ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = W0.ι ≫ PSpace.str R E.N → Etale e → e ≫ pullback.snd _ _ = O.ι ≫ E.Y.hom → (∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (w : T ⟶ W0.toScheme), w ≫ W0.ι = t ≫ O.ι ≫ E.j → t ≫ e ≫ pullback.fst _ _ = w ≫ τ0) → ∀ (c : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) M.π), c ≫ pullback.fst _ _ = (a ∣_ (b ⁻¹ᵁ W0)) ≫ (b ∣_ W0) ≫ τ0 → c ≫ pullback.snd _ _ = (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom → ∀ z : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme, ((a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ a) z = x → ∃ U : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme.Opens, z ∈ U ∧ Etale (U.ι ≫ c) := by
  first | exact @GlobalTheory.Mum.fibre_etale_near | exact GlobalTheory.Mum.fibre_etale_near | (intros; apply GlobalTheory.Mum.fibre_etale_near <;> assumption)
end
