module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3269
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3051
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3330
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineLeOrDisjoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonoFamThrough
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2928
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2958
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.semiAbelian_descends_near_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∀ φ, N.Datum φ → ∃ (G : Over (Sp R)) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), Smooth G.hom ∧ IsPullback β G'.hom G.hom π ∧ IsOpenImmersion i.left ∧ N.u ≫ β = pullback.fst _ _ ≫ i.left ∧ pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β := by
  first | exact @GlobalTheory.Mum.descends_near_closed_fibre | exact GlobalTheory.Mum.descends_near_closed_fibre | (intros; apply GlobalTheory.Mum.descends_near_closed_fibre <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem Total.comp {X : Scheme.{0}} [IsIntegral X] {J J' : Type} {f : J → X.functionField} (h : Total f)
    (ι : J' → J) : Total (f ∘ ι) :=
  ⟨fun j => h.1 (ι j), fun x j l => h.2 x (ι j) (ι l)⟩

theorem selfInter_nonneg_of_isFS (hC : GlobalTheory.Published.ArCalc) (hA : AmpleHS) (hS : SemiPull) {k : Type} [CommRing k]
    {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D) {M : HermLB p} {J : Type} [Fintype J]
    {f : J → X.functionField} {w : J → ℝ} (hM : IsFS M f w) (hw : ∀ j, 0 ≤ w j) {μ : ℝ} (hμ : M.IsSelfInter μ) :
    0 ≤ μ := by
  have hnef := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M J f w hM hw
  have hht := (GlobalTheory.T.arithKleiman_heightNef_of_isNef hC hA hS k X p D hX M hnef).2
  obtain ⟨h, hh, rfl⟩ := hμ
  exact hht h hh _

theorem levels_le_selfInter (hC : GlobalTheory.Published.ArCalc) (hA : AmpleHS) (hS : SemiPull) (k : Type) [CommRing k]
    (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsArithVar p D) (x : Fin D → X.functionField) (Δ : ℝ)
    (hx : AlgebraicIndependent ℤ x) (hΔ : 0 < Δ) :
    ∀ (N : ℕ) (J : Type) [Fintype J] (e : J → X.functionField) (n : J → ℕ) (M : HermLB p) (μ : ℝ),
      LinearIndependent ℤ e → (∀ j, n j ≤ N) → Total (boxFam e x) → IsFS M (boxFam e x) (fun c => n c.1 * Δ) →
      M.IsSelfInter μ → ((D + 1).factorial : ℝ) * Δ * ∑ j, (n j : ℝ) ≤ μ := by
  intro N
  induction N with
  | zero =>
    intro J _ e n M μ _ hn _ hM hμ
    have h0 : ∀ j, n j = 0 := fun j => Nat.le_zero.1 (hn j)
    simp only [h0, Nat.cast_zero, Finset.sum_const_zero, mul_zero]
    exact selfInter_nonneg_of_isFS hC hA hS hX hM (fun c => by simp [h0]) hμ
  | succ N ih =>
    intro J _ e n M μ he hn ht hM hμ
    classical
    have hw0 : ∀ c : J × Finset (Fin D), 0 ≤ (n c.1 : ℝ) * Δ := fun c => by positivity
    by_cases hJ : ∀ j, n j = 0
    · simp only [hJ, Nat.cast_zero, Finset.sum_const_zero, mul_zero]
      exact selfInter_nonneg_of_isFS hC hA hS hX hM hw0 hμ
    push_neg at hJ
    obtain ⟨j₀, hj₀⟩ := hJ
    let J' := {j // 1 ≤ n j}
    let e' : J' → X.functionField := fun j => e j.1
    let n' : J' → ℕ := fun j => n j.1 - 1
    let ι : J' × Finset (Fin D) → J × Finset (Fin D) := fun c => (c.1.1, c.2)
    have hι : Function.Injective ι := by
      rintro ⟨⟨a, ha⟩, s⟩ ⟨⟨b, hb⟩, t⟩ h
      simp only [ι, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    have hbox : boxFam e' x = boxFam e x ∘ ι := rfl
    haveI : Nonempty (J' × Finset (Fin D)) := ⟨(⟨j₀, Nat.one_le_iff_ne_zero.2 hj₀⟩, ∅)⟩
    have ht' : Total (boxFam e' x) := hbox ▸ ht.comp ι
    obtain ⟨M', hM'⟩ := GlobalTheory.T.exists_fubiniStudy_of_totallyOrdered_ratFnFamily k X p (J' × Finset (Fin D)) (boxFam e' x) (fun c => (n' c.1 : ℝ) * Δ) ht'
    obtain ⟨h', hh'⟩ := (hC.arExists k X p D hX).1 M'
    have hμ' : M'.IsSelfInter (h' (genericPoint X)) := ⟨h', hh', rfl⟩
    have he' : LinearIndependent ℤ e' := he.comp _ Subtype.val_injective
    have hn' : ∀ j, n' j ≤ N := fun j => by
      have := hn j.1
      simp only [n']
      omega
    have IH := ih J' e' n' M' _ he' hn' ht' hM' hμ'
    have hw0' : ∀ c : J' × Finset (Fin D), 0 ≤ (n' c.1 : ℝ) * Δ := fun c => by positivity
    have hstep : ∀ c : J' × Finset (Fin D), (n' c.1 : ℝ) * Δ + Δ ≤ (n (ι c).1 : ℝ) * Δ := fun c => by
      have h1 := c.1.2
      simp only [n', ι]
      rw [Nat.cast_sub h1]
      push_cast
      linarith
    have hle : Le (M'.shift (fun _ => Δ) fun _ => rfl) M :=
      GlobalTheory.T.fubiniStudy_subfamily_le_shift_fubiniStudy_family k X p M M' (J × Finset (Fin D)) (J' × Finset (Fin D)) (boxFam e x) (fun c => (n c.1 : ℝ) * Δ)
        (fun c => (n' c.1 : ℝ) * Δ) ι Δ hι hM (hbox ▸ hM') hstep
    have hnefM := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M _ _ _ hM hw0
    have hnefM' := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M' _ _ _ hM' hw0'
    have hnefS := GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX M' Δ hΔ.le hnefM'
    have hsh := hC.arShift k X p D hX M' _ Δ hμ'
    have hmono := GlobalTheory.T.arithSelfIntersection_mono_of_isNef hC hA hS k X p D hX M _ μ _ hnefM hnefS hle hμ hsh
    have hrk := GlobalTheory.T.rank_le_fubiniStudy_boxFamily hC hA k X p D hX M' J' e' x (fun c => (n' c.1 : ℝ) * Δ) he' hx hw0' hM'
    have hsum : ∑ j, (n j : ℝ) = ∑ j : J', (n' j : ℝ) + Fintype.card J' := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun j => 1 ≤ n j) (fun j => (n j : ℝ))]
      have h2 : ∑ j : {j // ¬ 1 ≤ n j}, (n j.1 : ℝ) = 0 :=
        Finset.sum_eq_zero fun j _ => by
          have := j.2
          have : n j.1 = 0 := by omega
          simp [this]
      rw [h2, add_zero]
      have h3 : ∀ j : J', (n j.1 : ℝ) = (n' j : ℝ) + 1 := fun j => by
        simp only [n']
        rw [Nat.cast_sub j.2]
        ring
      simp only [h3, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rfl
    have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hcard : ((D + 1).factorial : ℝ) * Δ * Fintype.card J' ≤ ((D : ℝ) + 1) * Δ * gdeg M' D := by
      calc ((D + 1).factorial : ℝ) * Δ * Fintype.card J' = ((D : ℝ) + 1) * Δ * (D.factorial * Fintype.card J') := by
            rw [hf]; ring
        _ ≤ ((D : ℝ) + 1) * Δ * gdeg M' D := mul_le_mul_of_nonneg_left hrk (by positivity)
    rw [hsum, mul_add]
    linarith

theorem chain_moving_parts : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (N : ℕ) (J : Type) [Fintype J] (e : J → X.functionField) (n : J → ℕ) (M : HermLB p) (μ : ℝ), LinearIndependent ℤ e → (∀ j, n j ≤ N) → Total (boxFam e x) → IsFS M (boxFam e x) (fun c => n c.1 * Δ) → M.IsSelfInter μ → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ μ + ((D : ℝ) + 1) * Δ * gdeg M D := by
  intro hC hA hS k _ X _ p D hX x Δ hx hΔ N J _ e n M μ he hn ht hM hμ
  have key := levels_le_selfInter hC hA hS k X p D hX x Δ hx hΔ N J e n M μ he hn ht hM hμ
  have hw0 : ∀ c : J × Finset (Fin D), 0 ≤ (n c.1 : ℝ) * Δ := fun c => by positivity
  have hrk := GlobalTheory.T.rank_le_fubiniStudy_boxFamily hC hA k X p D hX M J e x (fun c => (n c.1 : ℝ) * Δ) he hx hw0 hM
  have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hcard : ((D + 1).factorial : ℝ) * Δ * Fintype.card J ≤ ((D : ℝ) + 1) * Δ * gdeg M D := by
    calc ((D + 1).factorial : ℝ) * Δ * Fintype.card J = ((D : ℝ) + 1) * Δ * (D.factorial * Fintype.card J) := by
          rw [hf]; ring
      _ ≤ ((D : ℝ) + 1) * Δ * gdeg M D := mul_le_mul_of_nonneg_left hrk (by positivity)
  have hsum : ((∑ j, (n j + 1) : ℕ) : ℝ) = ∑ j, (n j : ℝ) + Fintype.card J := by
    push_cast
    rw [Finset.sum_add_distrib]
    simp
  rw [hsum, mul_add]
  linarith

end GlobalTheory.HSNef
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_labelledSemiAbelianCover_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → (letI := A'.isAb.comm; GlobalTheory.ZH.HypS A'.A A'.L) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))) (lab : Labels D₁.toPre A), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) ∧ OneTrait D₁.toPre A lab ∧ GalEqN n lab := by
  first | exact @GlobalTheory.Mum.exists_desc_labels | exact GlobalTheory.Mum.exists_desc_labels | (intros; apply GlobalTheory.Mum.exists_desc_labels <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.SecEmb.geometricallyIrreducible_of_smooth {X S : Scheme.{0}} (f : X ⟶ S) (hs : Smooth f)
    (hc : GeometricallyConnected f) : GeometricallyIrreducible f := by
  constructor
  intro K _ g Z fst snd h
  have : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h hs
  have hcs := hc.geometrically_connectedSpace g fst snd h
  exact GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace K Z snd this hcs

theorem GlobalTheory.Mum.SecEmb.emb_of_traitRed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (G : Over M.S) [GrpObj G],
    IsSemiAbelian G → ∀ (B L : LB G.left), B.IsLB → L.IsLB → ∀ (N : ℕ) (s : Fin (N + 1) → B.Sec) (θ : L.Sec)
    (Y : Over (Sp (ResidueField R))) [GrpObj Y], Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N),
    j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → IsImmersion j → ∀ (O : Y.left.Opens), (O : Set Y.left).Nonempty →
    GlobalTheory.Mum.SecEmb.TraitRed M G s θ Y j O → ∃ E : Emb M.π G, E.Theta L := by
  intro R _ _ _ hR M G _ hG B L hB hL N s θ Y _ hY j hj hi O hO hT
  have hH := GlobalTheory.Mum.SecEmb.mem_embH_of_closed R hR M G hG B L hB hL N s θ Y hY j hj hi O hT
  exact ⟨{ N := N
           H := GlobalTheory.Mum.SecEmb.embH s
           H_all := hH
           f := GlobalTheory.Mum.SecEmb.embF (G.hom ≫ M.π) s
           f_over := GlobalTheory.ProjSpace.toProj_str _ _ _
           Y := Y
           smooth := hY
           j := j
           j_over := hj
           imm := hi
           fib := fun Ω _ x κ hx => GlobalTheory.Mum.SecEmb.Fib.fib R hR M G hG B L hB hL N s θ Y hY j hj hi O hT hH Ω x κ hx },
    θ, O, hO, fun g y hy hc hf => GlobalTheory.Mum.SecEmb.ThetaPt.mem_basicOpen_theta R hR M G hG B L hB hL N s θ Y hY j hj hi O hT g y hy hc hf⟩

namespace GlobalTheory.Mum.SecEmb

theorem agree_pull {X P Q : Scheme.{0}} (L : LB X) {hP : P ⟶ X} {hQ : Q ⟶ X} (g : Q ⟶ P) (e : g ≫ hP = hQ) {k : ℕ}
    (σ : SecK L hP k) : ∃ σ' : SecK L hQ k, ∀ {Y : Scheme.{0}} {h : Y ⟶ X} (s : SecK L h k), Agree L σ s → Agree L σ' s := by
  subst e
  refine ⟨ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec σ g, fun s hs Z p p' hp z J hJ => ?_⟩
  rw [ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec σ g p z hJ]
  exact hs Z (p ≫ g) p' (by rw [Category.assoc]; exact hp) z J hJ

theorem traitReg_of_secs {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G : Over M.S) [GrpObj G]
    (L : LB G.left) {A : Scheme.{0}} (α : A ⟶ G.left) (Sc : Secs M G L α) :
    (∀ i, TraitReg M G L (Sc.s i)) ∧ TraitReg M G L Sc.θ := by
  constructor
  · intro i W _ _ _ hW φ ξ hinj hloc hξ
    obtain ⟨W', i1, i2, i3, io, G', iG', β, σ, θ', κ, e, hW', hio, hfin, hpb, -, -, hσ, -, -⟩ :=
      Sc.trait W hW φ ξ hinj hloc hξ
    obtain ⟨σ'', h''⟩ := agree_pull L hpb.1.isoPullback.inv hpb.1.isoPullback_inv_fst (σ i)
    exact ⟨W', i1, i2, i3, io, σ'', hW', hio, hfin, h'' _ (hσ i)⟩
  · intro W _ _ _ hW φ ξ hinj hloc hξ
    obtain ⟨W', i1, i2, i3, io, G', iG', β, σ, θ', κ, e, hW', hio, hfin, hpb, -, -, -, hθ, -⟩ :=
      Sc.trait W hW φ ξ hinj hloc hξ
    obtain ⟨σ'', h''⟩ := agree_pull L hpb.1.isoPullback.inv hpb.1.isoPullback_inv_fst θ'
    exact ⟨W', i1, i2, i3, io, σ'', hW', hio, hfin, h'' _ hθ⟩

theorem core : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C C' : LabCover D) (Sc : Secs C.toModif C.G C.P.L.L C.α) (h : C'.S ⟶ C.S) (β : C'.G.left ⟶ C.G.left),
    h ≫ C.π = C'.π → IsGrpPullback C'.G C.G h β → LBIso C'.P.L.L (C.P.L.L.pull β) →
    (∀ i, ∃ σ : SecK C.P.L.L β Sc.k, Agree C.P.L.L σ (Sc.s i)) → (∃ θ : SecK C.P.L.L β 1, Agree C.P.L.L θ Sc.θ) →
    ∃ E : Emb C'.π C'.G, E.Theta C'.P.L.L := by
  intro R _ _ _ hR D C C' Sc h β hπ hpb hL hs hθ
  choose σ hσ using hs
  obtain ⟨θ₀, hθ₀⟩ := hθ
  obtain ⟨θ, hT⟩ := GlobalTheory.Mum.SecEmb.traitRed_cover R hR D C C' Sc h β hπ hpb hL σ hσ θ₀ hθ₀
  exact GlobalTheory.Mum.SecEmb.emb_of_traitRed R hR C'.toModif C'.G C'.semi _ C'.P.L.L (LB.isLB_linComb C.P.L.isLB _ _) C'.P.L.isLB Sc.N σ θ Sc.Y Sc.smooth
    Sc.j Sc.j_over Sc.imm Sc.O Sc.O_ne hT

theorem emb_of_secs : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D), Nonempty (Secs C.toModif C.G C.P.L.L C.α) → ∃ (C' : LabCover D) (E : Emb C'.π C'.G), E.Theta C'.P.L.L := by
  intro R _ _ _ hR D C ⟨Sc⟩
  have hR' := hR
  obtain ⟨⟨hN, -, -, -⟩, hc⟩ := hR'
  have hsemi := C.semi
  obtain ⟨hs, hθ⟩ := traitReg_of_secs C.toModif C.G C.P.L.L C.α Sc
  obtain ⟨M', h, -, hgp, hπ, hσ⟩ := GlobalTheory.Mum.extend_finiteModif R C.toModif C.G hsemi.smooth hsemi.quasiCompact
    (GlobalTheory.Mum.SecEmb.geometricallyIrreducible_of_smooth _ hsemi.smooth hsemi.geomConnected) C.P.L.L C.P.L.isLB C.A.A.left C.α C.A.A.hom C.α_cart.1
    (Option (Fin (Sc.N + 1))) (fun o => o.elim 1 (fun _ => Sc.k))
    (Option.rec (motive := fun o => SecK C.P.L.L C.α (o.elim 1 (fun _ => Sc.k))) Sc.θ Sc.s)
    (by rintro (_ | i); exacts [hθ, hs i])
  obtain ⟨C', eS, β, hπ', hpb, hL⟩ := GlobalTheory.Mum.LabCover.exists_pull R D C M' h hgp hπ
  have hw : β ≫ C.G.hom = (C'.G.hom ≫ eS.hom) ≫ h := by rw [Category.assoc]; exact hpb.1.w
  refine ⟨C', core R hR D C C' Sc (eS.hom ≫ h) β (by rw [Category.assoc, hπ, hπ']) hpb hL ?_ ?_⟩
  · intro i
    obtain ⟨σ, hσi⟩ := hσ (some i)
    obtain ⟨σ', h'⟩ := agree_pull C.P.L.L (pullback.lift β (C'.G.hom ≫ eS.hom) hw) (pullback.lift_fst _ _ _) σ
    exact ⟨σ', h' _ hσi⟩
  · obtain ⟨σ, hσi⟩ := hσ none
    obtain ⟨σ', h'⟩ := agree_pull C.P.L.L (pullback.lift β (C'.G.hom ≫ eS.hom) hw) (pullback.lift_fst _ _ _) σ
    exact ⟨σ', h' _ hσi⟩

end GlobalTheory.Mum.SecEmb
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.tensorDegData_unitary_type : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) , ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → Nontrivial D.toPre.X → 1 ≤ r → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) → ∃ Dm : Datum H, PelOK Dm D'.toPre o := by
  first | exact @GlobalTheory.Mum.tens_pelOK | exact GlobalTheory.Mum.tens_pelOK | (intros; apply GlobalTheory.Mum.tens_pelOK <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.theta_series_sharp_reference_sixteen_terms : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∃ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f ∧ LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) ∧ (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) := by
  first | exact @GlobalTheory.Poinc.Sep.sharp_fibre_iso_exists | exact GlobalTheory.Poinc.Sep.sharp_fibre_iso_exists | (intros; apply GlobalTheory.Poinc.Sep.sharp_fibre_iso_exists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_map_thetaExpansion_all_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ), ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F := by
  first | exact @GlobalTheory.Mum.exists_map_exp_all_traits | exact GlobalTheory.Mum.exists_map_exp_all_traits | (intros; apply GlobalTheory.Mum.exists_map_exp_all_traits <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChartGeo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)}

theorem nontrivial_of_not_mem_range {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.Mum.Base V)
    (C : MonoFam Xo c φ V) {S T : Scheme.{0}} (s : S ⟶ T) [IsSeparated s] (j : Xo.XF c ⟶ S) (ξV : Sp V ⟶ S)
    (hs : ∀ f g : Sp V ⟶ S, jK V ≫ f = jK V ≫ g → f ≫ s = g ≫ s)
    (hy : C.y ≫ j = jK V ≫ ξV) (hx : ξV (closedPoint V) ∉ Set.range j) : Nontrivial C.P.D.toPre.X := by
  by_contra hX
  rw [not_nontrivial_iff_subsingleton] at hX
  haveI : IsEmpty (Fin C.m) := ⟨fun i =>
    C.cone.linearIndependent.ne_zero i (LinearMap.ext₂ fun a b => by
      rw [Subsingleton.elim a 0]; simp)⟩
  have hprod : ∏ i, C.s i = 1 := by simp [Finset.univ_eq_empty]
  obtain ⟨yo, -, -, -, hg⟩ := GlobalTheory.T.openPart_classified_monomialBoundaryFamily Xo c φ V hV C
  let A := Localization.Away (∏ i, C.s i)
  let e : V ≃ₐ[V] A := IsLocalization.atUnit V A (∏ i, C.s i) (by rw [hprod]; exact isUnit_one)
  let h : A →+* V := e.symm.toRingEquiv.toRingHom
  have hcomp : h.comp (algebraMap V A) = RingHom.id V := by
    ext r
    show e.symm (algebraMap V A r) = r
    exact e.symm.commutes r
  have hid : spMap h ≫ spMap (algebraMap V A) = 𝟙 _ := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
    exact Spec.map_id _
  have hψ : jK V ≫ spMap h ≫ yo = C.y := by
    rw [← Category.assoc]
    exact hg _ (by rw [Category.assoc, hid, Category.comp_id])
  have hgen : jK V ≫ (spMap h ≫ yo) ≫ j = jK V ≫ ξV := by
    rw [← Category.assoc, hψ, hy]
  haveI : IsDominant (jK V) := (GlobalTheory.Mum.Modif.self V).dominant
  have heq : (spMap h ≫ yo) ≫ j = ξV :=
    ext_of_isDominant_of_isSeparated s (hs _ _ hgen) (jK V) hgen
  exact hx ⟨(spMap h ≫ yo) (closedPoint V), by
    show ((spMap h ≫ yo) ≫ j) (closedPoint V) = _
    rw [heq]⟩

end GlobalTheory.UChartGeo

namespace GlobalTheory.UChartGeo



theorem exists_monoFam_algClosed : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), GlobalTheory.Mum.Base V ∧ IsAlgClosed (ResidueField V) ∧ Nontrivial C.P.D.toPre.X ∧ C.y ≫ j = jK V ≫ ξV ∧ ξV (closedPoint V) = x := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hS x hx
  obtain ⟨V, _, _, _, C, ξV, hV, hy, hxV⟩ :=
    GlobalTheory.UChartTrait.exists_monoFam_through Xo c φ hpq hpf hns zs i OZ N d J π j BD hU hS x hx
  obtain ⟨Nn, ιP, hci, hι⟩ := hU.2.2.2.2.1.2.1
  haveI : IsSeparated (π ≫ zs) := by rw [← hι]; infer_instance
  haveI : IsDominant (jK V) := (GlobalTheory.Mum.Modif.self V).dominant
  have hs : ∀ f g : Sp V ⟶ S, jK V ≫ f = jK V ≫ g → f ≫ π ≫ zs = g ≫ π ≫ zs := fun f g hfg =>
    ext_of_isDominant_of_isSeparated (terminal.from (Sp c.F)) (terminal.hom_ext _ _) (jK V) (by
      rw [← Category.assoc, hfg, Category.assoc])
  have hX : Nontrivial C.P.D.toPre.X :=
    nontrivial_of_not_mem_range hV C (π ≫ zs) j ξV hs hy (hxV ▸ hx)
  obtain ⟨y0, hy0⟩ := exists_ne (0 : C.P.D.toPre.X)
  obtain ⟨i0, -⟩ := C.mono.exists_pos (maximalIdeal.isMaximal _).ne_top hy0
  have hnf : ¬ IsField V := by
    intro hf
    have hm := C.s_mem i0
    rw [(IsLocalRing.isField_iff_maximalIdeal_eq).1 hf, Ideal.mem_bot] at hm
    exact C.s_ne_zero i0 hm
  haveI : IsNoetherianRing V := hV.1.1
  haveI : CharZero V := hV.2
  obtain ⟨W, _, _, _, ρ, hcomp, hac, hinj, hloc⟩ := GlobalTheory.T.exists_complete_dvr_algClosed_residue_injective_local V hnf ⟨C.b.comp (algebraMap ℚ c.F)⟩
  haveI : CharZero W := charZero_of_injective_ringHom hinj
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hne : ∀ k, ρ (C.s k) ≠ 0 := fun k h0 => C.s_ne_zero k (hinj (h0.trans (map_zero ρ).symm))
  choose w u hwu using fun k => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hne k) hϖ
  have hW : GlobalTheory.UU.CDVR W := ⟨inferInstance, hcomp, inferInstance⟩
  obtain ⟨t, P, e, be, -, htK, hbe, -, hmono, -⟩ := trait_pull C hV W hW ϖ ρ hinj hloc w u hwu
  have hinj' : Function.Injective ((algebraMap W (FractionRing W)).comp ρ) :=
    (IsFractionRing.injective W (FractionRing W)).comp hinj
  obtain ⟨gam, hgam⟩ : ∃ gam : FractionRing V →+* FractionRing W,
      gam.comp (algebraMap V (FractionRing V)) = (algebraMap W (FractionRing W)).comp ρ :=
    ⟨IsFractionRing.lift hinj', RingHom.ext fun r => by
      rw [RingHom.comp_apply, RingHom.comp_apply]; exact IsFractionRing.lift_algebraMap hinj' r⟩
  have hκ : spMap gam ≫ jK V = jK W ≫ spMap ρ := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hgam]
  obtain ⟨tK, h1, h2⟩ := htK (spMap gam) hκ
  have hover : (spMap gam ≫ C.y) ≫ pullback.snd _ _ = jK W ≫ spMap (ρ.comp C.b) := by
    rw [Category.assoc, C.y_over, ← Category.assoc, hκ, Category.assoc]
    congr 1
    exact (Spec.map_comp (CommRingCat.ofHom C.b) (CommRingCat.ofHom ρ)).symm
  let F : Fam Xo c W := ⟨ρ.comp C.b, t, P, spMap gam ≫ C.y, hover, ⟨tK, h1, h2⟩⟩
  let β : LinearMap.BilinForm ℤ P.D.toPre.X := ∑ k, (w k : ℤ) • pull e.toLinearMap (C.δ k)
  have hβ : β ∈ balForms H.bar P.D.toPre.X :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (pull_mem _ (C.cone.mem k))
  have hbeq : be = (l.M' : ℤ) • β := by
    rw [hbe, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ext a b
    simp only [LinearMap.smul_apply, pull_apply, smul_eq_mul]
    ring
  have hmono' : IsMonomial F.P.D.toPre ![ϖ] ![(l.M' : ℤ) • β] := hbeq ▸ hmono
  have hϖm : ϖ ∈ maximalIdeal W := (mem_maximalIdeal _).2 hϖ.not_isUnit
  obtain ⟨C', hC'⟩ := F.exists_monoFam hpf hϖm hβ hmono'
  have hyC : C'.toFam.y = spMap gam ≫ C.y := by rw [hC']
  refine ⟨W, inferInstance, inferInstance, inferInstance, C', spMap ρ ≫ ξV,
    ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩, hac, ?_, ?_, ?_⟩
  · rw [hC']
    exact e.symm.injective.nontrivial
  · show C'.toFam.y ≫ j = _
    rw [hyC, Category.assoc, hy, ← Category.assoc, hκ, Category.assoc]
  · show ξV (spMap ρ (closedPoint W)) = x
    have hcl : spMap ρ (closedPoint W) = closedPoint V := IsLocalRing.comap_closedPoint ρ
    rw [hcl, hxV]

end GlobalTheory.UChartGeo
end
end
