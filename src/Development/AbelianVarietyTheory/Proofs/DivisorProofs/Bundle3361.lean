module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3353
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle186
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataEighthPowerViaCharacterMaps
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3354
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3101
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem GlobalTheory.HSNef.lc_le_bound : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (x : Fin D → X.functionField) (β : ℝ) (q : ℕ), AlgebraicIndependent ℤ x → (∀ S : Finset (Fin D), ∏ i ∈ S, x i ∈ P.Bl 0 1 1) → (P.L.tens P.A).IsNef D → (P.L.tens P.A).IsSelfInter β → 3 ≤ q → P.lc 1 0 1 ≤ bound D q β (gdeg (P.L.tens P.A) D) := by
  intro hC hA hS k _ X _ p D hX P x β q hx hxB hNef hSI hq
  haveI := hX.charZero
  haveI hcz : CharZero X.functionField :=
    charZero_of_injective_ringHom (f := (X.germToFunctionField ⊤).hom) (X.germToFunctionField_injective ⊤)
  have hβ : 0 ≤ β := by
    obtain ⟨h, hh, rfl⟩ := hSI
    exact (GlobalTheory.T.arithKleiman_heightNef_of_isNef hC hA hS k X p D hX _ hNef).2 h hh _
  have hg : 0 ≤ gdeg (P.L.tens P.A) D := GlobalTheory.T.hermLineBundleGeometricDegree_nonneg_of_semiPos k X p D hX _ hNef.semiPos
  have hq' : (3:ℝ) ≤ q := by exact_mod_cast hq
  have hΔ : 0 < Real.log ((q:ℝ)/2) := Real.log_pos (by linarith)
  have hF : (0:ℝ) < ((D+1).factorial : ℝ) := by positivity
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hFD : 0 < ((D+1).factorial : ℝ) * Real.log ((q:ℝ)/2) := mul_pos hF hΔ
  set g := gdeg (P.L.tens P.A) D with hgdef
  set Δ := Real.log ((q:ℝ)/2) with hΔdef
  set α := (β + (D + 1) * (Δ + D * Real.log 2 / 2) * g) / ((D + 1).factorial * Δ) with hαdef
  set β' := (D + 1) * g / (2 * ((D + 1).factorial * Δ)) with hβ'def
  have hα : 0 ≤ α := div_nonneg (by positivity) hFD.le
  have hβ' : 0 ≤ β' := div_nonneg (by positivity) (by positivity)
  have hT : 0 ≤ α + β' * Real.log ((α + 2 * β' + 1) ^ 2) :=
    add_nonneg hα (mul_nonneg hβ' (Real.log_nonneg (by nlinarith)))
  have hexp : ∀ m : ℕ, (2 / q : ℝ) ^ m = Real.exp (-(m * Δ)) := by
    intro m
    have e1 : (2 / q : ℝ) = Real.exp (-Δ) := by
      rw [Real.exp_neg, hΔdef, Real.exp_log (by positivity), inv_div]
    rw [e1, ← Real.exp_nat_mul]
    congr 1
    ring
  have key : ∀ (r : ℕ) (e : Fin r → X.functionField) (n : Fin r → ℕ), LinearIndependent ℤ e →
      (∀ j, e j ∈ P.Bl 1 0 ((2 / q : ℝ) ^ n j)) →
      ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ α + β' * Real.log ((α + 2 * β' + 1) ^ 2) := by
    intro r e n he hB
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simpa using hT
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    have hsmall : SmallFam (P.L.tens P.A) (boxFam e x) (fun c => n c.1 * Δ) := by
      apply GlobalTheory.T.smallSections_pairSum_ratFnFamily_tensor k X p P
      rintro ⟨j, S⟩
      have h1 := hB j
      have h2 := hxB S
      obtain ⟨hm, hnu⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P 1 0 0 1 _ _ h1.1 h2.1
      have e10 : ((1:ℤ) + 0) = 1 := by norm_num
      have e01 : ((0:ℤ) + 1) = 1 := by norm_num
      rw [e10, e01] at hm hnu
      refine ⟨hm, fun σ y => ?_⟩
      show P.nu 1 1 σ y (e j * ∏ i ∈ S, x i) ≤ _
      rw [hnu, ← hexp]
      have h0 : 0 ≤ P.nu 1 0 σ y (e j) := by unfold Pair.nu; positivity
      exact (mul_le_of_le_one_right h0 (h2.2 σ y)).trans (h1.2 σ y)
    have hcore := GlobalTheory.T.nef_hermitian_small_sections_key_inequality hC hA hS k X p D hX _ β hNef hSI x Δ hx hΔ (Fin r) e n he hsmall
    rw [Fintype.card_fin] at hcore
    have hrs : (r:ℝ) ≤ ((∑ j, (n j + 1) : ℕ) : ℝ) := by
      have : r ≤ ∑ j : Fin r, (n j + 1) := by
        calc r = ∑ _j : Fin r, 1 := by simp
          _ ≤ _ := Finset.sum_le_sum (fun j _ => by omega)
      exact_mod_cast this
    have hs : ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ α + β' * Real.log r := by
      have e2 : α + β' * Real.log r =
          (β + ((D:ℝ) + 1) * (Δ + D * Real.log 2 / 2 + Real.log r / 2) * g) / ((D + 1).factorial * Δ) := by
        rw [hαdef, hβ'def]
        field_simp
        ring
      rw [e2, le_div_iff₀ hFD]
      linarith
    exact GlobalTheory.le_add_mul_log_sq_of_le_add_mul_log α β' r _ hα hβ' (by exact_mod_cast hr) hrs hs
  have hfin := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX P 1 0 1
  exact GlobalTheory.T.log_ncard_unitBall_le_of_independent_level_bound X.functionField (P.H 1 0) (P.Bl 1 0) (GlobalTheory.VolBr.Pair.isBallFam k X p P 1 0) hfin q _ hq hT key
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.Step

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

def extend (m : ℕ) (T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ) (V : (Fin (m + 1) → HermLB p) → X → ℝ) :
    ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ :=
  fun d L x => if h : d = m + 1 then V (fun a => L (Fin.cast h.symm a)) x else T d L x

theorem extend_of_ne {m : ℕ} {T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ} {V : (Fin (m + 1) → HermLB p) → X → ℝ}
    {d : ℕ} (h : d ≠ m + 1) (L : Fin d → HermLB p) (x : X) : extend m T V d L x = T d L x := dif_neg h

theorem extend_self {m : ℕ} {T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ} {V : (Fin (m + 1) → HermLB p) → X → ℝ}
    (L : Fin (m + 1) → HermLB p) (x : X) : extend m T V (m + 1) L x = V L x := by
  simp [extend]

theorem recVal_congr {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} {e : ℕ} {h h' : Y → ℝ}
    (H : ∀ z, Order.coheight z = 1 → h z = h' z) (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) : recVal h L M hr = recVal h' L M hr := by
  unfold recVal
  congr 1
  refine finsum_congr fun z => ?_
  by_cases hz : (M.div hr).mult z = 0
  · simp [hz]
  · rw [H z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)]

theorem isRatSec_tens_mul {Z : Scheme.{0}} [IsIntegral Z] {A B : LB Z} {r : A.ι → Z.functionFieldˣ}
    {s : B.ι → Z.functionFieldˣ} (hr : IsRatSec A r) (hs : IsRatSec B s) :
    IsRatSec (CechPic.tens A B) fun c : A.ι × B.ι => r c.1 * s c.2 := fun (c c' : A.ι × B.ι) h => by
  have h₁ : genericPoint Z ∈ A.U c.1 ⊓ A.U c'.1 := ⟨h.1.1, h.2.1⟩
  have h₂ : genericPoint Z ∈ B.U c.2 ⊓ B.U c'.2 := ⟨h.1.2, h.2.2⟩
  have e : fnOf _ h ((CechPic.tens A B).g c c' : Γ(Z, _)) =
      fnOf _ h₁ (A.g c.1 c'.1 : Γ(Z, _)) * fnOf _ h₂ (B.g c.2 c'.2 : Γ(Z, _)) := by
    change fnOf _ h ((res _ (A.g c.1 c'.1)).val * (res _ (B.g c.2 c'.2)).val) = _
    exact (map_mul (fnOf _ h) _ _).trans (congrArg₂ (· * ·) (fnOf_resG _ h _) (fnOf_resG _ h _))
  rw [Units.val_mul, Units.val_mul, hr c.1 c'.1 h₁, hs c.2 c'.2 h₂, e]
  ring

theorem isMix_succ : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∃ T, IsMix p (m + 1) T := by
  intro hI hR m hm k _ X p hp
  classical
  haveI : IsNoetherian X := hp.isNoetherian
  obtain ⟨T, hT⟩ := hm k X p hp
  choose v hv using GlobalTheory.T.mixedHeightRecursiveValue_well_defined hI hR m hm k X p hp T hT
  have hD := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hp
  have hdimi : ∀ (Y : Scheme.{0}) [IsIntegral Y] (i : Y ⟶ X) [IsClosedImmersion i] (d : ℕ),
      topologicalKrullDim Y = (d : ℕ) → HasDim (i (genericPoint Y)) d := fun Y _ i _ d h =>
    (hD.2.2.2.2.1 Y i (genericPoint Y) d).2 ((hD.2.2.2.2.2 Y d).2 h)
  have hcd : ∀ x : X, HasDim x (m + 1) → topologicalKrullDim (clo x) = ((m + 1 : ℕ) : WithBot ℕ∞) := fun x hx =>
    (hD.2.2.2.2.2 (clo x) (m + 1)).1
      ((hD.2.2.2.2.1 (clo x) (cloι x) (genericPoint (clo x)) (m + 1)).1 (by rw [cloι_genericPoint]; exact hx))
  have E : ∀ (x : X) (hx : HasDim x (m + 1)) (M : HermLB p) (L : Fin m → HermLB p)
      (M' : HermLB (cloι x ≫ p)) (L' : Fin m → HermLB (cloι x ≫ p)),
      (M.pull (cloι x) rfl).Isometric M' → (∀ a, ((L a).pull (cloι x) rfl).Isometric (L' a)) →
      ∀ (r : M'.B.ι → (clo x).functionFieldˣ) (hr : IsRatSec M'.B r)
        (TY : ∀ d : ℕ, (Fin d → HermLB (cloι x ≫ p)) → clo x → ℝ), IsMix (cloι x ≫ p) m TY →
      v x hx M L = recVal (TY m L') L' M' hr := by
    intro x hx M L M' L' hM hL r hr TY hTY
    rw [hv x hx M L (clo x) (cloι x ≫ p) (cloι x) rfl (cloι_genericPoint x) M' L' hM hL r hr]
    refine recVal_congr (fun z hz => ?_) L' M' hr
    have hz' : HasDim z m := ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k (clo x) (cloι x ≫ p) (hp.sub _) m (hcd x hx)).1 z).1 hz
    exact GlobalTheory.T.mixedHeight_unique_restrict_closedSubscheme k X (clo x) p (cloι x ≫ p) hp (cloι x) rfl m m T TY hT hTY m le_rfl le_rfl L L' hL z hz'
  let V : (Fin (m + 1) → HermLB p) → X → ℝ := fun L x =>
    if hx : HasDim x (m + 1) then v x hx (L 0) (Fin.tail L) else 0
  have hV : ∀ (L : Fin (m + 1) → HermLB p) (x : X) (hx : HasDim x (m + 1)),
      extend m T V (m + 1) L x = v x hx (L 0) (Fin.tail L) := fun L x hx => by
    rw [extend_self]
    exact dif_pos hx
  have hsym : ∀ (x : X) (hx : HasDim x (m + 1)) (L : Fin (m + 1) → HermLB p) (e : Equiv.Perm (Fin (m + 1))),
      v x hx (L (e 0)) (Fin.tail fun a => L (e a)) = v x hx (L 0) (Fin.tail L) := by
    intro x hx L e
    obtain ⟨TY, hTY⟩ := hm k (clo x) (cloι x ≫ p) (hp.sub (cloι x))
    have hq : IsAmb (cloι x ≫ p) := hp.sub (cloι x)
    have hdx := hcd x hx
    let F : (Fin (m + 1) → HermLB p) → ℝ := fun L => v x hx (L 0) (Fin.tail L)
    change F (fun a => L (e a)) = F L
    rcases m with _ | n
    · have : (fun a => L (e a)) = L := funext fun a => congrArg L (@Subsingleton.elim (Fin 1) _ _ _)
      rw [this]
    · refine GlobalTheory.T.perm_invariant_of_cons_swap_and_tail (HermLB p) n F (fun a L τ => ?_) (fun a b L => ?_) L e
      · simp only [F, Fin.cons_zero, Fin.tail_cons]
        obtain ⟨ra, hra⟩ := Cartier.exists_isRatSec (a.pull (cloι x) rfl).isLB
        rw [E x hx a (fun i => L (τ i)) (a.pull (cloι x) rfl) (fun i => (L (τ i)).pull (cloι x) rfl)
            (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) ra hra TY hTY,
          E x hx a L (a.pull (cloι x) rfl) (fun i => (L i).pull (cloι x) rfl)
            (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) ra hra TY hTY]
        exact (GlobalTheory.T.mixedHeight_inductive_rhs_symm_isometry_invariant hI k (clo x) (cloι x ≫ p) hq (n + 1) hdx TY hTY _ ra hra).2.1
          (fun i => (L i).pull (cloι x) rfl) τ
      · simp only [F, Fin.cons_zero, Fin.tail_cons]
        obtain ⟨ra, hra⟩ := Cartier.exists_isRatSec (a.pull (cloι x) rfl).isLB
        obtain ⟨rb, hrb⟩ := Cartier.exists_isRatSec (b.pull (cloι x) rfl).isLB
        have iso : ∀ (c : HermLB p) (j : Fin (n + 1)), ((Fin.cons c L : Fin (n + 1) → HermLB p) j).pull (cloι x) rfl |>.Isometric
            ((Fin.cons (c.pull (cloι x) rfl) (fun i => (L i).pull (cloι x) rfl) : Fin (n + 1) → HermLB (cloι x ≫ p)) j) := by
          intro c j
          refine Fin.cases ?_ (fun i => ?_) j <;> simp only [Fin.cons_zero, Fin.cons_succ] <;> exact HermLB.Isometric.refl _
        rw [E x hx a _ (a.pull (cloι x) rfl) _ (HermLB.Isometric.refl _) (iso b) ra hra TY hTY,
          E x hx b _ (b.pull (cloι x) rfl) _ (HermLB.Isometric.refl _) (iso a) rb hrb TY hTY]
        exact GlobalTheory.T.mixedHeightInduction_symmetric_firstTwo hI hR k (clo x) (cloι x ≫ p) hq n hdx TY hTY _ _ _ ra hra rb hrb
  refine ⟨extend m T V, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro d L M x hd hx hLM
    by_cases h : d = m + 1
    · subst h
      rw [hV _ _ hx, hV _ _ hx]
      obtain ⟨TY, hTY⟩ := hm k (clo x) (cloι x ≫ p) (hp.sub (cloι x))
      obtain ⟨r, hr⟩ := Cartier.exists_isRatSec ((L 0).pull (cloι x) rfl).isLB
      rw [E x hx (L 0) (Fin.tail L) ((L 0).pull (cloι x) rfl) (fun a => (Fin.tail L a).pull (cloι x) rfl)
          (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) r hr TY hTY,
        E x hx (M 0) (Fin.tail M) ((L 0).pull (cloι x) rfl) (fun a => (Fin.tail L a).pull (cloι x) rfl)
          ((hLM 0).symm.pull _ _) (fun a => (hLM a.succ).symm.pull _ _) r hr TY hTY]
    · rw [extend_of_ne h, extend_of_ne h]
      exact hT.iso d L M x (by omega) hx hLM
  · intro d L e x hd hx
    by_cases h : d = m + 1
    · subst h
      rw [hV _ _ hx, hV _ _ hx]
      exact hsym x hx L e
    · rw [extend_of_ne h, extend_of_ne h]
      exact hT.symm d L e x (by omega) hx
  · intro d A B L x hd hx
    by_cases h : d + 1 = m + 1
    · obtain rfl : d = m := by omega
      rw [hV _ _ hx, hV _ _ hx, hV _ _ hx]
      simp only [Fin.cons_zero, Fin.tail_cons]
      obtain ⟨TY, hTY⟩ := hm k (clo x) (cloι x ≫ p) (hp.sub (cloι x))
      obtain ⟨ra, hra⟩ := Cartier.exists_isRatSec (A.pull (cloι x) rfl).isLB
      obtain ⟨rb, hrb⟩ := Cartier.exists_isRatSec (B.pull (cloι x) rfl).isLB
      have ht := isRatSec_tens_mul hra hrb
      rw [E x hx (A.tens B) L ((A.pull (cloι x) rfl).tens (B.pull (cloι x) rfl)) (fun a => (L a).pull (cloι x) rfl)
          (HermLB.isometric_pull_tens A B _ _) (fun _ => HermLB.Isometric.refl _) _ ht TY hTY,
        E x hx A L (A.pull (cloι x) rfl) (fun a => (L a).pull (cloι x) rfl)
          (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) ra hra TY hTY,
        E x hx B L (B.pull (cloι x) rfl) (fun a => (L a).pull (cloι x) rfl)
          (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) rb hrb TY hTY]
      exact GlobalTheory.T.inductiveArakelovFormula_rhs_tensor_additive hI k (clo x) (cloι x ≫ p) (hp.sub _) d (hcd x hx) _ _ _ _ ra hra rb hrb _ ht
        fun _ _ _ _ => rfl
    · rw [extend_of_ne h, extend_of_ne h, extend_of_ne h]
      exact hT.add d A B L x (by omega) hx
  · intro L x hx
    rw [extend_of_ne (by omega)]
    exact hT.zero L x hx
  · intro Y _ _ q i _ hi e he hdim M L M' L' hM hL r hr
    have hfun : (fun z => extend m T V e L (i z)) = fun z => T e L (i z) :=
      funext fun z => extend_of_ne (by omega) L (i z)
    rw [hfun]
    by_cases h : e + 1 = m + 1
    · obtain rfl : e = m := by omega
      have hx := hdimi Y i (e + 1) hdim
      rw [hV _ _ hx]
      simp only [Fin.cons_zero, Fin.tail_cons]
      exact hv _ hx M L Y q i hi rfl M' L' hM hL r hr
    · rw [extend_of_ne h]
      exact hT.recur Y q i hi e (by omega) hdim M L M' L' hM hL r hr

end GlobalTheory.MixHt.Step
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart

theorem exists_complete_dvr_of_local (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (ψ : A →+* W), Function.Injective ψ ∧ IsLocalHom ψ := by
  by_cases h : IsField A
  · letI := h.toField
    refine ⟨PowerSeries A, inferInstance, inferInstance, inferInstance, ?_, PowerSeries.C,
      RingHom.injective _, inferInstance⟩
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  · obtain ⟨O, _, _, _, _, φ, h1, h2⟩ := GlobalTheory.exists_complete_discreteValuationRing_dominating A h
    exact ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, φ, h1, h2⟩

theorem exists_trait_at : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n))
    [LocallyOfFiniteType s] [IsLocallyNoetherian S] (j : F.X ⟶ S) [IsOpenImmersion j], 3 ≤ n → Dense (Set.range j) →
    j ≫ s = F.s → ∀ x : S, ∃ (T : GlobalTheory.Poinc.Trait F) (ξT : Sp T.V ⟶ S) (b : cycAway n →+* T.V),
      ξT (closedPoint T.V) = x ∧ jK T.V ≫ ξT = T.y ≫ j ∧ ξT ≫ s = spMap b := by
  intro g n F S s _ _ j _ _ hd hjs x
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI : Flat F.s := inferInstance
  obtain ⟨_, ⟨y0, rfl⟩, hw⟩ :=
    GlobalTheory.BlowOpen.exists_specializes_of_dense_scheme S _ j.isOpenEmbedding.isOpen_range hd x
  obtain ⟨y1, hy1, e1⟩ := Flat.generalizingMap F.s (genericPoint_specializes (F.s y0))
  have hη : j y1 ⤳ x := (hy1.map j.continuous).trans hw
  obtain ⟨q, hq⟩ : j y1 ∈ Set.range (S.fromSpecStalk x) := by rw [Scheme.range_fromSpecStalk]; exact hη
  haveI : q.asIdeal.IsPrime := q.isPrime
  haveI : IsLocalRing (S.presheaf.stalk x ⧸ q.asIdeal) := .of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨W, _, _, _, hWc, ψ, hψi, hψl⟩ := exists_complete_dvr_of_local (S.presheaf.stalk x ⧸ q.asIdeal)
  haveI : IsLocalHom (Ideal.Quotient.mk q.asIdeal) := .of_surjective _ Ideal.Quotient.mk_surjective
  let ψ' : S.presheaf.stalk x →+* W := ψ.comp (Ideal.Quotient.mk q.asIdeal)
  haveI : IsLocalHom ψ' := RingHom.isLocalHom_comp _ _
  let ξ0 : Sp W ⟶ S := spMap ψ' ≫ S.fromSpecStalk x
  have hξc : ξ0 (closedPoint W) = x := by
    show S.fromSpecStalk x (spMap ψ' (closedPoint W)) = x
    have e : spMap ψ' (closedPoint W) = closedPoint (S.presheaf.stalk x) := IsLocalRing.comap_closedPoint ψ'
    rw [e]
    exact Scheme.fromSpecStalk_closedPoint
  have hξg : ξ0 (⊥ : PrimeSpectrum W) = j y1 := by
    show S.fromSpecStalk x (spMap ψ' (⊥ : PrimeSpectrum W)) = j y1
    have : spMap ψ' (⊥ : PrimeSpectrum W) = q := by
      apply PrimeSpectrum.ext
      show Ideal.comap ψ' ⊥ = q.asIdeal
      rw [← RingHom.ker_eq_comap_bot, RingHom.ker_comp_of_injective _ hψi, Ideal.mk_ker]
    rw [this, hq]
  have hjKbot : ∀ pt : Sp (FractionRing W), jK W pt = (⊥ : PrimeSpectrum W) := fun pt => by
    apply PrimeSpectrum.ext
    have hpt : pt = (⊥ : PrimeSpectrum (FractionRing W)) := Subsingleton.elim (α := PrimeSpectrum (FractionRing W)) _ _
    subst hpt
    show Ideal.comap (algebraMap W (FractionRing W)) ⊥ = ⊥
    exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective W (FractionRing W))
  have hrange : Set.range (jK W ≫ ξ0) ⊆ Set.range j := by
    rintro _ ⟨pt, rfl⟩
    rw [Scheme.Hom.comp_apply, hjKbot, hξg]
    exact ⟨y1, rfl⟩
  let y : Sp (FractionRing W) ⟶ F.X := IsOpenImmersion.lift j (jK W ≫ ξ0) hrange
  have hy : y ≫ j = jK W ≫ ξ0 := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨θ, hθ⟩ := Spec.map_surjective (ξ0 ≫ s)
  let b0 : cycAway n →+* W := θ.hom
  have hb0 : spMap b0 = ξ0 ≫ s := hθ
  have hb0i : Function.Injective b0 := by
    have h1 : (spMap b0) (⊥ : PrimeSpectrum W) = genericPoint (Sp (cycAway n)) := by
      rw [hb0]
      exact (Scheme.Hom.comp_apply ξ0 s _).trans (by rw [hξg, ← Scheme.Hom.comp_apply, hjs, e1])
    rw [genericPoint_eq_bot_of_affine] at h1
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot]
    exact congrArg PrimeSpectrum.asIdeal h1
  haveI : CharZero W := charZero_of_injective_ringHom hb0i
  have hBase : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hWc⟩, inferInstance⟩
  obtain ⟨T, f, fK, -, hfl, -, hcomp, hTy⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n (cycAway n) (zetaAway n) F W hBase inferInstance y
  haveI := hfl
  refine ⟨T, spMap f ≫ ξ0, f.comp b0, ?_, ?_, ?_⟩
  · show ξ0 (spMap f (closedPoint T.V)) = x
    have e : spMap f (closedPoint T.V) = closedPoint W := IsLocalRing.comap_closedPoint f
    rw [e, hξc]
  · have key : jK T.V ≫ spMap f = spMap fK ≫ jK W := by
      simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a
      exact (hcomp a).symm
    rw [hTy, Category.assoc, hy, ← Category.assoc, key, Category.assoc]
  · rw [Category.assoc, ← hb0]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end GlobalTheory.TChart
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

theorem _root_.GlobalTheory.T.degenerationData_eighthPower_via_characterMaps : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → (∀ a, (c.lev a).left ≫ φc = y ≫ (F.univ.lev a).left) → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∀ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) → ∀ e : (Fin 8 → Q.X) ≃+ D.toPre.X, (∀ mu, e mu = ∑ u, c u (e₀.symm (∑ v, (W + W.transpose) u v • mu v))) → SharpRef W Q ρ D.toPre e := by
  first | exact @GlobalTheory.Mum.PowData.sharpRef_of_characters | exact GlobalTheory.Mum.PowData.sharpRef_of_characters | (intros; apply GlobalTheory.Mum.PowData.sharpRef_of_characters <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

theorem GlobalTheory.Poinc.Sep.conj_fibre_core : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∀ (a : Q.X) (p : Sp K ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = spMap (ev.comp ρ) ≫ (Q.c a).left → p ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = 𝟙 _ → ∃ (f : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left) (f₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left), IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f ∧ IsSquare f f₂ ∧ (∀ (ψ₀ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 Q.B).left) (ψσ : (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left ⟶ (G2 Q.B).left), IsSquare (pullback.fst Q.B.hom (spMap (ev.comp ρ))) ψ₀ → IsSquare (pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) ψσ → LBIso ((abelian₂ Q.B Q.M.L).pull ψ₀) ((abelian₂ Q.B Q.M.L).pull (f₂ ≫ ψσ))) ∧ p ≫ f ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) = spMap σ.toRingHom ≫ p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) := by
  intro g l hl hlo W hW
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.e8Power_fibre_conjugate_evaluation_iso g l hl hlo W hW
  refine ⟨max j₀ 1, ?_⟩
  intro j hj V V₁ _ _ _ _ _ hCN hlu Q hQg ρ hρ D e hSh C u mo hmo hTh K _ _ ev k₀ hk₀ hu σ hσ a p hpf hps
  obtain ⟨f, hf, hL, ht, hc⟩ :=
    hj₀ j (le_of_max_le_left hj) V V₁ hCN hlu Q hQg ρ hρ D e hSh C u mo hmo hTh K ev k₀ hk₀ hu σ hσ
  exact GlobalTheory.T.eighthPower_fibre_iso_sharp_torsion_gives_factor_iso l hl hlo W hW j (le_of_max_le_right hj) V V₁ hlu Q ρ hρ D e hSh
    K ev σ f hf hL ht hc a p hpf hps
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_theta_unit_at_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ Φ : IntFam (maximalIdeal R) D.toPre (m ^ 2) → SecK C.P.L.L C.α (m ^ 2), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) → ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ θ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u θ F₁ := by
  intro R _ _ _ hR D C m hm Φ hΦ F₁
  obtain ⟨θ₀, hθ₀⟩ := GlobalTheory.T.exists_polarisationSection_ratio_integralThetaFamily R hR D C F₁
  obtain ⟨r, t, hr, ht, h⟩ := GlobalTheory.T.thetaExpansionScalars_ratio_odd_mul R hR D C m hm Φ hΦ F₁ θ₀ hθ₀
  have hr' : algebraMap R (FractionRing R) r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale (scal C.A.A.hom
    (algebraMap R (FractionRing R) t / algebraMap R (FractionRing R) r)) θ₀, fun W _ _ _ T => ?_⟩
  obtain ⟨a, b, v, ha, hb, hE, hv⟩ := h W T
  exact ⟨v, GlobalTheory.T.trait_expansionScalar_rescale_degreeOne R hR D C F₁ θ₀ r t _ hr (div_mul_cancel₀ _ hr') W T a b v ha hb hE hv⟩

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lowerObject_completeDVR_both_maps : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ θ₁ θ₂ : R →+* V, Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK V ≫ spMap θ₁ → κ₂ ≫ jK R = jK V ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → ∃ (o' : LowObj Cn.D' c ((θ₁.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b)) (m₁ : ObjMap o' Cn.L.o (spMap (θ₁.comp (Cn.ψ.comp MvPolynomial.C)))) (m₂ : ObjMap o' Cn.L.o (spMap (θ₂.comp (Cn.ψ.comp MvPolynomial.C)))) (x : Cn.L.D.X → (Sp V ⟶ o'.t.G.left)), (∀ y, x y ≫ m₁.toSABMap.φ ≫ Cn.L.φB = spMap (θ₁.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.D.c y).left) ∧ (∀ y, x y ≫ m₂.toSABMap.φ ≫ Cn.L.φB = spMap (θ₂.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.D.c y).left) ∧ ∀ y, x y ≫ o'.t.G.hom = 𝟙 _ := by
  first | exact @GlobalTheory.UCanon.LowPull.exists_lowObj_cdvr | exact GlobalTheory.UCanon.LowPull.exists_lowObj_cdvr | (intros; apply GlobalTheory.UCanon.LowPull.exists_lowObj_cdvr <;> assumption)
end
