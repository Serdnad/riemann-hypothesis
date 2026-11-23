module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle008
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem mem_range_section_of_not_unitAt : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ (τ : ι) (a b : Fin (m τ)) (z : W.Z), ∀ A₁ ∈ E'.S (W.p₁ z), ∀ A₂ ∈ E'.S (W.p₂ z), AlmostLow τ a b (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) → ¬ UnitAt z ((A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b) → z ∈ Set.range W.δ := by
  intro F _ X Y ι _ m E E' φ f hf W hα τ a b z
  obtain ⟨k, _, w, rfl⟩ : ∃ (k : Type) (_ : Field k) (w : Sp k ⟶ W.Z), w (IsLocalRing.closedPoint k) = z :=
    ⟨W.Z.residueField z, inferInstance, W.Z.fromSpecResidueField z, Scheme.fromSpecResidueField_apply _ _⟩
  intro A₁ hA₁ A₂ hA₂ hlow hnu
  have hbase : W.p₁ ≫ f = W.p₂ ≫ f := GlobalTheory.T.maps_comp_eq_of_functionField_maps_agree F X Y φ f hf.hom W hα
  obtain ⟨ev, hev, hq⟩ := GlobalTheory.T.exists_eval_regular_functions_at_fieldPoint F Y W.Z k w
  refine W.diag k w ?_
  obtain ⟨A, hA⟩ := E.nonempty (f (W.p₁ (w (IsLocalRing.closedPoint k))))
  have hff : f (W.p₂ (w (IsLocalRing.closedPoint k))) = f (W.p₁ (w (IsLocalRing.closedPoint k))) := by
    rw [← Scheme.Hom.comp_apply W.p₂ f, ← hbase, Scheme.Hom.comp_apply]
  have hM₁ := hf.sub _ A₁ hA₁ A hA
  have hM₂ := hf.sub _ A₂ hA₂ A ((congrArg (fun y => A ∈ E.S y) hff).mpr hA)
  let v : W.Z.functionField → k := fun x =>
    if h : x ∈ (algebraMap (W.Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) W.Z.functionField).range then ev ⟨x, h⟩ else 0
  have hv : ∀ x : (algebraMap (W.Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) W.Z.functionField).range,
      v x = ev x := fun x => dif_pos x.2
  have hN₁ := hM₁.map W.α₁ fun x hx => (hq W.p₁ x (mem_O_ratOf.1 hx)).1
  have hN₂ := hM₂.map W.α₂ fun x hx => (hq W.p₂ x (mem_O_ratOf.1 hx)).1
  have e₁ : ((A₁ * (A.map φ)⁻¹).map W.α₁).map v = (A₁ * (A.map φ)⁻¹).map ((ratOf Y).val (w ≫ W.p₁)) := by
    funext σ
    ext i j
    obtain ⟨h, e⟩ := hq W.p₁ _ (mem_O_ratOf.1 ((hM₁ σ).1 i j))
    exact (hv ⟨_, h⟩).trans e
  have e₂ : ((A₂ * (A.map φ)⁻¹).map W.α₂).map v = (A₂ * (A.map φ)⁻¹).map ((ratOf Y).val (w ≫ W.p₂)) := by
    funext σ
    ext i j
    obtain ⟨h, e⟩ := hq W.p₂ _ (mem_O_ratOf.1 ((hM₂ σ).1 i j))
    exact (hv ⟨_, h⟩).trans e
  have hC : (A.map φ).map W.α₁ = (A.map φ).map W.α₂ := by
    funext σ
    ext i j
    exact hα _
  have hCd : ∀ σ, (((A.map φ).map W.α₂)⁻¹ σ).det ≠ 0 := fun σ => by
    have h := hN₂.det_ne σ
    rw [Mat.map_mul, Mat.map_inv, Pi.mul_apply, Matrix.det_mul] at h
    exact right_ne_zero_of_mul h
  have hg : A₁.map W.α₁ * (A₂.map W.α₂)⁻¹ =
      (A₁ * (A.map φ)⁻¹).map W.α₁ * ((A₂ * (A.map φ)⁻¹).map W.α₂)⁻¹ := by
    rw [Mat.map_mul, Mat.map_mul, Mat.map_inv, Mat.map_inv, hC, Mat.mul_inv_rev, mul_assoc, ← mul_assoc _ _ (A₂.map W.α₂)⁻¹,
      Mat.mul_inv hCd, one_mul]
  have hG := hN₁.mul hN₂.inv
  rw [hg] at hlow hnu
  generalize hN1 : (A₁ * (A.map φ)⁻¹).map W.α₁ = N₁ at *
  generalize hN2 : (A₂ * (A.map φ)⁻¹).map W.α₂ = N₂ at *
  have hb₁ := hN₁.map_of v ev hv
  have hb₂ := hN₂.map_of v ev hv
  have hbG := hG.map_of v ev hv
  have hmul : (N₁ * N₂⁻¹).map v * N₂.map v = N₁.map v := by
    rw [← hG.map_mul_of hN₂ v ev hv, mul_assoc, Mat.inv_mul hN₂.det_ne, mul_one]
  have hv0 : v 0 = 0 := (hv 0).trans (map_zero ev)
  have hlowv : Par m ⊤ ((N₁ * N₂⁻¹).map v) := fun σ => by
    refine ⟨(hbG σ).1, (hbG σ).2.1, (hbG σ).2.2.1, fun i j _ hij => ?_⟩
    show v ((N₁ * N₂⁻¹) σ i j) = 0
    by_cases hc : (⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩
    · obtain ⟨h1, h2⟩ := hc
      cases h1
      have h3 : j = b := eq_of_heq (Sigma.mk.inj h2).2
      subst h3
      by_contra h0
      exact hnu ((hev ⟨_, (hG τ).1 a j⟩).1 fun h => h0 ((hv ⟨_, (hG τ).1 a j⟩).trans h))
    · rw [hlow.2.2 σ i j hij hc, hv0]
  have hA' : A ∈ E.S ((w ≫ W.p₁ ≫ f) (IsLocalRing.closedPoint k)) :=
    (congrArg (fun y => A ∈ E.S y) ((Scheme.Hom.comp_apply w (W.p₁ ≫ f) _).trans
      (Scheme.Hom.comp_apply W.p₁ f _))).mpr hA
  refine (hf.lifts k (w ≫ W.p₁ ≫ f) A hA' (N₁.map v) hb₁).unique ⟨Category.assoc _ _ _, A₁, ?_, ?_⟩
    ⟨(Category.assoc _ _ _).trans (congrArg (w ≫ ·) hbase.symm), A₂, ?_, ?_⟩
  · exact (congrArg (fun y => A₁ ∈ E'.S y) (Scheme.Hom.comp_apply w W.p₁ _)).mpr hA₁
  · have : Par m ⊤ (N₁.map v * (N₁.map v)⁻¹) := by rw [Mat.mul_inv hb₁.det_ne]; exact Par.one
    exact e₁ ▸ this
  · exact (congrArg (fun y => A₂ ∈ E'.S y) (Scheme.Hom.comp_apply w W.p₂ _)).mpr hA₂
  · have : Par m ⊤ (N₁.map v * (N₂.map v)⁻¹) := by
      rw [← hmul, mul_assoc, Mat.mul_inv hb₂.det_ne, mul_one]; exact hlowv
    exact e₂ ▸ this

end GlobalTheory.FlagPush
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef GlobalTheory.CechPic GlobalTheory.Points GlobalTheory.ChartGlue

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem norm_mul_exp_neg_log_normSq {u : ℂ} (hu : u ≠ 0) :
    ‖u‖ * Real.exp (-Real.log (‖u‖ ^ 2) / 2) = 1 := by
  have h : 0 < ‖u‖ := norm_pos_iff.2 hu
  rw [Real.log_pow, show -((2 : ℕ) * Real.log ‖u‖) / 2 = -Real.log ‖u‖ by push_cast; ring,
    Real.exp_neg, Real.exp_log h, mul_inv_cancel₀ h.ne']

theorem ratSec_div_eq {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) {i j : L.ι}
    (h : genericPoint X ∈ L.U i ⊓ L.U j) :
    (r i : X.functionField) / (r j : X.functionField) = fnOf _ h (L.g i j : Γ(X, L.U i ⊓ L.U j)) := by
  rw [hr i j h, mul_div_cancel_right₀ _ (r j).ne_zero]

theorem regAt_ratSec_div {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) {i j : L.ι} {x : X}
    (hi : x ∈ L.U i) (hj : x ∈ L.U j) : RegAt x ((r i : X.functionField) / (r j : X.functionField)) := by
  rw [ratSec_div_eq hr (gen_mem (memInf hi hj))]
  exact regAt_fnOf (memInf hi hj) _ _

theorem ratVal_ratSec_div {σ : k →+* ℂ} {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) {i j : L.ι}
    {y : CxPts p σ} (hi : y ∈ ptsIn p σ (L.U i)) (hj : y ∈ ptsIn p σ (L.U j)) :
    ratVal ((r i : X.functionField) / (r j : X.functionField)) y = gv p σ L i j y := by
  have hy := mem_ptsIn_inf.2 ⟨hi, hj⟩
  rw [ratSec_div_eq hr (gen_mem (mem_ptsIn.1 hy)), ratVal_fnOf hy]
  rfl

theorem norm_ratSec_div {σ : k →+* ℂ} {L : LB X} (φ : Weight p σ L) {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r)
    {i j : L.ι} {y : CxPts p σ} (hi : y ∈ ptsIn p σ (L.U i)) (hj : y ∈ ptsIn p σ (L.U j)) :
    ‖ratVal ((r i : X.functionField) / (r j : X.functionField)) y‖ * Real.exp (-(φ.φ i y - φ.φ j y) / 2) = 1 := by
  rw [ratVal_ratSec_div hr hi hj, φ.trans i j y hi hj, sub_sub_cancel]
  exact norm_mul_exp_neg_log_normSq (gv_ne_zero hi hj)

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem Le.shift {A B : HermLB p} (t : ℝ) (h : Le B A) :
    Le (B.shift (fun _ => t) fun _ => rfl) (A.shift (fun _ => t) fun _ => rfl) := by
  obtain ⟨r, r', hr, hr', hreg, hn⟩ := (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p A B).1 h
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p _ _).2 ⟨r, r', hr, hr', hreg, fun σ y i j hi hj => ?_⟩
  have e : ((A.shift (fun _ => t) fun _ => rfl).φ σ).φ i y - ((B.shift (fun _ => t) fun _ => rfl).φ σ).φ j y =
      (A.φ σ).φ i y - (B.φ σ).φ j y := by
    simp only [HermLB.shift, Weight.addFn]; ring
  rw [e]
  exact hn σ y i j hi hj

theorem Le.trans {A B M : HermLB p} (h₁ : Le B A) (h₂ : Le A M) : Le B M := by
  obtain ⟨r₁, r₁', hr₁, hr₁', hreg₁, hn₁⟩ := (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p A B).1 h₁
  obtain ⟨r₂, r₂', hr₂, hr₂', hreg₂, hn₂⟩ := (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p M A).1 h₂
  obtain ⟨a₀, h₀⟩ := exists_chart A.isLB (genericPoint X)
  let c : X.functionFieldˣ := r₂' a₀ / r₁ a₀
  have hs : IsRatSec B.B fun j => r₁' j * c := fun i j h => by
    simp only [Units.val_mul]
    rw [hr₁' i j h, mul_assoc]
  have key (a : A.B.ι) (ha : genericPoint X ∈ A.B.U a) (i : M.B.ι) (j : B.B.ι) :
      (r₂ i : X.functionField) / ((r₁' j * c : X.functionFieldˣ) : X.functionField) =
        (r₂ i : X.functionField) / (r₂' a : X.functionField) * ((r₁ a : X.functionField) / (r₁' j : X.functionField)) := by
    have e₁ := hr₁ a a₀ (memInf ha h₀)
    have e₂ := hr₂' a a₀ (memInf ha h₀)
    have n₁ := (r₁ a₀).ne_zero
    have n₂ := (r₂' a₀).ne_zero
    have n₃ := (r₂' a).ne_zero
    have n₄ := (r₁' j).ne_zero
    simp only [c, Units.val_mul, Units.val_div_eq_div_val]
    rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero n₄ (div_ne_zero n₂ n₁)) (mul_ne_zero n₃ n₄), e₁, e₂]
    field_simp
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p M B).2 ⟨r₂, _, hr₂, hs, fun x i j hi hj => ?_, fun σ y i j hi hj => ?_⟩
  · obtain ⟨a, ha⟩ := exists_chart A.isLB x
    rw [key a (gen_mem ha)]
    exact (hreg₂ x i a hi ha).mul (hreg₁ x a j ha hj)
  · have ha := mem_pick (A.φ σ).isLB y
    set a := pick (A.φ σ).isLB y
    have hx := mem_ptsIn.1 ha
    rw [key a (gen_mem hx), ratVal_mul (hreg₂ _ i a (mem_ptsIn.1 hi) hx) (hreg₁ _ a j hx (mem_ptsIn.1 hj)), norm_mul]
    have e : -((M.φ σ).φ i y - (B.φ σ).φ j y) / 2 =
        -((M.φ σ).φ i y - (A.φ σ).φ a y) / 2 + -((A.φ σ).φ a y - (B.φ σ).φ j y) / 2 := by ring
    rw [e, Real.exp_add]
    calc _ = (‖ratVal ((r₂ i : X.functionField) / (r₂' a : X.functionField)) y‖ *
          Real.exp (-((M.φ σ).φ i y - (A.φ σ).φ a y) / 2)) *
        (‖ratVal ((r₁ a : X.functionField) / (r₁' j : X.functionField)) y‖ *
          Real.exp (-((A.φ σ).φ a y - (B.φ σ).φ j y) / 2)) := by ring
      _ ≤ 1 := mul_le_one₀ (hn₂ σ y i a hi ha) (by positivity) (hn₁ σ y a j ha hj)

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem Le.tens {A B : HermLB p} (M : HermLB p) (h : Le B A) : Le (M.tens B) (M.tens A) := by
  obtain ⟨r, r', hr, hr', hreg, hn⟩ := (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p A B).1 h
  obtain ⟨ρ, hρ⟩ := exists_isRatSec M.isLB
  have hs := ((presents_divOfRatSec M.isLB hρ).tens (presents_divOfRatSec A.isLB hr)).isRatSec
  have hs' := ((presents_divOfRatSec M.isLB hρ).tens (presents_divOfRatSec B.isLB hr')).isRatSec
  have key (c : M.B.ι × A.B.ι) (d : M.B.ι × B.B.ι) :
      ((ρ c.1 * r c.2 : X.functionFieldˣ) : X.functionField) / ((ρ d.1 * r' d.2 : X.functionFieldˣ) : X.functionField) =
        (ρ c.1 : X.functionField) / (ρ d.1 : X.functionField) * ((r c.2 : X.functionField) / (r' d.2 : X.functionField)) := by
    rw [Units.val_mul, Units.val_mul, mul_div_mul_comm]
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p (M.tens A) (M.tens B)).2 ⟨fun c => ρ c.1 * r c.2, fun d => ρ d.1 * r' d.2, hs, hs',
    fun x c d hc hd => ?_, fun σ y c d hc hd => ?_⟩
  · beta_reduce
    erw [key c d]
    exact (regAt_ratSec_div hρ hc.1 hd.1).mul (hreg x c.2 d.2 hc.2 hd.2)
  · have hc' := mem_ptsIn_inf.1 hc
    have hd' := mem_ptsIn_inf.1 hd
    beta_reduce
    erw [key c d]
    rw [ratVal_mul (regAt_ratSec_div hρ (mem_ptsIn.1 hc'.1) (mem_ptsIn.1 hd'.1))
      (hreg _ c.2 d.2 (mem_ptsIn.1 hc'.2) (mem_ptsIn.1 hd'.2)), norm_mul]
    have e : -(((M.tens A).φ σ).φ c y - ((M.tens B).φ σ).φ d y) / 2 =
        -((M.φ σ).φ c.1 y - (M.φ σ).φ d.1 y) / 2 + -((A.φ σ).φ c.2 y - (B.φ σ).φ d.2 y) / 2 := by
      simp only [HermLB.tens, Weight.tens]; ring
    rw [e, Real.exp_add]
    calc _ = (‖ratVal ((ρ c.1 : X.functionField) / (ρ d.1 : X.functionField)) y‖ *
          Real.exp (-((M.φ σ).φ c.1 y - (M.φ σ).φ d.1 y) / 2)) *
        (‖ratVal ((r c.2 : X.functionField) / (r' d.2 : X.functionField)) y‖ *
          Real.exp (-((A.φ σ).φ c.2 y - (B.φ σ).φ d.2 y) / 2)) := by ring
      _ ≤ 1 := by
        rw [norm_ratSec_div (M.φ σ) hρ hc'.1 hd'.1, one_mul]
        exact hn σ y c.2 d.2 hc'.2 hd'.2

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem le_of_isometric {A B : HermLB p} (hi : B.Isometric A) : Le B A := by
  classical
  obtain ⟨w, hw, h⟩ := hi.exists_units
  obtain ⟨r, hr⟩ := exists_isRatSec B.isLB
  obtain ⟨b₀, h₀⟩ := exists_chart B.isLB (genericPoint X)
  let F (U : X.Opens) (u : Γ(X, U)ˣ) : X.functionFieldˣ := gm (𝟙 X) (genericPoint X) U u
  have hF (U : X.Opens) (u : Γ(X, U)ˣ) (hU : genericPoint X ∈ U) : (F U u : X.functionField) = fnOf U hU u.val :=
    gm_val (𝟙 X) _ U hU u
  have hw' (a a' b b') (h₁ : genericPoint X ∈ A.B.U a) (h₂ : genericPoint X ∈ A.B.U a')
      (h₃ : genericPoint X ∈ B.B.U b) (h₄ : genericPoint X ∈ B.B.U b') :
      F _ (w a b) = F _ (A.B.g a a') * (F _ (B.B.g b b'))⁻¹ * F _ (w a' b') :=
    hw _ (𝟙 X) _ a a' b b' h₁ h₂ h₃ h₄
  have hM (a) (h₁ : genericPoint X ∈ A.B.U a) : F _ (A.B.g a a) = 1 := gm_self A.isLB (𝟙 X) _ h₁
  have hL : F _ (B.B.g b₀ b₀) = 1 := gm_self B.isLB (𝟙 X) _ h₀
  have hr' : IsRatSec A.B fun a => F _ (w a b₀) * r b₀ := fun a a' h' => by
    beta_reduce
    rw [← hF, ← Units.val_mul, hw' a a' b₀ b₀ h'.1 h'.2 h₀ h₀, hL, inv_one, mul_one, mul_assoc]
  have key (a b) (h' : genericPoint X ∈ A.B.U a ⊓ B.B.U b) :
      ((F _ (w a b₀) * r b₀ : X.functionFieldˣ) : X.functionField) / (r b : X.functionField) = fnOf _ h' (w a b).val := by
    rw [div_eq_iff (r b).ne_zero, ← hF, hr b b₀ (memInf h'.2 h₀), ← hF _ (B.B.g b b₀), ← Units.val_mul, ← Units.val_mul,
      hw' a a b b₀ h'.1 h'.1 h'.2 h₀, hM a h'.1, one_mul, mul_comm (F _ (B.B.g b b₀))⁻¹, mul_assoc,
      inv_mul_cancel_left]
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p A B).2 ⟨_, r, hr', hr, fun x a b ha hb => ?_, fun σ y a b ha hb => ?_⟩
  · beta_reduce
    rw [key a b (gen_mem (memInf ha hb))]
    exact regAt_fnOf (memInf ha hb) _ _
  · have hab := mem_ptsIn_inf.2 ⟨ha, hb⟩
    beta_reduce
    rw [key a b (gen_mem (mem_ptsIn.1 hab)), ratVal_fnOf hab, h σ a b y ha hb, add_sub_cancel_left, logSq,
      norm_mul_exp_neg_log_normSq (ev_ne_zero hab (Units.isUnit _))]

theorem le_tens_isometric_trans_shift : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ A B M : HermLB p, (Le B A → Le (M.tens B) (M.tens A)) ∧ (B.Isometric A → Le B A) ∧ (Le B A → Le A M → Le B M) ∧
      ∀ t : ℝ, Le B A → Le (B.shift (fun _ => t) fun _ => rfl) (A.shift (fun _ => t) fun _ => rfl) :=
  fun _ _ _ _ _ _ _ _ => ⟨Le.tens _, le_of_isometric, Le.trans, fun t => Le.shift t⟩

end GlobalTheory.HSNef
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem isometric_keeps : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ L M : HermLB p, L.Isometric M → (L.SemiPos D → M.SemiPos D) ∧
      (L.IsNef D → M.IsNef D) ∧ (HtNef L D → HtNef M D) ∧ (∀ a, L.IsSelfInter a → M.IsSelfInter a) ∧
      (IsAmpleLB L.B → IsAmpleLB M.B) := by
  intro hA k _ X _ p D hX L M e
  have hS : L.SemiPos D → M.SemiPos D := HermLB.Isometric.semiPos L M D e
  refine ⟨hS, fun hL => ?_, fun hL => ⟨hS hL.1, fun h H x => hL.2 h (e.symm.isArithHeight hX H) x⟩,
    fun a ha => e.isSelfInter hX ha, fun hL => ?_⟩
  · obtain ⟨h, H⟩ := (hA.arExists k X p D hX).1 L
    have HM := e.isArithHeight hX H
    obtain ⟨h₁, h₂⟩ := (H.isNef_iff hX).1 hL
    exact (HM.isNef_iff hX).2 ⟨hS h₁, h₂⟩
  · obtain ⟨w, hw, -⟩ := e.symm
    exact IsAmpleLB.of_lbIso hL M.isLB ⟨w, hw⟩

end GlobalTheory.HSNef
end
end

section

open NumberField IsDedekindDomain GlobalTheory.LKMid GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LKMid

theorem t2Space_kq {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) :
    T2Space (KQ p K r) := by
  haveI : IsModuleTopology ℚ_[p] (KQ p K r) := ⟨rfl⟩
  let b := Module.Free.chooseBasis ℚ_[p] (KQ p K r)
  let φ : KQ p K r →ₗ[ℚ_[p]] (Module.Free.ChooseBasisIndex ℚ_[p] (KQ p K r) → ℚ_[p]) :=
    Finsupp.lcoeFun ∘ₗ b.repr.toLinearMap
  have hinj : Function.Injective φ := by
    intro x y h
    apply b.repr.injective
    exact DFunLike.coe_injective h
  exact T2Space.of_injective_continuous hinj (IsModuleTopology.continuous_of_linearMap φ)

end GlobalTheory.LKMid
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.TenFin

theorem finite_quot_of_gen {R A B : Type} [CommRing R] [CommRing A] [CommRing B] (I : Ideal R)
    (f : A →+* R) (g : B →+* R) (J₁ : Ideal A) (J₂ : Ideal B) (h₁ : J₁.map f ≤ I) (h₂ : J₂.map g ≤ I)
    [Finite (A ⧸ J₁)] [Finite (B ⧸ J₂)] (hgen : Subring.closure (Set.range f ∪ Set.range g) = ⊤)
    (n : ℕ) (hn : n ≠ 0) (hI : (n : R) ∈ I) : Finite (R ⧸ I) := by
  let π := Ideal.Quotient.mk I
  let fa : A ⧸ J₁ →+* R ⧸ I := Ideal.Quotient.lift J₁ (π.comp f) (fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (h₁ (Ideal.mem_map_of_mem f ha)))
  let gb : B ⧸ J₂ →+* R ⧸ I := Ideal.Quotient.lift J₂ (π.comp g) (fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (h₂ (Ideal.mem_map_of_mem g ha)))
  have hfa : ∀ a, π (f a) = fa (Ideal.Quotient.mk J₁ a) := fun a => rfl
  have hgb : ∀ b, π (g b) = gb (Ideal.Quotient.mk J₂ b) := fun b => rfl
  let S : Set (R ⧸ I) := Set.image2 (· * ·) (Set.range fa) (Set.range gb)
  have hS : S.Finite := (Set.finite_range fa).image2 _ (Set.finite_range gb)
  let M : Submonoid (R ⧸ I) :=
    { carrier := S
      one_mem' := ⟨1, ⟨1, map_one _⟩, 1, ⟨1, map_one _⟩, one_mul 1⟩
      mul_mem' := by
        rintro _ _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ ⟨_, ⟨a', rfl⟩, _, ⟨b', rfl⟩, rfl⟩
        refine ⟨fa (a * a'), ⟨_, rfl⟩, gb (b * b'), ⟨_, rfl⟩, ?_⟩
        simp only [map_mul]; ring }
  have hsub : π '' (Set.range f ∪ Set.range g) ⊆ (M : Set (R ⧸ I)) := by
    rintro _ ⟨_, ⟨a, rfl⟩ | ⟨b, rfl⟩, rfl⟩
    · exact ⟨fa (Ideal.Quotient.mk J₁ a), ⟨_, rfl⟩, 1, ⟨1, map_one _⟩, (mul_one _).trans (hfa a).symm⟩
    · exact ⟨1, ⟨1, map_one _⟩, gb (Ideal.Quotient.mk J₂ b), ⟨_, rfl⟩, (one_mul _).trans (hgb b).symm⟩
  have htop : AddSubgroup.closure S = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Subring.closure (π '' (Set.range f ∪ Set.range g)) := by
      rw [← RingHom.map_closure, hgen, ← RingHom.range_eq_map]
      exact Ideal.Quotient.mk_surjective x
    rw [Subring.mem_closure_iff] at hx
    refine AddSubgroup.closure_mono ?_ hx
    exact Submonoid.closure_le.2 hsub
  haveI : AddGroup.FG (R ⧸ I) := AddGroup.fg_iff.mpr ⟨S, htop, hS⟩
  refine AddCommGroup.finite_of_fg_torsion _ fun x => ?_
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, Nat.pos_of_ne_zero hn, ?_⟩
  rw [nsmul_eq_mul]
  have : (n : R ⧸ I) = 0 := by
    rw [← map_natCast π]; exact Ideal.Quotient.eq_zero_iff_mem.2 hI
  rw [this, zero_mul]

theorem finite_intKQ_quot : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r m : ℕ),
    Finite (GlobalTheory.LKLoc.intK p K ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p K) ^ m}) →
    Finite (GlobalTheory.LKLoc.intK p (Qr p r) ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p (Qr p r)) ^ m}) →
    Finite (intKQ p K r ⧸ Ideal.span {(p : intKQ p K r) ^ m}) := by
  intro p _ K r m hA hB
  let f : GlobalTheory.LKLoc.intK p K →+* intKQ p K r :=
    ((inclK p K r).toRingHom.comp (GlobalTheory.LKLoc.intK p K).subtype).codRestrict (intKQ p K r)
      (fun a => Subring.subset_closure (Or.inl ⟨a, rfl⟩))
  let g : GlobalTheory.LKLoc.intK p (Qr p r) →+* intKQ p K r :=
    ((inclQ p K r).toRingHom.comp (GlobalTheory.LKLoc.intK p (Qr p r)).subtype).codRestrict (intKQ p K r)
      (fun b => Subring.subset_closure (Or.inr ⟨⟨b.1, b.2⟩, rfl⟩))
  have hgen : Subring.closure (Set.range f ∪ Set.range g) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    induction hx using Subring.closure_induction with
    | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
      · exact Subring.subset_closure (Or.inr ⟨⟨b.1, b.2⟩, rfl⟩)
    | zero => exact zero_mem _
    | one => exact one_mem _
    | add y z _ _ h1 h2 => exact add_mem h1 h2
    | neg y _ h => exact neg_mem h
    | mul y z _ _ h1 h2 => exact mul_mem h1 h2
  refine finite_quot_of_gen (J₁ := Ideal.span {(p : GlobalTheory.LKLoc.intK p K) ^ m})
    (J₂ := Ideal.span {(p : GlobalTheory.LKLoc.intK p (Qr p r)) ^ m}) _ f g ?_ ?_ hgen (p ^ m) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) ?_
  · rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]
  · rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]
  · rw [Nat.cast_pow]; exact Ideal.subset_span rfl

end GlobalTheory.TenFin
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
open CategoryTheory.Limits TopologicalSpace

namespace GlobalTheory.Mean4O.CoverDom

theorem isNormalScheme_G {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) : GlobalTheory.IsNormalScheme V.G := by
  have : GlobalTheory.IsNormalScheme V.X := GlobalTheory.IsNormalScheme.of_pred V.normal
  have : Flat (spMap (algebraMap (𝓞 F) F)) := flat_specMap_localization (nonZeroDivisors (𝓞 F)) F
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  have : Flat V.j := MorphismProperty.of_isPullback V.pb.flip ‹_›
  have : IsPreimmersion V.j := MorphismProperty.of_isPullback V.pb.flip ‹_›
  have : ∀ x, IsIso (V.j.stalkMap x) := fun x => isIso_stalkMap_of_flat_of_surjectiveOnStalks V.j x
  exact GlobalTheory.IsNormalScheme.of_isIso_stalkMap V.j

end GlobalTheory.Mean4O.CoverDom
end
end
