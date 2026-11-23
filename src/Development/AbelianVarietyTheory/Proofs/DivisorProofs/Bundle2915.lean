module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2808
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BudgetOfSizeAndWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle941
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Star.Int
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PushDiv

theorem hasDim_lt {X : Scheme.{0}} {x y : X} {d d' : ℕ} (hxy : y ⤳ x) (hne : x ≠ y)
    (hx : HasDim x d) (hy : HasDim y d') : d < d' := by
  have hsub : closure ({x} : Set X) ⊆ closure {y} := specializes_iff_closure_subset.1 hxy
  have hne' : closure ({x} : Set X) ≠ closure {y} := fun e =>
    hne (inseparable_iff_closure_eq.2 e).eq
  have h := topologicalKrullDim_add_one_le_of_ssubset X _ _ isClosed_closure
    isIrreducible_singleton.closure isIrreducible_singleton.closure (ssubset_of_subset_of_ne hsub hne')
  rw [show topologicalKrullDim (closure ({x} : Set X)) = d from hx,
    show topologicalKrullDim (closure ({y} : Set X)) = d' from hy] at h
  have h' : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d' : WithBot ℕ∞) := by exact_mod_cast h
  have h'' : d + 1 ≤ d' := by exact_mod_cast h'
  omega

theorem mult_genericPoint {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] (D : CartierDiv Z) :
    D.mult (genericPoint Z) = 0 := by
  rw [(D.isEqn_genericPoint 1).mult_eq]
  exact (unitAt_one _).ord_eq_zero

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (g : Y ⟶ X) (hη' : g (genericPoint Y) ⤳ genericPoint X) {B : LB X} (hB : B.IsLB)
  {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r)

theorem mult_pull_eq (w : Y) (i : B.ι) (hi : g w ∈ B.U i) :
    (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).mult w =
      Scheme.ord (TrueGeo.SmallSec.fnMap g hη' (r i : X.functionField)) w :=
  by
  have hm : w ∈ (B.pull g).U (fun _ => i) := Set.mem_iInter.2 fun _ => hi
  have h := (presents_divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).isEqn
    (fun _ => i) w hm
  rw [h.mult_eq]
  rfl

theorem mult_eq_chart (z : X) (i : B.ι) (hi : z ∈ B.U i) :
    (divOfRatSec hB hr).mult z = Scheme.ord (r i : X.functionField) z :=
  ((presents_divOfRatSec hB hr).isEqn i z hi).mult_eq

theorem map_ne_genericPoint (w : Y)
    (hw : (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).mult w ≠ 0) :
    g w ≠ genericPoint X := by
  intro e
  obtain ⟨i, hi⟩ := exists_chart hB (g w)
  apply hw
  rw [mult_pull_eq g hη' hB hr w i hi]
  exact (FrameGlue.Pull.unitAt_fnMap g hη' (e ▸ unitAt_genericPoint (r i).ne_zero)).ord_eq_zero

end GlobalTheory.PushDiv

namespace GlobalTheory.PushDiv

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (g : Y ⟶ X) (hη' : g (genericPoint Y) ⤳ genericPoint X) {B : LB X} (hB : B.IsLB)
  {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r)
  {k : Type} [CommRing k] {p : X ⟶ Sp k} {q : Y ⟶ Sp k}

theorem degree_ne_zero_and_coheight (hp : IsAmb p) (hq : IsAmb q) (hg : g ≫ p = q)
    (hη : g (genericPoint Y) = genericPoint X) (w : Y)
    (hw : (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).mult w ≠ 0)
    (hd : g.residueDegree w ≠ 0) :
    g.residueDegree (genericPoint Y) ≠ 0 ∧ Order.coheight (g w) = 1 := by
  have hw1 := CartierDiv.coheight_eq_one_of_mult_ne_zero hw
  have hgw := map_ne_genericPoint g hη' hB hr w hw
  have hwY : w ≠ genericPoint Y := fun e => hw (e ▸ mult_genericPoint _)
  have AY := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q hq
  have AX := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hp
  obtain ⟨mY, hmY⟩ := AY.1
  obtain ⟨mX, hmX⟩ := AX.1
  obtain ⟨dY, -, hdY⟩ := hmY (genericPoint Y)
  obtain ⟨dw, -, hdw⟩ := hmY w
  have hlt : dw < dY := hasDim_lt (genericPoint_specializes w) hwY hdw hdY
  obtain ⟨e, rfl⟩ : ∃ e, dY = e + 1 := ⟨dY - 1, by omega⟩
  have hYdim : topologicalKrullDim Y = ((e + 1 : ℕ) : WithBot ℕ∞) := (AY.2.2.2.2.2 Y (e + 1)).1 hdY
  have hwe : HasDim w e := ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq e hYdim).1 w).1 hw1
  obtain ⟨dgw, -, hdgw⟩ := hmX (g w)
  obtain ⟨dX, -, hdX⟩ := hmX (genericPoint X)
  have h1 := GlobalTheory.T.pointClosureDim_le_and_residueDegree_ne_zero_iff k X Y p q hp hq g hg w e dgw hwe hdgw
  have hdX' : HasDim (g (genericPoint Y)) dX := by rw [hη]; exact hdX
  have h2 := GlobalTheory.T.pointClosureDim_le_and_residueDegree_ne_zero_iff k X Y p q hp hq g hg (genericPoint Y) (e + 1) dX hdY hdX'
  have h3 : dgw < dX := hasDim_lt (genericPoint_specializes (g w)) hgw hdgw hdX
  have he : e = dgw := h1.2.1 hd
  have hXe : dX = e + 1 := by omega
  refine ⟨h2.2.2 hXe.symm, ?_⟩
  have hXdim : topologicalKrullDim X = ((e + 1 : ℕ) : WithBot ℕ∞) :=
    (AX.2.2.2.2.2 X (e + 1)).1 (hXe ▸ hdX)
  exact ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k X p hp e hXdim).1 (g w)).2 (he ▸ hdgw)

end GlobalTheory.PushDiv

namespace GlobalTheory.PushDiv

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (g : Y ⟶ X) (hη' : g (genericPoint Y) ⤳ genericPoint X) {B : LB X} (hB : B.IsLB)
  {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r)
  {k : Type} [CommRing k] {p : X ⟶ Sp k} {q : Y ⟶ Sp k}


open Classical in
theorem fiber_sum (hp : IsAmb p) (hq : IsAmb q) (hg : g ≫ p = q)
    (hη : g (genericPoint Y) = genericPoint X) [CompactSpace Y] (z : X) :
    ∑ w ∈ (CartierDiv.finite_support_mult
        (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr))).toFinset with g w = z,
      (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).mult w *
        (g.residueDegree w : ℤ) =
    (g.residueDegree (genericPoint Y) : ℤ) * (divOfRatSec hB hr).mult z := by
  by_cases h : g.residueDegree (genericPoint Y) ≠ 0 ∧ Order.coheight z = 1
  · obtain ⟨i, hi⟩ := exists_chart hB z
    have H := GlobalTheory.T.sum_schemeOrd_pullback_residueDegree_codimOne k X Y p q hp hq g hg hη h.1 z h.2 (r i : X.functionField) (r i).ne_zero
    have H2 : ∑ᶠ w ∈ g ⁻¹' {z},
        (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).mult w *
          (g.residueDegree w : ℤ) =
        (g.residueDegree (genericPoint Y) : ℤ) * (divOfRatSec hB hr).mult z := by
      rw [mult_eq_chart hB hr z i hi, ← H]
      refine finsum_mem_congr rfl fun w hw => ?_
      have hw' : g w = z := hw
      rw [mult_pull_eq g hη' hB hr w i (by rw [hw']; exact hi)]
    rw [← H2]
    refine (finsum_mem_eq_sum_of_inter_support_eq _ ?_).symm
    ext w
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_filter,
      Set.Finite.mem_toFinset, Function.mem_support, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨left_ne_zero_of_mul h2, h1⟩, h2⟩
    · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
  · have hR : (g.residueDegree (genericPoint Y) : ℤ) * (divOfRatSec hB hr).mult z = 0 := by
      by_cases hδ : g.residueDegree (genericPoint Y) = 0
      · rw [hδ, Nat.cast_zero, zero_mul]
      · have hz : Order.coheight z ≠ 1 := fun hz => h ⟨hδ, hz⟩
        rw [show (divOfRatSec hB hr).mult z = 0 from
          by_contra fun h0 => hz (CartierDiv.coheight_eq_one_of_mult_ne_zero h0), mul_zero]
    rw [hR]
    refine Finset.sum_eq_zero fun w hw => ?_
    have hwz : g w = z := (Finset.mem_filter.1 hw).2
    by_contra hne
    have h1 := left_ne_zero_of_mul hne
    have h2 : g.residueDegree w ≠ 0 := fun h0 => hne (by rw [h0, Nat.cast_zero, mul_zero])
    obtain ⟨hδ, hc⟩ := degree_ne_zero_and_coheight g hη' hB hr hp hq hg hη w h1 h2
    exact h ⟨hδ, hwz ▸ hc⟩

end GlobalTheory.PushDiv

namespace GlobalTheory.PushDiv

theorem finsum_mult_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), ∀ (B : LB X) (hB : B.IsLB) (r : B.ι → X.functionFieldˣ) (hr : IsRatSec B r) (φ : X → ℝ), ∑ᶠ w, ((divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr)).mult w : ℝ) * ((g.residueDegree w : ℝ) * φ (g w)) = (g.residueDegree (genericPoint Y) : ℝ) * ∑ᶠ z, ((divOfRatSec hB hr).mult z : ℝ) * φ z := by
  intro k _ X Y _ _ _ _ p q hp hq g hg hη B hB r hr φ
  classical
  haveI := hq.isNoetherian
  haveI := hp.isNoetherian
  set D' := divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g
    (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) with hD'
  set D := divOfRatSec hB hr with hD
  set S := D'.finite_support_mult.toFinset with hS
  set T := S.image g ∪ D.finite_support_mult.toFinset with hT
  have hL : ∑ᶠ w, (D'.mult w : ℝ) * ((g.residueDegree w : ℝ) * φ (g w)) =
      ∑ w ∈ S, (D'.mult w : ℝ) * ((g.residueDegree w : ℝ) * φ (g w)) := by
    apply finsum_eq_sum_of_support_subset
    intro w hw
    rw [hS, Set.Finite.coe_toFinset]
    exact fun h0 => hw (by simp only [h0, Int.cast_zero, zero_mul])
  have hR : ∑ᶠ z, (D.mult z : ℝ) * φ z = ∑ z ∈ T, (D.mult z : ℝ) * φ z := by
    apply finsum_eq_sum_of_support_subset
    intro z hz
    rw [hT, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inr fun h0 => hz (by simp only [h0, Int.cast_zero, zero_mul])
  rw [hL, hR, ← Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := g)
    (fun w hw => Finset.mem_union_left _ (Finset.mem_image_of_mem g hw)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hF := fiber_sum g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hB hr hp hq hg hη z
  calc ∑ w ∈ S with g w = z, (D'.mult w : ℝ) * ((g.residueDegree w : ℝ) * φ (g w))
      = ((∑ w ∈ S with g w = z, D'.mult w * (g.residueDegree w : ℤ) : ℤ) : ℝ) * φ z := by
        rw [Int.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [(Finset.mem_filter.1 hw).2]
        push_cast
        ring
    _ = (g.residueDegree (genericPoint Y) : ℝ) * ((D.mult z : ℝ) * φ z) := by
        rw [hF]
        push_cast
        ring

end GlobalTheory.PushDiv
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

open GlobalTheory.ChartGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixGen

theorem ofReal_dens_trans {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) (ε : ℤˣ) (c c' : AlgChart p σ D) (y : CxPts p σ) (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) :
    ENNReal.ofReal ((ε : ℤ) * dens L c y) =
      ENNReal.ofReal (‖transDet c.e c'.e y‖ ^ 2) * ENNReal.ofReal ((ε : ℤ) * dens L c' y) := by
  rw [GlobalTheory.T.mixedChernFormDensity_change_of_chart k X p σ D L c c' y hy hy', ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem map_part {k K : Type} [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] {X G : Scheme.{0}}
    [IsIntegral X] {p : X ⟶ Sp k} {q : G ⟶ Sp K} {j : G ⟶ X}
    (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) {D : ℕ} (hX : IsArithVar p D)
    (L : Fin D → MLine p (τ.comp (algebraMap k K))) (ε : ℤˣ) :
    Measure.map (bcPt hp.w τ) (part (fun i => (L i).bc hp.w τ) ε) = part L ε := by
  have hm : IsHomeomorph (bcPt hp.w τ) := GlobalTheory.T.complexPointsOverRingHom_isHomeomorph_baseChange k K (algebraMap k K) X G p q j hp τ
  obtain ⟨_, hT2, hSC⟩ := (IsArithVar.finite_emb_and_topology hX).2 (τ.comp (algebraMap k K))
  let h := hm.homeomorph (bcPt hp.w τ)
  haveI : T2Space (CxPts q τ) := h.isEmbedding.t2Space
  haveI : SecondCountableTopology (CxPts q τ) := h.isEmbedding.secondCountableTopology
  obtain ⟨hGi, _, _, _, hgen, _⟩ := GlobalTheory.Mix.genericFibre_facts k K X G p q j hp D hX
  obtain ⟨U, hU, hηU, t, ht⟩ := GenericCoords.exists_affine_etale_coords hX
  have hZ : IsClosed ((U : Set X)ᶜ) := U.isOpen.isClosed_compl
  have hgZ : genericPoint X ∉ (U : Set X)ᶜ := fun h => h hηU
  have hTc : IsClosed {y : CxPts p (τ.comp (algebraMap k K)) |
      y.1 (IsLocalRing.closedPoint ℂ) ∈ (U : Set X)ᶜ} := by
    have e : {y : CxPts p (τ.comp (algebraMap k K)) | y.1 (IsLocalRing.closedPoint ℂ) ∈ (U : Set X)ᶜ} =
        (ptsIn p (τ.comp (algebraMap k K)) U)ᶜ := by
      ext y
      simp [mem_ptsIn]
    rw [e]
    exact (isOpen_ptsIn _).isClosed_compl
  have hZG : IsClosed (j ⁻¹' (U : Set X)ᶜ) := hZ.preimage j.continuous
  have hgZG : genericPoint G ∉ j ⁻¹' (U : Set X)ᶜ := by
    simp only [Set.mem_preimage]
    rw [hgen]
    exact hgZ
  have key := GlueCoverNull.map_glueMeas_of_cover D (CxPts p (τ.comp (algebraMap k K))) (CxPts q τ)
    (AlgChart p (τ.comp (algebraMap k K)) D) (AlgChart q τ D) (fun c => c.e)
    (fun c y => ENNReal.ofReal ((ε : ℤ) * dens L c y)) (fun c => c.e)
    (fun c y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).bc hp.w τ) c y))
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ofReal_dens_trans L ε c c' y hy hy')
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ofReal_dens_trans _ ε c c' y hy hy')
    (bcPt hp.w τ) hm.continuous _ hTc (fun c => ChernNull.chart_null hX hZ hgZ _ c)
    (fun c => ChernNull.chart_null_field K G q τ D _ hZG hgZG c) 1
    (fun x _ => by
      obtain ⟨w0, hw0⟩ := hm.surjective x
      exact Set.encard_eq_one.2 ⟨w0, Set.ext fun w =>
        ⟨fun hw => hm.injective (hw.trans hw0.symm), fun hw => hw ▸ hw0⟩⟩)
    (fun z hz => by
      have hmem : bcPt hp.w τ z ∈ ptsIn p (τ.comp (algebraMap k K)) U := by
        simpa [mem_ptsIn] using hz
      obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hU t ht hmem
      obtain ⟨c', hz', hc'⟩ := GlobalTheory.Mix.exists_chart_dens_bc k K (algebraMap k K) X G p q j hp τ D c z hc
      exact ⟨c, c', hz', hc, fun w hw _ => ⟨(hc' w hw).2.1, by simp only [(hc' w hw).2.2 L]⟩⟩)
  rw [Nat.cast_one, one_smul] at key
  exact key

theorem part_int_generic : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (D : ℕ), IsArithVar p D → ∀ (L : Fin D → MLine p (τ.comp (algebraMap k K))), (∀ ε : ℤˣ, Measure.map (bcPt hp.w τ) (part (fun i => (L i).bc hp.w τ) ε) = part L ε) ∧ ∀ f : CxPts p (τ.comp (algebraMap k K)) → ℝ, (Intg (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) ↔ Intg L f) ∧ Mix.int (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) = Mix.int L f := by
  intro k K _ _ _ _ X G _ p q j hp τ D hX L
  have hmap := map_part hp τ hX L
  have hm : IsHomeomorph (bcPt hp.w τ) := GlobalTheory.T.complexPointsOverRingHom_isHomeomorph_baseChange k K (algebraMap k K) X G p q j hp τ
  have he : MeasurableEmbedding (bcPt hp.w τ) := (hm.homeomorph (bcPt hp.w τ)).measurableEmbedding
  refine ⟨hmap, fun f => ⟨?_, ?_⟩⟩
  · simp only [Intg]
    rw [← hmap 1, ← hmap (-1), he.integrable_map_iff, he.integrable_map_iff]
    rfl
  · simp only [Mix.int]
    rw [← hmap 1, ← hmap (-1), he.integral_map, he.integral_map]

end GlobalTheory.MixGen
end
end

section



open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.CovHt.DividedNum

section Point

open _root_.Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem zBase_pow_le_lenT {PP A : ℝ} (h : HostNum D L PP A 1) (hw : WtNum p i PP) :
    zBase L ^ 24 ≤ (lenT p i PP : ℝ) := by
  have m2 := D.R.two_le_m
  have k3 := D.R.m_add_three_le_k
  have f8 := h.f8
  have hDd : (1 : ℝ) ≤ dimFlag (dat p i) := by
    rw [hw.dim]
    exact_mod_cast Nat.mul_pos (by omega) (Nat.choose_pos (by unfold Ranks.r; omega))
  have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have hkm : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hL : (0 : ℝ) ≤ L.sc.L := by linarith [h.big.2.1]
  have hZ : 0 ≤ zBase L := by unfold zBase; positivity
  have hP : zBase L ^ 24 ≤ PP ^ 2 := by
    rw [show (24 : ℕ) = 12 * 2 by norm_num, pow_mul]
    exact pow_le_pow_left₀ (by positivity) h.ppLow 2
  have hPP : 0 ≤ PP ^ 2 := sq_nonneg _
  have h1 : PP ^ 2 ≤ PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
    rw [le_div_iff₀ hm]
    have a : (1 : ℝ) ≤ (dimFlag (dat p i) : ℝ) ^ 2 := one_le_pow₀ hDd
    have b : PP ^ 2 * D.R.m ≤ PP ^ 2 * D.R.k := mul_le_mul_of_nonneg_left hkm hPP
    have c : PP ^ 2 * D.R.k ≤ PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 * D.R.k :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hPP a) (by linarith)
    linarith
  exact hP.trans (h1.trans (Nat.le_ceil _))

theorem at_point {PP A : ℝ} (h : HostNum D L PP A 1) (hw : WtNum p i PP) (hi : (i : ℕ) + 1 < D.R.m) :
    zBase L ^ 24 ≤ (lenT p i PP : ℝ) ∧ ∀ u1, Quo p i PP u1 →
      lenT p i PP * GlobalTheory.CovHt.l1 u1 ≤ 834 * unitE p ∧
      ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → (lenT p i PP : ℤ) ≤ u1 τ a - u1 τ b := by
  refine ⟨zBase_pow_le_lenT p i h hw, fun u1 hq => ?_⟩
  obtain ⟨h0, S, eta, hS, he, hP, h4, hh, hH⟩ := hw.hyp hi
  have hW := hH u1
  have hD := (quo_iff p i PP h0 S eta u1).1 hq
  refine ⟨?_, ?_⟩
  · obtain ⟨hp1, hp2⟩ := GlobalTheory.CovHt.BudgetPf.pp_bounds h
    have m2 := D.R.two_le_m
    have k3 := D.R.m_add_three_le_k
    have f8 := h.f8
    have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by omega : 1 ≤ D.R.f)
    have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
    have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    have hb : 0 < L.sc.b := Real.exp_pos _
    have hcard : (Fintype.card (Psi p.T.Q.H) : ℝ) = D.R.f := by rw [← hw.card, Nat.card_eq_fintype_card]
    have hN : (((dat p i).p + (dat p i).q : ℕ) : ℝ) = D.R.r := by rw [hw.sig.2.2]
    have hT : (0 : ℝ) ≤ lenT p i PP := Nat.cast_nonneg _
    have fr : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ PP := by
      refine le_trans ?_ hp1
      have f2 : (D.R.f : ℝ) ≤ (D.R.f : ℝ) ^ 2 := le_self_pow₀ hf (by norm_num)
      have r2 : (D.R.r : ℝ) ^ 2 ≤ (D.R.r : ℝ) ^ 5 := pow_le_pow_right₀ hr (by norm_num)
      gcongr
    have rr : (D.R.r : ℝ) ^ 2 ≤ PP := le_trans (le_mul_of_one_le_left (by positivity) hf) fr
    have r1 : (D.R.r : ℝ) ≤ (D.R.r : ℝ) ^ 2 := le_self_pow₀ hr (by norm_num)
    have hPP : 1 ≤ PP := by nlinarith
    obtain ⟨a1, -, -⟩ := GlobalTheory.MeanTop.divided_weight_size _ _ _ hW hD
    have a3 := GlobalTheory.CovHt.BudgetPf.l1_u_le _ hW hS
    have e1 : (dat p i).p + (dat p i).q - (wtsAt p i PP h0 S eta u1).kc = D.R.m := by
      show (dat p i).p + (dat p i).q - (D.R.k - 1) = _
      rw [hw.sig.2.2]; unfold Ranks.r; omega
    rw [e1, hcard, hN] at a3
    rw [hcard, hN] at a1
    change _ ≤ D.R.f * (D.R.r * S + D.R.m * (2 * (4 * L.sc.b))) at a3
    change (lenT p i PP : ℝ) * GlobalTheory.MeanTop.l1 u1 ≤ _ + D.R.f * D.R.r * ((cZero D ((i : ℕ) + 1) : ℤ) + 4 * D.R.r) at a1
    have c1 : ((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) ≤ 22 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4 := by
      exact_mod_cast (cZero_spec D ((i : ℕ) + 1)).2.2
    have c2 : (D.R.r : ℝ) * ((cZero D ((i : ℕ) + 1) : ℤ) + 4 * D.R.r) ≤ 26 * L.sc.b := by
      have := mul_le_mul_of_nonneg_left c1 (by linarith : (0 : ℝ) ≤ D.R.r)
      nlinarith
    obtain ⟨τ⟩ : Nonempty (Psi p.T.Q.H) := by
      rw [← Fintype.card_pos_iff, ← Nat.card_eq_fintype_card, hw.card]; omega
    have w1 : L.sc.w'' D.R.n ≤ 8 * L.sc.b := by
      have h1 := hw.low τ
      have h2 : (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) ≤ 4 * L.sc.b := by
        unfold anchor
        split_ifs
        · exact (le_abs_self _).trans (hw.up τ _)
        · push_cast; linarith
      linarith
    have s1 : (D.R.r : ℝ) * S ≤ 800 * L.sc.b := by
      have h1 : (D.R.r : ℝ) * S ≤ PP * S := mul_le_mul_of_nonneg_right (by linarith) hS
      nlinarith [mul_nonneg (by linarith : 0 ≤ PP) he]
    have bm : L.sc.b ≤ D.R.m * L.sc.b := le_mul_of_one_le_left hb.le hm
    have t2 : (D.R.f : ℝ) * ((D.R.r * S + D.R.m * (2 * (4 * L.sc.b))) + D.R.r * ((cZero D ((i : ℕ) + 1) : ℤ) + 4 * D.R.r)) ≤
        D.R.f * (834 * (D.R.m * L.sc.b)) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have t3 : (lenT p i PP : ℝ) * GlobalTheory.MeanTop.l1 u1 ≤ 834 * (D.R.f * D.R.m * L.sc.b) := by nlinarith
    have u0 : (D.R.f : ℝ) * D.R.m * L.sc.b ≤ unitE p := by
      rw [hw.unit]
      have hL := h.big.2.1
      have hll := h.big.2.2.2
      have a0 : 0 ≤ (D.R.f : ℝ) * D.R.m * L.sc.b := by positivity
      have a1 : (D.R.f : ℝ) * D.R.m * L.sc.b ≤ D.R.f * D.R.m * L.sc.b * L.sc.L :=
        le_mul_of_one_le_right a0 (by linarith)
      have a2 : 0 ≤ (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L := le_trans a0 a1
      exact a1.trans (le_mul_of_one_le_right a2 hll)
    show (lenT p i PP : ℝ) * GlobalTheory.MeanTop.l1 u1 ≤ 834 * unitE p
    linarith
  · intro τ a b hab
    obtain ⟨g1, g2, -⟩ := GlobalTheory.MeanTop.divided_gaps _ _ _ hW hD τ a b hab
    have hT1 : 4 * dimFlag (dat p i) + 4 ≤ lenT p i PP := hW.h1
    change ((b : ℕ) ≠ (dat p i).p → (lenT p i PP : ℤ) + dimFlag (dat p i) + 2 + 2 * ((dat p i).p + (dat p i).q : ℕ) ≤ u1 τ a - u1 τ b) at g1
    change ((b : ℕ) = (dat p i).p → h0 ≤ 2 * (lenT p i PP : ℤ) * (u1 τ a - u1 τ b) ∧ _) at g2
    by_cases hb : (b : ℕ) = (dat p i).p
    · have k := (g2 hb).1
      have hT0 : (1 : ℤ) ≤ lenT p i PP := by exact_mod_cast (by omega : 1 ≤ lenT p i PP)
      nlinarith
    · have k := g1 hb
      have : (0 : ℤ) ≤ (dimFlag (dat p i) : ℤ) + 2 + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by positivity
      linarith

end Point

end GlobalTheory.CovHt.DividedNum
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.exists_normalised_blowup_cyclotomicAway_projective : ∀ (n : ℕ) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)), IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ (J : Z.IdealSheafData) (W : Z.Opens), Dense (W : Set Z) → (∀ x ∈ J.support, x ∉ W) → ∃ (S : Scheme.{0}) (π : S ⟶ Z) (BD : EffCartierData S), IsNormBl π J ∧ IsProjOver (π ≫ z) ∧ BD.idealSheaf = J.comap π ∧ IsIso (π ∣_ W) ∧ Dense (π ⁻¹' W : Set S) := by
  first | exact @GlobalTheory.NormBlowupInt.exists_normBl | exact GlobalTheory.NormBlowupInt.exists_normBl | (intros; apply GlobalTheory.NormBlowupInt.exists_normBl <;> assumption)
end
