module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle683
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionZeroCase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvTEqTerm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2642
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle005
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecSnc

open GlobalTheory.ShFam (LiesIn ev_eq_zero_iff isOpen_not_liesIn)

section Local

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem eventually_ev_eq (x : CxPts p σ) {U V : X.Opens} (hU : x.1 (IsLocalRing.closedPoint ℂ) ∈ U)
    (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V) (f : Γ(X, U)) (g : Γ(X, V))
    (h : X.presheaf.germ U _ hU f = X.presheaf.germ V _ hV g) :
    ∀ᶠ y in 𝓝 x, ev p σ U f y = ev p σ V g y := by
  obtain ⟨W, hW, iU, iV, he⟩ := TopCat.Presheaf.germ_eq X.presheaf _ hU hV f g h
  have hWU : W ≤ U := leOfHom iU
  have hWV : W ≤ V := leOfHom iV
  have hres : resG X hWU f = resG X hWV g := he
  refine Filter.eventually_of_mem ((isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)) fun z hz => ?_
  rw [← ev_res hWU hz, ← ev_res hWV hz, hres]

theorem eventually_ev_ne_zero (x : CxPts p σ) {V : X.Opens} (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V)
    (g : Γ(X, V)) (h : IsUnit (X.presheaf.germ V _ hV g)) : ∀ᶠ y in 𝓝 x, ev p σ V g y ≠ 0 := by
  have hx : x ∈ ptsIn p σ (X.basicOpen g) := mem_ptsIn.2 ((X.mem_basicOpen g _ hV).2 h)
  refine Filter.eventually_of_mem ((isOpen_ptsIn _).mem_nhds hx) fun z hz => ?_
  exact (mem_ptsIn_basicOpen (ptsIn_mono (X.basicOpen_le g) hz) g).1 hz

theorem eventually_ev_eq_zero_iff [IsLocallyNoetherian X] (x : CxPts p σ) (V : X.affineOpens)
    (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V.1) (g : Γ(X, V.1)) (C : Closeds X)
    (h : FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal C) (x.1 (IsLocalRing.closedPoint ℂ)) =
      Ideal.span {X.presheaf.germ V.1 _ hV g}) :
    ∀ᶠ y in 𝓝 x, (ev p σ V.1 g y = 0 ↔ LiesIn y C) := by
  rw [WMult.stalkId_eq_map_germ _ _ V hV] at h
  obtain ⟨s, hs, H⟩ := GlobalTheory.IdealSpread.ideal_eq_span_of_germ X _ V _ hV g
    (IsLocallyNoetherian.component_noetherian V) h
  refine Filter.eventually_of_mem ((isOpen_ptsIn _).mem_nhds (mem_ptsIn.2 hs)) fun z hz => ?_
  rw [← ev_res (X.basicOpen_le s) hz]
  exact ev_eq_zero_iff (V := X.affineBasicOpen s) (H s le_rfl) hz

theorem mem_range_ptMap_closι (z : X) (y : CxPts p σ) :
    y ∈ Set.range (ptMap (closι z) rfl σ) ↔ LiesIn y (Closeds.closure {z}) := by
  have hr : Set.range (closι z) = (Closeds.closure {z} : Closeds X) :=
    (Scheme.IdealSheafData.range_subschemeι _).trans (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  constructor
  · rintro ⟨w, rfl⟩
    have : closι z (w.1 (IsLocalRing.closedPoint ℂ)) ∈ Set.range (closι z) := ⟨_, rfl⟩
    rw [hr] at this
    exact this
  · intro hy
    have : IsReduced (Sp ℂ) := inferInstanceAs (IsReduced (Spec _))
    have hle : Set.range y.1 ⊆ Set.range (closι z) := by
      rintro _ ⟨a, rfl⟩
      have ha : a = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
      rw [hr, ha]
      exact hy
    have hk : (closι z).ker ≤ y.1.ker := ker_le_ker_of_range_subset_of_isReduced (closι z) y.1 hle
    have hl := IsClosedImmersion.lift_fac (closι z) y.1 hk
    exact ⟨⟨IsClosedImmersion.lift (closι z) y.1 hk, by rw [← Category.assoc, hl, y.2]⟩, Subtype.ext hl⟩

end Local

theorem exists_compatChart {F : Type} [Field F] {X : Scheme.{0}} {p : X ⟶ Sp F} {σ : F →+* ℂ} {D : ℕ}
    [SmoothOfRelativeDimension D p] {A : FinHolAtlas D (CxPts p σ)} (hA : IsAlgAtlas A) (x : CxPts p σ)
    {N : Set (CxPts p σ)} (hN : N ∈ 𝓝 x) (V : X.affineOpens) (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V.1) {n : ℕ}
    (G : Fin n → Γ(X, V.1))
    (hR : FinalTheorems.Rsp (X.presheaf.stalk (x.1 (IsLocalRing.closedPoint ℂ))) n (fun j => X.presheaf.germ V.1 _ hV (G j))) :
    ∃ (hn : n ≤ D) (ψ : OpenPartialHomeomorph (CxPts p σ) (Fin D → ℂ)), IsCompatChart A ψ ∧ x ∈ ψ.source ∧
      ψ.source ⊆ N ∧ ψ.source ⊆ ptsIn p σ V.1 ∧
      ∀ y ∈ ψ.source, ∀ j, ψ y (Fin.castLE hn j) = ev p σ V.1 (G j) y := by
  haveI : CharZero F := σ.charZero
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := D) (p := p) (σ := σ) x
  have hli := SncChart.linearIndependent_fderiv_params F X p D σ c x hc V hV n G hR
  have hxV : x ∈ ptsIn p σ V.1 := mem_ptsIn.2 hV
  have h0 : ∀ i, ev p σ V.1 (G i) x = 0 := by
    intro i
    by_contra hne
    have hb := mem_ptsIn.1 ((mem_ptsIn_basicOpen hxV (G i)).2 hne)
    rw [Scheme.mem_basicOpen _ _ _ hV] at hb
    have hmem : X.presheaf.germ V.1 _ hV (G i) ∈ IsLocalRing.maximalIdeal _ := by
      rw [← hR.1]; exact Ideal.subset_span ⟨i, rfl⟩
    exact hmem hb
  have hn : n ≤ D := by
    have := hli.fintype_card_le_finrank
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ReciprocityTheory.L2DbarEstimates.V D) (F' := ℂ)).finrank_eq,
      Module.finrank_linearMap, Module.finrank_self, _root_.mul_one] at this
    simpa [ReciprocityTheory.L2DbarEstimates.V] using this
  obtain ⟨e, hx0, hsub, -, hhol, hsymm, hev⟩ :=
    SncChart.exists_chart_of_fderiv F X p D σ c x hc V.1 hxV n G h0 hli
  obtain ⟨O, hON, hO, hxO⟩ := mem_nhds_iff.1 hN
  let ψ := e.restrOpen O hO
  have hψs : ψ.source = e.source ∩ O := e.restrOpen_source O hO
  refine ⟨hn, ψ, ?_, hψs ▸ ⟨hx0, hxO⟩, fun y hy => hON (hψs ▸ hy).2, fun y hy => hsub (hψs ▸ hy).1,
    fun y hy j => hev y (hψs ▸ hy).1 (Fin.castLE hn j) j.2⟩
  refine GlobalTheory.DivSec.isCompatChart_of_holAlong F X p σ D A hA ψ (fun j => ?_) ?_
  · intro V _ _ _ B' y hB' hy hm
    exact hhol j V B' y hB' hy (fun b hb => (hψs ▸ hm hb).1)
  · exact GlobalTheory.LocLift.isHolTo_mono hsymm ψ.open_target fun z hz => hz.1

theorem isSNC_locSec : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ (A : FinHolAtlas D (CxPts p σ)), IsAlgAtlas A → ∀ (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (r : ℕ) (z : Fin r → X), Function.Injective z → (∀ a, Order.coheight (z a) = 1) → ((nonzeroLocus s : Set X)ᶜ = ⋃ a, closure {z a}) → (∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x) → IsSNC A M.φ.locPot (M.φ.locSec (secVal p σ s)) (fun a => ((divOfSec M.φ.isLB s hs).mult (z a)).toNat) (fun a => Set.range (ptMap (closι (z a)) rfl σ)) := by
  intro F _ X _ _ p σ D _ hsm A hA M s hs r z hz hco hzero hsnc x
  classical
  haveI := hsm
  have hxi := mem_pick (p := p) (σ := σ) M.φ.isLB x
  have hi := mem_ptsIn.1 hxi
  obtain ⟨n, g, e, u, inst, hR, hI, hf⟩ :=
    GlobalTheory.SncForm.germ_eq_unit_mul_monomial X M.B M.φ.isLB s hs r z hz hco hzero _ (hsnc _) (pick M.φ.isLB x) hi
  obtain ⟨V, hV, G', hG'⟩ := GlobalTheory.DivSec.exists_affine_germ_eq X (x.1 (IsLocalRing.closedPoint ℂ)) (n + 1)
    (Fin.cons (u : X.presheaf.stalk _) g)
  let G : Fin n → Γ(X, V.1) := fun j => G' j.succ
  have hG : ∀ j, X.presheaf.germ V.1 _ hV (G j) = g j := fun j => hG' j.succ
  have hU : X.presheaf.germ V.1 _ hV (G' 0) = u := hG' 0
  have e1 := eventually_ev_eq x hi hV (s.f (pick M.φ.isLB x))
    (G' 0 * ∏ a, G (e a) ^ ((divOfSec M.φ.isLB s hs).mult (z a.1)).toNat) (by
      rw [hf, map_mul, map_prod, hU]
      simp only [map_pow, hG])
  have e2 := eventually_ev_ne_zero x hV (G' 0) (hU ▸ u.isUnit)
  have e3 := Filter.eventually_all.2 fun a => eventually_ev_eq_zero_iff x V hV (G (e a)) _ (by rw [hG]; exact hI a)
  have e4 : ∀ᶠ y in 𝓝 x, ∀ a, ¬ LiesIn x (Closeds.closure {z a}) → ¬ LiesIn y (Closeds.closure {z a}) :=
    Filter.eventually_all.2 fun a => by
      by_cases h : LiesIn x (Closeds.closure {z a})
      · exact Filter.Eventually.of_forall fun _ h' => absurd h h'
      · exact Filter.eventually_of_mem ((isOpen_not_liesIn _).mem_nhds h) fun y hy _ => hy
  have e5 : ∀ᶠ y in 𝓝 x, y ∈ M.φ.locPot.U x := (M.φ.locPot.isOpen_U x).mem_nhds (M.φ.locPot.mem_U x)
  obtain ⟨hn, ψ, hψ, hxψ, hN, hψV, hev⟩ := exists_compatChart hA x (e1.and (e2.and (e3.and (e4.and e5)))) V hV G
    (by rw [funext hG]; exact hR)
  let τ : Fin r → Option (Fin D) := fun a =>
    if h : x.1 (IsLocalRing.closedPoint ℂ) ∈ Closeds.closure {z a} then some (Fin.castLE hn (e ⟨a, h⟩)) else none
  refine ⟨ψ, hψ, hxψ, fun y hy => (hN hy).2.2.2.2, τ, ?_, ?_, ev p σ V.1 (G' 0), ?_, fun y hy => (hN hy).2.1, ?_⟩
  · intro a a' i h1 h2
    simp only [τ] at h1 h2
    split_ifs at h1 h2 with ha ha'
    have := Fin.castLE_injective hn ((Option.some.inj h1).trans (Option.some.inj h2).symm)
    exact congrArg Subtype.val (e.injective this)
  · intro a
    ext y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_range_ptMap_closι]
    refine and_comm.trans (and_congr_right fun hy => ?_)
    by_cases h : x.1 (IsLocalRing.closedPoint ℂ) ∈ Closeds.closure {z a}
    · simp only [τ, dif_pos h, Option.some.injEq, exists_eq_left', hev y hy]
      exact ((hN hy).2.2.1 ⟨a, h⟩).symm
    · simp only [τ, dif_neg h, reduceCtorEq, false_and, exists_false, iff_false]
      exact (hN hy).2.2.2.1 a h
  · exact (hA.holoOn_iff hA.anRead ψ.open_source).2 ((hA.anRead.holoOn_ev V.1 (G' 0)).mono hψV)
  · intro y hy
    refine (hN hy).1.trans ?_
    rw [ev_mul, ev_eq (hψV hy) (∏ _, _), map_prod,
      ← Fintype.prod_subtype_mul_prod_subtype (fun a => x.1 (IsLocalRing.closedPoint ℂ) ∈ Closeds.closure {z a})]
    congr 1
    rw [Finset.prod_eq_one (s := Finset.univ)
      (f := fun a : {a // ¬ x.1 (IsLocalRing.closedPoint ℂ) ∈ Closeds.closure {z a}} => _)
      (fun a _ => by simp only [τ, dif_neg a.2]), mul_one]
    refine Finset.prod_congr (by ext; simp) fun a _ => ?_
    simp only [τ, dif_pos a.2, map_pow, hev y hy, ev_eq (hψV hy)]

end GlobalTheory.SecSnc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.ArchProof

theorem coset_series {X : Type} [AddCommGroup X] [Module.Free ℤ X] {m : ℕ} (hm : 1 ≤ m) (y : X) (A B : X → ℂ)
    (h1 : ∀ χ, A (y + m • χ) = B χ) (h0 : ∀ α, (∀ χ, α ≠ y + m • χ) → A α = 0) (hB : Summable fun χ => ‖B χ‖) :
    (Summable fun α => ‖A α‖) ∧ ∑' α, A α = ∑' χ, B χ := by
  have hi : Function.Injective fun χ : X => y + m • χ := fun a b h => by
    have e : (m : ℤ) • a = (m : ℤ) • b := by simpa only [natCast_zsmul] using add_left_cancel h
    exact smul_right_injective X (by omega : (m : ℤ) ≠ 0) e
  have hz : ∀ α ∉ Set.range fun χ : X => y + m • χ, A α = 0 := fun α hα => h0 α fun χ e => hα ⟨χ, e.symm⟩
  refine ⟨(hi.summable_iff (f := fun α => ‖A α‖) fun α hα => by rw [hz α hα, norm_zero]).1 ?_, ?_⟩
  · simpa only [Function.comp_def, h1] using hB
  · rw [← hi.tsum_eq (f := A) fun α hα => by_contra fun h => hα (hz α h)]
    simp only [h1]

theorem exists_log (T : ℝ) (u : ℂ) (hu : u ≠ 0) (h : ‖u‖ < Real.exp (-(2 * Real.pi * T))) :
    ∃ w : ℂ, T < w.im ∧ Complex.exp ((2 * Real.pi * Complex.I : ℂ) * w) = u := by
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have e : Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (Complex.log u / (2 * Real.pi * Complex.I))) = u := by
    rw [mul_div_cancel₀ _ hne, Complex.exp_log hu]
  refine ⟨_, ?_, e⟩
  rw [← e, Complex.norm_exp, Real.exp_lt_exp] at h
  generalize Complex.log u / (2 * Real.pi * Complex.I) = w at h ⊢
  have : ((2 * Real.pi * Complex.I : ℂ) * w).re = -(2 * Real.pi * w.im) := by simp
  rw [this] at h
  have := Real.pi_pos
  nlinarith

theorem exists_cd (κ : Rule) (hκ : Rule4 κ) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {D : DegPre R} (h1 : D.PsiEven) (h2 : D.TauBimult) [Algebra (FractionRing R) ℂ] {N : NumD ℂ} (ν : NumOf D ℂ N)
    {r : ℕ} (bX : Module.Basis (Fin r) ℤ N.X) :
    ∃ (d : CD N D.P.g r bX) (_ : Geo ν d.toAB), KeyOK κ ν d.toAB := by
  have : ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), KeyOK κ ν d := by
    rcases Nat.eq_zero_or_pos D.P.g with h | h
    · exact GlobalTheory.MBLow.DimZero.main κ R D h1 h2 N ν h
    · exact GlobalTheory.T.exists_classicalThetaDescription_abelianPart κ hκ R D h1 h2 N ν h
  obtain ⟨e, G, hK⟩ := this
  obtain ⟨d, rfl⟩ := GlobalTheory.MBLow.Cl.PsiFrame.exists_cd N D.P.g r bX e (GlobalTheory.MBLow.Cl.cub_of_geo R D h1 h2 N ν _ e ⟨G⟩) (GlobalTheory.MBLow.Cl.sym_of_geo R D h1 h2 N ν _ e ⟨G⟩)
  exact ⟨d, G, hK⟩

theorem exists_vec (κ : Rule) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {D : DegPre R} (h1 : D.PsiEven) (h2 : D.TauBimult) [Algebra (FractionRing R) ℂ] {N : NumD ℂ} (ν : NumOf D ℂ N)
    {g r : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N D.P.g r bX) (G : Geo ν d.toAB) (hK : KeyOK κ ν d.toAB)
    (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r) (gm : Fin g → GtPt D (TE R ℂ))
    (hA : Adapted ν vB bX σ gm) (k₀ : ℂ) (hk : BKey κ ν vB k₀) :
    ∃ (Mx : Matrix (Fin g) (Fin g) ℂ) (c₀ : Fin g → ℂ), Mx.det ≠ 0 ∧ k₀ * d.c ^ 8 = Mx.det ^ 4 ∧
      ∀ j (k : ℕ) (s : Fam D ℂ k) (f : N.X → N.A → ℂ) (α : N.X) (F : (Fin g → ℂ) → ℂ), ν.FamV s f → Differentiable ℂ F →
        (∀ Y h, d.IsPt σ Y h → f α h.b * h.s α = (d.fr (zP σ Y) : ℂ) ^ k * F Y) →
        (jc ν s (gm j) α).fst / ν.rg ^ k = F 0 ∧ (jc ν s (gm j) α).snd / ν.rg ^ k =
          fderiv ℂ F 0 ((2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) + k * c₀ j * F 0 := by
  obtain ⟨hb, ho, hl, hr⟩ := hA
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hW : ∀ j, ∃ W, IsD ν d.toAB W (gm j).b ∧ ∀ l, j = σ.symm (Sum.inr l) → W = 0 := by
    intro j
    by_cases h : ∃ l, j = σ.symm (Sum.inr l)
    · obtain ⟨l, rfl⟩ := h
      exact ⟨0, by rw [(hr l).1]; exact GlobalTheory.MBLow.Cl.DZero.isD_zero R D h1 h2 N ν _ d.toAB, fun _ _ => rfl⟩
    · obtain ⟨o, hz, hp⟩ := ho j
      obtain ⟨W, hW⟩ := G.dif (gm j).b (hp.1.symm.trans (congrArg (·.left) hz.1))
      exact ⟨W, hW, fun l e => absurd ⟨l, e⟩ h⟩
  choose W hW hW0 using hW
  choose Z c₀ hZ hT hJ using fun j => GlobalTheory.MBLow.Cl.jet_family_deriv R D h1 h2 N ν _ r g bX d σ G (gm j) (W j) (ho j) (hW j)
  have hs : ∀ {n : ℕ} (v : Fin n → ℂ), (2 * Real.pi * Complex.I : ℂ)⁻¹ • (2 * Real.pi * Complex.I : ℂ) • v = v :=
    fun v => inv_smul_smul₀ hne v
  let Mx : Matrix (Fin g) (Fin g) ℂ := fun j => (2 * Real.pi * Complex.I : ℂ) • Z j
  let MB : Matrix (Fin D.P.g) (Fin D.P.g) ℂ := fun i => (2 * Real.pi * Complex.I : ℂ) • W (σ.symm (Sum.inl i))
  have hdet : Mx.det = MB.det := by
    refine GlobalTheory.MBLow.Cl.det_eq_det_block _ r g σ Mx MB (fun i => ?_) fun l => ⟨?_, ?_⟩
    · exact congrArg (fun v => (2 * Real.pi * Complex.I : ℂ) • v) (hZ (σ.symm (Sum.inl i)))
    · have := congrArg (fun v => (2 * Real.pi * Complex.I : ℂ) • v) ((hZ (σ.symm (Sum.inr l))).trans (hW0 _ l rfl))
      simp only [smul_zero] at this
      exact this
    · funext l'
      have e := congrArg TrivSqZeroExt.snd (((hT _ (hW0 _ l rfl) (bX l')).symm).trans ((hr l).2 (bX l')))
      have hc : co bX (bX l') = Pi.single l' 1 := by
        funext i
        by_cases hi : i = l' <;> simp [co, hi, Finsupp.single_apply, eq_comm]
      rw [hc, single_one_dotProduct] at e
      simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_one, TrivSqZeroExt.snd_inr, zero_add, Module.Basis.repr_self] at e
      refine e.trans ?_
      by_cases hi : l' = l <;> simp [hi, Finsupp.single_apply]
  obtain ⟨hd, hv⟩ := hK vB (fun i => (gm (σ.symm (Sum.inl i))).b) MB k₀ hb hl (fun i => by
    change IsD ν d.toAB ((2 * Real.pi * Complex.I : ℂ)⁻¹ • (2 * Real.pi * Complex.I : ℂ) • W (σ.symm (Sum.inl i))) _
    rw [hs]; exact hW _) hk
  refine ⟨Mx, c₀, hdet ▸ hd, hdet ▸ hv, fun j k s f α F hs' hF hY => ?_⟩
  have : (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j = Z j := hs _
  rw [this]
  exact hJ j k s f α F hs' hF hY

theorem arch_of_rule4 : ∀ κ : Rule, Rule4 κ → Arch κ := by
  intro κ hκ R _ _ _ _ D h1 h2 _ N ν g r m k hg hm hmk β ζ q hq s hs vB bX σ gm hA k₀ hk
  have hm1 : 1 ≤ m := hm.pos
  obtain ⟨d, G, hK⟩ := exists_cd κ hκ h1 h2 ν bX
  obtain ⟨Mx, c₀, hdet, hval, hJ⟩ := exists_vec κ h1 h2 ν d G hK vB σ gm hA k₀ hk
  obtain ⟨M, Nn, hrep, hlab⟩ := GlobalTheory.MBLow.Cl.exists_integral_labels N _ r g bX d σ (m ^ 2) (by positivity) ζ q hq
  obtain ⟨T, hT⟩ := GlobalTheory.MBLow.Cl.BlockPos.full_posDef N _ r g bX d σ k β
  obtain ⟨hdiff, htw⟩ := GlobalTheory.MBLow.Cl.term_smul_bmat N _ r g bX d σ
  refine ⟨Real.exp (-(2 * Real.pi * T)), Real.exp_pos _, fun u hu0 hu => ?_⟩
  obtain ⟨w, hw, hwu⟩ := exists_log T u hu0 hu
  obtain ⟨hS, hsym, hpos⟩ := hT w hw
  set S := w • bmat bX β with hSdef
  set V : Fin g → Fin g → ℂ := fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j with hV
  have key : ∀ a j,
      ((Summable fun α => ‖(jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
        ∑' α, (jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat =
          d.c * trF (d.full σ S) (d.aF σ) (d.bF σ) m (M a) (Nn a) 0) ∧
      (Summable fun α => ‖(jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
        ∑' α, (jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat =
          d.c * fderiv ℂ (trF (d.full σ S) (d.aF σ) (d.bF σ) m (M a) (Nn a)) 0 (V j) +
            ((m ^ 2 : ℕ) * c₀ j) * (d.c * trF (d.full σ S) (d.aF σ) (d.bF σ) m (M a) (Nn a) 0) := by
    intro a j
    obtain ⟨f, hf, hf1, hf0⟩ := hs a
    rw [(hrep a).1] at hf1 hf0
    set y := ∑ l, tP σ (Nn a) l • bX l with hy
    obtain ⟨s1, s2, t1, t2⟩ := GlobalTheory.MBLow.Cl.term_sum_and_fderiv N _ r g bX d σ S hS hpos m (M a) (Nn a) (V j)
    have on : ∀ χ, _ := fun χ => hJ j _ (s a) f (y + m • χ) (fun Y => d.c * d.term σ 0 m (M a) (Nn a) χ Y) hf
      ((hdiff _ _ _ _ _).const_mul _) fun Y h hY => by
        rw [hf1, GlobalTheory.MBLow.Cl.evT_eq_term N _ r g bX d σ m hm (M a) (Nn a) (q a) (hrep a) Y h hY χ]; ring
    have off : ∀ α, (∀ χ, α ≠ y + m • χ) → _ := fun α hα => hJ j _ (s a) f α (fun _ => 0) hf
      (differentiable_const _) fun Y h hY => by rw [hf0 α hα]; simp
    have tw : ∀ χ, d.term σ S m (M a) (Nn a) χ = fun Z => d.term σ 0 m (M a) (Nn a) χ Z *
        u ^ (β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2)).toNat := fun χ => funext fun Z => by
      rw [← hwu]; exact htw k m β hm1 hmk w (M a) (Nn a) χ Z
    have A := coset_series hm1 y
      (fun α => (jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat)
      (fun χ => d.c * d.term σ S m (M a) (Nn a) χ 0)
      (fun χ => by simp only [(on χ).1, tw χ]; ring) (fun α hα => by simp only [(off α hα).1, zero_mul])
      (by simpa only [norm_mul] using s1.mul_left ‖d.c‖)
    have B := coset_series hm1 y
      (fun α => (jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat)
      (fun χ => d.c * fderiv ℂ (d.term σ S m (M a) (Nn a) χ) 0 (V j) +
        ((m ^ 2 : ℕ) * c₀ j) * (d.c * d.term σ S m (M a) (Nn a) χ 0))
      (fun χ => by
        simp only [(on χ).2, tw χ]
        rw [fderiv_const_mul (hdiff _ _ _ _ _ _), fderiv_mul_const (hdiff _ _ _ _ _ _)]
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hV]
        ring)
      (fun α hα => by simp [(off α hα).2])
      (((s2.of_norm.mul_left d.c).add ((s1.of_norm.mul_left d.c).mul_left _)).norm)
    refine ⟨⟨A.1, ?_⟩, B.1, ?_⟩
    · rw [A.2, tsum_mul_left, t1]
    · rw [B.2, (s2.of_norm.mul_left d.c).tsum_add ((s1.of_norm.mul_left d.c).mul_left _), tsum_mul_left, tsum_mul_left,
        tsum_mul_left, t1, t2]
  have hrg : ν.rg ^ (m ^ 2) ≠ 0 := pow_ne_zero _ (GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν)
  have hmul : ∀ (x v : N.X → ℂ), (Summable fun α => ‖x α / ν.rg ^ (m ^ 2) * v α‖) → Summable fun α => ‖x α * v α‖ := by
    intro x v h
    refine (h.mul_left ‖ν.rg ^ (m ^ 2)‖).congr fun α => ?_
    rw [← norm_mul, ← _root_.mul_assoc, mul_div_cancel₀ _ hrg]
  refine ⟨fun a j => ⟨hmul _ _ (key a j).1.1, hmul _ _ (key a j).2.1⟩, ?_⟩
  have ha : Half (d.aF σ) := fun i => by
    unfold CD.aF
    rcases σ i with i | i
    · exact d.ha i
    · exact Or.inl rfl
  have hb : Half (d.bF σ) := fun i => by
    unfold CD.bF
    rcases σ i with i | i
    · exact d.hb i
    · exact d.hb2 i
  obtain ⟨x₀, hg₀, U, hNF⟩ := GlobalTheory.MBLow.Cl.exists_keyIn_nf g (d.full σ S) (d.aF σ) (d.bF σ) d.c Mx hg hsym hpos ha hb d.hc hdet
  obtain ⟨lev, hlev⟩ := GlobalTheory.MBLow.LabelLevel.exists_level_of_labels g x₀ hg₀ U _ _ _ _ _ hNF (m ^ 2) (by positivity) ζ hq.1 M Nn hlab
  refine ⟨x₀, hg₀, lev, fun a => d.c * trF (d.full σ S) (d.aF σ) (d.bF σ) m (M a) (Nn a) 0,
    fun a j => (key a j).1.2.symm, ?_, ?_⟩
  · simp only [fun a j => (key a j).2.2]
    exact GlobalTheory.MBLow.Cl.thJet_of_normalForm g x₀ hg₀ U _ _ _ _ _ hNF m hm _ M Nn _ (fun a => by rw [hlev a, Nat.cast_pow]) _
  · exact mul_right_cancel₀ (pow_ne_zero 8 d.hc) ((GlobalTheory.MBLow.Cl.key_value_of_nf κ hκ.1 hκ.2.2.1 g x₀ hg₀ U _ _ _ _ Mx hNF).2.trans hval.symm)

end GlobalTheory.MBLow.ArchProof

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.UMin.UnifPolFib

theorem polFib_of_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (t' : SAB H (Sp V)), Nonempty (SABMap t' t χ) → Nonempty (PELUnif (IsLocalRing.maximalIdeal V) t') → ∃ g : ℕ, ∀ (R : Type) [CommRing R] (e : FractionRing V →+* R), PolFib t.G t.PP.L g (spMap e ≫ jK V ≫ χ) := by
  intro E _ _ _ H S t V _ _ _ _ χ t' ⟨hm⟩ ⟨P⟩
  refine ⟨P.A.g, fun R _ e => ?_⟩
  have hL : t.PP.L.IsLB := RigLB.isLB _
  have hL' : t'.PP.L.IsLB := RigLB.isLB _
  have hF : LBIso t'.PP.L (t.PP.L.pull hm.cm.F) := by
    obtain ⟨w, hw, -, -⟩ := hm.lin
    exact ⟨w, hw⟩
  have hα : IsGrpPullback P.A.A t'.G (jK V) (P.U.gen.inv.left ≫ pullback.fst t'.G.hom (jK V)) :=
    GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (jK V) t'.G P.U.gen P.U.gen_hom
  have hLα : LBIso P.A.L (t'.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t'.G.hom (jK V))) := by
    obtain ⟨w, hw⟩ := P.U.ext
    have hA := P.A.isLB
    have hB : LBIso P.A.L ((P.A.L.pull P.U.gen.hom.left).pull P.U.gen.inv.left) := by
      have e : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
        rw [← Over.comp_left, P.U.gen.inv_hom_id, Over.id_left]
      have h1 := GlobalTheory.UMin.FibMove.lbIso_pull_comp hA P.U.gen.hom.left P.U.gen.inv.left
      rw [e] at h1
      exact LBIso.trans hA (pull_isLB hA _) (pull_isLB (pull_isLB hA _) _)
        (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hA) h1
    have hLG : P.U.LG.L.IsLB := RigLB.isLB _
    have h2 := GlobalTheory.ThetaAffineGlue.lbIso_comp hA (pull_isLB hA _) hLG hB ⟨w, hw⟩
    rw [P.bundle] at h2
    exact h2
  have h0 : PolFib t'.G t'.PP.L P.A.g (jK V) := ⟨P.A, _, rfl, hα, hLα⟩
  have h1 := (GlobalTheory.UMin.FibMove.polFib_move S (Sp V) t.G t.PP.L t'.G t'.PP.L χ hm.cm.F hL hL' hm.cart hF P.A.g
    (FractionRing V) (jK V)).2 R e h0
  have h2 := (GlobalTheory.UMin.FibMove.polFib_move S (Sp V) t.G t.PP.L t'.G t'.PP.L χ hm.cm.F hL hL' hm.cart hF P.A.g
    R (spMap e ≫ jK V)).1.mp h1
  rwa [Category.assoc] at h2

end GlobalTheory.UMin.UnifPolFib
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaConstant_unique_and_linear_in_section : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S) (θ θ' : SecAt G L x) (p : Over.mk x ⟶ G) (a c c' : K), Odd m → (m : K) ≠ 0 → PolFib G L g x → SecM.ofSec G θ' = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn a) • SecM.ofSec G θ → ThG G L ρ m θ p (GlobalTheory.ZH.fn c) → (ThG G L ρ m θ' p (GlobalTheory.ZH.fn c') ↔ c' = a * c) := by
  first | exact @GlobalTheory.UMin.thG_smul_iff | exact GlobalTheory.UMin.thG_smul_iff | (intros; apply GlobalTheory.UMin.thG_smul_iff <;> assumption)
end
