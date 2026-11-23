module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle108
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1817
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle545
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle460
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle539
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle484
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle483
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle435
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle047
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle487
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle493
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroLocusRegularFunctionNullStatement
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
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MixZ.Vert

theorem key (p : ℕ) [Fact p.Prime] {m : ℕ} {n : Fin (m + 1) → ℕ} (a : Fin (m + 1) → ℤ) (d : ℕ) :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ MP ℤ m n) [IsClosedImmersion f] [Algebra (ZMod p) Γ(Z, ⊤)],
      topologicalKrullDim Z = d → ∀ (L : LB Z) (hL : L.IsLB),
      cls L hL = ∑ k, a k • cls (pullO (f ≫ prB n k) 1) (isLB_pullO _ 1) →
      topSelfIntersection (ZMod p) L d = geoNum d (ptIdeal (f (genericPoint Z))) (fun _ => a) := by
  induction d with
  | zero =>
    intro Z _ f _ _ hd L hL _
    rw [topSelf_zero]
    exact GlobalTheory.T.euler_characteristic_dimension_zero m n Z f p hd _
  | succ d ih =>
    intro Z _ f _ _ hd L hL hc
    have hp : IsProjOver (strHom (ZMod p) (X := Z)) :=
      VertProj.isProjOver_strHom_zmod ℤ _ (mpStr ℤ m n) _ (isArithVar_mpStr m n) Z f p
    have hf := algebraMap_eq_strHom (ZMod p) Z
    have : AlgebraicGeometry.IsNoetherian Z := isNoetherian_of_isProjOver hp
    have hDV := diffVanish_chiPic_of_isProjOver hf (structureModule Z) hp (d := d + 1)
      (by rw [QCoh.suppDim_structureModule, hd])
    have red : ∀ w : Z, Order.coheight w = 1 →
        interNumRed (ZMod p) (⟨closure {w}, isClosed_closure⟩ : Closeds Z) (fun _ : Fin d => L) =
          geoNum d (ptIdeal (f w)) (fun _ => a) := by
      intro w hw
      let C : Closeds Z := ⟨closure {w}, isClosed_closure⟩
      have hirr : IsIrreducible (C : Set Z) := isIrreducible_singleton.closure
      haveI := isIntegral_red hirr
      letI : Algebra (ZMod p) Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) :=
        algebraΓOfHom (redι C ≫ strHom (ZMod p) Z)
      have hfZ : ∀ r : ZMod p, (redι C).appTop (algebraMap (ZMod p) Γ(Z, ⊤) r) =
          algebraMap (ZMod p) Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) r := fun r => by
        rw [hf r]; rfl
      have hdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal C).subscheme = d := by
        rw [topologicalKrullDim_red]
        exact VdmRec.CutSec.dim_closure_of_coheight (isArithVar_mpStr m n) f hd hw
      have hcl : cls (L.pull (redι C)) (pull_isLB hL _) =
          ∑ k, a k • cls (pullO ((redι C ≫ f) ≫ prB n k) 1) (isLB_pullO _ 1) := by

        rw [cls_pull hL, hc, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_zsmul, Category.assoc, GlobalTheory.T.cls_pullO_one_comp_eq_pull (redι C) (f ≫ prB n k)]
      have e := ih _ (redι C ≫ f) hdim _ (pull_isLB hL _) hcl
      rw [interNumRed_def, interNumSub_def, interNumOn_def,
        interNum_pushforward_of_isClosedImmersion hfZ _ (fun _ => hL)]
      rw [topSelf_def] at e
      refine e.trans ?_
      rw [Scheme.Hom.comp_apply, PullVanish.redι_genericPoint w]
    have hrel := (isMultiProjPrime_ptIdeal m n (f (genericPoint Z))).2.2
    have e := hDV.interNum_update_of_cls_eq_sum (ι := Fin (d + 1)) (L := fun _ => L) (by simp) (fun _ => hL) 0
      (Finset.univ) (P := fun k => pullO (f ≫ prB n k) 1) (fun k => isLB_pullO _ 1) a hL hc
    have upd : ∀ N : LB Z, Function.update (fun _ : Fin (d + 1) => L) 0 N = Fin.cons N (fun _ : Fin d => L) := by
      intro N
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp
      · simp [Function.update_of_ne (Fin.succ_ne_zero i)]
    simp only [upd] at e
    have e0 : (Fin.cons L (fun _ : Fin d => L) : Fin (d + 1) → LB Z) = fun _ => L := by
      funext i
      refine Fin.cases rfl (fun _ => rfl) i
    rw [e0] at e
    rw [topSelf_def, e, geoNum, dite_eq_left hrel]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine congrArg (a k * ·) ?_
    have hl := (hrel k).choose_spec
    have hs := GlobalTheory.T.generic_point_nonvanishing_coordinate_section m n Z f k _ hl
    rw [GlobalTheory.CompanionTheory.Ar.IntersectionMultiplicitySection.interNum_cons_eq_finsum_mult (ZMod p) Z hp d (by rw [hd]) _ (isLB_pullO _ 1)
      (fun _ => L) (fun _ => hL) _ hs]
    refine Eq.trans (finsum_congr fun w => ?_) (GlobalTheory.T.coordinate_divisor_multiplicity_sum m n Z f k _ hs (fun W => geoNum d W (fun _ => a)))
    by_cases hw : (divOfSec (isLB_pullO _ 1) _ hs).mult w = 0
    · rw [hw, zero_mul, zero_mul]
    · rw [red w (CartierDiv.coheight_eq_one_of_mult_ne_zero hw)]

theorem vertEq : VertEq := by
  intro m n M A hA X i _ Z _ j _ p _ _ d hd
  refine key p A.a d Z (j ≫ i) hd _ (pull_isLB (pull_isLB M.isLB _) _) ?_

  rw [cls_pull (pull_isLB M.isLB _), cls_pull M.isLB, GlobalTheory.T.hermRep_class_decomposition m n M A hA, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, map_zsmul, Category.assoc, GlobalTheory.T.cls_pullO_one_comp_eq_pull, GlobalTheory.T.cls_pullO_one_comp_eq_pull]

end GlobalTheory.CompanionTheory.MixZ.Vert
end
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ

section ZeroLocus

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {X : Scheme.{0}} [IsIntegral X] {i : X ⟶ MP ℤ m n}

theorem mem_ptsIn_preimage_mchart (c : ∀ k, Bk n k) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :
    y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) ↔
      PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) := by
  rw [CxPts.mem_ptsIn, CxPts.mem_ptsIn]
  rfl

theorem ev_dehomog_eq_zero_iff (c : ∀ k, Bk n k) {f : Pol n} {a : Fin (m + 1) → ℕ} (hf : IsMultiHomog f a)
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (hy : y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c))
    {z : (Σ k, Bk n k) → ℂ} (hz : IsUnder (PtsOver.map i rfl _ y) z) :
    ev (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) (i.app _ (dehomog c f)) y = 0 ↔
      eval z (map (Int.castRingHom ℂ) f) = 0 := by
  have hw := (mem_ptsIn_preimage_mchart c y).1 hy
  have hne : ∏ k, z ⟨k, c k⟩ ^ a k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ =>
    pow_ne_zero _ ((hz k (c k)).1.1 (CxPts.ptsIn_mono (mchart_le c k) hw))
  rw [CxPts.ev_app i rfl, GlobalTheory.T.dehomogenized_eval_eq_ratio m n c f a hf _ z hz hw, div_eq_zero_iff]
  exact ⟨fun h => h.resolve_right hne, Or.inl⟩

theorem zeroLocus_eq_iUnion [IsClosedImmersion i] {f : Pol n} {a : Fin (m + 1) → ℕ} (hf : IsMultiHomog f a) :
    {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀ | ∃ z, IsUnder (PtsOver.map i rfl _ y) z ∧
      eval z (map (Int.castRingHom ℂ) f) = 0} =
    ⋃ c : ∀ k, Bk n k, {y | y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) ∧
      ev (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) (i.app _ (dehomog c f)) y = 0} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨z, hz, h0⟩
    have hc : y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀
        (i ⁻¹ᵁ mchart fun k => ptChart ((PtsOver.map i rfl _ y).1 (IsLocalRing.closedPoint ℂ)) k) :=
      (mem_ptsIn_preimage_mchart _ y).2 (CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => mem_ptChart _ k))
    exact ⟨_, hc, (ev_dehomog_eq_zero_iff _ hf y hc hz).2 h0⟩
  · rintro ⟨c, hc, h0⟩
    obtain ⟨z, -, hz⟩ := GlobalTheory.T.complex_point_lifts_to_multicone m n X i y
    exact ⟨z, hz, (ev_dehomog_eq_zero_iff c hf y hc hz).1 h0⟩

theorem measurableSet_ev_eq_zero {Y : Scheme.{0}} (q : Y ⟶ Sp ℤ) (W : Y.Opens) (g : Γ(Y, W)) :
    MeasurableSet {y : GlobalTheory.CxPts q σ₀ | y ∈ ptsIn q σ₀ W ∧ ev q σ₀ W g y = 0} := by
  have hS : IsOpen (ptsIn q σ₀ W) := isOpen_ptsIn W
  have hO : IsOpen (ptsIn q σ₀ W ∩ ev q σ₀ W g ⁻¹' {0}ᶜ) :=
    (continuousOn_ev g).isOpen_inter_preimage hS isOpen_compl_singleton
  have e : {y : GlobalTheory.CxPts q σ₀ | y ∈ ptsIn q σ₀ W ∧ ev q σ₀ W g y = 0} =
      ptsIn q σ₀ W \ (ptsIn q σ₀ W ∩ ev q σ₀ W g ⁻¹' {0}ᶜ) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff, not_and, not_not]
    exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
  rw [e]
  exact hS.measurableSet.diff hO.measurableSet

end ZeroLocus

theorem zeroLocus_measurable_null : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (f : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog f a → f ∉ ptIdeal (i (genericPoint X)) →
    MeasurableSet {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀ | ∃ z, IsUnder (PtsOver.map i rfl _ y) z ∧
      eval z (map (Int.castRingHom ℂ) f) = 0} ∧
    ∀ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, volume (c.e.target ∩ c.e.symm ⁻¹'
      {y | ∃ z, IsUnder (PtsOver.map i rfl _ y) z ∧ eval z (map (Int.castRingHom ℂ) f) = 0}) = 0 := by
  intro m n X _ i _ D f a hf hI
  rw [zeroLocus_eq_iUnion hf]
  refine ⟨MeasurableSet.iUnion fun c => measurableSet_ev_eq_zero _ _ _, fun ch => ?_⟩
  rw [Set.preimage_iUnion, Set.inter_iUnion]
  refine measure_iUnion_null fun c => ?_
  by_cases hg : genericPoint X ∈ i ⁻¹ᵁ mchart c
  · exact GlobalTheory.T.zero_locus_regular_function_null X (i ≫ mpStr ℤ m n) σ₀ D ch _ hg _ (GlobalTheory.T.restricted_form_nonzero_on_generic_point m n X i c hg f a hf hI)
  · have e : ch.e.target ∩ ch.e.symm ⁻¹' {y | y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) ∧
        ev (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) (i.app _ (dehomog c f)) y = 0} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun v hv => hg
        (((genericPoint_spec X).mem_open_set_iff (i ⁻¹ᵁ mchart c).isOpen).2
          ⟨_, trivial, CxPts.mem_ptsIn.1 hv.2.1⟩)
    rw [e, measure_empty]

end GlobalTheory.CompanionTheory.MixZ
end
