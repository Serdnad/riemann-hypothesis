module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SphOff
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog HermLine IsSmoothHerm IsHorizontal divSupp multAt geoNum charOf ptsIntegral
  IsIntersectionFamily IntersectionSystem IsFullIntersectionSystem)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat RatRStatement)
open GlobalTheory.CompanionTheory.MPDict

namespace GlobalTheory.CompanionTheory.MixZ

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem dim_of_generic {X Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ X) [IsClosedImmersion j] :
    topologicalKrullDim (closure ({j (genericPoint Z)} : Set X)) = topologicalKrullDim Z := by
  have hrange : Set.range j = closure {j (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image j.continuous
    rw [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  exact topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange

theorem dim_closure_image {X Y : Scheme.{0}} (j : Y ⟶ X) [IsClosedImmersion j] (z : Y) :
    topologicalKrullDim (closure ({j z} : Set X)) = topologicalKrullDim (closure ({z} : Set Y)) := by
  obtain ⟨Z, k, _, _, rfl⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
  exact (dim_of_generic (k ≫ j)).trans (dim_of_generic k).symm

theorem isometric_restr_restr {X Z : Scheme.{0}} (N : HermLB (mpStr ℤ m n)) (i : X ⟶ MP ℤ m n) (j : Z ⟶ X) :
    ((N.restr i).restr j).Isometric (N.pull (j ≫ i) (Category.assoc _ _ _)) := by
  have hm : ∀ (c : ((N.restr i).restr j).B.ι) (x : Z), x ∈ ((N.restr i).restr j).B.U c →
      x ∈ (N.pull (j ≫ i) (Category.assoc _ _ _)).B.U (fun _ => c PUnit.unit PUnit.unit) := fun c x h =>
    (mem_pull (F := j ≫ i) (x := x)).2 ((mem_pull (F := i) (x := j x)).1 ((mem_pull (F := j) (x := x)).1 h))
  refine HermLB.isometric_of_chart (fun c _ => c PUnit.unit PUnit.unit) (fun c x h => hm c x h) (fun x c c' h h' => ?_)
    fun σ c y hy => ?_
  · have h₁ := (mem_pull (F := j) (x := x)).1 h
    have h₁' := (mem_pull (F := j) (x := x)).1 h'
    refine (gm_pull_g (N.B.pull i) j (𝟙 Z) x c c' h h').trans ?_
    refine (gm_pull_g N.B i (𝟙 Z ≫ j) x _ _ h₁ h₁').trans ?_
    refine Eq.trans ?_ (gm_pull_g N.B (j ≫ i) (𝟙 Z) x _ _ (hm c x h) (hm c' x h')).symm
    simp only [Category.assoc]
  · refine ((N.φ σ).pull_φ (j ≫ i) (Category.assoc _ _ _) _ y).trans ?_
    refine Eq.trans ?_ ((((N.φ σ).pull i rfl).pull_φ j rfl c y)).symm
    refine Eq.trans ?_ ((N.φ σ).pull_φ i rfl _ _).symm
    congr 1

theorem archInt_transport {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp ℤ} {L M : HermLB q} (iso : L.Isometric M)
    {r : L.B.ι → Z.functionFieldˣ} (hr : IsRatSec L.B r) :
    ∃ (r' : M.B.ι → Z.functionFieldˣ) (hr' : IsRatSec M.B r'), M.div hr' = L.div hr ∧
      (∀ e, M.archInt M e hr' = L.archInt L e hr) ∧
      ∀ σ, Set.EqOn (GlobalTheory.Cartier.logNorm (M.φ σ) r') (GlobalTheory.Cartier.logNorm (L.φ σ) r) (GlobalTheory.Cartier.offSupp q σ (L.div hr)) := by
  obtain ⟨r', hr', h₁, h₂⟩ := iso.exists_isRatSec hr
  refine ⟨r', hr', h₁, fun e => ?_, h₂⟩
  simp only [HermLB.archInt, h₁, iso.chernInt_eq]
  exact finsum_congr fun σ => Weight.chernInt_congr (isOpen_offSupp _).measurableSet (h₂ σ)

theorem rec_eq (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] (e : ℕ) (hZ : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) e)
    (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) (e + 1))
    (r : (N.restr i).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.restr i).B r) :
    cycVal II A (e + 1) (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, (((N.restr i).div hr).mult z : ℝ) * cycVal II A e (ptIdeal (i z)) -
        (N.restr i).archInt (N.restr i) e hr := by
  obtain ⟨f, g, hfg, hrat⟩ := h₅ m n N A hN Z i r hr
  have hcyc := h₆ m n N A hN Z i e hZ r hr f g hfg hrat (cycVal II A e)
  have hint := h₇ m n N N A A hN hN Z i e hZ hA hA r hr f g hfg hrat
  have hrr := hR _ _ (II _ (Bk n)) (hII.1 _ _) _ e (fun _ => A) A f g hP (fun _ => hA) hA hfg
  have hs : (Fin.snoc (fun _ : Fin e => A) A : Fin (e + 1) → HermLine (Bk n)) = fun _ => A := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  rw [hs] at hrr
  rw [hint, hcyc, cycVal, if_pos hP.2.2.1, hrr]
  rfl

theorem mp_var (m : ℕ) (n : Fin (m + 1) → ℕ) : GlobalTheory.IsArithVar (mpStr ℤ m n) (∑ i, n i) :=
  GlobalTheory.Amb.isArithVar_mp ℤ inferInstance m n

theorem not_horizontal_of_dim_zero (h₃ : PtDict) {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (z : X)
    (hz : topologicalKrullDim (closure ({z} : Set X)) = (0 : ℕ)) : ¬ IsHorizontal (ptIdeal (i z)) := by
  obtain ⟨Z, k, _, _, rfl⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
  have hd : topologicalKrullDim Z = (0 : ℕ) := (dim_of_generic k).symm.trans hz
  obtain ⟨-, h2, -, -⟩ := h₃ m n Z (k ≫ i) 0 hd
  intro hh
  have hc : CharZero Γ(Z, ⊤) := h2.1 hh
  exact (mp_var m n).dim_ne_zero (k ≫ i) hc (by exact_mod_cast hd)

theorem curve_eq (h₃ : PtDict) (h₄ : CodimOne) (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hPt : PtLen)
    (hC : CurveInt) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] (hZ : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) 0)
    (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) 1)
    (r : (N.restr i).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.restr i).B r) :
    cycVal II A 1 (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, (((N.restr i).div hr).mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) -
        ∑ᶠ σ, ∑ᶠ y : CxPts (i ≫ mpStr ℤ m n) σ, logNorm ((N.restr i).φ σ) r y := by
  rw [rec_eq h₅ h₆ h₇ hR II hII N A hN hA Z i 0 hZ hP r hr, (hC Z _ hZ (N.restr i) (N.restr i) r hr).2]
  refine congrArg (· - _) (finsum_congr fun z => ?_)
  by_cases hz : ((N.restr i).div hr).mult z = 0
  · simp [hz]
  have hd := h₄ Z _ 0 hZ z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)
  rw [cycVal, if_neg (not_horizontal_of_dim_zero h₃ i z hd), hPt m n Z i z hd]

theorem rec_eq' (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] {q : Z ⟶ Sp ℤ} (hq : i ≫ mpStr ℤ m n = q) (e : ℕ)
    (hZ : GlobalTheory.IsArithVar q e) (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) (e + 1))
    (r : (N.pull i hq).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.pull i hq).B r) :
    cycVal II A (e + 1) (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, (((N.pull i hq).div hr).mult z : ℝ) * cycVal II A e (ptIdeal (i z)) -
        (N.pull i hq).archInt (N.pull i hq) e hr := by
  subst hq
  exact rec_eq h₅ h₆ h₇ hR II hII N A hN hA Z i e hZ hP r hr

theorem curve_eq' (h₃ : PtDict) (h₄ : CodimOne) (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hPt : PtLen)
    (hC : CurveInt) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] {q : Z ⟶ Sp ℤ} (hq : i ≫ mpStr ℤ m n = q)
    (hZ : GlobalTheory.IsArithVar q 0) (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) 1)
    (r : (N.pull i hq).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.pull i hq).B r) :
    cycVal II A 1 (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, (((N.pull i hq).div hr).mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) -
        ∑ᶠ σ, ∑ᶠ y : CxPts q σ, logNorm ((N.pull i hq).φ σ) r y := by
  subst hq
  exact curve_eq h₃ h₄ h₅ h₆ h₇ hPt hC hR II hII N A hN hA Z i hZ hP r hr

theorem charP_of_cast {R : Type} [CommRing R] [IsDomain R] {p : ℕ} (hp : p.Prime) (h : (p : R) = 0) : CharP R p := by
  obtain ⟨ℓ, hℓ⟩ := CharP.exists R
  rcases (Nat.dvd_prime hp).1 ((CharP.cast_eq_zero_iff R ℓ p).1 h) with rfl | rfl
  · exact absurd ((Nat.cast_one (R := R)).symm.trans ((CharP.cast_eq_zero_iff R 1 1).2 dvd_rfl)) one_ne_zero
  · exact hℓ

theorem heightEq_of (h₃ : PtDict) (h₄ : CodimOne) (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hV : VertEq)
    (hPt : PtLen) (hC : CurveInt) (hR : RatRStatement) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) :
    HeightEq II := by
  intro m n N A hN hA X _ _ i _ h H z d hd
  induction d using Nat.strong_induction_on generalizing z with
  | _ d ih =>
  obtain ⟨Z, j, _, _, rfl⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
  have hZd : topologicalKrullDim Z = d := (dim_of_generic j).symm.trans hd
  have hmp := mp_var m n
  have hnoeth := hmp.isNoetherian_sub (j ≫ i)
  have hln : IsLocallyNoetherian Z := hnoeth.toIsLocallyNoetherian
  have hcomp : ∀ x, (j ≫ i) x = i (j x) := fun x => by simp
  obtain ⟨-, hp₃, hp₄, hp₅⟩ := h₃ m n Z (j ≫ i) d hZd
  simp only [hcomp] at hp₃ hp₄ hp₅
  by_cases hW : IsHorizontal (ptIdeal (i (j (genericPoint Z))))
  · have hc : CharZero Γ(Z, ⊤) := hp₃.1 hW
    have hP := hp₄ hW
    obtain ⟨r₀, hr₀⟩ := exists_isRatSec ((N.restr i).restr j).isLB
    obtain ⟨r, hr, e₁, e₂, e₃⟩ := archInt_transport (isometric_restr_restr N i j) hr₀
    cases d with
    | zero => exact absurd (by exact_mod_cast hZd) (hmp.dim_ne_zero (j ≫ i) hc)
    | succ e =>
      have hZ₀ : GlobalTheory.IsArithVar ((j ≫ i) ≫ mpStr ℤ m n) e := hmp.of_isClosedImmersion (j ≫ i) hc hZd
      have hZ : GlobalTheory.IsArithVar (j ≫ i ≫ mpStr ℤ m n) e := by
        rw [← Category.assoc]
        exact hZ₀
      rcases Nat.eq_zero_or_pos e with rfl | he
      · have hcv := curve_eq' h₃ h₄ h₅ h₆ h₇ hPt hC hR II hII N A hN hA Z (j ≫ i) (Category.assoc _ _ _) hZ
          (by simpa only [hcomp] using hP) r hr
        simp only [hcomp] at hcv
        rw [H.point Z j hc hZd r₀ hr₀, hcv, HermLB.curveDeg, e₁]
        refine congrArg _ (finsum_congr fun σ => finsum_congr fun y => (e₃ σ (mem_offSupp.2 ?_)).symm)
        rw [hZ.under_eq_genericPoint]
        exact CartierDiv.genericPoint_notMem_supp _
      · have hrc := rec_eq' h₅ h₆ h₇ hR II hII N A hN hA Z (j ≫ i) (Category.assoc _ _ _) e hZ
          (by simpa only [hcomp] using hP) r hr
        simp only [hcomp] at hrc
        rw [(H.recursion_one j hc he hZd hr₀).2, hrc, e₂, e₁]
        refine congrArg (· - _) (finsum_congr fun z' => ?_)
        by_cases hz : (((N.restr i).restr j).div hr₀).mult z' = 0
        · simp [hz]
        have hdz := h₄ Z _ e hZ z' (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)
        rw [ih e (Nat.lt_succ_self e) (j z') ((dim_closure_image j z').trans hdz)]
  · obtain ⟨hpr, hz⟩ := hp₅ hW
    have key : ∀ p : ℕ, p.Prime → ((p : ℕ) : Γ(Z, ⊤)) = 0 → h (j (genericPoint Z)) =
        (geoNum d (ptIdeal (i (j (genericPoint Z)))) (fun _ => A.a) : ℝ) * Real.log p := by
      intro p hp h0
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : CharP Γ(Z, ⊤) p := charP_of_cast hp h0
      letI : Algebra (ZMod p) Γ(Z, ⊤) := ZMod.algebra _ p
      have e₁ := H.vertical Z j (ZMod p) d hZd
      have e₂ : topSelfIntersection (ZMod p) ((N.restr i).B.pull j) d = _ := hV m n N A hN X i Z j p d hZd
      rw [e₁, e₂, Nat.card_zmod]
    rw [key _ hpr hz, cycVal, if_neg hW]

theorem heightEq_holds : PtDict → CodimOne → ExistsRat → CycleOfRat → ArchIntEq → VertEq → PtLen → CurveInt →
    RatRStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → HeightEq II :=
  fun h₃ h₄ h₅ h₆ h₇ hV hPt hC hR II hII => heightEq_of h₃ h₄ h₅ h₆ h₇ hV hPt hC hR II hII

end GlobalTheory.CompanionTheory.MixZ
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
noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.FnForm

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem evaluation_resG_apply {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    (X.evaluation V x hx).hom (resG X h s) = (X.evaluation U x (h hx)).hom s := by
  show X.residue x (X.presheaf.germ V x hx (X.presheaf.map (homOfLE h).op s)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

def chartCoord (c : ∀ k, Bk n k) (x : MP ℤ m n) (hx : x ∈ mchart c) (p : Σ k, Bk n k) :
    (MP ℤ m n).residueField x :=
  ((MP ℤ m n).evaluation (mchart c) x hx).hom
    (resG _ (mchart_le c p.1) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2))

theorem ptCoord_eq_mul_chartCoord (c : ∀ k, Bk n k) (x : MP ℤ m n) (hx : x ∈ mchart c) (p : Σ k, Bk n k) :
    ptCoord x p = ptCoord x ⟨p.1, c p.1⟩ * chartCoord c x hx p := by
  obtain ⟨k, j⟩ := p
  let P : MP ℤ m n ⟶ PSpace ℤ (n k) := prB n k
  let W₀ : (MP ℤ m n).Opens := blockChart n k (ptChart x k)
  let W₁ : (MP ℤ m n).Opens := blockChart n k (c k)
  have h₀ : W₀ ≤ P ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := le_rfl
  have h₁ : W₁ ≤ P ⁻¹ᵁ chart ℤ (n k) (c k) := le_rfl
  have hx₀ : x ∈ W₀ := mem_ptChart x k
  have hx₁ : x ∈ W₁ := mchart_le c k hx
  let V := W₀ ⊓ W₁
  have hxV : x ∈ V := ⟨hx₀, hx₁⟩
  have hV₀ : V ≤ P ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := inf_le_left.trans h₀
  have hV₁ : V ≤ P ⁻¹ᵁ chart ℤ (n k) (c k) := inf_le_right.trans h₁
  have e₀ : ∀ l : Bk n k, ptCoord x ⟨k, l⟩ =
      ((MP ℤ m n).evaluation V x hxV).hom (pullRatio P V (ptChart x k) hV₀ l) := by
    intro l
    show ((MP ℤ m n).evaluation W₀ x hx₀).hom (pullRatio P W₀ (ptChart x k) h₀ l) = _
    rw [← evaluation_resG_apply (inf_le_left : V ≤ W₀) x hxV]
    exact congrArg _ (resG_pullRatio (φ := P) (hi := h₀) inf_le_left)
  have e₁ : chartCoord c x hx ⟨k, j⟩ =
      ((MP ℤ m n).evaluation V x hxV).hom (pullRatio P V (c k) hV₁ j) := by
    show ((MP ℤ m n).evaluation (mchart c) x hx).hom (resG _ (mchart_le c k) (pullRatio P W₁ (c k) h₁ j)) = _
    rw [evaluation_resG_apply, ← evaluation_resG_apply (inf_le_right : V ≤ W₁) x hxV]
    exact congrArg _ (resG_pullRatio (φ := P) (hi := h₁) inf_le_right)
  show ptCoord x ⟨k, j⟩ = ptCoord x ⟨k, c k⟩ * chartCoord c x hx ⟨k, j⟩
  rw [e₀ j, e₀ (c k), e₁, ← map_mul]
  exact congrArg _ (pullRatio_mul_pullRatio (φ := P) (hi := hV₀) (hj := hV₁) (k := j)).symm

theorem evaluation_dehomog (c : ∀ k, Bk n k) (x : MP ℤ m n) (hx : x ∈ mchart c) (f : Pol n) :
    ((MP ℤ m n).evaluation (mchart c) x hx).hom (dehomog c f) = aeval (chartCoord c x hx) f := by
  have e : ((MP ℤ m n).evaluation (mchart c) x hx).hom.comp (dehomog c) =
      (aeval (chartCoord c x hx) : Pol n →ₐ[ℤ] _).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun p => by simp [dehomog, chartCoord])
  exact congrArg (fun φ => φ f) e

theorem aeval_ptCoord_eq_mul (c : ∀ k, Bk n k) (x : MP ℤ m n) (hx : x ∈ mchart c) {f : Pol n}
    {a : Fin (m + 1) → ℕ} (hf : IsMultiHomog f a) :
    aeval (ptCoord x) f = (∏ k, ptCoord x ⟨k, c k⟩ ^ a k) *
      ((MP ℤ m n).evaluation (mchart c) x hx).hom (dehomog c f) := by
  rw [evaluation_dehomog, ← GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse.aeval_smul hf]
  exact congrArg (fun v => aeval v f) (funext (ptCoord_eq_mul_chartCoord c x hx))

theorem fnAt_ne_zero_of_notMem_ptIdeal : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (c : ∀ k, Bk n k) (h : genericPoint X ∈ i ⁻¹ᵁ mchart c) (f : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog f a →
    f ∉ ptIdeal (i (genericPoint X)) → fnAt i c h f ≠ 0 := by
  intro m n X _ i _ c h f a hf hnot h0
  refine hnot ((mem_ptIdeal_iff_aeval_ptCoord m n _ f a hf).2 ?_)
  have hx : i (genericPoint X) ∈ mchart c := h
  have h1 : i.app (mchart c) (dehomog c f) = 0 :=
    fnOf_injective _ h (h0.trans (map_zero _).symm)
  have h2 : ((MP ℤ m n).evaluation (mchart c) _ hx).hom (dehomog c f) = 0 := by
    apply (i.residueFieldMap (genericPoint X)).hom.injective
    rw [map_zero]
    refine (Scheme.evaluation_naturality_apply i (genericPoint X) hx _).trans ?_
    rw [h1, map_zero]
  rw [aeval_ptCoord_eq_mul c _ hx hf, h2, mul_zero]

end GlobalTheory.CompanionTheory.MixZ.FnForm
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.CutOff.FinFT

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem measurableSet_boxL (L : AddSubgroup (Af E)) (hLo : IsOpen (L : Set (Af E)))
    (c : Fin k → Af E) : MeasurableSet (boxL (L : Set (Af E)) c) := by
  have e : boxL (L : Set (Af E)) c =
      Set.pi Set.univ fun i => (fun x : Af E => x - c i) ⁻¹' (L : Set (Af E)) := by
    ext f; simp [boxL, Set.mem_pi]
  rw [e]
  exact MeasurableSet.univ_pi fun i =>
    (hLo.preimage (continuous_id.sub continuous_const)).measurableSet

theorem boxL_add_single (L : AddSubgroup (Af E)) (c f : Fin k → Af E) (i : Fin k) {a : Af E}
    (ha : a ∈ L) : f + Pi.single i a ∈ boxL (L : Set (Af E)) c ↔ f ∈ boxL (L : Set (Af E)) c := by
  have hl : ∀ j, (Pi.single i a : Fin k → Af E) j ∈ L := fun j => by
    by_cases h : j = i
    · subst h; simpa using ha
    · simp [Pi.single_eq_of_ne h]
  have e : ∀ j, (f + Pi.single i a : Fin k → Af E) j - c j = (f j - c j) + (Pi.single i a : Fin k → Af E) j :=
    fun j => by simp only [Pi.add_apply]; ring
  constructor
  · intro h j
    have h1 : (f + Pi.single i a : Fin k → Af E) j - c j ∈ L := h j
    rw [e] at h1
    exact (L.add_mem_cancel_right (hl j)).1 h1
  · intro h j
    change (f + Pi.single i a : Fin k → Af E) j - c j ∈ L
    rw [e]
    exact L.add_mem (h j) (hl j)

theorem sum_add_single (f z : Fin k → Af E) (i : Fin k) (a : Af E) :
    ∑ j, (f + Pi.single i a : Fin k → Af E) j * z j = ∑ j, f j * z j + a * z i := by
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · simp

variable [_root_.NumberField.IsTotallyComplex E]

theorem box_fourier {ψ : AddChar (Ad E) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) (_hc : Continuous ψ)
    (L : AddSubgroup (Af E)) (_hLc : IsCompact (L : Set (Af E))) (hLo : IsOpen (L : Set (Af E)))
    (c z : Fin k → Af E) :
    ‖∫ f, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) *
        ψ (sFin E (∑ i, f i * z i)) ∂nuFin E k‖ ≤ (nuFin E k).real (boxL (L : Set (Af E)) c) ∧
    (∫ f, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) *
        ψ (sFin E (∑ i, f i * z i)) ∂nuFin E k ≠ 0 →
      ∀ i, ∀ a ∈ L, ψ (sFin E (a * z i)) = 1) := by
  have hm := measurableSet_boxL L hLo c
  refine ⟨?_, ?_⟩
  · refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    have e : (fun f : Fin k → Af E => ‖(((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) *
        ψ (sFin E (∑ i, f i * z i))‖) = (boxL (L : Set (Af E)) c).indicator 1 := by
      funext f
      by_cases hf : f ∈ boxL (L : Set (Af E)) c <;> simp [hf, hψ]
    rw [e, integral_indicator_one hm]
  · intro hI i a ha
    have hinv : (nuFin E k).IsAddRightInvariant := by
      unfold nuFin; infer_instance
    have key := integral_add_right_eq_self (μ := nuFin E k)
      (fun f => (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) *
        ψ (sFin E (∑ i, f i * z i))) (Pi.single i a : Fin k → Af E)
    have e : ∀ f : Fin k → Af E,
        (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) (f + Pi.single i a) : ℝ) : ℂ) *
          ψ (sFin E (∑ j, (f + Pi.single i a : Fin k → Af E) j * z j)) =
        ψ (sFin E (a * z i)) * ((((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) *
          ψ (sFin E (∑ j, f j * z j))) := fun f => by
      rw [sum_add_single, map_add (f := _), AddChar.map_add_eq_mul]
      by_cases hf : f ∈ boxL (L : Set (Af E)) c
      · rw [Set.indicator_of_mem ((boxL_add_single L c f i ha).2 hf), Set.indicator_of_mem hf]
        ring
      · rw [Set.indicator_of_notMem (fun h => hf ((boxL_add_single L c f i ha).1 h)),
          Set.indicator_of_notMem hf]
        simp
    simp only [e] at key
    rw [integral_const_mul] at key
    exact mul_right_cancel₀ hI (key.trans (one_mul _).symm)

theorem box_fourier_main : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}, (∀ x, ‖ψ x‖ = 1) → Continuous ψ → ∀ (L : AddSubgroup (Af E)), IsCompact (L : Set (Af E)) → IsOpen (L : Set (Af E)) → ∀ (c z : Fin k → Af E), ‖∫ f, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) * ψ (sFin E (∑ i, f i * z i)) ∂nuFin E k‖ ≤ (nuFin E k).real (boxL (L : Set (Af E)) c) ∧ (∫ f, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) * ψ (sFin E (∑ i, f i * z i)) ∂nuFin E k ≠ 0 → ∀ i, ∀ a ∈ L, ψ (sFin E (a * z i)) = 1) :=
  fun h1 h2 L h3 h4 c z => box_fourier h1 h2 L h3 h4 c z

end GlobalTheory.CompanionTheory.CutOff.FinFT
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.TorusCh

theorem continuous_chi {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (e : Matrix (Fin n) (Fin n) E) : Continuous (chi e : GA E n → Ad E) := by
  unfold chi
  refine Continuous.matrix_det ?_
  exact continuous_const.add (continuous_const.mul (Units.continuous_val.sub continuous_const))

theorem continuousOn_lam (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (e : Matrix (Fin n) (Fin n) E) (he : e * e = e)
    (hlog : ∀ s : (Ad E)ˣ, logAbs (s : Ad E) = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E s : ℝ))
    (H : Subgroup (GA E n)) (hH : ∀ t ∈ H, t.val * rm e = rm e * t.val) :
    ContinuousOn (lam e) (H : Set (GA E n)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let ψ : ↥(H : Set (GA E n)) → (Ad E)ˣ := fun t =>
    ⟨chi e t.1, chi e t.1⁻¹,
      by rw [← chi_mul e he _ _ (hH _ t.2), mul_inv_cancel, chi_one],
      by rw [← chi_mul e he _ _ (comm_inv (hH _ t.2)), inv_mul_cancel, chi_one]⟩
  have hψ : Continuous ψ := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (continuous_chi e).comp continuous_subtype_val
    · exact (continuous_chi e).comp (continuous_inv.comp continuous_subtype_val)
  have hm : Continuous fun t => (GroundTheory.Global.IdeleGroup.ideleModule E (ψ t) : ℝ) :=
    continuous_subtype_val.comp (GroundTheory.Global.IdeleGroup.continuous_ideleModule.comp hψ)
  have heq : (H : Set (GA E n)).domRestrict (lam e) =
      fun t : ↥(H : Set (GA E n)) => Real.log (GroundTheory.Global.IdeleGroup.ideleModule E (ψ t) : ℝ) := by
    funext t
    exact hlog (ψ t)
  rw [heq]
  exact hm.log fun t => (GroundTheory.Global.IdeleGroup.ideleModule E (ψ t)).2.ne'

end GlobalTheory.CompanionTheory.TorusCh

end
end
