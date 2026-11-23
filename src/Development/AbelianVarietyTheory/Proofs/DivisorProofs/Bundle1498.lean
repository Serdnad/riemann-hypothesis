module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1463
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.AmpleGen

theorem exists_genAt_mul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ P : Pair p, IsAmpleLB P.A.B → ∃ c₀ : ℕ, 0 < c₀ ∧ ∀ j : ℕ, GenAt P (c₀ * j) := by
  intro k _ X _ p D _ P hA
  obtain ⟨c, hc, N, s, hs⟩ := hA.exists_isGenerated_pow
  have hrep : P.Rep 0 (c : ℤ) (P.A.pow c) := by
    have := Pair.rep_pow k X p P 0 1 P.A c (Pair.rep_base k X p P).2.1
    simpa using this
  obtain ⟨e, -, hrange, hnu, -⟩ := RepDict.rep_dict k X p P 0 c (P.A.pow c) hrep
  have hmem : ∀ i, e (s i) ∈ P.H 0 c := fun i => by
    have : e (s i) ∈ Set.range e := ⟨s i, rfl⟩
    rw [hrange] at this
    exact this
  have hne : ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ i, P.nu 0 c σ y (e (s i)) ≠ 0 := by
    intro σ y
    obtain ⟨i, hi⟩ := exists_mem_ptsIn hs y
    refine ⟨i, fun h0 => ?_⟩
    have h2 := hnu (s i) σ y
    have hpick := mem_pick ((P.A.pow c).φ σ).isLB y
    have hv := (secVal_ne_zero_iff (s i) hpick).2 hi
    have hpos : ((P.A.pow c).φ σ).nsq (secVal p σ (s i)) y ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 hv)) (Real.exp_pos _).ne'
    rw [h0] at h2
    exact hpos (by rw [← h2]; ring)
  refine ⟨c, hc, fun j => ⟨N, fun i => e (s i) ^ j, fun i => ?_, fun σ y => ?_⟩⟩
  · obtain ⟨h1, -⟩ := NuPow.pow_mem_H_and_nu_pow k X p P 0 c (e (s i)) (hmem i) j
    have e1 : (j : ℤ) * 0 = 0 := by ring
    have e2 : (j : ℤ) * c = ((c * j : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2] at h1
    exact h1
  · obtain ⟨i, hi⟩ := hne σ y
    obtain ⟨-, h2⟩ := NuPow.pow_mem_H_and_nu_pow k X p P 0 c (e (s i)) (hmem i) j
    have e1 : (j : ℤ) * 0 = 0 := by ring
    have e2 : (j : ℤ) * c = ((c * j : ℕ) : ℤ) := by push_cast; ring
    have h3 := h2 σ y
    rw [e1, e2] at h3
    exact ⟨i, by rw [h3]; exact pow_ne_zero _ hi⟩

end GlobalTheory.HSNef.AmpleGen
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem kltAt_add_smul_of_lcAt : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∀ (Δ D : X → ℚ) (δ : ℚ) (x : X), IsQCart D → KltAt p n Δ x → LcAt p n (Δ + D) x → 0 < δ →
      δ ≤ 1 → KltAt p n (Δ + (1 - δ) • D) x := by
  intro X _ _ _ p n hp hn Δ D δ x hD hk hl hδ hδ1
  obtain ⟨η, m, g, hη, hm, hg, hkl⟩ := hk
  obtain ⟨m', f, hm', -, hf⟩ := GlobalTheory.T.exists_localEquation_effectiveQCartierDivisor X p D hD x
  obtain ⟨m₁, g₁, hm₁, h₁, e₁⟩ := GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n Δ D η x m m' g f 1 hm hm' hg hf
  obtain ⟨m₂, g₂, hm₂, h₂, e₂⟩ := GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n Δ D η x m m' g f (1 - δ) hm hm' hg hf
  rw [one_smul] at h₁
  have hlc := (GlobalTheory.T.logCanonicalAt_iff_of_isLogCanonicalLocalEquation X p n hp hn (Δ + D) η x m₁ g₁ hη hm₁ h₁).1 hl
  refine ⟨η, m₂, g₂, hη, hm₂, h₂, fun E hE => ?_⟩
  have a := hkl E hE
  have b := hlc E hE
  rw [e₁] at b
  rw [e₂]
  set t : ℚ := (E.ord f : ℚ) / m'
  set d := discrep E η m g
  have h1 : -δ < δ * d := by nlinarith
  have h2 : -(1 - δ) ≤ (1 - δ) * (d - 1 * t) := by nlinarith
  nlinarith

end GlobalTheory.PairStep
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem GlobalTheory.PairStep.kltAt_lcAt_of_le_coeff : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ B : X → ℚ) (a b : ℚ) (x : X), IsQCart B → a ≤ b → (KltAt p n (Γ + b • B) x → KltAt p n (Γ + a • B) x) ∧ (LcAt p n (Γ + b • B) x → LcAt p n (Γ + a • B) x) := by
  intro X _ _ _ p n _ _ Γ B a b x hB hab
  obtain ⟨m', f, hm', hf, hBf⟩ := GlobalTheory.T.exists_localEquation_effectiveQCartierDivisor X p B hB x
  have key : ∀ (η : RatForms p n) (m : ℕ) (g : X.functionFieldˣ), 0 < m →
      IsLogEqn p (Γ + b • B) η x m g →
      ∃ (m'' : ℕ) (g'' : X.functionFieldˣ), 0 < m'' ∧ IsLogEqn p (Γ + a • B) η x m'' g'' ∧
        ∀ E : DivOver p, E.Through x → discrep E η m g ≤ discrep E η m'' g'' := by
    intro η m g hm hlog
    obtain ⟨m'', g'', hm'', hlog'', hd⟩ :=
      GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n (Γ + b • B) B η x m m' g f (a - b) hm hm' hlog hBf
    have e : Γ + b • B + (a - b) • B = Γ + a • B := by
      funext z
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e] at hlog''
    refine ⟨m'', g'', hm'', hlog'', fun E hE => ?_⟩
    have h0 : (0 : ℚ) ≤ E.ord f := by exact_mod_cast (E.ord_nonneg_iff f).2 (hE _ hf)
    have h1 : (0 : ℚ) ≤ (E.ord f : ℚ) / m' := div_nonneg h0 (Nat.cast_nonneg _)
    rw [hd E]
    nlinarith [mul_nonneg (sub_nonneg.2 hab) h1]
  refine ⟨fun ⟨η, m, g, hη, hm, hlog, hk⟩ => ?_, fun ⟨η, m, g, hη, hm, hlog, hk⟩ => ?_⟩
  · obtain ⟨m'', g'', hm'', hlog'', hle⟩ := key η m g hm hlog
    exact ⟨η, m'', g'', hη, hm'', hlog'', fun E hE => lt_of_lt_of_le (hk E hE) (hle E hE)⟩
  · obtain ⟨m'', g'', hm'', hlog'', hle⟩ := key η m g hm hlog
    exact ⟨η, m'', g'', hη, hm'', hlog'', fun E hE => le_trans (hk E hE) (hle E hE)⟩
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.Meet

theorem val_spMap_pt {F : Type} [Field F] (Y : Var F) {K : Type} [Field K] (σ : Y.Fn →+* K) (x : Y.Fn) :
    (ratOf Y).val (spMap σ ≫ (ratOf Y).pt) x = σ x := by
  have hx : x ∈ (ratOf Y).O ((ratOf Y).pt (IsLocalRing.closedPoint Y.Fn)) := by
    refine (congrArg (fun z => x ∈ (ratOf Y).O z) ((ratOf Y).pt_apply _)).mpr ?_
    rw [RatModel.O_genericPoint]; exact Algebra.mem_top
  have h := RatModel.val_spMap_comp (M := ratOf Y) σ (ratOf Y).pt specializes_rfl ⟨x, hx⟩
  rw [RatModel.valLoc_eq_val] at h
  exact h.trans (congrArg σ (RatModel.val_pt x))


open GlobalTheory.FlagBundle.ClosedPt in
theorem meet : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ A ∈ E.S (f (genericPoint Y.X)), ∀ (τ : ι) (a b : Fin (m τ)), a < b → ∀ (K : Type) [Field K] (V : ValuationSubring K) (c : Y.Fn →+* V) (t : V), IsLocalRing.residue V t = 0 → ∀ v₂ : Sp V ⟶ Y.X, v₂ ≫ f = spMap c ≫ (ratOf Y).pt ≫ f → Bears E' φ A (shear τ a b (t : K) * (B * (A.map φ)⁻¹).map ((algebraMap V K).comp c)) (spMap (algebraMap V K) ≫ v₂) → spMap (IsLocalRing.residue V) ≫ spMap c ≫ (ratOf Y).pt = spMap (IsLocalRing.residue V) ≫ v₂ := by
  intro F _ X Y ι _ m E E' φ f hf B hB A hA τ a b hab K _ V c t ht v₂ e hbear
  have hM := hf.sub _ B hB A hA
  obtain ⟨-, -, -, hsm⟩ := GlobalTheory.T.blockMatrixElementaryShear_properties ι m τ a b hab V t
  obtain ⟨-, -, hs0, -⟩ := GlobalTheory.T.blockMatrixElementaryShear_properties ι m τ a b hab (IsLocalRing.ResidueField V) 0
  have hpt : ∀ (R : Type) [CommRing R] (g : Y.Fn →+* R) (w : Sp R),
      (spMap g ≫ (ratOf Y).pt) w = genericPoint Y.X := fun R _ g w =>
    (Scheme.Hom.comp_apply _ _ _).trans ((ratOf Y).pt_apply _)
  have hf₂ : f (v₂ (IsLocalRing.closedPoint V)) = f (genericPoint Y.X) := by
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans ?_
    rw [e]
    exact (Scheme.Hom.comp_apply (spMap c ≫ (ratOf Y).pt) f _).trans (congrArg f (hpt _ c _))
  obtain ⟨A₂, hA₂⟩ := E'.nonempty (v₂ (IsLocalRing.closedPoint V))
  have hM₂ := hf.sub _ A₂ hA₂ A ((congrArg (fun z => A ∈ E.S z) hf₂).mpr hA)
  obtain ⟨A₂', hA₂', hpar⟩ := hbear
  have hA₂g : A₂ ∈ E'.S ((spMap (algebraMap V K) ≫ v₂) (IsLocalRing.closedPoint K)) :=
    Fr.mem_of_specializes hA₂ (gen_specializes v₂ _)
  have hsp₂ := gen_specializes (L := K) v₂ (IsLocalRing.closedPoint K)
  have hG := (Fr.mem_iff hA₂g).1 hA₂'
  have hM₂g : Par 0 ((ratOf Y).O ((spMap (algebraMap V K) ≫ v₂) (IsLocalRing.closedPoint K))).toSubring
      (A₂ * (A.map φ)⁻¹) :=
    hM₂.mono le_rfl fun _ hx => RatModel.O_le_of_specializes hsp₂ hx
  set ψ := RatModel.valHom (M := ratOf Y) (spMap (algebraMap V K) ≫ v₂) _
    (RatModel.range_eq_singleton _ (IsLocalRing.closedPoint K))
  have hv : ∀ x : ((ratOf Y).O ((spMap (algebraMap V K) ≫ v₂) (IsLocalRing.closedPoint K))).toSubring,
      (ratOf Y).val (spMap (algebraMap V K) ≫ v₂) x = ψ x := fun _ => rfl
  have heqM : A₂' * (A.map φ)⁻¹ = (A₂' * A₂⁻¹) * (A₂ * (A.map φ)⁻¹) := by
    rw [mul_assoc, ← mul_assoc A₂⁻¹, Mat.inv_mul (Fr.det_ne hA₂), one_mul]
  have hmap : (A₂' * (A.map φ)⁻¹).map ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) =
      (A₂' * A₂⁻¹).map ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) *
        (A₂ * (A.map φ)⁻¹).map ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) := by
    rw [heqM]
    exact Par.map_mul_of hG hM₂g ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) ψ hv
  have hGv := Par.map_of hG ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) ψ hv
  have hpar2 := hpar
  erw [hmap] at hpar2
  rw [Mat.mul_inv_rev] at hpar2
  clear hpar
  have hL := hpar2.mul hGv
  rw [mul_assoc, mul_assoc, mul_assoc, Mat.inv_mul hGv.det_ne, mul_one, ← mul_assoc] at hL
  rw [map_val (algebraMap V K) v₂ _ (fun τ a b => (hM₂ τ).1 a b)] at hL
  have hN : ∀ (S : Type) [CommRing S] (g : V →+* S),
      (shear τ a b t * (B * (A.map φ)⁻¹).map c).map g =
        shear τ a b (g t) * (B * (A.map φ)⁻¹).map (g.comp c) := fun S _ g => by
    rw [← hsm S g]
    funext σ
    exact Matrix.map_mul
  have hN1 := hN K (algebraMap V K)
  have hN2 := hN _ (IsLocalRing.residue V)
  rw [ht, hs0, one_mul] at hN2
  have hh : Par 0 ⊤ ((B * (A.map φ)⁻¹).map ((IsLocalRing.residue V).comp c)) :=
    hM.map _ fun _ _ => trivial
  have hk₂ := par_val (IsLocalRing.residue V) v₂ hM₂
  have hD := descend (L := K) (shear τ a b t * (B * (A.map φ)⁻¹).map c)
    (vals v₂ _ (fun τ a b => (hM₂ τ).1 a b)) (by rw [hN2]; exact hh.det_ne)
    (by rw [← map_val]; exact hk₂.det_ne) (by rw [hN1]; exact hL)
  rw [hN2, ← map_val] at hD
  have ec : spMap (IsLocalRing.residue V) ≫ spMap c ≫ (ratOf Y).pt =
      spMap ((IsLocalRing.residue V).comp c) ≫ (ratOf Y).pt := by
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hb₂ : Bears E' φ A ((B * (A.map φ)⁻¹).map ((IsLocalRing.residue V).comp c))
      (spMap (IsLocalRing.residue V) ≫ v₂) :=
    ⟨A₂, (congrArg (fun z => A₂ ∈ E'.S z) (closedPt_comp v₂)).mpr hA₂, hD⟩
  have hb₁ : Bears E' φ A ((B * (A.map φ)⁻¹).map ((IsLocalRing.residue V).comp c))
      (spMap ((IsLocalRing.residue V).comp c) ≫ (ratOf Y).pt) := by
    refine ⟨B, (congrArg (fun z => B ∈ E'.S z) (hpt _ _ _)).mpr hB, ?_⟩
    rw [show (ratOf Y).val (spMap ((IsLocalRing.residue V).comp c) ≫ (ratOf Y).pt) =
      ⇑((IsLocalRing.residue V).comp c) from funext (val_spMap_pt Y _), Mat.mul_inv hh.det_ne]
    exact Par.one
  have hAk : A ∈ E.S (((spMap (IsLocalRing.residue V) ≫ v₂) ≫ f)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))) := by
    refine (congrArg (fun z => A ∈ E.S z) ?_).mpr hA
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg f (closedPt_comp v₂)).trans hf₂)
  obtain ⟨p, -, hp⟩ := hf.lifts _ _ A hAk _ hh
  refine (ec.trans (hp _ ⟨?_, hb₁⟩)).trans (hp _ ⟨rfl, hb₂⟩).symm
  rw [← ec]
  exact congrArg (spMap (IsLocalRing.residue V) ≫ ·) e.symm

end GlobalTheory.FlagPush.Meet
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.hermPairSections_good_shiftSecondBundleNormPair : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField) (u : ℝ), 0 ≤ u → P.Good D b s t → (shiftA P u).Good D b s t := by
  first | exact @GlobalTheory.HSNef.good_shiftA | exact GlobalTheory.HSNef.good_shiftA | (intros; apply GlobalTheory.HSNef.good_shiftA <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.isBirationalModel_of_isIso_over_nonempty_open : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X) (U : X.Opens), (U : Set X).Nonempty → IsIso (π ∣_ U) → ∃ φ : X.functionField →+* Y.functionField, IsModel π φ := by
  first | exact @GlobalTheory.HSNef.isModel_of_isIso_restrict | exact GlobalTheory.HSNef.isModel_of_isIso_restrict | (intros; apply GlobalTheory.HSNef.isModel_of_isIso_restrict <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem GlobalTheory.FlagPush.Dbl.transition_par_stalk : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ z : W.Z, ∀ A₁ ∈ E'.S (W.p₁ z), ∀ A₂ ∈ E'.S (W.p₂ z), Par 0 (algebraMap (W.Z.presheaf.stalk z) W.Z.functionField).range (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) := by
  intro F _ X Y ι _ m E E' φ f hR W hW z A₁ hA₁ A₂ hA₂
  have hbase := GlobalTheory.T.maps_comp_eq_of_functionField_maps_agree F X Y φ f hR.hom W hW
  have hf : f (W.p₁ z) = f (W.p₂ z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hbase]
  obtain ⟨A, hA⟩ := E.nonempty (f (W.p₁ z))
  have hA' : A ∈ E.S (f (W.p₂ z)) := hf ▸ hA
  have h₁ := hR.sub _ A₁ hA₁ A hA
  have h₂ := hR.sub _ A₂ hA₂ A hA'
  have reg : ∀ (p : W.Z ⟶ Y.X) [IsDominant p], ∀ x ∈ ((ratOf Y).O (p z)).toSubring,
      functionFieldMap p x ∈ (algebraMap (W.Z.presheaf.stalk z) W.Z.functionField).range := by
    intro p _ x hx
    obtain ⟨a, rfl⟩ := mem_O_ratOf.1 hx
    exact ⟨_, (functionFieldMap_algebraMap p z a).symm⟩
  have k₁ := h₁.map W.α₁ (reg W.p₁)
  have k₂ := h₂.map W.α₂ (reg W.p₂)
  set B : Mat m Y.Fn := A.map φ with hBdef
  have hB : ∀ τ, (B τ).det ≠ 0 := fun τ => by
    intro h
    exact Fr.det_ne hA τ ((map_eq_zero (φ : X.Fn →+* Y.Fn)).1 (((φ : X.Fn →+* Y.Fn).map_det (A τ)).trans h))
  have hB₂ : ∀ τ, (B.map W.α₂ τ).det ≠ 0 := fun τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hB τ)
  have e12 : B.map W.α₁ = B.map W.α₂ := by
    funext τ; ext i j; exact hW (A τ i j)
  have d₁ : A₁ = A₁ * B⁻¹ * B := by rw [mul_assoc, Mat.inv_mul hB, mul_one]
  have d₂ : A₂ = A₂ * B⁻¹ * B := by rw [mul_assoc, Mat.inv_mul hB, mul_one]
  have key : A₁.map W.α₁ * (A₂.map W.α₂)⁻¹ = (A₁ * B⁻¹).map W.α₁ * ((A₂ * B⁻¹).map W.α₂)⁻¹ := by
    conv_lhs => rw [d₁, d₂]
    rw [Mat.map_mul _ _ W.α₁, Mat.map_mul _ _ W.α₂, e12, Mat.mul_inv_rev, mul_assoc, ← mul_assoc (B.map W.α₂),
      Mat.mul_inv hB₂, one_mul]
  rw [key]
  exact k₁.mul k₂.inv
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.OnSection

theorem not_unitAt_of_eq {F : Type} [Field F] {X Y : Var F} {ι : Type} {m : ι → ℕ} {E : Fr (ratOf X) m 0}
    {E' : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hf : Refines E E' φ f) (W : Dbl Y)
    (hα : ∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) (τ : ι) (a b : Fin (m τ)) (hab : a ≠ b) {k : Type} [Field k]
    (w : Sp k ⟶ W.Z) (hw : w ≫ W.p₁ = w ≫ W.p₂) (A : Mat m Y.Fn)
    (hA : A ∈ E'.S (W.p₁ (w (IsLocalRing.closedPoint k)))) :
    ¬ UnitAt (w (IsLocalRing.closedPoint k)) ((A.map W.α₁ * (A.map W.α₂)⁻¹) τ a b) := by
  obtain ⟨ev, hev, hq⟩ := GlobalTheory.T.exists_eval_regular_functions_at_fieldPoint F Y W.Z k w
  have hp : W.p₂ (w (IsLocalRing.closedPoint k)) = W.p₁ (w (IsLocalRing.closedPoint k)) :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans
      ((congrArg (fun q : Sp k ⟶ Y.X => q (IsLocalRing.closedPoint k)) hw.symm).trans (Scheme.Hom.comp_apply _ _ _))
  obtain ⟨A₀, hA₀⟩ := E.nonempty (f (W.p₁ (w (IsLocalRing.closedPoint k))))
  have hM := hf.sub _ A hA A₀ hA₀
  have hd : ∀ σ, (A₀.map φ σ).det ≠ 0 := fun σ => by
    have := Mat.det_map A₀ (φ : X.Fn →+* Y.Fn) σ
    exact this.trans_ne ((map_ne_zero _).2 (Fr.det_ne hA₀ σ))
  generalize hB : A₀.map φ = B at hM hd
  have hB12 : B.map W.α₁ = B.map W.α₂ := by
    subst hB
    funext σ
    ext i j
    exact hα _
  have h1 : ∀ u ∈ ((ratOf Y).O (W.p₁ (w (IsLocalRing.closedPoint k)))).toSubring,
      ∃ h, ev ⟨W.α₁ u, h⟩ = (ratOf Y).val (w ≫ W.p₁) u := fun u hu => hq W.p₁ u (mem_O_ratOf.1 hu)
  have h2 : ∀ u ∈ ((ratOf Y).O (W.p₁ (w (IsLocalRing.closedPoint k)))).toSubring,
      ∃ h, ev ⟨W.α₂ u, h⟩ = (ratOf Y).val (w ≫ W.p₁) u := fun u hu => by
    obtain ⟨h, e⟩ := hq W.p₂ u (by rw [hp]; exact mem_O_ratOf.1 hu)
    exact ⟨h, e.trans (congrArg (fun q => (ratOf Y).val q u) hw.symm)⟩
  have hN₁ := hM.map W.α₁ fun u hu => (h1 u hu).choose
  have hN₂ := hM.map W.α₂ fun u hu => (h2 u hu).choose
  have hd₂ : ∀ σ, (B.map W.α₂ σ).det ≠ 0 := fun σ => (Mat.det_map B W.α₂ σ).trans_ne ((map_ne_zero _).2 (hd σ))
  have hg : A.map W.α₁ * (A.map W.α₂)⁻¹ = (A * B⁻¹).map W.α₁ * ((A * B⁻¹).map W.α₂)⁻¹ := by
    rw [Mat.map_mul, Mat.map_mul, Mat.map_inv, Mat.map_inv, hB12, Mat.mul_inv_rev, Mat.inv_inv hd₂, mul_assoc,
      ← mul_assoc _ (B.map W.α₂), Mat.inv_mul hd₂, one_mul]
  rw [hg]
  have hG := hN₁.mul hN₂.inv
  let v : W.Z.functionField → k := fun u => if h : u ∈ (algebraMap (W.Z.presheaf.stalk (w (IsLocalRing.closedPoint k)))
    W.Z.functionField).range then ev ⟨u, h⟩ else 0
  have hv : ∀ x : (algebraMap (W.Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) W.Z.functionField).range,
      v (x : W.Z.functionField) = ev x := fun x => dif_pos x.2
  have e1 := Par.map_mul_of hG hN₂ v ev hv
  rw [mul_assoc, Mat.inv_mul hN₂.det_ne, mul_one] at e1
  have e2 : ((A * B⁻¹).map W.α₁).map v = ((A * B⁻¹).map W.α₂).map v := by
    funext σ
    ext i j
    obtain ⟨p, hp⟩ := h1 _ ((hM σ).1 i j)
    obtain ⟨q, hq⟩ := h2 _ ((hM σ).1 i j)
    exact ((hv ⟨_, p⟩).trans hp).trans ((hv ⟨_, q⟩).trans hq).symm
  have hV := (Par.map_of hN₂ v ev hv).det_ne
  have e3 : ((A * B⁻¹).map W.α₁ * ((A * B⁻¹).map W.α₂)⁻¹).map v = 1 := by
    have := congrArg (· * (((A * B⁻¹).map W.α₂).map v)⁻¹) (e1.symm.trans e2)
    simpa only [mul_assoc, Mat.mul_inv hV, mul_one] using this
  intro hu
  refine (hev ⟨_, (hG τ).1 a b⟩).2 hu ((hv ⟨_, (hG τ).1 a b⟩).symm.trans ?_)
  exact (congrFun (congrFun (congrFun e3 τ) a) b).trans (Matrix.one_apply_ne hab)

end GlobalTheory.FlagPush.OnSection

theorem GlobalTheory.FlagPush.not_unitAt_section : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ (τ : ι) (a b : Fin (m τ)), a ≠ b → ∀ y : Y.X, ∀ A ∈ E'.S y, ¬ UnitAt (W.δ y) ((A.map W.α₁ * (A.map W.α₂)⁻¹) τ a b) := by
  intro F _ X Y ι _ m E E' φ f hf W hα τ a b hab y A hA
  let w₀ : Sp (Y.X.residueField y) ⟶ Y.X := Y.X.fromSpecResidueField y
  have h0 : w₀ (IsLocalRing.closedPoint _) = y := Scheme.fromSpecResidueField_apply _ _
  have h1 : (w₀ ≫ W.δ) (IsLocalRing.closedPoint _) = W.δ y := (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ h0)
  have h2 : W.p₁ (W.δ y) = y := by rw [← Scheme.Hom.comp_apply, W.δ₁]; rfl
  have := OnSection.not_unitAt_of_eq hf W hα τ a b hab (w₀ ≫ W.δ)
    (by rw [Category.assoc, Category.assoc, W.δ₁, W.δ₂]) A (by rw [h1, h2]; exact hA)
  rwa [h1] at this
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem genPair_specializes_diagonal : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K),
    GenPair Y ψ₁ ψ₂ → ∃ h : (spMap ψ₁ ≫ (ratOf Y).pt) ≫ Y.str = (spMap ψ₂ ≫ (ratOf Y).pt) ≫ Y.str,
      Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h
        (IsLocalRing.closedPoint K) ⤳ Limits.pullback.diagonal Y.str (genericPoint Y.X) := by
  intro F _ Y K _ ψ₁ ψ₂ hG
  obtain ⟨hF, V, v₁, v₂, e₁, e₂, e₃, e₄⟩ := hG
  have hs : (ratOf Y).pt ≫ Y.str = spMap (algebraMap F Y.Fn) := (ratOf Y).pt_s
  have k : ∀ ψ : Y.Fn →+* K, (spMap ψ ≫ (ratOf Y).pt) ≫ Y.str = spMap (ψ.comp (algebraMap F Y.Fn)) :=
    fun ψ => (Category.assoc (spMap ψ) (ratOf Y).pt Y.str).trans
      ((congrArg (fun g => spMap ψ ≫ g) hs).trans (by rw [← Spec.map_comp]; rfl))
  have h : (spMap ψ₁ ≫ (ratOf Y).pt) ≫ Y.str = (spMap ψ₂ ≫ (ratOf Y).pt) ≫ Y.str := by
    rw [k, k, hF]
  refine ⟨h, ?_⟩
  haveI : IsDominant (spMap (algebraMap V K)) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (algebraMap V K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp (show Function.Injective (algebraMap V K) from Subtype.val_injective)]
    exact bot_le
  have hv : v₁ ≫ Y.str = v₂ ≫ Y.str := by
    refine ext_of_isDominant (spMap (algebraMap V K)) ?_
    rw [← Category.assoc, ← Category.assoc, e₁, e₂]
    exact h
  let v := Limits.pullback.lift v₁ v₂ hv
  have hgen : spMap (algebraMap V K) ≫ v =
      Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h := by
    apply Limits.pullback.hom_ext
    · simp only [v, Category.assoc, Limits.pullback.lift_fst]; exact e₁.trans (Limits.pullback.lift_fst _ _ _).symm
    · simp only [v, Category.assoc, Limits.pullback.lift_snd]; exact e₂.trans (Limits.pullback.lift_snd _ _ _).symm
  have hres : spMap (IsLocalRing.residue V) ≫ v =
      (spMap (IsLocalRing.residue V) ≫ v₁) ≫ Limits.pullback.diagonal Y.str := by
    apply Limits.pullback.hom_ext
    · simp only [v, Category.assoc, Limits.pullback.lift_fst, Limits.pullback.diagonal_fst, Category.comp_id]
    · simp only [v, Category.assoc, Limits.pullback.lift_snd, Limits.pullback.diagonal_snd, Category.comp_id]
      exact e₃.symm
  have hsp := ClosedPt.gen_specializes v (IsLocalRing.closedPoint K)
  rw [hgen] at hsp
  have hc : v (IsLocalRing.closedPoint V) = Limits.pullback.diagonal Y.str (genericPoint Y.X) := by
    calc v (IsLocalRing.closedPoint V) = (spMap (IsLocalRing.residue V) ≫ v) (IsLocalRing.closedPoint _) :=
          (ClosedPt.closedPt_comp v).symm
      _ = ((spMap (IsLocalRing.residue V) ≫ v₁) ≫ Limits.pullback.diagonal Y.str) (IsLocalRing.closedPoint _) := by
          rw [hres]
      _ = Limits.pullback.diagonal Y.str ((spMap (IsLocalRing.residue V) ≫ v₁) (IsLocalRing.closedPoint _)) :=
          Scheme.Hom.comp_apply _ _ _
      _ = Limits.pullback.diagonal Y.str (genericPoint Y.X) := by rw [ClosedPt.closedPt_comp v₁, e₄]
  rw [hc] at hsp
  exact hsp

end GlobalTheory.FlagPush
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.geometricDegree_pull_birationalModel : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ L : HermLB p, gdeg (L.pull π hπ) D = gdeg L D ∧ ∀ (a t : ℝ), L.IsSelfInter a → ((L.pull π hπ).shift (fun _ => t) fun _ => rfl).IsSelfInter (a + ((D : ℝ) + 1) * t * gdeg L D) := by
  first | exact @GlobalTheory.HSNef.gdeg_pull_model | exact GlobalTheory.HSNef.gdeg_pull_model | (intros; apply GlobalTheory.HSNef.gdeg_pull_model <;> assumption)
end

section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes

theorem _root_.GlobalTheory.T.padicTensorUnramifiedFrobTwist_iterate_degree : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), 0 < r → ∀ x : KQ p K r, (⇑(sigKQ p K r))^[r] x = x :=
  @_root_.GlobalTheory.LKResNrmConj.sigKQ_iterate_self
end
