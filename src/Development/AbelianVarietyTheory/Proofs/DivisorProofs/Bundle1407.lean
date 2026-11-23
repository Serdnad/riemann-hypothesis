module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1323
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1316
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
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

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.isFubiniStudy_ratFns_mem_pairSections : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → ∃ P : Pair p, P.L = M ∧ ∀ j, f j ∈ P.H 1 0 := by
  first | exact @GlobalTheory.HSNef.isFS_mem_pair | exact GlobalTheory.HSNef.isFS_mem_pair | (intros; apply GlobalTheory.HSNef.isFS_mem_pair <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.maps_comp_eq_of_functionField_maps_agree : ∀ (F : Type) [Field F] (X Y : Var F) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), (ratOf X).IsHom (ratOf Y) φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → W.p₁ ≫ f = W.p₂ ≫ f := by
  first | exact @GlobalTheory.FlagPush.Dbl.p_comp_eq_of_isHom | exact GlobalTheory.FlagPush.Dbl.p_comp_eq_of_isHom | (intros; apply GlobalTheory.FlagPush.Dbl.p_comp_eq_of_isHom <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.shiftSecondBundleNormPair_norm_ball_generation : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (u : ℝ), (∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), (shiftA P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(b * u))) ∧ (∀ (a b : ℤ) (R : ℝ), (shiftA P u).Bl a b R = P.Bl a b (R * Real.exp (b * u))) ∧ (∀ c : ℕ, GenAt P c → GenAt (shiftA P u) c) := by
  first | exact @GlobalTheory.HSNef.shiftA_props | exact GlobalTheory.HSNef.shiftA_props | (intros; apply GlobalTheory.HSNef.shiftA_props <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.boxMonomialFamily_prod_mem_normBall_of_exponent_lt : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (D : ℕ) (J : Type) (e : J → X.functionField) (x : Fin D → X.functionField) (a b : ℤ) (R : ℝ), 0 ≤ R → (∀ c, boxFam e x c ∈ P.Bl a b R) → ∀ (m : ℕ) (u : Fin m → J) (n : Fin D → ℕ), (∀ i, n i < m) → (∏ l, e (u l)) * ∏ i, x i ^ n i ∈ P.Bl (m * a) (m * b) (R ^ m) := by
  first | exact @GlobalTheory.HSNef.BoxProd.prod_mem_Bl | exact GlobalTheory.HSNef.BoxProd.prod_mem_Bl | (intros; apply GlobalTheory.HSNef.BoxProd.prod_mem_Bl <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.exists_nonKltCentre_of_not_klt_after_adding : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (x : X), IsQCart D → KltAt p n Δ x → ¬ KltAt p n (Δ + D) x → ∃ z, z ⤳ x ∧ IsNkltCentre p n (Δ + D) z := by
  first | exact @GlobalTheory.PairStep.Centre.exists_isNkltCentre | exact GlobalTheory.PairStep.Centre.exists_isNkltCentre | (intros; apply GlobalTheory.PairStep.Centre.exists_isNkltCentre <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.isBirationalModel_id_and_comp : ∀ (X Y Z : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (π : Y ⟶ X) (π' : Z ⟶ Y) (φ : X.functionField →+* Y.functionField) (φ' : Y.functionField →+* Z.functionField), IsModel (𝟙 X) (RingHom.id _) ∧ (IsModel π φ → IsModel π' φ' → IsModel (π' ≫ π) (φ'.comp φ)) := by
  first | exact @GlobalTheory.HSNef.isModel_id_and_comp | exact GlobalTheory.HSNef.isModel_id_and_comp | (intros; apply GlobalTheory.HSNef.isModel_id_and_comp <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.semiPos_of_isFubiniStudyOfRatFnFamily : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (D : ℕ) (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → M.SemiPos D := by
  first | exact @GlobalTheory.HSNef.semiPos_of_isFS | exact GlobalTheory.HSNef.semiPos_of_isFS | (intros; apply GlobalTheory.HSNef.semiPos_of_isFS <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem nu_shiftA {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) (u : ℝ)
    (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    (shiftA P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(b * u)) := by
  change ‖ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y‖ *
      Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y +
        b * ((P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y + 2 * u)) / 2) = _
  rw [Pair.nu, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem Bl_subset_shiftA {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) {u : ℝ}
    (hu : 0 ≤ u) (a b : ℤ) (hb : 0 ≤ b) {R : ℝ} {f : X.functionField} (hf : f ∈ P.Bl a b R) :
    f ∈ (shiftA P u).Bl a b R := by
  refine ⟨hf.1, fun σ y => ?_⟩
  rw [nu_shiftA]
  have h1 : Real.exp (-(b * u)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : (0 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith)
  have h0 : 0 ≤ P.nu a b σ y f := by unfold Pair.nu; positivity
  have h2 : R ≥ P.nu a b σ y f := hf.2 σ y
  nlinarith [Real.exp_pos (-(b * u))]

theorem good_shiftA : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (b : ℕ) (s t : X.functionField) (u : ℝ), 0 ≤ u → P.Good D b s t → (shiftA P u).Good D b s t := by
  intro k _ X _ p D hX P b s t u hu h
  exact
    { ample := h.ample
      nef := GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX P.A u hu h.nef
      pos := h.pos
      s_mem := Bl_subset_shiftA P hu 0 1 zero_le_one h.s_mem
      s_ne := h.s_ne
      t_mem := Bl_subset_shiftA P hu (-1) b (Int.natCast_nonneg b) h.t_mem
      t_ne := h.t_ne
      reg := h.reg }

end GlobalTheory.HSNef
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem isModel_of_isIso_restrict : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X) (U : X.Opens),
    (U : Set X).Nonempty → IsIso (π ∣_ U) → ∃ φ : X.functionField →+* Y.functionField, IsModel π φ := by
  intro X Y _ _ π U hU hiso
  obtain ⟨h₁, h₂⟩ := GlobalTheory.Published.generic_of_isIso_restrict π U hU
  have e : closure ({genericPoint X} : Set X) = Set.univ := (genericPoint_spec X).def
  have hd : IsDominant π := ⟨dense_iff_closure_eq.mpr
    (Set.eq_univ_of_univ_subset (e ▸ closure_mono (Set.singleton_subset_iff.mpr ⟨_, h₁⟩)))⟩
  exact ⟨functionFieldMap π, h₁, h₂, fun y a => functionFieldMap_algebraMap π y a⟩

end GlobalTheory.HSNef
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.almostLowerTriangular_diag_minor_isUnit : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ (K : Type) [Field K] (O : Subring K) (g : Mat m K), AlmostLow τ a b g → Par 0 O g → (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → g x.1 x.2 x.2 ≠ 0 ∧ (g x.1 x.2 x.2)⁻¹ ∈ O) ∧ minor τ a b g ≠ 0 ∧ (minor τ a b g)⁻¹ ∈ O := by
  first | exact @GlobalTheory.FlagPush.almostLow_units | exact GlobalTheory.FlagPush.almostLow_units | (intros; apply GlobalTheory.FlagPush.almostLow_units <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.minor_two_by_two_triangular_product : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ (K : Type) [Field K] (S T C : Mat m K), Par m ⊤ S → Par m ⊤ T → AlmostLow τ a b C → AlmostLow τ a b (S * C * T) ∧ (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → (S * C * T) x.1 x.2 x.2 = S x.1 x.2 x.2 * C x.1 x.2 x.2 * T x.1 x.2 x.2) ∧ (S * C * T) τ a b = S τ a a * C τ a b * T τ b b ∧ minor τ a b (S * C * T) = S τ a a * S τ b b * minor τ a b C * (T τ a a * T τ b b) := by
  first | exact @GlobalTheory.FlagPush.almostLow_mul_entries | exact GlobalTheory.FlagPush.almostLow_mul_entries | (intros; apply GlobalTheory.FlagPush.almostLow_mul_entries <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem isometric_pull_shiftC {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    (L : HermLB p) (t : ℝ) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    ((L.shift (fun _ => t) fun _ => rfl).pull π hπ).Isometric ((L.pull π hπ).shift (fun _ => t) fun _ => rfl) :=
  HermLB.isometric_of_eqOn fun σ a y _ => by
    exact (congrArg (· + 2 * t) (Weight.pull_φ (L.φ σ) π hπ a y)).trans
      (Weight.pull_φ ((L.φ σ).addFn fun _ => 2 * t) π hπ a y).symm

theorem gdeg_pull_model : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q)
    (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ L : HermLB p, gdeg (L.pull π hπ) D = gdeg L D ∧
    ∀ (a t : ℝ), L.IsSelfInter a →
      ((L.pull π hπ).shift (fun _ => t) fun _ => rfl).IsSelfInter (a + ((D : ℝ) + 1) * t * gdeg L D) := by
  intro hC k _ X Y _ _ p q D hX hY π hπ φ hM L
  have hdeg : π.residueDegree (genericPoint Y) ≠ 0 := by rw [hM.deg]; exact one_ne_zero
  have hP := ((hC.arProj k X Y p q D hX hY π hπ hM.gen hdeg).1)
  have hP1 : ∀ (M : HermLB p) (a : ℝ), M.IsSelfInter a → (M.pull π hπ).IsSelfInter a := fun M a h => by
    have := hP M a h
    rwa [hM.deg, Nat.cast_one, one_mul] at this
  have hS := hC.arShift
  have hg : gdeg (L.pull π hπ) D = gdeg L D := by
    obtain ⟨h, hh⟩ := ((hC.arExists k X p D hX).1 L)
    have ha : L.IsSelfInter (h (genericPoint X)) := ⟨h, hh, rfl⟩
    set a := h (genericPoint X)

    have h1 := hP1 _ _ (hS k X p D hX L a 1 ha)
    have h1' := (isometric_pull_shiftC L 1 π hπ).isSelfInter hY h1
    have h2 := hS k Y q D hY (L.pull π hπ) a 1 (hP1 L a ha)
    have e := HermLB.IsSelfInter.unique hY h1' h2
    have hD : ((D : ℝ) + 1) ≠ 0 := by positivity
    have : ((D : ℝ) + 1) * gdeg L D = ((D : ℝ) + 1) * gdeg (L.pull π hπ) D := by linarith
    exact (mul_left_cancel₀ hD this).symm
  refine ⟨hg, fun a t ha => ?_⟩
  have := hS k Y q D hY (L.pull π hπ) a t (hP1 L a ha)
  rwa [hg] at this

end GlobalTheory.HSNef
end
end
