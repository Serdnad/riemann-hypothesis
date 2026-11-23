module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle962
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
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
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle005
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic
open ReciprocityTheory.L2DbarEstimates (V leviV)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem semiPos_of_isFS : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ (D : ℕ) (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ),
    IsFS M f w → M.SemiPos D := by
  intro k _ X _ p D M J _ f w hM σ i c y hy ξ
  classical
  obtain ⟨ρ, -, hreg, hφ⟩ := hM
  have hx : under y ∈ M.B.U i := mem_ptsIn.1 hy.2
  obtain ⟨hr, j0, hu⟩ := hreg (under y) i hx
  choose U hU a ha using fun j => (hr j).exists_fnOf
  let G (j : J) (v : V D) : ℂ := (Real.exp (w j) : ℂ) * ev p σ (U j) (a j) (c.e.symm v)
  let S : Set (CxPts p σ) := ptsIn p σ (M.B.U i) ∩ ⋂ j, ptsIn p σ (U j)
  have hSo : IsOpen S := (isOpen_ptsIn _).inter (isOpen_iInter_of_finite fun j => isOpen_ptsIn _)
  have hyS : y ∈ S := ⟨hy.2, Set.mem_iInter.2 fun j => mem_ptsIn.2 (hU j)⟩
  have hO := isOpen_over c.e hSo
  have hmO := mem_over c.e hy.1 hyS

  have hval (z : CxPts p σ) (hz : z ∈ S) (j : J) :
      ratVal (f j * (ρ i : X.functionField)) z = ev p σ (U j) (a j) z := by
    rw [← ha j]
    exact ratVal_fnOf (Set.mem_iInter.1 hz.2 j) _ _
  have hterm (z : CxPts p σ) (hz : z ∈ S) (j : J) :
      ‖ratVal (f j * (ρ i : X.functionField)) z‖ ^ 2 * Real.exp (2 * w j) =
        Complex.normSq ((Real.exp (w j) : ℂ) * ev p σ (U j) (a j) z) := by
    rw [hval z hz j, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq,
      ← Real.exp_add]
    ring_nf
  have hG (j : J) : ContDiffAt ℂ 2 (G j) (c.e y) := by
    have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (U j))
    have hm := mem_over c.e hy.1 (mem_ptsIn.2 (hU j))
    exact contDiffAt_const.mul ((((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ ho
      (c.holo (U j) (a j))).contDiffAt (ho.mem_nhds hm)).of_le (by norm_cast)))
  let e := Fintype.equivFin J
  let u (b : Fin (Fintype.card J)) (v : V D) : ℝ := Complex.normSq (G (e.symm b) v)
  have hsum (v : V D) : ∑ b, u b v = ∑ j, Complex.normSq (G j v) :=
    Equiv.sum_comp e.symm fun j => Complex.normSq (G j v)
  have hev : (fun v => (((M.φ σ).φ i (c.e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)]
      fun v => ((Real.log (∑ b, u b v) : ℝ) : ℂ) := by
    filter_upwards [hO.mem_nhds hmO] with v hv
    rw [hφ σ _ i hv.2.1, hsum]
    congr 2
    exact Finset.sum_congr rfl fun j _ => hterm _ hv.2 j
  have hpos : 0 < ∑ b, u b (c.e y) := by
    rw [hsum]
    simp only [G, c.e.left_inv hy.1]
    refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨j0, Finset.mem_univ _, ?_⟩
    rw [← hterm y hyS j0]
    exact mul_pos (pow_pos (norm_pos_iff.2 (ratVal_ne_zero hu)) 2) (Real.exp_pos _)
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr hev]
  exact ReciprocityTheory.L2DbarEstimates.leviV_log_sum_nonneg
    (fun b => ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp (hG _))
    (fun b => ReciprocityTheory.L2DbarEstimates.logPshAt_normSq (hG _)) hpos ξ

end GlobalTheory.HSNef
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.BoxProd

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f := by
  unfold Pair.nu; positivity

theorem mul_mem_Bl (P : Pair p) {a b a' b' : ℤ} {R R' : ℝ} (hR : 0 ≤ R) {f g : X.functionField}
    (hf : f ∈ P.Bl a b R) (hg : g ∈ P.Bl a' b' R') : f * g ∈ P.Bl (a + a') (b + b') (R * R') := by
  obtain ⟨h1, h2⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul _ _ _ P a b a' b' f g hf.1 hg.1
  refine ⟨h1, fun σ y => ?_⟩
  rw [h2 σ y]
  exact mul_le_mul (hf.2 σ y) (hg.2 σ y) (nu_nonneg _ _ _ _ _ _) hR

theorem one_mem_Bl (P : Pair p) : (1 : X.functionField) ∈ P.Bl 0 0 1 := by
  refine ⟨fun x i j _ _ => ?_, fun σ y => ?_⟩
  · simp only [Pair.loc, zpow_zero, mul_one]
    exact ⟨1, map_one _⟩
  · have e := IntExample.ratVal_nat y 1
    simp only [Nat.cast_one] at e
    simp [Pair.nu, Pair.loc, e]

theorem prod_mem_of_le (P : Pair p) (D : ℕ) (J : Type) (e : J → X.functionField) (x : Fin D → X.functionField)
    (a b : ℤ) (R : ℝ) (hR : 0 ≤ R) (h : ∀ c, boxFam e x c ∈ P.Bl a b R) :
    ∀ (m : ℕ) (u : Fin m → J) (n : Fin D → ℕ), (∀ i, n i ≤ m) →
      (∏ l, e (u l)) * ∏ i, x i ^ n i ∈ P.Bl (m * a) (m * b) (R ^ m) := by
  intro m
  induction m with
  | zero =>
    intro u n hn
    have h0 : ∀ i, n i = 0 := fun i => Nat.le_zero.1 (hn i)
    simp only [h0, pow_zero, Finset.prod_const_one, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
      Nat.cast_zero, zero_mul]
    exact one_mem_Bl P
  | succ m ih =>
    intro u n hn
    have hx : ∏ i, x i ^ n i =
        (∏ i ∈ Finset.univ.filter (fun i => 0 < n i), x i) * ∏ i, x i ^ (n i - 1) := by
      rw [Finset.prod_filter, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rcases Nat.eq_zero_or_pos (n i) with h0 | h0
      · simp [h0]
      · rw [if_pos h0, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ n i)]
    have key : (∏ l, e (u l)) * ∏ i, x i ^ n i =
        boxFam e x (u 0, Finset.univ.filter (fun i => 0 < n i)) *
          ((∏ l : Fin m, e (u l.succ)) * ∏ i, x i ^ (n i - 1)) := by
      rw [Fin.prod_univ_succ, hx]
      simp only [boxFam]
      ring
    rw [key]
    have hm := mul_mem_Bl P hR (h (u 0, Finset.univ.filter (fun i => 0 < n i)))
      (ih (fun l => u l.succ) (fun i => n i - 1) (fun i => by have := hn i; omega))
    have ea : ((m + 1 : ℕ) : ℤ) * a = a + m * a := by push_cast; ring
    have eb : ((m + 1 : ℕ) : ℤ) * b = b + m * b := by push_cast; ring
    rw [ea, eb, pow_succ']
    exact hm

theorem prod_mem_Bl : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (D : ℕ) (J : Type) (e : J → X.functionField) (x : Fin D → X.functionField) (a b : ℤ) (R : ℝ), 0 ≤ R → (∀ c, boxFam e x c ∈ P.Bl a b R) → ∀ (m : ℕ) (u : Fin m → J) (n : Fin D → ℕ), (∀ i, n i < m) → (∏ l, e (u l)) * ∏ i, x i ^ n i ∈ P.Bl (m * a) (m * b) (R ^ m) := by
  intro k _ X _ p P D J e x a b R hR h m u n hn
  exact prod_mem_of_le P D J e x a b R hR h m u n fun i => (hn i).le

end GlobalTheory.HSNef.BoxProd
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem isModel_id (X : Scheme.{0}) [IsIntegral X] : IsModel (𝟙 X) (RingHom.id X.functionField) := by
  refine { gen := rfl, deg := Scheme.Hom.residueDegree_id _, compat := ?_ }
  intro y a
  simp only [RingHom.id_apply, Scheme.Hom.stalkMap_id]
  rfl

theorem IsModel.comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z] {π : Y ⟶ X} {π' : Z ⟶ Y}
    {φ : X.functionField →+* Y.functionField} {φ' : Y.functionField →+* Z.functionField}
    (h : IsModel π φ) (h' : IsModel π' φ') : IsModel (π' ≫ π) (φ'.comp φ) := by
  refine { gen := ?_, deg := ?_, compat := ?_ }
  · show π (π' (genericPoint Z)) = genericPoint X
    rw [h'.gen, h.gen]
  · rw [GlobalTheory.CurveDegreesCompare.residueDegree_comp π' π (genericPoint Z), h'.deg]
    rw [h'.gen, h.deg]
  · intro z a
    refine (congrArg φ' (h.compat (π' z) a)).trans ((h'.compat z _).trans ?_)
    rw [Scheme.Hom.stalkMap_comp]
    rfl

theorem isModel_id_and_comp : ∀ (X Y Z : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (π : Y ⟶ X) (π' : Z ⟶ Y)
    (φ : X.functionField →+* Y.functionField) (φ' : Y.functionField →+* Z.functionField),
    IsModel (𝟙 X) (RingHom.id _) ∧ (IsModel π φ → IsModel π' φ' → IsModel (π' ≫ π) (φ'.comp φ)) :=
  fun X _ _ _ _ _ _ _ _ _ => ⟨isModel_id X, fun h h' => h.comp h'⟩

end GlobalTheory.HSNef
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep.Centre

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem centreAt_of_dominatesStalk {E : DivOver p} {z : X} (h : DominatesStalk E.ring z) :
    CentreAt E z := by
  refine ⟨by rintro _ ⟨a, rfl⟩; exact h.1 a, ?_⟩
  rintro f ⟨a, ha⟩ h0
  have hinv : ((f⁻¹ : X.functionFieldˣ) : X.functionField) ∈ E.ring :=
    (E.ord_nonneg_iff f⁻¹).1 (by rw [E.ord_inv, h0]; simp)
  have hu : IsUnit a := by
    by_contra hu
    have h1 := (E.ring.coe_mem_nonunits_iff (a := ⟨_, h.1 a⟩)).mp (h.2 a hu)
    refine h1 (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_))
    change algebraMap _ X.functionField a * _ = 1
    rw [ha]
    exact f.mul_inv
  obtain ⟨u, rfl⟩ := hu
  refine ⟨((u⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z), ?_⟩
  have e : algebraMap _ X.functionField
      ((u⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z) * (f : X.functionField) = 1 := by
    rw [← ha, ← map_mul, Units.inv_mul, map_one]
  exact (Units.inv_eq_of_mul_eq_one_left e).symm

theorem exists_centreAt {E : DivOver p} {x : X} (h : E.Through x) :
    ∃ z, z ⤳ x ∧ CentreAt E z :=
  have ⟨z, hz, hd⟩ := exists_specializes_dominatesStalk_of_regAt X E.ring x h
  ⟨z, hz, centreAt_of_dominatesStalk hd⟩

theorem exists_isLogEqn_add [IsLocallyNoetherian X] {n : ℕ} {Δ D : X → ℚ} {η : RatForms p n}
    {x : X} {m : ℕ} {g : X.functionFieldˣ} (hD : IsQCart D) (hm : 0 < m)
    (hg : IsLogEqn p Δ η x m g) :
    ∃ (m' : ℕ) (g' : X.functionFieldˣ), 0 < m' ∧ IsLogEqn p (Δ + D) η x m' g' := by
  obtain ⟨r, D₀, hr, -, rfl⟩ := hD
  obtain ⟨d, hd⟩ := D₀.exists_isEqn x
  obtain ⟨V, hV, hdV⟩ := hd.exists_nhds
  refine ⟨m * r, g ^ r * d ^ m, Nat.mul_pos hm hr, fun z hz E hE => ?_⟩
  have h1 := (hdV z (hz.mem_open V.isOpen hV)).mult_eq
  rw [← hE.ord_eq] at h1
  have h2 := hg z hz E hE
  have : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [E.ord_mul, E.ord_pow, E.ord_pow, Pi.add_apply, qWeil, h1]
  push_cast
  rw [← h2]
  field_simp
  ring

theorem exists_isNkltCentre : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∀ (Δ D : X → ℚ) (x : X), IsQCart D → KltAt p n Δ x → ¬ KltAt p n (Δ + D) x →
    ∃ z, z ⤳ x ∧ IsNkltCentre p n (Δ + D) z := by
  intro X _ _ _ p n hp hn Δ D x hD hk hnk
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  obtain ⟨η, m, g, hη, hm, hg, -⟩ := hk
  obtain ⟨m', g', hm', hg'⟩ := exists_isLogEqn_add hD hm hg
  rw [hg'.kltAt_iff hn hη hm'] at hnk
  push_neg at hnk
  obtain ⟨E, hE, hd⟩ := hnk
  obtain ⟨z, hz, hc⟩ := exists_centreAt hE
  exact ⟨z, hz, E, η, m', g', hη, hm', fun w hw => hg' w (hw.trans hz), hc, hd⟩

end GlobalTheory.PairStep.Centre
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.AlmostLowUnits

theorem det_almost {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (a b : Fin n)
    (hb : (b : ℕ) = a + 1) (hab : A a b ≠ 0)
    (hl : ∀ i j : Fin n, i < j → ¬ (i = a ∧ j = b) → A i j = 0) :
    A.det = (A a a * A b b - A a b * A b a) * ∏ i ∈ (Finset.univ.erase a).erase b, A i i := by
  have hne : a ≠ b := fun h => by rw [h] at hb; omega
  have hlt : a < b := by rw [Fin.lt_iff_val_lt_val]; omega
  set c := A a a / A a b with hc
  set U := A.updateCol a (fun k => A k a + (-c) • A k b) with hU
  set N := U.submatrix id (Equiv.swap a b) with hN
  have hdetU : U.det = A.det := Matrix.det_updateCol_add_smul_self A hne (-c)
  have hdetN : N.det = - A.det := by
    rw [hN, Matrix.det_permute', Equiv.Perm.sign_swap hne, hdetU]; simp
  have hUapp : ∀ i j, U i j = if j = a then A i a - c * A i b else A i j := by
    intro i j
    rw [hU, Matrix.updateCol_apply]
    split_ifs <;> simp [sub_eq_add_neg]
  have hNapp : ∀ i j, N i j = U i (Equiv.swap a b j) := fun _ _ => rfl
  have htri : N.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    rw [hNapp]
    by_cases hja : j = a
    · rw [hja, Equiv.swap_apply_left, hUapp, if_neg hne.symm]
      rw [hja] at hij'
      exact hl i b (lt_trans hij' hlt) (fun h => (ne_of_lt hij') h.1)
    · by_cases hjb : j = b
      · rw [hjb, Equiv.swap_apply_right, hUapp, if_pos rfl]
        rw [hjb] at hij'
        by_cases hia : i = a
        · rw [hia, hc, div_mul_cancel₀ _ hab, sub_self]
        · have hia' : i < a := by
            have h1 : (i : ℕ) < b := hij'
            have h2 : (i : ℕ) ≠ a := fun h => hia (Fin.ext h)
            rw [Fin.lt_iff_val_lt_val]; omega
          rw [hl i a hia' (fun h => hia h.1), hl i b (lt_trans hia' hlt) (fun h => hia h.1)]; ring
      · rw [Equiv.swap_apply_of_ne_of_ne hja hjb, hUapp, if_neg hja]
        exact hl i j hij' (fun h => hjb h.2)
  have hprod := Matrix.det_of_lowerTriangular N htri
  have hmb : b ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), ← Finset.mul_prod_erase _ _ hmb] at hprod
  have hNa : N a a = A a b := by rw [hNapp, Equiv.swap_apply_left, hUapp, if_neg hne.symm]
  have hNb : N b b = A b a - c * A b b := by rw [hNapp, Equiv.swap_apply_right, hUapp, if_pos rfl]
  have hrest : ∏ i ∈ (Finset.univ.erase a).erase b, N i i = ∏ i ∈ (Finset.univ.erase a).erase b, A i i := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hib := (Finset.mem_erase.1 hi).1
    have hia := (Finset.mem_erase.1 (Finset.mem_erase.1 hi).2).1
    rw [hNapp, Equiv.swap_apply_of_ne_of_ne hia hib, hUapp, if_neg hia]
  rw [hNa, hNb, hrest, hdetN] at hprod
  have e : A a b * (A b a - c * A b b) = A a b * A b a - A a a * A b b := by
    rw [hc]; field_simp
  rw [← mul_assoc, e] at hprod
  linear_combination (-1 : K) * hprod

theorem units_of_det {K α : Type} [Field K] [DecidableEq α] (O : Subring K) {s : Finset α} (x : α → K) (y d : K)
    (hd : d = y * ∏ i ∈ s, x i) (hd0 : d ≠ 0) (hdi : d⁻¹ ∈ O) (hy : y ∈ O) (hx : ∀ i ∈ s, x i ∈ O) :
    (y ≠ 0 ∧ y⁻¹ ∈ O) ∧ ∀ i ∈ s, x i ≠ 0 ∧ (x i)⁻¹ ∈ O := by
  have hP : ∏ i ∈ s, x i ∈ O := O.prod_mem hx
  rw [hd] at hd0
  refine ⟨⟨left_ne_zero_of_mul hd0, ?_⟩, fun i hi => ?_⟩
  · have e : y⁻¹ = d⁻¹ * ∏ i ∈ s, x i := by
      rw [hd, mul_inv, mul_assoc, inv_mul_cancel₀ (right_ne_zero_of_mul hd0), mul_one]
    rw [e]; exact O.mul_mem hdi hP
  · have e : d = x i * (y * ∏ j ∈ s.erase i, x j) := by
      rw [hd, ← Finset.mul_prod_erase s x hi]; ring
    have h0 : x i * (y * ∏ j ∈ s.erase i, x j) ≠ 0 := by rw [← e, hd]; exact hd0
    refine ⟨left_ne_zero_of_mul h0, ?_⟩
    have e' : (x i)⁻¹ = d⁻¹ * (y * ∏ j ∈ s.erase i, x j) := by
      rw [e, mul_inv, mul_assoc, inv_mul_cancel₀ (right_ne_zero_of_mul h0), mul_one]
    rw [e']
    exact O.mul_mem hdi (O.mul_mem hy (O.prod_mem fun j hj => hx j (Finset.mem_of_mem_erase hj)))

end GlobalTheory.FlagPush.AlmostLowUnits


open GlobalTheory.FlagPush.AlmostLowUnits in
theorem GlobalTheory.FlagPush.almostLow_units : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 →
    ∀ (K : Type) [Field K] (O : Subring K) (g : Mat m K), AlmostLow τ a b g → Par 0 O g →
    (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → g x.1 x.2 x.2 ≠ 0 ∧ (g x.1 x.2 x.2)⁻¹ ∈ O) ∧
      minor τ a b g ≠ 0 ∧ (minor τ a b g)⁻¹ ∈ O := by
  intro ι m τ a b hb K _ O g hg hp
  have hlτ : ∀ i j : Fin (m τ), i < j → ¬ (i = a ∧ j = b) → g τ i j = 0 := fun i j hij h =>
    hg.2.2 τ i j hij (fun h' => h ⟨eq_of_heq (Sigma.mk.inj h'.1).2, eq_of_heq (Sigma.mk.inj h'.2).2⟩)
  have hdetτ := det_almost (g τ) a b hb hg.2.1 hlτ
  have hmO : minor τ a b g ∈ O :=
    O.sub_mem (O.mul_mem ((hp τ).1 a a) ((hp τ).1 b b)) (O.mul_mem ((hp τ).1 a b) ((hp τ).1 b a))
  have hτ := units_of_det O (fun i => g τ i i) (minor τ a b g) ((g τ).det) hdetτ (hp τ).2.1 (hp τ).2.2.1 hmO
    (fun i _ => (hp τ).1 i i)
  refine ⟨?_, hτ.1⟩
  rintro ⟨σ, i⟩ h1 h2
  by_cases hσ : σ = τ
  · subst hσ
    have hia : i ≠ a := fun e => h1 (by rw [e])
    have hib : i ≠ b := fun e => h2 (by rw [e])
    exact hτ.2 i (Finset.mem_erase.2 ⟨hib, Finset.mem_erase.2 ⟨hia, Finset.mem_univ _⟩⟩)
  · have htri : (g σ).BlockTriangular OrderDual.toDual := fun i j hij =>
      hg.2.2 σ i j (OrderDual.toDual_lt_toDual.1 hij) (fun h' => hσ (congrArg Sigma.fst h'.1))
    have hdet := Matrix.det_of_lowerTriangular (g σ) htri
    have h := units_of_det O (s := Finset.univ) (fun j => g σ j j) 1 ((g σ).det) (by rw [one_mul]; exact hdet)
      (hp σ).2.1 (hp σ).2.2.1 O.one_mem (fun j _ => (hp σ).1 j j)
    exact h.2 i (Finset.mem_univ _)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma mem_offHyp_iff {n : ℕ} {S : Finset (Fin n)}
    {U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n} :
    v ∈ _root_.GlobalTheory.GoodTop.offHyp S U ↔ v ∈ U ∧ ∀ a ∈ S, v.ofLp a ≠ 0 := by
  unfold _root_.GlobalTheory.GoodTop.offHyp
  exact Iff.rfl


open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
lemma _root_.GlobalTheory.GoodTop.offHyp_ae_eq {n : ℕ} (S : Finset (Fin n))
    (U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) : _root_.GlobalTheory.GoodTop.offHyp S U =ᵐ[volume] U := by
  refine ae_eq_set.2 ⟨?_, ?_⟩
  · exact measure_mono_null
      (fun v hv => (hv.2 (mem_offHyp_iff.1 hv.1).1).elim) measure_empty
  · refine measure_mono_null (t := ⋃ a ∈ (S : Set (Fin n)), {v : _root_.ReciprocityTheory.L2DbarEstimates.V n | v.ofLp a = 0})
      ?_ ?_
    · intro v hv
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe, exists_prop]
      by_contra h
      push_neg at h
      exact hv.2 (mem_offHyp_iff.2 ⟨hv.1, h⟩)
    · refine (measure_biUnion_null_iff S.countable_toSet).2 fun a _ => ?_
      let L : _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℝ] ℂ :=
        (EuclideanSpace.proj a : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).toLinearMap.restrictScalars ℝ
      have hset : {v : _root_.ReciprocityTheory.L2DbarEstimates.V n | v.ofLp a = 0} = (LinearMap.ker L : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) := by
        ext v
        simp [L]
      rw [hset]
      refine Measure.addHaar_submodule _ _ fun htop => ?_
      have hmem : EuclideanSpace.single a (1 : ℂ) ∈ LinearMap.ker L := htop ▸ Submodule.mem_top
      simp [L] at hmem

end GlobalTheory.GoodTop
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop


open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
theorem _root_.GlobalTheory.GoodTop.isOpen_offHyp_of_isOpen {n : ℕ} (S : Finset (Fin n)) (U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (hU : IsOpen U) :
    IsOpen (_root_.GlobalTheory.GoodTop.offHyp S U) := by
  unfold _root_.GlobalTheory.GoodTop.offHyp
  have hset : {v : _root_.ReciprocityTheory.L2DbarEstimates.V n | v ∈ U ∧ ∀ a ∈ S, v.ofLp a ≠ 0} =
      U ∩ ⋂ a ∈ S, {v : _root_.ReciprocityTheory.L2DbarEstimates.V n | v.ofLp a ≠ 0} := by
    ext v
    simp
  rw [hset]
  refine hU.inter (isOpen_biInter_finset fun a _ => isOpen_ne_fun ?_ continuous_const)
  unfold _root_.ReciprocityTheory.L2DbarEstimates.V
  fun_prop

end GlobalTheory.GoodTop
end
