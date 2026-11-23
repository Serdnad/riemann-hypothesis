module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangent
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ChartKSBracket

theorem tanPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (u : TanM (𝟙 (Sp R)) Y.H), ∃ v' : TanM (𝟙 (Sp R)) t.G, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv u)) (tv v') := by
  intro E _ _ _ H R _ _ _ _ _ t P Y u
  letI := H.starRing
  have : Module.Finite R (DualNumber R) := inferInstanceAs (Module.Finite R (R × R))
  have := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal R) (DualNumber R)
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  have hs : spMap (algebraMap R (DualNumber R)) ≫ 𝟙 (Sp R) = spMap (algebraMap R (DualNumber R)) := Category.comp_id _
  obtain ⟨x, hx, -⟩ := GlobalTheory.FormalPoint.existsUnique_isPointOf' P.U.toUnifPre hs (Y.Φ _ (tv u))
  obtain ⟨x₀, -, hu₀⟩ := GlobalTheory.FormalPoint.existsUnique_isPointOf' P.U.toUnifPre hs (Y.Φ _ 1)
  have h1 := hx.pull (homAt (𝟙 (Sp R)) (tm ((0 : R) • (LinearMap.id : R →ₗ[R] R)))) (Y.rep.1 _ _ _ (tv u))
  have e : homAt (𝟙 (Sp R)) (tm ((0 : R) • (LinearMap.id : R →ₗ[R] R))) ≫ tv u = 1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem u
  rw [e] at h1
  have h2 := GlobalTheory.FormalPoint.isPointOf_one P.U.toUnifPre (GlobalTheory.ExpTan.isZero_one Y.rep (Over.mk (spMap (algebraMap R (DualNumber R)) ≫ 𝟙 (Sp R))))
  have hk : smT (𝟙 (Sp R)) 0 x = 1 := (hu₀ _ h1).trans (hu₀ _ h2).symm
  exact ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT x hk, hx⟩

theorem isTanAtG_tv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (v' : TanM (𝟙 (Sp R)) t.G), IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) (spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv v').left) := by
  intro E _ _ _ H R _ t v'
  refine GlobalTheory.LieMet.isTan_map _ ?_ (GlobalTheory.LieMet.isTan_tv v')
  rw [Category.comp_id, chart, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  rfl

end GlobalTheory.ChartKSBracket
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

namespace GlobalTheory.BddCusp

theorem mul_mem_cuspOn_of_bdd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : Rul Xo c), Nonempty (KeySec Xo c) → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → 1 ≤ Dw.p + Dw.q → Even G₀.2 → (∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → G₀.1 (τ, j) ≤ G₀.1 (τ, i)) → s ∈ secZ Xo c (exZ Dw G₀) → s ∈ suppOn Z → (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x G₀ s z ≤ C) → ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z G, f * s ∈ cuspOn U Z (G + G₀) := by
  intro E _ _ _ H Dw l Xo c r U x Z G₀ s hK hU hpq h0 hdec hs hZ hb G hG f hf
  exact mul_mem_cuspOn_of_isSec h0 hs hZ
    (fun σ hσ k => GlobalTheory.T.isSec_reading_decreasing_integer_exponents E H Dw l Xo c σ r (U σ) hK hσ (hU σ hσ) hpq G₀ h0 hdec s hs k) hb hG hf

end GlobalTheory.BddCusp
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

section IntCone

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem intCone_evalZ_sum {n : ℕ} {β : Fin n → LinearMap.BilinForm ℤ X} (h : φ.LinearOn β) (a : Fin n → ℕ) :
    φ.evalZ (∑ i, a i • β i) = ∑ i, (a i : ℝ) * φ.evalZ (β i) := by
  have := h (fun i => (a i : ℝ)) (fun i => Nat.cast_nonneg _)
  refine Eq.trans ?_ this
  unfold InvFun.evalZ
  congr 1
  funext x y
  simp [LinearMap.sum_apply]

theorem intCone_absorb {n s : ℕ} {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X)
    (hβp : ∀ i y, 0 ≤ β i y y) (hβl : φ.LinearOn β) {δ : Fin s → LinearMap.BilinForm ℤ X} (hδ : IsCone bar φ δ)
    (a : Fin n → ℕ) (b : Fin s → ℕ) (h : ∑ i, a i • β i = ∑ l, b l • δ l) (i : Fin n) (hi : 0 < a i) :
    ∃ (k : ℕ) (e : Fin s → ℕ), 0 < k ∧ k • β i = ∑ l, e l • δ l := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hδ.strict
  refine h3 (β i) (hβ i) (hβp i) ?_
  have hx1 : (ℓ (∑ i, a i • β i) : ℝ) = N * ∑ i, (a i : ℝ) * φ.evalZ (β i) := by

    rw [← intCone_evalZ_sum hβl, h, intCone_evalZ_sum hδ.linear, map_sum, Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_nsmul, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, h1]
    ring
  have hx2 : (ℓ (∑ i, a i • β i) : ℝ) = ∑ i, (a i : ℝ) * ℓ (β i) := by

    simp [map_sum, map_nsmul]
  have hle : ∀ j, (a j : ℝ) * (N * φ.evalZ (β j)) ≤ (a j : ℝ) * ℓ (β j) := fun j =>
    mul_le_mul_of_nonneg_left (h2 _ (hβ j) (hβp j)) (Nat.cast_nonneg _)
  have hsum : ∑ j, ((a j : ℝ) * ℓ (β j) - (a j : ℝ) * (N * φ.evalZ (β j))) = 0 := by
    rw [Finset.sum_sub_distrib, ← hx2, hx1, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by ring
  have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.2 (hle j))).1 hsum i (Finset.mem_univ _)
  have hai : (a i : ℝ) ≠ 0 := by exact_mod_cast hi.ne'
  have h4 : (a i : ℝ) * (ℓ (β i) - N * φ.evalZ (β i)) = 0 := by rw [mul_sub]; exact ht
  have h5 := (mul_eq_zero.1 h4).resolve_left hai
  linarith

theorem intCone_face : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X], IsPolFanOn bar φ X → ∀ (r r' : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X)
    (γ' : Fin r' → LinearMap.BilinForm ℤ X), IsCone bar φ γ → IsCone bar φ γ' → ∀ (c : Fin r → ℕ) (c' : Fin r' → ℕ),
    (∀ j, 0 < c j) → ∑ j, c j • γ j = ∑ j, c' j • γ' j → ∀ j, ∃ j', γ j = γ' j' := by
  intro O _ bar φ X _ _ _ _ r r' γ γ' hγ hγ' c c' hc he j
  obtain ⟨k, d, hk, hd⟩ := intCone_absorb hγ.mem hγ.nonneg hγ.linear hγ' c c' he j (hc j)
  have hd' : ∑ i, d i • γ' i = ∑ l, (Pi.single j k : Fin r → ℕ) l • γ l := by
    rw [← hd, Finset.sum_eq_single j (fun l _ hl => by simp [Pi.single_apply, hl]) (by simp)]
    simp
  have habs : ∀ i, 0 < d i → ∃ (k' : ℕ) (e : Fin r → ℕ), 0 < k' ∧ k' • γ' i = ∑ l, e l • γ l :=
    fun i hi => intCone_absorb hγ'.mem hγ'.nonneg hγ'.linear hγ d _ hd' i hi
  obtain ⟨f, hf⟩ := hγ.basis.exists_dual
  obtain ⟨g, hg⟩ := hγ'.basis.exists_dual
  let G : Fin r → balForms bar X := fun l => ⟨γ l, hγ.mem l⟩
  let G' : Fin r' → balForms bar X := fun i => ⟨γ' i, hγ'.mem i⟩
  have hfG : ∀ l m, f l (G m) = if l = m then 1 else 0 := hf
  have hgG : ∀ i m, g i (G' m) = if i = m then 1 else 0 := hg
  have hdG : k • G j = ∑ i, d i • G' i := Subtype.ext (by simp [G, G', hd])
  have hpos : ∀ i, 0 < d i → ∀ l, 0 ≤ f l (G' i) := by
    intro i hi l
    obtain ⟨k', e, hk', he'⟩ := habs i hi
    have h0 : k' • G' i = ∑ m, e m • G m := Subtype.ext (by simp [G, G', he'])
    have h1 := congrArg (f l) h0

    rw [map_nsmul, map_sum] at h1
    simp only [map_nsmul, hfG, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul,
      mul_one] at h1
    have hk'' : (0 : ℤ) < k' := by exact_mod_cast hk'
    by_contra hneg
    push_neg at hneg
    have : (k' : ℤ) * f l (G' i) < 0 := mul_neg_of_pos_of_neg hk'' hneg
    linarith [Int.natCast_nonneg (e l)]
  have hex : ∃ i, 0 < d i := by
    by_contra hno
    push_neg at hno
    have h0 : k • γ j = 0 := by
      rw [hd]
      exact Finset.sum_eq_zero fun i _ => by rw [Nat.le_zero.1 (hno i), zero_smul]
    refine hγ.linearIndependent.ne_zero j (LinearMap.ext₂ fun x y => ?_)
    have h1 := LinearMap.congr_fun₂ h0 x y
    simp only [LinearMap.smul_apply, LinearMap.zero_apply, nsmul_eq_mul] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (by exact_mod_cast hk.ne')
    · simpa using h2
  obtain ⟨i, hi⟩ := hex
  have hzero : ∀ l, l ≠ j → f l (G' i) = 0 := by
    intro l hl
    have h1 := congrArg (f l) hdG

    rw [map_nsmul, map_sum, hfG, if_neg hl, smul_zero] at h1
    simp only [map_nsmul, nsmul_eq_mul] at h1
    have hnn : ∀ i' ∈ Finset.univ, 0 ≤ (d i' : ℤ) * f l (G' i') := fun i' _ => by
      rcases Nat.eq_zero_or_pos (d i') with h | h
      · simp [h]
      · exact mul_nonneg (Int.natCast_nonneg _) (hpos i' h l)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h1.symm i (Finset.mem_univ _)
    exact (mul_eq_zero.1 h2).resolve_left (by exact_mod_cast hi.ne')
  obtain ⟨k', e, hk', he'⟩ := habs i hi
  have hE : k' • G' i = ∑ m, e m • G m := Subtype.ext (by simp [G, G', he'])
  have hem : ∀ m, (e m : ℤ) = k' * f m (G' i) := by
    intro m
    have h1 := congrArg (f m) hE

    rw [map_nsmul, map_sum] at h1
    simp only [map_nsmul, hfG, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul,
      mul_one] at h1
    exact h1.symm
  have hEj : k' • G' i = e j • G j := by
    rw [hE]
    refine Finset.sum_eq_single j (fun m _ hm => ?_) (by simp)
    have h1 := hem m
    rw [hzero m hm, mul_zero] at h1
    rw [show e m = 0 by exact_mod_cast h1, zero_smul]
  have h1 := congrArg (g i) hEj
  simp only [map_nsmul, hgG, if_true, nsmul_eq_mul, mul_one] at h1
  have h2 := hem j
  have hk'' : (0 : ℤ) < k' := by exact_mod_cast hk'
  have hu : f j (G' i) * g i (G j) = 1 := by
    have h3 : (k' : ℤ) * (f j (G' i) * g i (G j) - 1) = 0 := by
      rw [mul_sub, ← mul_assoc, ← h2, mul_one]
      linarith
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hk''.ne')
  have hf1 : f j (G' i) = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hu with h | h
    · exact h
    · have := Int.natCast_nonneg (e j)
      rw [h2, h] at this
      linarith
  have hej : e j = k' := by
    have := h2
    rw [hf1, mul_one] at this
    exact_mod_cast this
  rw [hej] at hEj
  refine ⟨i, LinearMap.ext₂ fun x y => ?_⟩
  have h3 := LinearMap.congr_fun₂ (congrArg Subtype.val hEj) x y
  simp only [G, G', Submodule.coe_smul, LinearMap.smul_apply, nsmul_eq_mul] at h3
  exact (mul_left_cancel₀ (by exact_mod_cast hk'.ne' : (k' : ℤ) ≠ 0) h3).symm

end IntCone

end GlobalTheory.Poinc
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.Cover

open Matrix

theorem isPosDef_toReal_of_pos {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {β : LinearMap.BilinForm ℤ X} (hs : ∀ y z, β y z = β z y) (hp : ∀ x, x ≠ 0 → 0 < β x x) :
    IsPosDef (toReal β) := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  let GZ : Matrix (Module.Free.ChooseBasisIndex ℤ X) (Module.Free.ChooseBasisIndex ℤ X) ℤ := fun i j => β (b i) (b j)
  let G : Matrix (Module.Free.ChooseBasisIndex ℤ X) (Module.Free.ChooseBasisIndex ℤ X) ℝ := GZ.map (Int.cast : ℤ → ℝ)
  have hval : ∀ v : Module.Free.ChooseBasisIndex ℤ X → ℤ,
      β (∑ i, v i • b i) (∑ i, v i • b i) = v ⬝ᵥ (GZ *ᵥ v) := fun v => by

    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, dotProduct, mulVec, GZ,
    Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hx : ∀ v : Module.Free.ChooseBasisIndex ℤ X → ℤ, v ≠ 0 → ∑ i, v i • b i ≠ 0 := fun v hv h0 =>
    hv (funext fun i => Fintype.linearIndependent_iff.1 b.linearIndependent v h0 i)
  have hcast : ∀ c : Module.Free.ChooseBasisIndex ℤ X → ℤ,
      (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ)) = ((c ⬝ᵥ (GZ *ᵥ c) : ℤ) : ℝ) := fun c => by
    simp [dotProduct, mulVec, G]
  have hG : G.IsHermitian := Matrix.IsHermitian.ext fun i j => by
    show star ((β (b j) (b i) : ℤ) : ℝ) = ((β (b i) (b j) : ℤ) : ℝ)
    rw [star_trivial, hs]
  have hpsd : G.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hG ?_
    intro x
    have hd : DenseRange (Pi.map (fun (_ : Module.Free.ChooseBasisIndex ℤ X) (q : ℚ) => (q : ℝ))) :=
      DenseRange.piMap (fun _ => Rat.denseRange_cast)
    rw [star_trivial]
    refine hd.induction_on (p := fun y => 0 ≤ y ⬝ᵥ (G *ᵥ y)) x ?_ ?_
    · refine isClosed_le continuous_const ?_
      simp only [dotProduct, mulVec]
      fun_prop
    · intro q
      obtain ⟨⟨d, hd0⟩, hq⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
      choose c hc using hq
      have hd1 : (d : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hd0
      have e : (fun i => (c i : ℝ)) = (d : ℝ) • Pi.map (fun (_ : Module.Free.ChooseBasisIndex ℤ X) (q : ℚ) => (q : ℝ)) q := by
        funext i
        have h1 : (c i : ℚ) = (d : ℚ) * q i := by simpa using hc i
        have h2 : ((c i : ℚ) : ℝ) = (((d : ℚ) * q i : ℚ) : ℝ) := by rw [h1]
        simpa using h2
      have h3 : (0 : ℝ) ≤ (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ)) := by
        rw [hcast]
        by_cases hc0 : c = 0
        · simp [hc0]
        · rw [← hval]; exact_mod_cast (hp _ (hx c hc0)).le
      rw [e, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
        ← mul_assoc] at h3
      exact (mul_nonneg_iff_of_pos_left (mul_self_pos.mpr hd1)).mp h3
  have hdef : ∀ c : Module.Free.ChooseBasisIndex ℤ X → ℝ, c ≠ 0 → 0 < c ⬝ᵥ (G *ᵥ c) := by
    intro c hc
    have h0 := hpsd.dotProduct_mulVec_nonneg c
    rw [star_trivial] at h0
    refine h0.lt_of_ne fun h1 => ?_
    have h2 : G *ᵥ c = 0 := by
      have := (hpsd.dotProduct_mulVec_zero_iff (x := c)).1
      rw [star_trivial] at this
      exact this h1.symm
    have h3 : G.det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨c, hc, h2⟩
    have h4 : GZ.det = 0 := by
      have : ((GZ.det : ℤ) : ℝ) = G.det := (Int.castRingHom ℝ).map_det GZ
      exact_mod_cast this.trans h3
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h4
    have := hp _ (hx v hv)
    rw [hval, hv0, dotProduct_zero] at this
    exact lt_irrefl _ this
  refine (isPosDef_iff_basis b _).2 fun c hc => (hdef c hc).trans_eq ?_
  have hGij : ∀ i j, G i j = ((β (b i) (b j) : ℤ) : ℝ) := fun _ _ => rfl
  simp only [dotProduct, mulVec, hGij, toReal_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.Poinc.Cover

namespace GlobalTheory.Poinc.Cover

theorem coeff_int {O : Type} [CommRing O] {bar : O → O} {X : Type} [AddCommGroup X] [Module O X] {m : ℕ}
    {γ : Fin m → LinearMap.BilinForm ℤ X} (hmem : ∀ i, γ i ∈ balForms bar X)
    (hb : IsPartOfBasis fun i => (⟨γ i, hmem i⟩ : balForms bar X)) {β : LinearMap.BilinForm ℤ X}
    (hβ : β ∈ balForms bar X) {c : Fin m → ℝ} (hs : toReal β = ∑ i, c i • toReal (γ i)) :
    ∃ n : Fin m → ℤ, ∀ i, c i = n i := by
  classical
  obtain ⟨k, bb, hbb⟩ := hb
  refine ⟨fun i => bb.coord (Sum.inl i) ⟨β, hβ⟩, fun i => ?_⟩
  let v : Option (Fin m) → balForms bar X := fun o => o.elim ⟨β, hβ⟩ fun i => ⟨γ i, hmem i⟩
  let w : Option (Fin m) → ℝ := fun o => o.elim (-1) c
  have h : ∑ o, w o • toReal ((balForms bar X).subtype (v o)) = 0 := by
    rw [Fintype.sum_option]
    simp only [w, v, Option.elim, Submodule.subtype_apply]
    rw [← hs]; simp
  have := sum_mul_eq_zero_of_sum_toReal (j := (balForms bar X).subtype) Subtype.val_injective
    (bb.coord (Sum.inl i)) h
  rw [Fintype.sum_option] at this
  simp only [w, v, Option.elim] at this
  have hc : ∀ i' : Fin m, bb.coord (Sum.inl i) ⟨γ i', hmem i'⟩ = if i' = i then 1 else 0 := fun i' => by
    rw [show (⟨γ i', hmem i'⟩ : balForms bar X) = bb (Sum.inl i') from (hbb i').symm, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h' : i' = i
    · simp [h']
    · simp [h', Ne.symm h']
  simp only [hc] at this
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at this
  linarith

theorem exists_cone : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X →
    ∀ β ∈ balForms bar X, (∀ x, x ≠ 0 → 0 < β x x) → ∃ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (k : ℕ)
      (c : Fin r → ℕ), IsCone bar φ γ ∧ 0 < k ∧ (∀ j, 0 < c j) ∧ k • β = ∑ j, c j • γ j := by
  intro O _ bar φ X _ _ _ _ _ _ hF β hβ hp
  classical
  have hB : toReal β ∈ psdCone (bar := bar) (X := X) :=
    (isPosDef_toReal_of_pos hβ.1 hp).mem_psdCone (toReal_mem hβ)
  obtain ⟨m, γ, c, hγ, hc, hsum⟩ := hF.cover _ hB
  obtain ⟨nZ, hnZ⟩ := coeff_int hγ.mem hγ.basis hβ hsum
  have hn0 : ∀ i, 0 ≤ nZ i := fun i => by exact_mod_cast (hnZ i) ▸ hc i
  let n : Fin m → ℕ := fun i => (nZ i).toNat
  have hn : ∀ i, ((n i : ℤ) : ℝ) = c i := fun i => by simp [n, Int.toNat_of_nonneg (hn0 i), hnZ i]
  have heq : β = ∑ i, n i • γ i := LinearMap.ext₂ fun a b => by
    have h1 := LinearMap.congr_fun₂ hsum a b
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, ← hn] at h1
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul]
    exact_mod_cast h1
  let S : Finset (Fin m) := Finset.univ.filter fun i => n i ≠ 0
  let e := S.orderEmbOfFin rfl
  refine ⟨S.card, fun j => γ (e j), 1, fun j => n (e j), hF.face _ _ γ e.toEmbedding hγ, one_pos,
    fun j => Nat.pos_of_ne_zero (Finset.mem_filter.1 (S.orderEmbOfFin_mem rfl j)).2, ?_⟩
  rw [one_smul, heq]
  have h2 : ∑ i ∈ S, n i • γ i = ∑ i, n i • γ i :=
    Finset.sum_filter_of_ne fun i _ h => fun h0 => h (by rw [h0, zero_smul])
  have h3 := Finset.sum_map (Finset.univ : Finset (Fin S.card)) e.toEmbedding fun i => n i • γ i
  rw [Finset.map_orderEmbOfFin_univ S rfl] at h3
  rw [← h2, h3]
  rfl

end GlobalTheory.Poinc.Cover
end
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc

theorem evalZ_eq_of_smul_eq_sum {X : Type} [AddCommGroup X] [Module.Finite ℤ X] {φ : InvFun ℤ} {m : ℕ}
    {γ : Fin m → LinearMap.BilinForm ℤ X} (h : φ.LinearOn γ) {b : LinearMap.BilinForm ℤ X} {k : ℕ} (hk : 0 < k)
    {cf : Fin m → ℕ} (he : k • b = ∑ j, cf j • γ j) : φ.evalZ b = ∑ j, ((cf j : ℝ) / k) * φ.evalZ (γ j) := by
  rw [← (linearOn_iff φ γ).1 h _ (fun j => by positivity), ← evalR_toReal]
  congr 1
  refine LinearMap.ext₂ fun x y => ?_
  have h1 := LinearMap.congr_fun₂ he x y
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul] at h1
  have h2 : (k : ℝ) * b x y = ∑ j, (cf j : ℝ) * γ j x y := by exact_mod_cast h1
  have hk' : (k : ℝ) ≠ 0 := by positivity
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul]
  rw [show ∑ j, (cf j : ℝ) / k * (γ j x y : ℝ) = (∑ j, (cf j : ℝ) * γ j x y) / k by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring, ← h2]
  field_simp

theorem polFn_eq_min_linear : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ r : ℕ, r ≤ g → ∀ (p : ℕ) (m : Fin p → ℕ) (γ : ∀ i, Fin (m i) → LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ i, IsCone id φ (γ i)) → ∃ (Nℓ : ℕ) (ℓ : Fin p → LinearMap.BilinForm ℤ (Fin r → ℤ) →ₗ[ℤ] ℤ), 0 < Nℓ ∧ ∀ b' : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) → (∃ (i : Fin p) (k : ℕ) (cf : Fin (m i) → ℕ), 0 < k ∧ k • b' = ∑ j, cf j • γ i j) → (∀ i, (Nℓ : ℝ) * φ.evalZ b' ≤ ℓ i b') ∧ ∃ i, (Nℓ : ℝ) * φ.evalZ b' = ℓ i b' := by
  intro g φ _ r _ p m γ hγ
  choose N ℓ hN h1 h2 h3 using fun i => (hγ i).strict
  refine ⟨∏ i, N i, fun i => ((∏ j ∈ Finset.univ.erase i, N j : ℕ) : ℤ) • ℓ i,
    Finset.prod_pos fun i _ => hN i, ?_⟩
  rintro b' hs hp ⟨i, k, cf, hk, he⟩
  have hb : b' ∈ balForms (id : ℤ → ℤ) (Fin r → ℤ) := mem_balForms_int.2 hs
  have key : ∀ i, ((∏ j, N j : ℕ) : ℝ) = ((∏ j ∈ Finset.univ.erase i, N j : ℕ) : ℝ) * N i := fun i => by
    rw [← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have eq : ∀ i, (N i : ℝ) * φ.evalZ b' ≤ ℓ i b' := fun i => h2 i b' hb hp
  refine ⟨fun i' => ?_, i, ?_⟩
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
    rw [key i', mul_assoc]
    exact mul_le_mul_of_nonneg_left (eq i') (by positivity)
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
    rw [key i, mul_assoc]
    congr 1
    have hev := evalZ_eq_of_smul_eq_sum (hγ i).linear hk he
    have hl : (k : ℤ) * ℓ i b' = ∑ j, (cf j : ℤ) * ℓ i (γ i j) := by
      have := congrArg (ℓ i) he

      simpa [map_sum, map_nsmul, nsmul_eq_mul] using this
    have hl' : (k : ℝ) * ℓ i b' = ∑ j, (cf j : ℝ) * ℓ i (γ i j) := by exact_mod_cast hl
    have hk' : (k : ℝ) ≠ 0 := by positivity
    rw [hev, Finset.mul_sum, show (ℓ i b' : ℝ) = (∑ j, (cf j : ℝ) * ℓ i (γ i j)) / k by
      rw [← hl']; field_simp, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h1 i j]
    field_simp

end GlobalTheory.Poinc
end
end

section

open GlobalTheory.PolFan GlobalTheory.LocM

theorem _root_.GlobalTheory.T.transport_classMinimisers_along_linearEquiv : ∀ (O : Type) [CommRing O] (X Y : Type) [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] (n N : ℕ) [NeZero N] (ebX : X ≃ₗ[ℤ] (Fin n → ℤ)) (ebY : Y ≃ₗ[ℤ] (Fin n → ℤ)) (f : X ≃ₗ[O] Y) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((ebY (μ cl) i : ℤ) : ZMod N) = cl i) → ∃ σ : Equiv.Perm (Fin n → ZMod N), (∀ cl i, ((ebX (f.symm (μ (σ cl))) i : ℤ) : ZMod N) = cl i) ∧ ∀ b : LinearMap.BilinForm ℤ Y, (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → ∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → pull f.toLinearMap b (f.symm (μ (σ cl))) (f.symm (μ (σ cl))) ≤ pull f.toLinearMap b α α := by
  first | exact @GlobalTheory.transport_minimisers | exact GlobalTheory.transport_minimisers | (intros; apply GlobalTheory.transport_minimisers <;> assumption)
end
