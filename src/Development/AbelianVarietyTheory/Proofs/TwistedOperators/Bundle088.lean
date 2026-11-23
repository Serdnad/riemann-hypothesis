module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitSubtorusOfIdempotentFamily
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupCommutantScalars
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle080
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle079
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.split_subtorus_of_idempotent_family : GlobalTheory.RegSS.SubtorusOfIdempotents := by
  first | exact @GlobalTheory.RegSS.IdemTorus.subtorusOfIdempotents | exact GlobalTheory.RegSS.IdemTorus.subtorusOfIdempotents | (intros; apply GlobalTheory.RegSS.IdemTorus.subtorusOfIdempotents <;> assumption)
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.unitaryGroup_commutant_scalars : GlobalTheory.RegSS.UnitaryCommutant := by
  first | exact @GlobalTheory.RegSS.unitaryCommutant | exact GlobalTheory.RegSS.unitaryCommutant | (intros; apply GlobalTheory.RegSS.unitaryCommutant <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.jordanHolder_mult_normalised_induction_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] [LinearOrder β] (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) (W W₁ W₂ : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂] (π : Representation ℂ (∀ i, GlobalTheory.SmGL.Levi k (c i)) W) (π₁ : Representation ℂ (∀ i, GlobalTheory.SmGL.Levi k (c i)) W₁) (π₂ : Representation ℂ (∀ i, GlobalTheory.SmGL.Levi k (c i)) W₂) (ι : π₁.IntertwiningMap π) (p : π.IntertwiningMap π₂), Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) → (∀ v, p v = 0 → ∃ u, ι u = v) → GlobalTheory.PRep.IsSmooth π → ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (GlobalTheory.SmGL.Levi k m) Y), τ.IsIrreducible → GlobalTheory.SmGL.jhMult τ (GlobalTheory.SmGL.relInd f π) = GlobalTheory.SmGL.jhMult τ (GlobalTheory.SmGL.relInd f π₁) + GlobalTheory.SmGL.jhMult τ (GlobalTheory.SmGL.relInd f π₂) := by
  first | exact @GlobalTheory.SmGL.IndExact.jhMult_relInd_exact | exact GlobalTheory.SmGL.IndExact.jhMult_relInd_exact | (intros; apply GlobalTheory.SmGL.IndExact.jhMult_relInd_exact <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section
namespace GlobalTheory.ReindexTorus

def reindexGL (k : Type) [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (σ : n ≃ n') : GL n k ≃* GL n' k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k σ).toMulEquiv

theorem val_reindexGL (k : Type) [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (σ : n ≃ n') (g : GL n k) : (reindexGL k σ g).val = Matrix.reindex σ σ g.val := rfl

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem map_reindexGL_KO (σ : n ≃ n') : (KO k n).map (reindexGL k σ).toMonoidHom = KO k n' := by
  ext x
  rw [Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap, GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.SplitFlip.mem_KO_iff]
  have h1 : ∀ i j, ((reindexGL k σ).symm x).val i j = x.val (σ i) (σ j) := fun i j => rfl
  have h2 : ∀ i j, (((reindexGL k σ).symm x)⁻¹).val i j = (x⁻¹).val (σ i) (σ j) := fun i j => by
    rw [← map_inv]; rfl
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, h1, h2]
  exact and_congr ⟨fun h i j => by simpa using h (σ.symm i) (σ.symm j), fun h i j => h _ _⟩
    ⟨fun h i j => by simpa using h (σ.symm i) (σ.symm j), fun h i j => h _ _⟩

theorem reindexGL_torusElt (σ : n ≃ n') (ϖ : kˣ) (e : n → ℤ) :
    reindexGL k σ (torusElt k n ϖ e) = torusElt k n' ϖ (e ∘ σ.symm) := by
  refine Units.ext ?_
  rw [val_reindexGL, val_torusElt, val_torusElt, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
  rfl

theorem relIndex_conj_torusElt_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (σ : n ≃ n') (e : n → ℤ),
    ((KO k n').map (MulAut.conj (torusElt k n' ϖ (e ∘ σ.symm))).toMonoidHom).relIndex (KO k n') =
      ((KO k n).map (MulAut.conj (torusElt k n ϖ e)).toMonoidHom).relIndex (KO k n) := by
  intro k _ _ _ _ ϖ n n' _ _ _ _ σ e
  set φ := reindexGL k σ
  have hconj : ∀ g : GL n k, ∀ H : Subgroup (GL n k),
      (H.map (MulAut.conj g).toMonoidHom).map φ.toMonoidHom =
        (H.map φ.toMonoidHom).map (MulAut.conj (φ g)).toMonoidHom := by
    intro g H
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x : 1
    simp [φ, map_mul, map_inv]
  have hK := map_reindexGL_KO k σ
  rw [← reindexGL_torusElt k σ ϖ e, ← hK, ← hconj]
  have key : ∀ A B : Subgroup (GL n k), (A.map φ.toMonoidHom).relIndex (B.map φ.toMonoidHom) = A.relIndex B := by
    intro A B
    rw [Subgroup.map_equiv_eq_comap_symm' φ A, Subgroup.relIndex_comap, Subgroup.map_map]
    have : (φ.symm.toMonoidHom.comp φ.toMonoidHom) = MonoidHom.id _ := by ext x : 1; simp
    rw [this, Subgroup.map_id]
  exact key _ _

end GlobalTheory.ReindexTorus
end
end

section

set_option autoImplicit false

noncomputable section

open IsDedekindDomain IsLocalRing Formalism.L2.Pj

namespace GlobalTheory.CompleteValExt

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem exists_algebraMap_eq_iff (x : K) : (∃ a : V, algebraMap V K a = x) ↔ 0 ≤ vV V x := by
  by_cases hx : x = 0
  · subst hx
    exact ⟨fun _ => by simp [vV], fun _ => ⟨0, map_zero _⟩⟩
  have h1 := WithZero.log_le_log (valV_ne_zero (V := V) hx) one_ne_zero
  rw [WithZero.log_one] at h1
  have h2 : 0 ≤ vV V x ↔ valV V x ≤ 1 := by
    rw [← h1]
    unfold vV
    omega
  rw [h2]
  refine ⟨?_, fun h => IsDiscreteValuationRing.exists_lift_of_le_one (A := V) (K := K) h⟩
  rintro ⟨a, rfl⟩
  exact HeightOneSpectrum.valuation_le_one _ a

variable {W L : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L]
  [IsFractionRing W L]

theorem finite_and_integral_of_scale [IsAdicComplete (maximalIdeal V) V] (i : K →+* L) {r : ℕ} (hr : 0 < r)
    (hi : ∀ z, vV W (i z) = (r : ℤ) * vV V z) (h' : Finite (ResidueField W)) :
    i.Finite ∧ ∀ b : W, (i.comp (algebraMap V K)).IsIntegralElem (algebraMap W L b) := by
  have hint : ∀ a : V, ∃ v : W, algebraMap W L v = i (algebraMap V K a) := fun a =>
    (exists_algebraMap_eq_iff _).2 (by
      rw [hi]; exact mul_nonneg (by positivity) ((exists_algebraMap_eq_iff _).1 ⟨a, rfl⟩))
  choose g0 hg0 using hint
  have hinj := IsFractionRing.injective W L
  let g : V →+* W :=
    { toFun := g0
      map_one' := hinj (by simp [hg0])
      map_mul' := fun a b => hinj (by simp [hg0])
      map_zero' := hinj (by simp [hg0])
      map_add' := fun a b => hinj (by simp [hg0]) }
  have hg : ∀ a, algebraMap W L (g a) = i (algebraMap V K a) := hg0
  letI : Algebra V W := g.toAlgebra
  letI : Algebra K L := i.toAlgebra
  letI : Algebra V L := (i.comp (algebraMap V K)).toAlgebra
  have : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq fun a => (hg a).symm
  have : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hgi : Function.Injective (algebraMap V W) := fun a b hab => by
    apply IsFractionRing.injective V K
    apply i.injective
    rw [← hg, ← hg]
    exact congrArg _ hab
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hgi
  have hle : (maximalIdeal V).map (algebraMap V W) ≤ maximalIdeal W := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_maximalIdeal]
    intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hb' : i (algebraMap V K a) * algebraMap W L b = 1 := by
      rw [← hg, ← map_mul, ← map_one (algebraMap W L)]
      exact congrArg _ hb
    have h0 : algebraMap V K a ≠ 0 := fun h => by
      rw [h, map_zero, zero_mul] at hb'
      exact zero_ne_one hb'
    have h1 : algebraMap W L b = i (algebraMap V K a)⁻¹ := by
      rw [map_inv₀]
      exact eq_inv_of_mul_eq_one_right hb'
    have h2 := (exists_algebraMap_eq_iff (V := W) _).1 ⟨b, h1⟩
    rw [hi] at h2
    obtain ⟨c, hc⟩ := (exists_algebraMap_eq_iff (V := V) _).2
      (nonneg_of_mul_nonneg_right h2 (by exact_mod_cast hr))
    refine (mem_maximalIdeal a).1 ha (IsUnit.of_mul_eq_one c (IsFractionRing.injective V K ?_))
    rw [map_mul, hc, map_one, mul_inv_cancel₀ h0]
  have hne : (maximalIdeal V).map (algebraMap V W) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective hgi]
    exact IsDiscreteValuationRing.not_a_field V
  have htop : (maximalIdeal V).map (algebraMap V W) ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal W).ne_top hle
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have : Finite (W ⧸ maximalIdeal W) := h'
  have : Module.Finite V W := GlobalTheory.finite_of_forall_prime_mem hϖ.ne_zero (fun P hP h0 => by
    rw [eq_maximalIdeal (hP.isMaximal h0)]
    exact hϖ.not_isUnit) hne htop
  refine ⟨Module.Finite.of_isLocalization V W (nonZeroDivisors V), fun b => ?_⟩
  exact (Algebra.IsIntegral.isIntegral (R := V) b).algebraMap (B := L)

theorem finite_and_integral : ∀ (T T' : CDVR) (i : T.Fr →+* T'.Fr) (r : ℕ), 0 < r →
    (∀ a : T.Fr, vV T'.V (i a) = (r : ℤ) * vV T.V a) → T'.FinRes →
    i.Finite ∧ ∀ b : T'.V, (i.comp (algebraMap T.V T.Fr)).IsIntegralElem (algebraMap T'.V T'.Fr b) :=
  fun T T' i _ hr hi h' => finite_and_integral_of_scale (V := T.V) (W := T'.V) i hr hi h'

end GlobalTheory.CompleteValExt
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Host

theorem _root_.GlobalTheory.T.heckeChar_local_value_div_uniformiser_pow : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L), ∃ N : ℕ, 0 < N ∧ ∀ (w : HeightOneSpectrum (𝓞 L)) (x : (w.adicCompletion L)ˣ), ∃ a : ℤ, ((χ.loc w x / χ.val w ^ a : ℂˣ) : ℂ) ^ N = 1 := by
  first | exact @GlobalTheory.HeckeLocDec.loc_div_val_pow | exact GlobalTheory.HeckeLocDec.loc_div_val_pow | (intros; apply GlobalTheory.HeckeLocDec.loc_div_val_pow <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host

theorem _root_.GlobalTheory.T.heckeChar_uniformiser_value_isAlgebraic : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (m : (L →+* ℂ) → ℤ), (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ m φ) → ∀ w : HeightOneSpectrum (𝓞 L), IsAlgebraic ℚ ((χ.val w : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.heckeChar_val_isAlgebraic | exact GlobalTheory.heckeChar_val_isAlgebraic | (intros; apply GlobalTheory.heckeChar_val_isAlgebraic <;> assumption)
end
