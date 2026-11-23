module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle052
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle064
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle065
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.diagOneUnit_conj_lifts_sl2IntReductionMod : ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ), (∀ γ : SL(2, ℤ), ∃ γ' : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u) ∧ ∀ γ' : SL(2, ℤ), ∃ γ : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u := by
  first | exact @GlobalTheory.FN.dg_conj_lift | exact GlobalTheory.FN.dg_conj_lift | (intros; apply GlobalTheory.FN.dg_conj_lift <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_slTwoPermutedModularFamily_of_level : ∀ (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ), (∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[k] γ = f) → ∃ F : GL (Fin 2) (ZMod N) → ℍ → ℂ, IsFam (gact N 1) k F ∧ (∀ γ : SL(2, ℤ), F (redGL N γ) = f ∣[k] γ) ∧ ∀ α, (∃ γ : SL(2, ℤ), α = redGL N γ) ∨ F α = 0 := by
  first | exact @GlobalTheory.FamOfLevel.exists_family | exact GlobalTheory.FamOfLevel.exists_family | (intros; apply GlobalTheory.FamOfLevel.exists_family <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory

open TensorProduct

theorem tensor_padic_cls_eq {G : Type} [CommGroup G] (l : ℕ) [Fact l.Prime] (n : ℕ) (f f' : G)
    (h : ((1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul f' - (1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul f) ∈
      ((Ideal.span {(l : ℤ_[l])}) ^ n • (⊤ : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] Additive G)))) :
    ∃ u : G, f' = f * u ^ (l ^ n) := by
  classical
  let M := Additive G
  let ψ : M →ₗ[ℤ] M := {
    toFun := fun x : M => (((l : ℤ) ^ n) • x)
    map_add' := fun x y => by simp
    map_smul' := fun (k : ℤ) x => by simp [smul_smul, mul_comm]
  }
  let P : Submodule ℤ M := LinearMap.range ψ
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hkill : ∀ q : M ⧸ P, (l ^ n) • q = 0 := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨m, by change ((l : ℤ) ^ n) • m = l ^ n • m; rw [← Nat.cast_pow, natCast_zsmul]⟩
  letI : Module (ZMod (l ^ n)) (M ⧸ P) := AddCommGroup.zmodModule hkill
  let B : ℤ_[l] →ₗ[ℤ] M →ₗ[ℤ] M ⧸ P :=
    LinearMap.mk₂ ℤ (fun c m => (PadicInt.toZModPow n c) • P.mkQ m)
      (fun c c' m => by simp [add_smul])
      (fun k c m => by
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod (l ^ n)), ← Int.cast_smul_eq_zsmul (ZMod (l ^ n)),
          smul_smul, smul_eq_mul])
      (fun c m m' => by simp [smul_add])
      (fun k c m => by
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod (l ^ n)), ← Int.cast_smul_eq_zsmul (ZMod (l ^ n)),
          smul_smul, smul_smul, mul_comm])
  let φ : ℤ_[l] ⊗[ℤ] M →ₗ[ℤ] M ⧸ P := TensorProduct.lift B
  have hφ : ∀ c m, φ (c ⊗ₜ m) = (PadicInt.toZModPow n c) • P.mkQ m := fun c m => by
    exact TensorProduct.lift.tmul (f' := B) c m
  have hI : (Ideal.span {(l : ℤ_[l])}) ^ n = RingHom.ker (PadicInt.toZModPow (p := l) n) := by
    rw [PadicInt.ker_toZModPow, Ideal.span_singleton_pow]
  have hzero : ∀ x ∈ ((Ideal.span {(l : ℤ_[l])}) ^ n • (⊤ : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] M))), φ x = 0 := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero])
    rw [hI, RingHom.mem_ker] at hr
    clear hy
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c m =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, hφ, map_mul, hr, zero_mul, zero_smul]
    | add a b ha hb => rw [smul_add, map_add (f := _), ha, hb, add_zero]
  have h0 := hzero _ h
  rw [map_sub, hφ, hφ, map_one, one_smul, one_smul, sub_eq_zero, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq] at h0
  obtain ⟨y, hy⟩ := h0
  refine ⟨Additive.toMul y, ?_⟩
  have hy' : Additive.toMul (((l : ℤ) ^ n) • y) = f' / f := by
    have hy2 : ((l : ℤ) ^ n) • y = Additive.ofMul f' - Additive.ofMul f := hy
    rw [hy2]; rfl
  rw [toMul_zsmul] at hy'
  rw [← div_eq_iff_eq_mul', ← hy']
  norm_cast

theorem Tower.cls_eq_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (n : ℕ) (f f' : X.Kˣ) (h : X.cls l n f = X.cls l n f') :
    ∃ u : X.Kˣ, (f' : X.K) = f * (u : X.K) ^ (l ^ n) := by
  unfold Tower.cls at h
  rw [Submodule.Quotient.eq'] at h
  obtain ⟨u, hu⟩ := tensor_padic_cls_eq l n f f' (by simpa [neg_add_eq_sub] using h)
  exact ⟨u, by rw [hu]; push_cast; rfl⟩

end GlobalTheory
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate

theorem _root_.GlobalTheory.T.latticeFunctionDivisibleFirst_substitution : ∀ (N l : ℕ) (ν : DirichletCharacter ℂ N) (φ : ZMod l → ℂ) (a b c d : ℤ),
    (N : ℤ) * a * d - l * b * c = 1 → 0 < N → 0 < l → ∀ y : ℤ × ℤ,
    (if (N : ℤ) ∣ y.1 then latF l (ch ν) φ (y.1 / N * (N * d) - y.2 * (l * c), -(y.1 / N * b) + y.2 * a) else 0) =
      latF (N * l) (fun _ => 1) (fun z => ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) z) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) z)) y := by
  first | exact @GlobalTheory.latF_rows_subst | exact GlobalTheory.latF_rows_subst | (intros; apply GlobalTheory.latF_rows_subst <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.character_average_twistedSpan_eq_zero : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ → ∀ u ∈ aug π H θ, ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ j ∈ R, j ∈ H) ∧ ∑ j ∈ R, (θ j)⁻¹ • π j u = 0 := by
  first | exact @GlobalTheory.PsType.aug_avg_zero | exact GlobalTheory.PsType.aug_avg_zero | (intros; apply GlobalTheory.PsType.aug_avg_zero <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.exists_character_average_eigenvector_compact_subgroup : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ → ∀ w : V, ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ j ∈ R, j ∈ H) ∧ IsEig π H θ (∑ j ∈ R, (θ j)⁻¹ • π j w) := by
  first | exact @GlobalTheory.PsType.avg_eig | exact GlobalTheory.PsType.avg_eig | (intros; apply GlobalTheory.PsType.avg_eig <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.twistedJacquet_survival_product_of_two_groups : ∀ (G₁ G₂ V : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G₁ × G₂) V), IsSmooth ρ → ∀ (U₁ : Subgroup G₁) (U₂ : Subgroup G₂) (J₁ : Set G₁) (J₂ : Set G₂) (θ₁ : G₁ → ℂ) (θ₂ : G₂ → ℂ), (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G₁ W), IsSmooth σ → ∀ w ∈ twKer σ U₁ 1, IsEig σ J₁ θ₁ w → w = 0) → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G₂ W), IsSmooth σ → ∀ w ∈ twKer σ U₂ 1, IsEig σ J₂ θ₂ w → w = 0) → ∀ v ∈ twKer (ρ.comp (MonoidHom.inl G₁ G₂)) U₁ 1 ⊔ twKer (ρ.comp (MonoidHom.inr G₁ G₂)) U₂ 1, IsEig (ρ.comp (MonoidHom.inl G₁ G₂)) J₁ θ₁ v → IsEig (ρ.comp (MonoidHom.inr G₁ G₂)) J₂ θ₂ v → v = 0 := by
  first | exact @GlobalTheory.PsType.eq_zero_of_mem_sup_twKer_prod | exact GlobalTheory.PsType.eq_zero_of_mem_sup_twKer_prod | (intros; apply GlobalTheory.PsType.eq_zero_of_mem_sup_twKer_prod <;> assumption)
end
