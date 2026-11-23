module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2059
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2070
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle250
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

namespace GlobalTheory.FrameExt

theorem idem_factor {K : Type} [Field K] {n : ℕ} (Q : Matrix (Fin n) (Fin n) K) (hQ : Q * Q = Q) :
    ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) K) (C : Matrix (Fin m) (Fin n) K), Z * C = Q ∧ C * Z = 1 := by
  let W := LinearMap.range Q.mulVecLin
  let b := Module.finBasis K W
  have key : ∀ w : W, Q.mulVecLin.rangeRestrict (w : Fin n → K) = w := by
    rintro ⟨w, v, rfl⟩
    apply Subtype.ext
    simp [Matrix.mulVec_mulVec, hQ]
  refine ⟨Module.finrank K W, LinearMap.toMatrix' (W.subtype ∘ₗ b.equivFun.symm.toLinearMap),
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ Q.mulVecLin.rangeRestrict), ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]
    have : (W.subtype ∘ₗ b.equivFun.symm.toLinearMap) ∘ₗ (b.equivFun.toLinearMap ∘ₗ Q.mulVecLin.rangeRestrict)
        = Q.mulVecLin := LinearMap.ext fun v => by simp
    rw [this, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  · rw [← LinearMap.toMatrix'_comp]
    have : (b.equivFun.toLinearMap ∘ₗ Q.mulVecLin.rangeRestrict) ∘ₗ (W.subtype ∘ₗ b.equivFun.symm.toLinearMap)
        = LinearMap.id := LinearMap.ext fun c => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype, key,
        LinearEquiv.apply_symm_apply, LinearMap.id_apply]
    rw [this, LinearMap.toMatrix'_id]

end GlobalTheory.FrameExt

theorem GlobalTheory.FrameExt.exists_fr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ := by
  intro F E _ _ _ _ _ σ n J r X Y hcm hJ hW
  have hσ : ∀ e, σ (σ e) = e := fun e => GlobalTheory.SiegelSet.sigma_sigma (σ := σ) hcm e
  have ccT : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) E), cT (σ : E →+* E) (cT (σ : E →+* E) M) = M :=
    fun M => Matrix.ext fun i j => by simp [Formalism.UG.cT, hσ]
  have cT0 : ∀ {p q : ℕ}, cT (σ : E →+* E) (0 : Matrix (Fin p) (Fin q) E) = 0 :=
    Matrix.ext fun i j => by simp [Formalism.UG.cT]
  have hJJ : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  have hBX : cT (σ : E →+* E) Y * J * X = 1 := GlobalTheory.StdPar.yx hcm hJ hW
  obtain ⟨A, hA⟩ : ∃ A, A = cT (σ : E →+* E) X * J := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = cT (σ : E →+* E) Y * J := ⟨_, rfl⟩
  have hAX : A * X = 0 := by rw [hA]; exact hW.xx
  have hAY : A * Y = 1 := by rw [hA]; exact hW.xy
  have hBY : B * Y = 0 := by rw [hB]; exact hW.yy
  have hBX' : B * X = 1 := by rw [hB]; exact hBX
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 1 - X * B - Y * A := ⟨_, rfl⟩
  have hAQ : A * Q = 0 := by
    rw [hQ, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAX, hAY]
    simp
  have hBQ : B * Q = 0 := by
    rw [hQ, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBX', hBY]
    simp
  have hQQ : Q * Q = Q := by
    calc Q * Q = (1 - X * B - Y * A) * Q := by rw [← hQ]
      _ = Q - X * (B * Q) - Y * (A * Q) := by
        rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = Q := by rw [hBQ, hAQ]; simp
  obtain ⟨m, Z, C, hZC, hCZ⟩ := GlobalTheory.FrameExt.idem_factor Q hQQ
  have hQZ : Q * Z = Z := by rw [← hZC, Matrix.mul_assoc, hCZ, Matrix.mul_one]
  have hAZ : A * Z = 0 := by rw [← hQZ, ← Matrix.mul_assoc, hAQ, Matrix.zero_mul]
  have hBZ : B * Z = 0 := by rw [← hQZ, ← Matrix.mul_assoc, hBQ, Matrix.zero_mul]

  have hzc : cT (σ : E →+* E) Z * J * X = 0 := by
    have := congrArg (cT (σ : E →+* E)) hAZ
    rwa [hA, Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, cT0, ← Matrix.mul_assoc] at this
  have hzd : cT (σ : E →+* E) Z * J * Y = 0 := by
    have := congrArg (cT (σ : E →+* E)) hBZ
    rwa [hB, Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, cT0, ← Matrix.mul_assoc] at this
  obtain ⟨J₀, hJ₀⟩ : ∃ J₀, J₀ = cT (σ : E →+* E) Z * J * Z := ⟨_, rfl⟩
  have hJ₀h : cT (σ : E →+* E) J₀ = J₀ := by
    rw [hJ₀, Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, Matrix.mul_assoc]
  have key : cT (σ : E →+* E) Z * J = J₀ * C := by
    calc cT (σ : E →+* E) Z * J = cT (σ : E →+* E) Z * J * (X * B + Y * A + Z * C) := by
          rw [hZC, hQ]; simp
      _ = cT (σ : E →+* E) Z * J * X * B + cT (σ : E →+* E) Z * J * Y * A + J₀ * C := by
          rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ₀]
      _ = J₀ * C := by rw [hzc, hzd]; simp
  have hJZ : J * Z = cT (σ : E →+* E) C * J₀ := by
    have := congrArg (cT (σ : E →+* E)) key
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, hJ₀h] at this
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
  have hZ : Z = J⁻¹ * (cT (σ : E →+* E) C * J₀) := by
    rw [← hJZ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJu, Matrix.one_mul]
  have hdet₀ : J₀.det ≠ 0 := by
    refine Matrix.det_ne_zero_of_left_inverse (B := C * J⁻¹ * cT (σ : E →+* E) C) ?_
    rw [← hCZ, hZ]; simp only [Matrix.mul_assoc]
  have hJ₀u : IsUnit J₀.det := isUnit_iff_ne_zero.mpr hdet₀
  refine ⟨m, Z, J₀, ⟨hcm, hJ, ⟨fun i j => ?_, hdet₀⟩, hW.xx, hW.yy, hW.xy, hBX, ?_, ?_, hzc, hzd, hJ₀.symm, ?_, ?_⟩⟩
  · have := congrFun (congrFun hJ₀h i) j
    simpa [Formalism.UG.cT] using this
  · rw [← hA]; exact hAZ
  · rw [← hB]; exact hBZ
  · rw [← hA, ← hB, key, ← Matrix.mul_assoc J₀⁻¹, Matrix.nonsing_inv_mul _ hJ₀u, Matrix.one_mul, hZC, hQ]
    abel
  · have htr : (1 : Matrix (Fin n) (Fin n) E).trace = (X * B).trace + (Y * A).trace + (Z * C).trace := by
      rw [← Matrix.trace_add, ← Matrix.trace_add, hZC, hQ]; congr 1; abel
    rw [Matrix.trace_mul_comm X B, hBX', Matrix.trace_mul_comm Y A, hAY, Matrix.trace_mul_comm Z C, hCZ] at htr
    simp only [Matrix.trace_one, Fintype.card_fin] at htr
    have h3 : ((m + 2 * (r + 1) : ℕ) : E) = ((n : ℕ) : E) := by push_cast at htr ⊢; rw [htr]; ring
    exact Nat.cast_injective h3
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.InvTame

open Filter
open scoped Classical

theorem isTame_inv : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ A : Fn F n d →ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), A (e Φ) = Φ) → IsTame F A := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE hbij A hA g hg
  obtain ⟨m, c, φ, hφ, hstd, rfl⟩ := GlobalTheory.MixEvAdm.sb_decomp F (Fin n × Fin d) g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  have hbi : Function.Bijective ei :=
    ⟨GlobalTheory.T.weil_eigen_injective_extends F E σ B n d X W M M₁ hP.good e hbij.injOn ei ev (fun v => (hev v).1) hloc,
      GlobalTheory.T.weil_eigen_surjective_extends F E σ B n d X W M M₁ hP.good hM₁ e hbij.surjOn ei ev hev hloc⟩
  obtain ⟨S, hS⟩ := GlobalTheory.T.schwartz_bijection_right_inverse _ _ ei hbi
  have hpre : ∀ j v, ∃ ψ ∈ SB (Fin n × Fin d → Fv F v), ev v ψ = φ j v ∧ (φ j v = M₁.vac v → ψ = M.vac v) := by
    intro j v
    by_cases h : φ j v = M₁.vac v
    · exact ⟨M.vac v, (hP.good.vac v).1, (hev v).1.trans h.symm, fun _ => rfl⟩
    · have h2 : φ j v ∈ (SB (Fin n × Fin d → Fv F v)).map (ev v) := (hev v).2.symm ▸ hφ j v
      obtain ⟨ψ, hψ, hψe⟩ := Submodule.mem_map.1 h2
      exact ⟨ψ, hψ, hψe, fun h' => (h h').elim⟩
  choose ψ hψSB hψev hψvac using hpre
  have hψfam : ∀ j, ∀ᶠ v in cofinite, ψ j v = M.vac v := fun j =>
    ((hstd j).and hM₁.std).mono fun v hv => hψvac j v (hv.1.trans hv.2.symm)
  have hψstd : ∀ j, ∀ᶠ v in cofinite,
      ψ j v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun j =>
    ((hψfam j).and hP.good.std).mono fun v hv => hv.1.trans hv.2
  have hG : ∀ j, (fun y : Fin n × Fin d → Af F => ∏ᶠ v, ψ j v fun i => evalV F v (y i)) ∈
      SB (Fin n × Fin d → Af F) := fun j =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB j) (hψstd j),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB j) (hψstd j)⟩
  refine ⟨Fin m, inferInstance, fun j => c j • S, fun j y => ∏ᶠ v, ψ j v fun i => evalV F v (y i), hG, fun f => ?_⟩
  have hsplit : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
      (∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => evalV F v (y i)) =
      ∑ j, c j • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) := by
    funext x
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm]
    rfl
  have hφe : ∀ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) =
      e (pureA F ((S f : SInf F _) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
        (fun y => ∏ᶠ v, ψ j v fun i => evalV F v (y i))) := by
    intro j
    have h1 := hloc (S f) (ψ j) (hψSB j) (hψfam j)
    rw [hS] at h1
    have h2 : (fun v => ev v (ψ j v)) = φ j := funext fun v => hψev j v
    rw [h2] at h1
    exact h1.symm

  rw [hsplit, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hφe j, hA _ (Submodule.subset_span ⟨S f, _, hG j, rfl⟩)]
  funext x
  simp [pureA, mul_assoc]

end GlobalTheory.InvTame
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.EvSymmTame

open Filter
open scoped Classical

theorem isTame_symm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood B.ψ → M₁.IsGood B.ψ →
    ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e →
    Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ T : Fn F n d ≃ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ = e Φ) → IsTame F T.symm.toLinearMap := by
  intro F E _ _ _ _ _ σ B n d X W M M₁ hM hM₁ e hE hbij T hT g hg
  have hA : ∀ Φ ∈ schA F (Fin n × Fin d), T.symm (e Φ) = Φ := fun Φ hΦ => by
    rw [← hT Φ hΦ, LinearEquiv.symm_apply_apply]
  obtain ⟨m, c, φ, hφ, hstd, rfl⟩ := GlobalTheory.MixEvAdm.sb_decomp F (Fin n × Fin d) g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  have hbi : Function.Bijective ei :=
    ⟨GlobalTheory.T.weil_eigen_injective_extends F E σ B n d X W M M₁ hM e hbij.injOn ei ev (fun v => (hev v).1) hloc,
      GlobalTheory.ArchSurj.surjective_arch F E σ B n d X W M M₁ hM hM₁ e hbij.surjOn ei ev hev hloc⟩
  obtain ⟨S, hS⟩ := GlobalTheory.T.schwartz_bijection_right_inverse _ _ ei hbi
  have hpre : ∀ j v, ∃ ψ ∈ SB (Fin n × Fin d → Fv F v), ev v ψ = φ j v ∧ (φ j v = M₁.vac v → ψ = M.vac v) := by
    intro j v
    by_cases h : φ j v = M₁.vac v
    · exact ⟨M.vac v, (hM.vac v).1, (hev v).1.trans h.symm, fun _ => rfl⟩
    · have h2 : φ j v ∈ (SB (Fin n × Fin d → Fv F v)).map (ev v) := (hev v).2.symm ▸ hφ j v
      obtain ⟨ψ, hψ, hψe⟩ := Submodule.mem_map.1 h2
      exact ⟨ψ, hψ, hψe, fun h' => (h h').elim⟩
  choose ψ hψSB hψev hψvac using hpre
  have hψfam : ∀ j, ∀ᶠ v in cofinite, ψ j v = M.vac v := fun j =>
    ((hstd j).and hM₁.std).mono fun v hv => hψvac j v (hv.1.trans hv.2.symm)
  have hψstd : ∀ j, ∀ᶠ v in cofinite,
      ψ j v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun j =>
    ((hψfam j).and hM.std).mono fun v hv => hv.1.trans hv.2
  have hG : ∀ j, (fun y : Fin n × Fin d → Af F => ∏ᶠ v, ψ j v fun i => evalV F v (y i)) ∈
      SB (Fin n × Fin d → Af F) := fun j =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB j) (hψstd j),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB j) (hψstd j)⟩
  refine ⟨Fin m, inferInstance, fun j => c j • S, fun j y => ∏ᶠ v, ψ j v fun i => evalV F v (y i), hG, fun f => ?_⟩
  have hsplit : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
      (∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => evalV F v (y i)) =
      ∑ j, c j • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) := by
    funext x
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm]
    rfl
  have hφe : ∀ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) =
      e (pureA F ((S f : SInf F _) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
        (fun y => ∏ᶠ v, ψ j v fun i => evalV F v (y i))) := by
    intro j
    have h1 := hloc (S f) (ψ j) (hψSB j) (hψfam j)
    rw [hS] at h1
    have h2 : (fun v => ev v (ψ j v)) = φ j := funext fun v => hψev j v
    rw [h2] at h1
    exact h1.symm

  rw [LinearEquiv.coe_toLinearMap, hsplit, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hφe j, hA _ (Submodule.subset_span ⟨S f, _, hG j, rfl⟩)]
  funext x
  simp [pureA, mul_assoc]

end GlobalTheory.EvSymmTame
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.IntertwLocal.local_intertw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ (v : Pl (F := F)) (x : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (φ φ₁ φ₂ φ₃ φ₄ : (Fin n × Fin d → Fv F v) → ℂ), φ ∈ SB (Fin n × Fin d → Fv F v) → φ₁ ∈ SB (Fin n × Fin d → Fv F v) →
    φ₂ ∈ SB (Fin n × Fin d → Fv F v) → Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁ → Acts (evFin F v) (om x) φ φ₂ →
    Acts (evFin F v) (om x) φ₁ φ₃ → Acts (evFin F v) (M.co.rho B.ψ (mat x.1 * u * (mat x.2)ᵀ)) φ₂ φ₄ → φ₄ = φ₃ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v x u φ φ₁ φ₂ φ₃ φ₄ hφ hφ₁ hφ₂ h1 h2 h3 h4
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin n × Fin d) v
  have hΦ : tens (evFin F v) φ R ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) := (hR φ hφ).2
  have himpl := hW.impl x u (tens (evFin F v) φ R) hΦ
  have hact : GlobalTheory.WeilM.actAB (cA σ) x u = mat x.1 * u * (mat x.2)ᵀ := rfl
  rw [hact] at himpl
  have key : tens (evFin F v) φ₄ R = tens (evFin F v) φ₃ R := by
    rw [← h4 R (hR φ₂ hφ₂), ← h2 R (hR φ hφ), ← himpl, h1 R (hR φ hφ), h3 R (hR φ₁ hφ₁)]
  funext t
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
    intro u' hu'; funext i; exact GlobalTheory.LatVac.at_liftV v _ u' hu'
  have hRz : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
    simpa using (hR φ hφ).1 0 _ hz
  have := congrFun key (fun i => GlobalTheory.LatVac.liftV v (t i))
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hRz] at this
  exact mul_right_cancel₀ hR0 this
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.FunObj.SqNum GlobalTheory.NormSum

noncomputable section

namespace GlobalTheory.LevelRed

open GlobalTheory.BotPairSmall.BlockIdx

variable (D : D7) (𝔪 : Ideal (𝓞 D.host.E))

theorem mk_eq_iff (h𝔪 : 𝔪 ≠ ⊥) (r b : 𝓞 D.host.E) :
    Ideal.Quotient.mk 𝔪 r = Ideal.Quotient.mk 𝔪 b ↔
      inc D (r : D.host.E) - inc D (b : D.host.E) ∈ hatId D 𝔪 := by
  have e : inc D (r : D.host.E) - inc D (b : D.host.E) = inc D ((r - b : 𝓞 D.host.E) : D.host.E) := by
    push_cast
    rw [map_sub]
  rw [Ideal.Quotient.eq, e]
  constructor
  · intro h
    simpa using gen_mem_hatId D 𝔪 h (one_mem (OhE D))
  · intro h
    obtain ⟨c, hc, e'⟩ := (FractionalIdeal.mem_coeIdeal _).1 (GlobalTheory.HeisTranslate.mem_of_inc_mem_hatId h𝔪 h)
    have : c = r - b := RingOfIntegers.coe_injective e'
    exact this ▸ hc

theorem exists_redHom (h𝔪 : 𝔪 ≠ ⊥) : ∃ red : OhE D →+* 𝓞 D.host.E ⧸ 𝔪, ∀ (x : OhE D) (b : 𝓞 D.host.E),
    red x = Ideal.Quotient.mk 𝔪 b ↔ (x : AE D) - inc D (b : D.host.E) ∈ hatId D 𝔪 := by
  choose r hr using fun x : OhE D => exists_red D 𝔪 h𝔪 (x : AE D) x.2
  have key : ∀ (x : OhE D) (b : 𝓞 D.host.E), Ideal.Quotient.mk 𝔪 (r x) = Ideal.Quotient.mk 𝔪 b ↔
      (x : AE D) - inc D (b : D.host.E) ∈ hatId D 𝔪 := by
    intro x b
    rw [mk_eq_iff D 𝔪 h𝔪]
    constructor
    · intro h
      have := add_mem (hr x) h
      rwa [sub_add_sub_cancel] at this
    · intro h
      have := sub_mem h (hr x)
      rwa [sub_sub_sub_cancel_left] at this
  refine ⟨{ toFun := fun x => Ideal.Quotient.mk 𝔪 (r x)
            map_one' := ?_
            map_mul' := fun x y => ?_
            map_zero' := ?_
            map_add' := fun x y => ?_ }, key⟩
  · rw [← map_one (Ideal.Quotient.mk 𝔪), key]
    simp
  · rw [← map_mul, key]
    have := add_mem (mul_mem_hatId D 𝔪 y.2 (hr x))
      (mul_mem_hatId D 𝔪 (VacMove.inc_int D (r x)) (hr y))
    convert this using 1
    push_cast
    rw [map_mul]
    ring
  · rw [← map_zero (Ideal.Quotient.mk 𝔪), key]
    simp
  · rw [← map_add (f := _), key]
    have := add_mem (hr x) (hr y)
    convert this using 1
    push_cast
    rw [map_add (f := _)]
    ring

def intMat (N : ℕ) : ↥(intG D N) →* Matrix (Fin N) (Fin N) (OhE D) where
  toFun k := Matrix.of fun i j =>
    ⟨(((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j, (((mem_intG _).1 k.2) i j).1⟩
  map_one' := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  map_mul' x y := by
    ext i j
    simp [Matrix.mul_apply]

theorem exists_levelRed : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ N : ℕ,
    ∃ ρ : ↥(intG D N) →* GL (Fin N) (𝓞 D.host.E ⧸ 𝔪), ∀ (k : ↥(intG D N)) (i j : Fin N) (b : 𝓞 D.host.E),
      ((ρ k : Matrix (Fin N) (Fin N) (𝓞 D.host.E ⧸ 𝔪)) i j = Ideal.Quotient.mk 𝔪 b ↔
        (((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j - inc D (b : D.host.E) ∈ hatId D 𝔪) := by
  intro D 𝔪 h𝔪 N
  obtain ⟨red, hred⟩ := exists_redHom D 𝔪 h𝔪
  exact ⟨((red.mapMatrix (m := Fin N)).toMonoidHom.comp (intMat D N)).toHomUnits,
    fun k i j b => hred (intMat D N k i j) b⟩

end GlobalTheory.LevelRed

end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.weil_integralPoint_skewLatticeUnitVector_same_eigen : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (r : GA D a), r ∈ intG D a → ∀ c : ℂ, W.Om r 1 e0 = c • e0 → W.Om r 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0) = c • Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 := by
  first | exact @GlobalTheory.FunObj.EigUnit.eig_unit | exact GlobalTheory.FunObj.EigUnit.eig_unit | (intros; apply GlobalTheory.FunObj.EigUnit.eig_unit <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.heisenbergTranslate_unitVector_congr_unimodular : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ y y' : Matrix (Fin d) (Fin a) D.host.E, (∀ i l, inc D (y i l - y' i l) ∈ hatId D (D.host.conj • 𝔪)) → ∃ c : ℂ, ‖c‖ = 1 ∧ Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y) (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) = c • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y') (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) := by
  first | exact @GlobalTheory.HeisTranslate.wd_unitVec_congr | exact GlobalTheory.HeisTranslate.wd_unitVec_congr | (intros; apply GlobalTheory.HeisTranslate.wd_unitVec_congr <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.weil_skewIdealLatticeUnitVector_unimodular_eigen : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ g ∈ intG D a, ∀ g' ∈ intG D d, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om g g' (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) = c • (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) := by
  first | exact @GlobalTheory.BotPairSmall.CvEig.om_unitVec_eig | exact GlobalTheory.BotPairSmall.CvEig.om_unitVec_eig | (intros; apply GlobalTheory.BotPairSmall.CvEig.om_unitVec_eig <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

theorem _root_.GlobalTheory.T.exists_realTrivial_point_finiteAdelicHom_eq : ∀ {D : D7} (V : HSp D) (M : GL (Fin V.rank) (Lev.EAf D)), M ∈ UA D.sp.cm V.gram → ∃ g : GfC V, finG V g = M := by
  first | exact @GlobalTheory.FrameTransport.exists_finG_eq | exact GlobalTheory.FrameTransport.exists_finG_eq | (intros; apply GlobalTheory.FrameTransport.exists_finG_eq <;> assumption)
end
