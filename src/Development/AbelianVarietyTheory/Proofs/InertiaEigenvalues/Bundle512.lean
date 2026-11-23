module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinBasisSubsetOfIsField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdemNotMemFilVOne
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle079
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle502
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
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract

@[expose] public section

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DRDual

open GlobalTheory.DRFil

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def twistRep (χ : G →* LLˣ) (ρ : Representation LL G V) : Representation LL G V where
  toFun g := ((χ g : LLˣ) : LL) • ρ g
  map_one' := by simp
  map_mul' g h := by simp [smul_smul, mul_comm]

theorem act_zpow (T : Fˣ) (hT : (T : F) = PD.ι PD.t) (n : ℤ) (g : G) :
    PD.actdR g ((T ^ n : Fˣ) : F) = ((PD.χ g ^ n : Qpˣ) : Qp) • ((T ^ n : Fˣ) : F) := by
  have hsm : ∀ (q : Qp) (b : B), PD.ι (q • b) = q • PD.ι b := fun q b =>
    (PD.ι.toLinearMap.restrictScalars Qp).map_smul q b
  have h1 : Units.map (PD.actdR g : F →* F) T = Units.map (algebraMap Qp F : Qp →* F) (PD.χ g) * T := by
    ext
    have h2 := PD.ι_comm g PD.t
    rw [PD.t_act, hsm, ← hT, Algebra.smul_def] at h2
    exact h2.symm
  have h3 := congrArg (fun x : Fˣ => ((x ^ n : Fˣ) : F)) h1
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map] at h3
  rw [Algebra.smul_def, ← map_zpow]
  exact h3

theorem twist_unit (ρ ρ' : Representation LL G V) (u : Fˣ) (n : ℤ) (ψ : G → Qpˣ)
    (hu : (u : F) ∈ PD.Fil n) (hu' : ((u⁻¹ : Fˣ) : F) ∈ PD.Fil (-n))
    (ha : ∀ g, PD.actdR g (u : F) = (ψ g : Qp) • (u : F))
    (ha' : ∀ g, PD.actdR g ((u⁻¹ : Fˣ) : F) = (((ψ g)⁻¹ : Qpˣ) : Qp) • ((u⁻¹ : Fˣ) : F))
    (hρ : ∀ g x, (ψ g : Qp) • ρ' g x = ρ g x) :
    (IsDR PD ρ → IsDR PD ρ') ∧
      ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), multV PD ρ' τ (n + a) = multV PD ρ τ a := by
  have hρ' : ∀ g x, (((ψ g)⁻¹ : Qpˣ) : Qp) • ρ g x = ρ' g x := fun g x => by
    rw [← hρ, smul_smul, Units.inv_mul, one_smul]
  let Φ : V ⊗[Qp] F →ₗ[LL] V ⊗[Qp] F := mulR Qp F LL V u ∘ₗ ext Qp F LinearMap.id
  let Ψ : V ⊗[Qp] F →ₗ[LL] V ⊗[Qp] F := mulR Qp F LL V (u⁻¹ : Fˣ) ∘ₗ ext Qp F LinearMap.id
  have h1 : ∀ x, Φ (Ψ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul v b => simp [Φ, Ψ]
  have h2 : ∀ x, Ψ (Φ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul v b => simp [Φ, Ψ]
  let E : V ⊗[Qp] F ≃ₗ[LL] V ⊗[Qp] F := LinearEquiv.ofLinear Φ Ψ (LinearMap.ext h1) (LinearMap.ext h2)
  have hD : (DdR PD ρ).map E.toLinearMap = DdR PD ρ' := by
    refine le_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact twist_mem_DdR PD ρ ρ' LinearMap.id _ _ ha hρ hx
    · exact ⟨Ψ y, twist_mem_DdR PD ρ' ρ LinearMap.id _ _ ha' hρ' hy, h1 y⟩
  have hF : ∀ τ a, (FildR PD ρ τ a).map E.toLinearMap = FildR PD ρ' τ (n + a) := by
    intro τ a
    refine le_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact twist_mem_FildR PD ρ ρ' LinearMap.id _ _ ha hρ τ hu hx
    · have := twist_mem_FildR PD ρ' ρ LinearMap.id _ _ ha' hρ' τ hu' hy
      rw [neg_add_cancel_left] at this
      exact ⟨Ψ y, this, h1 y⟩
  refine ⟨fun h => ?_, fun τ a => ?_⟩
  · rw [IsDR, ← hD, LinearEquiv.finrank_map_eq, h]
  · unfold multV
    rw [add_assoc, ← hF, ← hF, LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]

end Generic

theorem twisted_dual_deRham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (m : V →ₗ[↥LL.1] V' →ₗ[↥LL.1] ↥LL.1) (j : ℤ), Function.Bijective m → (∀ g x y, m (ρ g x) (ρ' g y) = ((cycLL (P.PD K) ↥LL.1 g ^ j : (↥LL.1)ˣ) : ↥LL.1) * m x y) → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 → multV (P.PD K) ρ' τ (-a - j) = multV (P.PD K) ρ τ a := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' m j hm hg h
  have := K.2
  have := LL.2
  have := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL V ρ).1
  have hs := filSpans T K LL ρ h
  let ρ₀ : Representation ↥LL.1 ↥(GK K) V' := twistRep (cycLL (P.PD K) ↥LL.1 ^ (-j)) ρ'
  have hρ₀ : ∀ g y, ρ₀ g y = ((cycLL (P.PD K) ↥LL.1 g ^ (-j) : (↥LL.1)ˣ) : ↥LL.1) • ρ' g y :=
    fun g y => rfl
  have hβ : ∀ g x y, m (ρ g x) (ρ₀ g y) = m x y := fun g x y => by
    rw [hρ₀, map_smul, hg, smul_eq_mul, zpow_neg, Units.inv_mul_cancel_left]
  have hβ' : Function.Bijective m.flip := (LinearEquiv.ofBijective m hm).flip.bijective
  have h₀ : IsDR (P.PD K) ρ₀ := isDR_of_spans T K LL ρ₀
    (spans_dual_of_spans (P.PD K) ρ ρ₀ m (isField_dR T) hβ hβ' (hs.spans _))
  have ht : (GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR P K : P.R.BdR) = (P.PD K).ι (P.PD K).t := rfl
  obtain ⟨h1, h2⟩ := twist_unit (P.PD K) ρ₀ ρ' (GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR P K ^ (-j)) (-j)
    (fun g => (P.PD K).χ g ^ (-j)) (tdR_zpow_mem T K _)
    (by rw [← zpow_neg]; exact tdR_zpow_mem T K _) (act_zpow _ _ ht _)
    (fun g => by rw [← zpow_neg, ← zpow_neg]; exact act_zpow _ _ ht _ g)
    (fun g x => by
      rw [hρ₀, ← algebraMap_smul ↥LL.1]
      congr 1
      exact congrArg Units.val
        (map_zpow (Units.map (algebraMap ℚ_[l] ↥LL.1 : ℚ_[l] →* ↥LL.1)) ((P.PD K).χ g) (-j)))
  refine ⟨h1 h₀, fun τ a _ => ?_⟩
  obtain ⟨n, d, k, had⟩ := exists_adapted (P.PD K) (isField_dR T) ρ hs τ
  obtain ⟨d', had'⟩ := had.dual ρ₀ m hβ hβ'
  rw [show -a - j = -j + -a by ring, h2, had.multV_eq, had'.multV_eq]
  simp only [neg_inj]

end GlobalTheory.DRDual
end
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory
namespace NormCharL

theorem norm_cast_eq_one (K : Type) [Field K] [NumberField K] (m : ℕ) (β : 𝓞 K)
    (h : β - 1 ∈ Ideal.span {(m : 𝓞 K)}) : ((Algebra.norm ℤ β : ℤ) : ZMod m) = 1 := by
  obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton'.1 h
  have hβ : β = 1 + (m : 𝓞 K) * γ := by rw [mul_comm, hγ]; ring
  let b := Module.Free.chooseBasis ℤ (𝓞 K)
  have key : (Int.castRingHom (ZMod m)).mapMatrix (Algebra.leftMulMatrix b β) = 1 := by
    rw [hβ, map_add (f := _), map_one, map_mul, map_natCast, map_add (f := _), map_one, map_mul, map_natCast]
    ext i j
    simp [Matrix.one_apply]
  have h2 := (Int.castRingHom (ZMod m)).map_det (Algebra.leftMulMatrix b β)
  rw [key, Matrix.det_one, ← Algebra.norm_eq_matrix_det] at h2
  simpa using h2

theorem sup_eq_top_iff (K : Type) [Field K] [NumberField K] (m : ℕ) (hm : m.Prime)
    (I : Ideal (𝓞 K)) : I ⊔ Ideal.span {(m : 𝓞 K)} = ⊤ ↔ ¬ m ∣ Ideal.absNorm I := by
  constructor
  · intro h hdvd
    obtain ⟨i, hi, y, hy, hiy⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 h)
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    have hmem : i - 1 ∈ Ideal.span {(m : 𝓞 K)} := by
      rw [Ideal.mem_span_singleton']
      exact ⟨-z, by rw [← hiy]; ring⟩
    have h1 := GlobalTheory.NormCharL.norm_cast_eq_one K m i hmem
    have hd : Ideal.absNorm I ∣ (Algebra.norm ℤ i).natAbs := by
      rw [← Ideal.absNorm_span_singleton]
      exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hi)
    have hz : ((Algebra.norm ℤ i : ℤ) : ZMod m) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact Int.natCast_dvd.2 (hdvd.trans hd)
    rw [hz] at h1
    have : Fact m.Prime := ⟨hm⟩
    exact zero_ne_one h1
  · intro h
    have hc : Nat.Coprime (Ideal.absNorm I) m := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hm).2 h))
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hc
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 K) = (u : 𝓞 K) * (Ideal.absNorm I : 𝓞 K) + (v : 𝓞 K) * (m : 𝓞 K) := by
      have := congrArg (Int.cast : ℤ → 𝓞 K) huv
      push_cast at this
      exact this.symm
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem I)))
      (Submodule.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

theorem exists_continuous_ne_zero_one :
    ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → ∀ (χ : (ZMod m)ˣ →* ℂˣ) (cl : HeightOneSpectrum (𝓞 K) → (ZMod m)ˣ), (∀ P, ¬ m ∣ Ideal.absNorm P.asIdeal → (cl P : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ)) → (∃ P, ¬ m ∣ Ideal.absNorm P.asIdeal ∧ χ (cl P) ≠ 1) → ∃ L : ℂ → ℂ, Continuous L ∧ L 1 ≠ 0 ∧ ∀ s : ℝ, 1 < s → Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - ((χ (cl P) : ℂˣ) : ℂ) * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ)))) = L s := by
  intro K _ _ m hm χ cl hcl hχ
  have : Fact m.Prime := ⟨hm⟩
  set M : Ideal (𝓞 K) := Ideal.span {(m : 𝓞 K)} with hMdef
  let ψ : ZMod m → ℂ := fun x => if h : x = 0 then 0 else ((χ (Units.mk0 x h) : ℂˣ) : ℂ)
  have hψ0 : ψ 0 = 0 := by simp [ψ]
  have hψmul : ∀ x y, ψ (x * y) = ψ x * ψ y := by
    intro x y
    by_cases hx : x = 0
    · simp [ψ, hx]
    by_cases hy : y = 0
    · simp [ψ, hy]
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    simp only [ψ, dif_neg hx, dif_neg hy, dif_neg hxy]
    rw [← Units.val_mul, ← map_mul]
    congr 3
    ext
    simp
  have hψunit : ∀ u : (ZMod m)ˣ, ψ (u : ZMod m) = ((χ u : ℂˣ) : ℂ) := by
    intro u
    simp only [ψ, dif_neg u.ne_zero]
    congr 3
    ext
    simp
  let X : Ideal (𝓞 K) → ℂ := fun I => ψ (Ideal.absNorm I : ZMod m)
  have hcop : ∀ I : Ideal (𝓞 K), I ⊔ M = ⊤ ↔ (Ideal.absNorm I : ZMod m) ≠ 0 := by
    intro I
    rw [GlobalTheory.NormCharL.sup_eq_top_iff K m hm I, Ne, ZMod.natCast_eq_zero_iff]
  have hM0 : M ≠ ⊥ := by
    rw [hMdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hm.ne_zero
  have hX0 : X ⊥ = 0 := by simp [X, hψ0]
  have hXmul : ∀ I J, X (I * J) = X I * X J := by
    intro I J
    simp only [X, map_mul, Nat.cast_mul, hψmul]
  have hXnorm : ∀ I, I ≠ ⊥ → I ⊔ M = ⊤ → ‖X I‖ = 1 := by
    intro I _ hI
    have hne := (hcop I).1 hI
    simp only [X, ψ, dif_neg hne]
    exact GlobalTheory.Mem.RayPrimes.norm_char χ _
  have hXzero : ∀ I, I ⊔ M ≠ ⊤ → X I = 0 := by
    intro I hI
    have : (Ideal.absNorm I : ZMod m) = 0 := by
      by_contra h
      exact hI ((hcop I).2 h)
    simp [X, this, hψ0]
  set ε : ℂ := ((χ (-1) : ℂˣ) : ℂ) with hε
  have hεε : ε * ε = 1 := by
    rw [hε, ← Units.val_mul, ← map_mul]
    simp
  obtain ⟨φ, hφmul, hφhom, hφsm, hφnorm, hφβ⟩ := GlobalTheory.T.exists_mixedSpace_norm_sign_character K ε hεε
  have hXφ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ M → X (Ideal.span {β}) = φ (mixedEmbedding K β) := by
    intro β hβ0 hβ1
    rw [hφβ β hβ0]
    have h1 := GlobalTheory.NormCharL.norm_cast_eq_one K m β hβ1
    have hN0 : Algebra.norm ℤ β ≠ 0 := by
      rw [Ne, Algebra.norm_eq_zero_iff]
      exact hβ0
    simp only [X, Ideal.absNorm_span_singleton]
    split_ifs with hpos
    · have : (((Algebra.norm ℤ β).natAbs : ℕ) : ZMod m) = 1 := by
        rw [← Int.cast_natCast, Int.natAbs_of_nonneg hpos.le, h1]
      rw [this, ← Units.val_one, hψunit]
      simp
    · have hneg : Algebra.norm ℤ β ≤ 0 := le_of_not_gt hpos
      have : (((Algebra.norm ℤ β).natAbs : ℕ) : ZMod m) = ((-1 : (ZMod m)ˣ) : ZMod m) := by
        rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos hneg, Int.cast_neg, h1]
        simp
      rw [this, hψunit]
  obtain ⟨P, hPm, hPχ⟩ := hχ
  have hPtop : P.asIdeal ⊔ M = ⊤ := (GlobalTheory.NormCharL.sup_eq_top_iff K m hm P.asIdeal).2 hPm
  have hclX (Q : HeightOneSpectrum (𝓞 K)) (hQ : ¬ m ∣ Ideal.absNorm Q.asIdeal) :
      X Q.asIdeal = ((χ (cl Q) : ℂˣ) : ℂ) := by
    show ψ (Ideal.absNorm Q.asIdeal : ZMod m) = _
    rw [← hcl Q hQ, hψunit]
  have hnt : ∃ J, J ≠ ⊥ ∧ J ⊔ M = ⊤ ∧ X J ≠ 1 := by
    refine ⟨P.asIdeal, P.ne_bot, hPtop, ?_⟩
    rw [hclX P hPm]
    intro h
    exact hPχ (Units.val_eq_one.1 h)
  let c : HeightOneSpectrum (𝓞 K) → ℂ := fun Q => ((χ (cl Q) : ℂˣ) : ℂ)
  have hc : ∀ Q, ‖c Q‖ ≤ 1 := fun Q => (GlobalTheory.Mem.RayPrimes.norm_char χ (cl Q)).le
  have hcX : ∀ Q : HeightOneSpectrum (𝓞 K), ¬ M ≤ Q.asIdeal → c Q = X Q.asIdeal := by
    intro Q hQ
    have hmax : Q.asIdeal.IsMaximal := Q.isMaximal
    have htop : Q.asIdeal ⊔ M = ⊤ := by
      refine hmax.1.2 _ (lt_of_le_of_ne le_sup_left ?_)
      intro h
      exact hQ (h ▸ le_sup_right)
    rw [hclX Q ((GlobalTheory.NormCharL.sup_eq_top_iff K m hm Q.asIdeal).1 htop)]
  obtain ⟨L, hLd, hLe, hL1⟩ := GlobalTheory.idealCharacterL_continuation_ne_zero_one K M X φ hM0 hX0 hXmul
    hXnorm hXzero hφmul hφhom hφsm hφnorm hXφ hnt c hc hcX
  refine ⟨fun z => L ((max z.re 1 : ℝ) : ℂ), ?_, ?_, ?_⟩
  · refine hLd.continuousOn.comp_continuous (by fun_prop) (fun z => ?_)
    show (0 : ℝ) < ((max z.re 1 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    exact lt_of_lt_of_le one_pos (le_max_right _ _)
  · simpa using hL1
  · intro s hs
    have hmax : max (s : ℂ).re 1 = s := by
      rw [Complex.ofReal_re]
      exact max_eq_left hs.le
    simp only [hmax]
    exact (hLe s (by rwa [Complex.ofReal_re])).symm

end NormCharL
end GlobalTheory
end

section

open TensorProduct Module

noncomputable section

namespace GlobalTheory.RegularRing

theorem exists_periodMatrix_of_finrank (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (B : Type) [CommRing B] [IsDomain B] [Algebra F B] [Algebra E B] [IsScalarTower F E B]
    (G : Type) (act : G → B →+* B) (n : Type) [Fintype n] [DecidableEq n] (A : G → Matrix n n F)
    (hA : ∀ g, (A g).det ≠ 0) (hE : ∀ g (c : E), act g (algebraMap E B c) = algebraMap E B c)
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * act g b' = act g b * b') → ∃ c : E, b' = algebraMap E B c * b)
    (hu : ∀ b : B, b ≠ 0 → (∀ g, ∃ x : F, act g b = algebraMap F B x * b) → IsUnit b)
    (W : Submodule F (n → B))
    (hW : ∀ x, x ∈ W ↔ ∀ g, ((A g).map (algebraMap F B)).mulVec (fun i => act g (x i)) = x)
    (hdim : finrank F ↥W = finrank F E * Fintype.card n) :
    ∃ Q : GL n B, ∀ g, (A g).map (algebraMap F B) * (Q : Matrix n n B).map (act g) = Q := by
  classical
  by_cases hn : IsEmpty n
  · refine ⟨1, fun g => ?_⟩
    ext i
    exact isEmptyElim i
  rw [not_isEmpty_iff] at hn
  let WE : Submodule E (n → B) :=
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := by
        intro c x hx
        rw [SetLike.mem_coe, hW] at hx ⊢
        intro g
        have h1 : (fun i => act g ((c • x) i)) = algebraMap E B c • fun i => act g (x i) := by
          funext i
          simp [Algebra.smul_def, hE]
        rw [h1, Matrix.mulVec_smul, hx g]
        funext i
        simp [Algebra.smul_def] }
  have hWE : ∀ x, x ∈ WE ↔ x ∈ W := fun x => Iff.rfl
  have hfr : finrank E ↥WE = Fintype.card n := by
    have h1 := Module.finrank_mul_finrank F E ↥WE
    have h2 : finrank F ↥WE = finrank F ↥W :=
      ((Submodule.restrictScalarsEquiv F E (n → B) WE).restrictScalars F).finrank_eq.symm.trans
        (by congr 1)
    rw [h2, hdim] at h1
    exact Nat.eq_of_mul_eq_mul_left finrank_pos h1
  haveI : Module.Finite E ↥WE := Module.finite_of_finrank_pos (by rw [hfr]; exact Fintype.card_pos)
  let b : Basis n E ↥WE := (Module.finBasisOfFinrankEq E ↥WE hfr).reindex (Fintype.equivFin n).symm
  let v : n → (n → B) := fun j => (b j : n → B)
  have hv : ∀ g j, ((A g).map (algebraMap F B)).mulVec (fun i => act g (v j i)) = v j :=
    fun g j => (hW _).1 ((hWE _).1 (b j).2) g
  let σ : G → (n → B) →+ (n → B) := fun g =>
    { toFun := fun x => ((A g).map (algebraMap F B)).mulVec (fun i => act g (x i))
      map_zero' := by
        simp only [Pi.zero_apply, map_zero]
        exact Matrix.mulVec_zero _
      map_add' := by
        intro x y
        simp only [Pi.add_apply, map_add (f := _)]
        exact Matrix.mulVec_add _ _ _ }
  have hσ : ∀ g (c : B) (w : n → B), σ g (c • w) = act g c • σ g w := by
    intro g c w
    change ((A g).map (algebraMap F B)).mulVec (fun i => act g ((c • w) i)) =
      act g c • ((A g).map (algebraMap F B)).mulVec (fun i => act g (w i))
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp
  have hvE : LinearIndependent E v :=
    b.linearIndependent.map' WE.subtype WE.ker_subtype
  have hvB : LinearIndependent B v := by
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    exact linearIndepOn_of_invariant (fun g c => act g c) σ hσ hreg v hv s (hvE.linearIndepOn _)
  let Q : Matrix n n B := Matrix.of fun i j => v j i
  have hQ : ∀ g, (A g).map (algebraMap F B) * Q.map (act g) = Q := by
    intro g
    ext i j
    have := congrFun (hv g j) i
    rw [Matrix.mul_apply]
    simpa [Q, Matrix.mulVec, dotProduct] using this
  have hdet0 : Q.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hc
    funext j
    refine Fintype.linearIndependent_iff.1 hvB c ?_ j
    funext i
    have := congrFun hc0 i
    simpa [Q, Matrix.mulVec, dotProduct, mul_comm] using this
  have hdetU : IsUnit Q.det := by
    refine hu _ hdet0 fun g => ?_
    have h2 := congrArg Matrix.det (hQ g)
    rw [Matrix.det_mul] at h2
    have h3 : ((A g).map (algebraMap F B)).det = algebraMap F B (A g).det := (RingHom.map_det _ _).symm
    have h4 : (Q.map (act g)).det = act g Q.det := (RingHom.map_det _ _).symm
    rw [h3, h4] at h2
    refine ⟨(A g).det⁻¹, ?_⟩
    conv_rhs => rw [← h2]
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (hA g), map_one, one_mul]
  exact ⟨Matrix.GeneralLinearGroup.mk'' Q hdetU, hQ⟩

end GlobalTheory.RegularRing
end
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

theorem _root_.GlobalTheory.T.finite_H2_twist_quotient_pow_and_card_le : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ k : ℕ, Finite (H2 (twist ε (O ⧸ IsLocalRing.maximalIdeal O ^ k))) ∧ Nat.card (H2 (twist ε (O ⧸ IsLocalRing.maximalIdeal O ^ k))) ≤ Nat.card (O ⧸ IsLocalRing.maximalIdeal O ^ k) := by
  first | exact @GlobalTheory.QuotientH2Count.h2_quot_card | exact GlobalTheory.QuotientH2Count.h2_quot_card | (intros; apply GlobalTheory.QuotientH2Count.h2_quot_card <;> assumption)
end
