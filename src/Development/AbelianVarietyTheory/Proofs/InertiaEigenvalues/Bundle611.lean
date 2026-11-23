module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle579
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle593
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle530
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle125
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle592
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle453
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
public import Formalism.WeaklyAdmissibleFiltrations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle595
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.ScaledValuations.ValuationApplyLtOneIff

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.CovTrans

theorem zOm_smul_eq_q {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module (Om l) X] [Module ℚ_[l] X]
    [IsScalarTower ℚ_[l] (Om l) X] (c : ℤ_[l]) (x : X) : zOm l c • x = ((c : ℚ_[l])) • x := by
  show (algebraMap ℚ_[l] (Om l) (algebraMap ℤ_[l] ℚ_[l] c)) • x = _
  rw [algebraMap_smul]
  rfl

theorem coord_inj {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module (Om l) X] [Module ℚ_[l] X]
    [IsScalarTower ℚ_[l] (Om l) X] {n : ℕ} {v : Fin n → X} (hv : LinearIndependent ℚ_[l] v) {u u' : Fin n → ℤ_[l]}
    (h : ∑ i, zOm l (u i) • v i = ∑ i, zOm l (u' i) • v i) : u = u' := by
  simp only [zOm_smul_eq_q] at h
  have := Fintype.linearIndependent_iff.mp hv (fun i => (u i : ℚ_[l]) - u' i)
    (by simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self])
  funext i
  have h2 := this i
  rw [sub_eq_zero] at h2
  exact Subtype.ext h2

theorem dsum {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module (Om l) X] {p q : ℕ} (α : Fin p → ℤ_[l])
    (β : Fin p → Fin q → ℤ_[l]) (w : Fin q → X) :
    ∑ s, zOm l (α s) • ∑ i, zOm l (β s i) • w i = ∑ i, zOm l (∑ s, β s i * α s) • w i := by

  simp only [Finset.smul_sum, smul_smul, map_sum, map_mul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => ?_
  rw [mul_comm]

theorem transition : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (d : ℕ) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)), LinearIndependent ℚ_[l] b → ∀ (m m' : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (ρs' : Fin m' → (Γ →* GL (Fin a) (Om l))) (ι : Fin m → Fin m'), (∀ k, ρs' (ι k) = ρs k) → ∀ (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (t' : Fin m' → Finset (Matrix (Fin a) (Fin a) (Om l))), (∀ k, t' (ι k) = t k) → ∀ (M M' : ℕ), M ≤ M' → ∀ (d₁ d₂ : ℕ) (ρ₁ : Γ →* GL (Fin d₁) ℤ_[l]) (ρ₂ : Γ →* GL (Fin d₂) ℤ_[l]) (bb₁ : Fin d₁ → Fin m → Matrix (Fin a) (Fin a) (Om l)) (bb₂ : Fin d₂ → Fin m' → Matrix (Fin a) (Fin a) (Om l)) (e₁ : Fin d₁ → ℤ_[l]) (e₂ : Fin d₂ → ℤ_[l]), LinearIndependent ℚ_[l] bb₁ → (∀ k, Reads ρ₁ (ρs k) (fun s => bb₁ s k) e₁) → (∀ k, Reads ρ₂ (ρs' k) (fun s => bb₂ s k) e₂) → (∀ s, bb₂ s ∈ GlobalTheory.TraceConjugationCover.latT ρs' t' M') → (∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∃ z : Fin d₁ → ℤ_[l], x = ∑ s, zOm l (z s) • bb₁ s) → ∀ (P₁ : Matrix (Fin d) (Fin d₁) ℤ_[l]) (P₂ : Matrix (Fin d) (Fin d₂) ℤ_[l]) (n N₁ N₂ : ℕ), n ≤ N₁ → n ≤ N₂ → GlobalTheory.TraceConjugationCover.Carries r b ρs t M bb₁ P₁ N₁ → GlobalTheory.TraceConjugationCover.Carries r b ρs' t' M' bb₂ P₂ N₂ → ∃ f : Matrix (Fin d₁) (Fin d₂) ℤ_[l], (∀ g, f * ((ρ₂ g : GL (Fin d₂) ℤ_[l]) : Matrix (Fin d₂) (Fin d₂) ℤ_[l]) = ((ρ₁ g : GL (Fin d₁) ℤ_[l]) : Matrix (Fin d₁) (Fin d₁) ℤ_[l]) * f) ∧ ∀ i j, (l : ℤ_[l]) ^ n ∣ (P₁ * f - P₂) i j := by
  intro l _ Γ _ a r d b hb m m' ρs ρs' ι hι t t' ht M M' hM d₁ d₂ ρ₁ ρ₂ bb₁ bb₂ e₁ e₂ hbb₁ hR₁ hR₂ hmem₂ hcoord
    P₁ P₂ n N₁ N₂ hn₁ hn₂ hC₁ hC₂
  have hsm : ∀ {k : Fin m} (c : Om l) (w : Matrix (Fin a) (Fin a) (Om l)),
      (Pi.single k (c • w) : Fin m → Matrix (Fin a) (Fin a) (Om l)) = c • Pi.single k w := by
    intro k c w
    funext k₀
    by_cases h : k₀ = k
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hπL : ∀ y ∈ GlobalTheory.TraceConjugationCover.latL t' M', y ∘ ι ∈ GlobalTheory.TraceConjugationCover.latL t M := by
    intro y hy
    have hle : Submodule.map (LinearMap.funLeft ℤ_[l] (Matrix (Fin a) (Fin a) (Om l)) ι) (GlobalTheory.TraceConjugationCover.latL t' M') ≤
        GlobalTheory.TraceConjugationCover.latL t M := by
      rw [GlobalTheory.TraceConjugationCover.latL, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      simp only [Set.mem_iUnion, Set.mem_image] at hx
      obtain ⟨k', v, hv, rfl⟩ := hx
      change (Pi.single k' ((l : Om l) ^ M' • v)) ∘ ι ∈ _
      rw [← Finset.univ_sum_single (Pi.single k' ((l : Om l) ^ M' • v) ∘ ι)]
      refine Submodule.sum_mem _ fun k _ => ?_
      by_cases hk : ι k = k'
      · subst hk
        simp only [Function.comp_apply, Pi.single_eq_same]
        have hv' : v ∈ t k := by rw [← ht k]; exact hv
        have e1 : ((l : Om l) ^ M' • v) = zOm l ((l : ℤ_[l]) ^ (M' - M)) • ((l : Om l) ^ M • v) := by
          rw [map_pow, map_natCast, smul_smul, ← pow_add, Nat.sub_add_cancel hM]
        rw [e1, hsm, GlobalTheory.TraceConjugationCover.zOm_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_iUnion.mpr ⟨k, v, hv', rfl⟩))
      · simp [Pi.single_eq_of_ne hk]
    exact hle ⟨y, hy, rfl⟩
  have hdec : ∀ j, ∃ (F : Γ →₀ ℤ_[l]) (y : Fin m' → Matrix (Fin a) (Fin a) (Om l)), y ∈ GlobalTheory.TraceConjugationCover.latL t' M' ∧
      bb₂ j = (F.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs' g) + y := by
    intro j
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp (hmem₂ j)
    obtain ⟨F, hF⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hx
    refine ⟨F, y, hy, ?_⟩
    rw [← hxy, ← hF]
    simp only [GlobalTheory.TraceConjugationCover.zOm_smul]
  choose F y hy hbb using hdec
  have hπF : ∀ (G : Γ →₀ ℤ_[l]), (G.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs' g) ∘ ι =
      G.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g := by
    intro G
    funext k
    simp [Finsupp.sum, Finset.sum_apply, GlobalTheory.TraceConjugationCover.tup, hι]
  have hπbb : ∀ j, bb₂ j ∘ ι = ((F j).sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) + y j ∘ ι := by
    intro j
    rw [hbb j, ← hπF]
    rfl
  have hmemT : ∀ j, bb₂ j ∘ ι ∈ GlobalTheory.TraceConjugationCover.latT ρs t M := by
    intro j
    rw [hπbb j]
    refine Submodule.add_mem_sup ?_ (hπL _ (hy j))
    simp only [GlobalTheory.TraceConjugationCover.zOm_smul]
    exact Submodule.finsuppSum_mem _ _ _ _ (fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩))
  choose z hz using fun j => hcoord _ (hmemT j)
  have hcol : ∀ j k, bb₂ j (ι k) = ∑ s, zOm l (z j s) • bb₁ s k := by
    intro j k
    have := congrFun (hz j) k
    simpa [Finset.sum_apply] using this
  refine ⟨Matrix.of fun s j => z j s, ?_, ?_⟩
  · intro g
    ext i j
    have hA : ∀ k, (ρs k g).val * bb₂ j (ι k) =
        ∑ i, zOm l (((ρ₁ g).val * Matrix.of fun s j => z j s) i j) • bb₁ i k := by
      intro k
      have e := fun s => (hR₁ k).equi g s
      try simp only at e
      rw [hcol, Finset.mul_sum]
      simp_rw [Matrix.mul_smul, e]
      rw [dsum]
      simp [Matrix.mul_apply]
    have hB : ∀ k, (ρs k g).val * bb₂ j (ι k) =
        ∑ i, zOm l (((Matrix.of fun s j => z j s) * (ρ₂ g).val) i j) • bb₁ i k := by
      intro k
      rw [← hι k]
      have e := (hR₂ (ι k)).equi g j
      try simp only at e
      rw [e]
      simp_rw [hcol]
      rw [dsum]
      simp [Matrix.mul_apply]
    have key : (fun i => ((Matrix.of fun s j => z j s) * (ρ₂ g).val) i j) =
        fun i => ((ρ₁ g).val * Matrix.of fun s j => z j s) i j := by
      apply GlobalTheory.CovTrans.coord_inj hbb₁
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply]
      rw [← hB k, hA k]
    exact congrArg _ (congrFun key i)
  · intro i j
    have hsingle : ∑ s, zOm l ((Pi.single j 1 : Fin d₂ → ℤ_[l]) s) • bb₂ s = bb₂ j := by
      simp [Pi.single_apply]
    obtain ⟨w₂, hw₂⟩ := hC₂ (Pi.single j 1) (F j) (y j) (hy j) (by rw [hsingle]; exact hbb j)
    obtain ⟨w₁, hw₁⟩ := hC₁ (fun s => z j s) (F j) (y j ∘ ι) (hπL _ (hy j)) (by rw [← hz j, hπbb j])
    have hP₂ : P₂ *ᵥ Pi.single j 1 = fun i => P₂ i j := by
      funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hP₁ : P₁ *ᵥ (fun s => z j s) = fun i => (P₁ * Matrix.of fun s j => z j s) i j := by
      funext i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [hP₂] at hw₂
    rw [hP₁] at hw₁
    have key : (fun i => (P₁ * Matrix.of fun s j => z j s) i j - P₂ i j) =
        fun i => (l : ℤ_[l]) ^ n * ((l : ℤ_[l]) ^ (N₁ - n) * w₁ i - (l : ℤ_[l]) ^ (N₂ - n) * w₂ i) := by
      apply GlobalTheory.CovTrans.coord_inj hb
      have hs : ∑ i, zOm l ((P₁ * Matrix.of fun s j => z j s) i j - P₂ i j) • b i =
          ∑ i, zOm l ((P₁ * Matrix.of fun s j => z j s) i j) • b i - ∑ i, zOm l (P₂ i j) • b i := by
        simp only [map_sub, sub_smul, Finset.sum_sub_distrib]
      rw [hs, hw₁, hw₂, add_sub_add_left_eq_sub]
      have e1 : (l : Om l) ^ N₁ = (l : Om l) ^ n * (l : Om l) ^ (N₁ - n) := by rw [← pow_add, Nat.add_sub_cancel' hn₁]
      have e2 : (l : Om l) ^ N₂ = (l : Om l) ^ n * (l : Om l) ^ (N₂ - n) := by rw [← pow_add, Nat.add_sub_cancel' hn₂]
      rw [e1, e2]
      simp only [Finset.smul_sum, smul_smul, map_mul, map_sub, map_pow, map_natCast, mul_sub, sub_smul,
        Finset.sum_sub_distrib, mul_assoc]
    have := congrFun key i
    rw [Matrix.sub_apply, this]
    exact Dvd.intro _ rfl

end GlobalTheory.CovTrans
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.HodgeAt

theorem phiS_idem : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K L : FinExt l) [FiniteDimensional ℚ_[l] ↥K.1] (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (σ : GQ l), (∀ x : ↥K.1, σ ((τ x : ↥L.1) : Om l) = (x : Om l)) → phiS P σ L (GlobalTheory.DRFil.idem P.R.BdR τ) = 1 := by
  intro l _ P K L _ τ σ hσ
  obtain ⟨n, a, c, h, h1⟩ := GlobalTheory.DRFil.idem_repr P.R.BdR τ

  rw [h, map_sum]
  simp only [phiS_tmul]
  have hc : ∀ i, algebraMap ↥K.1 P.R.BdR (c i) = algebraMap (Om l) P.R.BdR ((c i : ↥K.1) : Om l) := fun i => rfl

  simp only [hc, ← map_mul, ← map_sum]
  have : ∑ i, σ ((a i : ↥L.1) : Om l) * ((c i : ↥K.1) : Om l) = σ (((∑ i, a i * τ (c i) : ↥L.1)) : Om l) := by

    simp only [IntermediateField.coe_sum, IntermediateField.coe_mul, map_sum, map_mul, hσ]
  rw [this, h1]
  simp

theorem phiS_mem_Fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K L : FinExt l) (σ : GQ l) (n : ℤ) (r : ↥L.1 ⊗[ℚ_[l]] P.R.BdR), r ∈ FilV (P.PD K) (LL := ↥L.1) (V := ↥L.1) n → phiS P σ L r ∈ (P.PD K).Fil n := by
  intro l _ P AI T K L σ n r hr
  have h0 : ∀ x : Om l, algebraMap (Om l) P.R.BdR x ∈ (P.PD K).Fil 0 := by
    intro x
    rw [T.fil]
    obtain ⟨y, hy, -⟩ := T.om x
    rw [hy]
    exact ((GlobalTheory.MemLoc.filD_laws l).2.2.2.2.2.2 0 y).2 (GlobalTheory.MemLoc.FilSeed.mem_filtration_zero' y)
  refine GlobalTheory.DRFil.FilV_induction (P.PD K) (p := fun r => phiS P σ L r ∈ (P.PD K).Fil n) ?_ ?_ ?_ hr
  · simp
  · intro c b hb
    rw [phiS_tmul]
    simpa using (P.PD K).Fil_mul 0 n _ _ (h0 _) hb
  · intro x y hx hy
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hx hy

end GlobalTheory.HodgeAt

namespace GlobalTheory.HodgeAt

theorem exists_ext_fixing : ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (σ : GQ l), ∃ K' : FinExt l, K.1 ≤ K'.1 ∧ ∀ g ∈ GK K', ∀ y : ↥L.1, g (σ (y : Om l)) = σ (y : Om l) := by
  intro l _ K L σ
  haveI := K.2
  haveI := L.2
  haveI : FiniteDimensional ℚ_[l] ↥(L.1.map (σ : Om l →ₐ[ℚ_[l]] Om l)) :=
    LinearEquiv.finiteDimensional (IntermediateField.equivMap L.1 (σ : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv
  refine ⟨⟨K.1 ⊔ L.1.map (σ : Om l →ₐ[ℚ_[l]] Om l), IntermediateField.finiteDimensional_sup _ _⟩, le_sup_left, ?_⟩
  intro g hg y
  have hmem : σ (y : Om l) ∈ K.1 ⊔ L.1.map (σ : Om l →ₐ[ℚ_[l]] Om l) :=
    le_sup_right (a := K.1) ((IntermediateField.mem_map _).2 ⟨y, y.2, rfl⟩)
  exact (mem_fixingSubgroup_iff _).1 hg _ hmem

end GlobalTheory.HodgeAt

namespace GlobalTheory.HodgeAt

theorem exists_xi_pow_mul : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l) (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (K : FinExt l) (k : ℤ) (q p : ℕ), k + q = p → ∀ x ∈ (P.PD K).Fil k, ∃ z : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ q * T.eD x = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ p * z) := by
  intro l _ P AI T C ξ hξ K k q p hkp x hx
  obtain ⟨hP, -, -, -, -, hshift, -⟩ := GlobalTheory.MemLoc.seed_fil l C ξ hξ
  rw [T.fil] at hx
  have hy := (hshift k q (T.eD x)).2 hx
  rw [hkp] at hy
  obtain ⟨y, hye⟩ := (GlobalTheory.MemLoc.mem_FilD_iff_xi_pow l C.ε (GlobalTheory.MemLoc.core_isEps l C) p _).1 hy
  have h0 : (-(p : ℤ)).toNat = 0 := by omega
  rw [h0, pow_zero, mul_one, Int.toNat_natCast] at hye
  have hz : aDp l (xi C.ε) ^ p * y ∈ Per.FilP l p :=
    ((GlobalTheory.MemLoc.filtration_eq_xi_pow l C.ε (GlobalTheory.MemLoc.core_isEps l C)).1 p _).2 (dvd_mul_right _ _)
  rw [hP, Ideal.mem_span_singleton'] at hz
  obtain ⟨z', hz'⟩ := hz
  refine ⟨z', ?_⟩
  rw [mul_comm (aDp l ξ ^ p) z', hz', hye]

end GlobalTheory.HodgeAt
end

section

noncomputable section

namespace GlobalTheory.ExpImage.Expand

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem frob_teich (x : OCb l) :
    WittVector.frobenius (WittVector.teichmuller l x) = WittVector.teichmuller l x ^ l := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

theorem root_pow (AI : LocAinf l P) (m : ℕ) : AI.εroot m ^ (l ^ m) = AI.ε := by
  induction m with
  | zero => simp [LocAinf.εroot]
  | succ m ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem epsT_pow (AI : LocAinf l P) (s : ℕ) :
    epsT AI s ^ (l ^ s) = WittVector.teichmuller l AI.ε := by
  rw [epsT, ← map_pow, root_pow]

theorem lifts_iter {AI : LocAinf l P} {K : FinExt l} {w : Ainf l} {c : ↥(K0 K)}
    (h : Lifts AI K w c) (k : ℕ) :
    Lifts AI K ((WittVector.frobenius : Ainf l → Ainf l)^[k] w) ((frK P K ^ k) c) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', AlgHom.mul_apply]
    exact ih.frob

theorem qB_eq (z : ℚ_[l]) : qB P z = oB P (algebraMap ℚ_[l] (Om l) z) :=
  IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR z

theorem coeff_eq (K : FinExt l) (s j : ℕ) {ι : Type} (T : Finset ι) (c : ι → ↥(K0 K))
    (m : ι → ℕ) (d : ↥(K0 K)) :
    algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ *
        levSum P K s j T c m d =
      ∑ k ∈ Finset.range s, ∑ i ∈ T, (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) *
          (P.ζQ s ^ (m i * l ^ k) * algebraMap ℚ_[l] (Om l)
            ((((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j / (j.factorial : ℚ_[l]))) +
        algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l])⁻¹) * (d : Om l) := by
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hj : (j.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  rw [levSum, mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j / (j.factorial : ℚ_[l]) =
        ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * ((l : ℚ_[l]) ^ (j * k) * (m i : ℚ_[l]) ^ j) := by
      push_cast
      rw [div_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm k j]
      field_simp
    rw [e, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]
    ring
  · have e : (j.factorial : ℚ_[l])⁻¹ =
        ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * (l : ℚ_[l]) ^ (s * j) := by
      field_simp
    rw [e, map_mul, map_pow, map_natCast, mul_assoc]

theorem expand : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (ι : Type) (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K)) (m : ι → ℕ) (M : ℕ) (d : ℕ → ↥(K0 K)), 1 ≤ M → (∀ i ∈ T, Lifts AI K (w i) (c i)) → (∀ j < M, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK P K (d j) = (frK P K ^ s) (∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j)) → ∃ y : Ainf l, y - WittVector.frobenius y = ∑ i ∈ T, w i * epsT AI s ^ m i ∧ io AI y - ∑ j ∈ Finset.range M, oB P (algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * levSum P K s j T c m (d j)) * tD P ^ j ∈ FilB P (M : ℤ) := by
  intro l _ P AI TT K s ι T w c m M d hM hw hd
  obtain ⟨y₁, h1, h2⟩ := GlobalTheory.T.frobenius_equation_lift_Ainf l P AI TT K ι T
    (fun i => (WittVector.frobenius : Ainf l → Ainf l)^[s] (w i)) (fun i => (frK P K ^ s) (c i)) m M d hM
    (fun i hi => lifts_iter (hw i hi) s) (fun j hj => ⟨(hd j hj).1, by

      rw [(hd j hj).2, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, map_natCast]⟩)
  set H : ℕ → Ainf l := fun k =>
    ∑ i ∈ T, (WittVector.frobenius : Ainf l → Ainf l)^[k] (w i) * epsT AI s ^ (m i * l ^ k) with hH
  have hφ : ∀ k, WittVector.frobenius (H k) = H (k + 1) := by
    intro k
    simp only [hH]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, Function.iterate_succ_apply', epsT, frob_teich, ← pow_mul]
    congr 2
    ring
  have hs : H s = ∑ i ∈ T, (WittVector.frobenius : Ainf l → Ainf l)^[s] (w i) *
      WittVector.teichmuller l AI.ε ^ m i := by
    simp only [hH]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (m i), pow_mul, epsT_pow]
  have h0 : H 0 = ∑ i ∈ T, w i * epsT AI s ^ m i := by simp [hH]
  refine ⟨∑ k ∈ Finset.range s, H k + y₁, ?_, ?_⟩
  · have ht := Finset.sum_range_sub' H s
    rw [Finset.sum_sub_distrib] at ht

    rw [map_add (f := _), map_sum, Finset.sum_congr rfl (fun k _ => hφ k), ← h0]
    rw [← hs] at h1
    linear_combination ht + h1
  · have hk : ∑ k ∈ Finset.range s, ∑ i ∈ T, oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) *
        (io AI (epsT AI s ^ (m i * l ^ k)) - oB P (P.ζQ s ^ (m i * l ^ k)) *
          ∑ j ∈ Finset.range M, qB P ((((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j /
            (j.factorial : ℚ_[l])) * tD P ^ j) ∈ FilB P (M : ℤ) := by
      refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i hi => ?_
      refine FilB_zero_mul ?_ (GlobalTheory.T.teichmullerEpsilonRoot_pow_sub_zeta_exp_mem_filtration l P AI TT s (m i * l ^ k) M)
      rw [← (lifts_iter (hw i hi) k).io_eq]
      exact io_mem AI _
    have e1 : io AI (∑ k ∈ Finset.range s, H k) = ∑ k ∈ Finset.range s, ∑ i ∈ T,
        oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) * io AI (epsT AI s ^ (m i * l ^ k)) := by

      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hH]

      rw [map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_mul, (lifts_iter (hw i hi) k).io_eq]
    have e2 : ∑ j ∈ Finset.range M, oB P (algebraMap ℚ_[l] (Om l)
          ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * levSum P K s j T c m (d j)) * tD P ^ j =
        ∑ k ∈ Finset.range s, ∑ i ∈ T, oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) *
          (oB P (P.ζQ s ^ (m i * l ^ k)) *
            ∑ j ∈ Finset.range M, qB P ((((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j /
              (j.factorial : ℚ_[l])) * tD P ^ j) +
        ∑ j ∈ Finset.range M, qB P ((j.factorial : ℚ_[l])⁻¹) * oB P (d j : Om l) * tD P ^ j := by

      simp only [coeff_eq, map_add (f := _), map_sum, map_mul, ← qB_eq, add_mul, Finset.sum_add_distrib,
      Finset.sum_mul, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have := add_mem hk h2
    rw [map_add (f := _), e1, e2]
    convert this using 1
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring

end GlobalTheory.ExpImage.Expand
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.MainNotions.V

namespace GlobalTheory


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.frob_dense_off_finite : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (T : Set (HeightOneSpectrum (𝓞 F))), T.Finite →
    Dense {σ : _root_.Formalism.ConjugateSelfDual.G F Ω | ∃ v : HeightOneSpectrum (𝓞 F), v ∉ T ∧ ∃ A : ValuationSubring Ω,
      _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v ∧ _root_.Formalism.ConjugateSelfDual.IsFrob A (_root_.Formalism.ConjugateSelfDual.normV v) σ} := by
  intro F Ω _ _ _ _ _ T hT
  refine (_root_.GlobalTheory.Published.chebotarevDegreeOne'.dense
    (F := F) (Ω := Ω) hT).mono ?_
  rintro σ ⟨v, hv, -, A, hA, hσ⟩
  exact ⟨v, hv, A, hA, hσ⟩

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

theorem _root_.GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := ℚ_[l]) ι π → IsCrys (P.PD K) T₀.ρ → IsCrys (P.PD K) T₁.ρ → IsCrys (P.PD K) T₂.ρ → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K) T₁.ρ τ a ↔ IsJumpV (P.PD K) T₀.ρ τ a ∨ IsJumpV (P.PD K) T₂.ρ τ a := by
  first | exact @GlobalTheory.Per.SESJumps.isJumpV_iff_of_isSESLat | exact GlobalTheory.Per.SESJumps.isJumpV_iff_of_isSESLat | (intros; apply GlobalTheory.Per.SESJumps.isJumpV_iff_of_isSESLat <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.map_Dcris_eq_DdR_crystalline_unramified : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), Function.Bijective (algebraMap ↥(K0 K) ↥K.1) → ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → (Dcris (P.PD K) ρ).map (ιV (P.PD K) (LL := ↥LL.1) (V := V)) = DdR (P.PD K) ρ ∧ ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧ finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = finrank ↥LL.1 V ∧ ∀ a : ℤ, FildR (P.PD K) ρ τ a = (FilCris (P.PD K) ρ a ⊓ DcrisL (P.PD K) ρ (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1))).map (ιV (P.PD K) (LL := ↥LL.1) (V := V)) := by
  first | exact @GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR | exact GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR | (intros; apply GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.crysLattice_basis_mem_sum_deRham_filtration : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), IsCrys (P.PD K) ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[l] ↥L.T), ∀ j : Fin d, ∃ (m : ℕ) (k : Fin m → ℤ) (c : Fin m → Per.BdR l) (v : Fin m → Fin d → Per.BdR l), (∀ i (g : ↥(GK K)), ((LinearMap.toMatrix b b (actT L g)).map (Per.zD l)).mulVec (fun r => Per.σD (g : GQ l) (v i r)) = v i) ∧ (∀ i r, v i r ∈ Per.FilD l (k i)) ∧ (∀ i, c i ∈ Per.FilD l (-k i)) ∧ (Pi.single j 1 : Fin d → Per.BdR l) = ∑ i, c i • v i := by
  first | exact @GlobalTheory.crysLattice_basis_mem_sum_fil_dR | exact GlobalTheory.crysLattice_basis_mem_sum_fil_dR | (intros; apply GlobalTheory.crysLattice_basis_mem_sum_fil_dR <;> assumption)
end
