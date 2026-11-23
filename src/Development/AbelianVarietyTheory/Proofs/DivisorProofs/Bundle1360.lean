module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import GroundTheory.LocalFields.LocalFourierHaar
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceBasisHyperbolicPlaneComplement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsTransportedActionFinitePointPreimage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

noncomputable section

namespace GlobalTheory.HeckeExtend

variable (F : Type) [Field F] [NumberField F]

def finU : (Af F)ˣ →* (AF F)ˣ := Units.map (MonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem continuous_finU : Continuous (finU F) :=
  Continuous.units_map _ (continuous_const.prodMk continuous_id)

def sndU : (AF F)ˣ →* (Af F)ˣ := Units.map (MonoidHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem continuous_circle_toUnits : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
  Units.continuous_iff.2 ⟨continuous_subtype_val, by
    have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
    refine h.congr fun z => ?_
    simp⟩

theorem exists_cong_sub (K : Set (Af F)ˣ) (hK : K ∈ 𝓝 1) : ∃ M : ℕ, 0 < M ∧ ∀ u : (Af F)ˣ,
    (∃ c : Af F, (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ (u : Af F) - 1 = M • c) →
    (∃ c : Af F, (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ ((u⁻¹ : (Af F)ˣ) : Af F) - 1 = M • c) → u ∈ K := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hK
  obtain ⟨T, hT, hTK⟩ := hK
  obtain ⟨T1, hT1, T2, hT2, hTT⟩ := mem_nhds_prod_iff.1 hT
  have hf : Continuous fun b : Af F => 1 + b := continuous_const.add continuous_id
  have h1 : (fun b : Af F => 1 + b) ⁻¹' T1 ∈ 𝓝 0 :=
    hf.continuousAt.preimage_mem_nhds (by rw [add_zero]; exact hT1)
  have h2 : (fun b : Af F => MulOpposite.op (1 + b)) ⁻¹' T2 ∈ 𝓝 0 :=
    (MulOpposite.continuous_op.comp hf).continuousAt.preimage_mem_nhds
      (by rw [Function.comp_apply, add_zero]; exact hT2)
  obtain ⟨N, hN, hNW⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ (Filter.inter_mem h1 h2)
  refine ⟨N, hN, fun u ⟨a, ha, e⟩ ⟨b, hb, e'⟩ => hTK (hTT ⟨?_, ?_⟩)⟩
  · change (u : Af F) ∈ T1
    rw [eq_add_of_sub_eq' e]; exact (hNW a ha).1
  · change MulOpposite.op ((u⁻¹ : (Af F)ˣ) : Af F) ∈ T2
    rw [eq_add_of_sub_eq' e']; exact (hNW b hb).2

theorem exists_cong_ker (lam : (AF F)ˣ →* Circle) (hlam : Continuous lam)
    (h : ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) :
    ∃ M : ℕ, 0 < M ∧ ∀ b : (AF F)ˣ,
      (b : AF F) - 1 ∈ intF F M → ((b⁻¹ : (AF F)ˣ) : AF F) - 1 ∈ intF F M → lam b = 1 := by
  let ψ : (Af F)ˣ →* ℂˣ := Circle.toUnits.comp (lam.comp (finU F))
  have hψ : Continuous ψ := (continuous_circle_toUnits).comp (hlam.comp (continuous_finU F))
  have hK := (GlobalTheory.CuspRep.isOpen_ker_finIdele F ψ hψ).mem_nhds (x := 1) (by simp)
  obtain ⟨M, hM, hMK⟩ := exists_cong_sub F _ hK
  refine ⟨M, hM, fun b hb hb' => ?_⟩
  obtain ⟨c, hc, e⟩ := hb
  obtain ⟨c', hc', e'⟩ := hb'
  have h2 : ψ (sndU F b) = 1 := hMK (sndU F b) ⟨c, hc, e⟩ ⟨c', hc', e'⟩
  have h3 : lam (finU F (sndU F b)) = 1 := by
    have := congrArg Units.val h2
    exact Subtype.ext (by simpa [ψ] using this)
  set a : (AF F)ˣ := b * (finU F (sndU F b))⁻¹ with ha
  have hfin : ((a : AF F)).2 = 1 := by
    show (b : AF F).2 * ((b⁻¹ : (AF F)ˣ) : AF F).2 = 1
    exact congrArg Prod.snd (Units.mul_inv b)
  have hA : At (evI F) ((a : AF F) - 1) := by
    intro u hu
    have hu1 : u.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 hu
    refine Prod.ext ?_ ?_
    · show u.1 * ((a : AF F).1 - 1) = 0
      rw [hu1, zero_mul]
    · show u.2 * ((a : AF F).2 - 1) = 0
      rw [hfin, sub_self, mul_zero]
  have hb : b = a * finU F (sndU F b) := by rw [ha, inv_mul_cancel_right]
  rw [hb, map_mul, h a hA, h3, mul_one]

end GlobalTheory.HeckeExtend

end
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.BCChar

open scoped GroundTheory.Global.AdicLiesOver

theorem adicCompletionMap_comp_adicCompletionMap {K M L : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Field L] [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 M))
    (w : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal]
    [w.asIdeal.LiesOver v.asIdeal] :
    (GroundTheory.Global.adicCompletionMap u w).comp (GroundTheory.Global.adicCompletionMap v u) =
      GroundTheory.Global.adicCompletionMap v w := by
  have h := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) (K := K) v).equalizer
    ((GroundTheory.Global.continuous_adicCompletionMap u w).comp
      (GroundTheory.Global.continuous_adicCompletionMap v u))
    (GroundTheory.Global.continuous_adicCompletionMap v w) (funext fun x ↦ ?_)
  · exact RingHom.ext (congrFun h)
  · simp only [Function.comp_apply]
    rw [GroundTheory.Global.adicCompletionMap_algebraMap, GroundTheory.Global.adicCompletionMap_algebraMap,
      GroundTheory.Global.adicCompletionMap_algebraMap, ← IsScalarTower.algebraMap_apply K M L]

theorem normU_comp_normU {K M L : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Field L] [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 M))
    (w : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal]
    [w.asIdeal.LiesOver v.asIdeal] :
    (normU v u).comp (normU u w) = normU v w := by
  haveI : IsScalarTower (v.adicCompletion K) (u.adicCompletion M) (w.adicCompletion L) :=
    .of_algebraMap_eq' (adicCompletionMap_comp_adicCompletionMap v u w).symm
  refine MonoidHom.ext fun x => Units.ext ?_
  simp only [normU, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  exact Algebra.norm_norm (R := v.adicCompletion K) (S := u.adicCompletion M) (a := (x : w.adicCompletion L))

end GlobalTheory.BCChar

end
end

section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

noncomputable section
namespace GlobalTheory.PlaneSkewDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J a (b + c) = form σ J a b + form σ J a c := by
  unfold form
  have : (fun i => σ ((b + c) i)) = (fun i => σ (b i)) + (fun i => σ (c i)) := by
    funext i; simp
  rw [this, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) (s : E) :
    form σ J a (s • b) = σ s * form σ J a b := by
  unfold form
  have : (fun i => σ ((s • b) i)) = σ s • (fun i => σ (b i)) := by
    funext i; simp
  rw [this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_restrict (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E)
    (u u' : Fin n₁ → E) : form σ (ιᵀ * J * ι.map σ) u u' = form σ J (ι *ᵥ u) (ι *ᵥ u') := by
  unfold form
  have h : (fun i => σ ((ι *ᵥ u') i)) = ι.map σ *ᵥ (fun i => σ (u' i)) := by
    funext i
    exact RingHom.map_mulVec (σ : E →+* E) ι u' i
  rw [h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

end GlobalTheory.PlaneSkewDual

namespace GlobalTheory.PlaneSkewDual

theorem lowLat_selfDual (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n₁ : ℕ) (J : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E) (L : Submodule (𝓞 E) (Fin (n₁ + 2) → E))
    (x y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E)
    (hL : ∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x)))
    (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0)
    (hsplit : ∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y) :
    ∀ u, u ∈ lowLat ι L ↔ ∀ u' ∈ lowLat ι L, ∀ o : 𝓞 E,
      IsIntegral ℤ (Algebra.trace ℚ E (o * form σ (ιᵀ * J * ι.map σ) u u')) := by
  intro u
  simp only [mem_lowLat, form_restrict]
  constructor
  · intro hu u' hu' o
    exact (hL _).1 hu _ hu' o
  · intro h
    refine (hL _).2 fun z hz o => ?_
    obtain ⟨s, t, u', -, -, hu', rfl⟩ := hsplit z hz
    have hz' : form σ J (ι *ᵥ u) (s • x + ι *ᵥ u' + t • y) = form σ J (ι *ᵥ u) (ι *ᵥ u') := by
      rw [form_add_right, form_add_right, form_smul_right, form_smul_right, (horth u).1, (horth u).2]
      ring
    rw [hz']
    exact h u' hu' o

end GlobalTheory.PlaneSkewDual
end
end

section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

noncomputable section

namespace GlobalTheory.PlaneSkewBasis

open GlobalTheory.AdelicU GlobalTheory.PlaneBasis

theorem exists_decomp {E : Type} [Field E] {n₁ : ℕ} (x y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E)
    (hind : ∀ (s t : E) (u : Fin n₁ → E), s • x + ι *ᵥ u + t • y = 0 → s = 0 ∧ t = 0 ∧ u = 0)
    (z : Fin (n₁ + 2) → E) : ∃ (s t : E) (u : Fin n₁ → E), z = s • x + ι *ᵥ u + t • y := by
  let φ : (E × E) × (Fin n₁ → E) →ₗ[E] (Fin (n₁ + 2) → E) :=
    ((LinearMap.fst E E E).smulRight x).comp (LinearMap.fst E (E × E) (Fin n₁ → E)) +
      (Matrix.mulVecLin ι).comp (LinearMap.snd E (E × E) (Fin n₁ → E)) +
      ((LinearMap.snd E E E).smulRight y).comp (LinearMap.fst E (E × E) (Fin n₁ → E))
  have hφ : ∀ p, φ p = p.1.1 • x + ι *ᵥ p.2 + p.1.2 • y := fun p => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨s, t⟩, u⟩ h
    rw [hφ] at h
    obtain ⟨rfl, rfl, rfl⟩ := hind s t u h
    rfl
  have hdim : Module.finrank E ((E × E) × (Fin n₁ → E)) = Module.finrank E (Fin (n₁ + 2) → E) := by
    simp [Module.finrank_prod]; omega
  obtain ⟨p, hp⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj z
  exact ⟨p.1.1, p.1.2, p.2, by rw [← hp, hφ]⟩

theorem exists_isSplitBasis_plane_of_indep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] Fv F v) (n₁ : ℕ) (L : Submodule (𝓞 E) (Fin (n₁ + 2) → E))
    (x y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E) (β₁ : GL (Fin n₁) (Fv F v)) (i₀ i₁ : ℕ),
    i₀ < i₁ → i₁ < n₁ + 2 →
    (∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y) →
    (∀ (s t : E) (u : Fin n₁ → E), s • x + ι *ᵥ u + t • y = 0 → s = 0 ∧ t = 0 ∧ u = 0) →
    PrimAt (GlobalTheory.AdelicU.splitPrime τ) L x → PrimAt (GlobalTheory.AdelicU.splitPrime τ) L y → GlobalTheory.AdelicU.IsSplitBasis τ (lowLat ι L) β₁ →
    ∃ β : GL (Fin (n₁ + 2)) (Fv F v), GlobalTheory.AdelicU.IsSplitBasis τ L β ∧ ∀ i : Fin (n₁ + 2),
      (i.1 = i₀ → ∀ r, β.1 r i = τ (x r)) ∧ (i.1 = i₁ → ∀ r, β.1 r i = τ (y r)) ∧
      ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, β.1 r i = (ι.map τ * β₁.1) r j := by
  intro F E _ _ _ _ _ σ _ v τ n₁ L x y ι β₁ i₀ i₁ h01 h1n hdec hind hxP hyP hβ₁
  have hx : (∀ c : E, c • x ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • x ∈ L ∧ Valued.v (τ c) = 1 := by
    simp only [valued_apply_eq_valuation]; exact hxP
  have hy : (∀ c : E, c • y ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • y ∈ L ∧ Valued.v (τ c) = 1 := by
    simp only [valued_apply_eq_valuation]; exact hyP
  have hO : ∀ a : v.adicCompletion F, a ∈ v.adicCompletionIntegers F ↔ Valued.v a ≤ 1 := fun a =>
    HeightOneSpectrum.mem_adicCompletionIntegers _ _ _
  set M := colMat τ x y ι β₁.1 i₀ i₁ with hM
  set P := Submodule.span (v.adicCompletionIntegers F) (Set.range fun i r => M r i) with hP
  set Q := LinearMap.range M.mulVecLin with hQ
  have hsmul : ∀ (c : E) (z : Fin (n₁ + 2) → E), (fun r => τ ((c • z) r)) = τ c • fun r => τ (z r) :=
    fun c z => funext fun r => by simp
  have hτmul : ∀ u : Fin n₁ → E, (fun r => τ ((ι *ᵥ u) r)) = ι.map τ *ᵥ fun r => τ (u r) :=
    fun u => funext fun r => by simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hc0 : (fun r => M r ⟨i₀, by omega⟩) = fun r => τ (x r) := funext fun r => by simp [hM, colMat]
  have hc1 : (fun r => M r ⟨i₁, h1n⟩) = fun r => τ (y r) := funext fun r => by
    simp [hM, colMat, h01.ne']
  have hcj : ∀ j : Fin n₁, (fun r => M r ⟨skip i₀ i₁ j, skip_lt j.2⟩) = fun r => (ι.map τ * β₁.1) r j :=
    fun j => funext fun r => by
      simp [hM, colMat, skip_ne_left h01, skip_ne_right h01, unskip_skip h01, j.2]
  have hPx : (fun r => τ (x r)) ∈ P := hc0 ▸ Submodule.subset_span ⟨_, rfl⟩
  have hPy : (fun r => τ (y r)) ∈ P := hc1 ▸ Submodule.subset_span ⟨_, rfl⟩
  have hPcol : ∀ j : Fin n₁, (fun r => (ι.map τ * β₁.1) r j) ∈ P := fun j =>
    hcj j ▸ Submodule.subset_span ⟨_, rfl⟩
  have hcolsum : ∀ w₁ : Fin n₁ → v.adicCompletion F,
      (ι.map τ * β₁.1) *ᵥ w₁ = ∑ j, w₁ j • (fun r => (ι.map τ * β₁.1) r j) := by
    intro w₁; funext r; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hPimg : ∀ w₁ : Fin n₁ → v.adicCompletion F, (∀ j, w₁ j ∈ v.adicCompletionIntegers F) →
      (ι.map τ * β₁.1) *ᵥ w₁ ∈ P := by
    intro w₁ hw
    rw [hcolsum]
    exact sum_mem fun j _ => smul_mem_int (hw j) (hPcol j)
  have hQcolv : ∀ i, (fun r => M r i) ∈ Q := fun i =>
    ⟨Pi.single i 1, funext fun r => by simp [Matrix.mulVec_single_one, Matrix.transpose_apply]⟩
  have hQx : (fun r => τ (x r)) ∈ Q := hc0 ▸ hQcolv _
  have hQy : (fun r => τ (y r)) ∈ Q := hc1 ▸ hQcolv _
  have hQimg : ∀ w₁ : Fin n₁ → v.adicCompletion F, (ι.map τ * β₁.1) *ᵥ w₁ ∈ Q := by
    intro w₁
    rw [hcolsum]
    exact sum_mem fun j _ => Submodule.smul_mem _ _ (hcj j ▸ hQcolv _)
  have hsplit : ∀ (s t : E) (u : Fin n₁ → E), (fun r => τ ((s • x + ι *ᵥ u + t • y) r)) = τ s • (fun r => τ (x r)) +
      (ι.map τ * β₁.1) *ᵥ ((β₁⁻¹).1 *ᵥ fun r => τ (u r)) + τ t • fun r => τ (y r) := by
    intro s t u
    have e : (fun r => τ (u r)) = β₁.1 *ᵥ ((β₁⁻¹).1 *ᵥ fun r => τ (u r)) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, ← e, ← hτmul, ← hsmul, ← hsmul]; funext r; simp
  have hSub : ∀ z ∈ L, (fun r => τ (z r)) ∈ P := by
    intro z hz
    obtain ⟨s, t, u, hs, ht, hu, rfl⟩ := hdec z hz
    have hu' : u ∈ lowLat ι L := hu
    have h1 := (hβ₁ ((β₁⁻¹).1 *ᵥ fun r => τ (u r))).2 (by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact tau_mem_splitLat τ hu')
    rw [hsplit]
    exact add_mem (add_mem (smul_mem_int ((hO _).2 (hx.1 s hs)) hPx) (hPimg _ h1))
      (smul_mem_int ((hO _).2 (hy.1 t ht)) hPy)
  have hImg : ∀ u ∈ splitLat τ (lowLat ι L), ι.map τ *ᵥ u ∈ splitLat τ L := fun u hu =>
    splitLat_induction τ _ (p := fun u => ι.map τ *ᵥ u ∈ splitLat τ L)
      (fun a ha z hz => by
        rw [Matrix.mulVec_smul, ← hτmul]; exact smul_mem_int ha (tau_mem_splitLat τ hz))
      (by rw [Matrix.mulVec_zero]; exact zero_mem _)
      (fun u w hu hw => by rw [Matrix.mulVec_add]; exact add_mem hu hw)
      (fun u hu => by rw [Matrix.mulVec_neg]; exact neg_mem hu) hu
  have hunit : ∀ z : Fin (n₁ + 2) → E, ((∀ c : E, c • z ∈ L → Valued.v (τ c) ≤ 1) ∧
      ∃ c : E, c • z ∈ L ∧ Valued.v (τ c) = 1) → (fun r => τ (z r)) ∈ splitLat τ L := by
    rintro z ⟨-, c, hc, hv⟩
    have hne : τ c ≠ 0 := by intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
    have h2 := tau_mem_splitLat τ hc
    rw [hsmul] at h2
    have hinv : (τ c)⁻¹ ∈ v.adicCompletionIntegers F := (hO _).2 (by rw [map_inv₀, hv, inv_one])
    have := smul_mem_int hinv h2
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have hColSL : ∀ i, (fun r => M r i) ∈ splitLat τ L := by
    intro i
    by_cases h0 : i.1 = i₀
    · convert hunit x hx using 1; funext r; simp [hM, colMat, h0]
    by_cases h1 : i.1 = i₁
    · convert hunit y hy using 1; funext r; simp only [hM, colMat, if_neg h0, if_pos h1]
    by_cases h2 : unskip i₀ i₁ i.1 < n₁
    · have : (fun r => M r i) = ι.map τ *ᵥ (β₁.1 *ᵥ Pi.single ⟨_, h2⟩ 1) := by
        funext r
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
        simp only [hM, colMat, if_neg h0, if_neg h1, dif_pos h2, Matrix.transpose_apply]
        rfl
      rw [this]
      refine hImg _ ((hβ₁ _).1 fun k => ?_)
      rw [Pi.single_apply]; split_ifs
      exacts [one_mem _, zero_mem _]
    · convert zero_mem (splitLat τ L) using 1; funext r; simp [hM, colMat, h0, h1, h2]
  have hPle : P ≤ splitLat τ L := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hColSL i)
  have hSLle : ∀ u ∈ splitLat τ L, u ∈ P := fun u hu =>
    splitLat_induction τ L (p := (· ∈ P)) (fun a ha z hz => smul_mem_int ha (hSub z hz)) (zero_mem _)
      (fun _ _ => add_mem) (fun _ => neg_mem) hu
  have hR : ∀ z : Fin (n₁ + 2) → E, (fun r => τ (z r)) ∈ Q := by
    intro z
    obtain ⟨s, t, u, rfl⟩ := exists_decomp x y ι hind z
    rw [hsplit]
    exact add_mem (add_mem (Submodule.smul_mem _ _ hQx) (hQimg _)) (Submodule.smul_mem _ _ hQy)
  have hsurj : Function.Surjective M.mulVec := by
    intro u
    have : u ∈ Q := by
      rw [← Finset.univ_sum_single u]
      refine sum_mem fun k _ => ?_
      have e : Pi.single k (u k) = u k • fun r => τ ((Pi.single k (1 : E) : Fin (n₁ + 2) → E) r) := by
        funext r
        by_cases h : r = k
        · subst h; simp
        · simp [h]
      rw [e]
      exact Submodule.smul_mem _ _ (hR _)
    obtain ⟨w, hw⟩ := this
    exact ⟨w, hw⟩
  have hU : IsUnit M := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  refine ⟨hU.unit, ?_, fun i => ⟨?_, ?_, ?_⟩⟩
  · intro u
    rw [IsUnit.unit_spec]
    constructor
    · intro hu; exact hPle (mem_colSpan.2 ⟨u, hu, rfl⟩)
    · intro hu
      obtain ⟨w, hw, e⟩ := mem_colSpan.1 (hSLle _ hu)
      have := Matrix.mulVec_injective_iff_isUnit.2 hU e
      rw [← this]; exact hw
  · intro h r; rw [IsUnit.unit_spec]; simp [hM, colMat, h]
  · intro h r; rw [IsUnit.unit_spec]; simp [hM, colMat, h, h01.ne']
  · intro j h r
    rw [IsUnit.unit_spec]
    have : i = ⟨skip i₀ i₁ j, skip_lt j.2⟩ := Fin.ext h
    subst this
    exact congrFun (hcj j) r

end GlobalTheory.PlaneSkewBasis
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.WeilTransNbhdD

theorem exists_nhds_finite_preimage_D : ∀ (D : D7) (a b : ℕ) (JA : Matrix (Fin a) (Fin a) D.host.E) (JB : Matrix (Fin b) (Fin b) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) →
    IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) →
    ∀ p0 : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB),
    ∃ N ∈ nhds p0, ∃ L₁' L₂' : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      IsOpen (L₁' : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
      IsCompact (L₁' : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
      IsOpen (L₂' : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
      ∀ p ∈ N, ∀ x ∈ L₁', ∀ y ∈ L₂', ∃ x' ∈ L₁, ∃ y' ∈ L₂,
        co.e (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) p
          (co.e.symm (GlobalTheory.WeilCont.adeleJoin D.host.F 0 x', GlobalTheory.WeilCont.adeleJoin D.host.F 0 y'))) =
          (GlobalTheory.WeilCont.adeleJoin D.host.F 0 x, GlobalTheory.WeilCont.adeleJoin D.host.F 0 y) := by
  intro D a b JA JB ξ κ _ co L₁ L₂ hL₁ hL₂ p0
  exact GlobalTheory.WeilTransNbhd.exists_nhds_finite_preimage D.host.F D.host.E D.sp.cm.sig a b JA JB ξ κ co L₁ L₂ hL₁ hL₂ p0

end GlobalTheory.WeilTransNbhdD
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchTransportHost

theorem archDir_transport_host : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (m n : ℕ) (JA : Matrix (Fin m) (Fin m) D.host.E)
    (JB : Matrix (Fin n) (Fin n) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ)),
    (∀ p w, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
      om p (co.rho ψ w φ) = co.rho ψ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) p w) (om p φ)) →
    ∃ M : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
        GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) → ((κ → mixedEmbedding.mixedSpace D.host.F) × (κ → mixedEmbedding.mixedSpace D.host.F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace D.host.F) × (κ → mixedEmbedding.mixedSpace D.host.F)),
      (∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        om p (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair D.host.F (M p h)) φ) =
          GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair D.host.F h) (om p φ)) ∧
      ∀ h, Continuous fun p => M p h := by
  intro D ψ m n JA JB ξ κ _ co om hom
  exact GlobalTheory.ArchTransportDir.archDir_transport D.host.F D.host.E D.sp.cm.sig ψ m n JA JB ξ κ co om hom

end GlobalTheory.ArchTransportHost

end
end
