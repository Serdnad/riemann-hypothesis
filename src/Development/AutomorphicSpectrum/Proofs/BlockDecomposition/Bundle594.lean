module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle003
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.InUQT
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle146
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle308
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle524
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapHBijOfRes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle583
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.GunrResCard

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def redCoord {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (S : Subring (Fv F v ⊗[F] E)) (hS : (S : Set (Fv F v ⊗[F] E)) = Rv bs v)
    (ϖ : v.adicCompletionIntegers F) (x : S) (k : Fin d) :
    v.adicCompletionIntegers F ⧸ Ideal.span {ϖ} :=
  Ideal.Quotient.mk _ ⟨(Algebra.TensorProduct.basis (Fv F v) bs).repr x k,
    (show (x : Fv F v ⊗[F] E) ∈ Rv bs v from hS ▸ x.2) k⟩

theorem redCoord_eq_iff {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (S : Subring (Fv F v ⊗[F] E)) (hS : (S : Set (Fv F v ⊗[F] E)) = Rv bs v)
    (ϖ : v.adicCompletionIntegers F) (hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S) (x y : S) :
    redCoord bs v S hS ϖ x = redCoord bs v S hS ϖ y ↔ x - y ∈ lev (⟨_, hϖ⟩ : S) 1 := by
  set B := Algebra.TensorProduct.basis (Fv F v) bs with hB
  have hsm : ∀ z : Fv F v ⊗[F] E, z * algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ = (ϖ : Fv F v) • z := by
    intro z
    rw [Algebra.smul_def, mul_comm]
  rw [show lev (⟨_, hϖ⟩ : S) 1 = Ideal.span {(⟨_, hϖ⟩ : S) ^ 1} from rfl, pow_one,
    Ideal.mem_span_singleton']
  constructor
  · intro h
    have hk : ∀ k, ∃ t : v.adicCompletionIntegers F, (t : Fv F v) * ϖ = B.repr x k - B.repr y k := by
      intro k
      have h1 := congrFun h k
      simp only [redCoord] at h1
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h1
      obtain ⟨t, ht⟩ := h1
      refine ⟨t, ?_⟩
      have h2 := congrArg Subtype.val ht
      push_cast at h2
      exact h2
    choose t ht using hk
    let z : Fv F v ⊗[F] E := B.equivFun.symm (fun k => (t k : Fv F v))
    have hz : ∀ k, B.repr z k = t k := by
      intro k
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    have hzS : z ∈ S := by
      have hzR : z ∈ Rv bs v := by
        intro k
        rw [hz k]
        exact (t k).2
      rw [← hS] at hzR
      exact hzR
    refine ⟨⟨z, hzS⟩, ?_⟩
    apply Subtype.ext
    show z * algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ = (x : Fv F v ⊗[F] E) - y
    rw [hsm, B.ext_elem_iff]
    intro k
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hz k, map_sub, Finsupp.sub_apply, mul_comm]
    exact ht k
  · rintro ⟨a, ha⟩
    have hxy : (x : Fv F v ⊗[F] E) - y = (ϖ : Fv F v) • (a : Fv F v ⊗[F] E) := by
      rw [← hsm]
      exact (congrArg Subtype.val ha).symm
    have haR : (a : Fv F v ⊗[F] E) ∈ Rv bs v := hS ▸ a.2
    funext k
    simp only [redCoord]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    refine ⟨⟨B.repr a k, haR k⟩, ?_⟩
    apply Subtype.ext
    push_cast
    have h3 := congrArg (fun w => B.repr w k) hxy
    simp only [map_sub, Finsupp.sub_apply, map_smul, Finsupp.smul_apply, smul_eq_mul] at h3
    rw [mul_comm, ← h3]

theorem redCoord_surjective {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (S : Subring (Fv F v ⊗[F] E)) (hS : (S : Set (Fv F v ⊗[F] E)) = Rv bs v)
    (ϖ : v.adicCompletionIntegers F) : Function.Surjective (redCoord bs v S hS ϖ) := by
  intro g
  set B := Algebra.TensorProduct.basis (Fv F v) bs with hB
  choose t ht using fun k => Ideal.Quotient.mk_surjective (g k)
  let z : Fv F v ⊗[F] E := B.equivFun.symm (fun k => (t k : Fv F v))
  have hz : ∀ k, B.repr z k = t k := by
    intro k
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hzS : z ∈ S := by
    have hzR : z ∈ Rv bs v := by
      intro k
      rw [hz k]
      exact (t k).2
    rw [← hS] at hzR
    exact hzR
  refine ⟨⟨z, hzS⟩, ?_⟩
  funext k
  simp only [redCoord]
  rw [← ht k]
  congr 1
  exact Subtype.ext (hz k)

theorem card_quot {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (S : Subring (Fv F v ⊗[F] E)) (hS : (S : Set (Fv F v ⊗[F] E)) = Rv bs v)
    (ϖ : v.adicCompletionIntegers F) (hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S) :
    Nat.card (S ⧸ lev (⟨_, hϖ⟩ : S) 1) = Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) ^ d := by
  have hsurj := Ideal.Quotient.mk_surjective (I := lev (⟨_, hϖ⟩ : S) 1)
  let sec := Function.surjInv hsurj
  have hsec : ∀ q, Ideal.Quotient.mk _ (sec q) = q := Function.surjInv_eq hsurj
  let g : S ⧸ lev (⟨_, hϖ⟩ : S) 1 → (Fin d → v.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) :=
    fun q => redCoord bs v S hS ϖ (sec q)
  have hg : Function.Bijective g := by
    constructor
    · intro q₁ q₂ h
      rw [← hsec q₁, ← hsec q₂, Ideal.Quotient.eq]
      exact (redCoord_eq_iff bs v S hS ϖ hϖ _ _).mp h
    · intro w
      obtain ⟨x, hx⟩ := redCoord_surjective bs v S hS ϖ w
      refine ⟨Ideal.Quotient.mk _ x, ?_⟩
      rw [← hx]
      apply (redCoord_eq_iff bs v S hS ϖ hϖ _ _).mpr
      rw [← Ideal.Quotient.eq, hsec]
  rw [Nat.card_congr (Equiv.ofBijective g hg), Nat.card_fun, Nat.card_fin]

theorem q3 : PositivityTheory.SiegelWeilFormula.Gunr.Q3 := by
  intro F E _ _ _ _ _ σ d bs v S σS ϖ hQ hϖ
  obtain ⟨hCM, -, hS, -, -, -, -, hcard⟩ := hQ
  have hd : d = 2 := by
    rw [← hCM.2.2.1, Module.finrank_eq_card_basis bs, Fintype.card_fin]
  subst hd
  rw [card_quot bs v S hS ϖ hϖ, hcard]

end GlobalTheory.CompanionTheory.GunrResCard
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.ResidueInvolution

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_tmul (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (a : R) (e : E) :
    sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl

theorem sigR_sigR {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] (x : R ⊗[F] E) :
    sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e => rw [sigR_tmul, sigR_tmul, sigma_sigma h]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz]

theorem sigR_algebraMap (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (c : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) c) = algebraMap R (R ⊗[F] E) c := by
  rw [Algebra.TensorProduct.algebraMap_apply, sigR_tmul]
  simp

theorem one_lt_absNorm (v : HeightOneSpectrum (𝓞 F)) : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

theorem eq_zero_of_forall_pow {v : HeightOneSpectrum (𝓞 F)} {ϖ c : Fv F v} (h0 : ϖ ≠ 0) (h1 : ‖ϖ‖ < 1)
    (hc : ∀ j : ℕ, (ϖ⁻¹) ^ j * c ∈ v.adicCompletionIntegers F) : c = 0 := by
  by_contra hne
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hne) h1
  have h2 : ‖(ϖ⁻¹) ^ j * c‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 (hc j)
  rw [norm_mul, norm_pow, norm_inv, inv_pow] at h2
  have h3 : 0 < ‖ϖ‖ ^ j := pow_pos (norm_pos_iff.2 h0) j
  rw [inv_mul_le_iff₀ h3, mul_one] at h2
  exact absurd hj (not_lt.2 h2)

theorem q1 : PositivityTheory.SiegelWeilFormula.Gunr.Q1 := by
  intro F E _ _ _ _ _ σ d bs v S σS ϖ hH hϖ
  obtain ⟨hσ, -, hcar, hsig, h0, h1, -, -⟩ := hH
  refine ⟨fun a => Subtype.ext ?_, Subtype.ext ?_, ?_, ?_, one_lt_absNorm v⟩
  · rw [hsig, hsig, sigR_sigR hσ]
  · rw [hsig, sigR_algebraMap]
  · intro x y hxy
    have e : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * (x : Fv F v ⊗[F] E) =
        algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * (y : Fv F v ⊗[F] E) := congrArg Subtype.val hxy
    rw [← Algebra.smul_def, ← Algebra.smul_def] at e
    exact Subtype.ext (smul_right_injective _ h0 e)
  · intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hb1 : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * (b : Fv F v ⊗[F] E) = 1 := congrArg Subtype.val hb
    have hb2 : (b : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ : Fv F v)⁻¹ := by
      have e : algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ : Fv F v)⁻¹ *
          algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ = 1 := by
        rw [← map_mul, inv_mul_cancel₀ h0, map_one]
      calc (b : Fv F v ⊗[F] E)
          = (algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ : Fv F v)⁻¹ *
              algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) * (b : Fv F v ⊗[F] E) := by rw [e, one_mul]
        _ = _ := by rw [mul_assoc, hb1, mul_one]
    have hc : ∀ k, (Algebra.TensorProduct.basis (Fv F v) bs).repr 1 k = 0 := fun k => by
      refine eq_zero_of_forall_pow h0 h1 fun j => ?_
      have hm : ((b ^ j : S) : Fv F v ⊗[F] E) ∈ Rv bs v := by
        rw [← hcar]
        exact (b ^ j).2
      have e : ((b ^ j : S) : Fv F v ⊗[F] E) = ((ϖ : Fv F v)⁻¹ ^ j) • (1 : Fv F v ⊗[F] E) := by
        rw [Subring.coe_pow, hb2, ← map_pow, Algebra.algebraMap_eq_smul_one]
      have := hm k
      rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul] at this
      exact this
    have h10 : (1 : Fv F v ⊗[F] E) = 0 :=
      (Algebra.TensorProduct.basis (Fv F v) bs).repr.map_eq_zero_iff.1 (Finsupp.ext hc)
    exact one_ne_zero h10

end GlobalTheory.CompanionTheory.ResidueInvolution

end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.ValuationCompleteness

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr Filter _root_.Topology
open scoped TensorProduct

section Abstract

variable {K A : Type} [NormedField K] [CommRing A] [Algebra K A] {d : ℕ}
  (b : Module.Basis (Fin d) K A) (S : Subring A)

theorem mem_lev_iff (hS : ∀ x, x ∈ S ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {ϖ : K} (h0 : ϖ ≠ 0)
    (hϖ : algebraMap K A ϖ ∈ S) (a : S) (k : ℕ) :
    a ∈ lev (⟨_, hϖ⟩ : S) k ↔ ∀ i, ‖b.repr (a : A) i‖ ≤ ‖ϖ‖ ^ k := by
  have hpow : ∀ c : A, c * (algebraMap K A ϖ) ^ k = ϖ ^ k • c := by
    intro c
    rw [← map_pow, Algebra.smul_def, mul_comm]
  have hcoe : ∀ c : S, ((c * (⟨_, hϖ⟩ : S) ^ k : S) : A) = ϖ ^ k • (c : A) := by
    intro c
    rw [← hpow]
    rfl
  constructor
  · intro ha i
    rw [lev, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, hc⟩ := ha
    have hc' : (a : A) = ϖ ^ k • (c : A) := by
      rw [← hc, hcoe]
    rw [hc', map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_pow]
    have hci := (hS c).1 c.2 i
    calc ‖ϖ‖ ^ k * ‖b.repr (c : A) i‖ ≤ ‖ϖ‖ ^ k * 1 := by gcongr
      _ = ‖ϖ‖ ^ k := mul_one _
  · intro ha
    rw [lev, Ideal.mem_span_singleton']
    have hpos : 0 < ‖ϖ‖ ^ k := pow_pos (norm_pos_iff.mpr h0) k
    have hcS : (ϖ ^ k)⁻¹ • (a : A) ∈ S := by
      rw [hS]
      intro i
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_inv, norm_pow,
        inv_mul_le_iff₀ hpos, mul_one]
      exact ha i
    refine ⟨⟨_, hcS⟩, ?_⟩
    apply Subtype.ext
    rw [hcoe]
    change ϖ ^ k • ((ϖ ^ k)⁻¹ • (a : A)) = (a : A)
    rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero k h0), one_smul]

theorem separated (hS : ∀ x, x ∈ S ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {ϖ : K} (h0 : ϖ ≠ 0) (h1 : ‖ϖ‖ < 1)
    (hϖ : algebraMap K A ϖ ∈ S) (a : S) (h : ∀ k, a ∈ lev (⟨_, hϖ⟩ : S) k) : a = 0 := by
  have hi : ∀ i, b.repr (a : A) i = 0 := by
    intro i
    have hle : ∀ k : ℕ, ‖b.repr (a : A) i‖ ≤ ‖ϖ‖ ^ k :=
      fun k => (mem_lev_iff b S hS h0 hϖ a k).1 (h k) i
    have ht : Tendsto (fun k : ℕ => ‖ϖ‖ ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h1
    exact norm_le_zero_iff.mp (ge_of_tendsto' ht hle)
  have hr : b.repr (a : A) = 0 := by
    ext i
    exact hi i
  have ha : (a : A) = 0 := (LinearEquiv.map_eq_zero_iff b.repr).mp hr
  exact_mod_cast ha

variable [CompleteSpace K] [IsUltrametricDist K]

theorem complete (hS : ∀ x, x ∈ S ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {ϖ : K} (h0 : ϖ ≠ 0) (h1 : ‖ϖ‖ < 1)
    (hϖ : algebraMap K A ϖ ∈ S) (f : ℕ → S) (hf : ∀ k, f (k + 1) - f k ∈ lev (⟨_, hϖ⟩ : S) k) :
    ∃ a, ∀ k, a - f k ∈ lev (⟨_, hϖ⟩ : S) k := by
  set x : ℕ → Fin d → K := fun k i => b.repr (f k : A) i with hx
  have hstep : ∀ k i, ‖x (k + 1) i - x k i‖ ≤ ‖ϖ‖ ^ k := by
    intro k i
    have := (mem_lev_iff b S hS h0 hϖ _ k).1 (hf k) i
    simpa [hx, map_sub] using this
  have hn0 : 0 ≤ ‖ϖ‖ := norm_nonneg _
  have hle1 : ‖ϖ‖ ≤ 1 := le_of_lt h1
  have hfar : ∀ i k m, k ≤ m → ‖x m i - x k i‖ ≤ ‖ϖ‖ ^ k := by
    intro i k m hkm
    induction m, hkm using Nat.le_induction with
    | base => simp
    | succ m hkm ih =>
      have e : x (m + 1) i - x k i = (x (m + 1) i - x m i) + (x m i - x k i) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
      exact (hstep m i).trans (pow_le_pow_of_le_one hn0 hle1 hkm)
  have hcau : ∀ i, CauchySeq (fun k => x k i) := by
    intro i
    refine cauchySeq_of_le_geometric ‖ϖ‖ 1 h1 (fun n => ?_)
    rw [dist_eq_norm, ← norm_neg, neg_sub, one_mul]
    exact hstep n i
  choose c hc using fun i => cauchySeq_tendsto_of_complete (hcau i)
  have hbd : ∀ i k, ‖c i - x k i‖ ≤ ‖ϖ‖ ^ k := by
    intro i k
    have ht : Tendsto (fun m => ‖x m i - x k i‖) atTop (𝓝 ‖c i - x k i‖) :=
      ((hc i).sub_const _).norm
    refine le_of_tendsto ht ?_
    filter_upwards [eventually_ge_atTop k] with m hm
    exact hfar i k m hm
  set aA : A := b.equivFun.symm c with haA
  have hrep : ∀ i, b.repr aA i = c i := by
    intro i
    rw [← b.equivFun_apply, haA, LinearEquiv.apply_symm_apply]
  have hmem : aA ∈ S := by
    rw [hS]
    intro i
    rw [hrep]
    have e : c i = (c i - x 0 i) + x 0 i := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · simpa using hbd i 0
    · exact (hS _).1 (f 0).2 i
  refine ⟨⟨aA, hmem⟩, fun k => ?_⟩
  rw [mem_lev_iff b S hS h0 hϖ]
  intro i
  have e : ((⟨aA, hmem⟩ - f k : S) : A) = aA - (f k : A) := rfl
  rw [e, map_sub, Finsupp.sub_apply, hrep]
  exact hbd i k

end Abstract

theorem q2 : Q2 := by
  intro F E _ _ _ _ _ σ d bs v S σS ϖ hQ hϖ
  obtain ⟨-, -, hSR, -, h0, h1, -, -⟩ := hQ
  have hS : ∀ x, x ∈ S ↔ ∀ i, ‖(Algebra.TensorProduct.basis (Fv F v) bs).repr x i‖ ≤ 1 := by
    intro x
    rw [← SetLike.mem_coe, hSR]
    exact forall_congr' fun i =>
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).trans
        Valued.toNormedField.norm_le_one_iff.symm
  exact ⟨fun a ha => separated _ S hS h0 h1 hϖ a ha, fun f hf => complete _ S hS h0 h1 hϖ f hf⟩

end GlobalTheory.CompanionTheory.ValuationCompleteness

end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution CrystallineSemistableComparison.Pb.LsQ

namespace GlobalTheory.CompanionTheory.GradedDegreeZeroIsLocal

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {ρ : O →+* k}

def polyV {m : ℕ} {𝒱 : Set X.Opens} (P : Poly (sP (stF q ρ m 𝒱))) : Poly (sV q ρ m 𝒱) where
  P := P.P
  j := P.j
  X := P.X
  X_mem := P.X_mem
  univ := P.univ
  span := P.span

def frameV {m : ℕ} {𝒱 : Set X.Opens} {d : ℕ} (E : Frame (sP (stF q ρ m 𝒱)) d) : Frame (sV q ρ m 𝒱) d where
  D := E.D
  ne := E.ne
  τ := E.τ
  mem := E.mem
  add := E.add
  nat := E.nat
  bij := E.bij

theorem nil_m (k : Type) [Field k] [CharP k l] [PerfectRing k l] (m : ℕ) : IsNilpotent ((l : ℕ) : Wc.Wm l k m) := ⟨m, by
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ m})), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _⟩

theorem o_bij {n : ℕ} (hn : n ≠ 0) (𝒱 : Set X.Opens) (T : (stF q ρ (n + 1) 𝒱).FullSubcategory) :
    Function.Bijective (((mqS q ρ hn 𝒱).o (IdF.span _ ((l : WittVector l k) ^ n)) fun _ => le_rfl).τ T) := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (show T.obj.B ⧸ lI n T.obj from x)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective (show T.obj.B ⧸ lI n T.obj from y)
    exact congrArg Subtype.val hxy
  · rintro ⟨z, hz⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk (lI n T.obj) a, Subtype.ext rfl⟩

theorem iso_bij {m : ℕ} {T T' : Thick (Wc.L l (B.schFn q) ρ m)} (e : T ≅ T') : Function.Bijective e.hom.φ := by
  refine Function.bijective_iff_has_inverse.2 ⟨e.inv.φ, fun x => ?_, fun x => ?_⟩
  · exact RingHom.congr_fun (congrArg (fun f => f.φ) e.hom_inv_id) x
  · exact RingHom.congr_fun (congrArg (fun f => f.φ) e.inv_hom_id) x



theorem local_bij (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) {n : ℕ} (hn : n ≠ 0) {W : X.Opens} {d : ℕ}
    (cW : Coord q W d) (j : ℕ) :
    Function.Bijective (((mqS q ρ hn {W}).o (IdF.span _ ((l : WittVector l k) ^ n)) (fun _ => le_rfl)).pull j) := by
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  obtain ⟨c', hF', -⟩ := GlobalTheory.CompanionTheory.FlatChartP.exists_flat_chart (Wc.pd l k (n + 1)) l hl0 (nil_m k (n + 1)) q
    ((Wc.res l k (n + 1)).comp ρ) cW
  obtain ⟨c, e, hec, hfl⟩ := GlobalTheory.T.witt_chart_descend_level q ρ hn c'
  have hF : FlatT c.D := hfl (GlobalTheory.T.flat_thickening_quotient l k O (B.schFn q) ρ n hn c'.D hF')
  obtain ⟨PA, hPA⟩ := poly_all (Wc.pd l k n) l hl0 q ((Wc.res l k n).comp ρ) FlatT (Or.inr rfl) {W}
  obtain ⟨PB, hPB⟩ := poly_all (Wc.pd l k (n + 1)) l hl0 q ((Wc.res l k (n + 1)).comp ρ) FlatT (Or.inr rfl) {W}
  have hgA := GlobalTheory.CompanionTheory.ChartMaps.good c
  have hgB := GlobalTheory.CompanionTheory.ChartMaps.good c'
  have hQA : ∀ T, stF q ρ n {W} T → InU W T := by
    rintro T ⟨-, V, rfl, hV⟩
    exact hV
  have hQB : ∀ T, stF q ρ (n + 1) {W} T → InU W T := by
    rintro T ⟨-, V, rfl, hV⟩
    exact hV
  have hDA : stF q ρ n {W} c.D := ⟨hF, W, rfl, c.inV⟩
  have hDB : stF q ρ (n + 1) {W} c'.D := ⟨hF', W, rfl, c'.inV⟩
  let E : Frame (sV q ρ n {W}) d := frameV (c.frame hgA _ hQA hDA)
  let E' : Frame (sV q ρ (n + 1) {W}) d := frameV (c'.frame hgB _ hQB hDB)
  let M := mqS q ρ hn {W}
  let e' : E.D ⟶ M.G.obj E'.D := ObjectProperty.homMk e.hom
  have he : M.Fr E E' e' := by
    intro i T s₁ s₂
    change M.ρ T (qφ s₂.hom (e.hom.φ (c.t i)) - qφ s₁.hom (e.hom.φ (c.t i))) =
      Ideal.Quotient.mk _ (s₂.hom.φ (c'.t i) - s₁.hom.φ (c'.t i))
    rw [hec]
    rfl
  let b : ℤ → IdF (sV q ρ (n + 1) {W}).A := fun _ => IdF.span _ ((l : WittVector l k) ^ n)
  exact GlobalTheory.CompanionTheory.LocCmp.localComparison M (polyV PA) (polyV PB) E E' e' he b (fun _ _ => le_rfl) 0 (hPA 0).2.1
    (fun r _ => ((hPB r).2.2 (Ideal.Quotient.mk _ ((l : WittVector l k) ^ n))).2.2)
    (fun r' _ _ => (o_bij hn {W} E'.D).comp (iso_bij e)) j

end GlobalTheory.CompanionTheory.GradedDegreeZeroIsLocal

end
end
