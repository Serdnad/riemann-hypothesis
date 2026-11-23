module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHEqThSDictionary
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsGoodSplitPrimeCmField
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsIntegralBasisHermitianMatricesDual
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsNearlyPrimitive
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TracePairingGeDetImPowHermitianHalfSpace
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle006
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInnerProductSelfNonnegBounds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.HaarProp

open HaarLevel

theorem mem_perSub' {K κ ι : Type} [Field K] (R : ℕ) (x : Matrix κ ι K) :
    x ∈ perSub K κ ι R ↔ ∃ y, IntM y ∧ R • y = x := by
  rw [mem_perSub]
  simp only [intM_iff]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨_, ⟨y, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩; exact ⟨y, rfl⟩

theorem transport {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (t : AddSubgroup B)
    (φ : B → ℂ) (hφ : ∀ x, ∀ y ∈ t, φ (x + y) = φ x) :
    ∃ g : (A ⧸ t.comap e.toAddMonoidHom) ≃ (B ⧸ t), ∀ q, φ (e q.out) = φ (g q).out := by
  refine ⟨(QuotientAddGroup.congr (t.comap e.toAddMonoidHom) t e
    (AddSubgroup.map_comap_eq_self_of_surjective e.surjective t)).toEquiv, fun q => ?_⟩
  set g := QuotientAddGroup.congr (t.comap e.toAddMonoidHom) t e
    (AddSubgroup.map_comap_eq_self_of_surjective e.surjective t)
  have h2 : g q = (e q.out : B ⧸ t) := by
    conv_lhs => rw [← QuotientAddGroup.out_eq' q]
    rfl
  have h3 : ((g q).out : B ⧸ t) = (e q.out : B ⧸ t) := by
    rw [QuotientAddGroup.out_eq', h2]
  have := hφ (g q).out _ (QuotientAddGroup.eq.1 h3)
  change _ = φ (g q).out
  rw [← this]; congr 1; abel

variable {K K' κ ι κ' ι' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
  [Fintype κ] [Fintype ι] [Fintype κ'] [Fintype ι']

theorem haar_comp (e : Matrix κ ι K ≃+ Matrix κ' ι' K') (D D' : ℕ) (hD : 0 < D) (hD' : 0 < D')
    (h1 : ∀ x, IntM x → IntM (D • e x)) (h2 : ∀ x, IntM x → IntM (D' • e.symm x))
    (hd : Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι) =
      Module.finrank ℚ K' * (Fintype.card κ' * Fintype.card ι')) :
    ∃ c : ℝ, 0 < c ∧ ∀ φ : Matrix κ' ι' K' → ℂ, IsSB φ → haar (fun m => φ (e m)) = c * haar φ := by
  set d := Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι) with hdd
  let t : ℕ → AddSubgroup (Matrix κ ι K) := fun R => (perSub K' κ' ι' R).comap e.toAddMonoidHom
  have ht : ∀ R x, x ∈ t R ↔ ∃ y, IntM y ∧ R • y = e x := fun R x => mem_perSub' R (e x)
  have hle : ∀ R, perSub K κ ι (R * D) ≤ t R := by
    intro R x hx
    obtain ⟨y, hy, rfl⟩ := (mem_perSub' _ _).1 hx
    exact (ht _ _).2 ⟨_, h1 y hy, by rw [map_nsmul, mul_smul]⟩
  have hne : (perSub K κ ι D).relIndex (t 1) ≠ 0 := by
    have hle' : t (1 * (D * D')) ≤ perSub K κ ι D := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := (ht _ _).1 hx
      refine (mem_perSub' _ _).2 ⟨_, h2 y hy, ?_⟩
      rw [← mul_smul, ← map_nsmul, ← one_mul (D * D'), hxy, e.symm_apply_apply]
    have h0 : (t (1 * (D * D'))).relIndex (t 1) ≠ 0 := by
      rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective e.surjective,
        relIndex_perSub _ _ one_pos]
      positivity
    exact fun h => h0 (AddSubgroup.relIndex_eq_zero_of_le_left hle' h)
  have hsc : ∀ R, 0 < R → (perSub K κ ι (R * D)).relIndex (t R) =
      (perSub K κ ι D).relIndex (t 1) := by
    intro R hR
    have ha : (perSub K κ ι (R * D)).comap (nsmulAddMonoidHom R) = perSub K κ ι D := by
      ext x
      simp only [AddSubgroup.mem_comap, mem_perSub', nsmulAddMonoidHom_apply, mul_smul,
        nsmul_cancel hR]
    have hb : (t 1).map (nsmulAddMonoidHom R) = t R := by
      ext x
      simp only [AddSubgroup.mem_map, ht, nsmulAddMonoidHom_apply, one_smul]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨_, hz, by rw [map_nsmul]⟩
      · rintro ⟨y, hy, hxy⟩
        refine ⟨e.symm y, ⟨y, hy, by simp⟩, ?_⟩
        rw [← map_nsmul, hxy, e.symm_apply_apply]
    rw [← ha, AddSubgroup.relIndex_comap, hb]
  refine ⟨((perSub K κ ι D).relIndex (t 1) : ℝ) / (D : ℝ) ^ d, by positivity, fun φ hφ => ?_⟩
  obtain ⟨S, hS, hψ⟩ : IsSB (fun m => φ (e m)) :=
    Dict.isSB_comp e.toAddMonoidHom D D' hD hD' h1 (fun x hx => by simpa using h2 _ hx) hφ
  obtain ⟨R, hR, hφ⟩ := hφ
  obtain ⟨g, hg⟩ := transport e (perSub K' κ' ι' R) φ (periodic hφ)
  have hidx : (perSub K κ ι (R * D * S)).relIndex (t R) =
      S ^ d * (perSub K κ ι D).relIndex (t 1) := by
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ (perSub_le (R * D) S) (hle R), hsc R hR,
      relIndex_perSub _ _ (by positivity)]
  have hfin : (Function.support fun q : Matrix κ ι K ⧸ t R => φ (e q.out)).Finite := by
    have := (finite_support hR hφ).preimage (f := g) g.injective.injOn
    refine this.subset fun q hq => ?_
    simp only [Set.mem_preimage, Function.mem_support] at hq ⊢
    rwa [← hg]
  have hsum := finsum_quotient_of_le ((perSub_le (R * D) S).trans (hle R))
    (by rw [hidx]; positivity) (fun m => φ (e m))
    (fun x y hy => by rw [map_add (f := _)]; exact periodic hφ _ _ hy) hfin
  have hsum2 : ∑ᶠ q : Matrix κ ι K ⧸ t R, φ (e q.out) =
      ∑ᶠ q : Matrix κ' ι' K' ⧸ perSub K' κ' ι' R, φ q.out := by
    rw [← finsum_comp_equiv g]
    exact finsum_congr hg
  rw [(haar_eq_haarAt _ _ _ S _ hS hψ).1, (haar_eq_haarAt _ _ _ R _ hR hφ).1,
    ← haarAt_mul hS hψ (S := R * D) (by positivity), mul_comm S, haarAt, haarAt, hsum, hsum2, hidx,
    ← hd, ← hdd]
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hD'' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  push_cast
  rw [mul_pow, mul_pow]
  field_simp

end GlobalTheory.SW.HaarProp

theorem GlobalTheory.SW.haar_ofQ_proportional : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → haar (fun m : Matrix (Fin n) (QI E N) ℚ => φ (ofQ m)) = c * haar φ := by
  intro E _ _ _ n N
  obtain ⟨D, hD, h⟩ := Dict.exists_den_ofQ (E := E) (n := n) (N := N)
  obtain ⟨D', hD', h'⟩ := Dict.exists_den_symm (E := E) (n := n) (N := N)
  exact HaarProp.haar_comp (Dict.ofQEquiv E n N) D D' hD hD' h h' (by simp; ring)
end

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW

variable {N : ℕ}

theorem norm_det_le_add_posSemidef (A P : Matrix (Fin N) (Fin N) ℂ) (hA : A.PosDef)
    (hP : P.PosSemidef) : ‖A.det‖ ≤ ‖(A + P).det‖ := by
  have h1 : imH (I • A) = A := by
    have := imH_add_I_smul 0 A hA.1
    simpa [imH] using this
  have h := (norm_det_denom_mono N 1 0 (I • A) P (by simp) (by simpa using Matrix.PosDef.one)
    (by rwa [h1]) hP).2
  simpa [← smul_add, det_smul] using h

theorem star_dotProduct_self_eq_sum (x : Fin N → ℂ) :
    star x ⬝ᵥ x = ((∑ a, ‖x a‖ ^ 2 : ℝ) : ℂ) := by
  simp [dotProduct, Complex.conj_mul']

theorem posSemidef_sub_mul_conjTranspose (X : Matrix (Fin N) (Fin N) ℂ) (B : ℝ)
    (hX : ∀ a b, ‖X a b‖ ≤ B) :
    ((((N : ℝ) ^ 2 * B ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - X * Xᴴ).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine IsHermitian.sub ?_ (isHermitian_mul_conjTranspose_self X)
    simp [IsHermitian]
  · have h1 : star x ⬝ᵥ (X * Xᴴ) *ᵥ x = star (Xᴴ *ᵥ x) ⬝ᵥ (Xᴴ *ᵥ x) := by
      rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec, mulVec_mulVec]
    rw [sub_mulVec, dotProduct_sub, h1, smul_mulVec, one_mulVec, dotProduct_smul,
      star_dotProduct_self_eq_sum, star_dotProduct_self_eq_sum, smul_eq_mul, ← ofReal_mul,
      ← ofReal_sub, Complex.zero_le_real, sub_nonneg]
    have h2 : ∀ a, ‖(Xᴴ *ᵥ x) a‖ ^ 2 ≤ B ^ 2 * (N * ∑ b, ‖x b‖ ^ 2) := by
      intro a
      have h3 : ‖(Xᴴ *ᵥ x) a‖ ≤ B * ∑ b, ‖x b‖ := by
        rw [Finset.mul_sum]
        refine (norm_sum_le Finset.univ fun b => Xᴴ a b * x b).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [norm_mul, conjTranspose_apply, norm_star]
        exact mul_le_mul_of_nonneg_right (hX b a) (norm_nonneg _)
      have h4 : (∑ b, ‖x b‖) ^ 2 ≤ N * ∑ b, ‖x b‖ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun b => ‖x b‖)
      calc ‖(Xᴴ *ᵥ x) a‖ ^ 2 ≤ (B * ∑ b, ‖x b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
        _ = B ^ 2 * (∑ b, ‖x b‖) ^ 2 := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left h4 (sq_nonneg B)
    refine (Finset.sum_le_sum fun a _ => h2 a).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

theorem denom_mul_conjTranspose (C D X : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian)
    (hX : X.IsHermitian) (δ : ℝ) :
    (C * (X + (I * δ) • 1) + D) * (C * (X + (I * δ) • 1) + D)ᴴ =
      (C * X + D) * (C * X + D)ᴴ + ((δ : ℂ) ^ 2) • (C * Cᴴ) := by
  have h1 : D * Cᴴ = C * Dᴴ := by simpa using h.eq
  have h2 : star (I * δ : ℂ) = -(I * δ) := by simp
  have h3 : (δ : ℂ) ^ 2 = -((I * δ) * (I * δ)) := by
    have : I * δ * (I * δ) = (I * I) * (δ : ℂ) ^ 2 := by ring
    rw [this, I_mul_I]; ring
  rw [h3]
  generalize (I * δ : ℂ) = t at h2 ⊢
  simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_smul, conjTranspose_one, hX.eq, h2,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, h1]
  module

theorem norm_det_mul_conjTranspose (A : Matrix (Fin N) (Fin N) ℂ) :
    (A * Aᴴ).det = ((‖A.det‖ ^ 2 : ℝ) : ℂ) := by
  rw [det_mul, det_conjTranspose, star_def, Complex.mul_conj']
  simp

theorem norm_det_denom_compare :
    ∀ (N : ℕ) (δ B : ℝ), 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ C D Z : Matrix (Fin N) (Fin N) ℂ, (C * Dᴴ).IsHermitian → (C * Cᴴ + D * Dᴴ).PosDef → (imH Z - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef → (∀ a b, ‖(Z + Zᴴ) a b‖ ≤ B) → c * ‖(C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D).det‖ ≤ ‖(C * Z + D).det‖ ∧ ‖(C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D).det‖ ^ 2 = (C * Cᴴ + D * Dᴴ).det.re := by
  intro N δ B hδ
  set K : ℝ := (N : ℝ) ^ 2 * (B / 2) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set c : ℝ := δ ^ 2 / (2 * δ ^ 2 + 1 + 2 * K) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : 0 ≤ 1 - 2 * c := by
    rw [hc, sub_nonneg, ← mul_div_assoc, div_le_one (by positivity)]
    linarith
  have hc2 : 0 ≤ δ ^ 2 - c - 2 * c * K := by
    have : c * (2 * δ ^ 2 + 1 + 2 * K) = δ ^ 2 := by rw [hc]; field_simp
    nlinarith [mul_pos hc0 (pow_pos hδ 2)]
  refine ⟨Real.sqrt (c ^ N), by positivity, fun C D Z h hp hZ hB => ?_⟩
  have hG : (C * Cᴴ + D * Dᴴ).det =
      ((‖(C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D).det‖ ^ 2 : ℝ) : ℂ) := by
    have := denom_mul_conjTranspose C D 0 h isHermitian_zero 1
    rw [← norm_det_mul_conjTranspose]
    simp only [ofReal_one, mul_one, zero_add, Matrix.mul_zero, one_pow, one_smul] at this
    rw [this, add_comm]
  refine ⟨?_, by rw [hG, ofReal_re]⟩
  set X : Matrix (Fin N) (Fin N) ℂ := (2⁻¹ : ℂ) • (Z + Zᴴ) with hXdef
  have hX : X.IsHermitian := by
    simp [hXdef, IsHermitian, add_comm]
  have hXB : ∀ a b, ‖X a b‖ ≤ B / 2 := by
    intro a b
    have := hB a b
    rw [hXdef, Matrix.smul_apply, norm_smul]
    simp only [norm_inv, Complex.norm_ofNat]
    linarith
  have hone : ((δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (by exact_mod_cast hδ)
  have him : imH (X + (I * δ) • 1) = (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    rw [mul_smul, imH_add_I_smul _ _ hone.1, imH, hX.eq]
    simp
  have hZe : X + (I * δ) • 1 + I • (imH Z - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) = Z := by
    have h2 : I * (2 * I)⁻¹ = 2⁻¹ := by field_simp
    rw [smul_sub, imH, smul_smul, smul_smul, h2, hXdef]
    module
  have hm := (norm_det_denom_mono N C D (X + (I * δ) • 1) _ h hp (by rwa [him]) hZ).2
  rw [hZe] at hm
  refine le_trans ?_ hm
  have hP : ((((1 - 2 * c : ℝ)) : ℂ) • ((C * X + D) * (C * X + D)ᴴ) +
      ((δ ^ 2 - c - 2 * c * K : ℝ) : ℂ) • (C * Cᴴ) +
      ((2 * c : ℝ) : ℂ) • (C * ((K : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - X * Xᴴ) * Cᴴ) +
      (c : ℂ) • ((C * X + D + C * X) * (C * X + D + C * X)ᴴ)).PosSemidef := by
    refine (((posSemidef_self_mul_conjTranspose _).smul ?_).add
      ((posSemidef_self_mul_conjTranspose _).smul ?_)).add
      (((posSemidef_sub_mul_conjTranspose X _ hXB).mul_mul_conjTranspose_same C).smul ?_) |>.add
      ((posSemidef_self_mul_conjTranspose _).smul ?_)
    · exact Complex.zero_le_real.2 hc1
    · exact Complex.zero_le_real.2 hc2
    · exact Complex.zero_le_real.2 (by positivity)
    · exact Complex.zero_le_real.2 hc0.le
  have hd := norm_det_le_add_posSemidef _ _ (hp.smul (Complex.zero_lt_real.2 hc0)) hP
  have he : (c : ℂ) • (C * Cᴴ + D * Dᴴ) + ((((1 - 2 * c : ℝ)) : ℂ) • ((C * X + D) * (C * X + D)ᴴ) +
      ((δ ^ 2 - c - 2 * c * K : ℝ) : ℂ) • (C * Cᴴ) +
      ((2 * c : ℝ) : ℂ) • (C * ((K : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - X * Xᴴ) * Cᴴ) +
      (c : ℂ) • ((C * X + D + C * X) * (C * X + D + C * X)ᴴ)) =
      (C * (X + (I * δ) • 1) + D) * (C * (X + (I * δ) • 1) + D)ᴴ := by
    rw [denom_mul_conjTranspose C D X h hX]
    push_cast
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc]
    module
  rw [he, norm_det_mul_conjTranspose, det_smul, hG, ← ofReal_pow, ← ofReal_mul, norm_real,
    norm_real, Fintype.card_fin, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity)] at hd
  refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
  rwa [mul_pow, Real.sq_sqrt (by positivity)]

end GlobalTheory.SW
end

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.exists_good_split_prime_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (m : ℕ), 0 < m → ∃ (q : ℕ) (P : Ideal (𝓞 E)), GoodPrime m q P := by
  first | exact @GlobalTheory.SW.SplitPrime.exists_goodPrime | exact GlobalTheory.SW.SplitPrime.exists_goodPrime | (intros; apply GlobalTheory.SW.SplitPrime.exists_goodPrime <;> assumption)
end

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.exists_integral_basis_hermitian_matrices_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N R : ℕ, 0 < R → ∃ (m : ℕ) (β T : Fin m → Matrix (Fin N) (Fin N) E) (c : ℕ), 0 < c ∧ (∀ i, ccT (β i) = β i ∧ ccT (T i) = T i ∧ Den c (T i) ∧ ∃ y : Matrix (Fin N) (Fin N) E, IntM y ∧ ccT y = y ∧ β i = (R : E) • y) ∧ (∀ i j, ∑ τ : Ψ, τ.1 (T i * β j).trace = if i = j then 1 else 0) ∧ ∀ Z : CM Ψ N N, Z = fun τ => ∑ j, (∑ σ : Ψ, ((T j).map σ.1 * Z σ).trace) • (β j).map τ.1 := by
  first | exact @GlobalTheory.SW.HermLat.exists_basis | exact GlobalTheory.SW.HermLat.exists_basis | (intros; apply GlobalTheory.SW.HermLat.exists_basis <;> assumption)
end

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.LagRep

theorem linearIndependent_mul {E κ ι : Type} [Field E] [Fintype κ] [DecidableEq κ]
    (b : Matrix κ κ E) (hb : b.det ≠ 0) (W : Matrix κ ι E)
    (hW : LinearIndependent E (fun i => W i)) : LinearIndependent E (fun i => (b * W) i) := by
  have h1 : Function.Injective W.vecMul := Matrix.vecMul_injective_iff.mpr hW
  have h2 : Function.Injective b.vecMul :=
    Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det b).mpr hb.isUnit)
  refine Matrix.vecMul_injective_iff.mp ?_
  intro s t hst
  apply h2
  apply h1
  simpa only [Matrix.vecMul_vecMul] using hst

theorem span_mul_le {E κ ι : Type} [Field E] [Fintype κ]
    (b : Matrix κ κ E) (W : Matrix κ ι E) :
    Submodule.span E (Set.range fun i => (b * W) i) ≤
      Submodule.span E (Set.range fun i => W i) := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have : (b * W) i = ∑ k, b i k • W k := by
    ext j
    simp [Matrix.mul_apply, Finset.sum_apply]
  show (b * W) i ∈ Submodule.span E (Set.range fun i => W i)
  rw [this]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem span_mul {E κ ι : Type} [Field E] [Fintype κ] [DecidableEq κ]
    (b : Matrix κ κ E) (hb : b.det ≠ 0) (W : Matrix κ ι E) :
    Submodule.span E (Set.range fun i => (b * W) i) =
      Submodule.span E (Set.range fun i => W i) := by
  refine le_antisymm (span_mul_le b W) ?_
  have := span_mul_le b⁻¹ (b * W)
  rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul b hb.isUnit, Matrix.one_mul] at this

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ccT_ccT' {α β : Type} (A : Matrix α β E) : ccT (ccT A) = A := by
  ext i j
  simp [ccT, cc]

theorem ccT_mul' {α β δ : Type} [Fintype β] (A : Matrix α β E) (B : Matrix β δ E) :
    ccT (A * B) = ccT B * ccT A := by
  ext i j
  simp [ccT, cc, Matrix.mul_apply, mul_comm]

theorem lower_rows {N : ℕ} (γ : M2 E N) (hγ : γ ∈ UU E N) :
    LinearIndependent E (fun i => (γ.submatrix Sum.inr id) i) ∧
      γ.submatrix Sum.inr id * Matrix.J (Fin N) E * ccT (γ.submatrix Sum.inr id) = 0 := by
  obtain ⟨⟨hdet, -, hc, -⟩, -⟩ := unitary_act_halfSpace E ∅ N γ hγ
  constructor
  · have h : LinearIndependent E (fun i => γ i) :=
      Matrix.linearIndependent_rows_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det γ).mpr hdet)
    exact h.comp Sum.inr Sum.inr_injective
  · have h : γ * Matrix.J (Fin N) E * ccT γ = Matrix.J (Fin N) E := by
      have : ccT (ccT γ) * Matrix.J (Fin N) E * ccT γ = Matrix.J (Fin N) E := hc
      rwa [ccT_ccT'] at this
    ext i j
    have h' : (γ * Matrix.J (Fin N) E * ccT γ) (Sum.inr i) (Sum.inr j) = 0 := by
      rw [h]
      simp [Matrix.J]
    exact h'

theorem exists_rep_den : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ),
    ∃ c : ℕ, 0 < c ∧ ∀ U : Lag E N, ∃ γ ∈ UU E N, Den c γ ∧ botSpan γ = U.1 := by
  intro E _ _ _ N
  classical
  obtain ⟨c, C, hc, hprim⟩ := exists_nearly_primitive E N
  obtain ⟨c', hc', hext⟩ := RowExt.exists_unitary_ext E N c hc
  refine ⟨c', hc', ?_⟩
  rintro ⟨U, γ₀, hγ₀, rfl⟩
  obtain ⟨hli, hiso⟩ := lower_rows γ₀ hγ₀
  set W₀ : Matrix (Fin N) (Fin N ⊕ Fin N) E := γ₀.submatrix Sum.inr id with hW₀
  obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Fin N × (Fin N ⊕ Fin N) => W₀ p.1 p.2)
  set D : Matrix (Fin N) (Fin N) E := (d : E) • (1 : Matrix (Fin N) (Fin N) E) with hD
  have hDdet : D.det ≠ 0 := by
    rw [hD, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (Int.cast_ne_zero.mpr hd)
  have hDint : IntM (D * W₀) := by
    intro i j
    have := hint (W₀ i j) (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
    rw [hD, Matrix.smul_mul, Matrix.one_mul]
    simpa [zsmul_eq_mul] using this
  obtain ⟨a, ha, -, haint, hap⟩ := hprim _ (D * W₀) hDint (linearIndependent_mul D hDdet W₀ hli)
  obtain ⟨γ, hγ, hden, hrows⟩ := hext (a * (D * W₀)) haint
    (linearIndependent_mul a ha _ (linearIndependent_mul D hDdet W₀ hli))
    (by
      have : a * (D * W₀) * Matrix.J (Fin N) E * ccT (a * (D * W₀)) =
          a * D * (W₀ * Matrix.J (Fin N) E * ccT W₀) * (ccT D * ccT a) := by
        simp only [ccT_mul', Matrix.mul_assoc]
      rw [this, hiso, Matrix.mul_zero, Matrix.zero_mul]) hap
  refine ⟨γ, hγ, hden, ?_⟩
  show botSpan γ = botSpan γ₀
  unfold botSpan
  simp only [hrows]
  rw [span_mul a ha, span_mul D hDdet]
  rfl

end GlobalTheory.SW.LagRep
end

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.trace_pairing_ge_detIm_pow_hermitianHalfSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N c : ℕ, 0 < N → 0 < c → ∃ k : ℝ, 0 < k ∧ ∀ T : Matrix (Fin N) (Fin N) E, ccT T = T → Den c T → (∀ τ : Ψ, (T.map τ.1).PosDef) → ∀ Z ∈ Hn Ψ N, k * detIm Z ^ (1 / ((Ψ.card * N : ℕ) : ℝ)) ≤ ∑ τ : Ψ, (T.map τ.1 * imH (Z τ)).trace.re := by
  first | exact @GlobalTheory.SW.TracePair.trace_ge | exact GlobalTheory.SW.TracePair.trace_ge | (intros; apply GlobalTheory.SW.TracePair.trace_ge <;> assumption)
end

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

theorem _root_.GlobalTheory.T.unitary_act_halfSpace_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (N : ℕ) (γ : M2 E N), γ ∈ UU E N → (IsUnit γ.det ∧ γ⁻¹ ∈ UU E N ∧ ccT γ ∈ UU E N ∧ γ⁻¹ = -(Matrix.J (Fin N) E * ccT γ * Matrix.J (Fin N) E) ∧ ∀ γ' ∈ UU E N, γ' * γ ∈ UU E N) ∧ ∀ Z ∈ Hn Ψ N, (∀ τ, (hDen Ψ γ Z τ).det ≠ 0 ∧ (hDen' Ψ γ Z τ).det * τ.1 γ.det = (hDen Ψ γ Z τ).det ∧ ‖τ.1 γ.det‖ = 1 ∧ (hDen Ψ γ Z τ)ᴴ * imH (hAct Ψ γ Z τ) * hDen Ψ γ Z τ = imH (Z τ)) ∧ hAct Ψ γ Z ∈ Hn Ψ N ∧ detIm (hAct Ψ γ Z) * ∏ τ, ‖(hDen Ψ γ Z τ).det‖ ^ 2 = detIm Z ∧ ∀ γ' ∈ UU E N, hAct Ψ (γ' * γ) Z = hAct Ψ γ' (hAct Ψ γ Z) ∧ (∀ τ, hDen Ψ (γ' * γ) Z τ = hDen Ψ γ' (hAct Ψ γ Z) τ * hDen Ψ γ Z τ) ∧ ∀ τ, hDen' Ψ (γ' * γ) Z τ = hDen' Ψ γ Z τ * hDen' Ψ γ' (hAct Ψ γ Z) τ := by
  first | exact @GlobalTheory.SW.unitary_act_halfSpace | exact GlobalTheory.SW.unitary_act_halfSpace | (intros; apply GlobalTheory.SW.unitary_act_halfSpace <;> assumption)
end

section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

theorem _root_.GlobalTheory.T.eq_of_siegelThetaSeriesRational_eq : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (φ ψ : Matrix κ ι ℚ → ℂ), IsSB φ → IsSB ψ → ∀ τ ∈ Siegel ι, (∀ ζ, thS φ τ ζ = thS ψ τ ζ) → φ = ψ := by
  first | exact @GlobalTheory.SW.eq_of_thS_eq | exact GlobalTheory.SW.eq_of_thS_eq | (intros; apply GlobalTheory.SW.eq_of_thS_eq <;> assumption)
end

section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

theorem _root_.GlobalTheory.T.schwartzBruhatInnerProduct_self_nonneg_bounds : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] (R : ℕ) (φ : Matrix κ ι K → ℂ), 0 < R → HasLevel R φ → (ip φ φ).im = 0 ∧ 0 ≤ (ip φ φ).re ∧ (∀ x, ‖φ x‖ ^ 2 ≤ (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) * (ip φ φ).re) ∧ (∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) → (ip φ φ).re ≤ (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) * B ^ 2) ∧ (∃ B : ℝ, ∀ x, ‖φ x‖ ≤ B) ∧ ∀ ψ, IsSB ψ → ‖ip φ ψ‖ ^ 2 ≤ (ip φ φ).re * (ip ψ ψ).re := by
  first | exact @GlobalTheory.SW.ip_self_nonneg_and_bounds | exact GlobalTheory.SW.ip_self_nonneg_and_bounds | (intros; apply GlobalTheory.SW.ip_self_nonneg_and_bounds <;> assumption)
end
