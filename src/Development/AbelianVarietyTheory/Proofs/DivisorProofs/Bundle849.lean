module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle043
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInv
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle308
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle822
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.CrystallineConnectionFormCoboundaryZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle823
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep

theorem constTerm_unip_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ f : GA E a → ℂ, (∀ γ g, f (ratGL E a γ * g) = f g) → ∀ (y : BlockIx a r → Ad E) (g : GA E a), ∫ x in 𝓕, f (unip x * (unip y * g)) ∂μ = ∫ x in 𝓕, f (unip x * g) ∂μ := by
  intro E _ _ _ a r _ _ μ 𝓕 hμ h𝓕 f hf y g
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (ratN E a r) := by
    have : ((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)) = Set.range
        (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) := AddMonoidHom.coe_range _
    change Countable (((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)))
    rw [this]; exact (Set.countable_range _).to_subtype
  set h : (BlockIx a r → Ad E) → ℂ := fun x => f (unip x * g) with hh
  have hinv : ∀ (γ : ratN E a r) (x : BlockIx a r → Ad E), h (γ +ᵥ x) = h x := by
    rintro ⟨_, e, rfl⟩ x
    change f (unip ((fun p => algebraMap E (Ad E) (e p)) + x) * g) = f (unip x * g)
    rw [unip_add, unip_algebraMap, mul_assoc, hf]
  have hL : ∀ x, f (unip x * (unip y * g)) = h (x + y) := fun x => by
    simp only [hh, unip_add, mul_assoc]
  simp_rw [hL]

  have hmp : MeasurePreserving (fun x : BlockIx a r → Ad E => x + y) μ μ := measurePreserving_add_right μ y
  have hemb : MeasurableEmbedding (fun x : BlockIx a r → Ad E => x + y) :=
    (MeasurableEquiv.addRight y).measurableEmbedding
  let S : Set (BlockIx a r → Ad E) := (fun x => x - y) ⁻¹' 𝓕
  have hpre : (fun x : BlockIx a r → Ad E => x + y) ⁻¹' S = 𝓕 := by
    ext x; simp [S]
  have hS : IsAddFundamentalDomain (ratN E a r) S μ := by
    refine h𝓕.preimage_of_equiv (e := id) ?_ Function.bijective_id ?_
    · exact (measurePreserving_sub_right μ y).quasiMeasurePreserving
    · intro γ x
      change (γ : BlockIx a r → Ad E) + x - y = (γ : BlockIx a r → Ad E) + (x - y)
      abel
  calc ∫ x in 𝓕, h (x + y) ∂μ = ∫ x in (fun x : BlockIx a r → Ad E => x + y) ⁻¹' S, h (x + y) ∂μ := by rw [hpre]
    _ = ∫ x in S, h x ∂μ := hmp.setIntegral_preimage_emb hemb h S
    _ = ∫ x in 𝓕, h x ∂μ := hS.setIntegral_eq h𝓕 hinv

end GlobalTheory.CuspRep
end

section

noncomputable section

open NumberField Topology

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem continuous_mapInf : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_mapFin : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pFin)

theorem IsAutForm.continuous {φ : Sm E a} (h : IsAutForm φ) : Continuous φ.1 := by
  rw [continuous_iff_continuousAt]
  intro g₀
  have hmul : Continuous fun g : GA E a => g₀⁻¹ * g := continuous_const.mul continuous_id
  have hN : {g : GA E a | Matrix.GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) ∈ {k | finRep E a k φ = φ}} ∈ 𝓝 g₀ := by
    refine (h.level.preimage (continuous_mapFin.comp hmul)).mem_nhds ?_
    simp
  have heq : φ.1 =ᶠ[𝓝 g₀] fun g => chart φ.1 g₀ (toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) := by
    filter_upwards [hN] with g hg
    rw [chart_val]
    have hk : ∀ x, φ.1 (x * finGL E a (Matrix.GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g))) = φ.1 x :=
      fun x => congrArg (fun ψ : Sm E a => ψ.1 x) hg
    conv_lhs => rw [← mul_inv_cancel_left g₀ g, ← infGL_mul_finGL (g₀⁻¹ * g), ← mul_assoc, hk]
  refine ContinuousAt.congr ?_ heq.symm
  have hc : ContinuousAt (chart φ.1 g₀) (toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g₀)).val) :=
    (contDiffAt_chart φ.2 g₀ (val_mem_invSet _)).continuousAt
  exact ContinuousAt.comp (f := fun g : GA E a => toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) hc
    (Units.continuous_val.comp (continuous_mapInf.comp hmul)).continuousAt

end GlobalTheory.CuspRep
end
end

section

namespace GlobalTheory.CompactUniformHeightBound

open Filter Topology

theorem height_one_le {E : Type} [Field E] [NumberField E] {a : ℕ}
    (y : GL (Fin a) (GlobalTheory.CuspRep.Cinf E)) : 1 ≤ GlobalTheory.CuspRep.height y := by
  unfold GlobalTheory.CuspRep.height
  exact le_add_of_le_of_nonneg (le_add_of_nonneg_right (norm_nonneg _)) (norm_nonneg _)

theorem compact_uniform_bound : (let d1 : {E : Type} → [inst : Field E] → [inst_1 : NumberField E] → [NumberField.IsTotallyComplex E] → {a : ℕ} → (GlobalTheory.CuspRep.GA E a → ℂ) → Prop := @(fun {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E] {a : ℕ} (F : GlobalTheory.CuspRep.GA E a → ℂ) ↦ ∀ (g₀ : GlobalTheory.CuspRep.GA E a), ∃ (C : ℝ) (N : ℕ), (0 : ℝ) ≤ C ∧ ∀ᶠ (g : GlobalTheory.CuspRep.GA E a) in nhds g₀, ∀ (y : GL (Fin a) (GlobalTheory.CuspRep.Cinf E)), ‖F (g * (GlobalTheory.CuspRep.infGL E a : GL (Fin a) (GlobalTheory.CuspRep.Cinf E) → GlobalTheory.CuspRep.GA E a) y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N); ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsTotallyComplex E] {a : ℕ} {F : GlobalTheory.CuspRep.GA E a → ℂ}, d1 F → ∀ {K : Set (GlobalTheory.CuspRep.GA E a)}, IsCompact K → ∃ (C : ℝ) (N : ℕ), (0 : ℝ) ≤ C ∧ ∀ g ∈ K, ∀ (y : GL (Fin a) (GlobalTheory.CuspRep.Cinf E)), ‖F (g * (GlobalTheory.CuspRep.infGL E a : GL (Fin a) (GlobalTheory.CuspRep.Cinf E) → GlobalTheory.CuspRep.GA E a) y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N) := by
  intro d1 E _ _ _ a F hF K hK
  have hb : ∀ g₀ : GlobalTheory.CuspRep.GA E a, ∃ (C : ℝ) (N : ℕ), (0 : ℝ) ≤ C ∧
      {g : GlobalTheory.CuspRep.GA E a | ∀ (y : GL (Fin a) (GlobalTheory.CuspRep.Cinf E)),
        ‖F (g * (GlobalTheory.CuspRep.infGL E a : GL (Fin a) (GlobalTheory.CuspRep.Cinf E) → GlobalTheory.CuspRep.GA E a) y)‖
          ≤ C * GlobalTheory.CuspRep.height y ^ N} ∈ 𝓝 g₀ := fun g₀ => hF g₀
  choose C N hC hU using hb
  obtain ⟨t, -, hKt⟩ := hK.elim_nhds_subcover _ (fun x _ => hU x)
  refine ⟨∑ x ∈ t, C x, t.sup N, Finset.sum_nonneg (fun x _ => hC x), ?_⟩
  intro g hg y
  obtain ⟨x, hx, hgx⟩ := Set.mem_iUnion₂.mp (hKt hg)
  have h1 := height_one_le y
  calc _ ≤ C x * GlobalTheory.CuspRep.height y ^ N x := hgx y
    _ ≤ (∑ i ∈ t, C i) * GlobalTheory.CuspRep.height y ^ t.sup N :=
      mul_le_mul (Finset.single_le_sum (fun i _ => hC i) hx)
        (pow_le_pow_right₀ h1 (Finset.le_sup hx))
        (pow_nonneg (zero_le_one.trans h1) _) (Finset.sum_nonneg fun i _ => hC i)

end GlobalTheory.CompactUniformHeightBound
end

section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.ZalgCpt

theorem zalg_comm_cptRep : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (k : GlobalTheory.CuspRep.Kinf E a) (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)),
    z ∈ GlobalTheory.CuspRep.Zalg E a → z * GlobalTheory.CuspRep.cptRep E a k = GlobalTheory.CuspRep.cptRep E a k * z := by
  intro E _ _ _ a k z hz
  have hle : GlobalTheory.CuspRep.Zalg E a ≤ Subalgebra.centralizer ℂ {GlobalTheory.CuspRep.cptRep E a k} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, u, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    rintro g rfl
    exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u (Unitary.toUnits k)).eq.symm
  exact ((Subalgebra.mem_centralizer_iff ℂ).1 (hle hz) _ rfl).symm

end GlobalTheory.ZalgCpt
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem clifford_prime_index : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ),
    (Nat.card Γ).Prime → s ≠ 1 → ∀ χ : G ⋊[φ] Γ → ℂ, IsIrrChar ℂ ℂ χ →
      (∀ δ, χ (inl δ * inr s) = 0) ∨ (IsIrrChar ℂ ℂ (fun g => χ (inl g)) ∧
        ∑ᶠ g, χ (inl g * inr s) * star (χ (inl g * inr s)) = (Nat.card G : ℂ)) := by
  intro G Γ _ _ _ _ φ s hl hs χ hχ
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  haveI := Fintype.ofFinite (G ⋊[φ] Γ)
  have hH : Nat.card (G ⋊[φ] Γ) = Nat.card G * Nat.card Γ := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
  have hHne : (Nat.card (G ⋊[φ] Γ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hord : orderOf s = Nat.card Γ := by
    rcases (Nat.dvd_prime hl).1 (orderOf_dvd_natCard s) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hs
    · exact h
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    have htop : Subgroup.zpowers s = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord])
    intro t
    rw [htop]
    trivial
  have hl0 : Nat.card Γ ≠ 0 := hl.ne_zero
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (Nat.card Γ : ℂ))) (Nat.card Γ) :=
    Complex.isPrimitiveRoot_exp _ hl0
  obtain ⟨η, hη1, hηs, hF⟩ := GlobalTheory.Shin.CosetFourier.fourier_coset_sums G Γ φ s hgen _ hζ
  set ζ := Complex.exp (2 * Real.pi * Complex.I / (Nat.card Γ : ℂ)) with hζdef
  have hχchar : IsChar ℂ ℂ χ := by
    obtain ⟨n, ρ, -, h⟩ := hχ
    exact ⟨n, ρ, h⟩
  have hVR := virt_mul_comap_conj_ind_linear (G ⋊[φ] Γ)
  have hnorm : ∑ᶠ x, χ x * star (χ x) = (Nat.card (G ⋊[φ] Γ) : ℂ) := by
    obtain ⟨n, ρ, hρ, h⟩ := hχ
    haveI := hρ
    haveI : Invertible (Nat.card (G ⋊[φ] Γ) : ℂ) := invertibleOfNonzero hHne
    have ho := Representation.char_orthonormal ρ ρ
    rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at ho
    have hc : χ = ρ.character := funext fun g => by simpa using h g
    rw [finsum_eq_sum_of_fintype]
    have hst : ∀ x, star (χ x) = χ x⁻¹ := star_virt_eq_inv _ χ (isChar_mem_virt_complex hχchar)
    simp_rw [hst]
    rw [hc]
    exact ((inv_mul_eq_one₀ hHne).1 (by simpa using ho)).symm
  have hηstar : ∀ x, (η x : ℂ) * star (η x : ℂ) = 1 := by
    intro x
    have h := star_virt_eq_inv _ (fun x => (η x : ℂ)) (hVR.2.2.2.2 η) x
    rw [h, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hψchar : ∀ a : ℕ, IsChar ℂ ℂ (fun x => χ x * (η x : ℂ) ^ a) := by
    intro a
    have h := isChar_mul_complex hχchar (isChar_monoidHom_complex (η ^ a))
    convert h using 1
  have hψnorm : ∀ a : ℕ, ∑ᶠ x, (fun x => χ x * (η x : ℂ) ^ a) x * star ((fun x => χ x * (η x : ℂ) ^ a) x) =
      (Nat.card (G ⋊[φ] Γ) : ℂ) := by
    intro a
    rw [← hnorm]
    congr 1
    funext x
    dsimp only
    rw [star_mul, star_pow]
    calc χ x * (η x : ℂ) ^ a * (star (η x : ℂ) ^ a * star (χ x))
        = χ x * star (χ x) * ((η x : ℂ) * star (η x : ℂ)) ^ a := by ring
      _ = χ x * star (χ x) := by rw [hηstar, one_pow, mul_one]
  have hψirr : ∀ a : ℕ, IsIrrChar ℂ ℂ (fun x => χ x * (η x : ℂ) ^ a) := fun a =>
    ((irr_of_norm_one _ _ (isChar_mem_virt_complex (hψchar a)) (hψnorm a)).2 (hψchar a)).1
  by_cases hcase : ∃ a, 0 < a ∧ a < Nat.card Γ ∧ (fun x => χ x * (η x : ℂ) ^ a) = χ
  · left
    obtain ⟨a, ha0, hal, he⟩ := hcase
    intro δ
    have h1 := congrFun he (inl δ * inr s)
    have hv : (η (inl δ * inr s) : ℂ) = ζ := by rw [map_mul, hη1, one_mul, hηs]
    rw [hv] at h1
    have hζa : ζ ^ a ≠ 1 := hζ.pow_ne_one_of_pos_of_lt ha0.ne' hal
    have h2 : χ (inl δ * inr s) * (ζ ^ a - 1) = 0 := by rw [mul_sub, h1, mul_one, sub_self]
    exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hζa)
  · right
    push_neg at hcase
    have hNa : ∀ a ∈ Finset.range (Nat.card Γ), a ≠ 0 →
        ∑ᶠ x, χ x * star (χ x * (η x : ℂ) ^ a) = 0 := by
      intro a ha ha0
      have hne := hcase a (Nat.pos_of_ne_zero ha0) (Finset.mem_range.1 ha)
      have hp := pair_eq_zero_of_isIrrChar_ne _ χ _ hχ (hψirr a) (Ne.symm hne)
      unfold pair at hp
      have hs0 := (mul_eq_zero.1 hp).resolve_left (inv_ne_zero hHne)
      rw [← hs0]
      congr 1
      funext x
      have h := star_virt_eq_inv _ _ (isChar_mem_virt_complex (hψchar a)) x
      rw [h]
    have hN0 : ∑ᶠ x, χ x * star (χ x * (η x : ℂ) ^ 0) = (Nat.card (G ⋊[φ] Γ) : ℂ) := by
      simpa using hnorm
    have h0mem : 0 ∈ Finset.range (Nat.card Γ) := Finset.mem_range.2 (Nat.pos_of_ne_zero hl0)
    obtain ⟨hA, hB⟩ := hF χ χ
    rw [Finset.sum_eq_single 0 (fun a ha ha0 => hNa a ha ha0) (fun h => absurd h0mem h), hN0, hH] at hA
    rw [Finset.sum_eq_single 0 (fun a ha ha0 => by rw [hNa a ha ha0, mul_zero]) (fun h => absurd h0mem h),
      pow_zero, one_mul, hN0, hH] at hB
    have hlc : (Nat.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hl0
    push_cast at hA hB
    have hSG : ∑ᶠ g, χ (inl g) * star (χ (inl g)) = (Nat.card G : ℂ) :=
      mul_left_cancel₀ hlc (by rw [hA, mul_comm])
    refine ⟨?_, mul_left_cancel₀ hlc (by rw [hB, mul_comm])⟩
    have hrchar : IsChar ℂ ℂ (fun g => χ (inl g)) := by
      obtain ⟨n, ρ, h⟩ := hχchar
      exact ⟨n, ρ.comp SemidirectProduct.inl, fun g => h _⟩
    exact ((irr_of_norm_one G _ (isChar_mem_virt_complex hrchar) hSG).2 hrchar).1

end GlobalTheory.Shin
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH

theorem _root_.GlobalTheory.T.exists_nonempty_isIso_morphismRestrict_of_isProjOver : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y M : RatModel o Ω), IsProjOver Y.s → ∀ q : Y.Z ⟶ M.Z, M.IsHom Y (AlgHom.id o Ω) q → ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧ IsIso (q ∣_ U) := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isProjOver | exact GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isProjOver | (intros; apply GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isProjOver <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.ChartPair

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
  {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V}

theorem exists_affine_pt (y : Sp ℂ ⟶ X) : ∃ U : X.Opens, IsAffineOpen U ∧ ⊤ ≤ y ⁻¹ᵁ U := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (x := y (default : PrimeSpectrum ℂ)) (U := ⊤) trivial
  refine ⟨U, hU, fun p _ ↦ ?_⟩
  have : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  subst this
  exact hy

theorem isOpen_dom (u : Unif F s σ) (U : X.Opens) : IsOpen {p : Tot I g | p.1 ∈ F.V ∧ ⊤ ≤ u.E p ⁻¹ᵁ U} :=
  (u.hol U 0).1

def Good (u : Unif F s σ) (W : Opens (Tot I g)) : Prop :=
  (∀ p ∈ W, p.1 ∈ F.V) ∧ ∃ U : X.Opens, IsAffineOpen U ∧ ∀ p ∈ W, ⊤ ≤ u.E p ⁻¹ᵁ U

def charts (u : Unif F s σ) : Charts F where
  K := {W : Opens (Tot I g) // Good u W}
  W k := k.1
  base k := k.2.1
  le l k' k := ∀ p ∈ k'.1, F.shift l p ∈ k.1
  le_refl k p hp := by rwa [F.shift_zero]
  le_trans {l m k k' k''} h h' p hp := by rw [F.shift_add]; exact h _ (h' p hp)
  maps h := h

end GlobalTheory.AnPer.ChartPair

namespace GlobalTheory.AnPer.ChartPair

variable {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁}
  {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V}
  {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂}
  {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V}

def pairCharts (u₁ : Unif F₁ s₁ σ₁) (u₂ : Unif F₂ s₂ σ₂) (b : (I₁ → ℂ) → I₂ → ℂ)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂) : Charts F₁ where
  K := {q : Opens (Tot I₁ g₁) × Opens (Tot I₂ g₂) //
    Good u₁ q.1 ∧ Good u₂ q.2 ∧ ∀ p ∈ q.1, ((b p.1, M p.2) : Tot I₂ g₂) ∈ q.2}
  W k := k.1.1
  base k := k.2.1.1
  le l k' k := (∀ p ∈ k'.1.1, F₁.shift l p ∈ k.1.1) ∧ ∀ p ∈ k'.1.2, F₂.shift (A l) p ∈ k.1.2
  le_refl k := ⟨fun p hp ↦ by rwa [F₁.shift_zero], fun p hp ↦ by rwa [map_zero, F₂.shift_zero]⟩
  le_trans {l m k k' k''} h h' := ⟨fun p hp ↦ by rw [F₁.shift_add]; exact h.1 _ (h'.1 p hp),
    fun p hp ↦ by rw [map_add (f := _), F₂.shift_add]; exact h.2 _ (h'.2 p hp)⟩
  maps h := h.1

theorem exists_pair (u₁ : Unif F₁ s₁ σ₁) (u₂ : Unif F₂ s₂ σ₂) (b : (I₁ → ℂ) → I₂ → ℂ)
    (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂)
    (hτ : ∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) :
    ∃ (K₁ : Charts F₁) (K₂ : Charts F₂) (κ : K₁.K → K₂.K), K₁.Rich ∧
      (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K₁.W k, ⊤ ≤ u₁.E p ⁻¹ᵁ U) ∧
      (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K₂.W k, ⊤ ≤ u₂.E p ⁻¹ᵁ U) ∧
      (∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) ∧
      ∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k) := by
  let Φ : Tot I₁ g₁ → Tot I₂ g₂ := fun p ↦ (b p.1, M p.2)
  have hΦ : ∀ l (p : Tot I₁ g₁), p.1 ∈ F₁.V → Φ (F₁.shift l p) = F₂.shift (A l) (Φ p) := by
    intro l p hp
    simp only [Φ, Fam.shift, map_add (f := _), hτ l p.1 hp]
  have hcont : ContinuousOn Φ {p : Tot I₁ g₁ | p.1 ∈ F₁.V} :=
    (hb.continuousOn.comp continuous_fst.continuousOn fun p hp ↦ hp).prodMk
      (M.continuous_of_finiteDimensional.comp continuous_snd).continuousOn
  refine ⟨pairCharts u₁ u₂ b M A, charts u₂, fun k ↦ ⟨k.1.2, k.2.2.1⟩, ⟨?_, ?_⟩,
    fun k ↦ k.2.1.2, fun k ↦ k.2.2, fun k ↦ k.2.2.2, fun l k' k h ↦ h.2⟩
  · intro p hp
    obtain ⟨U₁, hU₁, h₁⟩ := exists_affine_pt (u₁.E p)
    obtain ⟨U₂, hU₂, h₂⟩ := exists_affine_pt (u₂.E (Φ p))
    let O₁ := {q : Tot I₁ g₁ | q.1 ∈ F₁.V ∧ ⊤ ≤ u₁.E q ⁻¹ᵁ U₁}
    let O₂ := {q : Tot I₂ g₂ | q.1 ∈ F₂.V ∧ ⊤ ≤ u₂.E q ⁻¹ᵁ U₂}
    have hO₂ : IsOpen O₂ := isOpen_dom u₂ U₂
    have hO₁ : IsOpen (O₁ ∩ Φ ⁻¹' O₂) :=
      (hcont.mono fun (q : Tot I₁ g₁) (hq : q ∈ O₁) ↦ hq.1).isOpen_inter_preimage (isOpen_dom u₁ U₁) hO₂
    refine ⟨⟨(⟨O₁ ∩ Φ ⁻¹' O₂, hO₁⟩, ⟨O₂, hO₂⟩),
      ⟨fun q hq ↦ hq.1.1, U₁, hU₁, fun q hq ↦ hq.1.2⟩, ⟨fun q hq ↦ hq.1, U₂, hU₂, fun q hq ↦ hq.2⟩,
      fun q hq ↦ hq.2⟩, ?_⟩
    exact ⟨⟨hp, h₁⟩, hbV _ hp, h₂⟩
  · intro l k₁ k₂ p hp hp'
    have hb₁ := k₁.2.1.1
    have hb₂ := k₁.2.2.1.1
    have o₁ : IsOpen ((k₁.1.1 : Set (Tot I₁ g₁)) ∩ F₁.shift l ⁻¹' k₂.1.1) :=
      (F₁.shift_analytic l hb₁).continuousOn.isOpen_inter_preimage k₁.1.1.isOpen k₂.1.1.isOpen
    have o₂ : IsOpen ((k₁.1.2 : Set (Tot I₂ g₂)) ∩ F₂.shift (A l) ⁻¹' k₂.1.2) :=
      (F₂.shift_analytic (A l) hb₂).continuousOn.isOpen_inter_preimage k₁.1.2.isOpen k₂.1.2.isOpen
    obtain ⟨U₁, hU₁, h₁⟩ := k₁.2.1.2
    obtain ⟨U₂, hU₂, h₂⟩ := k₁.2.2.1.2
    refine ⟨⟨(⟨_, o₁⟩, ⟨_, o₂⟩), ⟨fun q hq ↦ hb₁ q hq.1, U₁, hU₁, fun q hq ↦ h₁ q hq.1⟩,
      ⟨fun q hq ↦ hb₂ q hq.1, U₂, hU₂, fun q hq ↦ h₂ q hq.1⟩, fun q hq ↦ ⟨k₁.2.2.2 q hq.1, ?_⟩⟩,
      ⟨hp, hp'⟩, ⟨fun q hq ↦ ?_, fun q hq ↦ ?_⟩, ⟨fun q hq ↦ hq.2, fun q hq ↦ hq.2⟩⟩
    · show F₂.shift (A l) (Φ q) ∈ k₂.1.2
      rw [← hΦ l q (hb₁ q hq.1)]
      exact k₂.2.2.2 _ hq.2
    · rw [F₁.shift_zero]; exact hq.1
    · rw [map_zero, F₂.shift_zero]; exact hq.1

end GlobalTheory.AnPer.ChartPair
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem isChern_real : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F) (r : Real K s σ) (M : LB X) (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∀ z : SecondDeRham s, IsChern (dp0 B) s M z → ∃ (i : K.Obj → M.ι) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : GlobalTheory.CatCoh.Z2 K.Oc), (∀ T, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (i T)) ∧ (∀ (T T' : K.Obj) (φ : T ⟶ T') (hh : ⊤ ≤ (r.obj T').x ⁻¹ᵁ (M.U (i T') ⊓ M.U (i T))), Ideal.Quotient.mk T'.J (uu T T' φ) = evalAt (r.obj T').x (M.U (i T') ⊓ M.U (i T)) hh (M.g (i T') (i T)).val) ∧ (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), (show ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C from ℓ.1) T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ ((show ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C from ℓ.1) T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) ∧ r.coef.pull2 z = GlobalTheory.CatCoh.H2.mk K.Oc ℓ := by
  intro I _ g Λ _ F B _ X s σ K r M j hj z hz
  obtain ⟨i₀, hi₀, u₀, ℓ₀, h1, h2, h3⟩ := hz
  let G : K.Obj ⥤ (IsSmall (dp0 B) s M.U).FullSubcategory :=
    ObjectProperty.lift _ r.functor fun T ↦ ⟨j T.k, fun p _ ↦ hj T.k (Set.mem_univ _)⟩
  let n : GlobalTheory.CatCoh.CoefMap σ ((IsSmall (dp0 B) s M.U).ι ⋙ O (dp0 B) s) K.Oc :=
    { G := G
      α := fun T ↦ RingHom.id T.C
      naturality := fun _ _ ↦ rfl
      smul := fun T b c ↦ r.coef.smul T b c }
  refine ⟨fun T ↦ i₀ (G.obj T), fun T T' φ ↦ u₀ _ _ (G.map φ), n.pullbackTwoCocycle ℓ₀, fun T ↦ hi₀ (G.obj T),
    fun T T' φ _ ↦ h1 _ _ (G.map φ), fun T T' T'' φ ψ ↦ ?_, ?_⟩
  · have h := h2 _ _ _ (G.map φ) (G.map ψ)
    rw [← G.map_comp] at h
    exact h
  · rw [← n.pullCohomologyTwo_class, ← h3]
    obtain ⟨z, rfl⟩ := GlobalTheory.CatCoh.H2.mk_surjective _ z
    rfl

end GlobalTheory.AnPer
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.adelicMatrixDegree_le_two_mul_of_upperTriangular : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (g : Place k F → Matrix (Fin 2) (Fin 2) F), admitted g → (∀ v, g v 1 0 = 0) → ∀ b : ℝ, LinesLE g b → (deg g : ℝ) ≤ 2 * b := by
  first | exact @GlobalTheory.Nef.deg_le_two_mul_of_triangular | exact GlobalTheory.Nef.deg_le_two_mul_of_triangular | (intros; apply GlobalTheory.Nef.deg_le_two_mul_of_triangular <;> assumption)
end
