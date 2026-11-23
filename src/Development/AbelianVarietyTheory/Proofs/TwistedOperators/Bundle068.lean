module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle062
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharEqOneOfOpENeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle042
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle051
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle056
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle063
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle065
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem _root_.GlobalTheory.T.rootExchangeUnipotent_exists_residueCardPow_mem_nhds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), (resCard k).Prime → ∀ u ∈ N k n c p, ∀ U ∈ 𝓝 (1 : GL (n ⊕ Fin c) k), ∃ m : ℕ, u ^ (resCard k ^ m) ∈ U := by
  first | exact @GlobalTheory.RootEx.UnipPow.exists_pow_mem_nhds | exact GlobalTheory.RootEx.UnipPow.exists_pow_mem_nhds | (intros; apply GlobalTheory.RootEx.UnipPow.exists_pow_mem_nhds <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

namespace GlobalTheory.RootEx

attribute [local instance 2000] _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace

private theorem exists_open_translations {M : Type*} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] {Φ : M → ℂ} (hΦ : Φ ∈ SB M) :
    ∃ Λ : AddSubgroup M, IsOpen (Λ : Set M) ∧ ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  obtain ⟨K, hKo, hK⟩ := GlobalTheory.QuotInt.exists_open_stab (G := Multiplicative M)
    (F := fun x => Φ (Multiplicative.toAdd x)) hΦ
  refine ⟨{ carrier := {y | Multiplicative.ofAdd y ∈ K}
            add_mem' := fun hy hz => K.mul_mem hy hz
            zero_mem' := K.one_mem
            neg_mem' := fun hy => K.inv_mem hy }, hKo, ?_⟩
  intro x y hy
  exact hK (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) hy

theorem exists_isQuotInt_unfolding : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (P P' : Type) [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P'] (π : Representation ℂ (GL n k) P) (π' : Representation ℂ (GL n' k) P') (θ : P' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] P) (_ : ∀ g h φ Ψ Ψ', Ψ'.1 = om μ g h Ψ.1 → θ (π' g φ) Ψ' = π h (θ φ Ψ)) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : IsPos ψ p π σ b) (φ : P') (F : A) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (f : GL (n ⊕ Fin c) k → ℂ) (_ : ∀ h Ψ, Ψ.1 = opE ψ ν p (om μ 1 h Φ.1) → f h = b (θ φ Ψ) (σ h F)), ∃ z, IsQuotInt ν μX μG p f z := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp1 hpc ψ hψc hψ1 ν _ μ hμ μX _ μG _ A _ _ σ hσ P P' _ _ _ _
    π π' θ hθ b hb φ F Φ f hf
  have hom := om_isSmoothRepresentation k (n' ⊕ Fin (c + 1)) (n ⊕ Fin c) μ hμ
  have hom' := om_isSmoothRepresentation k n' n μ hμ
  have hE := opE_SB_and_linear k n n' c p ψ hψc ν
  have hΦ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
  have hmemΨ : ∀ h : GL (n ⊕ Fin c) k, opE ψ ν p (om μ 1 h Φ.1) ∈ SB (Matrix n n' k) :=
    fun h => hE.1 _ (hom.2.2.2.1 1 h Φ.1 Φ.2)
  have om_smul : ∀ {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      (g : GL a k) (h : GL b k) (z : ℂ) (G : Matrix b a k → ℂ), om μ g h (z • G) = z • om μ g h G := by
    intro a b _ _ _ _ g h z G
    funext y
    simp only [om, Pi.smul_apply, smul_eq_mul]
    ring
  have hloc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hU : {y : GL (n ⊕ Fin c) k | σ y F = F ∧ om μ 1 y Φ.1 = Φ.1} ∈ 𝓝 (1 : GL (n ⊕ Fin c) k) := by
      have hσU : {y : GL (n ⊕ Fin c) k | σ y F = F} ∈ 𝓝 (1 : GL (n ⊕ Fin c) k) :=
        (hσ F).mem_nhds (by simp)
      have ho : IsOpen {y : GL (n ⊕ Fin c) k | om μ 1 y Φ.1 = Φ.1} :=
        (hom.2.2.2.2 Φ.1 Φ.2).preimage (continuous_const.prodMk continuous_id)
      filter_upwards [hσU, ho.mem_nhds (hom.1 Φ.1)] with y hy hz
      exact ⟨hy, hz⟩
    have hx : {y | x⁻¹ * y ∈ {y : GL (n ⊕ Fin c) k | σ y F = F ∧ om μ 1 y Φ.1 = Φ.1}} ∈ 𝓝 x := by
      have hc : Continuous fun y : GL (n ⊕ Fin c) k => x⁻¹ * y := continuous_const.mul continuous_id
      exact hc.continuousAt.preimage_mem_nhds (by simpa using hU)
    filter_upwards [hx] with y hy
    obtain ⟨z, rfl⟩ : ∃ z, y = x * z := ⟨x⁻¹ * y, by group⟩
    simp only [inv_mul_cancel_left] at hy
    obtain ⟨h1, h2⟩ := hy
    have e1 : om μ 1 (x * z) Φ.1 = om μ 1 x Φ.1 := by
      have := hom.2.1 1 1 x z Φ.1
      rw [mul_one] at this
      rw [this, h2]
    have hσz : σ (x * z) F = σ x F := by
      rw [map_mul, Module.End.mul_apply, h1]
    rw [hf (x * z) ⟨_, hmemΨ x⟩ (by rw [e1]), hf x ⟨_, hmemΨ x⟩ rfl, hσz]
  obtain ⟨Λ, hΛo, hΛ⟩ := exists_open_translations (M := Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) Φ.2
  obtain ⟨Ω, hΩ, hΩR⟩ := opE_support_compact_mod_R k n n' c p hp1 hpc ψ hψc hψ1 ν (tsupport Φ.1) hΦ.2
    Λ hΛo
  have hsupp : ∀ h, f h ≠ 0 → ∃ r ∈ R k n c p, ∃ w ∈ Ω, h = r * w := by
    intro h hfh
    have hne : opE ψ ν p (om μ 1 h Φ.1) ≠ 0 := by
      intro h0
      apply hfh
      rw [hf h 0 (by rw [h0]; rfl)]
      simp
    obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hne
    exact hΩR μ Φ.1 (subset_tsupport _) hΛ (fun _ => 1) (IsLocallyConstant.const 1) h x₀
      (by simpa using hx₀)
  have hequiv : ∀ (x : GL n k), ∀ u ∈ N k n c p, ∀ h, f (embX c x * u * h) =
      ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) * f h := by
    intro x u hu h
    let Ψ'' : SB (Matrix n n' k) := ⟨om μ 1 x (opE ψ ν p (om μ 1 h Φ.1)), hom'.2.2.2.1 1 x _ (hmemΨ h)⟩
    have m1 : om μ 1 (embX c x * u * h) Φ.1 = om μ 1 (embX c x) (om μ 1 u (om μ 1 h Φ.1)) := by
      have e1 := hom.2.1 1 1 (embX c x * u) h Φ.1
      have e2 := hom.2.1 1 1 (embX c x) u (om μ 1 h Φ.1)
      rw [mul_one] at e1 e2
      rw [e1, e2]
    have hkey : (((((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) *
        (ψ (-simpleSum u) : ℂ)) • Ψ'' : SB (Matrix n n' k)) : Matrix n n' k → ℂ) =
        opE ψ ν p (om μ 1 (embX c x * u * h) Φ.1) := by
      rw [m1, (opE_om_embX k n n' c p hp1 hpc ψ ν μ _).1 x,
        opE_om_target_unipotent k n n' c p hp1 hpc ψ ν μ _ u hu, om_smul, Submodule.coe_smul, smul_smul]
    have hθΨ : θ φ Ψ'' = π x (θ φ ⟨_, hmemΨ h⟩) := by
      have := hθ 1 x φ ⟨_, hmemΨ h⟩ Ψ'' rfl
      simpa using this
    rw [hf _ _ hkey, hf h ⟨_, hmemΨ h⟩ rfl, map_smul, hθΨ, map_smul, LinearMap.smul_apply, map_mul,
      map_mul, Module.End.mul_apply, Module.End.mul_apply, hb.2 x, hb.1 _ u hu, smul_eq_mul]
    have hN : 0 < nabs k (Matrix.GeneralLinearGroup.det x) := GlobalTheory.RootEx.OpELevi.nabs_pos _
    have hpow : (nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) =
        nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) *
          nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) := by
      rw [← Real.rpow_add hN]
      ring_nf
    have hψ : (ψ (-simpleSum u) : ℂ) * (ψ (simpleSum u) : ℂ) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one,
        Circle.coe_one]
    rw [hpow, Complex.ofReal_mul]
    linear_combination
      ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) *
      ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) *
      b (θ φ ⟨_, hmemΨ h⟩) (σ h F) * hψ
  exact (GlobalTheory.QuotInt.quotInt_unique_exists k n c p hp1 hpc ν μX μG f).2 hloc ⟨Ω, hΩ, hsupp⟩ hequiv

end GlobalTheory.RootEx
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.RootEx.ProperTriple

open MeasureTheory ValuativeRel Matrix in
private lemma unipotent_block_entries_eq_one_zero {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    {c ρ : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ _root_.GlobalTheory.RootEx.N k n c (ρ + 1)) :
    (∀ t t' : n, (u : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl t) (Sum.inl t') =
      (1 : Matrix n n k) t t') ∧
    (∀ (t : n) (i : Fin c), (i : ℕ) + 1 = ρ + 1 →
      (u : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl t) (Sum.inr i) = 0) ∧
    (∀ (t : n) (i : Fin c), (i : ℕ) + 1 = ρ + 1 →
      (u : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inl t) = 0) := by
  have h := _root_.GlobalTheory.RootEx.Model.mem_N_iff.1 hu
  unfold _root_.GlobalTheory.RootEx.InN _root_.GlobalTheory.RootEx.lev at h
  refine ⟨fun t t' => ?_, fun t i hi => ?_, fun t i hi => ?_⟩
  · rw [h _ _ (by simp)]
    simp [Matrix.one_apply]
  · rw [h _ _ (by simp [hi])]
    simp
  · rw [h _ _ (by simp [hi])]
    simp

open MeasureTheory ValuativeRel Matrix in
private lemma recover_colE_vec_from_embX_product {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    {c ρ : ℕ} (hρc : ρ < c) (x : GL n k) (u : _root_.GlobalTheory.RootEx.N k n c (ρ + 1))
    (β : n → k) (r : n) :
    ∑ s, (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
        _root_.GlobalTheory.RootEx.colE c (ρ + 1) β)⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl r) (Sum.inl s) *
      (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
        _root_.GlobalTheory.RootEx.colE c (ρ + 1) β) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl s) (Sum.inr ⟨ρ, hρc⟩) = β r := by
  obtain ⟨hll, hlr, -⟩ := unipotent_block_entries_eq_one_zero u.2
  obtain ⟨hll', -, hrl'⟩ := unipotent_block_entries_eq_one_zero (inv_mem u.2)
  have h1 : ∀ s, (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
      _root_.GlobalTheory.RootEx.colE c (ρ + 1) β) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl s) (Sum.inr ⟨ρ, hρc⟩) = ((x : Matrix n n k) *ᵥ β) s := by
    intro s
    rw [Units.val_mul, Units.val_mul, _root_.GlobalTheory.RootEx.Radical.embX_val,
      _root_.GlobalTheory.RootEx.ExchangeSupport.colE_val]
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hll, hlr, _root_.GlobalTheory.RootEx.ExchangeSupport.colM,
      Matrix.mulVec, dotProduct, Matrix.one_apply]
  have h2 : ∀ s, (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
      _root_.GlobalTheory.RootEx.colE c (ρ + 1) β)⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl r) (Sum.inl s) = (↑x⁻¹ : Matrix n n k) r s := by
    intro s
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← map_inv,
      _root_.GlobalTheory.RootEx.Radical.embX_val, _root_.GlobalTheory.RootEx.ExchangeSupport.colE_inv_val]
    simp only [Matrix.coe_units_inv] at hll' hrl' ⊢
    have hz : ∀ i : Fin c, (i : ℕ) = ρ →
        ∑ a, ((u : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)⁻¹ (Sum.inr i) (Sum.inl a) *
          (↑x : Matrix n n k)⁻¹ a s = 0 :=
      fun i hi => Finset.sum_eq_zero fun a _ => by rw [hrl' a i (by omega), zero_mul]
    simp +contextual [Matrix.mul_apply, Fintype.sum_sum_type, hll', _root_.GlobalTheory.RootEx.ExchangeSupport.colM,
      Matrix.one_apply, hz]
  simp_rw [h1, h2]
  change ((↑x⁻¹ : Matrix n n k) *ᵥ ((x : Matrix n n k) *ᵥ β)) r = β r
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]


open MeasureTheory ValuativeRel Matrix in
theorem _root_.GlobalTheory.RootEx.ProperTriple.proper_triple : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ)
    (_ : ρ < c) (C : Set (GL (n ⊕ Fin c) k)) (_ : IsCompact C),
    ∃ D : Set (GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1) × (n → k)), IsCompact D ∧
      ∀ z : GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1) × (n → k),
        _root_.GlobalTheory.RootEx.embX c z.1 * (z.2.1 : GL (n ⊕ Fin c) k) *
          _root_.GlobalTheory.RootEx.colE c (ρ + 1) z.2.2 ∈ C → z ∈ D := by
  intro k _ _ _ _ n _ _ c ρ _ hρc C hC
  let F : GL (n ⊕ Fin c) k → (n → k) := fun g r =>
    ∑ s, (↑g⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl r) (Sum.inl s) *
      (g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl s) (Sum.inr ⟨ρ, hρc⟩)
  have hF : Continuous F := by
    refine continuous_pi fun r => continuous_finsetSum _ fun s _ => ?_
    exact (Units.continuous_coe_inv.matrix_elem _ _).mul (Units.continuous_val.matrix_elem _ _)
  have hK : IsCompact (F '' C) := hC.image hF
  have hC' : IsCompact ((fun q : GL (n ⊕ Fin c) k × (n → k) =>
      q.1 * (_root_.GlobalTheory.RootEx.colE c (ρ + 1) q.2)⁻¹) '' (C ×ˢ (F '' C))) :=
    (hC.prod hK).image (continuous_fst.mul
      (_root_.GlobalTheory.RootEx.ExchangeSupport.continuous_colE.comp continuous_snd).inv)
  obtain ⟨D₀, hD₀, hD₀C⟩ := _root_.GlobalTheory.QuotInt.compact_preimage
    (_root_.GlobalTheory.RootEx.VolN.isClosed_N (k := k) (n := n) (c := c) (ρ + 1)) hC'
  refine ⟨(fun q : (GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1)) × (n → k) =>
    (q.1.1, q.1.2, q.2)) '' (D₀ ×ˢ (F '' C)), (hD₀.prod hK).image (by fun_prop), ?_⟩
  intro z hz
  have hβ : z.2.2 ∈ F '' C := ⟨_, hz, funext (recover_colE_vec_from_embX_product hρc z.1 z.2.1 z.2.2)⟩
  have hz' : (z.1, z.2.1) ∈ D₀ := hD₀C _ ⟨(_, z.2.2), ⟨hz, hβ⟩, by simp⟩
  exact ⟨((z.1, z.2.1), z.2.2), ⟨hz', hβ⟩, rfl⟩

end GlobalTheory.RootEx.ProperTriple
end

section

noncomputable section

open GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix

namespace GlobalTheory.LocalCartan

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]


open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.LocalCartan.diagT_mem_KO {t : n → kˣ} (ht : ∀ i, valuation k (t i : k) = 1) :
    _root_.GlobalTheory.SmGL.diagT k n t ∈ _root_.GlobalTheory.SplitWeil.KO k n := by
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [_root_.GlobalTheory.SmGL.val_diagT, diagonal_apply]
    split_ifs with h
    · subst h
      exact (Valuation.mem_integer_iff _ _).mpr (ht i).le
    · exact zero_mem _
  · rw [← map_inv, _root_.GlobalTheory.SmGL.val_diagT, diagonal_apply]
    split_ifs with h
    · subst h
      refine (Valuation.mem_integer_iff _ _).mpr (le_of_eq ?_)
      rw [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, ht i, inv_one]
    · exact zero_mem _


open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.LocalCartan.exists_diagT (g : GL n k) :
    ∃ x ∈ _root_.GlobalTheory.SplitWeil.KO k n, ∃ y ∈ _root_.GlobalTheory.SplitWeil.KO k n,
      ∃ t : n → kˣ, g = x * _root_.GlobalTheory.SmGL.diagT k n t * y := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors 𝒪[k])
    (Finset.univ : Finset (n × n)) (fun p => (g : Matrix n n k) p.1 p.2)
  choose G hG using fun i j => RingHom.mem_rangeS.mp (hb (i, j) (Finset.mem_univ _))
  set f := algebraMap 𝒪[k] k with hf
  set c : k := f b with hc_def
  have hc : c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hGg : f.mapMatrix (Matrix.of G) = c • (g : Matrix n n k) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul]
    rw [hG i j, Algebra.smul_def]
  have hdet : (Matrix.of G).det ≠ 0 := by
    intro h0
    have h1 := congrArg f h0
    rw [RingHom.map_det, hGg, map_zero, Matrix.det_smul] at h1
    exact mul_ne_zero (pow_ne_zero _ hc) ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero h1
  obtain ⟨P, C, hP, hC, a, ha, hPC⟩ := _root_.Formalism.UG.P.cartan_smith (Matrix.of G) hdet
  have hinj : Function.Injective f := IsFractionRing.injective _ _
  have hmap : ∀ A : GL n 𝒪[k],
      ((GeneralLinearGroup.map f A : GL n k) : Matrix n n k) = f.mapMatrix (A : Matrix n n 𝒪[k]) :=
    fun A => by ext i j; rw [GeneralLinearGroup.map_apply]; rfl
  have hmem : ∀ A : GL n 𝒪[k], GeneralLinearGroup.map f A ∈ _root_.GlobalTheory.SplitWeil.KO k n :=
    fun A => by unfold _root_.GlobalTheory.SplitWeil.KO; exact ⟨A, rfl⟩
  have hne : ∀ i, f (a i) / c ≠ 0 := fun i =>
    div_ne_zero ((map_ne_zero_iff f hinj).mpr (ha i)) hc
  refine ⟨_, hmem (GeneralLinearGroup.mk'' P hP), _, hmem (GeneralLinearGroup.mk'' C hC),
    fun i => Units.mk0 (f (a i) / c) (hne i), ?_⟩
  have key : f.mapMatrix P * diagonal (fun i => f (a i)) * f.mapMatrix C = c • (g : Matrix n n k) := by
    have hd : f.mapMatrix (diagonal a) = diagonal (fun i => f (a i)) := by
      rw [RingHom.mapMatrix_apply]
      exact Matrix.diagonal_map (map_zero f)
    rw [← hGg, hPC, map_mul, map_mul, hd]
  have hdiag : diagonal (fun i => ((Units.mk0 (f (a i) / c) (hne i) : kˣ) : k)) =
      c⁻¹ • diagonal (fun i => f (a i)) := by
    ext i j
    by_cases h : i = j <;> simp [diagonal_apply, h, div_eq_inv_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hmap, hmap, _root_.GlobalTheory.SmGL.val_diagT]
  change (g : Matrix n n k) = f.mapMatrix P * _ * f.mapMatrix C
  rw [hdiag, Matrix.mul_smul, Matrix.smul_mul, key, smul_smul, inv_mul_cancel₀ hc, one_smul]

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
private lemma ord_one_twisted_operators : _root_.GlobalTheory.SmGL.ord k 1 = 0 :=
  _root_.GlobalTheory.SmGL.ord_eq_zero_iff.mpr (by simp)

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
private lemma ord_inv_twisted_operators (y : kˣ) :
    _root_.GlobalTheory.SmGL.ord k y⁻¹ = -_root_.GlobalTheory.SmGL.ord k y := by
  have h := _root_.GlobalTheory.SmGL.ord_mul k y y⁻¹
  rw [mul_inv_cancel, ord_one_twisted_operators] at h
  omega

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
private lemma ord_zpow_uniformizer' {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) (m : ℤ) :
    _root_.GlobalTheory.SmGL.ord k (ϖ ^ m) = m := by
  have h1 := _root_.GlobalTheory.SmGL.ord_eq_one hϖ
  induction m using Int.induction_on with
  | zero => simpa using ord_one_twisted_operators
  | succ i ih => rw [_root_.zpow_add_one, _root_.GlobalTheory.SmGL.ord_mul, ih, h1]
  | pred i ih =>
    rw [_root_.zpow_sub_one, _root_.GlobalTheory.SmGL.ord_mul, ih, ord_inv_twisted_operators, h1]
    ring

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
private lemma exists_unit_mul_zpow_uniformizer {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) (x : kˣ) :
    ∃ u : kˣ, ∃ m : ℤ, valuation k (u : k) = 1 ∧ x = u * ϖ ^ m := by
  refine ⟨x * (ϖ ^ _root_.GlobalTheory.SmGL.ord k x)⁻¹, _root_.GlobalTheory.SmGL.ord k x, ?_, by simp⟩
  apply _root_.GlobalTheory.SmGL.ord_eq_zero_iff.mp
  rw [_root_.GlobalTheory.SmGL.ord_mul, ord_inv_twisted_operators,
    ord_zpow_uniformizer' hϖ]
  ring


open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.LocalCartan.cartan_decomposition (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n]
    (ϖ : kˣ) (g : GL n k) (hϖ : valuation k (ϖ : k) = uniformizer k) :
    ∃ x ∈ _root_.GlobalTheory.SplitWeil.KO k n, ∃ y ∈ _root_.GlobalTheory.SplitWeil.KO k n,
      ∃ m : n → ℤ, g = x * _root_.GlobalTheory.SmGL.diagT k n (fun i => ϖ ^ m i) * y := by
  obtain ⟨x, hx, y, hy, t, rfl⟩ := _root_.GlobalTheory.LocalCartan.exists_diagT g
  choose u m hu htu using fun i => exists_unit_mul_zpow_uniformizer hϖ (t i)
  refine ⟨x * _root_.GlobalTheory.SmGL.diagT k n u,
    mul_mem hx (_root_.GlobalTheory.LocalCartan.diagT_mem_KO hu), y, hy, m, ?_⟩
  have ht : t = u * fun i => ϖ ^ m i := funext htu
  rw [ht, map_mul]
  simp only [mul_assoc]

end GlobalTheory.LocalCartan
end
end

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem _root_.GlobalTheory.T.finite_quotient_cosets_scaledStandardLatticeBox : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (c₁ c₂ : kˣ), {yb : (n → k) ⧸ box n c₂ | ∃ y ∈ box n c₁, Submodule.Quotient.mk y = yb}.Finite := by
  first | exact @GlobalTheory.BoxCosets.finite_cosets | exact GlobalTheory.BoxCosets.finite_cosets | (intros; apply GlobalTheory.BoxCosets.finite_cosets <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem _root_.GlobalTheory.T.firstVertex_parahoricLevelChain_twist : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ (s : ℕ) (t : Type) [Fintype t] [DecidableEq t] (κ : Type) [Fintype κ] [DecidableEq κ] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (c : ℕ) (H : 0 + c = s + 1), (prX (Cgrp ((twistChain s t κ δ hδ η).lev 0 c H).J 1) : Set (GL (XIx κ t 0) k)) = KO k (XIx κ t 0) ∧ (∀ γ ∈ KO k (XIx κ t 0), ∃ hm : embX c γ ∈ ((twistChain s t κ δ hδ η).lev 0 c H).J, (((twistChain s t κ δ hδ η).lev 0 c H).lam ⟨_, hm⟩ : ℂ) = 1) ∧ ∀ u ∈ N k (XIx κ t 0) c 1, ∀ hm : u ∈ ((twistChain s t κ δ hδ η).lev 0 c H).J, (((twistChain s t κ δ hδ η).lev 0 c H).lam ⟨u, hm⟩ : ℂ) = ψ (simpleSum u) := by
  first | exact @GlobalTheory.TwistVertex.firstVertex_twist | exact GlobalTheory.TwistVertex.firstVertex_twist | (intros; apply GlobalTheory.TwistVertex.firstVertex_twist <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.piTensor_smooth_reps_exact_each_factor : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ i, Group (Γ i)] [∀ i, TopologicalSpace (Γ i)] (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)) (i : α) (B B₁ B₂ : GlobalTheory.SmGL.SmRep (Γ i)) (ι : B₁.ρ.IntertwiningMap B.ρ) (p : B.ρ.IntertwiningMap B₂.ρ), Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) → (∀ v, p v = 0 → ∃ u, ι u = v) → ∃ (ι' : (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B₁ a).ρ).IntertwiningMap (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B a).ρ)) (p' : (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B a).ρ).IntertwiningMap (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B₂ a).ρ)), Function.Injective ι' ∧ Function.Surjective p' ∧ (∀ u, p' (ι' u) = 0) ∧ (∀ v, p' v = 0 → ∃ u, ι' u = v) := by
  first | exact @GlobalTheory.SmGL.piTensor_exact_position | exact GlobalTheory.SmGL.piTensor_exact_position | (intros; apply GlobalTheory.SmGL.piTensor_exact_position <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.piTensor_doubly_indexed_swap_blocks_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (Y : α → β → Type) [∀ i j, AddCommGroup (Y i j)] [∀ i j, Module ℂ (Y i j)] (σ : ∀ i j, Representation ℂ (GL (c i j) k) (Y i j)), Nonempty (Representation.Equiv ((GlobalTheory.SmGL.piTensor fun i => GlobalTheory.SmGL.piTensor fun j => σ i j).comp (GlobalTheory.SmGL.swapBlocks k c)) (GlobalTheory.SmGL.piTensor fun j => GlobalTheory.SmGL.piTensor fun i => σ i j)) := by
  first | exact @GlobalTheory.SmGL.piTensor_swapBlocks_equiv | exact GlobalTheory.SmGL.piTensor_swapBlocks_equiv | (intros; apply GlobalTheory.SmGL.piTensor_swapBlocks_equiv <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.relative_jacquet_functor_piTensor_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] [LinearOrder β] (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) (X : α → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] (ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)), Nonempty ((GlobalTheory.SmGL.relJac f (GlobalTheory.SmGL.piTensor ρ)).Equiv (GlobalTheory.SmGL.piTensor fun i => GlobalTheory.SmGL.jac (f i) (ρ i))) := by
  first | exact @GlobalTheory.RelJacTensor.relJac_piTensor_equiv | exact GlobalTheory.RelJacTensor.relJac_piTensor_equiv | (intros; apply GlobalTheory.RelJacTensor.relJac_piTensor_equiv <;> assumption)
end

section


theorem _root_.GlobalTheory.T.hermForm_eq_of_im_eq_on_spanning_family : ∀ {g : ℕ} {L : Type} [AddCommGroup L] (P : L →+ (Fin g → ℂ)), Submodule.span ℝ (Set.range P) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (h h' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ a b, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h (P a)) (h (P b))).im = (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' (P a)) (h' (P b))).im) → ∀ x y, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h x) (h y) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' x) (h' y) := by
  first | exact @GlobalTheory.hermForm_eq_of_im_eq_on_spanning_lattice | exact GlobalTheory.hermForm_eq_of_im_eq_on_spanning_lattice | (intros; apply GlobalTheory.hermForm_eq_of_im_eq_on_spanning_lattice <;> assumption)
end

section


theorem _root_.GlobalTheory.T.eq_of_flag_of_hermForm_preserving : ∀ {α : Type} {m : α → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : α, Fin (m τ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) → ∀ (h h' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ x y, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h x) (h y) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' x) (h' y)) → ∀ (bv : ∀ τ, Fin (m τ) → (Fin g → ℂ)) (s : ℂ), s ≠ 0 → (∀ τ i, h (Pi.single (e.symm ⟨τ, i⟩) 1) - s • bv τ i ∈ Submodule.span ℂ (bv τ '' {j | j < i})) → (∀ τ i, h' (Pi.single (e.symm ⟨τ, i⟩) 1) - s • bv τ i ∈ Submodule.span ℂ (bv τ '' {j | j < i})) → h = h' := by
  first | exact @GlobalTheory.FlagEq.eq_of_flag_of_hermForm | exact GlobalTheory.FlagEq.eq_of_flag_of_hermForm | (intros; apply GlobalTheory.FlagEq.eq_of_flag_of_hermForm <;> assumption)
end
