module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle013
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle034
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle037
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

noncomputable section
namespace GlobalTheory.SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_cball_addChar_eq_one (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    ∃ s : kˣ, ∀ y ∈ cball s, ψ y = 1 := by
  have hU : ψ ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (0 : k) := by
    refine ((Circle.isOpen_centeredArc _).preimage hψ).mem_nhds ?_
    rw [Set.mem_preimage, AddChar.map_zero_eq_one]
    exact ⟨0, by simpa using Real.pi_pos, by simp⟩
  obtain ⟨s, hs⟩ := exists_cball_subset hU
  refine ⟨s, fun y hy => Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ => ?_⟩
  rw [← AddChar.map_nsmul_eq_pow]
  refine hs ?_
  clear * - hy
  induction n with
  | zero => simp [cball]
  | succ n ih => rw [succ_nsmul]; exact add_mem_cball ih hy

theorem exists_hasConductor_of_continuous (ψ : AddChar k Circle) (hψ : Continuous ψ) (h1 : ψ ≠ 1) :
    ∃ c : kˣ, HasConductor ψ c := by
  classical
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one ψ hψ
  obtain ⟨y₀, hy₀⟩ : ∃ y, ψ y ≠ 1 := by
    by_contra h
    push Not at h
    exact h1 (by ext y; simp [h y])
  have hy0 : y₀ ≠ 0 := by
    rintro rfl
    exact hy₀ (AddChar.map_zero_eq_one ψ)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := by simpa using hϖ.ne_zero
  have hlt : ∀ y : 𝒪[k], y ∈ 𝓂[k] ↔ valuation k (y : k) < 1 := fun y => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one
  have hϖ1 : valuation k (ϖ : k) < 1 := (hlt ϖ).mp hϖ.not_isUnit
  have hex : ∃ n : ℕ, ∀ y, valuation k y ≤ valuation k (y₀ * (ϖ : k) ^ n) → ψ y = 1 := by
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ1
      (Units.mk0 (valuation k (y₀⁻¹ * s)) (by simp [hy0]))
    refine ⟨n, fun y hy => hs y (show valuation k y ≤ valuation k (s : k) from hy.trans ?_)⟩
    rw [Units.val_mk0, map_mul, map_inv₀, lt_inv_mul_iff₀ (by simp [zero_lt_iff, hy0])] at hn
    rw [map_mul, map_pow]
    exact hn.le
  have hspec := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hspec
    exact hy₀ (hspec y₀ (by simp))
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hmin := Nat.find_min hex (m := m) (by omega)
  rw [hm] at hspec
  refine ⟨Units.mk0 (y₀ * (ϖ : k) ^ (m + 1)) (mul_ne_zero hy0 (pow_ne_zero _ h0)), fun x => ⟨fun h => ?_,
    fun h y hy => hspec y (hy.trans h)⟩⟩
  by_contra hx
  rw [Units.val_mk0, not_le] at hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hxp : 0 < valuation k x := by simp [zero_lt_iff, hx0]
  have hxi : valuation k (x⁻¹ * (y₀ * (ϖ : k) ^ (m + 1))) < 1 := by
    rw [map_mul, map_inv₀, inv_mul_lt_iff₀ hxp, mul_one]
    exact hx
  have h2 : valuation k (x⁻¹ * (y₀ * (ϖ : k) ^ (m + 1))) ≤ valuation k (ϖ : k) :=
    (mem_cball_uniformiser hϖ (x := Units.mk0 _ h0) rfl
      ⟨_, (Valuation.mem_integer_iff _ _).mpr hxi.le⟩).mpr ((hlt _).mpr hxi)
  rw [map_mul, map_inv₀, inv_mul_le_iff₀ hxp, pow_succ, ← mul_assoc, map_mul,
    mul_le_mul_iff_left₀ (by simp [zero_lt_iff, h0])] at h2
  exact hmin fun y hy => h y (hy.trans h2)

theorem conductor_exists :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [MeasurableSpace k] [BorelSpace k],
      (∀ ψ : AddChar k Circle, Continuous ψ → ψ ≠ 1 → ∃ c : kˣ, HasConductor ψ c) ∧
      (∃ ψ : AddChar k Circle, Continuous ψ ∧ ψ ≠ 1 ∧ HasConductor ψ 1) ∧
      ∃ ν : Measure k, IsUnitVol ν := by
  intro k _ _ _ _ _ _
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AddChar k Circle, HasConductor ψ 1 := exists_hasConductor_one k
  exact ⟨exists_hasConductor_of_continuous, ⟨ψ, hψ.continuous, hψ.ne_one, hψ⟩, exists_isUnitVol k⟩

end GlobalTheory.SplitWeil
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

namespace GlobalTheory.SplitWeil

section
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem om_smul_add (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) (z : ℂ) (Φ Ψ : Matrix b a k → ℂ) :
    om μ g h (z • Φ + Ψ) = z • om μ g h Φ + om μ g h Ψ := by
  funext x
  simp only [om, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem eventually_comp_sideMul_eq {Φ : Matrix b a k → ℂ} (hΦ : Φ ∈ SB (Matrix b a k)) :
    ∀ᶠ gh : GL a k × GL b k in 𝓝 1, ∀ x, Φ (sideMul gh.1 gh.2 x) = Φ x := by
  have hc : Continuous fun q : (GL a k × GL b k) × Matrix b a k => sideMul q.1.1 q.1.2 q.2 := by
    show Continuous fun q : (GL a k × GL b k) × Matrix b a k =>
      (q.1.2⁻¹ : GL b k).val * q.2 * q.1.1.val
    exact ((Units.continuous_coe_inv.comp (continuous_snd.comp continuous_fst)).matrix_mul
      continuous_snd).matrix_mul (Units.continuous_val.comp (continuous_fst.comp continuous_fst))
  have h1 : ∀ᶠ gh : GL a k × GL b k in 𝓝 1, ∀ x ∈ tsupport Φ, Φ (sideMul gh.1 gh.2 x) = Φ x := by
    refine IsCompact.eventually_forall_of_forall_eventually hΦ.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : (GL a k × GL b k) × Matrix b a k =>
        (Φ (sideMul q.1.1 q.1.2 q.2), Φ q.2) :=
      (hΦ.1.comp_continuous hc).prodMk (hΦ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (1, x)] with q hq
    simp only [Prod.mk.injEq] at hq
    rw [hq.1, hq.2]
    congr 1
    show ((1 : GL b k)⁻¹ : GL b k).val * x * (1 : GL a k).val = x
    simp
  have h2 : ∀ᶠ gh : GL a k × GL b k in 𝓝 1,
      ∀ x ∈ tsupport Φ, Φ (sideMul gh⁻¹.1 gh⁻¹.2 x) = Φ x := by
    have ht : Filter.Tendsto (fun gh : GL a k × GL b k => gh⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv (G := GL a k × GL b k)).tendsto 1
    exact ht.eventually h1
  filter_upwards [h1, h2] with gh hs hs' x
  by_cases hx : x ∈ tsupport Φ
  · exact hs x hx
  by_cases hx' : sideMul gh.1 gh.2 x ∈ tsupport Φ
  · rw [← hs' _ hx']
    congr 1
    have := (sideMul gh.1 gh.2).left_inv x
    refine Eq.trans ?_ this
    show (gh.2⁻¹⁻¹ : GL b k).val * sideMul gh.1 gh.2 x * (gh.1⁻¹ : GL a k).val = _
    rw [inv_inv]
    rfl
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem isOpen_valuation_eq_one : IsOpen {x : kˣ | valuation k (x : k) = 1} := by
  have : {x : kˣ | valuation k (x : k) = 1} =
      (fun x : kˣ => (x : k)) ⁻¹' (𝒪[k] : Set k) ∩ (fun x : kˣ => ((x⁻¹ : kˣ) : k)) ⁻¹' (𝒪[k] : Set k) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe,
      Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀]
    rw [inv_le_one₀ (by simp [zero_lt_iff])]
    exact le_antisymm_iff
  rw [this]
  exact ((isOpen_int k).preimage Units.continuous_val).inter
    ((isOpen_int k).preimage Units.continuous_coe_inv)

theorem eventually_det_trivial (n : Type*) [Fintype n] [DecidableEq n] {μ : kˣ →* ℂˣ}
    (hμ : IsOpen (μ.ker : Set kˣ)) :
    ∀ᶠ g : GL n k in 𝓝 1, μ (Matrix.GeneralLinearGroup.det g) = 1 ∧
      nabs k (Matrix.GeneralLinearGroup.det g) = 1 := by
  have hU := (hμ.inter isOpen_valuation_eq_one).preimage
    (Matrix.GeneralLinearGroup.continuous_det (n := n) (R := k))
  filter_upwards [hU.mem_nhds (x := 1) (by simp)] with g hg
  exact ⟨hg.1, nabs_eq_one_of_valuation_eq_one hg.2⟩

theorem isOpen_stabilizer_om {μ : kˣ →* ℂˣ} (hμ : IsOpen (μ.ker : Set kˣ)) {Φ : Matrix b a k → ℂ}
    (hΦ : Φ ∈ SB (Matrix b a k)) : IsOpen {gh : GL a k × GL b k | om μ gh.1 gh.2 Φ = Φ} := by
  let S : Subgroup (GL a k × GL b k) :=
    { carrier := {gh | om μ gh.1 gh.2 Φ = Φ}
      one_mem' := om_one μ Φ
      mul_mem' := fun {x y} hx hy => by
        show om μ (x.1 * y.1) (x.2 * y.2) Φ = Φ
        rw [om_mul, hy, hx]
      inv_mem' := fun {x} hx => by
        show om μ x.1⁻¹ x.2⁻¹ Φ = Φ
        conv_lhs => rw [← hx]
        rw [← om_mul, inv_mul_cancel, inv_mul_cancel, om_one] }
  refine S.isOpen_of_mem_nhds (g := 1) ?_
  have h1 := (continuous_fst.tendsto (1 : GL a k × GL b k)).eventually (eventually_det_trivial a hμ)
  have h2 := (continuous_snd.tendsto (1 : GL a k × GL b k)).eventually (eventually_det_trivial b hμ)
  filter_upwards [h1, h2, eventually_comp_sideMul_eq hΦ] with gh hg hh hs
  show om μ gh.1 gh.2 Φ = Φ
  funext x
  have := hs x
  simp only [om, hg.1, hg.2, hh.1, hh.2, Real.one_rpow, inv_one, Units.val_one, Complex.ofReal_one,
    one_mul]
  exact this

end

theorem om_isSmoothRepresentation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)), (∀ Φ : Matrix b a k → ℂ, om μ 1 1 Φ = Φ) ∧ (∀ (g g' : GL a k) (h h' : GL b k) (Φ : Matrix b a k → ℂ), om μ (g * g') (h * h') Φ = om μ g h (om μ g' h' Φ)) ∧ (∀ (g : GL a k) (h : GL b k) (z : ℂ) (Φ Ψ : Matrix b a k → ℂ), om μ g h (z • Φ + Ψ) = z • om μ g h Φ + om μ g h Ψ) ∧ (∀ (g : GL a k) (h : GL b k), ∀ Φ ∈ SB (Matrix b a k), om μ g h Φ ∈ SB (Matrix b a k)) ∧ ∀ Φ ∈ SB (Matrix b a k), IsOpen {gh : GL a k × GL b k | om μ gh.1 gh.2 Φ = Φ} :=
  fun _ _ _ _ _ _ _ _ _ _ _ μ hμ =>
    ⟨om_one μ, om_mul μ, om_smul_add μ, fun g h _ hΦ => om_mem_SB μ g h hΦ,
      fun _ hΦ => isOpen_stabilizer_om hμ hΦ⟩

end GlobalTheory.SplitWeil
end

section

open scoped TensorProduct

namespace GlobalTheory.TensHead

section Quot
variable {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def quotOp (N : Submodule ℂ V) (f : Module.End ℂ V) : Module.End ℂ (V ⧸ N) := by
  classical
  exact if h : N ≤ N.comap f then N.mapQ N f h else 0

theorem quotOp_mk (N : Submodule ℂ V) (f : Module.End ℂ V) (h : ∀ x ∈ N, f x ∈ N) (x : V) :
    quotOp N f (N.mkQ x) = N.mkQ (f x) := by
  have h' : N ≤ N.comap f := fun x hx => h x hx
  unfold quotOp
  rw [dite_eq_left h']
  simp

theorem quotOp_mul (N : Submodule ℂ V) (f₁ f₂ : Module.End ℂ V) (h₁ : ∀ x ∈ N, f₁ x ∈ N)
    (h₂ : ∀ x ∈ N, f₂ x ∈ N) : quotOp N f₁ * quotOp N f₂ = quotOp N (f₁ * f₂) := by
  have h₁₂ : ∀ x ∈ N, (f₁ * f₂) x ∈ N := fun x hx => h₁ _ (h₂ x hx)
  apply Submodule.linearMap_qext
  ext x
  simp only [LinearMap.comp_apply, Module.End.mul_apply]
  rw [quotOp_mk N f₂ h₂, quotOp_mk N f₁ h₁, quotOp_mk N _ h₁₂, Module.End.mul_apply]

end Quot

section Slot
variable {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

theorem piOp_comm (i j : ι) (hij : j ≠ i) (g : Module.End ℂ (M i)) (h : Module.End ℂ (M j)) :
    piOp i g * piOp j h = piOp j h * piOp i g := by
  unfold piOp
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← PiTensorProduct.map_comp,
    ← PiTensorProduct.map_comp]
  congr 1
  funext k
  by_cases hki : k = i
  · subst hki
    simp [Function.update_of_ne hij.symm]
  · by_cases hkj : k = j
    · subst hkj
      simp [Function.update_of_ne hij]
    · simp [Function.update_of_ne hki, Function.update_of_ne hkj]

end Slot

end GlobalTheory.TensHead

namespace GlobalTheory.TensHead

theorem position_mem_of_maximal_stable : ∀ {ι : Type} [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]
    {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i))) (i : ι)
    (Rel K : Submodule ℂ (M i)),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (M i)), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op i, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ (M i), Rel ≤ N → GlobalTheory.TensHead.Stab (Op i) N → N ≠ ⊤ → N ≤ K) →
    K ≠ ⊤ → GlobalTheory.TensHead.Stab (Op i) K →
    ∀ N' : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)),
      (∀ x ∈ Rel, ∀ (x₀ : M₀) (y : ∀ j, M j),
        x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N') →
      GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ (GlobalTheory.TensHead.piOps Op)) N' →
      (∀ U, GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ (GlobalTheory.TensHead.piOps Op)) U → N' ≤ U →
        U = N' ∨ U = ⊤) →
      ∀ x ∈ K, ∀ (x₀ : M₀) (y : ∀ j, M j),
        x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N' := by
  intro ι _ M₀ _ _ M _ _ Op₀ Op i Rel K hlen hmax hK hKst N' hRel hN'st hN'max x hx x₀ y
  let φ : M i →ₗ[ℂ] (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)) ⧸ N' :=
    N'.mkQ ∘ₗ (TensorProduct.mk ℂ M₀ (⨂[ℂ] j, M j) x₀) ∘ₗ
      ((PiTensorProduct.tprod ℂ : (∀ j, M j) →ₘₗ[ℂ] (⨂[ℂ] j, M j)).toLinearMap y i)
  have hφ : ∀ z, φ z = N'.mkQ (x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i z)) := by
    intro z
    simp [φ, MultilinearMap.toLinearMap_apply]
  let act : Module.End ℂ (M i) → Module.End ℂ ((M₀ ⊗[ℂ] (⨂[ℂ] j, M j)) ⧸ N') :=
    fun g => quotOp N' (TensorProduct.map LinearMap.id (piOp i g))
  let B : Set (Module.End ℂ ((M₀ ⊗[ℂ] (⨂[ℂ] j, M j)) ⧸ N')) :=
    quotOp N' '' ({f | ∃ g ∈ Op₀, f = TensorProduct.map g LinearMap.id} ∪
      {f | ∃ j, j ≠ i ∧ ∃ h ∈ Op j, f = TensorProduct.map LinearMap.id (piOp j h)})
  have hst0 : ∀ g ∈ Op₀, ∀ z ∈ N', TensorProduct.map g LinearMap.id z ∈ N' :=
    fun g hg => hN'st _ (Or.inl ⟨g, hg, rfl⟩)
  have hst1 : ∀ j, ∀ h ∈ Op j, ∀ z ∈ N', TensorProduct.map LinearMap.id (piOp j h) z ∈ N' :=
    fun j h hh => hN'st _ (Or.inr ⟨piOp j h, ⟨j, h, hh, rfl⟩, rfl⟩)
  have key := GlobalTheory.T.le_ker_of_local_finite_length_to_simple (Op i) Rel K φ act B hlen hmax hK hKst ?_ ?_ ?_ ?_
  · have h0 := key hx
    rw [LinearMap.mem_ker, hφ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  · intro z hz
    rw [LinearMap.mem_ker, hφ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hRel z hz x₀ y
  · intro g hg
    ext z
    simp only [LinearMap.comp_apply]
    rw [hφ, hφ, quotOp_mk N' _ (hst1 i g hg), TensorProduct.map_tmul, LinearMap.id_apply,
      piOp_tprod_update]
  · intro g hg b hb
    obtain ⟨f, hf, rfl⟩ := hb
    rcases hf with ⟨g₀, hg₀, rfl⟩ | ⟨j, hji, h, hh, rfl⟩
    · rw [quotOp_mul N' _ _ (hst1 i g hg) (hst0 g₀ hg₀), quotOp_mul N' _ _ (hst0 g₀ hg₀) (hst1 i g hg)]
      congr 1
      simp only [Module.End.mul_eq_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
        LinearMap.comp_id]
    · rw [quotOp_mul N' _ _ (hst1 i g hg) (hst1 j h hh), quotOp_mul N' _ _ (hst1 j h hh) (hst1 i g hg)]
      congr 1
      simp only [Module.End.mul_eq_comp, ← TensorProduct.map_comp, LinearMap.id_comp]
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, piOp_comm i j hji g h]
  · intro U hU
    have hs : U = (U.comap N'.mkQ).map N'.mkQ :=
      (Submodule.map_comap_eq_of_surjective N'.mkQ_surjective U).symm
    have hle : N' ≤ U.comap N'.mkQ := by
      intro z hz
      rw [Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N').mpr hz]
      exact U.zero_mem
    have hstab : Stab (tensOps Op₀ (piOps Op)) (U.comap N'.mkQ) := by
      intro f hf z hz
      rw [Submodule.mem_comap] at hz ⊢
      rw [← quotOp_mk N' f (hN'st f hf)]
      apply hU _ _ _ hz
      rcases hf with ⟨g₀, hg₀, rfl⟩ | ⟨p, ⟨j, h, hh, rfl⟩, rfl⟩
      · exact Or.inr ⟨_, Or.inl ⟨g₀, hg₀, rfl⟩, rfl⟩
      · by_cases hji : j = i
        · subst hji
          exact Or.inl ⟨h, hh, rfl⟩
        · exact Or.inr ⟨_, Or.inr ⟨j, hji, h, hh, rfl⟩, rfl⟩
    rcases hN'max _ hstab hle with h | h
    · left
      rw [hs, h, Submodule.mkQ_map_self]
    · right
      rw [hs, h, Submodule.map_top, Submodule.range_mkQ]

end GlobalTheory.TensHead
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory

theorem gl_character_eq_one_of_transpose_inv (k : Type) [Field k] [Infinite k] (n : Type)
    [Fintype n] [DecidableEq n] (χ : GL n k →* NNReal)
    (h : ∀ g g' : GL n k, g'.val = (g⁻¹ : GL n k).valᵀ → χ g' = χ g) (g : GL n k) :
    χ g = 1 := by
  classical
  have hne : ∀ g : GL n k, χ g ≠ 0 := by
    intro g h0
    have : χ (g * g⁻¹) = 1 := by simp
    rw [map_mul, h0, zero_mul] at this
    exact zero_ne_one this
  have hdiag : ∀ (D : n → k) (g : GL n k), g.val = diagonal D → χ g = 1 := by
    intro D g hg
    have h1 : χ g⁻¹ = χ g := by
      apply h
      rw [Matrix.coe_units_inv, Matrix.transpose_nonsing_inv, hg, diagonal_transpose]
    have h2 : χ g * χ g = 1 := by
      calc χ g * χ g = χ g * χ g⁻¹ := by rw [h1]
        _ = 1 := by rw [← map_mul]; simp
    have h3 : χ g ^ 2 = 1 := by rw [sq, h2]
    exact (pow_eq_one_iff_of_nonneg (zero_le) two_ne_zero).1 h3
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  have ha0 : a ≠ 0 := by intro h0; apply ha; simp [h0]
  have ha1 : 1 - a ≠ 0 := by
    intro h0; apply ha; have : a = 1 := by linear_combination -h0
    simp [this]
  have htr : ∀ (t : TransvectionStruct n k) (g : GL n k), g.val = t.toMatrix → χ g = 1 := by
    rintro ⟨i, j, hij, x⟩ g hg
    let T : k → GL n k := fun y => GeneralLinearGroup.mkOfDetNeZero (transvection i j y)
      (by rw [det_transvection_of_ne i j hij]; exact one_ne_zero)
    have hT : ∀ y, (T y).val = transvection i j y := fun y => rfl
    have hgT : g = T x := Units.ext (by rw [hg, hT]; rfl)
    have hconj : ∀ b : k, b ≠ 0 → χ (T (b * x)) = χ (T x) := by
      intro b hb
      let D : GL n k := GeneralLinearGroup.mkOfDetNeZero (diagonal (Function.update 1 i b))
        (by
          rw [det_diagonal]
          refine Finset.prod_ne_zero_iff.2 fun l _ => ?_
          by_cases hl : l = i
          · subst hl; simpa using hb
          · simp [Function.update_of_ne hl])
      have hD : D.val = diagonal (Function.update 1 i b) := rfl
      have e : D * T x = T (b * x) * D := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, hD, hT, hT]
        ext p q
        rw [diagonal_mul, mul_diagonal]
        simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
        by_cases hp : i = p
        · subst hp
          by_cases hq : j = q
          · subst hq
            simp [hij, Function.update_of_ne hij.symm]
          · by_cases hpq : i = q
            · subst hpq; simp [hq]
            · simp [hq, hpq]
        · by_cases hpq : p = q
          · subst hpq; simp [hp]
          · simp [hp, hpq]
      have := congrArg χ e
      rw [map_mul, map_mul, hdiag _ D hD, one_mul, mul_one] at this
      exact this.symm
    have e : T x = T (a * x) * T ((1 - a) * x) := by
      apply Units.ext
      rw [Units.val_mul, hT, hT, hT, transvection_mul_transvection_same i j hij]
      congr 1
      ring
    have e2 := congrArg χ e
    rw [map_mul, hconj a ha0, hconj _ ha1] at e2
    rw [hgT]
    exact (mul_eq_left₀ (hne _)).1 e2.symm
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ g : GL n k, g.val = M → χ g = 1) g.val g.det_ne_zero
    (fun D _ => hdiag D) htr ?_ g rfl
  intro A B hA hB pA pB u hu
  have : u = GeneralLinearGroup.mkOfDetNeZero A hA * GeneralLinearGroup.mkOfDetNeZero B hB :=
    Units.ext hu
  rw [this, map_mul, pA _ rfl, pB _ rfl, one_mul]

end GlobalTheory
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.periodic_theta_norm_mean_factor_le : ∀ (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (Fd Fd' : Set (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (u u' : (Fin g → ℂ) → ℝ) (p n : ℕ) (v : Fin n → (Fin g → ℂ)) (T : ℝ), Countable Λ → Countable Λ' → MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume → MeasureTheory.IsAddFundamentalDomain Λ' Fd' MeasureTheory.volume → 0 < p → (∀ a ∈ Λ, h a ∈ Λ') → (∀ z, 0 ≤ u z) → (∀ z, 0 ≤ u' z) → (∀ a ∈ Λ, ∀ z, u (z + a) = u z) → (∀ a ∈ Λ', ∀ z, u' (z + a) = u' z) → (∫ z in Fd, u z ^ 2) / (MeasureTheory.volume Fd).toReal = 1 → (∫ z in Fd', u' z ^ 2) / (MeasureTheory.volume Fd').toReal = 1 → (∀ z, T * u' (h z) ≤ ∑ m, u ((p : ℂ) • z + v m)) → T ≤ n := by
  first | exact @GlobalTheory.PeriodicMean.mean_factor_le | exact GlobalTheory.PeriodicMean.mean_factor_le | (intros; apply GlobalTheory.PeriodicMean.mean_factor_le <;> assumption)
end
