module

public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Localization.Finiteness
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.SelfDualIsom

theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {M₁ M₂ V : Type}
    [AddCommGroup M₁] [Module (𝓞 E) M₁] [Module.Finite (𝓞 E) M₁]
    [AddCommGroup M₂] [Module (𝓞 E) M₂] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (φ₁ : M₁ →ₗ[𝓞 E] V) (φ₂ : M₂ →ₗ[𝓞 E] V)
    (hspan : Submodule.span E (Set.range φ₂) = ⊤) :
    ∃ N : ℕ, 0 < N ∧ ∀ x, (N : 𝓞 E) • φ₁ x ∈ LinearMap.range φ₂ := by
  classical
  have h1 : ∀ v : V, ∃ n : ℕ, 0 < n ∧ (n : 𝓞 E) • v ∈ LinearMap.range φ₂ := by
    intro v
    have hv : v ∈ Submodule.span E (Set.range φ₂) := by rw [hspan]; trivial
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E _ v hv
    rw [← LinearMap.coe_range, Submodule.span_eq] at ht
    have ht0 : (t : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero t.2
    have hm := Ideal.absNorm_mem (Ideal.span {(t : 𝓞 E)})
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hm
    refine ⟨Ideal.absNorm (Ideal.span {(t : 𝓞 E)}), Nat.pos_of_ne_zero ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact ht0
    · rw [← hc, mul_smul]
      exact Submodule.smul_mem _ _ ht
  choose n hn hmem using h1
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := 𝓞 E) (M := M₁)
  refine ⟨∏ x ∈ s, n (φ₁ x), Finset.prod_pos fun x _ => hn _, fun x => ?_⟩
  have hx : x ∈ Submodule.span (𝓞 E) (s : Set M₁) := by rw [hs]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => n (φ₁ x)) (Finset.mem_coe.1 hy)
    rw [hk, Nat.cast_mul, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (hmem _)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _), smul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul, smul_comm]; exact Submodule.smul_mem _ _ ha

end GlobalTheory.SelfDualIsom
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.ThetaHalf

theorem exists_real_of_half {g : ℕ} {c : Fin g → ℂ} (hc : ∀ i, c i = 0 ∨ c i = 1 / 2) :
    ∃ a : Fin g → ℝ, c = fun i => (a i : ℂ) := by
  refine ⟨fun i => if c i = 0 then 0 else 1 / 2, funext fun i => ?_⟩
  rcases hc i with h | h
  · show c i = ((if c i = 0 then (0 : ℝ) else 1 / 2 : ℝ) : ℂ)
    rw [if_pos h, h, Complex.ofReal_zero]
  · have h0 : c i ≠ 0 := by rw [h]; norm_num
    show c i = ((if c i = 0 then (0 : ℝ) else 1 / 2 : ℝ) : ℂ)
    rw [if_neg h0, h]
    norm_num

theorem thetaChar_holomorphic_ne_zero : ∀ (g : ℕ) (c₁ c₂ : Fin g → ℂ), (∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) → (∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2) → (∀ τ : Matrix (Fin g) (Fin g) ℂ, τ.IsSymm → (τ.map Complex.im).PosDef → Differentiable ℂ (thetaChar τ c₁ c₂) ∧ ∃ z, thetaChar τ c₁ c₂ z ≠ 0) ∧ ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B → (∀ b ∈ B, (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef) → (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B ∧ DifferentiableOn ℂ (fun b => τ b i j) B) → DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => thetaChar (τ bz.1) c₁ c₂ (h bz.1 *ᵥ bz.2)) (B ×ˢ Set.univ) := by
  intro g c₁ c₂ h₁ h₂
  obtain ⟨a, rfl⟩ := exists_real_of_half h₁
  obtain ⟨b, rfl⟩ := exists_real_of_half h₂
  refine ⟨fun τ hs hp => ⟨GlobalTheory.CanTh.differentiable_thetaChar (GlobalTheory.CanTh.mem_thetaDomain hp) a b, ?_⟩, ?_⟩
  · by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact GlobalTheory.CanTh.thetaChar_ne_zero hs hp a b (funext hcon)
  · intro m B h τ _ hτ hdiff
    have hT : ∀ i j, DifferentiableOn ℂ (fun w : (Fin m → ℂ) × (Fin g → ℂ) => τ w.1 i j) (B ×ˢ Set.univ) :=
      fun i j => (hdiff i j).2.comp differentiableOn_fst fun w hw => hw.1
    have hZ : DifferentiableOn ℂ (fun w : (Fin m → ℂ) × (Fin g → ℂ) => h w.1 *ᵥ w.2) (B ×ˢ Set.univ) := by
      rw [differentiableOn_pi]
      intro i
      simp only [Matrix.mulVec, dotProduct]
      have hj : ∀ j, DifferentiableOn ℂ (fun w : (Fin m → ℂ) × (Fin g → ℂ) => h w.1 i j) (B ×ˢ Set.univ) :=
        fun j => (hdiff i j).1.comp differentiableOn_fst fun w hw => hw.1
      refine DifferentiableOn.fun_sum fun j _ => (hj j).mul ?_
      have hs : Differentiable ℂ (fun w : (Fin m → ℂ) × (Fin g → ℂ) => w.2 j) := by fun_prop
      exact hs.differentiableOn
    have hdom : ∀ w ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)), τ w.1 ∈ ReciprocityTheory.PTheta.ThetaDomain (Fin g) :=
      fun w hw => GlobalTheory.CanTh.mem_thetaDomain (hτ w.1 hw.1).2
    exact GlobalTheory.CanTh.differentiableOn_thetaChar hT hZ hdom a b

end GlobalTheory.ThetaHalf
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.ExpChain

theorem isDerivAt0_comp_linear {g : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (he : IsHolTo Set.univ e) (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (w : Fin g → ℂ)
    (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt0 (fun z => e (L z)) w v ↔ IsDerivAt0 e (L w) v := by
  have key : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 →
      ∀ (U : X.Opens) (_ : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (L z)) U f) 0 w =
        fderiv ℂ (fun z => valAt' (e z) U f) 0 (L w) := by
    intro h0 U hU f
    have hmem : (0 : Fin g → ℂ) ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e b ⁻¹ᵁ U} := by
      refine ⟨trivial, ?_⟩
      rw [← h0]
      intro x _
      exact hU (Set.mem_univ _)
    have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) 0 :=
      ((he U f).2 0 hmem).differentiableAt ((he U f).1.mem_nhds hmem)
    let L' := LinearMap.toContinuousLinearMap L
    have hd' : HasFDerivAt (fun z => valAt' (e z) U f) (fderiv ℂ (fun z => valAt' (e z) U f) 0) (L' 0) := by
      rw [map_zero]; exact hd.hasFDerivAt
    have := (hd'.comp (0 : Fin g → ℂ) L'.hasFDerivAt).fderiv
    exact DFunLike.congr_fun this w
  unfold IsDerivAt0
  simp only [map_zero]
  exact and_congr_right fun h0 => forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => by
    rw [key h0 U hU f]

theorem isHolTo_slice {g m : ℕ} {X : Scheme.{0}} (e : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (h : IsHolTo (Set.univ ×ˢ Set.univ) e) : IsHolTo Set.univ (fun z => e (0, z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hj : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin m → ℂ), z)) :=
    (differentiable_const _).prodMk differentiable_id
  refine ⟨?_, ?_⟩
  · have h3 := h1.preimage hj.continuous
    simpa only [Set.preimage_setOf_eq, Set.mem_prod, Set.mem_univ, true_and] using h3
  · exact h2.comp hj.differentiableOn fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩

theorem isHolTo_ex {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di k) ty P) :
    IsHolTo Set.univ (fun z => (F.ex k P z).left) := by
  have h := (F.hol k 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  have h2 := isHolTo_slice _ h
  simp only at h2
  exact h2

theorem isDerivAt0_ex_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) ty P → ∀ (k' : Fin F.n) (P' : (F.Di k').La →+ (Fin g → ℂ)) (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsPeriod (F.Di k') ty P' → (∀ z, (F.ex k' P' (L z)).left = (F.ex k P z).left) → ∀ w (v : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)), IsDerivAt0 (fun z => (F.ex k P z).left) w v ↔ IsDerivAt0 (fun z => (F.ex k' P' z).left) (L w) v := by
  intro E _ _ _ H Dw l Xo σ' g ty F k P _ k' P' L hP' hL w v
  rw [← isDerivAt0_comp_linear _ (isHolTo_ex F k' P' hP') L w v]
  simp only [hL]

end GlobalTheory.ExpChain
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.PeriodLin


open NumberField AlgebraicGeometry CategoryTheory Limits in
open scoped Matrix nonZeroDivisors in
theorem _root_.GlobalTheory.PeriodLin.exists_period_mulVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (h₀ : Matrix (Fin g) (Fin g) ℂ), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P → IsUnit h₀.det → (∀ j j', h₀ j j' ≠ 0 → ty j = ty j') → ∃ P' : D.La →+ (Fin g → ℂ), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P' ∧ ∀ a, P' a = h₀ *ᵥ P a := by
  intro E _ _ _ H D g ty P h₀ hP hu hty
  refine ⟨(h₀.mulVecLin).toAddMonoidHom.comp P,
    _root_.GlobalTheory.PeriodConn.isPeriod_mulVec hP (isUnit_iff_ne_zero.mp hu) fun i j hij => ?_,
    fun a => rfl⟩
  by_contra hne
  exact hij (hty i j hne)

end GlobalTheory.PeriodLin
end
