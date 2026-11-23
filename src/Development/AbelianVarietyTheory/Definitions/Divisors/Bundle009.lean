module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle345
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.GalV

structure HTower (k : Type) [Field k] where
  Γ : Type
  Z : Scheme.{0}
  q : Z ⟶ Spec (CommRingCat.of k)
  Y : Γ → Scheme.{0}
  s : ∀ g, Y g ⟶ Z
  t : ∀ g, Y g ⟶ Z
  comm : ∀ g, t g ≫ q = s g ≫ q

variable {k : Type} [Field k] (l : ℕ) [Fact l.Prime] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω]

abbrev HTower.geomZ : Scheme.{0} := GlobalTheory.Et.geom Ω H.q

def HTower.sΩ (g : H.Γ) : GlobalTheory.Et.geom Ω (H.s g ≫ H.q) ⟶ H.geomZ Ω := GlobalTheory.Et.geomMap Ω (H.s g ≫ H.q) (H.s g) rfl

def HTower.tΩ (g : H.Γ) : GlobalTheory.Et.geom Ω (H.s g ≫ H.q) ⟶ H.geomZ Ω := GlobalTheory.Et.geomMap Ω (H.s g ≫ H.q) (H.t g) (H.comm g)


open Classical in
def hop (g : H.Γ) : Htot l (sch.obj (H.geomZ Ω)) →ₗ[ℚ_[l]] Htot l (sch.obj (H.geomZ Ω)) := by
  classical
  exact if h : ∃ T, IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T then h.choose else 0

def V (L : Type) [Field L] [Algebra ℚ_[l] L] {J : Type} (ι : J → H.Γ) (θ : J → L) :
    Submodule L (TensorProduct ℚ_[l] L (Htot l (sch.obj (H.geomZ Ω)))) :=
  genEig L (fun j => hop l H Ω (ι j)) θ

def galV (L : Type) [Field L] [Algebra ℚ_[l] L] (σ : Ω ≃ₐ[k] Ω) :
    TensorProduct ℚ_[l] L (Htot l (sch.obj (H.geomZ Ω))) →ₗ[L] TensorProduct ℚ_[l] L (Htot l (sch.obj (H.geomZ Ω))) :=
  (galTot l Ω H.q σ).baseChange L

def HTower.idTower (k : Type) [Field k] : HTower k where
  Γ := Unit
  Z := Spec (CommRingCat.of k)
  q := 𝟙 _
  Y := fun _ => Spec (CommRingCat.of k)
  s := fun _ => 𝟙 _
  t := fun _ => 𝟙 _
  comm := fun _ => rfl

end GlobalTheory.GalV

end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.Model

open GlobalTheory.PD

variable (k : Type) [Field k] (d : ℕ)

section Bundle

variable (k : Type) [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} (x : Fin (d + 1) → F)

end Bundle

section Cover

variable (k : Type) [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} (x : Fin (d + 1) → F)

def yc (i : Fin (d + 1)) : Fin d → F := fun j => x (i.succAbove j) / x i

theorem isFrac_of_adjoin_eq_top (S : Set F) (h : IntermediateField.adjoin k S = ⊤) :
    IsFractionRing (Algebra.adjoin k S) F := by
  refine IsFractionRing.of_field (Algebra.adjoin k S) F fun z => ?_
  have hz : z ∈ IntermediateField.adjoin k S := h ▸ IntermediateField.mem_top
  obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.1 hz
  exact ⟨⟨r, hr⟩, ⟨s, hs⟩, rfl⟩

theorem ratio_mem_field (hx : ∀ i, x i ≠ 0) (i a : Fin (d + 1)) :
    x a / x i ∈ IntermediateField.adjoin k (Set.range (yc x i)) := by
  rcases eq_or_ne a i with rfl | h
  · rw [div_self (hx a)]
    exact IntermediateField.one_mem _
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq h
    exact IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩

theorem adjoin_yc_eq_top (hP : IsPd k x) (i : Fin (d + 1)) :
    IntermediateField.adjoin k (Set.range (yc x i)) = ⊤ := by
  rw [eq_top_iff, ← hP.gen, IntermediateField.adjoin_le_iff]
  rintro _ ⟨j, rfl⟩
  show x j.succ / x 0 ∈ IntermediateField.adjoin k (Set.range (yc x i))

  have e : x j.succ / x 0 = (x j.succ / x i) / (x 0 / x i) := by
    rw [div_div_div_cancel_right₀ (hP.ne i)]
  rw [e]
  exact div_mem (ratio_mem_field k x hP.ne i _) (ratio_mem_field k x hP.ne i _)

theorem trdeg_eq (hP : IsPd k x) : Cardinal.mk (Fin d) ≤ Algebra.trdeg k F := by
  exact hP.indep.cardinalMk_le_trdeg

theorem indep_yc (hP : IsPd k x) (i : Fin (d + 1)) : AlgebraicIndependent k (yc x i) := by

  have : IsFractionRing (Algebra.adjoin k (Set.range (yc x i))) F :=
    isFrac_of_adjoin_eq_top k _ (adjoin_yc_eq_top k x hP i)
  have : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range (yc x i))) F :=
    IsLocalization.isAlgebraic F (nonZeroDivisors (Algebra.adjoin k (Set.range (yc x i))))
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite k (yc x i) (trdeg_eq k x hP)).1

theorem rA_single_eq (hx : ∀ i, x i ≠ 0) (i : Fin (d + 1)) :
    rA k x {i} = Algebra.adjoin k (Set.range (yc x i)) := by
  unfold rA
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨i', hi', j, rfl⟩
    rw [Finset.mem_singleton] at hi'
    subst hi'
    rcases eq_or_ne j i' with rfl | h
    · rw [div_self (hx j)]
      exact Subalgebra.one_mem _
    · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq h
      exact Algebra.subset_adjoin ⟨l, rfl⟩
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    exact Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, i.succAbove j, rfl⟩

def chartEquiv (hP : IsPd k x) (i : Fin (d + 1)) : MvPolynomial (Fin d) k ≃ₐ[k] rA k x {i} :=
  (indep_yc k x hP i).aevalEquiv.trans (Subalgebra.equivOfEq _ _ (rA_single_eq k x hP.ne i).symm)

end Cover

section Extra

end Extra

end GlobalTheory.PD.Model
end
end

section

noncomputable section

open MeasureTheory Matrix ValuativeRel Filter
open scoped NNReal Topology Kronecker

namespace GlobalTheory.WeilM

theorem eventually_comp_eq {P V : Type} [TopologicalSpace P] [TopologicalSpace V] {p₀ : P} (f g : P → V → V)
    (hf : Continuous fun q : P × V => f q.1 q.2) (hg : Continuous fun q : P × V => g q.1 q.2)
    (f0 : ∀ v, f p₀ v = v) (g0 : ∀ v, g p₀ v = v) (hgf : ∀ p v, g p (f p v) = v) {φ : V → ℂ} (hφ : φ ∈ SB V) :
    ∀ᶠ p in 𝓝 p₀, ∀ v, φ (f p v) = φ v := by
  have key : ∀ f : P → V → V, (Continuous fun q : P × V => f q.1 q.2) → (∀ v, f p₀ v = v) →
      ∀ᶠ p in 𝓝 p₀, ∀ v ∈ tsupport φ, φ (f p v) = φ v := fun f hf f0 => by
    refine IsCompact.eventually_forall_of_forall_eventually hφ.2 fun v _ => ?_
    filter_upwards [(hφ.1.comp_continuous hf).eventually_eq (p₀, v),
      (hφ.1.comp_continuous continuous_snd).eventually_eq (p₀, v)] with q h1 h2
    simp only [Function.comp, f0] at h1 h2
    rw [h1, h2]
  filter_upwards [key f hf f0, key g hg g0] with p h1 h2 v
  by_cases hv : v ∈ tsupport φ
  · exact h1 v hv
  · by_cases hw : f p v ∈ tsupport φ
    · rw [← h2 _ hw, hgf]
    · rw [image_eq_zero_of_notMem_tsupport hv, image_eq_zero_of_notMem_tsupport hw]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem eventually_char_eq_one (μ : Fˣ →* Circle) (hμ : Continuous μ) :
    ∀ᶠ t in 𝓝 (1 : Fˣ), μ t = 1 ∧ distribHaarChar F t = 1 := by
  have h0 : {t : Fˣ | ‖(μ t : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : Fˣ) :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨U, hU, hUV⟩ := h0
  have h1 : (fun x : F => 1 + x) ⁻¹' U ∈ 𝓝 (0 : F) :=
    (Continuous.tendsto' (by fun_prop) _ _ (by simp) : Tendsto (fun x : F => 1 + x) (𝓝 0) (𝓝 ((1 : Fˣ) : F))) hU
  have h2 : {x : F | valuation F x < 1} ∈ 𝓝 (0 : F) := (IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨1, fun _ h => h⟩
  obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset (inter_mem h1 h2)
  have h3 : Tendsto (fun t : Fˣ => (t : F) - 1) (𝓝 1) (𝓝 0) := Continuous.tendsto' (by fun_prop) _ _ (by simp)
  filter_upwards [h3.eventually (SplitWeil.cball_mem_nhds s)] with t ht
  have hv : valuation F (t : F) = 1 := by simpa using (valuation F).map_one_add_of_lt (hs ht).2
  have hn : ∀ n : ℕ, (t : F) ^ n - 1 ∈ SplitWeil.cball s := fun n => by
    induction n with
    | zero => simp [SplitWeil.cball]
    | succ n ih =>
      rw [show (t : F) ^ (n + 1) - 1 = t * (t ^ n - 1) + (t - 1) by ring]
      refine SplitWeil.add_mem_cball ?_ ht
      show valuation F ((t : F) * ((t : F) ^ n - 1)) ≤ valuation F (s : F)
      rw [map_mul, hv, one_mul]
      exact ih
  refine ⟨Circle.coe_eq_one.mp (eq_one_of_forall_pow_near fun n => ?_),
    NNReal.coe_injective (SplitWeil.nabs_eq_one_of_valuation_eq_one hv)⟩
  have : t ^ n ∈ Units.val ⁻¹' U := by simpa using (hs (hn n)).1
  simpa using hUV this

variable {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]


variable [Invertible (2 : F)] {JA : Matrix α α (F × F)} {JB : Matrix β β (F × F)}

end GlobalTheory.WeilM

end
end

section

open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
open scoped Classical

noncomputable section
namespace GlobalTheory.SplitFlip.Model
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section NonZero
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]


omit [DecidableEq A] in
theorem isPrimFrame_mul {Λ Λ' : Submodule 𝒪[k] (D → k)} {X : Matrix A D k} (hX : IsPrimFrame Λ X) (g : GL D k)
    (hg : ∀ x, x ᵥ* g.val ∈ Λ' ↔ x ∈ Λ) : IsPrimFrame Λ' (X * g.val) := by
  have hr : ∀ i, (X * g.val).row i = X.row i ᵥ* g.val := fun i => by
    funext j; simp [Matrix.row, Matrix.mul_apply, vecMul, dotProduct]
  refine ⟨?_, fun i => ?_, le_antisymm ?_ ?_⟩
  · rw [rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)]; exact hX.1
  · rw [hr, hg]; exact hX.2.1 i
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨Submodule.subset_span ⟨i, rfl⟩, by rw [SetLike.mem_coe, hr, hg]; exact hX.2.1 i⟩
  · rintro x ⟨hx, hx'⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hx
    have e1 : ∑ i, c i • (X * g.val).row i = (∑ i, c i • X.row i) ᵥ* g.val := by
      simp only [hr, sum_vecMul, smul_vecMul]
    rw [e1] at hx' ⊢
    have h2 : (∑ i, c i • X.row i) ∈ Submodule.span 𝒪[k] (Set.range X.row) := by
      rw [hX.2.2]
      exact ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)), (hg _).1 hx'⟩
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun 𝒪[k]).1 h2
    rw [← hd, sum_vecMul]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_vecMul, ← hr]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem val_le_iff_mem {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (r : 𝒪[k]) :
    r ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ e ↔ valuation k (r : k) ≤ valuation k ((ϖ ^ e : kˣ) : k) := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← (Valuation.integer.integers (valuation k)).le_iff_dvd]
  rfl


open Classical in
theorem sum_psi {ϖ : kˣ} (hϖ : IsUnif ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (e : ℕ) (s s' : Res (k := k) e) :
    ∑ t : Res (k := k) e, (ψ (((Quotient.out t : 𝒪[k]) : k) *
      ((((ϖ ^ e)⁻¹ : kˣ) : k) * (((Quotient.out s : 𝒪[k]) : k) - ((Quotient.out s' : 𝒪[k]) : k)))) : ℂ) =
      if s = s' then (Fintype.card (Res (k := k) e) : ℂ) else 0 := by
  split_ifs with h
  · subst h; simp
  set x : k := (((ϖ ^ e)⁻¹ : kˣ) : k) * (((Quotient.out s : 𝒪[k]) : k) - ((Quotient.out s' : 𝒪[k]) : k)) with hx
  have h0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := zero_lt_iff.2 (by simp)
  have hvx : valuation k x = (valuation k ((ϖ ^ e : kˣ) : k))⁻¹ *
      valuation k ((Quotient.out s - Quotient.out s' : 𝒪[k]) : k) := by
    rw [hx, map_mul, Units.val_inv_eq_inv_val, map_inv₀]; rfl
  have triv : ∀ y : k, valuation k y ≤ 1 → ψ y = 1 := fun y hy => (hψ 1).2 le_rfl y (by simpa using hy)
  have hx1 : ¬ valuation k x ≤ valuation k ((1 : kˣ) : k) := by
    intro H
    rw [hvx, Units.val_one, map_one, inv_mul_le_iff₀ h0, mul_one, ← val_le_iff_mem hϖ, ← Ideal.Quotient.eq] at H
    exact h (by simpa using H)
  rw [← hψ x] at hx1
  push Not at hx1
  obtain ⟨y, hy, hy'⟩ := hx1
  have hx0 : x ≠ 0 := by
    rintro H
    rw [H, map_zero, le_zero_iff, map_eq_zero] at hy
    exact hy' (by simp [hy])
  have hr : y / x ∈ 𝒪[k] := by
    rw [Valuation.mem_integer_iff, map_div₀]; exact div_le_one_of_le₀ hy zero_le
  have key : ∀ a b : 𝒪[k], Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e) a = Ideal.Quotient.mk _ b →
      ψ ((a : k) * x) = ψ ((b : k) * x) := fun a b hab => by
    rw [Ideal.Quotient.eq, val_le_iff_mem hϖ] at hab
    rw [show (a : k) * x = b * x + ((a - b : 𝒪[k]) : k) * x by push_cast; ring, AddChar.map_add_eq_mul,
      triv (((a - b : 𝒪[k]) : k) * x), mul_one]
    rw [map_mul, hvx, ← mul_assoc]
    exact mul_le_one' (by rw [mul_inv_le_iff₀ h0, one_mul]; exact hab) (Quotient.out s - Quotient.out s' : 𝒪[k]).2
  set S := ∑ t : Res (k := k) e, (ψ (((Quotient.out t : 𝒪[k]) : k) * x) : ℂ) with hS
  have hshift : S = ψ y * S := by
    rw [hS, Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight (Ideal.Quotient.mk _ (⟨_, hr⟩ : 𝒪[k]) : Res (k := k) e))]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [key _ (Quotient.out t + ⟨_, hr⟩) (by simp), ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 2
    push_cast
    field_simp
    ring
  by_contra hne
  exact hy' (Circle.ext (by simpa using (mul_left_eq_self₀.1 hshift.symm).resolve_right hne))

theorem sum_invFourierSum {ϖ : kˣ} (hϖ : IsUnif ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (e : ℕ)
    (P : Finset D) (Ψ : Matrix A D k → ℂ) (X : Matrix A D k) (S₀ : A → P → Res (k := k) e) :
    ∑ T : A → P → Res (k := k) e, GlobalTheory.SplitFlip.invFourierSum ψ ϖ e P Ψ (setCols P X (liftRes T)) *
      (ψ (pairCols P (setCols P X ((ϖ ^ e)⁻¹ • liftRes S₀)) (liftRes T)) : ℂ) =
      (Fintype.card (Res (k := k) e) : ℂ) ^ (Fintype.card A * P.card) * Ψ (setCols P X ((ϖ ^ e)⁻¹ • liftRes S₀)) := by
  classical
  have h1 : ∀ T S, setCols P (setCols P X T) S = setCols P X S := fun T S => by
    ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
  have h2 : ∀ T : A → P → Res (k := k) e, ∀ i, ∀ j ∈ P, setCols P X (liftRes T) i j ∈ 𝒪[k] := fun T i j h => by
    simpa [setCols, h] using liftRes_mem T i ⟨j, h⟩
  simp only [GlobalTheory.SplitFlip.invFourierSum_apply, if_pos (h2 _), h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h3 : ∀ S T : A → P → Res (k := k) e,
      (ψ (-pairCols P (setCols P X (liftRes T)) ((ϖ ^ e)⁻¹ • liftRes S)) : ℂ) *
        (ψ (pairCols P (setCols P X ((ϖ ^ e)⁻¹ • liftRes S₀)) (liftRes T)) : ℂ) =
      ∏ i, ∏ j, (ψ (((Quotient.out (T i j) : 𝒪[k]) : k) * ((((ϖ ^ e)⁻¹ : kˣ) : k) *
        (((Quotient.out (S₀ i j) : 𝒪[k]) : k) - ((Quotient.out (S i j) : 𝒪[k]) : k)))) : ℂ) := fun S T => by
    have hp : ∀ {ι : Type _} (s : Finset ι) (f : ι → k), (ψ (∑ i ∈ s, f i) : ℂ) = ∏ i ∈ s, (ψ (f i) : ℂ) :=
      fun s f => by
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul,
            Circle.coe_mul, ih]
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← Finset.prod_product', ← hp, Finset.sum_product]
    congr 2
    simp only [pairCols, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [setCols, liftRes, Units.smul_def]
    ring
  have h4 : ∀ S : A → P → Res (k := k) e, ∑ T : A → P → Res (k := k) e,
      ∏ i, ∏ j, (ψ (((Quotient.out (T i j) : 𝒪[k]) : k) * ((((ϖ ^ e)⁻¹ : kˣ) : k) *
        (((Quotient.out (S₀ i j) : 𝒪[k]) : k) - ((Quotient.out (S i j) : 𝒪[k]) : k)))) : ℂ) =
      if S₀ = S then (Fintype.card (Res (k := k) e) : ℂ) ^ (Fintype.card A * P.card) else 0 := fun S => by
    rw [← Fintype.prod_sum (fun i (t : P → Res (k := k) e) => ∏ j, (ψ (((Quotient.out (t j) : 𝒪[k]) : k) *
      ((((ϖ ^ e)⁻¹ : kˣ) : k) *
        (((Quotient.out (S₀ i j) : 𝒪[k]) : k) - ((Quotient.out (S i j) : 𝒪[k]) : k)))) : ℂ))]
    have h5 : ∀ i, ∑ t : P → Res (k := k) e, ∏ j, (ψ (((Quotient.out (t j) : 𝒪[k]) : k) * ((((ϖ ^ e)⁻¹ : kˣ) : k) *
        (((Quotient.out (S₀ i j) : 𝒪[k]) : k) - ((Quotient.out (S i j) : 𝒪[k]) : k)))) : ℂ) =
        ∏ j, if S₀ i j = S i j then (Fintype.card (Res (k := k) e) : ℂ) else 0 := fun i => by
      rw [← Fintype.prod_sum (fun (j : P) (t : Res (k := k) e) => (ψ (((Quotient.out t : 𝒪[k]) : k) *
        ((((ϖ ^ e)⁻¹ : kˣ) : k) *
        (((Quotient.out (S₀ i j) : 𝒪[k]) : k) - ((Quotient.out (S i j) : 𝒪[k]) : k)))) : ℂ))]
      exact Finset.prod_congr rfl fun j _ => by convert sum_psi hϖ hψ e (S₀ i j) (S i j)
    rw [Finset.prod_congr rfl fun i _ => h5 i]
    split_ifs with h
    · subst h; simp [← pow_mul, mul_comm]
    · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hi
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj))
  simp only [mul_assoc, h3, ← Finset.mul_sum, h4]
  simp [mul_comm]

variable [MeasurableSpace k] [BorelSpace k]

end NonZero

variable {A D₁ D₂ : Type*} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]





variable [MeasurableSpace k] [BorelSpace k]

end GlobalTheory.SplitFlip.Model
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory

namespace PDivGroup

open PDiv

variable {p : ℕ} {k : Type} [CommRing k]

def IsConn (G : PDivGroup p k) : Prop := ∀ n, ∀ a ∈ augIdeal k (G.A n), IsNilpotent a

def IsEt (G : PDivGroup p k) : Prop := ∀ n, IsReduced (G.A n)

end PDivGroup

end GlobalTheory
end
end
