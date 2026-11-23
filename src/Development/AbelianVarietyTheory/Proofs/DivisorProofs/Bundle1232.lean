module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.Valuation.LocalSubring
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

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TraceLevel

theorem apply_out_mk {L W : Type} [Group L] (H : Subgroup L) (ψ : L → W) (hψ : ∀ g, ∀ h ∈ H, ψ (g * h) = ψ g)
    (g : L) : ψ (QuotientGroup.mk g : L ⧸ H).out = ψ g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh, hψ g h h.2]

theorem finsum_out_left {L W : Type} [Group L] [AddCommMonoid W] (H : Subgroup L) (ψ : L → W)
    (hψ : ∀ g, ∀ h ∈ H, ψ (g * h) = ψ g) (l : L) :
    ∑ᶠ q : L ⧸ H, ψ (l * q.out) = ∑ᶠ q : L ⧸ H, ψ q.out := by
  rw [← finsum_comp_equiv (MulAction.toPerm l : Equiv.Perm (L ⧸ H)) (f := fun q : L ⧸ H => ψ q.out)]
  congr 1
  funext q
  have : (MulAction.toPerm l : Equiv.Perm (L ⧸ H)) q = (QuotientGroup.mk (l * q.out) : L ⧸ H) := by
    rw [MulAction.toPerm_apply]
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  show ψ (l * q.out) = ψ ((MulAction.toPerm l : Equiv.Perm (L ⧸ H)) q).out
  rw [this, apply_out_mk H ψ hψ]

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (H : Subgroup G) (v : V) : v ∈ fixed ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  constructor
  · intro hv h hh
    have := hv ⟨h, hh⟩
    simpa using this
  · intro hv h
    show ρ (h : G) v = ((1 : H →* ℂˣ) h : ℂ) • v
    simpa using hv h h.2

theorem support_out_finite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (F : G → ℂ) (hF : HasCompactSupport F) :
    (Function.support fun q : G ⧸ H => F q.out).Finite := by
  haveI := QuotientGroup.discreteTopology hH
  refine ((HasCompactSupport.isCompact hF).image QuotientGroup.continuous_mk).finite_of_discrete.subset ?_
  intro q hq
  exact ⟨q.out, subset_tsupport _ hq, QuotientGroup.out_eq' q⟩

end GlobalTheory.TraceLevel

namespace GlobalTheory.TraceLevel

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem levOp_id_apply (ρ : Representation ℂ G V) (K H : Subgroup G) (F : G → ℂ)
    (hfin : (Function.support fun q : G ⧸ H => F q.out).Finite) (v : V) :
    levOp ρ K H F LinearMap.id v = ((H.relIndex K : ℕ) : ℂ)⁻¹ • ∑ᶠ q : G ⧸ H, F q.out • ρ q.out v := by
  unfold levOp
  rw [LinearMap.smul_apply]
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (fun q hq => by
      rw [Set.Finite.coe_toFinset]
      exact Function.mem_support.2 fun h0 => (Function.mem_support.1 hq) (by simp [h0])),
    finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (fun q hq => by
      rw [Set.Finite.coe_toFinset]
      exact Function.mem_support.2 fun h0 => (Function.mem_support.1 hq) (by simp [h0])),
    LinearMap.sum_apply]
  simp

theorem levOp_mem_fixed (ρ : Representation ℂ G V) (K K₀ H : Subgroup G) (F : G → ℂ) (hF : IsHecke K₀ F)
    (hH : IsOpen (H : Set G)) (hle : H ≤ K₀) (v : V) (hv : v ∈ fixed ρ H) :
    levOp ρ K H F LinearMap.id v ∈ fixed ρ H := by
  have hfin := support_out_finite H hH F hF.1
  rw [mem_fixed_iff] at hv ⊢
  intro k hk
  rw [levOp_id_apply ρ K H F hfin, map_smul]
  congr 1
  have hfin' : (Function.support fun q : G ⧸ H => F q.out • ρ q.out v).Finite :=
    hfin.subset fun q hq => Function.mem_support.2 fun h0 => (Function.mem_support.1 hq) (by simp [h0])
  rw [map_finsum (ρ k) hfin']
  have := finsum_out_left H (fun g => F g • ρ g v) (fun g h hh => by
    rw [(hF.2 h (hle hh) g).2, map_mul, Module.End.mul_apply, hv h hh]) k
  rw [← this]
  congr 1
  funext q
  rw [map_smul, ← Module.End.mul_apply, ← map_mul, (hF.2 k (hle hk) q.out).1]

theorem twTr_level (ρ : Representation ℂ G V) (K K₀ K'' : Subgroup G) (F : G → ℂ) (hK''o : IsOpen (K'' : Set G))
    (hK : IsCompact (K : Set G)) (hle : K'' ≤ K₀) (hle' : K₀ ≤ K) (hF : IsHecke K₀ F)
    (hfd : FiniteDimensional ℂ (fixed ρ K'')) :
    twTr ρ K K'' F LinearMap.id = twTr ρ K K₀ F LinearMap.id := by
  have hK₀o : IsOpen (K₀ : Set G) := Subgroup.isOpen_mono hle hK''o
  have hc : K''.relIndex K ≠ 0 := by
    haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have ho : IsOpen ((K''.subgroupOf K : Subgroup K) : Set K) := hK''o.preimage continuous_subtype_val
    haveI := Subgroup.quotient_finite_of_isOpen _ ho
    exact Subgroup.index_ne_zero_of_finite
  have hmul : K''.relIndex K₀ * K₀.relIndex K = K''.relIndex K :=
    Subgroup.relIndex_mul_relIndex (H := K'') (K := K₀) (L := K) hle hle'
  have hd : K''.relIndex K₀ ≠ 0 := left_ne_zero_of_mul (hmul ▸ hc)
  have hcard : Nat.card (↥K₀ ⧸ K''.subgroupOf K₀) ≠ 0 := hd
  haveI : Finite (↥K₀ ⧸ K''.subgroupOf K₀) := Nat.finite_of_card_ne_zero hcard
  letI := Fintype.ofFinite (↥K₀ ⧸ K''.subgroupOf K₀)
  set d : ℕ := K''.relIndex K₀ with hd_def
  obtain ⟨P, hPapp⟩ : ∃ P : V →ₗ[ℂ] V, ∀ v, P v =
      (d : ℂ)⁻¹ • ∑ k : ↥K₀ ⧸ K''.subgroupOf K₀, ρ ((k.out : K₀) : G) v :=
    ⟨(d : ℂ)⁻¹ • ∑ k : ↥K₀ ⧸ K''.subgroupOf K₀, ρ ((k.out : K₀) : G), fun v => by
      simp [LinearMap.sum_apply]⟩
  have hPfix : ∀ v ∈ fixed ρ K'', P v ∈ fixed ρ K₀ := by
    intro v hv
    rw [mem_fixed_iff] at hv ⊢
    intro k hk

    rw [hPapp, map_smul, map_sum]
    congr 1
    have := finsum_out_left (K''.subgroupOf K₀) (fun x : K₀ => ρ (x : G) v) (fun g h hh => by
      simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
      rw [hv _ (Subgroup.mem_subgroupOf.1 hh)]) ⟨k, hk⟩
    simp only [finsum_eq_sum_of_fintype, Subgroup.coe_mul, map_mul, Module.End.mul_apply] at this
    exact this
  have hPid : ∀ v ∈ fixed ρ K₀, P v = v := by
    intro v hv
    rw [mem_fixed_iff] at hv
    rw [hPapp, Finset.sum_congr rfl (fun k _ => hv _ (k.out).2), Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    have : (Fintype.card (↥K₀ ⧸ K''.subgroupOf K₀) : ℂ) = d := by
      rw [← Nat.card_eq_fintype_card]
      rfl
    rw [this, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hd), one_smul]
  have key : ∀ v ∈ fixed ρ K'', levOp ρ K K'' F LinearMap.id v = levOp ρ K K₀ F LinearMap.id (P v) := by
    intro v hv
    have hv' := (mem_fixed_iff ρ K'' v).1 hv
    have hfin'' := support_out_finite K'' hK''o F hF.1
    have hfin₀ := support_out_finite K₀ hK₀o F hF.1
    rw [levOp_id_apply ρ K K'' F hfin'', levOp_id_apply ρ K K₀ F hfin₀]
    have hR : ∀ a : G ⧸ K₀, F a.out • ρ a.out (P v) =
        (d : ℂ)⁻¹ • ∑ᶠ b : ↥K₀ ⧸ K''.subgroupOf K₀, F a.out • ρ (a.out * ((b.out : K₀) : G)) v := by
      intro a

      rw [hPapp, map_smul, map_sum, smul_comm, finsum_eq_sum_of_fintype, Finset.smul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      rw [map_mul, Module.End.mul_apply]
    simp_rw [hR]
    rw [← smul_finsum, smul_smul]
    have hL : ∑ᶠ q : G ⧸ K'', F q.out • ρ q.out v =
        ∑ᶠ a : G ⧸ K₀, ∑ᶠ b : ↥K₀ ⧸ K''.subgroupOf K₀, F a.out • ρ (a.out * ((b.out : K₀) : G)) v := by
      set e := Subgroup.quotientEquivProdOfLE hle
      rw [← finsum_comp_equiv e.symm]
      have hφ : ∀ g, ∀ h ∈ K'', (fun g => F g • ρ g v) (g * h) = (fun g => F g • ρ g v) g := fun g h hh => by
        simp only
        rw [(hF.2 h (hle hh) g).2, map_mul, Module.End.mul_apply, hv' h hh]
      have he : ∀ p : (G ⧸ K₀) × (↥K₀ ⧸ K''.subgroupOf K₀),
          e.symm p = (QuotientGroup.mk (p.1.out * ((p.2.out : K₀) : G)) : G ⧸ K'') := by
        rintro ⟨a, b⟩
        conv_lhs => rw [← QuotientGroup.out_eq' b]
        rfl
      have h2 : ∀ p : (G ⧸ K₀) × (↥K₀ ⧸ K''.subgroupOf K₀),
          F (e.symm p).out • ρ (e.symm p).out v = F p.1.out • ρ (p.1.out * ((p.2.out : K₀) : G)) v := by
        intro p
        rw [he p]
        have := apply_out_mk K'' (fun g => F g • ρ g v) hφ (p.1.out * ((p.2.out : K₀) : G))
        rw [this, (hF.2 _ (p.2.out).2 p.1.out).2]
      simp_rw [h2]
      rw [finsum_curry]
      refine (hfin₀.prod Set.finite_univ).subset ?_
      rintro ⟨a, b⟩ hp
      refine ⟨?_, Set.mem_univ _⟩
      exact Function.mem_support.2 fun h0 => (Function.mem_support.1 hp) (by simp [h0])
    rw [hL]
    congr 1
    rw [← hmul]
    push_cast
    rw [mul_inv, mul_comm]
  have hVle : fixed ρ K₀ ≤ fixed ρ K'' := by
    intro v hv
    rw [mem_fixed_iff] at hv ⊢
    exact fun h hh => hv h (hle hh)
  haveI : FiniteDimensional ℂ (fixed ρ K₀) := Submodule.finiteDimensional_of_le hVle
  have h'' : ∀ v ∈ fixed ρ K'', levOp ρ K K'' F LinearMap.id v ∈ fixed ρ K'' :=
    fun v hv => levOp_mem_fixed ρ K K₀ K'' F hF hK''o hle v hv
  have h0 : ∀ v ∈ fixed ρ K₀, levOp ρ K K₀ F LinearMap.id v ∈ fixed ρ K₀ :=
    fun v hv => levOp_mem_fixed ρ K K₀ K₀ F hF hK₀o le_rfl v hv
  unfold twTr
  rw [dite_eq_left h'', dite_eq_left h0]
  let Pr : fixed ρ K'' →ₗ[ℂ] fixed ρ K₀ :=
    (P.domRestrict (fixed ρ K'')).codRestrict (fixed ρ K₀) (fun v => hPfix v.1 v.2)
  let ι : fixed ρ K₀ →ₗ[ℂ] fixed ρ K'' := Submodule.inclusion hVle
  have h1 : (levOp ρ K K'' F LinearMap.id).restrict h'' =
      ι ∘ₗ (((levOp ρ K K₀ F LinearMap.id).restrict h0) ∘ₗ Pr) := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    show levOp ρ K K'' F LinearMap.id v = levOp ρ K K₀ F LinearMap.id (P v)
    exact key v v.2
  have h2 : Pr ∘ₗ ι = LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    show P v = v
    exact hPid v v.2
  rw [h1, LinearMap.trace_comp_comm', LinearMap.comp_assoc, h2, LinearMap.comp_id]

end GlobalTheory.TraceLevel
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.BCT.ConjugationGramUnitary

open Formalism.UG

theorem negOne_zpow_ordL_mul {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L)
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (a x : L) (ha : a ≠ 0) :
    (-1 : ℂ) ^ ordL (σ a * a * x) = (-1 : ℂ) ^ ordL x := by
  have key : ∀ (y : L) (m : ℤ), Valued.v y = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
      ordL y = m := by
    intro y m h
    have hne : Valued.v y ≠ 0 := by rw [h]; exact WithZero.coe_ne_zero
    unfold ordL
    rw [dite_eq_right hne]
    have e : ((WithZero.unzero hne : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = Multiplicative.ofAdd (-m) := by
      rw [WithZero.coe_unzero, h]
    rw [WithZero.coe_inj.mp e]
    simp
  have spec : ∀ y : L, y ≠ 0 → Valued.v y = ((Multiplicative.ofAdd (-(ordL y)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro y hy
    have hne : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
    unfold ordL
    rw [dite_eq_right hne]
    simp
  by_cases hx : x = 0
  · simp [hx]
  have h1 : ordL (σ a * a * x) = 2 * ordL a + ordL x := by
    apply key
    rw [map_mul, map_mul, hσ, spec a ha, spec x hx]
    rw [← WithZero.coe_mul, ← WithZero.coe_mul]
    congr 1
    rw [← ofAdd_add, ← ofAdd_add]
    congr 1
    ring
  rw [h1, zpow_add₀ (by norm_num), Even.neg_one_zpow (even_two_mul _), one_mul]

def gram {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {ι : Type} (v : ι → (Fin n → K)) : Matrix ι ι K :=
  Matrix.of fun i j => ∑ k, σ (v i k) * v j k

theorem gram_basis {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (V : Submodule K (Fin n → K)) {ι : Type} [Fintype ι]
    [DecidableEq ι] (b c : Module.Basis ι K V) :
    gram σ (fun i => (c i : Fin n → K)) =
      ((b.toMatrix c).map σ)ᵀ * gram σ (fun i => (b i : Fin n → K)) * b.toMatrix c := by
  have hc : ∀ j k, (c j : Fin n → K) k = ∑ l, b.toMatrix c l j * (b l : Fin n → K) k := by
    intro j k
    have := b.sum_toMatrix_smul_self c j
    rw [← this, Submodule.coe_sum, Finset.sum_apply]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  ext i j

  simp only [gram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hc, map_sum, map_mul,
  Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem gram_unitary {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (g : Matrix (Fin n) (Fin n) K)
    (hg : (g.map σ)ᵀ * g = 1) {ι : Type} (v : ι → (Fin n → K)) :
    gram σ (fun i => g *ᵥ v i) = gram σ v := by
  have he : ∀ a b, ∑ k, σ (g k a) * g k b = if a = b then 1 else 0 := by
    intro a b
    have := congrFun (congrFun hg a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hm : ∀ (x : Fin n → K) k, (g *ᵥ x) k = ∑ a, g k a * x a := fun _ _ => rfl
  ext i j

  simp only [gram, Matrix.of_apply, hm, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  have : ∀ y, ∑ k, σ (g k y) * σ (v i y) * (g k a * v j a) = σ (v i y) * v j a * (if y = a then 1 else 0) := by
    intro y
    rw [← he y a, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem aeval_conj {K : Type} [Field K] {n : ℕ} (γ g : GL (Fin n) K) (Q : K[X]) :
    aeval (g⁻¹ * γ * g).val Q = (g⁻¹).val * aeval γ.val Q * g.val := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, Matrix.mul_add, Matrix.add_mul]
  | monomial k a =>
    simp only [aeval_monomial, Units.val_mul]
    have : ((g⁻¹).val * γ.val * g.val) ^ k = (g⁻¹).val * γ.val ^ k * g.val := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ih, pow_succ]
        simp only [Matrix.mul_assoc]
        congr 2
        rw [← Matrix.mul_assoc g.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    rw [this]
    simp [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.BCT.ConjugationGramUnitary

namespace GlobalTheory.BCT

open GlobalTheory.BCT.ConjugationGramUnitary

theorem kapSign_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, Valued.v (cj w x) = Valued.v x) →
    ∀ (Q₁ : (w.adicCompletion E)[X]) (γ g : UL n w), kapSign n w Q₁ (g⁻¹ * γ * g).1 = kapSign n w Q₁ γ.1 := by
  intro E _ _ _ n w hv Q₁ γ g
  unfold kapSign
  split_ifs with hs
  · rfl
  have hg : ((g.1.val).map (cj w))ᵀ * g.1.val = 1 := by
    have h := g.2
    simp only [UL, hs, if_false] at h
    have h2 : Formalism.UG.cT (cj w) (g.1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 * (g.1 : Matrix (Fin n) (Fin n) _) = 1 := h
    simpa [Formalism.UG.cT] using h2
  have hinv : ((g.1)⁻¹).val * g.1.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hinv' : g.1.val * ((g.1)⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hM : aeval ((g⁻¹ * γ * g).1).val Q₁ = ((g.1)⁻¹).val * aeval γ.1.val Q₁ * g.1.val := by
    have : (g⁻¹ * γ * g).1 = g.1⁻¹ * γ.1 * g.1 := by simp
    rw [this]
    exact aeval_conj _ _ _
  dsimp only
  let V := LinearMap.ker (Matrix.toLin' (aeval γ.1.val Q₁))
  let V' := LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : UL n w) : GLw n w).val Q₁))
  have hmem : ∀ x, x ∈ V' ↔ g.1.val *ᵥ x ∈ V := by
    intro x
    simp only [V, V', LinearMap.mem_ker, Matrix.toLin'_apply]
    rw [hM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    constructor
    · intro h
      have := congrArg (g.1.val *ᵥ ·) h
      simpa [Matrix.mulVec_mulVec, hinv'] using this
    · intro h
      rw [h, Matrix.mulVec_zero]
  have hinj : Function.Injective (Matrix.toLin' g.1.val) := by
    intro x y h
    have := congrArg (((g.1)⁻¹).val *ᵥ ·) h
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hinv] using this
  have hmap : V'.map (Matrix.toLin' g.1.val) = V := by
    ext x
    simp only [Submodule.mem_map, Matrix.toLin'_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem y).mp hy
    · intro hx
      refine ⟨((g.1)⁻¹).val *ᵥ x, ?_, ?_⟩
      · rw [hmem, Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
        exact hx
      · rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
  let e : V' ≃ₗ[w.adicCompletion E] V :=
    (Submodule.equivMapOfInjective _ hinj V').trans (LinearEquiv.ofEq _ _ hmap)
  let b := Module.finBasis (w.adicCompletion E) V
  let b' := Module.finBasis (w.adicCompletion E) V'
  let c₀ := b'.map e
  let c := c₀.reindex (b.indexEquiv c₀).symm
  have hc₀ : ∀ i, (c₀ i : Fin n → w.adicCompletion E) = g.1.val *ᵥ (b' i : Fin n → w.adicCompletion E) := by
    intro i
    rfl
  have h1 : gram (cj w) (fun i => (b' i : Fin n → w.adicCompletion E)) =
      gram (cj w) (fun i => (c₀ i : Fin n → w.adicCompletion E)) := by
    simp only [hc₀]
    exact (gram_unitary (cj w) _ hg _).symm
  have h2 : (gram (cj w) (fun i => (c₀ i : Fin n → w.adicCompletion E))).det =
      (gram (cj w) (fun i => (c i : Fin n → w.adicCompletion E))).det := by
    have : gram (cj w) (fun i => (c i : Fin n → w.adicCompletion E)) =
        (gram (cj w) (fun i => (c₀ i : Fin n → w.adicCompletion E))).submatrix (b.indexEquiv c₀) (b.indexEquiv c₀) := by
      ext i j
      simp [ConjugationGramUnitary.gram, c, Module.Basis.reindex_apply]
    rw [this, Matrix.det_submatrix_equiv_self]
  let A := b.toMatrix c
  have hA : A.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse (b.toMatrix_mul_toMatrix_flip c)
  have h3 : (gram (cj w) (fun i => (c i : Fin n → w.adicCompletion E))).det =
      cj w A.det * A.det * (gram (cj w) (fun i => (b i : Fin n → w.adicCompletion E))).det := by
    have hd : ((b.toMatrix c).map (cj w)).det = cj w A.det := by rw [RingHom.map_det]; rfl
    rw [gram_basis (cj w) V b c, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hd]
    ring
  change (-1 : ℂ) ^ Formalism.UG.ordL (gram (cj w) (fun i => (b' i : Fin n → w.adicCompletion E))).det =
    (-1 : ℂ) ^ Formalism.UG.ordL (gram (cj w) (fun i => (b i : Fin n → w.adicCompletion E))).det
  rw [h1, h2, h3]
  exact negOne_zpow_ordL_mul (cj w) hv _ _ hA

end GlobalTheory.BCT
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem monic_dvd_integral_factor_bezout : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (P₀ : (w.adicCompletionIntegers E)[X]), P₀.Monic →
    IsCoprime P₀ (derivative P₀) → ∀ Q₁ : (w.adicCompletion E)[X],
    Q₁ ∣ P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∃ (Q₁₀ Q₂₀ A B : (w.adicCompletionIntegers E)[X]) (c : w.adicCompletion E), c ≠ 0 ∧ P₀ = Q₁₀ * Q₂₀ ∧
      A * Q₁₀ + B * Q₂₀ = 1 ∧ Q₁ = C c * Q₁₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
  intro E _ _ w P₀ hP hc Q₁ hQ
  have hinj : Function.Injective (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := IsFractionRing.injective (w.adicCompletionIntegers E) (w.adicCompletion E)
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (w.adicCompletion E) hP hQ
  have hPm : (P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))).Monic := hP.map _
  have hQ0 : Q₁ ≠ 0 := by
    rintro rfl
    exact hPm.ne_zero (zero_dvd_iff.mp hQ)
  have hlc : Q₁.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ0
  have hgm' : g.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = Q₁ * C Q₁.leadingCoeff⁻¹ := by
    calc _ = g.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) * C Q₁.leadingCoeff * C Q₁.leadingCoeff⁻¹ := by
          rw [mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, mul_one]
      _ = Q₁ * C Q₁.leadingCoeff⁻¹ := by rw [hg]
  have hgmon : g.Monic := by
    apply Polynomial.monic_of_injective hinj
    rw [hgm']
    exact monic_mul_leadingCoeff_inv hQ0
  have hdvd : g ∣ P₀ := by
    rw [← map_dvd_map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) hinj hgmon]
    exact dvd_trans ⟨C Q₁.leadingCoeff, hg.symm⟩ hQ
  obtain ⟨Q₂, hQ₂⟩ := hdvd
  obtain ⟨a, b, hab⟩ := hc
  refine ⟨g, Q₂, a * Q₂ + b * derivative Q₂, b * derivative g, Q₁.leadingCoeff, hlc, hQ₂, ?_, ?_⟩
  · rw [hQ₂, derivative_mul] at hab
    linear_combination hab
  · exact hg.symm.trans (mul_comm _ _)

end GlobalTheory
end

end

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.dvd_integral_monic_coprime_derivative_bezout_factor : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (P₀ : (w.adicCompletionIntegers E)[X]), P₀.Monic →
    IsCoprime P₀ (derivative P₀) → ∀ Q₁ : (w.adicCompletion E)[X],
    Q₁ ∣ P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∃ (Q₁₀ Q₂₀ A B : (w.adicCompletionIntegers E)[X]) (c : w.adicCompletion E), c ≠ 0 ∧ P₀ = Q₁₀ * Q₂₀ ∧
      A * Q₁₀ + B * Q₂₀ = 1 ∧ Q₁ = C c * Q₁₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
  first | exact @GlobalTheory.monic_dvd_integral_factor_bezout | exact GlobalTheory.monic_dvd_integral_factor_bezout | (intros; apply GlobalTheory.monic_dvd_integral_factor_bezout <;> assumption)

end
end

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.localSign_kernel_charFactor_conj_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, Valued.v (cj w x) = Valued.v x) →
    ∀ (Q₁ : (w.adicCompletion E)[X]) (γ g : UL n w), kapSign n w Q₁ (g⁻¹ * γ * g).1 = kapSign n w Q₁ γ.1 := by
  first | exact @GlobalTheory.BCT.kapSign_conj | exact GlobalTheory.BCT.kapSign_conj | (intros; apply GlobalTheory.BCT.kapSign_conj <;> assumption)

end
end
