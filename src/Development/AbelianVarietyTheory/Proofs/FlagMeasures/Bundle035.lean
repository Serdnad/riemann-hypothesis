module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle011
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardQuotPow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle025
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
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
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem exists_fg_span_stable_of_unipotent {E : Type} [CommRing E] (O : Subring E) {n : ℕ}
    (g : (Fin n → E) →ₗ[E] (Fin n → E)) (e : ℕ) (hg : (g - 1) ^ e = 0) :
    ∃ Λ : Submodule O (Fin n → E), Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧
      (∀ v ∈ Λ, g v ∈ Λ) ∧ ∀ v ∈ Λ, ∃ w ∈ Λ, g w = v := by
  set x : (Fin n → E) →ₗ[E] (Fin n → E) := 1 - g with hx
  have hxe : x ^ e = 0 := by
    have : x = -(g - 1) := by rw [hx, neg_sub]
    rw [this, neg_pow, hg, mul_zero]
  let s : Set (Fin n → E) :=
    Set.range fun p : Fin (e + 1) × Fin n => (x ^ (p.1 : ℕ)) (Pi.single p.2 1)
  have hall : ∀ (i : ℕ) (j : Fin n), (x ^ i) (Pi.single j 1) ∈ Submodule.span O s := by
    intro i j
    by_cases hi : i < e + 1
    · exact Submodule.subset_span ⟨(⟨i, hi⟩, j), rfl⟩
    · have : x ^ i = 0 := pow_eq_zero_of_le (by omega) hxe
      rw [this]
      exact Submodule.zero_mem _
  have hpow : ∀ (k : ℕ), ∀ v ∈ Submodule.span O s, (x ^ k) v ∈ Submodule.span O s := by
    intro k v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, rfl⟩ := hy
      have := hall (k + p.1) p.2
      rwa [pow_add, Module.End.mul_apply] at this
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have : (x ^ k) (c • a) = c • (x ^ k) a := (x ^ k).map_smul (c : E) a
      rw [this]
      exact Submodule.smul_mem _ c ha
  refine ⟨Submodule.span O s, Submodule.fg_span (Set.finite_range _), ?_, ?_, ?_⟩
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    have := hall 0 j
    simpa using this
  · intro v hv
    have h1 := hpow 1 v hv
    have h2 : g v = v - (x ^ 1) v := by simp [hx]
    rw [h2]
    exact Submodule.sub_mem _ hv h1
  · intro v hv
    refine ⟨(∑ i ∈ Finset.range e, x ^ i) v, ?_, ?_⟩
    · rw [LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun i _ => hpow i v hv
    · have h := mul_neg_geom_sum x e
      have h1 : 1 - x = g := by rw [hx, sub_sub_cancel]
      rw [h1, hxe, sub_zero] at h
      rw [← Module.End.mul_apply, h, Module.End.one_apply]

theorem exists_isLat_stabL_of_unipotent : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (g : ((Fin n → E) ≃ₗ[E] (Fin n → E))) (e : ℕ), (((g : (Fin n → E) →ₗ[E] (Fin n → E)) - 1) ^ e = 0) → ∃ Λ : Submodule L.O (Fin n → E), IsLat L Λ ∧ g ∈ stabL L Λ := by
  intro F _ _ _ _ _ E _ _ _ L n g e hg
  obtain ⟨Λ, h1, h2, h3, h4⟩ := exists_fg_span_stable_of_unipotent L.O _ e hg
  refine ⟨Λ, ⟨h1, h2⟩, ?_⟩
  rw [MulAction.mem_stabilizer_iff]
  ext v
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact h3 w hw
  · intro hv
    obtain ⟨w, hw, h⟩ := h4 v hv
    exact ⟨w, hw, h⟩

end GlobalTheory.HL
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.OrbMono

theorem orbSum_eq (G α : Type) [Group G] [MulAction G α] (X : Set α) (N : α → ℝ≥0∞) :
    orbSum G X N = ∑' q : MulAction.orbitRel.Quotient G α,
      if Quotient.out q ∈ X then
        ((ENat.card (MulAction.stabilizer G (Quotient.out q)) : ℕ∞) : ℝ≥0∞)⁻¹ * N (Quotient.out q)
      else 0 := by
  exact (tsum_subtype {q : MulAction.orbitRel.Quotient G α | Quotient.out q ∈ X}
    (fun q => ((ENat.card (MulAction.stabilizer G (Quotient.out q)) : ℕ∞) : ℝ≥0∞)⁻¹ *
      N (Quotient.out q))).trans (tsum_congr fun q => by simp [Set.indicator_apply])

theorem main : ∀ (G α : Type) [Group G] [MulAction G α] , (∀ (X Y : Set α) (N N' : α → ℝ≥0∞), X ⊆ Y → (∀ x ∈ X, N x ≤ N' x) → orbSum G X N ≤ orbSum G Y N') ∧ (∀ (X : Set α) (B : ℝ≥0∞), orbSum G X (fun _ => B) = B * orbMass G X) ∧ (∀ (ι : Type) (s : Finset ι) (X : Set α) (Xi : ι → Set α) (N : α → ℝ≥0∞), X ⊆ ⋃ i ∈ s, Xi i → orbSum G X N ≤ ∑ i ∈ s, orbSum G (Xi i) N) ∧ (∀ (X : Set α) (s : Set α), (∀ x ∈ X, ∃ y ∈ s, ∃ g : G, g • y = x) → orbMass G X ≤ ((s.encard : ℕ∞) : ℝ≥0∞)) ∧ (∀ (X : Set α) (N N' : α → ℝ≥0∞), orbSum G X (fun x => N x + N' x) = orbSum G X N + orbSum G X N') := by
  intro G α _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X Y N N' hXY hN
    simp only [orbSum_eq]
    refine ENNReal.tsum_le_tsum fun q => ?_
    by_cases hq : Quotient.out q ∈ X
    · rw [if_pos hq, if_pos (hXY hq)]
      gcongr
      exact hN _ hq
    · rw [if_neg hq]
      exact zero_le
  · intro X B
    simp only [orbMass, orbSum]
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun q => by rw [mul_one, mul_comm]
  · intro ι s X Xi N hX
    simp only [orbSum_eq]
    rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
    refine ENNReal.tsum_le_tsum fun q => ?_
    by_cases hq : Quotient.out q ∈ X
    · obtain ⟨i, hi, hqi⟩ := Set.mem_iUnion₂.1 (hX hq)
      refine le_trans ?_ (Finset.single_le_sum (fun j _ => zero_le) hi)
      simp [hq, hqi]
    · rw [if_neg hq]
      exact zero_le
  · intro X s hs
    have key : ∀ q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
        ∃ y : s, (Quotient.mk _ (y : α) : MulAction.orbitRel.Quotient G α) = q.1 := by
      rintro ⟨q, hq⟩
      obtain ⟨y, hy, g, hg⟩ := hs _ hq
      refine ⟨⟨y, hy⟩, ?_⟩
      exact (Quotient.sound (MulAction.orbitRel_apply.2 ⟨g⁻¹, by simp [← hg]⟩)).trans
        (Quotient.out_eq q)
    choose φ hφ using key
    have hinj : Function.Injective φ := by
      intro a b h
      apply Subtype.ext
      rw [← hφ a, ← hφ b, h]
    calc orbMass G X
        = ∑' q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
            ((ENat.card (MulAction.stabilizer G (Quotient.out q.1)) : ℕ∞) : ℝ≥0∞)⁻¹ * 1 := rfl
      _ ≤ ∑' q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
            (fun _ : s => (1 : ℝ≥0∞)) (φ q) := by
          refine ENNReal.tsum_le_tsum fun q => ?_
          rw [mul_one]
          apply ENNReal.inv_le_one.2
          have h1 : (1 : ℕ∞) ≤ ENat.card (MulAction.stabilizer G (Quotient.out q.1)) :=
            (ENat.one_le_card_iff_nonempty _).2 ⟨1⟩
          exact_mod_cast h1
      _ ≤ ∑' _ : s, (1 : ℝ≥0∞) := (by refine' _root_.le_trans _ (_root_.tsum_comp_le_tsum_of_injective hinj _); exact _root_.le_rfl)
      _ = s.encard := ENNReal.tsum_set_one s
  · intro X N N'
    simp only [orbSum]
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun q => mul_add _ _ _

end GlobalTheory.Mass.OrbMono
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LatDet

theorem card_quot_pow {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {p : R}
    (hp : Irreducible p) (k : ℕ) :
    Nat.card (R ⧸ Ideal.span {p ^ k}) = Nat.card (R ⧸ Ideal.span {p}) ^ k := by
  haveI : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime
  have hq := cardQuot_pow_of_prime (P := Ideal.span {p})
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hp.ne_zero) (i := k)
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply, Ideal.span_singleton_pow] at hq
  exact hq


open Module Submodule in
theorem card_coker {R M ι : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] [Fintype ι] (b : Basis ι R M) {p : R} (hp : Irreducible p)
    (φ : M →ₗ[R] M) (hφ : Function.Injective φ) :
    ∃ m : ℕ, Associated (LinearMap.det φ) (p ^ m) ∧
      Nat.card (M ⧸ LinearMap.range φ) = Nat.card (R ⧸ Ideal.span {p}) ^ m :=
  _root_.GlobalTheory.CardQuotientPow.main b hp φ hφ

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem resQ_ne_zero {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) : resQ ϖ ≠ 0 := by
  unfold resQ
  rw [← hϖ.maximalIdeal_eq]
  haveI : Finite (𝒪[F] ⧸ IsLocalRing.maximalIdeal 𝒪[F]) := inferInstanceAs (Finite 𝓀[F])
  exact Nat.card_pos.ne'

theorem relIndex_map {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {W : Type} [AddCommGroup W] [Module F W]
    {ι : Type} [Fintype ι] (b : Module.Basis ι F W) (ψ : W →ₗ[F] W) (a : ℤ) (u : (𝒪[F])ˣ)
    (hd : LinearMap.det ψ = (ϖ : F) ^ a * ((u : 𝒪[F]) : F)) (W0 : AddSubgroup W)
    (hW : ∀ x, x ∈ W0 ↔ ∀ i, b.repr x i ∈ 𝒪[F]) (hψ : ∀ i j, b.repr (ψ (b j)) i ∈ 𝒪[F]) :
    ∃ m : ℕ, a = m ∧ (W0.map ψ.toAddMonoidHom).relIndex W0 = resQ ϖ ^ m :=
  _root_.UpperTheory.Reformulated.B.Yzb5.relIndex_map hϖ b ψ a u hd W0 hW hψ

theorem relVol_map : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {W : Type} [AddCommGroup W] [Module F W] {ι : Type} [Fintype ι] (b : Module.Basis ι F W) (φ : W ≃ₗ[F] W) (a : ℤ) (u : (𝒪[F])ˣ), LinearMap.det (φ : W →ₗ[F] W) = (ϖ : F) ^ a * ((u : 𝒪[F]) : F) → ∀ W0 : AddSubgroup W, (∀ x, x ∈ W0 ↔ ∀ i, b.repr x i ∈ 𝒪[F]) → (W0.map φ.toAddEquiv.toAddMonoidHom).relIndex W0 ≠ 0 ∧ W0.relIndex (W0.map φ.toAddEquiv.toAddMonoidHom) ≠ 0 ∧ relVol W0 (W0.map φ.toAddEquiv.toAddMonoidHom) = (resQ ϖ : ℝ) ^ (-a) := by
  intro F _ _ _ _ ϖ hϖ W _ _ ι _ b φ a u hd W0 hW
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hq := resQ_ne_zero hϖ
  haveI := Module.Finite.of_basis b
  haveI := Module.Free.of_basis b
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors 𝒪[F])
    (fun ij : ι × ι => b.repr (φ (b ij.2)) ij.1)
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (nonZeroDivisors.ne_zero c.2) hϖ
  set d := Module.finrank F W
  set t : F := (ϖ : F) ^ n with ht
  have htO : t ∈ 𝒪[F] := pow_mem ϖ.2 n
  have h1 : ∀ i j, b.repr ((t • (φ : W →ₗ[F] W)) (b j)) i ∈ 𝒪[F] := by
    intro i j
    obtain ⟨y, hy⟩ := hc (i, j)
    have e1 : t = ((v : 𝒪[F]) : F) * ((c : 𝒪[F]) : F) := by
      rw [ht, mul_comm]; exact_mod_cast congrArg (fun x : 𝒪[F] => (x : F)) hv.symm
    have e2 : b.repr ((t • (φ : W →ₗ[F] W)) (b j)) i = ((v : 𝒪[F]) : F) * (y : F) := by
      have hy' : (y : F) = ((c : 𝒪[F]) : F) * b.repr (φ (b j)) i := hy
      rw [hy', ← mul_assoc, ← e1]
      simp
    rw [e2]
    exact mul_mem (v : 𝒪[F]).2 y.2
  have h2 : ∀ i j, b.repr ((t • (LinearMap.id : W →ₗ[F] W)) (b j)) i ∈ 𝒪[F] := by
    intro i j
    simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    split_ifs
    · simpa using htO
    · simp
  obtain ⟨m1, hm1, i1⟩ := relIndex_map hϖ b _ (n * d + a) u (by
    rw [LinearMap.det_smul, hd, zpow_add₀ h0, ht, ← pow_mul, ← zpow_natCast, mul_assoc]
    push_cast; rfl) W0 hW h1
  obtain ⟨m2, hm2, i2⟩ := relIndex_map hϖ b _ (n * d) 1 (by
    rw [LinearMap.det_smul, LinearMap.det_id, ht, ← pow_mul, ← zpow_natCast]
    push_cast; rfl) W0 hW h2
  set A := W0.map φ.toAddEquiv.toAddMonoidHom with hA
  set B := W0.map (t • (φ : W →ₗ[F] W)).toAddMonoidHom with hB
  have hBe : B = (W0.map (t • (LinearMap.id : W →ₗ[F] W)).toAddMonoidHom).map
      φ.toAddEquiv.toAddMonoidHom := by
    rw [hB, AddSubgroup.map_map]
    congr 1
    ext x
    simp
  have i3 : B.relIndex A = resQ ϖ ^ m2 := by
    rw [hBe, hA, AddSubgroup.relIndex_map_map_of_injective _ _ φ.injective, i2]
  have hle : ∀ ψ : W →ₗ[F] W, (∀ i j, b.repr (ψ (b j)) i ∈ 𝒪[F]) →
      W0.map ψ.toAddMonoidHom ≤ W0 := by
    rintro ψ hψ _ ⟨x, hx, rfl⟩
    rw [hW]
    intro i
    have : b.repr (ψ.toAddMonoidHom x) i = ∑ j, b.repr x j * b.repr (ψ (b j)) i := by
      change b.repr (ψ x) i = _

      conv_lhs => rw [← b.sum_repr x, map_sum, map_sum, Finsupp.finsetSum_apply]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [this]
    exact sum_mem fun j _ => mul_mem ((hW x).1 hx j) (hψ i j)
  have hBW : B ≤ W0 := hle _ h1
  have hBA : B ≤ A := by
    rw [hBe, hA]; exact AddSubgroup.map_mono (hle _ h2)
  have t1 := AddSubgroup.relIndex_mul_relIndex B (A ⊓ W0) W0 (le_inf hBA hBW) inf_le_right
  have t2 := AddSubgroup.relIndex_mul_relIndex B (A ⊓ W0) A (le_inf hBA hBW) inf_le_left
  rw [AddSubgroup.inf_relIndex_right, i1] at t1
  rw [AddSubgroup.inf_relIndex_left, i3] at t2
  have n1 := mul_ne_zero_iff.1 (t1 ▸ pow_ne_zero m1 hq)
  have n2 := mul_ne_zero_iff.1 (t2 ▸ pow_ne_zero m2 hq)
  refine ⟨n1.2, n2.2, ?_⟩
  have hq' : (resQ ϖ : ℝ) ≠ 0 := by exact_mod_cast hq
  have c0 : (B.relIndex (A ⊓ W0) : ℝ) ≠ 0 := by exact_mod_cast n1.1
  have t1' : (B.relIndex (A ⊓ W0) : ℝ) * A.relIndex W0 = (resQ ϖ : ℝ) ^ m1 := by exact_mod_cast t1
  have t2' : (B.relIndex (A ⊓ W0) : ℝ) * W0.relIndex A = (resQ ϖ : ℝ) ^ m2 := by exact_mod_cast t2
  have ea : -a = (m2 : ℤ) - m1 := by omega
  unfold relVol
  rw [ea, zpow_sub₀ hq', zpow_natCast, zpow_natCast, ← t1', ← t2', mul_div_mul_left _ _ c0]

end GlobalTheory.HL.LatDet
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.LatComm

theorem finite_between {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (c : R)
    [Finite (R ⧸ Ideal.span {c})] (Λ : Submodule R V) (hΛ : Λ.FG) :
    {M : Submodule R V | M ≤ Λ ∧ ∀ v ∈ Λ, c • v ∈ M}.Finite := by
  have hfg : (⊤ : Submodule R Λ).FG := (Submodule.fg_top Λ).2 hΛ
  have hf : Finite (Λ ⧸ (Ideal.span {c}) • (⊤ : Submodule R Λ)) :=
    Submodule.finite_quotient_smul _ hfg
  have hs : Finite (Submodule R (Λ ⧸ (Ideal.span {c}) • (⊤ : Submodule R Λ))) :=
    Finite.of_injective _ SetLike.coe_injective
  have key : ∀ M : Submodule R V, (M ≤ Λ ∧ ∀ v ∈ Λ, c • v ∈ M) →
      (((M.comap Λ.subtype).map ((Ideal.span {c}) • (⊤ : Submodule R Λ)).mkQ).comap
        ((Ideal.span {c}) • (⊤ : Submodule R Λ)).mkQ).map Λ.subtype = M := by
    intro M hM
    have h1 : (Ideal.span {c}) • (⊤ : Submodule R Λ) ≤ M.comap Λ.subtype := by
      rw [Submodule.smul_le]
      intro r hr v _
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      rw [mul_smul]
      exact Submodule.smul_mem _ _ (hM.2 v v.2)
    rw [Submodule.comap_map_mkQ, sup_eq_right.2 h1, Submodule.map_comap_subtype,
      inf_eq_right.2 hM.1]
  refine Set.Finite.of_finite_image (f := fun M : Submodule R V =>
    (M.comap Λ.subtype).map ((Ideal.span {c}) • (⊤ : Submodule R Λ)).mkQ) (Set.toFinite _) ?_
  intro M hM N hN h
  rw [← key M hM, ← key N hN]
  simp only at h
  rw [h]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_pow_smul_mem (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (p : L.O)
    (hp : (p : E) = algebraMap F E (ϖ : F)) {n : ℕ}
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (v : Fin n → E) :
    ∃ j : ℕ, p ^ j • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.PowMulMemOrder.main
  | exact _root_.GlobalTheory.PowMulMemOrder.main
  | (apply _root_.GlobalTheory.PowMulMemOrder.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowMulMemOrder.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowMulMemOrder.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowMulMemOrder.main ..)

theorem exists_pow_smul_le (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (p : L.O)
    (hp : (p : E) = algebraMap F E (ϖ : F)) {n : ℕ}
    {Λ Λ' : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (hΛ' : Λ'.FG) :
    ∃ j : ℕ, ∀ v ∈ Λ', p ^ j • v ∈ Λ := by
  obtain ⟨s, rfl⟩ := hΛ'
  choose f hf using exists_pow_smul_mem L hϖ p hp hΛ
  refine ⟨s.sup f, fun v hv => ?_⟩
  have : Submodule.span L.O (s : Set (Fin n → E)) ≤
      Λ.comap (LinearMap.lsmul L.O (Fin n → E) (p ^ s.sup f)) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := f) hx)
    show p ^ s.sup f • x ∈ Λ
    rw [hk, pow_add, mul_smul]
    exact Λ.smul_mem _ (hf x)
  exact this hv

theorem stab_commensurable : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Λ Λ' : Submodule L.O (Fin n → E)), IsLat L Λ → IsLat L Λ' → ∀ H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), (H ⊓ stabL L Λ').relIndex (H ⊓ stabL L Λ) ≠ 0 ∧ ∀ g : ((Fin n → E) ≃ₗ[E] (Fin n → E)), IsLat L (g • Λ) ∧ stabL L (g • Λ) = MulAut.conj g • stabL L Λ := by
  intro F _ _ _ _ _ E _ _ _ L n Λ Λ' hΛ hΛ' H
  refine ⟨?_, fun g => ⟨⟨?_, ?_⟩, ?_⟩⟩
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    obtain ⟨-, -, -, -, hO, hcard, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
    let p : L.O := ⟨algebraMap F E (ϖ : F), (hO _).2 ϖ.2⟩
    have hp : (p : E) = algebraMap F E (ϖ : F) := rfl
    obtain ⟨a, ha⟩ := exists_pow_smul_le L hϖ p hp hΛ hΛ'.1
    obtain ⟨b, hb⟩ := exists_pow_smul_le L hϖ p hp hΛ' hΛ.1
    have hfin : Finite (L.O ⧸ Ideal.span {p ^ (a + b)}) := by
      have h1 := hcard (a + b)
      have h2 : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ (a + b))} = {p ^ (a + b)} := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Subtype.ext_iff,
          SubmonoidClass.coe_pow, hp, map_pow]
      rw [h2] at h1
      apply Nat.finite_of_card_ne_zero
      rw [h1]
      exact pow_ne_zero _ (by omega)
    have hF := finite_between (p ^ (a + b)) Λ hΛ.1
    have hu : IsUnit ((p ^ a : L.O) : E) := by
      rw [SubmonoidClass.coe_pow, hp]
      exact ((IsUnit.mk0 _ (fun h => hϖ.ne_zero (Subtype.ext h))).map (algebraMap F E)).pow a
    have hinj : Function.Injective (LinearMap.lsmul L.O (Fin n → E) (p ^ a)) := by
      intro x y h
      exact hu.smul_left_cancel.1 h
    have hcomm : ∀ (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (r : L.O) (v : Fin n → E),
        g • (r • v) = r • (g • v) := fun g r v => map_smul g (r : E) v
    have heq : (H ⊓ stabL L Λ').subgroupOf (H ⊓ stabL L Λ) =
        MulAction.stabilizer (H ⊓ stabL L Λ :) Λ' := by
      ext g
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
      exact ⟨fun h => h.2, fun h => ⟨g.2.1, h⟩⟩
    rw [Subgroup.relIndex, heq, MulAction.index_stabilizer]
    refine Set.ncard_ne_zero_of_mem (MulAction.mem_orbit_self Λ') ?_
    refine Set.Finite.of_finite_image
      (f := fun M => Submodule.map (LinearMap.lsmul L.O (Fin n → E) (p ^ a)) M) (hF.subset ?_)
      (Submodule.map_injective_of_injective hinj).injOn
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have hg : g.1 • Λ = Λ := g.2.2
    refine ⟨?_, fun v hv => ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists w g.1 Λ').1 hw
      show p ^ a • (g.1 • x) ∈ Λ
      rw [← hcomm]
      exact hg.le (Submodule.smul_mem_pointwise_smul _ _ _ (ha x hx))
    · rw [← hg] at hv
      obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists v g.1 Λ).1 hv
      refine ⟨g.1 • (p ^ b • x), Submodule.smul_mem_pointwise_smul _ g.1 _ (hb x hx), ?_⟩
      rw [LinearMap.lsmul_apply, hcomm, pow_add, mul_smul]
  · exact hΛ.1.map _
  · rw [eq_top_iff]
    intro v _
    have hv : g.symm v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
    have h2 := Submodule.apply_mem_span_image_of_mem_span (g : (Fin n → E) →ₗ[E] (Fin n → E)) hv
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.smul_mem_pointwise_smul _ g _ hx
  · exact MulAction.stabilizer_smul_eq_stabilizer_map_conj g Λ

end GlobalTheory.LatComm
end

section

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc

namespace GlobalTheory.HL.StdPlace

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

def coordLat {L : LocE F E} {r k : ℕ} (S : Frames L r k) : Submodule L.O S.V :=
  Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V))

structure Good {L : LocE F E} {r k : ℕ} (S : Frames L r k) : Prop where
  gg : S.gg = false
  Hm_int : IsIntM L S.Hm
  Hm_unit : ∃ y ∈ L.O, S.Hm.det * y = 1
  f_int : ∀ a i, S.f a i ∈ L.O
  f'_int : ∀ a i, S.f' a i ∈ L.O
  es_int : ∀ a i, S.es a i ∈ L.O
  es'_int : ∀ a i, S.es' a i ∈ L.O
  G_unit : S.G ∈ L.O ∧ ∃ y ∈ L.O, S.G * y = 1
  D_unit : ∀ l, S.D l ≠ 0 → S.D l ∈ L.O ∧ ∃ y ∈ L.O, S.D l * y = 1

end GlobalTheory.HL.StdPlace
end
end
