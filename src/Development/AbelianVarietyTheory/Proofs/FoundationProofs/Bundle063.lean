module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle029
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem kaehler_D_of_pow_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (a b : S) (m : ℕ) (h : a ^ m = b) :
    a • KaehlerDifferential.D R S b = ((m : S) * b) • KaehlerDifferential.D R S a := by
  subst h
  rw [Derivation.leibniz_pow]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [smul_comm a, ← Nat.cast_smul_eq_nsmul S, smul_smul, smul_smul]
    congr 1
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    ring

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zS_pow (T : Tower p Ω) (n k : ℕ) : zS T (n + k) ^ (p ^ k) = zS T n := by
  induction k with
  | zero => simp
  | succ k ih =>
    apply Subtype.ext
    have h1 : (zS T (n + (k + 1)) : Ω) ^ p = (zS T (n + k) : Ω) := T.ζpow (n + k)
    have h2 : (zS T (n + k) : Ω) ^ (p ^ k) = (zS T n : Ω) := congrArg Subtype.val ih
    simp only [SubmonoidClass.coe_pow]
    rw [pow_succ', pow_mul, h1, h2]

theorem qS_pow (T : Tower p Ω) (n k : ℕ) : qS T (n + k) ^ (p ^ k) = qS T n := by
  induction k with
  | zero => simp
  | succ k ih =>
    apply Subtype.ext
    have h1 : (qS T (n + (k + 1)) : Ω) ^ p = (qS T (n + k) : Ω) := T.qpow (n + k)
    have h2 : (qS T (n + k) : Ω) ^ (p ^ k) = (qS T n : Ω) := congrArg Subtype.val ih
    simp only [SubmonoidClass.coe_pow]
    rw [pow_succ', pow_mul, h1, h2]

theorem dlog_transition : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω) (n k : ℕ), zS T (n + k) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T n) = ((p : (integralClosure (O0 p) Ω)) ^ k * zS T n) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T (n + k)) ∧ qS T (n + k) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T n) = ((p : (integralClosure (O0 p) Ω)) ^ k * qS T n) • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T (n + k)) := by
  intro p _ Ω _ _ T n k
  constructor
  · have := kaehler_D_of_pow_eq (R := O0 p) _ _ _ (zS_pow T n k)
    simpa [Nat.cast_pow] using this
  · have := kaehler_D_of_pow_eq (R := O0 p) _ _ _ (qS_pow T n k)
    simpa [Nat.cast_pow] using this

end GlobalTheory.AlmostEt
end

section

noncomputable section

namespace GlobalTheory.AlmostEt

open Finsupp

theorem kerTotal_gen_local {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    (g : S →₀ S)
    (hg : g ∈ ((Set.range fun x : S × S => single x.1 1 + single x.2 1 - single (x.1 + x.2) 1) ∪
        Set.range fun x : S × S => single x.2 x.1 + single x.1 x.2 - single (x.1 * x.2) 1) ∪
      Set.range fun x : A => single (algebraMap A S x) 1) :
    ∃ F : Finset S, ∀ C : Subalgebra A S, (↑F : Set S) ⊆ C →
      ∀ (M : Type) [AddCommGroup M] [Module S M] (D : S → M), IsDerOn C D →
        Finsupp.linearCombination S D g = 0 := by
  classical
  rcases hg with (⟨⟨u, w⟩, rfl⟩ | ⟨⟨u, w⟩, rfl⟩) | ⟨a, rfl⟩
  · refine ⟨{u, w}, fun C hC M _ _ D hD => ?_⟩
    have hu : u ∈ C := hC (by simp)
    have hw : w ∈ C := hC (by simp)
    simp [hD.add u hu w hw]
  · refine ⟨{u, w}, fun C hC M _ _ D hD => ?_⟩
    have hu : u ∈ C := hC (by simp)
    have hw : w ∈ C := hC (by simp)
    simp [hD.mul u hu w hw, add_comm]
  · refine ⟨∅, fun C _ M _ _ D hD => ?_⟩
    simp [hD.alg a]

theorem kaehler_rel_local : ∀ (A S : Type) [CommRing A] [CommRing S] [Algebra A S] (n : ℕ)
    (x y : Fin n → S), ∑ i, x i • KaehlerDifferential.D A S (y i) = 0 →
    ∃ T : Finset S, ∀ C : Subalgebra A S, (↑T : Set S) ⊆ C → (∀ i, y i ∈ C) →
      ∀ (M : Type) [AddCommGroup M] [Module S M] (D : S → M), IsDerOn C D →
        ∑ i, x i • D (y i) = 0 := by
  intro A S _ _ _ n x y h
  classical
  set v : S →₀ S := ∑ i, single (y i) (x i) with hv
  have hlc : ∀ (M : Type) [AddCommGroup M] [Module S M] (D : S → M),
      Finsupp.linearCombination S D v = ∑ i, x i • D (y i) := by
    intro M _ _ D

    simp [hv, map_sum, Finsupp.linearCombination_single]
  have hmem : v ∈ KaehlerDifferential.kerTotal A S := by
    rw [← KaehlerDifferential.kerTotal_eq, LinearMap.mem_ker, hlc, h]
  obtain ⟨G, hGs, hvG⟩ := Submodule.mem_span_finite_of_mem_span hmem
  have key := fun g (hg : g ∈ G) => kerTotal_gen_local (A := A) g (hGs hg)
  choose F hF using key
  refine ⟨G.attach.biUnion (fun g => F g.1 g.2), ?_⟩
  intro C hC _ M _ _ D hD
  rw [← hlc]
  have hle : Submodule.span S (↑G : Set (S →₀ S)) ≤
      LinearMap.ker (Finsupp.linearCombination S D) := by
    rw [Submodule.span_le]
    intro g hg
    refine hF g hg C (fun z hz => hC ?_) M D hD
    simp only [Finset.coe_biUnion, Finset.coe_attach, Set.mem_univ, Set.iUnion_true,
      Set.mem_iUnion]
    exact ⟨⟨g, hg⟩, hz⟩
  exact hle hvG

end GlobalTheory.AlmostEt
end
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.LevelRed


open scoped MatrixGroups TensorProduct in
open Matrix in
theorem _root_.GlobalTheory.KZ.LevelRed.gamma_le_of_dvd {M M0 : ℕ} (h : M ∣ M0) :
    CongruenceSubgroup.Gamma M0 ≤ CongruenceSubgroup.Gamma M := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  have key : ∀ z : ℤ, ((z : ZMod M0).cast : ZMod M) = z := ZMod.cast_intCast h
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← key, h1, ZMod.cast_one h]
  · rw [← key, h2, ZMod.cast_zero]
  · rw [← key, h3, ZMod.cast_zero]
  · rw [← key, h4, ZMod.cast_one h]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

noncomputable abbrev bc (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) : X.Kl l →ₗ[ℤ_[l]] X.Kl l :=
  LinearMap.baseChange ℤ_[l] (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom)))

end GlobalTheory.KZ.LevelRed

namespace GlobalTheory.KZ

open scoped MatrixGroups TensorProduct in
open Matrix in
private lemma exists_level_bc_eq_of_agree_on_level {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
    (X : _root_.GlobalTheory.KZ.Tower Ω ε) (l : ℕ) [Fact l.Prime] (m : X.Kl l) :
    ∃ M0 : ℕ, 0 < M0 ∧ ∀ φ ψ : X.K ≃+* X.K,
      (∀ f : X.K, (∀ γ ∈ CongruenceSubgroup.Gamma M0,
        X.sl (_root_.GlobalTheory.KZ.ofSL γ) f = f) → φ f = ψ f) →
      _root_.GlobalTheory.KZ.LevelRed.bc X l φ m = _root_.GlobalTheory.KZ.LevelRed.bc X l ψ m := by
  induction m using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, fun φ ψ _ => by simp⟩
  | tmul c u =>
    obtain ⟨M, hM, hfix⟩ := X.level ((Additive.toMul u : X.Kˣ) : X.K)
    refine ⟨M, hM, fun φ ψ h => ?_⟩
    have hu : Units.map φ.toMonoidHom (Additive.toMul u) =
        Units.map ψ.toMonoidHom (Additive.toMul u) :=
      Units.ext (by simpa using h _ hfix)
    simp only [LinearMap.baseChange_tmul]
    congr 1
  | add x y hx hy =>
    obtain ⟨M1, hM1, h1⟩ := hx
    obtain ⟨M2, hM2, h2⟩ := hy
    refine ⟨M1 * M2, Nat.mul_pos hM1 hM2, fun φ ψ h => ?_⟩
    rw [map_add (f := _), map_add (f := _),
      h1 φ ψ fun f hf => h f fun γ hγ => hf γ (_root_.GlobalTheory.KZ.LevelRed.gamma_le_of_dvd (dvd_mul_right M1 M2) hγ),
      h2 φ ψ fun f hf => h f fun γ hγ => hf γ (_root_.GlobalTheory.KZ.LevelRed.gamma_le_of_dvd (dvd_mul_left M2 M1) hγ)]


open scoped MatrixGroups TensorProduct in
open Matrix in
theorem _root_.GlobalTheory.KZ.Tower.eval_kmap_levelRed : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε) (l : ℕ) [Fact l.Prime] (a : X.Khat l) (n : ℕ), ∃ M0 : ℕ, 0 < M0 ∧ ∀ φ ψ : X.K ≃+* X.K, (∀ f : X.K, (∀ γ ∈ CongruenceSubgroup.Gamma M0, X.sl (_root_.GlobalTheory.KZ.ofSL γ) f = f) → φ f = ψ f) → AdicCompletion.eval (_root_.GlobalTheory.KZ.idl l) (X.Kl l) n (X.kmap l φ a) = AdicCompletion.eval (_root_.GlobalTheory.KZ.idl l) (X.Kl l) n (X.kmap l ψ a) := by
  intro Ω _ _ ε X l _ a n
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (a.1 n)
  obtain ⟨M0, hM0, hlev⟩ := exists_level_bc_eq_of_agree_on_level X l m
  refine ⟨M0, hM0, fun φ ψ h => ?_⟩
  unfold _root_.GlobalTheory.KZ.Tower.kmap
  simp only [LinearMap.coe_restrictScalars, AdicCompletion.map_val_apply,
    AdicCompletion.eval_apply]
  rw [← hm]
  simp only [LinearMap.reduceModIdeal_apply]
  exact congrArg _ (hlev φ ψ h)

end GlobalTheory.KZ
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType Matrix

namespace GlobalTheory.PsType.MinorMul

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_of_val_le {χ : kˣ →* ℂˣ} {x y : k} (h : valuation k y ≤ valuation k x) (hx : Triv χ x) : Triv χ y :=
  fun u hu hle => hx u hu (hle.trans h)

theorem triv_zero (χ : kˣ →* ℂˣ) : Triv χ (0 : k) := by
  intro u _ hle
  rw [map_zero, le_zero_iff, map_eq_zero, sub_eq_zero] at hle
  have : u = 1 := Units.ext hle
  simp [this]

def trivIdeal (χ : kˣ →* ℂˣ) : Ideal 𝒪[k] where
  carrier := {x | Triv χ (x : k)}
  zero_mem' := triv_zero χ
  add_mem' {x y} hx hy := by
    show Triv χ ((x : k) + y)
    rcases le_max_iff.1 (Valuation.map_add (valuation k) (x : k) y) with h | h
    · exact triv_of_val_le h hx
    · exact triv_of_val_le h hy
  smul_mem' c x hx := by
    show Triv χ ((c : k) * x)
    refine triv_of_val_le ?_ hx
    rw [map_mul]
    exact mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).1 c.2)

theorem mem_trivIdeal {χ : kˣ →* ℂˣ} {x : 𝒪[k]} : x ∈ trivIdeal χ ↔ Triv χ (x : k) := Iff.rfl

theorem isUnit_of_isUnit_mk {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R} (hI : I ≠ ⊤) {x : R}
    (hx : IsUnit (Ideal.Quotient.mk I x)) : IsUnit x := by
  by_contra hn
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1 : x * y - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hy, map_one, sub_self]
  have hm : x * y ∈ IsLocalRing.maximalIdeal R :=
    Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal x).2 hn)
  have h2 := (IsLocalRing.le_maximalIdeal hI) h1
  have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem _ hm h2
    rwa [sub_sub_cancel] at this
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem toSquareBlockProp_mul {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (M N : Matrix ι ι R) (h : ∀ i, p i → ∀ j, ¬ p j → M i j = 0) :
    (M * N).toSquareBlockProp p = M.toSquareBlockProp p * N.toSquareBlockProp p := by
  have h0 : (M.toBlock p fun i => ¬ p i) = 0 := by
    ext i j; exact h i i.2 j j.2
  unfold toSquareBlockProp
  rw [toBlock_mul_eq_add p p p M N, h0, Matrix.zero_mul, add_zero]

theorem minor_map {n : ℕ} (u : GL (Fin n) 𝒪[k]) (m : Fin n) :
    minor (GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) m =
      algebraMap 𝒪[k] k ((u.val.toSquareBlockProp fun i => i ≤ m).det) := by
  rw [RingHom.map_det]; rfl

end GlobalTheory.PsType.MinorMul

open GlobalTheory.PsType.MinorMul in
theorem GlobalTheory.PsType.minor_mul_mod : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ m : Fin n, ¬ Triv (ψ m / nxt ψ m) 1 → (∀ a ∈ grp ψ, valuation k (minor a m) = 1) ∧ ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, Triv (ψ m / nxt ψ m) (minor (a * b) m - minor a m * minor b m) := by
  intro k _ _ _ _ n ψ hψ m hm
  set χ := ψ m / nxt ψ m with hχ
  set I := trivIdeal χ with hIdef
  have hI : I ≠ ⊤ := by
    intro h
    have : (1 : 𝒪[k]) ∈ I := h ▸ Submodule.mem_top
    exact hm (by have h2 := (mem_trivIdeal (χ := χ) (x := 1)).1 this; simpa using h2)

  have hent : ∀ a ∈ grp ψ, ∀ i j : Fin n, i ≤ m → ¬ j ≤ m → Triv χ (a.val i j) := by
    intro a ha i j hi hj
    have hj' : m < j := not_le.1 hj
    have hlt : (m : ℕ) + 1 < n := lt_of_le_of_lt (Nat.succ_le_of_lt (Fin.lt_def.1 hj')) j.2
    have hnx : nxt ψ m = ψ ⟨(m : ℕ) + 1, hlt⟩ := dif_pos hlt
    have h1 := ha.2 i j (lt_of_le_of_lt hi hj')
    rw [hχ, hnx]
    exact hψ i m ⟨(m : ℕ) + 1, hlt⟩ j hi (Fin.le_def.2 (Nat.le_succ _))
      (Fin.le_def.2 (Nat.succ_le_of_lt (Fin.lt_def.1 hj'))) _ h1

  have hzero : ∀ u : GL (Fin n) 𝒪[k], GeneralLinearGroup.map (algebraMap 𝒪[k] k) u ∈ grp ψ →
      ∀ i, i ≤ m → ∀ j, ¬ j ≤ m → (Ideal.Quotient.mk I).mapMatrix u.val i j = 0 := by
    intro u hu i hi j hj
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hent _ hu i j hi hj)
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨u, rfl⟩ := ha.1
    rw [minor_map]
    refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.1 ?_
    refine isUnit_of_isUnit_mk hI ?_
    have hdet : IsUnit ((Ideal.Quotient.mk I).mapMatrix u.val).det := by
      rw [← RingHom.map_det]
      exact (Matrix.isUnits_det_units u).map _
    rw [twoBlockTriangular_det' _ (fun i => i ≤ m) (hzero u ha)] at hdet
    have := isUnit_of_mul_isUnit_left hdet
    rwa [show (((Ideal.Quotient.mk I).mapMatrix u.val).toSquareBlockProp fun i => i ≤ m) =
      (Ideal.Quotient.mk I).mapMatrix (u.val.toSquareBlockProp fun i => i ≤ m) from rfl, ← RingHom.map_det] at this
  · intro a ha b hb
    obtain ⟨u, rfl⟩ := ha.1
    obtain ⟨w, rfl⟩ := hb.1
    rw [← map_mul, minor_map, minor_map, minor_map, ← map_mul, ← map_sub]
    suffices hs : (((u * w).val.toSquareBlockProp fun i => i ≤ m).det -
        (u.val.toSquareBlockProp fun i => i ≤ m).det * (w.val.toSquareBlockProp fun i => i ≤ m).det) ∈ I from hs
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, RingHom.map_det, RingHom.map_det, RingHom.map_det, sub_eq_zero,
      ← det_mul]
    congr 1
    rw [Units.val_mul]
    show ((Ideal.Quotient.mk I).mapMatrix (u.val * w.val)).toSquareBlockProp (fun i => i ≤ m) = _
    rw [map_mul, toSquareBlockProp_mul _ _ _ (hzero u ha)]
    rfl
end
end

section

namespace GlobalTheory.AdjoinStableCommutes

theorem adjoin_stable_and_commutes {E V G : Type} [Field E] [AddCommGroup V] [Module E V]
    (A : Set GlobalTheory.KZ.Letter) (f : GlobalTheory.KZ.Letter → Module.End E V) (W : Submodule E V)
    (g : G → Module.End E V)
    (hW : ∀ T ∈ A, ∀ x ∈ W, f T x ∈ W)
    (hg : ∀ T ∈ A, ∀ (s : G), ∀ x ∈ W, f T (g s x) = g s (f T x)) :
    ∀ Q ∈ Algebra.adjoin E (FreeAlgebra.ι E '' A), ∀ x ∈ W,
      (FreeAlgebra.lift E f Q) x ∈ W ∧
        ∀ s : G, g s ((FreeAlgebra.lift E f Q) x) = (FreeAlgebra.lift E f Q) (g s x) := by
  intro Q hQ
  induction hQ using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨T, hT, rfl⟩ := hy
    intro x hx
    rw [FreeAlgebra.lift_ι_apply]
    exact ⟨hW T hT x hx, fun s => (hg T hT s x hx).symm⟩
  | algebraMap r =>
    intro x hx
    rw [AlgHom.commutes]
    refine ⟨?_, fun s => ?_⟩
    · rw [Module.algebraMap_end_apply]
      exact W.smul_mem r hx
    · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  | add a b _ _ ha hb =>
    intro x hx
    rw [map_add (f := _)]
    refine ⟨?_, fun s => ?_⟩
    · rw [LinearMap.add_apply]
      exact W.add_mem (ha x hx).1 (hb x hx).1
    · rw [LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), (ha x hx).2 s, (hb x hx).2 s]
  | mul a b _ _ ha hb =>
    intro x hx
    rw [map_mul]
    refine ⟨?_, fun s => ?_⟩
    · rw [Module.End.mul_apply]
      exact (ha _ (hb x hx).1).1
    · rw [Module.End.mul_apply, Module.End.mul_apply, (ha _ (hb x hx).1).2 s, (hb x hx).2 s]

end GlobalTheory.AdjoinStableCommutes
end

section

open GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

theorem derOn_killed_sq : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
    [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S),
    IsTrData B C tr a b e → ∀ D : S → M, IsDerOn C D → (∀ β ∈ B, D β = 0) →
      ∀ x ∈ C, (e * e) • D x = 0 := by
  intro A S M _ _ _ _ _ B C tr n a b e h D hD hB x hx
  have hsum : ∀ (s : Finset (Fin n)) (f : Fin n → S), (∀ i, f i ∈ C) →
      D (∑ i ∈ s, f i) = ∑ i ∈ s, D (f i) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using hD.alg 0
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        hD.add _ (hf j) _ (Subalgebra.sum_mem _ (fun i _ => hf i)), ih]
  have key : ∀ y ∈ C, e • D y = ∑ j, tr (b j * y) • D (a j) := by
    intro y hy
    have heC : e ∈ C := h.le h.e_mem
    have h1 : D (e * y) = e • D y := by
      rw [hD.mul e heC y hy, hB e h.e_mem, smul_zero, add_zero]
    rw [← h1, ← h.left y hy, hsum _ _ (fun j => C.mul_mem (h.a_mem j)
      (h.le (h.tr_mem _ (C.mul_mem (h.b_mem j) hy))))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have ht : tr (b j * y) ∈ B := h.tr_mem _ (C.mul_mem (h.b_mem j) hy)
    rw [hD.mul _ (h.a_mem j) _ (h.le ht), hB _ ht, smul_zero, zero_add]
  have L : ∑ i, b i • (e • D (x * a i)) = ∑ j, (e * x * b j) • D (a j) := by
    simp_rw [key _ (C.mul_mem hx (h.a_mem _)), Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_smul]
    congr 1
    have hr := h.right (b j * x) (C.mul_mem (h.b_mem j) hx)
    calc ∑ i, b i * tr (b j * (x * a i)) = ∑ i, b i * tr (a i * (b j * x)) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [show b j * (x * a i) = a i * (b j * x) by ring]
      _ = e * (b j * x) := hr
      _ = e * x * b j := by ring
  have R : ∑ i, b i • (e • D (x * a i)) = ∑ j, (e * x * b j) • D (a j) + (e * e) • D x := by
    simp_rw [hD.mul x hx _ (h.a_mem _), smul_add, smul_smul, Finset.sum_add_distrib,
      ← Finset.sum_smul]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1; ring
    · congr 1
      rw [show e * e = e * ∑ i, a i * b i by rw [h.sum], Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
  have := R.symm.trans L
  simpa using this

end GlobalTheory.AlmostEt
end

section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Tower.klm (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) : X.Kl l →ₗ[ℤ_[l]] X.Kl l :=
  LinearMap.baseChange ℤ_[l] (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom)))

def Tower.Lev (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (M : ℕ) : Submodule ℤ_[l] (X.Kl l) :=
  Submodule.span ℤ_[l] {x | ∃ f : X.Kˣ, (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (f : X.K) = f) ∧
    x = (1 : ℤ_[l]) ⊗ₜ Additive.ofMul f}

end GlobalTheory.KZ
end
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.exists_qRoot_poly_of_fixed_geometric_stabilizer : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (N : ℕ) (y : Ω), (∀ g ∈ Ggeo (p := p) Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) ∧
    y = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j := by
  first | exact @GlobalTheory.K5.span_fixed_ggeo_stab | exact GlobalTheory.K5.span_fixed_ggeo_stab | (intros; apply GlobalTheory.K5.span_fixed_ggeo_stab <;> assumption)
end
