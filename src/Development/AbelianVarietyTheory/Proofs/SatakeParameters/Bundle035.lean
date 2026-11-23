module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle020
public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle029
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
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import ReciprocityTheory.Automorphisms.PlaceA
public import ReciprocityTheory.DualLattices.Bundle016
import ReciprocityTheory.DualLattices.UpSmith
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Basic.PEquiv
public import Mathlib.Data.Matrix.PEquiv

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut

noncomputable section

namespace GlobalTheory.TSetFin

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => maximalRealSubfield L

theorem exists_sep (s : SplitPlace L) : ∃ e : 𝓞 L, Valued.v (s.i (e : L)) = 1 ∧
    Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 := GlobalTheory.T.exists_integer_unit_split_place_conjugate_prime L s

theorem mem_ALint_of_local (s : SplitPlace L) (e : 𝓞 L) (he : Valued.v (s.i (e : L)) = 1)
    (he' : Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1) (z : AL L)
    (hz : ∀ w, w ≠ s.v → compAt L w z = 0) (h1 : Valued.v (s.proj (L := L) z) ≤ 1)
    (h2 : Valued.v (s.proj (L := L) (conjAL L z)) ≤ 1) : z ∈ ALint L := GlobalTheory.T.cmField_adele_split_place_support_integral L s e he he' z hz h1 h2

theorem local_int {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (ϖ : v.adicCompletion F) (k : ℕ) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (a a' b b' g g' : GL (Fin n) (v.adicCompletion F))
    (ha' : ∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1)
    (hai : ∀ i j, Valued.v (((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1)
    (hbi : ∀ i j, Valued.v (((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1)
    (hb' : ∀ i j, Valued.v ((b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1)
    (hc : ∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j -
      (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) < 1)
    (hg : (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)))
    (hg' : (g' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b' : Matrix (Fin n) (Fin n) (v.adicCompletion F))) :
    ∀ i j, Valued.v (((g⁻¹ * g' : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1 :=
  GlobalTheory.T.heckeDoubleCoset_adicCompletion_inv_mul_integral F v n ϖ k hϖ a a' b b' g g' ha' hai hbi hb' hc hg hg'

theorem triv_mul {n : ℕ} {T : Set (HeightOneSpectrum (𝓞 L⁺))} {x y : GA L n}
    (hx : TrivOutside (L := L) T x) (hy : TrivOutside (L := L) T y) :
    TrivOutside (L := L) T (x * y) := by
  intro w hw
  have : ((x * y).1 : Matrix (Fin n) (Fin n) (AL L)) = (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [this, Matrix.map_mul, hx w hw, hy w hw, mul_one]

theorem triv_inv {n : ℕ} {T : Set (HeightOneSpectrum (𝓞 L⁺))} {x : GA L n}
    (hx : TrivOutside (L := L) T x) : TrivOutside (L := L) T x⁻¹ := by
  intro w hw
  have h1 : (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have h2 := congrArg (fun M => M.map (compAt L w)) h1
  simp only [Matrix.map_mul, hx w hw, mul_one] at h2
  rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mem_Umax_of_loc {n : ℕ} (s : SplitPlace L) (x : GA L n) (hx : TrivOutside (L := L) {s.v} x)
    (h1 : ∀ i j, Valued.v (((s.loc (L := L) n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1)
    (h2 : ∀ i j, Valued.v (((s.loc (L := L) n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1) :
    x ∈ Umax L n := by
  obtain ⟨e, he, he'⟩ := exists_sep s
  intro i j
  have hconj : conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
    have hm := x.2
    simp only [GA, UGroup, Subgroup.mem_mk] at hm
    have h1 : ((x.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) x.1 :=
      Units.inv_eq_of_mul_eq_one_right hm
    simp only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]
  have hz : (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
    apply mem_ALint_of_local s e he he'
    · intro w hw
      have := congrFun (congrFun (hx w (by simpa using hw)) i) j
      simp only [Matrix.map_apply] at this
      rw [map_sub, this]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · have e1 : s.proj (L := L) ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          ((s.loc (L := L) n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j := rfl
      rw [map_sub, e1]
      refine (Valuation.map_sub _ _ _).trans (max_le (h1 i j) ?_)
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · have e1 : s.proj (L := L) ((((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
          ((s.loc (L := L) n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) j i := rfl
      rw [map_sub, map_sub, hconj, e1]
      refine (Valuation.map_sub _ _ _).trans (max_le (h2 j i) ?_)
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have := add_mem hz (show (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem])
  simpa using this

theorem glint_int {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    {a : GL (Fin n) (v.adicCompletion F)} (ha : a ∈ Formalism.UG.GLint (Fin n) (v.adicCompletionIntegers F).toSubring) :
    (∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) ∧
      ∀ i j, Valued.v (((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1 := by
  obtain ⟨g, rfl⟩ := ha
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · exact ((g : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F).toSubring) i j).2
  · rw [← map_inv]
    exact (((g⁻¹ : GL (Fin n) (v.adicCompletionIntegers F).toSubring) : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F).toSubring) i j).2

theorem approx_class (v : HeightOneSpectrum (𝓞 L⁺)) :
    ∃ c : v.adicCompletion L⁺ → 𝓞 L⁺ ⧸ v.asIdeal, ∀ y y' : v.adicCompletion L⁺, Valued.v y ≤ 1 → Valued.v y' ≤ 1 →
      c y = c y' → Valued.v (y - y') < 1 := by
  classical
  refine ⟨fun y => if h : Valued.v y ≤ 1 then Ideal.Quotient.mk _ (adic_exists_approx v y h).choose else 0, ?_⟩
  intro y y' hy hy' hc
  simp only [dif_pos hy, dif_pos hy'] at hc
  have ha := (adic_exists_approx v y hy).choose_spec
  have ha' := (adic_exists_approx v y' hy').choose_spec
  set a := (adic_exists_approx v y hy).choose
  set a' := (adic_exists_approx v y' hy').choose
  rw [Ideal.Quotient.eq] at hc
  have h3 : Valued.v (algebraMap (𝓞 L⁺) (v.adicCompletion L⁺) (a - a')) < 1 := by
    show Valued.v (algebraMap L⁺ (v.adicCompletion L⁺) (algebraMap (𝓞 L⁺) L⁺ (a - a'))) < 1
    rw [adic_valued_algebraMap]
    exact (v.valuation_lt_one_iff_mem (K := L⁺) _).2 hc
  have e : y - y' = (y - algebraMap (𝓞 L⁺) (v.adicCompletion L⁺) a) -
      (y' - algebraMap (𝓞 L⁺) (v.adicCompletion L⁺) a') + algebraMap (𝓞 L⁺) (v.adicCompletion L⁺) (a - a') := by
    rw [map_sub]; ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ha ha')) h3)

theorem finite_image_tSet : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (J : Subgroup (Formalism.AUTREP.GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))),
    Formalism.L2.NG.HypOutside J χ B → ∀ (s : ReciprocityTheory.Aut.SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ),
    s.v ∉ B → Formalism.AUTREP.IsUnif L s.v ϖ →
    ((fun x : Formalism.AUTREP.GAf L n => (x : Formalism.AUTREP.GAf L n ⧸ J)) '' Formalism.AUTREP.tSet L n s ϖ k).Finite := by
  intro L _ _ _ n J χ B hJ s ϖ k hB hϖ
  classical
  obtain ⟨c, hc⟩ := approx_class s.v
  haveI : Finite (𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ s.v.ne_bot
  let κ : Formalism.AUTREP.GAf L n → (Fin n → Fin n → 𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := fun x =>
    if h : x ∈ Formalism.AUTREP.tSet L n s ϖ k then
      fun i j => c (((h.2.choose : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j)
    else 0
  have key : ∀ x ∈ Formalism.AUTREP.tSet L n s ϖ k, ∀ x' ∈ Formalism.AUTREP.tSet L n s ϖ k, κ x = κ x' →
      (x : Formalism.AUTREP.GAf L n ⧸ J) = x' := by
    intro x hx x' hx' hκ
    simp only [κ, dif_pos hx, dif_pos hx'] at hκ
    obtain ⟨ha, b, hb, hg⟩ := hx.2.choose_spec
    obtain ⟨ha', b', hb', hg'⟩ := hx'.2.choose_spec
    set a := hx.2.choose
    set a' := hx'.2.choose
    have ia := glint_int ha
    have ia' := glint_int ha'
    have ib := glint_int hb
    have ib' := glint_int hb'
    have hcl : ∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j -
        (a' : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) < 1 := fun i j =>
      hc _ _ (ia.1 i j) (ia'.1 i j) (congrFun (congrFun hκ i) j)
    have hcl' : ∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j -
        (a : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) < 1 := fun i j => by
      rw [← Valuation.map_neg, neg_sub]; exact hcl i j
    have hunif : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
    have h1 := local_int s.v ϖ k hunif a a' b b' _ _ ia'.1 ia.2 ib.2 ib'.1 hcl hg hg'
    have h2 := local_int s.v ϖ k hunif a' a b' b _ _ ia.1 ia'.2 ib'.2 ib.1 hcl' hg' hg
    rw [QuotientGroup.eq]
    have htriv : TrivOutside (L := L) {s.v} (x⁻¹ * x') := triv_mul (triv_inv hx.1) hx'.1
    refine ((hJ _ ?_).1).2 ?_
    · intro w hw
      refine htriv w ?_
      rintro rfl
      exact hB (by simpa using hw)
    · refine mem_Umax_of_loc s _ htriv (fun i j => ?_) (fun i j => ?_)
      · rw [map_mul, map_inv]; exact h1 i j
      · rw [mul_inv_rev, inv_inv, map_mul, map_inv]; exact h2 i j
  let g : Formalism.AUTREP.GAf L n ⧸ J → (Fin n → Fin n → 𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := fun q =>
    if h : ∃ x ∈ Formalism.AUTREP.tSet L n s ϖ k, (x : Formalism.AUTREP.GAf L n ⧸ J) = q then κ h.choose else 0
  refine Set.Finite.of_finite_image (f := g) (Set.toFinite _) ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ hgg
  have h : ∃ y ∈ Formalism.AUTREP.tSet L n s ϖ k, (y : Formalism.AUTREP.GAf L n ⧸ J) = x := ⟨x, hx, rfl⟩
  have h' : ∃ y ∈ Formalism.AUTREP.tSet L n s ϖ k, (y : Formalism.AUTREP.GAf L n ⧸ J) = x' := ⟨x', hx', rfl⟩
  simp only [g, dif_pos h, dif_pos h'] at hgg
  show (x : Formalism.AUTREP.GAf L n ⧸ J) = x'
  rw [← h.choose_spec.2, ← h'.choose_spec.2]
  exact key _ h.choose_spec.1 _ h'.choose_spec.1 hgg

end GlobalTheory.TSetFin
end
end

section

open Matrix

namespace GlobalTheory.SmithValued

variable (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))]

noncomputable def vNN : Valuation L NNReal :=
  (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).map
    { toMonoidWithZeroHom := WithZeroMulInt.toNNReal (e := 2) (by norm_num)
      monotone' := (WithZeroMulInt.toNNReal_strictMono (e := 2) (by norm_num)).monotone }

theorem vNN_le_one_iff (x : L) : vNN L x ≤ 1 ↔ x ∈ Formalism.UG.intL L := by
  have h := (WithZeroMulInt.toNNReal_strictMono (e := 2) (by norm_num)).le_iff_le
    (a := (Valued.v x : WithZero (Multiplicative ℤ))) (b := 1)
  rw [map_one] at h
  exact h

theorem vNN_integers : (vNN L).Integers ↥(Formalism.UG.intL L) := by
  refine ⟨Subtype.val_injective, ?_, ?_⟩
  · intro x
    exact (vNN_le_one_iff L _).2 x.2
  · intro r hr
    exact ⟨⟨r, (vNN_le_one_iff L _).1 hr⟩, rfl⟩

theorem exists_clear {ι : Type} (s : Finset ι) (f : ι → L) :
    ∃ c : L, c ≠ 0 ∧ c ∈ Formalism.UG.intL L ∧ ∀ i ∈ s, c * f i ∈ Formalism.UG.intL L := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, one_mem _, by simp⟩
  | insert a s _ ih =>
    obtain ⟨c, hc0, hc, hs⟩ := ih
    by_cases ha : f a ∈ Formalism.UG.intL L
    · refine ⟨c, hc0, hc, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact mul_mem hc ha
      · exact hs i hi
    · have h0 : f a ≠ 0 := by
        intro h; exact ha (h ▸ zero_mem _)
      have hinv : (f a)⁻¹ ∈ Formalism.UG.intL L := by
        rw [← vNN_le_one_iff] at ha ⊢
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ (not_le.1 ha).le
      refine ⟨(f a)⁻¹ * c, mul_ne_zero (inv_ne_zero h0) hc0, mul_mem hinv hc, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · have : (f i)⁻¹ * c * f i = c := by field_simp
        rw [this]; exact hc
      · rw [mul_assoc]; exact mul_mem hinv (hs i hi)

theorem smith_valued : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) (M : Matrix (Fin m) (Fin n) L),
    ∃ (P P' : Matrix (Fin m) (Fin m) L) (Q Q' : Matrix (Fin n) (Fin n) L) (d : Fin m → L),
      (∀ i j, P i j ∈ Formalism.UG.intL L) ∧ (∀ i j, P' i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, Q i j ∈ Formalism.UG.intL L) ∧ (∀ i j, Q' i j ∈ Formalism.UG.intL L) ∧ P * P' = 1 ∧ Q * Q' = 1 ∧
      M = P * Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0) * Q := by
  intro L _ _ m n M
  classical
  obtain ⟨c, hc0, -, hc⟩ := exists_clear L (Finset.univ : Finset (Fin m × Fin n))
    (fun p => M p.1 p.2)
  let A : Matrix (Fin m) (Fin n) ↥(Formalism.UG.intL L) :=
    Matrix.of fun i j => ⟨c * M i j, hc (i, j) (Finset.mem_univ _)⟩
  have diagonalize : ∀ (d n : ℕ) (X : Matrix (Fin d) (Fin n) ↥(Formalism.UG.intL L)),
      ∃ (P : Matrix (Fin d) (Fin d) ↥(Formalism.UG.intL L))
        (Q : Matrix (Fin n) (Fin n) ↥(Formalism.UG.intL L)) (a : Fin d → ↥(Formalism.UG.intL L)),
        IsUnit P.det ∧ IsUnit Q.det ∧
          ∀ j k, (P * X * Q) j k = if (k : ℕ) = (j : ℕ) then a j else 0 := by
    open ReciprocityTheory.PGsh.Up.Smith in
    intro d
    induction d with
    | zero =>
      intro n X
      exact ⟨1, 1, Fin.elim0, by simp, by simp, fun j => j.elim0⟩
    | succ d ih =>
      intro n X
      cases n with
      | zero => exact ⟨1, 1, 0, by simp, by simp, fun j k => k.elim0⟩
      | succ n =>
        let g : Fin (n + 1) → Fin (d + 1) → ↥(Formalism.UG.intL L) := fun j i => X i j
        obtain ⟨i₀, a, u, s, hu, -, hs, hz, hnz⟩ := exists_pivot (vNN_integers L) g
        by_cases ha : a = 0
        · have hX : X = 0 := by
            apply Matrix.ext
            intro i j
            exact congrFun (hz ha j) i
          exact ⟨1, 1, 0, by simp, by simp, fun j k => by simp [hX]⟩
        obtain ⟨j₀, hj₀, hs₀⟩ := hnz ha
        have hcol : ∀ i, X i j₀ = a * u i := fun i => congrFun hj₀ i
        have hrow : ∀ j, X i₀ j = a * s j := hs
        let B := (Vm i₀ u)ᵀ * X * Vm j₀ s
        have hB (i j) : B i j = if i = i₀ then (if j = j₀ then a else 0) else
            if j = j₀ then 0 else X i j - s j * (a * u i) := by
          dsimp only [B]
          rw [Matrix.mul_assoc, VmT_mul, mul_Vm, mul_Vm]
          by_cases hi : i = i₀ <;> by_cases hj : j = j₀
          · subst i
            subst j
            simp [hcol, hu]
          · subst i
            simp [hj, hrow, hs₀]
            ring
          · subst j
            simp [hi, hcol, hu]
            ring
          · simp only [hi, hj, ite_false, hcol, hrow, hu]
            ring
        let C := B.submatrix (piv i₀) (piv j₀)
        let Y := Matrix.of fun (i : Fin d) (j : Fin n) => C i.succ j.succ
        obtain ⟨P, Q, b, hP, hQ, hY⟩ := ih n Y
        let U : Matrix (Fin (d + 1)) (Fin (d + 1)) ↥(Formalism.UG.intL L) :=
          (piv i₀).toPEquiv.toMatrix
        let V : Matrix (Fin (n + 1)) (Fin (n + 1)) ↥(Formalism.UG.intL L) :=
          (piv j₀).symm.toPEquiv.toMatrix
        have hC : U * B * V = C := by
          dsimp only [U, V, C]
          rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm]
          rfl
        have hrow₀ (j : Fin n) : C 0 j.succ = 0 := by
          simp [C, piv_zero, piv_succ, hB, Fin.succAbove_ne]
        have hcol₀ (i : Fin d) : C i.succ 0 = 0 := by
          simp [C, piv_zero, piv_succ, hB, Fin.succAbove_ne]
        obtain ⟨h00, h0j, hi0, hij⟩ := blockOne_mul_mul_blockOne P C Q hrow₀ hcol₀
        refine ⟨bd1 P * U * (Vm i₀ u)ᵀ, Vm j₀ s * V * bd1 Q, Fin.cons a b, ?_, ?_, ?_⟩
        · rw [Matrix.det_mul, Matrix.det_mul, det_blockOne_alt, Matrix.det_transpose, det_Vm, mul_one]
          exact hP.mul (isUnit_det_perm _)
        · rw [Matrix.det_mul, Matrix.det_mul, det_blockOne_alt, det_Vm, one_mul]
          exact (isUnit_det_perm _).mul hQ
        · have hfull : bd1 P * U * (Vm i₀ u)ᵀ * X * (Vm j₀ s * V * bd1 Q) =
              bd1 P * C * bd1 Q := by
            rw [← hC]
            simp only [B, Matrix.mul_assoc]
          intro i j
          rw [hfull]
          refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
          · rw [h00]
            simp [C, piv_zero, hB]
          · rw [h0j]
            simp
          · rw [hi0]
            simp
          · rw [hij, hY]
            simp [Fin.val_succ]
  obtain ⟨P, Q, a, hP, hQ, hD⟩ := diagonalize m n A
  let φ : ↥(Formalism.UG.intL L) →+* L := (Formalism.UG.intL L).subtype
  have hP1 : P⁻¹.map φ * P.map φ = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hP, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hQ1 : Q⁻¹.map φ * Q.map φ = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hQ, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hQ2 : Q.map φ * Q⁻¹.map φ = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hQ, Matrix.map_one _ (map_zero φ) (map_one φ)]
  refine ⟨P⁻¹.map φ, P.map φ, Q⁻¹.map φ, Q.map φ, fun j => c⁻¹ * (a j : L),
    fun i j => (P⁻¹ i j).2, fun i j => (P i j).2, fun i j => (Q⁻¹ i j).2, fun i j => (Q i j).2,
    hP1, hQ1, ?_⟩
  have hA : A.map φ = c • M := by
    ext i j; simp [A, φ]
  have hD' : Matrix.of (fun (j : Fin m) (k : Fin n) =>
      if (k : ℕ) = (j : ℕ) then c⁻¹ * (a j : L) else 0) = P.map φ * M * Q.map φ := by
    have h1 : (P * A * Q).map φ = c • (P.map φ * M * Q.map φ) := by
      rw [Matrix.map_mul, Matrix.map_mul, hA, Matrix.mul_smul, Matrix.smul_mul]
    have h2 : P.map φ * M * Q.map φ = c⁻¹ • (P * A * Q).map φ := by
      rw [h1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [h2]
    ext j k
    rw [Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, hD, smul_eq_mul]
    split_ifs
    · rfl
    · simp
  rw [hD', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP1, Matrix.one_mul, Matrix.mul_assoc, hQ2,
    Matrix.mul_one]

end GlobalTheory.SmithValued
end

section

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Module

namespace GlobalTheory

theorem cocycle_bound_length_le : ∀ {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (Z : Submodule O (G → V)), (∀ c ∈ Z, ∀ g, c g ∈ L.T) → Module.length O (↥(Z ⊓ (B1 ρ).restrictScalars O) ⧸ (latticeCoboundaries L).comap (Z ⊓ (B1 ρ).restrictScalars O).subtype) ≤ Module.length O ↥(Representation.invariants (repD L)) := by
  intro G _ LL _ O _ _ V _ _ _ _ ρ L Z hZ
  set M := Z ⊓ (B1 ρ).restrictScalars O with hM
  set K := (latticeCoboundaries L).comap M.subtype with hK

  let χ : V →ₗ[O] (G → V) ⧸ latticeCoboundaries L := (latticeCoboundaries L).mkQ ∘ₗ (cob ρ).restrictScalars O
  have hχ : L.T ≤ LinearMap.ker χ := by
    intro t ht
    simp only [LinearMap.mem_ker, χ, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨t, ht, rfl⟩
  let ψ : ↥(Representation.invariants (repD L)) →ₗ[O] (G → V) ⧸ latticeCoboundaries L :=
    (L.T.liftQ χ hχ) ∘ₗ (Representation.invariants (repD L)).subtype
  let ι : M →ₗ[O] (G → V) ⧸ latticeCoboundaries L := (latticeCoboundaries L).mkQ ∘ₗ M.subtype
  have hKι : K ≤ LinearMap.ker ι := by
    intro x hx
    simpa [ι, K, Submodule.Quotient.mk_eq_zero] using hx
  let f : (M ⧸ K) →ₗ[O] (G → V) ⧸ latticeCoboundaries L := K.liftQ ι hKι
  have hfinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K x
    simp only [LinearMap.mem_ker, f, Submodule.liftQ_apply, ι, LinearMap.coe_comp,
      Function.comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hx
    simp only [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, K, Submodule.mem_comap,
      Submodule.coe_subtype]
    exact hx
  have hrange : LinearMap.range f ≤ LinearMap.range ψ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨⟨c, hcM⟩, rfl⟩ := Submodule.Quotient.mk_surjective K x
    obtain ⟨hcZ, hcB⟩ := hcM
    obtain ⟨v, hv⟩ := hcB
    have hinv : L.T.mkQ v ∈ Representation.invariants (repD L) := by
      intro g
      change (Submodule.Quotient.mk ((ρ g) v) : V ⧸ L.T) = Submodule.Quotient.mk v
      rw [Submodule.Quotient.eq]
      have := hZ c hcZ g
      rw [← hv] at this
      simpa [cob] using this
    refine ⟨⟨_, hinv⟩, ?_⟩
    simp [ψ, f, ι, χ, hv]
  calc Module.length O (M ⧸ K) ≤ Module.length O (LinearMap.range ψ) :=
        Module.length_le_of_injective ((Submodule.inclusion hrange).comp f.rangeRestrict) (by
          intro a b hab
          apply hfinj
          have := congrArg Subtype.val hab
          simpa using this)
    _ ≤ _ := Module.length_le_of_surjective ψ.rangeRestrict ψ.surjective_rangeRestrict

end GlobalTheory
end

section

open NumberField IsDedekindDomain WithZero

theorem _root_.GlobalTheory.T.surjective_algebraMap_adicCompletion_complete_dvr : ∀ {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (π : W) (hπ : Irreducible π) (hc : IsAdicComplete (Ideal.span {π}) W) (v : HeightOneSpectrum W), Function.Surjective (algebraMap Qq (v.adicCompletion Qq)) := by
  first | exact @GlobalTheory.DenseCompl.surjective_algebraMap_adicCompletion | exact GlobalTheory.DenseCompl.surjective_algebraMap_adicCompletion | (intros; apply GlobalTheory.DenseCompl.surjective_algebraMap_adicCompletion <;> assumption)
end
