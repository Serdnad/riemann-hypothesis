module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import ReciprocityTheory.DualLattices.Bundle001
public import Mathlib.Data.EReal.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise

noncomputable section
namespace GlobalTheory.SplitWeil.Model

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem secondCountable_and_t2_local_field : SecondCountableTopology k ∧ T2Space k := by
  let _ := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  let _ : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  open scoped Valued in
  exact ⟨secondCountable_of_proper, inferInstance⟩

theorem nabs_pos (x : kˣ) : 0 < nabs k x := by
  unfold nabs; exact_mod_cast distribHaarChar_pos

theorem nabs_mul (x y : kˣ) : nabs k (x * y) = nabs k x * nabs k y := by
  simp [nabs]

theorem nabs_one : nabs k 1 = 1 := by simp [nabs]

theorem om_one {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (Φ : Matrix b a k → ℂ) : om μ (1 : GL a k) (1 : GL b k) Φ = Φ := by
  funext x; simp [om, nabs_one]

theorem om_mul {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g g' : GL a k) (h h' : GL b k) (Φ : Matrix b a k → ℂ) :
    om μ (g * g') (h * h') Φ = om μ g h (om μ g' h' Φ) := by
  funext x
  simp only [om, map_mul, nabs_mul, Real.mul_rpow (nabs_pos _).le (nabs_pos _).le,
    _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Complex.ofReal_mul]
  ring

theorem not_hasConductor_one (c : kˣ) : ¬ HasConductor (1 : AddChar k Circle) c := by
  intro h
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have := (h (c / r)).1 (fun y _ => rfl)
  have hc : valuation k (c : k) ≠ 0 := by simp
  have hr' : valuation k r ≠ 0 := by simpa using hr
  rw [map_div₀, div_le_iff₀ (zero_lt_iff.2 hr')] at this
  have h2 : valuation k (c : k) * valuation k r < valuation k (c : k) * 1 :=
    mul_lt_mul_of_pos_left hr1 (zero_lt_iff.2 hc)
  rw [mul_one] at h2
  exact absurd this (not_le.2 h2)

def ratCircle : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp⟩)

theorem ratCircle_eq_zero (x : AddCircle (1 : ℚ)) (h : ratCircle x = 0) : x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H q =>
    have h' : (((q : ℝ)) : AddCircle (1 : ℝ)) = 0 := h
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h'
    refine (AddCircle.coe_eq_zero_iff _).2 ⟨n, ?_⟩
    have : ((n : ℚ) : ℝ) = (q : ℝ) := by simpa using hn
    simpa using (Rat.cast_injective this : (n : ℚ) = q)

theorem exists_hasConductor : ∃ ψ : AddChar k Circle, HasConductor ψ 1 := by
  obtain ⟨t, ht⟩ := ValuativeRel.valuation_surjective (uniformizer k)⁻¹
  have ht1 : 1 < valuation k t := by
    rw [ht]; exact uniformizer_inv_le_iff.1 le_rfl
  let O : AddSubgroup k := (𝒪[k]).toAddSubgroup
  have hne : (QuotientAddGroup.mk t : k ⧸ O) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    exact not_le.2 ht1
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  let c' : (k ⧸ O) →+ AddCircle (1 : ℚ) := c
  let f : k →+ AddCircle (1 : ℝ) := ratCircle.comp (c'.comp (QuotientAddGroup.mk' O))
  refine ⟨(AddCircle.toCircle_addChar (T := 1)).compAddMonoidHom f, fun x => ⟨fun h => ?_, fun h y hy => ?_⟩⟩
  · by_contra hx
    have hx' : 1 < valuation k x := by simpa using hx
    have h1 := h t (ht ▸ uniformizer_inv_le_iff.2 hx')
    have h2 : AddCircle.toCircle (f t) = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      rw [AddCircle.toCircle_zero]; exact h1
    exact hc (ratCircle_eq_zero _ (AddCircle.injective_toCircle one_ne_zero h2))
  · have hy' : (QuotientAddGroup.mk y : k ⧸ O) = 0 := by
      rw [QuotientAddGroup.eq_zero_iff]
      exact hy.trans (by simpa using h)
    show AddCircle.toCircle (ratCircle (c' (QuotientAddGroup.mk y))) = 1
    rw [hy']; simp

theorem KOne_le_KO (n : Type*) [Fintype n] [DecidableEq n] : KOne k n ≤ KO k n :=
  Subgroup.map_le_range _ _

theorem isOpen_int : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer

theorem isCompact_int : IsCompact (𝒪[k] : Set k) :=
  IsNonarchimedeanLocalField.isCompact_closedBall k 1

variable [MeasurableSpace k] [BorelSpace k]

theorem exists_isUnitVol : ∃ ν : Measure k, IsUnitVol ν := by
  let K : TopologicalSpace.PositiveCompacts k := ⟨⟨(𝒪[k] : Set k), isCompact_int⟩, by
    rw [show interior ((⟨(𝒪[k] : Set k), isCompact_int⟩ : TopologicalSpace.Compacts k).carrier) =
      (𝒪[k] : Set k) from isOpen_int.interior_eq]
    exact ⟨0, zero_mem _⟩⟩
  exact ⟨Measure.addHaarMeasure K, inferInstance, Measure.addHaarMeasure_self⟩

theorem nabs_vol (ν : Measure k) (h : IsUnitVol ν) (x : kˣ) :
    ν (x • (𝒪[k] : Set k)) = ENNReal.ofReal (nabs k x) := by
  have := h.1
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  rw [← distribHaarChar_mul ν x, h.2]; simp [nabs]

theorem nabs_le_one (x : kˣ) (hx : valuation k (x : k) ≤ 1) : nabs k x ≤ 1 := by
  obtain ⟨ν, h⟩ := exists_isUnitVol (k := k)
  have : ν (x • (𝒪[k] : Set k)) ≤ ν (𝒪[k] : Set k) := by
    apply measure_mono
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (show (x : k) ∈ 𝒪[k] from hx) hy
  rw [nabs_vol ν h, h.2] at this
  exact ENNReal.ofReal_le_one.1 this

theorem measurableEmbedding_val (n : Type*) [Fintype n] [DecidableEq n] :
    MeasurableEmbedding (fun g : GL n k => g.val) := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  refine MeasurableEmbedding.iff_comap_eq.2 ⟨Units.val_injective, rfl, ?_⟩
  have hB : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  have : Set.range (fun g : GL n k => g.val) = {x : Matrix n n k | x.det ≠ 0} := by
    ext x
    simp only [Set.mem_range, Set.mem_setOf_eq]
    rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
    rfl
  rw [this]
  exact (isOpen_ne_fun (continuous_id.matrix_det) continuous_const).measurableSet




omit [MeasurableSpace k] [BorelSpace k] in
theorem om_mem_SB {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) {Φ : Matrix b a k → ℂ} (hΦ : Φ ∈ SB (Matrix b a k)) :
    om μ g h Φ ∈ SB (Matrix b a k) := by
  let e : Matrix b a k ≃ₜ Matrix b a k :=
    { toFun := fun x => (h⁻¹ : GL b k).val * x * g.val
      invFun := fun x => h.val * x * (g⁻¹ : GL a k).val
      left_inv := fun x => by
        simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      right_inv := fun x => by
        simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  have h1 : (Φ ∘ e) ∈ SB (Matrix b a k) :=
    ⟨hΦ.1.comp_continuous e.continuous, hΦ.2.comp_homeomorph e⟩
  exact (SB (Matrix b a k)).smul_mem _ h1

end GlobalTheory.SplitWeil.Model
end
end

section

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise

namespace GlobalTheory.HL

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

def hf (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  ∑ i, ∑ j, x i * Hm i j * L.cj (y j)

def cT (L : LocE F E) {m n : Type} (A : Matrix m n E) : Matrix n m E := fun i j => L.cj (A j i)

def IsHerm (L : LocE F E) {m : Type} (A : Matrix m m E) : Prop := cT L A = A

def IsHermND (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) : Prop :=
  IsHerm L Hm ∧ IsUnit Hm.det

def IsIntM (L : LocE F E) {m n : Type} (A : Matrix m n E) : Prop := ∀ i j, A i j ∈ L.O

def perp (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (Y : Submodule E (Fin n → E)) :
    Submodule E (Fin n → E) where
  carrier := {x | ∀ y ∈ Y, hf L Hm x y = 0}
  zero_mem' := by intro y _; simp [hf]
  add_mem' := by
    intro a b ha hb y hy
    have h : hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
      simp [hf, add_mul, Finset.sum_add_distrib]
    rw [h, ha y hy, hb y hy, add_zero]
  smul_mem' := by
    intro c a ha y hy
    have h : hf L Hm (c • a) y = c * hf L Hm a y := by
      simp [hf, Finset.mul_sum, mul_assoc]
    rw [h, ha y hy, mul_zero]

def IsLat (L : LocE F E) {n : ℕ} (Λ : Submodule L.O (Fin n → E)) : Prop :=
  Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤

def IsSD (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (Λ : Submodule L.O (Fin n → E)) : Prop :=
  IsLat L Λ ∧ ∀ y, (∀ x ∈ Λ, hf L Hm x y ∈ L.O) ↔ y ∈ Λ

def isomG (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) :
    Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)) where
  carrier := {g | ∀ x y, hf L Hm (g x) (g y) = hf L Hm x y}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb x y
    exact (ha (b x) (b y)).trans (hb x y)
  inv_mem' := by
    intro a ha x y
    have h := ha (a.symm x) (a.symm y)
    simp only [LinearEquiv.apply_symm_apply] at h
    exact h.symm

def unipOn {n : ℕ} (A B : Submodule E (Fin n → E)) : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)) where
  carrier := {g | (∀ v, g v ∈ A ↔ v ∈ A) ∧ ∀ v ∈ A, g v - v ∈ B}
  one_mem' := ⟨fun _ => Iff.rfl, fun v _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun v => (ha (b v)).trans (hb v), fun v hv => ?_⟩
    have h : (a * b) v - v = (a (b v) - b v) + (b v - v) := by simp
    rw [h]
    exact B.add_mem (ha' _ ((hb v).2 hv)) (hb' v hv)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : ∀ v, a.symm v ∈ A ↔ v ∈ A := fun v => by
      have := ha (a.symm v)
      simp only [LinearEquiv.apply_symm_apply] at this
      exact this.symm
    refine ⟨h1, fun v hv => ?_⟩
    have h2 := ha' _ ((h1 v).2 hv)
    simp only [LinearEquiv.apply_symm_apply] at h2
    have h3 : a⁻¹ v - v = -(v - a.symm v) := by
      rw [neg_sub]; rfl
    rw [h3]
    exact B.neg_mem h2

def eich (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x u : Fin n → E) (s : E)
    (v : Fin n → E) : Fin n → E :=
  v + hf L Hm v u • x - hf L Hm v x • (u + s • x)

def invVol {G : Type*} [Group G] (K0 K : Subgroup G) : ℝ :=
  (K.relIndex K0 : ℝ) / (K0.relIndex K : ℝ)

def resQ (ϖ : 𝒪[F]) : ℕ := Nat.card (𝒪[F] ⧸ Ideal.span {ϖ})

def vE (L : LocE F E) (ϖ : 𝒪[F]) (c : E) : ℤ :=
  sSup {m : ℤ | ∃ y ∈ L.O, c = algebraMap F E ((ϖ : F) ^ m) * y}

def lead {N : ℕ} (Z : Matrix (Fin N) (Fin N) E) (l : Fin (N + 1)) : E :=
  (Z.submatrix (Fin.castLE (Nat.lt_succ_iff.mp l.2)) (Fin.castLE (Nat.lt_succ_iff.mp l.2))).det

end GlobalTheory.HL
end
end

section

namespace GlobalTheory.FGDepth

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

variable {C : Type} [Field C]

def toE (x : WithTop ℝ) : EReal := (WithBot.some x : WithBot (WithTop ℝ))

def mfact {σ : Type} (α : σ →₀ ℕ) : C := α.prod fun _ n => (n.factorial : C)

def derivAt0 {σ : Type} (P : MvPolynomial σ C) (g : MvPowerSeries σ C) : C :=
  ∑ α ∈ P.support, P.coeff α * mfact α * coeff α g

def content (v : AddValuation C (WithTop ℝ)) {σ : Type} (P : MvPolynomial σ C) : EReal :=
  ⨅ α ∈ P.support, toE (v (P.coeff α * mfact α))

variable {v : AddValuation C (WithTop ℝ)}

def IsExp {d : ℕ} (G : LogFGL v d) (ex : Fin d → MvPowerSeries (Fin d) C) : Prop :=
  (∀ a, constantCoeff (ex a) = 0) ∧ ∀ a, subst ex (G.lg a) = X a

def expOf {d : ℕ} (G : LogFGL v d) : Fin d → MvPowerSeries (Fin d) C :=
  Classical.epsilon (IsExp G)

def expAlong {κ : Type} {d : κ → ℕ} (G : ∀ b, LogFGL v (d b)) {ι : κ → Type}
    [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C) :
    (Σ b, Fin (d b)) → MvPowerSeries (Σ b, ι b) C :=
  fun x => subst (fun e : Fin (d x.1) =>
    ∑ a, u x.1 a e • (X ⟨x.1, a⟩ : MvPowerSeries (Σ b, ι b) C)) (expOf (G x.1) x.2)

def depth {κ : Type} {d : κ → ℕ} (G : ∀ b, LogFGL v (d b)) {ι : κ → Type}
    [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (P : MvPolynomial (Σ b, ι b) C) : EReal :=
  ⨅ f : {f : MvPowerSeries (Σ b, Fin (d b)) C // MvIsInt v f},
    toE (v (derivAt0 P (subst (expAlong G u) f.1)))

def detPow (C : Type) [Field C] (i c : ℕ) : MvPolynomial (Σ _ : Fin i, Fin i) C :=
  (Matrix.det (Matrix.of fun a b : Fin i =>
    (MvPolynomial.X ⟨b, a⟩ : MvPolynomial (Σ _ : Fin i, Fin i) C))) ^ c

def IsSatFrame (v : AddValuation C (WithTop ℝ)) {i d : ℕ} (u : Fin i → Fin d → C) : Prop :=
  (∀ a e, IsIntV v (u a e)) ∧
    ∃ r : Fin i → Fin d, v (Matrix.det (Matrix.of fun a b => u a (r b))) = 0

def detDepth {i d : ℕ} (G : LogFGL v d) (u : Fin i → Fin d → C) (c : ℕ) : EReal :=
  depth (fun _ : Fin i => G) (fun _ => u) (detPow C i c)

def IsCharLog {d : ℕ} (G : LogFGL v d) (l : Fin d → C) : Prop :=
  ∃ χ : MvPowerSeries (Fin d) C, MvIsInt v χ ∧
    ∀ α, coeff α (subst (expOf G) χ) = α.prod fun e n => l e ^ n / (n.factorial : C)

end

end GlobalTheory.FGDepth
end
