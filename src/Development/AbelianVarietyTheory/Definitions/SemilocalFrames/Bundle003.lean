module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle017
public import Formalism.HermitianLattices.StatementLat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Order.Real
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

def GoodSub {W : Type} [AddCommGroup W] (W0 A : AddSubgroup W) (S : Set W) : Prop :=
  A.relIndex W0 ≠ 0 ∧ W0.relIndex A ≠ 0 ∧ (∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) ∧
    ((QuotientAddGroup.mk : W → W ⧸ A) '' S).Finite

def IsCO {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (S : Set W) : Prop := ∃ A, GoodSub W0 A S

def relVol {W : Type} [AddCommGroup W] (W0 A : AddSubgroup W) : ℝ :=
  (W0.relIndex A : ℝ) / (A.relIndex W0 : ℝ)

def cont {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (S : Set W) : ℝ :=
  if h : IsCO W0 S then
    (((QuotientAddGroup.mk : W → W ⧸ h.choose) '' S).ncard : ℝ) * relVol W0 h.choose else 0

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

def gramT (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x : Fin m → Fin n → E) :
    Matrix (Fin m) (Fin m) E := Matrix.of fun a b => hf L Hm (x b) (x a)

def rmul {n m : ℕ} (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) : Fin m → Fin n → E :=
  fun j => ∑ i, A i j • x i

def IsUni {N : ℕ} (s : Matrix (Fin N) (Fin N) E) : Prop := (∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1

def congK (L : LocE F E) (ϖ : 𝒪[F]) (m i : ℕ) : Set (Matrix (Fin m) (Fin m) E) :=
  {A | ∀ a b, ∃ c ∈ L.O, A a b - (1 : Matrix (Fin m) (Fin m) E) a b = algebraMap F E ((ϖ : F) ^ i) * c}

def thick (L : LocE F E) (ϖ : 𝒪[F]) {n m : ℕ} (Ω : Set (Fin m → Fin n → E)) (i : ℕ) :
    Set (Fin m → Fin n → E) := {x | ∃ y ∈ Ω, ∃ A ∈ congK L ϖ m i, x = rmul y A}

def horb (L : LocE F E) (ϖ : 𝒪[F]) {m : ℕ} (Γ : Matrix (Fin m) (Fin m) E) (i : ℕ) :
    Set (Matrix (Fin m) (Fin m) E) := {X | ∃ A ∈ congK L ϖ m i, X = cT L A * Γ * A}

def tupLat (L : LocE F E) {n : ℕ} (Λ : Submodule L.O (Fin n → E)) (m : ℕ) :
    AddSubgroup (Fin m → Fin n → E) := AddSubgroup.pi Set.univ fun _ => Λ.toAddSubgroup

def hermLat (L : LocE F E) (m : ℕ) : AddSubgroup (Matrix (Fin m) (Fin m) E) :=
  AddSubgroup.closure {X | IsHerm L X ∧ IsIntM L X}

def IsPrimT (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (Λ : Submodule L.O (Fin n → E))
    (x : Fin m → Fin n → E) : Prop :=
  (∀ a, x a ∈ Λ) ∧ ∃ y : Fin m → Fin n → E, (∀ a, y a ∈ Λ) ∧
    ∀ a b, hf L Hm (x a) (y b) = if a = b then 1 else 0

def fixG (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (Y : Submodule E (Fin n → E)) :
    Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)) := isomG L Hm ⊓ unipOn Y ⊥

abbrev stabL (L : LocE F E) {n : ℕ} (Λ : Submodule L.O (Fin n → E)) :
    Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)) := MulAction.stabilizer ((Fin n → E) ≃ₗ[E] (Fin n → E)) Λ

def torb {n m : ℕ} (K : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E))) (x : Fin m → Fin n → E) :
    Set (Fin m → Fin n → E) := {y | ∃ g ∈ K, y = fun a => g (x a)}

def CongId (L : LocE F E) (ϖ : 𝒪[F]) {n : ℕ} (Λ : Submodule L.O (Fin n → E)) (N : ℕ)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) : Prop :=
  ∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = algebraMap F E ((ϖ : F) ^ N) • w

def sigMass (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (Y : Submodule E (Fin n → E))
    (Λ0 Mh : Submodule L.O (Fin n → E)) : ℝ≥0∞ :=
  ∑' o : MulAction.orbitRel.Quotient (fixG L Hm Y) (Submodule L.O (Fin n → E)),
    if IsSD L Hm o.out ∧ o.out ⊓ Y.restrictScalars L.O = Mh then
      ENNReal.ofReal (invVol (fixG L Hm Y ⊓ stabL L Λ0) (fixG L Hm Y ⊓ stabL L o.out)) else 0

def IsQRefl (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a : Fin n → E)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) : Prop :=
  IsUnit (hf L Hm a a) ∧ g ∈ isomG L Hm ∧ ∃ c : E, ∀ v, g v = v + (c * hf L Hm v a) • a

end GlobalTheory.HL
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors

namespace GlobalTheory.SgGlob

variable {E : Type} [Field E] [NumberField E]

abbrev Lz (E : Type) [Field E] (m : ℕ) : Type := Submodule (𝓞 E) (Fin m → E) × (Fin m → E)

def zOf {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Fin n → E := fun i => P i (Fin.last r)

def spanX {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Submodule E (Fin n → E) :=
  LinearMap.range (eOf P).mulVecLin

def perpX (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E) :
    Submodule E (Fin n → E) := LinearMap.ker (cT σ (eOf P) * J).mulVecLin

def latIn {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (S : Submodule E (Fin n → E)) :
    Submodule (𝓞 E) (Fin n → E) := Λ ⊓ S.restrictScalars (𝓞 E)

def mulLat {n : ℕ} (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) :=
  Λ.map ((g : 𝓞 E) • LinearMap.id)

def IsRed (σ : E →+* E) {n m r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Jb : Matrix (Fin m) (Fin m) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) (x : Lz E m)
    (al : Matrix (Fin m) (Fin n) E) : Prop :=
  (∀ v ∈ perpX σ J P, al *ᵥ v = 0 ↔ v ∈ spanX P) ∧
  (∀ y, ∃ v ∈ perpX σ J P, al *ᵥ v = y) ∧
  (∀ v ∈ perpX σ J P, ∀ w ∈ perpX σ J P, form σ Jb (al *ᵥ v) (al *ᵥ w) = form σ J v w) ∧
  (latIn Λ (perpX σ J P)).map (al.mulVecLin.restrictScalars (𝓞 E)) = x.1 ∧
  al *ᵥ zOf P = x.2

def UO (E : Type) [Field E] [NumberField E] (r : ℕ) : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E) :=
  {u | IsUp u ∧ ∀ a b : Fin (r + 1), a < b → u a b ∈ dInv E ((b : ℕ) - a)}

section Basic

variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}



omit [NumberField E] in
theorem mem_perpX (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    v ∈ perpX σ J P ↔ (cT σ (eOf P) * J) *ᵥ v = 0 := Iff.rfl


omit [NumberField E] in
theorem mem_perpX_iff_form (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    v ∈ perpX σ J P ↔ ∀ a : Fin r, form σ J v (fun i => P i a.castSucc) = 0 := by
  rw [mem_perpX, ← Matrix.mulVec_mulVec, funext_iff]
  rfl




omit [NumberField E] in
theorem mem_latMap (γ : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E) :
    v ∈ latMap γ Λ ↔ ∃ w ∈ Λ, γ *ᵥ w = v := Iff.rfl









end Basic

section Iota

variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}

end Iota

section Iso

variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}



omit [NumberField E] in
theorem isUn_mul {γ δ : Matrix (Fin n) (Fin n) E} (hγ : IsUn σ J γ) (hδ : IsUn σ J δ) :
    IsUn σ J (γ * δ) := by
  have e : cT σ (γ * δ) = cT σ δ * cT σ γ := by rw [cT, Matrix.map_mul, Matrix.transpose_mul]; rfl
  rw [IsUn, e, show cT σ δ * cT σ γ * J * (γ * δ) = cT σ δ * (cT σ γ * J * γ) * δ by
    simp only [Matrix.mul_assoc], hγ, hδ]


theorem latMap_one (Λ : Submodule (𝓞 E) (Fin n → E)) : latMap 1 Λ = Λ := by
  ext v
  simp [mem_latMap]

theorem latMap_mul (γ δ : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    latMap (γ * δ) Λ = latMap γ (latMap δ Λ) := by
  rw [latMap, latMap, latMap, ← Submodule.map_comp, Matrix.mulVecLin_mul]
  rfl

end Iso

section Unip

variable {n r : ℕ}

end Unip

section Examples

variable {σ : E →+* E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

end Examples

end GlobalTheory.SgGlob
end
end

section

noncomputable section
open scoped Classical

namespace GlobalTheory.IdxInt.Model
open GlobalTheory.IdxInt

variable {W : Type} [AddCommGroup W]

lemma out_mk {φ : W → ℂ} {B : AddSubgroup W} (h : ∀ w, ∀ b ∈ B, φ (w + b) = φ w) (w : W) :
    φ (QuotientAddGroup.mk w : W ⧸ B).out = φ w := by
  obtain ⟨b, hb⟩ := QuotientAddGroup.mk_out_eq_add B w
  rw [hb]; exact h w b b.2

lemma sum_refine {A B C : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) (hC : C ≤ B)
    (hi : C.relIndex B ≠ 0) :
    (∑ᶠ c : W ⧸ C, φ c.out) = (C.relIndex B : ℂ) * ∑ᶠ c : W ⧸ B, φ c.out := by
  first
  | exact @_root_.GlobalTheory.SumRefinement.sum_refine
  | exact _root_.GlobalTheory.SumRefinement.sum_refine
  | (apply _root_.GlobalTheory.SumRefinement.sum_refine <;> assumption)
  | (intros; apply _root_.GlobalTheory.SumRefinement.sum_refine <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SumRefinement.sum_refine <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SumRefinement.sum_refine ..)

lemma ratio_eq {A B B' : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) (h' : Fine A φ B') :
    (∑ᶠ c : W ⧸ B, φ c.out) / (B.relIndex A : ℂ) = (∑ᶠ c : W ⧸ B', φ c.out) / (B'.relIndex A : ℂ) := by
  have hC : (B ⊓ B').relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero h.2.1 h'.2.1
  have m1 := AddSubgroup.relIndex_mul_relIndex (B ⊓ B') B A inf_le_left h.1
  have m2 := AddSubgroup.relIndex_mul_relIndex (B ⊓ B') B' A inf_le_right h'.1
  have i1 : (B ⊓ B').relIndex B ≠ 0 := fun z => hC (by rw [← m1, z, zero_mul])
  have i2 : (B ⊓ B').relIndex B' ≠ 0 := fun z => hC (by rw [← m2, z, zero_mul])
  have s1 := sum_refine h inf_le_left i1
  have s2 := sum_refine h' inf_le_right i2
  have c1 : (B.relIndex A : ℂ) ≠ 0 := by exact_mod_cast h.2.1
  have c2 : (B'.relIndex A : ℂ) ≠ 0 := by exact_mod_cast h'.2.1
  have c3 : (((B ⊓ B').relIndex B : ℕ) : ℂ) ≠ 0 := by exact_mod_cast i1
  have c4 : (((B ⊓ B').relIndex B' : ℕ) : ℂ) ≠ 0 := by exact_mod_cast i2
  have m : (((B ⊓ B').relIndex B : ℕ) : ℂ) * (B.relIndex A : ℂ) = (((B ⊓ B').relIndex B' : ℕ) : ℂ) * (B'.relIndex A : ℂ) := by
    exact_mod_cast m1.trans m2.symm
  rw [← mul_div_mul_left _ _ c3, ← s1, ← mul_div_mul_left (∑ᶠ c : W ⧸ B', φ c.out) _ c4, ← s2, m]

theorem cint_eq {A B : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) :
    cint A φ = (∑ᶠ c : W ⧸ B, φ c.out) / (B.relIndex A : ℂ) := by
  have hn : Nice A φ := ⟨B, h⟩
  rw [cint, dite_eq_left hn]
  exact ratio_eq hn.choose_spec h

lemma fine_refine {A B C : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) (hC : C ≤ B)
    (hi : C.relIndex A ≠ 0) : Fine A φ C := by
  have m1 := AddSubgroup.relIndex_mul_relIndex C B A hC h.1
  have i1 : C.relIndex B ≠ 0 := fun z => hi (by rw [← m1, z, zero_mul])
  haveI : Finite (B ⧸ C.addSubgroupOf B) := Nat.finite_of_card_ne_zero i1
  refine ⟨hC.trans h.1, hi, fun w b hb => h.2.2.1 w b (hC hb), ?_⟩
  let e := AddSubgroup.quotientEquivProdOfLE hC
  refine ((h.2.2.2.prod (Set.finite_univ (α := B ⧸ C.addSubgroupOf B))).preimage
    e.injective.injOn).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨⟨w, hw, rfl⟩, trivial⟩

end GlobalTheory.IdxInt.Model
end
end

section

noncomputable section

open NumberField Matrix
open scoped ENNReal Classical

namespace GlobalTheory.Mass

def orbSum (G : Type*) [Group G] {α : Type*} [MulAction G α] (X : Set α) (N : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
    ((ENat.card (MulAction.stabilizer G (Quotient.out q.1)) : ℕ∞) : ℝ≥0∞)⁻¹ * N (Quotient.out q.1)

def orbMass (G : Type*) [Group G] {α : Type*} [MulAction G α] (X : Set α) : ℝ≥0∞ :=
  orbSum G X fun _ => 1

def Stable (G : Type*) [Group G] {α : Type*} [MulAction G α] (X : Set α) : Prop :=
  ∀ (g : G), ∀ x ∈ X, g • x ∈ X

section Act

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

instance latAct (h : V →ₗ⋆[K] V →ₗ[K] K) : MulAction (Formalism.HermitianLatticesTheory.isom h) (Submodule R V) where
  smul g L := Formalism.HermitianLatticesTheory.gmap (g : V ≃ₗ[K] V) L
  one_smul L := by
    ext x
    change x ∈ Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) L ↔ _
    simp [Formalism.HermitianLatticesTheory.gmap]
  mul_smul a b L := by
    ext x
    change x ∈ Formalism.HermitianLatticesTheory.gmap ((a : V ≃ₗ[K] V) * (b : V ≃ₗ[K] V)) L ↔
      x ∈ Formalism.HermitianLatticesTheory.gmap (a : V ≃ₗ[K] V) (Formalism.HermitianLatticesTheory.gmap (b : V ≃ₗ[K] V) L)
    simp [Formalism.HermitianLatticesTheory.gmap]

def primeTo (d : R) : Submonoid R where
  carrier := {s | ∀ P : Ideal R, P.IsMaximal → d ∈ P → s ∉ P}
  one_mem' := fun P hP _ h1 => hP.ne_top ((Ideal.eq_top_iff_one P).2 h1)
  mul_mem' := fun ha hb P hP hd hab =>
    (hP.isPrime.mem_or_mem hab).elim (ha P hP hd) (hb P hP hd)

def idxN {W : Type*} [AddCommGroup W] [Module R W] (A B : Submodule R W) : ℕ :=
  B.toAddSubgroup.relIndex A.toAddSubgroup

def discN (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule R V) : ℕ := idxN (Formalism.HermitianLatticesTheory.dual h M) M

def IsIntLat (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule R V) : Prop :=
  Submodule.IsFullLattice K M ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h M

def IsMaxLat (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule R V) : Prop :=
  IsIntLat h M ∧ ∀ N : Submodule R V, IsIntLat h N → M ≤ N → N = M

def badP (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule R V) : Set (Ideal R) :=
  {P | P.IsMaximal ∧ ¬ Formalism.HermitianLatticesTheory.IsUnimodularAt h P M}

def hRes (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) : U →ₗ⋆[K] U →ₗ[K] K := h.domRestrict₁₂ U U

def latIn (U : Submodule K V) (M : Submodule R V) : Submodule R U :=
  M.comap (U.subtype.restrictScalars R)

def perp (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) : Submodule K V := ⨅ x ∈ U, LinearMap.ker (h x)

def latsDisc (h : V →ₗ⋆[K] V →ₗ[K] K) (n : ℕ) : Set (Submodule R V) :=
  {M | IsIntLat h M ∧ discN h M = n}

def primSp (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) (j n : ℕ) : Set (Submodule K V) :=
  {U | Module.finrank K U = j ∧ discN (hRes h U) (latIn U L) = n}

end Act

def PD {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ τ : K →+* ℂ, ∀ x : V, x ≠ 0 → 0 < (τ (h x x)).re

def qIn {K : Type*} [Field K] [NumberField K] (P : Ideal (𝓞 K)) : ℕ := Nat.sqrt (Ideal.absNorm P)

def lamMax {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V) : ℝ :=
  ∏ᶠ P ∈ badP h M, ((qIn P : ℝ) ^ Module.finrank K V - (-1) ^ Module.finrank K V) / ((qIn P : ℝ) + 1)

end GlobalTheory.Mass
end
end
