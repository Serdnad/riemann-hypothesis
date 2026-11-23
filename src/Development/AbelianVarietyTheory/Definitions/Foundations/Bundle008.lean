module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
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
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.ZMod.Units

@[expose] public section

section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ

def slP {R : Type} [CommRing R] (m : Matrix (Fin 2) (Fin 2) ℤ) : MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  MvPolynomial.aeval fun i => (m i 0 : R) • MvPolynomial.X 0 + (m i 1 : R) • MvPolynomial.X 1

def Pot (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)) : Set (ℂ → MvPolynomial (Fin 2) R) :=
  {F | (∀ z, (F z).IsHomogeneous w) ∧ ∀ γ ∈ Γ, ∃ p, ∀ z ∈ Hs,
    slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) z)) - F z = p}

def Triv (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)) : Set (ℂ → MvPolynomial (Fin 2) R) :=
  {F | ∃ (ψ : ℂ → MvPolynomial (Fin 2) R) (p : MvPolynomial (Fin 2) R),
    (∀ γ ∈ Γ, ∀ z ∈ Hs, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (ψ (mob (ofSL γ) z)) = ψ z) ∧ ∀ z ∈ Hs, F z = ψ z + p}

def opP (R : Type) [CommRing R] (m : Matrix (Fin 2) (Fin 2) ℤ) :
    (ℂ → MvPolynomial (Fin 2) R) →ₗ[R] (ℂ → MvPolynomial (Fin 2) R) where
  toFun F z := slP m (F (mob (toGQ m) z))
  map_add' F G := by funext z; simp
  map_smul' c F := by funext z; simp

def opL (R : Type) [CommRing R] (N l : ℕ) :
    Letter → ((ℂ → MvPolynomial (Fin 2) R) →ₗ[R] (ℂ → MvPolynomial (Fin 2) R))
  | Letter.T q => (∑ j ∈ Finset.range q, opP R !![1, (j : ℤ); 0, (q : ℤ)]) +
      opP R ((sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])
  | Letter.U => ∑ j ∈ Finset.range l, opP R !![1, (j : ℤ); 0, (l : ℤ)]
  | Letter.D d => opP R (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ)

def admitted (N l : ℕ) : Letter → Prop
  | Letter.T q => q.Prime ∧ ¬ q ∣ N * l
  | Letter.U => True
  | Letter.D d => Nat.Coprime d N

def LetAlg (R : Type) [CommRing R] (S : Letter → Prop) : Subalgebra R (FreeAlgebra R Letter) :=
  Algebra.adjoin R (FreeAlgebra.ι R '' {T | S T})

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def FrobAt (q : ℕ) (s : Ω ≃ₐ[ℚ] Ω) : Prop :=
  ∃ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits ∧ ∀ x ∈ V, s x ∈ V ∧ V.valuation (s x - x ^ q) < 1

def Tower.VB (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] :
    Submodule E (E ⊗[ℤ_[l]] X.Fn l) :=
  LinearMap.range (LinearMap.baseChange E (X.B N l w).subtype)

def Tower.opV (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] (T : Letter) :
    Module.End E (E ⊗[ℤ_[l]] X.Fn l) :=
  LinearMap.baseChange E (X.op N l T)

def Tower.galV (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] (s : Ω ≃ₐ[ℚ] Ω) :
    Module.End E (E ⊗[ℤ_[l]] X.Fn l) :=
  LinearMap.baseChange E (X.galB l s)

namespace Betti

section Letters

variable {R : Type} [CommRing R] {S : Letter → Prop}

theorem lift_congr {A : Type} [Semiring A] [Algebra R A] {f g : Letter → A} (h : ∀ T, S T → f T = g T)
    {P : FreeAlgebra R Letter} (hP : P ∈ LetAlg R S) : FreeAlgebra.lift R f P = FreeAlgebra.lift R g P := by
  unfold LetAlg at hP
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    simp [h T hT]
  | algebraMap r => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | mul x y _ _ hx hy => simp [hx, hy]

end Letters

theorem exists_isDiam {N l d : ℕ} (hN : N ≠ 0) (hl : l ≠ 0) (hd : Nat.Coprime d N) : ∃ γ, IsDiam N l d γ := by
  have : NeZero (N * l) := ⟨Nat.mul_ne_zero hN hl⟩
  have hNl : N ∣ N * l := Dvd.intro l rfl
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hNl (ZMod.unitOfCoprime d hd)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime u)
  have hdet : (!![a, -b; ((N * l : ℕ) : ℤ), ((u : ZMod (N * l)).val : ℤ)]).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hab
  obtain ⟨γ, hγ⟩ : ∃ γ : SL(2, ℤ),
      (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, -b; ((N * l : ℕ) : ℤ), ((u : ZMod (N * l)).val : ℤ)] :=
    ⟨⟨_, hdet⟩, rfl⟩
  refine ⟨γ, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem, hγ]
    simp
  · rw [CongruenceSubgroup.Gamma0_mem, hγ]
    simp
  · have hcast : (((u : ZMod (N * l)).val : ℕ) : ZMod N) = d := by
      rw [ZMod.natCast_val, ← ZMod.unitsMap_val hNl, hu, ZMod.coe_unitOfCoprime]
    simpa [en, hγ] using hcast

theorem isDiam_sgD {N l d : ℕ} (hN : N ≠ 0) (hl : l ≠ 0) (hd : Nat.Coprime d N) : IsDiam N l d (sgD N l d) := by
  exact Classical.epsilon_spec (exists_isDiam hN hl hd)

theorem isDiam_sgD_of_adm {N l q : ℕ} (h : admitted N l (Letter.T q)) : IsDiam N l q (sgD N l q) := by
  have h' : q.Prime ∧ ¬ q ∣ N * l := h
  obtain ⟨hq, hqN⟩ := h'
  have hN : N ≠ 0 := by
    rintro rfl
    exact hqN (by simp)
  have hl : l ≠ 0 := by
    rintro rfl
    exact hqN (by simp)
  exact isDiam_sgD hN hl ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h'' => hqN (h''.mul_right l))

section Slash

variable {R : Type} [CommRing R]

theorem slP_X (m : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) :
    slP (R := R) m (MvPolynomial.X i) = (m i 0 : R) • MvPolynomial.X 0 + (m i 1 : R) • MvPolynomial.X 1 := by
  simp only [slP, MvPolynomial.aeval_X]

theorem polySlash_one (p : MvPolynomial (Fin 2) R) : slP 1 p = p := by
  have h1 : slP (R := R) 1 = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [slP_X]
    fin_cases i <;> simp [Matrix.one_apply]
  rw [h1, AlgHom.id_apply]

theorem polySlash_polySlash (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R) :
    slP m' (slP m p) = slP (m * m') p := by
  have h1 : (slP m').comp (slP m) = slP (R := R) (m * m') := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, slP_X, map_add (f := _), map_smul, Matrix.mul_apply, Fin.sum_univ_two,
      Int.cast_add, Int.cast_mul]
    module
  exact DFunLike.congr_fun h1 p

theorem polySlash_isHomogeneous (m : Matrix (Fin 2) (Fin 2) ℤ) {p : MvPolynomial (Fin 2) R} {w : ℕ} (hp : p.IsHomogeneous w) :
    (slP m p).IsHomogeneous w := by
  have h1 := hp.aeval (fun i => (m i 0 : R) • MvPolynomial.X 0 + (m i 1 : R) • MvPolynomial.X 1)
    (n := 1) fun i => (MvPolynomial.homogeneousSubmodule (Fin 2) R 1).add_mem
      ((MvPolynomial.homogeneousSubmodule (Fin 2) R 1).smul_mem _ (MvPolynomial.isHomogeneous_X R 0))
      ((MvPolynomial.homogeneousSubmodule (Fin 2) R 1).smul_mem _ (MvPolynomial.isHomogeneous_X R 1))
  rw [one_mul] at h1
  exact h1

theorem eval_slP (m : Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2 → R) (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.eval u (slP m p) = MvPolynomial.eval (m.map (Int.castRingHom R) *ᵥ u) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, slP_X, MvPolynomial.eval_X, map_add (f := _), MvPolynomial.smul_eval]
    congr 1
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem toGQ_sl (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  have h : 0 < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by
    rw [Matrix.SpecialLinearGroup.det_coe]
    exact one_pos
  unfold toGQ
  rw [dite_eq_left h]
  apply Subtype.ext
  apply Units.ext
  rfl

variable {w : ℕ} {Γ : Subgroup SL(2, ℤ)}

def potSub (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)) : Submodule R (ℂ → MvPolynomial (Fin 2) R) where
  carrier := Pot R w Γ
  zero_mem' := ⟨fun _ => MvPolynomial.isHomogeneous_zero _ _ _, fun _ _ => ⟨0, fun _ _ => by simp⟩⟩
  add_mem' := by
    rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    refine ⟨fun z => (hF z).add (hG z), fun γ hγ => ?_⟩
    obtain ⟨p, hp⟩ := hF' γ hγ
    obtain ⟨q, hq⟩ := hG' γ hγ
    refine ⟨p + q, fun z hz => ?_⟩
    rw [← hp z hz, ← hq z hz]; simp only [Pi.add_apply, map_add (f := _)]; ring
  smul_mem' := by
    rintro c F ⟨hF, hF'⟩
    refine ⟨fun z => (MvPolynomial.homogeneousSubmodule (Fin 2) R w).smul_mem c (hF z), fun γ hγ => ?_⟩
    obtain ⟨p, hp⟩ := hF' γ hγ
    refine ⟨c • p, fun z hz => ?_⟩
    rw [← hp z hz]; simp only [Pi.smul_apply, map_smul, smul_sub]

end Slash

end Betti

end GlobalTheory.KZ
end
end

section

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc

namespace GlobalTheory.HL.Model

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_add_left (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L H (a + b) y = hf L H a y + hf L H b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_smul_left (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L H (c • a) y = c * hf L H a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_add_right (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L H y (a + b) = hf L H y a + hf L H y b := by
  simp [hf, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem hf_smul_right (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L H y (c • a) = L.cj c * hf L H y a := by
  unfold hf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem hf_symm (L : LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E} (h : IsHerm L H)
    (x y : Fin n → E) : hf L H y x = L.cj (hf L H x y) := by
  have hH : ∀ i j, L.cj (H j i) = H i j := fun i j => congrFun (congrFun h i) j
  unfold hf

  simp only [map_sum, map_mul, L.cj_cj, hH]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def stdLat (L : LocE F E) (n : ℕ) : Submodule L.O (Fin n → E) :=
  Submodule.span L.O (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → E))

theorem nontrivial (L : LocE F E) : Nontrivial E := by
  exact Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)

end GlobalTheory.HL.Model
end
end

section

open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.RootEx.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem inN_tri {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : InN p g) : g.val.BlockTriangular (lev p) := by
  intro r s h
  rw [hg r s h.le, Matrix.one_apply_ne]
  rintro rfl; exact lt_irrefl _ h

theorem mul_entry {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : InN p g) {h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k}
    (hh : h.BlockTriangular (lev p)) (r s) (hrs : lev p s ≤ lev p r) : (g.val * h) r s = h r s := by
  have : (g.val * h) r s = ((1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * h) r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : lev p t ≤ lev p r
    · rw [hg r t ht]
    · rw [hh (show lev p s < lev p t by omega)]; simp
  rw [this, Matrix.one_mul]

def Nsub (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c p : ℕ) : Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | InN p g}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun {a b} ha hb r s hrs => by
    rw [Units.val_mul, mul_entry ha (inN_tri hb) r s hrs, hb r s hrs]
  inv_mem' := fun {a} ha r s hrs => by
    have h1 : (a⁻¹).val.BlockTriangular (lev p) := by
      rw [Matrix.coe_units_inv]
      haveI := a.invertible
      exact Matrix.blockTriangular_inv_of_blockTriangular (inN_tri ha)
    rw [← mul_entry ha h1 r s hrs, Units.mul_inv]

theorem mem_N_iff {p : ℕ} {g : GL (n ⊕ Fin c) k} : g ∈ N k n c p ↔ InN p g := by
  have : N k n c p = Nsub k n c p := Subgroup.closure_eq (Nsub k n c p)
  rw [this]; rfl

theorem conj_mem {p : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) (g : GL n k) :
    (embX c g)⁻¹ * u * embX c g ∈ N k n c p := by
  rw [mem_N_iff] at hu ⊢
  rw [← map_inv]
  have h11 : u.val.toBlocks₁₁ = 1 := by
    ext r s
    have := hu (Sum.inl r) (Sum.inl s) le_rfl
    simpa [Matrix.one_apply, toBlocks₁₁] using this
  have hv : ((embX c g⁻¹) * u * embX c g).val = fromBlocks 1 ((g⁻¹).val * u.val.toBlocks₁₂)
      (u.val.toBlocks₂₁ * g.val) u.val.toBlocks₂₂ := by
    rw [Units.val_mul, Units.val_mul, ← fromBlocks_toBlocks u.val, h11]
    simp [embX, fromBlocks_multiply]
  rintro (r | r) (s | s) h <;> rw [hv]
  · simp [Matrix.one_apply]
  · have : ∀ t, u.val (Sum.inl t) (Sum.inr s) = 0 := fun t => by
      simpa using hu (Sum.inl t) (Sum.inr s) h
    simp [Matrix.mul_apply, toBlocks₁₂, this]
  · have : ∀ t, u.val (Sum.inr r) (Sum.inl t) = 0 := fun t => by
      simpa using hu (Sum.inr r) (Sum.inl t) h
    simp [Matrix.mul_apply, toBlocks₂₁, this]
  · simpa [toBlocks₂₂] using hu (Sum.inr r) (Sum.inr s) h

def mkN (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} → k) :
    Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
  Matrix.of fun r s => if h : lev p r < lev p s then e ⟨(r, s), h⟩ else (1 : Matrix _ _ k) r s

theorem det_mkN (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} → k) :
    (mkN p e).det = 1 := by
  have ht : (mkN p e).BlockTriangular (lev p) := by
    intro r s h
    have : r ≠ s := by rintro rfl; exact lt_irrefl _ h
    simp [mkN, not_lt.2 h.le, this]
  rw [ht.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : (mkN p e).toSquareBlock (lev p) a = 1 := by
    ext ⟨r, hr⟩ ⟨s, hs⟩
    simp [toSquareBlock_def, mkN, hr, hs, Matrix.one_apply]
  rw [this, det_one]

def mkNel (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} → k) : N k n c p :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (mkN p e) (by rw [det_mkN]; exact one_ne_zero), by
    rw [mem_N_iff]
    intro r s h
    show mkN p e r s = _
    simp [mkN, not_lt.2 h]⟩

section meas
variable [MeasurableSpace k]

theorem coord_embedding (p : ℕ) : MeasurableEmbedding
    (fun (g : N k n c p) (rs : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2}) =>
      (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) ∧ Function.Surjective
    (fun (g : N k n c p) (rs : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2}) =>
      (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) := by
  have hs : Function.Surjective
      (fun (g : N k n c p) (rs : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2}) =>
      (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) := by
    intro e
    refine ⟨mkNel p e, ?_⟩
    funext rs
    show mkN p e _ _ = _
    simp [mkN, rs.2]
  refine ⟨MeasurableEmbedding.of_measurable_inverse (g := mkNel (k := k) p) ?_ ?_ ?_ ?_, hs⟩
  · refine Measurable.of_eval fun rs => ?_
    have h1 : Measurable (fun g : GL (n ⊕ Fin c) k => g.val) := comap_measurable _
    have h2 : Measurable (fun m : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k => m rs.1.1 rs.1.2) :=
      (measurable_pi_apply rs.1.2).comp (measurable_pi_apply rs.1.1)
    exact h2.comp (h1.comp measurable_subtype_coe)
  · rw [hs.range_eq]; exact MeasurableSet.univ
  · refine Measurable.subtype_mk ?_
    refine measurable_comap_iff.2 ?_
    refine Measurable.of_eval fun r => Measurable.of_eval fun s => ?_
    show Measurable fun e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} → k => mkN (k := k) p e r s
    by_cases h : lev p r < lev p s
    · simp only [mkN, Matrix.of_apply, dif_pos h]; exact measurable_pi_apply _
    · simp only [mkN, Matrix.of_apply, dif_neg h]; exact measurable_const
  · intro g
    ext r s
    show mkN (k := k) p (fun rs => (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) r s = _
    by_cases h : lev p r < lev p s
    · simp [mkN, h]
    · simp only [mkN, Matrix.of_apply, dif_neg h]
      exact (mem_N_iff.1 g.2 r s (not_lt.1 h)).symm

end meas

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


end GlobalTheory.RootEx.Model
end
end
