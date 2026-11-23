module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle261
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle245
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GlobalTheory.Proof.LocalGlobalSelmer

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Cut

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i) (k : ℕ) (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)), InR' D.nd r S 1 → UnrOut i r Xs → ∀ v, v ∉ placesOver D.host.E (D.nd.l i) → v ∉ D.nd.S i → v ∉ D.nd.Q i → resIne i (cocW i r S Xs ψ) v = ⊥ := by
  intro D i r Xs S k ψ hone hU v h1 h2 h3
  have hY : ∀ γ, InY D.nd r S (yg D.nd r S γ) := fun γ =>
    ⟨1, fun _ => 1, fun _ => γ, fun _ => hone, by simp⟩
  have hy : ∀ γ x', yg D.nd r S γ x' = (rTwO D.nd i r (S.p x') γ - 1) * Eel D.nd S x' := by
    intro γ x'
    simp [yg, rTwO, twistM, sub_mul]
  rw [resIne, cocW, Submodule.map_span, Submodule.span_eq_bot]
  rintro _ ⟨_, ⟨φ, -, h0, rfl⟩, rfl⟩
  funext γ
  exact h0 _ (hY γ.1) fun x' hx => by rw [hy, hU v h1 h2 h3 _ hx γ.1 γ.2]; simp

end GlobalTheory.Proof.LocalGlobalSelmer
end

section

open Polynomial

namespace GlobalTheory.GLq.LabelModel
theorem lift {F : Type} [Field F] {m M : ℕ} (hM : 0 < M) (hm : m ∣ M) {ξ ζ : F} (hξ : IsPrimitiveRoot ξ M)
    (hζ : IsPrimitiveRoot ζ m) : ∃ ξ' : F, IsPrimitiveRoot ξ' M ∧ ξ' ^ (M / m) = ζ := by
  obtain ⟨c, rfl⟩ := hm
  have hm0 : 0 < m := Nat.pos_of_mul_pos_right hM
  haveI : NeZero m := ⟨hm0.ne'⟩
  haveI : NeZero (m * c) := ⟨hM.ne'⟩
  have hη : IsPrimitiveRoot (ξ ^ c) m := hξ.pow hM (mul_comm _ _)
  obtain ⟨a, -, hac, ha⟩ := (hη.isPrimitiveRoot_iff).1 hζ
  obtain ⟨U, hU⟩ := ZMod.unitsMap_surjective (n := m) (m := m * c) (Dvd.intro _ rfl) (ZMod.unitOfCoprime a hac)
  refine ⟨ξ ^ (U : ZMod (m * c)).val, hξ.pow_of_coprime _ (ZMod.val_coe_unit_coprime U), ?_⟩
  rw [Nat.mul_div_cancel_left _ hm0, ← pow_mul, mul_comm, pow_mul, ← ha]
  have h1 : (((U : ZMod (m * c)).val : ℕ) : ZMod m) = (a : ZMod m) := by
    have := congrArg (fun u : (ZMod m)ˣ => (u : ZMod m)) hU
    simpa [ZMod.unitsMap_val] using this
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
  rw [pow_eq_pow_mod _ hη.pow_eq_one, pow_eq_pow_mod a hη.pow_eq_one, h2]

variable (g : ℕ) [hg : Fact g.Prime]

theorem pos {d : ℕ} (hd : 0 < d) : 0 < g ^ d - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' hg.out.one_lt)

theorem dv {d e : ℕ} (h : d ∣ e) : g ^ d - 1 ∣ g ^ e - 1 := Nat.pow_sub_one_dvd_pow_sub_one g h

theorem exprim {d : ℕ} (hd : 0 < d) : ∃ ξ : Formalism.CyclotomicNorms.Fbar g, IsPrimitiveRoot ξ (g ^ d - 1) := by
  haveI : NeZero (((g ^ d - 1 : ℕ)) : Formalism.CyclotomicNorms.Fbar g) := ⟨by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hg.out.pos), Nat.cast_pow, CharP.cast_eq_zero (Formalism.CyclotomicNorms.Fbar g) g, zero_pow hd.ne']
    simp⟩
  haveI : NeZero (g ^ d - 1) := ⟨(pos g hd).ne'⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot _ _

theorem chain : ∃ z : ℕ → Formalism.CyclotomicNorms.Fbar g, ∀ n, IsPrimitiveRoot (z n) (g ^ n.factorial - 1) ∧
    z (n+1) ^ ((g ^ (n+1).factorial - 1) / (g ^ n.factorial - 1)) = z n := by
  have step : ∀ n (x : {x : Formalism.CyclotomicNorms.Fbar g // IsPrimitiveRoot x (g ^ n.factorial - 1)}),
      ∃ y : {x : Formalism.CyclotomicNorms.Fbar g // IsPrimitiveRoot x (g ^ (n+1).factorial - 1)},
        y.1 ^ ((g ^ (n+1).factorial - 1) / (g ^ n.factorial - 1)) = x.1 := by
    intro n x
    obtain ⟨ξ, hξ⟩ := exprim g (Nat.factorial_pos (n+1))
    obtain ⟨y, hy, hy'⟩ := lift (pos g (Nat.factorial_pos (n+1))) (dv g (Nat.factorial_dvd_factorial (Nat.le_succ n))) hξ x.2
    exact ⟨⟨y, hy⟩, hy'⟩
  choose f hf using step
  obtain ⟨x0, hx0⟩ := exprim g (Nat.factorial_pos 0)
  let s : ∀ n : ℕ, {x : Formalism.CyclotomicNorms.Fbar g // IsPrimitiveRoot x (g ^ n.factorial - 1)} :=
    fun n => Nat.rec ⟨x0, hx0⟩ (fun n x => f n x) n
  exact ⟨fun n => (s n).1, fun n => ⟨(s n).2, hf n (s n)⟩⟩

theorem divmul {a b c : ℕ} (h1 : a ∣ b) (h2 : b ∣ c) (hb : 0 < b) : c / b * (b / a) = c / a := by
  obtain ⟨u, rfl⟩ := h1
  obtain ⟨v, rfl⟩ := h2
  have ha : 0 < a := Nat.pos_of_mul_pos_right hb
  rw [Nat.mul_div_cancel_left _ hb, Nat.mul_div_cancel_left _ ha, mul_assoc, Nat.mul_div_cancel_left _ ha, mul_comm]

theorem gensys : ∃ ζ : ℕ → Formalism.CyclotomicNorms.Fbar g, ∀ d, 0 < d → IsPrimitiveRoot (ζ d) (g ^ d - 1) ∧
    ∀ d', d ∣ d' → 0 < d' → ζ d' ^ ((g ^ d' - 1) / (g ^ d - 1)) = ζ d := by
  obtain ⟨z, hz⟩ := chain g
  have hc : ∀ n k, z (n + k) ^ ((g ^ (n+k).factorial - 1) / (g ^ n.factorial - 1)) = z n := by
    intro n k
    induction k with
    | zero => simp [Nat.div_self (pos g (Nat.factorial_pos n))]
    | succ k ih =>
      rw [← ih, ← (hz (n+k)).2, ← pow_mul, ← add_assoc,
        divmul (dv g (Nat.factorial_dvd_factorial (Nat.le_add_right n k)))
          (dv g (Nat.factorial_dvd_factorial (Nat.le_succ _))) (pos g (Nat.factorial_pos _))]
  refine ⟨fun d => z d ^ ((g ^ d.factorial - 1) / (g ^ d - 1)), fun d hd => ⟨?_, fun d' hdd hd' => ?_⟩⟩
  · exact (hz d).1.pow (pos g (Nat.factorial_pos _)) (Nat.div_mul_cancel (dv g (Nat.dvd_factorial hd le_rfl))).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_dvd hd' hdd)
    beta_reduce
    rw [← hc d k, ← pow_mul, ← pow_mul,
      divmul (dv g hdd) (dv g (Nat.dvd_factorial hd' le_rfl)) (pos g hd'),
      divmul (dv g (Nat.dvd_factorial hd le_rfl)) (dv g (Nat.factorial_dvd_factorial (Nat.le_add_right d k))) (pos g (Nat.factorial_pos _))]

theorem level (x : Formalism.CyclotomicNorms.Fbar g) (hx : x ≠ 0) : ∃ d, 0 < d ∧ x ^ (g ^ d - 1) = 1 := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  let K := IntermediateField.adjoin (ZMod g) {x}
  haveI : FiniteDimensional (ZMod g) K := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = g ^ Module.finrank (ZMod g) K := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card]
  let y : K := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have := FiniteField.pow_card_sub_one_eq_one y hy
  rw [hcard] at this
  exact ⟨_, Module.finrank_pos, by simpa [y] using congrArg Subtype.val this⟩

noncomputable def E (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((g ^ d - 1 : ℕ) : ℂ))

theorem E_prim {d : ℕ} (hd : 0 < d) : IsPrimitiveRoot (E g d) (g ^ d - 1) :=
  Complex.isPrimitiveRoot_exp _ (pos g hd).ne'

theorem E_pow {d d' : ℕ} (h : d ∣ d') (hd : 0 < d) (hd' : 0 < d') : E g d' ^ ((g ^ d' - 1) / (g ^ d - 1)) = E g d := by
  obtain ⟨c, hc⟩ := dv g h
  have h1 := pos g hd
  have h2 := pos g hd'
  have hc0 : c ≠ 0 := by rintro rfl; omega
  unfold E
  rw [← Complex.exp_nat_mul, hc, Nat.mul_div_cancel_left _ h1]
  congr 1
  have : ((g ^ d - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h1.ne'
  have : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc0
  rw [Nat.cast_mul]
  field_simp

theorem prim_iff {R : Type} [CommMonoid R] {z : R} {m : ℕ} (h : IsPrimitiveRoot z m) (hm : 0 < m) (a b : ℕ) :
    z ^ a = z ^ b ↔ a ≡ b [MOD m] := by
  have hf : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, h.pow_eq_one⟩
  rw [hf.pow_eq_pow_iff_modEq, ← h.eq_orderOf]

theorem inhab : Nonempty (LabelDatum g) := by
  classical
  obtain ⟨ζ, hζ⟩ := gensys g
  let R : Formalism.CyclotomicNorms.Fbar g → ℂ → Prop := fun x c => ∃ d, 0 < d ∧ ∃ j, x = ζ d ^ j ∧ c = E g d ^ j
  have common : ∀ x c y c', R x c → R y c' → ∃ d, 0 < d ∧ ∃ j j', x = ζ d ^ j ∧ c = E g d ^ j ∧ y = ζ d ^ j' ∧ c' = E g d ^ j' := by
    rintro x c y c' ⟨d, hd, j, rfl, rfl⟩ ⟨e, he, k, rfl, rfl⟩
    have hde := Nat.mul_pos hd he
    refine ⟨d * e, hde, (g ^ (d * e) - 1) / (g ^ d - 1) * j, (g ^ (d * e) - 1) / (g ^ e - 1) * k, ?_, ?_, ?_, ?_⟩
    · rw [pow_mul (ζ _), (hζ d hd).2 _ (Dvd.intro _ rfl) hde]
    · rw [pow_mul (E _ _), E_pow g (Dvd.intro _ rfl) hd hde]
    · rw [pow_mul (ζ _), (hζ e he).2 _ (Dvd.intro_left _ rfl) hde]
    · rw [pow_mul (E _ _), E_pow g (Dvd.intro_left _ rfl) he hde]
  have key : ∀ x c y c', R x c → R y c' → (x = y ↔ c = c') := by
    intro x c y c' h h'
    obtain ⟨d, hd, j, j', rfl, rfl, rfl, rfl⟩ := common _ _ _ _ h h'
    rw [prim_iff (hζ d hd).1 (pos g hd), prim_iff (E_prim g hd) (pos g hd)]
  have mul : ∀ x c y c', R x c → R y c' → R (x * y) (c * c') := by
    intro x c y c' h h'
    obtain ⟨d, hd, j, j', rfl, rfl, rfl, rfl⟩ := common _ _ _ _ h h'
    exact ⟨d, hd, j + j', (pow_add _ _ _).symm, (pow_add _ _ _).symm⟩
  have ex : ∀ x, x ≠ 0 → ∃ c, R x c := by
    intro x hx
    obtain ⟨d, hd, h⟩ := level g x hx
    haveI : NeZero (g ^ d - 1) := ⟨(pos g hd).ne'⟩
    obtain ⟨j, -, hj⟩ := (hζ d hd).1.eq_pow_of_pow_eq_one h
    exact ⟨_, d, hd, j, hj.symm, rfl⟩
  choose! t ht using ex
  let t' : Formalism.CyclotomicNorms.Fbar g → ℂ := fun x => if x = 0 then 0 else t x
  have ht' : ∀ x, x ≠ 0 → R x (t' x) := fun x hx => by simpa [t', hx] using ht x hx
  refine ⟨⟨⟨⟨t', ?_⟩, ?_⟩, ?_, ζ, fun d hd => (hζ d hd).1.eq_orderOf.symm,
    fun d e hd he => (hζ d hd).2 _ (Dvd.intro _ rfl) (Nat.mul_pos hd he)⟩⟩
  · exact (key _ _ _ _ (ht' 1 one_ne_zero) ⟨1, one_pos, 0, by simp, by simp⟩).1 rfl
  · intro x y
    by_cases hx : x = 0
    · simp [t', hx]
    by_cases hy : y = 0
    · simp [t', hy]
    exact (key _ _ _ _ (ht' _ (mul_ne_zero hx hy)) (mul _ _ _ _ (ht' x hx) (ht' y hy))).1 rfl
  · intro x y hx hy h
    exact (key _ _ _ _ (ht' x hx) (ht' y hy)).2 h

theorem thetaOf_pow (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ^ (g ^ d - 1) = 1) (n : ℕ) :
    thetaOf L d x (L.gen d ^ n) = L.teich x ^ n := by
  have h : ∃ m : ℕ, L.gen d ^ n = L.gen d ^ m := ⟨n, rfl⟩
  have hp : IsPrimitiveRoot (L.gen d) (g ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  have h1 := (prim_iff hp (pos g hd) _ _).1 h.choose_spec
  have h2 : L.teich x ^ (g ^ d - 1) = 1 := by rw [← map_pow, hx, map_one]
  rw [thetaOf, dite_eq_left h, pow_eq_pow_mod _ h2, pow_eq_pow_mod n h2, h1]

end GlobalTheory.GLq.LabelModel
end

section

noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

variable {l : ℕ} [Fact l.Prime]

theorem norm_zC (x : ℤ_[l]) : ‖zC x‖ = ‖x‖ := by
  unfold zC
  rw [norm_algebraMap']
  rfl

theorem mem_OC (y : PadicComplex l) : y ∈ PadicComplexInt l ↔ ‖y‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
  simp [Valuation.norm_def, ← NNReal.coe_one, ← NNReal.coe_le_coe,
    ← map_one (Valuation.RankLeOne.hom' Valued.v),
    (Valuation.RankLeOne.strictMono' (v := (Valued.v : Valuation (PadicComplex l) _))).le_iff_le, ← map_one Valued.v.restrict]

theorem act_zC {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (h : IsActC act) (g : GQ l)
    (x : ℤ_[l]) : act g (zC x) = zC x := by
  have h1 : zC x = ((algebraMap ℚ_[l] (Om l) (x : ℚ_[l]) : Om l) : PadicComplex l) := rfl
  rw [h1, h.1, AlgEquiv.commutes]

def zOC (l : ℕ) [Fact l.Prime] : ℤ_[l] →+* OC l :=
  ((algebraMap ℚ_[l] (PadicComplex l)).comp PadicInt.Coe.ringHom).codRestrict (PadicComplexInt l)
    (fun x => (mem_OC _).2 ((norm_zC x).le.trans x.norm_le_one))

scoped instance algOC : Algebra ℤ_[l] (OC l) := (zOC l).toAlgebra

theorem coe_algebraMap_OC (x : ℤ_[l]) :
    ((algebraMap ℤ_[l] (OC l) x : OC l) : PadicComplex l) = zC x := rfl

abbrev OCO (LL : FinExt l) : Type := OC l ⊗[ℤ_[l]] ↥(OL LL)

def gRA {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g : GQ l) : RA LL →ₐ[↥(OL LL)] RA LL :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (AI.actWHom g).toAlgHom

def IsThetaShift {P : LocPrime l} (AI : LocAinf l P) (n : ℕ) (θ : Ainf l →ₐ[ℤ_[l]] OC l) : Prop :=
  (∀ (g : GQ l) (a : Ainf l), ((θ (AI.actWHom g a) : OC l) : PadicComplex l) =
    AI.actC g ((θ a : OC l) : PadicComplex l)) ∧
  ∀ j : ℕ, θ (WittVector.teichmuller l (AI.εroot j)) = AI.ζ (j + n)

def thR (LL : FinExt l) (θ : Ainf l →ₐ[ℤ_[l]] OC l) : RA LL →+* OCO LL :=
  ((Algebra.TensorProduct.comm ℤ_[l] ↥(OL LL) (OC l)).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id ℤ_[l] ↥(OL LL)) θ)).toRingHom

theorem thR_tmul (LL : FinExt l) (θ : Ainf l →ₐ[ℤ_[l]] OC l) (a : ↥(OL LL)) (w : Ainf l) :
    thR LL θ (a ⊗ₜ[ℤ_[l]] w) = θ w ⊗ₜ[ℤ_[l]] a := rfl

def kap {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (x : OCO LL) (k : Fin f) :
    PadicComplex l :=
  (((Algebra.TensorProduct.basis (OC l) o).repr x k : OC l) : PadicComplex l)

theorem kap_tmul {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (c : OC l)
    (a : ↥(OL LL)) (k : Fin f) :
    kap o (c ⊗ₜ[ℤ_[l]] a) k = (c : PadicComplex l) * zC (o.repr a k) := by
  simp [kap, Algebra.TensorProduct.basis_repr_tmul, coe_algebraMap_OC]

theorem kap_add {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (x y : OCO LL)
    (k : Fin f) : kap o (x + y) k = kap o x k + kap o y k := by
  simp [kap]

theorem kap_zero {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (k : Fin f) : kap o 0 k = 0 := by
  simp [kap]

theorem kap_tmul_one_mul {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (c : OC l) (x : OCO LL) (k : Fin f) :
    kap o ((c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) * x) k = (c : PadicComplex l) * kap o x k := by
  have : (c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) * x = c • x := by
    rw [Algebra.smul_def]; rfl
  rw [this]
  simp [kap]

theorem norm_kap_le {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (x : OCO LL)
    (k : Fin f) : ‖kap o x k‖ ≤ 1 := (mem_OC _).1 (Subtype.property _)

def lam {LL : FinExt l} {f d : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (x : OCO LL) :
    Matrix (Fin d) (Fin d) (PadicComplex l) :=
  ∑ k, kap o x k • A (o k)

theorem freeOL (LL : FinExt l) : Module.Free ℤ_[l] ↥(OL LL) :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : Module.IsTorsionFree ℤ_[l] ↥LL.1 := Module.isTorsionFree_iff_algebraMap_injective.mpr (by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]
    exact (algebraMap ℚ_[l] ↥LL.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l]))
  IsIntegralClosure.module_free ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

theorem finiteOL (LL : FinExt l) : Module.Finite ℤ_[l] ↥(OL LL) :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

theorem inclR_injective (LL : FinExt l) : Function.Injective (inclR LL) := by
  haveI := freeOL LL
  letI : Module.Flat ℤ_[l] ↥(OL LL) := Module.Flat.of_free
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ↥(OL LL)) (inclWA l).toLinearMap
    (WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l)))

set_option synthInstance.maxHeartbeats 400000 in
theorem inclR_gRA {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g : GQ l) (r : RA LL) :
    inclR LL (gRA AI LL g r) = AI.gRW LL g (inclR LL r) := by
  induction r using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a w =>
    exact congrArg (fun u => a ⊗ₜ[ℤ_[l]] u) (inclW_act AI g w).symm

set_option synthInstance.maxHeartbeats 400000 in
theorem kap_thR_gRA {P : LocPrime l} (AI : LocAinf l P) {LL : FinExt l} {f n : ℕ}
    (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) {θ : Ainf l →ₐ[ℤ_[l]] OC l} (hθ : IsThetaShift AI n θ)
    (g : GQ l) (r : RA LL) (k : Fin f) :
    kap o (thR LL θ (gRA AI LL g r)) k = AI.actC g (kap o (thR LL θ r) k) := by
  induction r using TensorProduct.induction_on with
  | zero => simp only [map_zero, kap_zero]
  | add x y hx hy => simp only [map_add (f := _), kap_add, hx, hy]
  | tmul a w =>
    have h1 : gRA AI LL g (a ⊗ₜ[ℤ_[l]] w) = a ⊗ₜ[ℤ_[l]] AI.actWHom g w := rfl
    rw [h1, thR_tmul, thR_tmul, kap_tmul, kap_tmul, map_mul, hθ.1, act_zC ⟨AI.actC_ext, AI.actC_norm⟩]

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
  [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
  {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']

scoped instance (priority := high) twModule (T : LocLat G Qp LL O) : Module R (TW R T) :=
  inferInstance

scoped instance (priority := high) twSMul (T : LocLat G Qp LL O) : SMul R (TW R T) :=
  inferInstance

theorem TWincl_smul (f : R →ₐ[O] R') (T : LocLat G Qp LL O) (r : R) (z : TW R T) :
    TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul a t => simp [TWincl, TensorProduct.smul_tmul']

theorem TWact_smul (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (g : G) (r : R) (z : TW R T) :
    TWact f T g (r • z) = f r • TWact f T g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul a t => simp [TWact, TensorProduct.smul_tmul']

theorem TWincl_act (f : R →ₐ[O] R') (u : R →ₐ[O] R) (u' : R' →ₐ[O] R') (h : ∀ r, f (u r) = u' (f r))
    (T : LocLat G Qp LL O) (g : G) (z : TW R T) :
    TWincl f T (TWact u T g z) = TWact u' T g (TWincl f T z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a t => simp [TWact, TWincl, h]

theorem TWincl_injective (f : R →ₐ[O] R') (hf : Function.Injective f) (T : LocLat G Qp LL O) :
    Function.Injective (TWincl f T) := by
  haveI : Module.Free O ↥T.L.T := T.L.free
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T) f.toLinearMap hf

theorem TWincl_one_tmul (f : R →ₐ[O] R') (T : LocLat G Qp LL O) (t : ↥T.L.T) :
    TWincl f T ((1 : R) ⊗ₜ[O] t) = (1 : R') ⊗ₜ[O] t := by
  simp [TWincl]

end Generic

end GlobalTheory.Cyc.Decomp
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem htBasis_of_isDec : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m d : ℕ) (M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (Dm : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) (J : Set ℤ), IsDec act χ K m M Dm U g → HTBasis act χ (Gj K m) M J → HTBasis act χ (Gj K m) U J := by
  intro l _ act χ _ _ K m d M U Dm g J hD hH
  obtain ⟨hdet, -, -, -, hrel⟩ := hD
  obtain ⟨e, u, hli, hu, hfix⟩ := hH
  have hDe : ∀ v : Fin d → PadicComplex l, Dm.mulVec (Dm⁻¹.mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hinj : ∀ v w : Fin d → PadicComplex l, Dm.mulVec v = Dm.mulVec w → v = w := by
    intro v w h
    have h2 := congrArg (fun x => Dm⁻¹.mulVec x) h
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec] using h2
  refine ⟨fun k => Dm⁻¹.mulVec (e k), u, ?_, hu, ?_⟩
  · refine LinearIndependent.of_comp Dm.mulVecLin ?_
    have : (Dm.mulVecLin ∘ fun k => Dm⁻¹.mulVec (e k)) = e := by
      funext k
      exact hDe (e k)
    rw [this]
    exact hli
  · intro σ hσ k
    apply hinj
    have hmap : (Dm.map (act σ)).mulVec (fun a => act σ (Dm⁻¹.mulVec (e k) a)) =
        fun a => act σ (e k a) := by
      funext a
      conv_rhs => rw [← hDe (e k)]

      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
    have h1 := hfix σ hσ k
    unfold twAct at h1 ⊢
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hrel σ hσ, ← Matrix.mulVec_mulVec, hmap, h1, hDe]

end GlobalTheory.Cyc
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open Topology Filter

namespace GlobalTheory.TensorOneCoc

theorem isCoc_tmul_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (G : Subgroup (GQ l)) (Y : Type) [AddCommGroup Y] [Module ℤ_[l] Y] (ρ : ↥G →* (Y →ₗ[ℤ_[l]] Y)) (b : ℤ) (f : ↥G → Y), (∀ g h, f (g * h) = f g + ρ g (f h)) → (∀ (n : ℕ) (g : ↥G), ∀ᶠ h in nhds g, ∃ y : Y, f h - f g = (l ^ n : ℕ) • y) → ∀ one : ↥(Mxi (AinfSub l) (xiU AI) 0), (one : WCb l) = 1 → letI : TopologicalSpace (TensorProduct ℤ_[l] Y (Qab (AinfSub l) (xiU AI) 0 b)) := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _; IsCoc (repQ AI G ρ 0 b) (fun g => f g ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU AI) 0 b)) := by
  intro l _ P AI G Y _ _ ρ b f hf hc one h1
  refine ⟨(GlobalTheory.continuous_adicModule_iff (l : ℤ_[l]) _).2 fun g n => ?_, fun g h => ?_⟩
  · filter_upwards [hc n g] with h ⟨y, e⟩
    refine ⟨y ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU AI) 0 b), ?_⟩
    rw [← TensorProduct.sub_tmul, e, TensorProduct.smul_tmul', ← Nat.cast_pow,
      Nat.cast_smul_eq_nsmul]
  · have hq : actQab (xiOK AI) 0 b (g : GQ l)
        (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU AI) 0 b) = Submodule.Quotient.mk one := by
      rw [actQab, Submodule.mapQ_apply]
      congr 1
      apply Subtype.ext
      change AI.actWCbHom (g : GQ l) (one : WCb l) = one
      rw [h1, map_one]
    have : repQ AI G ρ 0 b g (f h ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU AI) 0 b))
        = ρ g (f h) ⊗ₜ[ℤ_[l]] actQab (xiOK AI) 0 b (g : GQ l) (Submodule.Quotient.mk one) := rfl
    beta_reduce
    rw [this, hq, hf, TensorProduct.add_tmul]

end GlobalTheory.TensorOneCoc
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.phi_sub_sub_mem_xi_of_monodromy_eq : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Y, ∀ σ : Vec K a ι, D.conn σ = D.zeta y → ∃ d : D.D, D.phi σ - σ - D.phi y = D.xi d := by
  first | exact @GlobalTheory.BK.BKDat.phi_sub_sub_mem_xi | exact GlobalTheory.BK.BKDat.phi_sub_sub_mem_xi | (intros; apply GlobalTheory.BK.BKDat.phi_sub_sub_mem_xi <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.vPow_lattice_le_image_add_lPow_of_finite_cokernel : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), IsFiniteLength (A O K) F.coker → ∀ b : ℕ, 1 ≤ b → H + η + b ≤ l → ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L, ((X : K⟦X⟧) ^ e) ^ (H + η + b) • x = F.app y + (l : K) ^ b • z := by
  first | exact @GlobalTheory.LiftCoker.vPow_mem_imL_add_lPow | exact GlobalTheory.LiftCoker.vPow_mem_imL_add_lPow | (intros; apply GlobalTheory.LiftCoker.vPow_mem_imL_add_lPow <;> assumption)
end
