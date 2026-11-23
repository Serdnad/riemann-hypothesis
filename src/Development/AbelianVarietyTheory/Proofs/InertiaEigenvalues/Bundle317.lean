module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle113
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle290
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle292
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCoboundariesAmongBlockCocyclesLe
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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle291

@[expose] public section

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.HcDeg

variable {g : ℕ} [Fact g.Prime]

theorem prod_Icc_eq_range (f : ℕ → ℂ) (d : ℕ) : ∏ i ∈ Finset.Icc 1 d, f i = ∏ i ∈ Finset.range d, f (i + 1) := by
  induction d with
  | zero => simp
  | succ d ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

theorem card_GL_C (d : ℕ) : (Fintype.card (Gn g d) : ℂ) =
    (∏ i ∈ Finset.range d, (g : ℂ) ^ i) * ∏ i ∈ Finset.Icc 1 d, ((g : ℂ) ^ i - 1) := by
  rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field, ZMod.card, Nat.cast_prod,
    Fin.prod_univ_eq_prod_range (fun i => (((g ^ d - g ^ i : ℕ)) : ℂ)) d]
  have h1 : ∀ i ∈ Finset.range d, (((g ^ d - g ^ i : ℕ)) : ℂ) = (g : ℂ) ^ i * ((g : ℂ) ^ (d - 1 - i + 1) - 1) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hle : g ^ i ≤ g ^ d := Nat.pow_le_pow_right (Fact.out : g.Prime).pos hi'.le
    rw [Nat.cast_sub hle, mul_sub, mul_one, ← pow_add]
    push_cast
    congr 2
    omega
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, prod_Icc_eq_range,
    Finset.prod_range_reflect (fun i => (g : ℂ) ^ (i + 1) - 1) d]

theorem prod_pow_add (a b : ℕ) : ∏ i ∈ Finset.range (a + b), (g : ℂ) ^ i =
    (∏ i ∈ Finset.range a, (g : ℂ) ^ i) * (∏ i ∈ Finset.range b, (g : ℂ) ^ i) * (g : ℂ) ^ (a * b) := by
  rw [Finset.prod_range_add]
  simp only [pow_add, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
  ring

theorem toG_one (n : ℕ) : toG (1 : Mt g n) = 1 := by
  apply Units.ext
  rw [toG, dite_eq_left isUnit_one, IsUnit.unit_spec]
  rfl

theorem tl_one (a b : ℕ) : tl a (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [GlobalTheory.GLm.ParBasic.tl_apply]
  simp [Matrix.one_apply, Fin.castAdd_inj]

theorem br_one (a b : ℕ) : br a b (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [GlobalTheory.GLm.ParBasic.br_apply]
  simp [Matrix.one_apply, Fin.natAdd_inj]

theorem hc_one (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) :
    hc a b α β (a + b) 1 * (Fintype.card (Gn g a) * Fintype.card (Gn g b) * (g : ℂ) ^ (a * b)) =
      Fintype.card (Gn g (a + b)) * (α 1 * β 1) := by
  have hP := GlobalTheory.GLm.ParBasic.card_par (g := g) (a := a) (b := b)
  have hne : ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
    exact ⟨1, by simpa using GlobalTheory.GLm.ParBasic.inPar_one (g := g) a (a + b)⟩
  have hs : hc a b α β (a + b) 1 = ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ)⁻¹ *
      (Fintype.card (Gn g (a + b)) * (α 1 * β 1)) := by
    simp only [hc, hcT, mul_one, inv_mul_cancel, Units.val_one, GlobalTheory.GLm.ParBasic.inPar_one, if_true, tl_one, br_one,
      toG_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hP' : ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ) =
      Fintype.card (Gn g a) * Fintype.card (Gn g b) * (g : ℂ) ^ (a * b) := by
    rw [hP]; push_cast; ring
  rw [hs, ← hP']
  field_simp

theorem prodIcc_ne (d : ℕ) : ∏ i ∈ Finset.Icc 1 d, ((g : ℂ) ^ i - 1) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  have : (1 : ℕ) < g ^ i := Nat.one_lt_pow (by omega) hg
  rw [sub_ne_zero]
  exact_mod_cast this.ne'

theorem hc_degree : ∀ (g : ℕ) [Fact g.Prime] (L : List (Pc g)) (n : ℕ), n = degL L → hcL L n 1 * (L.map fun p => ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)).prod = (∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1)) * (L.map fun p => p.2 1).prod := by
  intro g _ L
  induction L with
  | nil =>
    intro n hn
    subst hn
    simp [hcL_nil, degL]
  | cons p L ih =>
    intro n hn
    have hn' : n = p.1 + degL L := by rw [hn]; simp [degL]
    subst hn'
    have h1 := hc_one p.1 (degL L) p.2 (hcL L (degL L))
    have h2 := ih (degL L) rfl
    rw [card_GL_C, card_GL_C, card_GL_C, prod_pow_add] at h1
    have hA := prodIcc_ne (g := g) p.1
    have hB := prodIcc_ne (g := g) (degL L)
    have hG : ∀ d, ∏ i ∈ Finset.range d, (g : ℂ) ^ i ≠ 0 := fun d =>
      Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (by exact_mod_cast (Fact.out : g.Prime).ne_zero)
    have hg0 : (g : ℂ) ^ (p.1 * degL L) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : g.Prime).ne_zero)
    simp only [List.map_cons, List.prod_cons, hcL_cons]
    set A := ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)
    set B := ∏ i ∈ Finset.Icc 1 (degL L), ((g : ℂ) ^ i - 1)
    set C := ∏ i ∈ Finset.Icc 1 (p.1 + degL L), ((g : ℂ) ^ i - 1)
    set Ga := ∏ i ∈ Finset.range p.1, (g : ℂ) ^ i
    set Gb := ∏ i ∈ Finset.range (degL L), (g : ℂ) ^ i
    set X := hc p.1 (degL L) p.2 (hcL L (degL L)) (p.1 + degL L) 1
    set Y := (L.map fun p => ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)).prod
    set Z := (L.map fun p => p.2 1).prod

    have key : X * (A * B) = C * (p.2 1 * hcL L (degL L) 1) := by
      apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (hG p.1) (hG (degL L))) hg0)
      linear_combination h1
    calc X * (A * Y) = X * (A * B) * Y / B := by field_simp
      _ = C * (p.2 1 * (hcL L (degL L) 1 * Y)) / B := by rw [key]; ring
      _ = C * (p.2 1 * Z) := by rw [h2]; field_simp

end GlobalTheory.GLq.HcDeg
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.FrobeniusFixedBasis

variable {F K M : Type} [Field F] [Field K] [Algebra F K] [AddCommGroup M] [Module K M] [Module F M]
  [IsScalarTower F K M]

theorem isScalarTower_sub (E : IntermediateField F K) : IsScalarTower F E M :=
  ⟨fun q e m => by
    show ((q • e : E) : K) • m = q • ((e : K) • m)
    rw [IntermediateField.coe_smul, smul_assoc]⟩

theorem exists_tower_basis (E : IntermediateField F K) {r : ℕ} (bω : Module.Basis (Fin r) F E)
    (n : Type) [Fintype n] [DecidableEq n] (v : n × Fin r → M) (hv : LinearIndependent F v)
    (hst : ∀ e ∈ E, ∀ c, e • v c ∈ Submodule.span F (Set.range v)) :
    ∃ a : n → M, (∀ j, a j ∈ Submodule.span F (Set.range v)) ∧
      LinearIndependent F (fun jk : n × Fin r => ((bω jk.2 : E) : K) • a jk.1) ∧
      Submodule.span F (Set.range fun jk : n × Fin r => ((bω jk.2 : E) : K) • a jk.1) =
        Submodule.span F (Set.range v) := by
  haveI := isScalarTower_sub (M := M) E
  set V := Submodule.span F (Set.range v) with hVdef
  have hstab : ∀ e ∈ E, ∀ x ∈ V, e • x ∈ V := by
    intro e he x hx
    have hle : V ≤ V.comap ((LinearMap.lsmul K M e).restrictScalars F) := by
      rw [hVdef, Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      exact hst e he c
    exact hle hx
  let VE : Submodule E M :=
    { carrier := V
      add_mem' := fun hx hy => V.add_mem hx hy
      zero_mem' := V.zero_mem
      smul_mem' := fun e x hx => hstab (e : K) e.2 x hx }
  have hfinV : Module.finrank F V = Fintype.card n * r := by
    rw [hVdef, finrank_span_eq_card hv, Fintype.card_prod, Fintype.card_fin]
  let e1 : VE ≃ₗ[F] V :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfinVE : Module.finrank F VE = Fintype.card n * r := by
    rw [← hfinV]; exact e1.finrank_eq
  haveI : Module.Finite F V := by
    rw [hVdef]; exact FiniteDimensional.span_of_finite F (Set.finite_range v)
  haveI : Module.Finite F VE := Module.Finite.equiv e1.symm
  haveI : Module.Finite E VE := Module.Finite.of_restrictScalars_finite F E VE
  have hE : Module.finrank F E = r := by
    rw [Module.finrank_eq_card_basis bω, Fintype.card_fin]
  haveI : Module.Finite F E := Module.Finite.of_basis bω
  have hrpos : 0 < r := by
    rw [← hE]; exact Module.finrank_pos
  have htower := Module.finrank_mul_finrank F E VE
  rw [hE, hfinVE] at htower
  have hnE : Module.finrank E VE = Fintype.card n := by
    have : Module.finrank E VE * r = Fintype.card n * r := by rw [mul_comm]; exact htower
    exact Nat.eq_of_mul_eq_mul_right hrpos this
  let b : Module.Basis n E VE := (Module.finBasisOfFinrankEq E VE hnE).reindex (Fintype.equivFin n).symm
  let bt : Module.Basis (Fin r × n) F VE := bω.smulTower b
  let f : VE →ₗ[F] M := (VE.subtype).restrictScalars F
  have hf : Function.Injective f := Subtype.val_injective
  refine ⟨fun j => (b j : M), fun j => (b j).2, ?_, ?_⟩
  · have h1 : LinearIndependent F (f ∘ bt) := bt.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
    have h2 := h1.comp (Equiv.prodComm n (Fin r)) (Equiv.injective _)
    convert h2 using 1
    ext jk
    simp [bt, f, Module.Basis.smulTower_apply, ← algebraMap_smul K]
  · have hli : LinearIndependent F (fun jk : n × Fin r => ((bω jk.2 : E) : K) • (b jk.1 : M)) := by
      have h1 : LinearIndependent F (f ∘ bt) := bt.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
      have h2 := h1.comp (Equiv.prodComm n (Fin r)) (Equiv.injective _)
      convert h2 using 1
      ext jk
      simp [bt, f, Module.Basis.smulTower_apply, ← algebraMap_smul K]
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨jk, rfl⟩
      exact hstab _ (bω jk.2).2 _ (b jk.1).2
    · rw [finrank_span_eq_card hli, hfinV, Fintype.card_prod, Fintype.card_fin]

end GlobalTheory.FrobeniusFixedBasis

namespace GlobalTheory.FrobeniusFixedBasis

def frFixed (l : ℕ) [Fact l.Prime] (r : ℕ) : IntermediateField ℚ_[l] ↥(MaximalUnramifiedExtension l) where
  carrier := {c | fr l r c = c}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, ha, hb]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_add (f := _), ha, hb]
  algebraMap_mem' := fun q => by
    show (frobUr l ^ r) (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = _
    exact AlgHom.commutes _ q
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    rw [map_inv₀, hx]

end GlobalTheory.FrobeniusFixedBasis

namespace GlobalTheory


open GlobalTheory.FrobeniusFixedBasis in
theorem exists_frFixed_tower_basis : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) →
    LinearIndependent ℚ_[l] ω → (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → ∃ a : Fin r → ℚ_[l], c = ∑ k, a k • ω k) →
    ∀ (M : Type) [AddCommGroup M] [Module ↥(MaximalUnramifiedExtension l) M] [Module ℚ_[l] M] [IsScalarTower ℚ_[l] ↥(MaximalUnramifiedExtension l) M] (n : Type)
      [Fintype n] [DecidableEq n] (v : n × Fin r → M), LinearIndependent ℚ_[l] v →
      (∀ e : ↥(MaximalUnramifiedExtension l), fr l r e = e → ∀ c, e • v c ∈ Submodule.span ℚ_[l] (Set.range v)) →
      ∃ a : n → M, (∀ j, a j ∈ Submodule.span ℚ_[l] (Set.range v)) ∧
        LinearIndependent ℚ_[l] (fun jk : n × Fin r => ω jk.2 • a jk.1) ∧
        Submodule.span ℚ_[l] (Set.range fun jk : n × Fin r => ω jk.2 • a jk.1) = Submodule.span ℚ_[l] (Set.range v) := by
  intro l _ r ω hω hli hsp M _ _ _ _ n _ _ v hv hst
  let E := frFixed l r
  let ω' : Fin r → E := fun k => ⟨ω k, hω k⟩
  have hli' : LinearIndependent ℚ_[l] ω' := by
    apply LinearIndependent.of_comp (E.val.toLinearMap)
    exact hli
  have hsp' : ⊤ ≤ Submodule.span ℚ_[l] (Set.range ω') := by
    rintro ⟨c, hc⟩ _
    obtain ⟨a, ha⟩ := hsp c hc
    have : (⟨c, hc⟩ : E) = ∑ k, a k • ω' k := by
      apply Subtype.ext
      show c = ((∑ k, a k • ω' k : E) : ↥(MaximalUnramifiedExtension l))
      rw [ha]
      simp [ω']
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let bω : Module.Basis (Fin r) ℚ_[l] E := Module.Basis.mk hli' hsp'
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_tower_basis E bω n v hv (fun e he c => hst e he c)
  have hb : ∀ k, ((bω k : E) : ↥(MaximalUnramifiedExtension l)) = ω k := fun k => by
    simp [bω, ω', Module.Basis.mk_apply]
  simp only [hb] at ha2 ha3
  exact ⟨a, ha1, ha2, ha3⟩

end GlobalTheory
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem intertwine_mul {G ι R S : Type} [Monoid G] [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (B : G → Matrix ι ι S) (hB1 : B 1 = 1)
    (hBm : ∀ g h, B (g * h) = B g * B h) (p : GL ι S) (T : G → Matrix ι ι R)
    (hT : ∀ g, (p : Matrix ι ι S) * (T g).map f = B g * p) :
    T 1 = 1 ∧ ∀ g h, T (g * h) = T g * T h := by
  have hinj : Function.Injective (fun M : Matrix ι ι R => M.map f) := Matrix.map_injective hf
  refine ⟨?_, fun g h => ?_⟩
  · apply hinj
    apply (Units.mul_right_inj p).1
    show (p : Matrix ι ι S) * (T 1).map f = (p : Matrix ι ι S) * (1 : Matrix ι ι R).map f
    rw [hT, hB1, one_mul, Matrix.map_one f (map_zero f) (map_one f), mul_one]
  · apply hinj
    apply (Units.mul_right_inj p).1
    show (p : Matrix ι ι S) * (T (g * h)).map f = (p : Matrix ι ι S) * (T g * T h).map f
    calc (p : Matrix ι ι S) * (T (g * h)).map f = B g * B h * p := by rw [hT, hBm]
      _ = B g * ((p : Matrix ι ι S) * (T h).map f) := by rw [mul_assoc, hT]
      _ = ((p : Matrix ι ι S) * (T g).map f) * (T h).map f := by rw [← mul_assoc, hT]
      _ = (p : Matrix ι ι S) * (T g * T h).map f := by rw [Matrix.map_mul, mul_assoc]

theorem exists_ratForm : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (W : GL (Fin r) ↥(MaximalUnramifiedExtension l)), IsRat r σ →
    (∀ m k : Fin r, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k = fr l m (ω k)) → (∀ k, fr l r (ω k) = ω k) →
    (∀ (X : Type) [TopologicalSpace X] (x : X → ↥(MaximalUnramifiedExtension l)), (∀ t, fr l r (x t) = x t) →
      Continuous (fun t => ((x t : ↥(MaximalUnramifiedExtension l)) : Om l)) →
      ∃ a : X → Fin r → ℚ_[l], Continuous a ∧ ∀ t (m : Fin r),
        fr l m (x t) = ∑ k, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a t k)) →
    ∃ (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)),
      (∀ i j, Continuous fun g => (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]) i j) ∧
      (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) ∧
      (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) ∧
      ∀ c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l), (∀ g i, fr l r (c g i) = c g i) →
        (∀ i, Continuous fun g => ((c g i : ↥(MaximalUnramifiedExtension l)) : Om l)) →
        ∃ c₀ : ↥(GK K) → n × Fin r → ℚ_[l], Continuous c₀ ∧ ∀ g,
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1) := by
  intro l _ n _ _ K r σ ω W hσ hW hω hcoef
  classical

  let P0 : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) :=
    Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (1 : Matrix n n ↥(MaximalUnramifiedExtension l)) (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l))
  let Q0 : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) :=
    Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (1 : Matrix n n ↥(MaximalUnramifiedExtension l)) ((W⁻¹ : GL (Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l))
  have hPQ : P0 * Q0 = 1 := by
    simp only [P0, Q0]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_kronecker_one]
  have hQP : Q0 * P0 = 1 := by
    simp only [P0, Q0]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_kronecker_one]
  let p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l) := ⟨P0, Q0, hPQ, hQP⟩
  have hp : ∀ i m j k, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) (i, m) (j, k) =
      if i = j then (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k else 0 := by
    intro i m j k
    show P0 (i, m) (j, k) = _
    simp only [P0, Matrix.kronecker_apply, Matrix.one_apply]
    split_ifs <;> simp

  have hA : ∀ (i j : n) (k : Fin r), ∃ a : ↥(GK K) → Fin r → ℚ_[l], Continuous a ∧ ∀ g (m : Fin r),
      fr l m ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j * ω k) =
        ∑ k', (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k' * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a g k') := by
    intro i j k
    refine hcoef ↥(GK K) (fun g => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j * ω k) (fun g => ?_) ?_
    · rw [map_mul, hσ.rat, hω]
    · show Continuous fun g => (((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) * ((ω k : ↥(MaximalUnramifiedExtension l)) : Om l)
      exact (hσ.cont i j).mul continuous_const
  choose A hAc hA using hA
  let T : ↥(GK K) → Matrix (n × Fin r) (n × Fin r) ℚ_[l] := fun g x y => A x.1 y.1 y.2 g x.2
  let B : ↥(GK K) → Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := fun g =>
    Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))
  have hB1 : B 1 = 1 := by
    simp only [B, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.blockDiagonal_one
  have hBm : ∀ g h, B (g * h) = B g * B h := by
    intro g h
    simp only [B, map_mul, Units.val_mul, Matrix.map_mul]
    rw [Matrix.blockDiagonal_mul]
  have hT : ∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * (T g).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
      B g * p := by
    intro g
    refine Matrix.ext ?_
    rintro ⟨i, m⟩ ⟨j, k⟩
    rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [hp, B, T, Matrix.map_apply, Matrix.blockDiagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Fintype.sum_eq_single i (fun x hx => by simp [Ne.symm hx])]
    simp only [if_true]
    refine (show _ = ∑ x, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m x * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (A i j k g x)
      from rfl).trans ?_
    rw [← hA i j k g m, map_mul]
    symm
    simp [hW]
  obtain ⟨hT1, hTm⟩ := intertwine_mul (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)).injective
    B hB1 hBm p T hT
  let T' : ↥(GK K) →* Matrix (n × Fin r) (n × Fin r) ℚ_[l] :=
    { toFun := T, map_one' := hT1, map_mul' := hTm }
  refine ⟨T'.toHomUnits, p, ?_, ?_, ?_, ?_⟩
  · rintro ⟨i, k'⟩ ⟨j, k⟩
    exact (continuous_apply k').comp (hAc i j k)
  · rintro ⟨i, m⟩ ⟨j, k⟩
    apply hσ.le
    rw [hp]
    split_ifs
    · rw [hW]; exact fr_comm (hω k) m
    · exact map_zero _
  · intro g
    exact hT g
  · intro c hc hcc
    have hC : ∀ i : n, ∃ a : ↥(GK K) → Fin r → ℚ_[l], Continuous a ∧ ∀ g (m : Fin r),
        fr l m (c g i) = ∑ k, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a g k) :=
      fun i => hcoef ↥(GK K) (fun g => c g i) (fun g => hc g i) (hcc i)
    choose a hac ha using hC
    refine ⟨fun g x => a x.1 g x.2, continuous_pi fun x => (continuous_apply x.2).comp (hac x.1), fun g => ?_⟩
    funext ⟨i, m⟩
    rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    simp only [hp, ite_mul, zero_mul]
    rw [Fintype.sum_eq_single i (fun x hx => by simp [Ne.symm hx])]
    simp only [if_true]
    rw [ha i g m]

end GlobalTheory.PMon

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.cocycle_restrictionScalars_rational_coords : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l)) (c₀ : ↥(GK K) → n × Fin r → ℚ_[l]),
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1)) →
    (∀ g h, c (g * h) = c g + (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).mulVec (c h)) →
    ∀ g h, c₀ (g * h) = c₀ g + (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).mulVec (c₀ h) := by
  first | exact @GlobalTheory.PMon.cocycle_rat_coords | exact GlobalTheory.PMon.cocycle_rat_coords | (intros; apply GlobalTheory.PMon.cocycle_rat_coords <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.length_cocycles_le_coboundaries_add_selmer : ∀ (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) D.R.r)), C ≤ Z1 (WKG (WpO D.nd i ρ π)) → (∀ f ∈ C, IsFinL i (WpO D.nd i ρ π) f) → (∀ v, v ∉ placesOver D.host.E (D.nd.l i) → v ∉ D.nd.S i → v ∉ D.nd.Q i → resIne i C v = ⊥) → Module.length (D.nd.O i) ↥C ≤ lenCob i (WpO D.nd i ρ π) (C) + Module.length (D.nd.O i) ↥(Br.selPi D.loc D.nbr i ρ π) := by
  first | exact @GlobalTheory.Cut.SelClass.main | exact GlobalTheory.Cut.SelClass.main | (intros; apply GlobalTheory.Cut.SelClass.main <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.length_coboundaries_among_block_cocycles_le : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → lenCob i (WpO D.nd i ρ π) (cocRho i r S Xs) ≤ ((2 * D.R.r : ℕ) : ℕ∞) * lenQ i (del51 D.nd S S.π') ∧ ∀ c : Fin D.R.t, lenCob i (chiRatO D.nd i ((c : ℕ) + 1)) (cocChi i r S Xs c) ≤ 2 * lenQ i (del51 D.nd S S.π') := by
  first | exact @GlobalTheory.Cut.Cob.main | exact GlobalTheory.Cut.Cob.main | (intros; apply GlobalTheory.Cut.Cob.main <;> assumption)
end
