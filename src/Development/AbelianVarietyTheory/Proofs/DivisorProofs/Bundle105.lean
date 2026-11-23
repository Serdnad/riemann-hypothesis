module

public import Mathlib.NumberTheory.NumberField.Basic
import Batteries.Tactic.Lint.Basic
import Batteries.Tactic.Lint.Misc
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
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
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

section

open NumberField

noncomputable section
namespace GlobalTheory.UnitaryStd

variable {r g : ℕ}

def matAddEnd (V : Type) [AddCommGroup V] (r : ℕ) : Matrix (Fin r) (Fin r) ℤ →+* AddMonoid.End (Fin r → V) where
  toFun M :=
    { toFun := fun x i => ∑ j, M i j • x j
      map_zero' := by ext i; simp
      map_add' := fun x y => by ext i; simp [smul_add, Finset.sum_add_distrib] }
  map_one' := AddMonoidHom.ext fun x => funext fun i => by
    show ∑ j, (1 : Matrix (Fin r) (Fin r) ℤ) i j • x j = x i
    simp [Matrix.one_apply, ite_smul]
  map_mul' := fun M N => AddMonoidHom.ext fun x => funext fun i => by
    show ∑ j, (M * N) i j • x j = ∑ k, M i k • ∑ j, N k j • x j
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  map_zero' := AddMonoidHom.ext fun x => funext fun i => by
    show ∑ j, (0 : Matrix (Fin r) (Fin r) ℤ) i j • x j = 0
    simp
  map_add' := fun M N => AddMonoidHom.ext fun x => funext fun i => by
    show ∑ j, (M + N) i j • x j = ∑ j, M i j • x j + ∑ j, N i j • x j
    simp [add_smul, Finset.sum_add_distrib]

@[nolint unusedArguments]
def Lat {E : Type} [Field E] [NumberField E] (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ) : Type :=
  Fin r → (Fin g → ℤ) × (Fin g → ℤ)

variable {E : Type} [Field E] [NumberField E] (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ)

instance : AddCommGroup (Lat ρ g) := inferInstanceAs (AddCommGroup (Fin r → (Fin g → ℤ) × (Fin g → ℤ)))

instance : Module (𝓞 E) (Lat ρ g) :=
  Module.compHom (Fin r → (Fin g → ℤ) × (Fin g → ℤ)) ((matAddEnd ((Fin g → ℤ) × (Fin g → ℤ)) r).comp ρ)

variable {ρ g}

theorem smul_apply (a : 𝓞 E) (x : Lat ρ g) (i : Fin r) : (a • x) i = ∑ j, ρ a i j • x j := rfl

theorem add_apply (x y : Lat ρ g) (i : Fin r) : (x + y) i = x i + y i := rfl

theorem zsmul_apply (n : ℤ) (x : Lat ρ g) (i : Fin r) : (n • x) i = n • x i := rfl

theorem neg_apply (x : Lat ρ g) (i : Fin r) : (-x) i = -x i := rfl

variable (ρ g)

def coordEquiv : Lat ρ g ≃ₗ[ℤ] (Fin r × (Fin g ⊕ Fin g) → ℤ) where
  toFun x := fun p => Sum.elim (x p.1).1 (x p.1).2 p.2
  invFun c := fun i => (fun k => c (i, Sum.inl k), fun k => c (i, Sum.inr k))
  left_inv x := by
    funext i
    apply Prod.ext <;> funext k <;> rfl
  right_inv c := by
    funext p
    rcases p with ⟨i, k⟩
    cases k <;> rfl
  map_add' x y := by
    funext p
    rcases p with ⟨i, k⟩
    cases k <;> rfl
  map_smul' n x := by
    funext p
    rcases p with ⟨i, k⟩
    cases k <;> rfl

def basis : Module.Basis (Fin r × (Fin g ⊕ Fin g)) ℤ (Lat ρ g) := Module.Basis.ofEquivFun (coordEquiv ρ g)

instance : Module.Free ℤ (Lat ρ g) := Module.Free.of_basis (basis ρ g)
instance : Module.Finite ℤ (Lat ρ g) := Module.Finite.of_basis (basis ρ g)

def form (S : Matrix (Fin r) (Fin r) ℤ) : LinearMap.BilinForm ℤ (Lat ρ g) :=
  LinearMap.mk₂ ℤ (fun x y => ∑ i, ∑ j, S i j * ((x i).1 ⬝ᵥ (y j).2 - (x i).2 ⬝ᵥ (y j).1))
    (fun x y z => by
      simp only [add_apply, Prod.fst_add, Prod.snd_add, add_dotProduct, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (fun n x y => by
      simp only [zsmul_apply, Prod.smul_fst, Prod.smul_snd, smul_dotProduct, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (fun x y z => by
      simp only [add_apply, Prod.fst_add, Prod.snd_add, dotProduct_add, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (fun n x y => by
      simp only [zsmul_apply, Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

theorem form_apply (S : Matrix (Fin r) (Fin r) ℤ) (x y : Lat ρ g) :
    form ρ g S x y = ∑ i, ∑ j, S i j * ((x i).1 ⬝ᵥ (y j).2 - (x i).2 ⬝ᵥ (y j).1) := rfl

def cx : Lat ρ g →ₗ[ℤ] Lat ρ g where
  toFun x := fun i => ((x i).2, -(x i).1)
  map_add' x y := by
    funext i
    refine Prod.ext (funext fun k => rfl) (funext fun k => ?_)
    show -((x i).1 k + (y i).1 k) = -(x i).1 k + -(y i).1 k
    ring
  map_smul' n x := by
    funext i
    refine Prod.ext (funext fun k => rfl) (funext fun k => ?_)
    show -(n * (x i).1 k) = n * -(x i).1 k
    ring

theorem cx_apply (x : Lat ρ g) (i : Fin r) : cx ρ g x i = ((x i).2, -(x i).1) := rfl

def act (a : 𝓞 E) : Lat ρ g →ₗ[ℤ] Lat ρ g := (DistribSMul.toAddMonoidHom (Lat ρ g) a).toIntLinearMap

theorem act_apply (a : 𝓞 E) (x : Lat ρ g) : act ρ g a x = a • x := rfl

theorem basis_repr (x : Lat ρ g) (p : Fin r × (Fin g ⊕ Fin g)) :
    (basis ρ g).repr x p = Sum.elim (x p.1).1 (x p.1).2 p.2 := rfl

theorem basis_apply (p : Fin r × (Fin g ⊕ Fin g)) (i : Fin r) :
    basis ρ g p i = (fun k => Pi.single (M := fun _ => ℤ) p 1 (i, Sum.inl k),
      fun k => Pi.single (M := fun _ => ℤ) p 1 (i, Sum.inr k)) := by
  rw [basis, Module.Basis.coe_ofEquivFun]
  rfl

end GlobalTheory.UnitaryStd
end
end

section

open scoped NumberField

namespace GlobalTheory.IdealPrincipalCoprime

theorem natCast_prime_not_isUnit (F : Type) [Field F] [NumberField F] {p : ℕ} (hp : p.Prime) :
    ¬ IsUnit (p : 𝓞 F) := by
  intro h
  have h1 := h.map (Algebra.norm ℤ (S := 𝓞 F))
  rw [← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap,
    isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h1
  exact hp.ne_one h1

theorem exists_mul_eq_span_coprime : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime →
    ∀ (w : Ideal (𝓞 F)), w ≠ ⊥ → ∃ (g e : 𝓞 F) (𝔟 : Ideal (𝓞 F)), g ≠ 0 ∧ e ∈ w ∧ 1 - e ∈ 𝔟 ∧
      w * 𝔟 = Ideal.span {g} ∧ 𝔟 ⊔ Ideal.span {(p : 𝓞 F)} = ⊤ := by
  intro F _ _ p hp w hw
  set N : Ideal (𝓞 F) := Ideal.span {(p : 𝓞 F)} * w with hN
  have hp0 : (p : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hN0 : N ≠ ⊥ := by
    rw [hN, Ne, Ideal.mul_eq_bot, not_or, Ideal.span_singleton_eq_bot]
    exact ⟨hp0, hw⟩
  obtain ⟨g, hg⟩ := IsDedekindDomain.exists_sup_span_eq (I := w * N) (J := w) Ideal.mul_le_left
    (mul_ne_zero hw hN0)
  have hgw : Ideal.span {g} ≤ w := hg ▸ le_sup_right
  obtain ⟨𝔟, h𝔟⟩ := Ideal.dvd_iff_le.mpr hgw
  have hsup : N ⊔ 𝔟 = ⊤ := by
    apply mul_left_cancel₀ (show w ≠ 0 from hw)
    rw [Ideal.mul_sup, ← h𝔟, hg, Ideal.mul_top]
  have hNp : N ≤ Ideal.span {(p : 𝓞 F)} := Ideal.mul_le_left
  have hNw : N ≤ w := Ideal.mul_le_right
  have hbp : 𝔟 ⊔ Ideal.span {(p : 𝓞 F)} = ⊤ := by
    have h : N ⊔ 𝔟 ≤ 𝔟 ⊔ Ideal.span {(p : 𝓞 F)} := sup_le (le_sup_of_le_right hNp) le_sup_left
    rw [hsup] at h; exact eq_top_iff.mpr h
  have hwb : w ⊔ 𝔟 = ⊤ := by
    have h : N ⊔ 𝔟 ≤ w ⊔ 𝔟 := sup_le (le_sup_of_le_left hNw) le_sup_right
    rw [hsup] at h; exact eq_top_iff.mpr h
  have h1 : (1 : 𝓞 F) ∈ w ⊔ 𝔟 := by rw [hwb]; exact Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp h1
  refine ⟨g, e, 𝔟, ?_, he, ?_, h𝔟.symm, hbp⟩
  · intro hg0
    have hb0 : 𝔟 = ⊥ := by
      have : w * 𝔟 = ⊥ := by rw [← h𝔟, hg0, Ideal.span_singleton_eq_bot.mpr rfl]
      rcases Ideal.mul_eq_bot.mp this with h | h
      · exact absurd h hw
      · exact h
    rw [hb0, bot_sup_eq] at hbp
    exact natCast_prime_not_isUnit F hp (Ideal.span_singleton_eq_top.mp hbp)
  · rw [← hef, add_sub_cancel_left]; exact hf

end GlobalTheory.IdealPrincipalCoprime
end

section

open NumberField

namespace GlobalTheory
namespace RepTrace

theorem isUnit_of_ne_zero {E : Type} [Field E] [NumberField E] {P : Type} [CommRing P] [Algebra ℚ P]
    (g : 𝓞 E →+* P) (b : 𝓞 E) (hb : b ≠ 0) : IsUnit (g b) := by
  have hI : Ideal.span {b} ≠ ⊥ := by simpa using hb
  have hn : Ideal.absNorm (Ideal.span {b}) ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (Ideal.absNorm_mem (Ideal.span {b}))
  set n := Ideal.absNorm (Ideal.span {b})
  have hu : IsUnit (g b * g c) := by
    rw [← map_mul, ← hc, map_natCast]
    have h1 : (n : P) = algebraMap ℚ P (n : ℚ) := by simp
    rw [h1]
    exact (isUnit_iff_ne_zero.2 (by exact_mod_cast hn : (n : ℚ) ≠ 0)).map _
  exact isUnit_of_mul_isUnit_left hu

theorem trace_lsmul_restrictScalars {K L V : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [AddCommGroup V] [Module K V] [Module L V] [IsScalarTower K L V] [FiniteDimensional L V] (a : L) :
    LinearMap.trace K V ((LinearMap.lsmul L V a).restrictScalars K) =
      (Module.finrank L V : K) * Algebra.trace K L a := by
  classical
  let b := Module.finBasis L V
  let c := Module.finBasis K L
  rw [LinearMap.trace_eq_matrix_trace K (c.smulTower b), Algebra.trace_eq_matrix_trace c]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Fintype.sum_prod_type, Algebra.leftMulMatrix_eq_repr_mul,
    Module.Basis.smulTower_repr_mk, smul_smul, Finsupp.single_apply, Finset.mul_sum, mul_comm]

end RepTrace

theorem repTrace_eq_mul_trace {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (s : ℕ)
    (hr : r = s * Module.finrank ℚ E) (a : 𝓞 E) : (ρ a).trace = s * Algebra.trace ℤ (𝓞 E) a := by
  classical
  let g : 𝓞 E →+* Module.End ℚ (Fin r → ℚ) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin r) (Fin r) ℚ ≃ₐ[ℚ] _).toRingEquiv.toRingHom.comp
      ((Int.castRingHom ℚ).mapMatrix.comp ρ)
  let A := Algebra.adjoin ℚ (Set.range g)
  haveI : IsMulCommutative A := Algebra.isMulCommutative_adjoin ℚ (s := Set.range g) (by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _
    change g x * g y = g y * g x
    rw [← map_mul, ← map_mul, mul_comm])
  letI : CommRing A := open scoped IsMulCommutative in inferInstance
  let g' : 𝓞 E →+* A := g.codRestrict A (fun x => Algebra.subset_adjoin ⟨x, rfl⟩)
  let φ : E →+* Module.End ℚ (Fin r → ℚ) :=
    (A.val : A →ₐ[ℚ] Module.End ℚ (Fin r → ℚ)).toRingHom.comp
      (IsLocalization.lift (M := nonZeroDivisors (𝓞 E)) (S := E) (g := g')
        (fun y => RepTrace.isUnit_of_ne_zero g' y (nonZeroDivisors.ne_zero y.2)))
  letI : Module E (Fin r → ℚ) := Module.compHom (Fin r → ℚ) φ
  have hφq : φ.comp (algebraMap ℚ E) = algebraMap ℚ (Module.End ℚ (Fin r → ℚ)) := Subsingleton.elim _ _
  haveI : IsScalarTower ℚ E (Fin r → ℚ) := ⟨fun q x v => by
    change φ (q • x) v = q • φ x v
    rw [Algebra.smul_def, map_mul, Module.End.mul_apply]
    have := RingHom.congr_fun hφq q
    simp only [RingHom.comp_apply] at this
    rw [this, Module.algebraMap_end_apply]⟩
  haveI : FiniteDimensional E (Fin r → ℚ) := Module.Finite.of_restrictScalars_finite ℚ E _
  have hfin : Module.finrank E (Fin r → ℚ) = s := by
    have h := Module.finrank_mul_finrank ℚ E (Fin r → ℚ)
    rw [Module.finrank_fin_fun] at h
    have hd : 0 < Module.finrank ℚ E := Module.finrank_pos
    have h2 : Module.finrank ℚ E * Module.finrank E (Fin r → ℚ) = Module.finrank ℚ E * s := by
      rw [h, hr, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hd h2
  have key : LinearMap.trace ℚ (Fin r → ℚ) (g a) = ((ρ a).trace : ℚ) := by
    change LinearMap.trace ℚ _ (Matrix.toLin' ((ρ a).map (Int.castRingHom ℚ))) = _
    rw [LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ (Fin r)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin']
    simp [Matrix.trace]
  have hga : g a = (LinearMap.lsmul E (Fin r → ℚ) (a : E)).restrictScalars ℚ := by
    refine LinearMap.ext fun v => ?_
    change g a v = φ (algebraMap (𝓞 E) E a) v
    simp only [φ, RingHom.comp_apply, IsLocalization.lift_eq]
    rfl
  apply Int.cast_injective (α := ℚ)
  rw [← key, hga, RepTrace.trace_lsmul_restrictScalars, hfin]
  push_cast
  rw [Algebra.coe_trace_int]

end GlobalTheory
end

section

open NumberField Polynomial

namespace GlobalTheory

theorem ringOfIntegers_action_injective (F : Type) [Field F] [NumberField F] (X : Type)
    [AddCommGroup X] [Module.Free ℤ X] [Nontrivial X] (ρ : 𝓞 F →+* Module.End ℤ X) :
    Function.Injective ρ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  have hmem : a ∈ RingHom.ker ρ := ha
  have hn : ((Ideal.absNorm (RingHom.ker ρ) : ℕ) : 𝓞 F) ∈ RingHom.ker ρ := Ideal.absNorm_mem _
  rw [RingHom.mem_ker, map_natCast] at hn
  obtain ⟨χ, hχ⟩ := exists_ne (0 : X)
  have h1 : (Ideal.absNorm (RingHom.ker ρ) : ℕ) • χ = 0 := by
    have := congrArg (fun f : Module.End ℤ X => f χ) hn
    simpa using this
  rw [← Nat.cast_smul_eq_nsmul ℤ] at h1
  have h2 : Ideal.absNorm (RingHom.ker ρ) = 0 := by
    rcases smul_eq_zero.mp h1 with h | h
    · exact_mod_cast h
    · exact absurd h hχ
  rw [Ideal.absNorm_eq_zero_iff] at h2
  rw [h2] at hmem
  simpa using hmem

theorem dvd_coord_of_action_dvd (F : Type) [Field F] [NumberField F] (X : Type)
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Nontrivial X]
    (ρ : 𝓞 F →+* Module.End ℤ X) (ι : Type) [Fintype ι] (b : Module.Basis ι ℤ (𝓞 F))
    (p : ℤ) (hp : p ≠ 0) (a : 𝓞 F)
    (h : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
      p ∣ (Module.Free.chooseBasis ℤ X).repr (ρ a χ) r) :
    ∀ i, p ∣ b.repr a i := by
  set B := Module.Free.chooseBasis ℤ X
  let T : Module.End ℤ X := B.constr ℤ (fun s => ∑ r, ((B.repr (ρ a (B s)) r) / p) • B r)
  have hT : algebraMap ℤ (Module.End ℤ X) p * T = ρ a := by
    apply B.ext
    intro s
    rw [Module.End.mul_apply, Module.algebraMap_end_apply]
    simp only [T, Module.Basis.constr_basis, Finset.smul_sum, smul_smul]
    conv_rhs => rw [← B.sum_repr (ρ a (B s))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Int.mul_ediv_cancel' (h _ r)]
  obtain ⟨f, hfm, hf⟩ := Algebra.IsIntegral.isIntegral (R := ℤ) T
  have hf' : aeval T f = 0 := by rw [aeval_def]; exact hf
  have h1 := Polynomial.scaleRoots_aeval_eq_zero (r := p) hf'
  rw [hT] at h1
  have h2 : aeval a (f.scaleRoots p) = 0 := by
    apply ringOfIntegers_action_injective F X ρ
    rw [map_zero]
    have := Polynomial.aeval_algHom_apply (ρ.toIntAlgHom) a (f.scaleRoots p)
    change ρ.toIntAlgHom _ = 0
    rw [← this]
    exact h1
  have h3 : aeval (algebraMap (𝓞 F) F a) (f.scaleRoots p) = 0 := by
    rw [Polynomial.aeval_algebraMap_apply, h2, map_zero]
  have hpF : (algebraMap ℤ F p) ≠ 0 := by simpa using hp
  set β : F := algebraMap (𝓞 F) F a / algebraMap ℤ F p with hβdef
  have hβa : algebraMap ℤ F p * β = algebraMap (𝓞 F) F a := by
    rw [hβdef]; field_simp
  have h4 : eval₂ (algebraMap ℤ F) β f = 0 := by
    have e := Polynomial.scaleRoots_eval₂_mul (p := f) (algebraMap ℤ F) β p
    rw [hβa, ← aeval_def, h3] at e
    exact (mul_eq_zero.mp e.symm).resolve_left (pow_ne_zero _ hpF)
  have hβ : IsIntegral ℤ β := ⟨f, hfm, h4⟩
  let y : 𝓞 F := ⟨β, hβ⟩
  have hy : p • y = a := by
    apply RingOfIntegers.coe_injective
    rw [map_zsmul, zsmul_eq_mul]
    have : algebraMap (𝓞 F) F y = β := rfl
    rw [this, ← hβa]
    simp
  intro i
  refine ⟨b.repr y i, ?_⟩
  rw [← hy, map_zsmul, Finsupp.smul_apply, smul_eq_mul]

theorem finrank_eq_zero_of_dual_killed : ∀ (F : Type) [Field F] [NumberField F] (X : Type)
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (ρ : 𝓞 F →+* Module.End ℤ X)
    (k : Type) [Field k] (ι : Type) [Fintype ι] (b : Module.Basis ι ℤ (𝓞 F)) (w : ι → k),
    w ≠ 0 → (∀ (l : X →+ k) (χ : X), ∑ i, w i * l (ρ (b i) χ) = 0) →
    Module.finrank ℤ X = 0 := by
  intro F _ _ X _ _ _ ρ k _ ι _ b w hw hyp
  classical
  by_contra hX
  haveI : Nontrivial X := Module.finrank_pos_iff.mp (Nat.pos_of_ne_zero hX)
  obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
    by_contra hc; push_neg at hc; exact hw (funext hc)
  set B := Module.Free.chooseBasis ℤ X
  have key : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
      ∑ i, (B.repr (ρ (b i) χ) r) • w i = 0 := by
    intro χ r
    have := hyp ((Int.castAddHom k).comp (B.coord r).toAddMonoidHom) χ
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [zsmul_eq_mul, mul_comm]
  have lin : ∀ (e : ι → ℤ) (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
      B.repr (ρ (∑ i, e i • b i) χ) r = ∑ i, e i * B.repr (ρ (b i) χ) r := by
    intro e χ r

    simp [map_sum, map_zsmul, LinearMap.sum_apply, Finsupp.finsetSum_apply]
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · set p := ringChar k with hpdef
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : CharP k p := ringChar.charP k
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    obtain ⟨π, hπ⟩ : ∃ π : Module.Dual (ZMod p) k, π (w i0) ≠ 0 := by
      by_contra hc; push_neg at hc
      exact hi0 ((Module.forall_dual_apply_eq_zero_iff (ZMod p) (w i0)).mp hc)
    set e : ι → ℤ := fun i => ((π (w i)).val : ℤ) with hedef
    have hdiv : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
        (p : ℤ) ∣ B.repr (ρ (∑ i, e i • b i) χ) r := by
      intro χ r
      rw [lin, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have := congrArg π (key χ r)

      rw [map_sum, map_zero] at this
      rw [← this]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, zsmul_eq_mul, hedef]
      simp [ZMod.natCast_zmod_val, mul_comm]
    have h := GlobalTheory.dvd_coord_of_action_dvd F X ρ ι b p (by exact_mod_cast hp.ne_zero) _ hdiv i0
    rw [Module.Basis.repr_sum_self] at h
    apply hπ
    rw [← ZMod.natCast_zmod_val (π (w i0))]
    have h' : ((((π (w i0)).val : ℕ) : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    exact_mod_cast h'
  · haveI : CharZero k := by
      have := ringChar.charP k; rw [hp] at this; exact CharP.charP_to_charZero k
    letI : Algebra ℚ k := DivisionRing.toRatAlgebra
    obtain ⟨π, hπ⟩ : ∃ π : Module.Dual ℚ k, π (w i0) ≠ 0 := by
      by_contra hc; push_neg at hc
      exact hi0 ((Module.forall_dual_apply_eq_zero_iff ℚ (w i0)).mp hc)
    set c : ι → ℚ := fun i => π (w i) with hcdef
    set e : ι → ℤ := fun i => (c i).num * ∏ j ∈ Finset.univ.erase i, ((c j).den : ℤ) with hedef
    have he : ∀ i, (e i : ℚ) = c i * ∏ j, ((c j).den : ℚ) := by
      intro i
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← mul_assoc, Rat.mul_den_eq_num, hedef]
      push_cast; rfl
    have hzero : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
        B.repr (ρ (∑ i, e i • b i) χ) r = 0 := by
      intro χ r
      rw [lin]
      have := congrArg π (key χ r)

      rw [map_sum, map_zero] at this
      simp only [map_zsmul] at this
      have h2 : ((∑ i, e i * B.repr (ρ (b i) χ) r : ℤ) : ℚ)
          = (∏ j, ((c j).den : ℚ)) * ∑ i, (B.repr (ρ (b i) χ) r) • π (w i) := by
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [he, zsmul_eq_mul, hcdef]; ring
      rw [this, mul_zero] at h2
      exact_mod_cast h2
    have hρ : ρ (∑ i, e i • b i) = 0 := by
      ext χ
      simp only [LinearMap.zero_apply]
      exact B.ext_elem fun r => by rw [hzero, map_zero, Finsupp.zero_apply]
    have ha : (∑ i, e i • b i) = 0 :=
      GlobalTheory.ringOfIntegers_action_injective F X ρ (by rw [hρ, map_zero])
    have h0 := congrArg (fun x => b.repr x i0) ha
    simp only [Module.Basis.repr_sum_self, map_zero, Finsupp.zero_apply] at h0
    have hc0 : c i0 ≠ 0 := hπ
    have : (e i0 : ℚ) ≠ 0 := by
      rw [he]
      exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (c j).den_nz)
    exact this (by exact_mod_cast h0)

end GlobalTheory
end
