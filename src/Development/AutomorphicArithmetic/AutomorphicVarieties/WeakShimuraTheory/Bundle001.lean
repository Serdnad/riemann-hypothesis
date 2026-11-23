module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle038
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
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

section
variable {ι Γ R R' R'' : Type} [Group Γ] [CommRing R] [CommRing R'] [CommRing R'']

theorem PD.map_map (P : PD ι Γ R) (f : R →+* R') (g : R' →+* R'') : (P.map f).map g = P.map (g.comp f) := rfl

theorem adj_map (f : R →+* R') (X : M4 R) : adj (X.map f) = (adj X).map f := by
  ext i j
  simp only [adj_apply, Matrix.map_apply]
  rw [map_zsmul]

theorem isGSp_map (f : R →+* R') {ν : R} {X : M4 R} (h : IsGSp ν X) : IsGSp (f ν) (X.map f) := by
  unfold IsGSp at h ⊢
  rw [adj_map, ← Matrix.map_mul, h]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.one_apply]
  split_ifs <;> simp

theorem PD.map_r (P : PD ι Γ R) (f : R →+* R') (g : Γ) : (P.map f).r g = (P.r g).map f := rfl

theorem PD.map_n (P : PD ι Γ R) (f : R →+* R') (v : ι) : (P.map f).n v = (P.n v).map f := rfl

theorem PD.map_flag (P : PD ι Γ R) (f : R →+* R') (v : ι) (s : Γ) :
    adj ((P.map f).n v) * (P.map f).r s * (P.map f).n v = (adj (P.n v) * P.r s * P.n v).map f := by
  rw [PD.map_r, PD.map_n, adj_map, ← Matrix.map_mul, ← Matrix.map_mul]

theorem PD.map_ψ (P : PD ι Γ R) (f : R →+* R') (v : ι) (i : Fin 4) (s : Γ) : (P.map f).ψ v i s = f (P.ψ v i s) := by
  unfold PD.ψ
  rw [PD.map_flag]
  rfl

theorem PD.Cont.map [TopologicalSpace Γ] {P : PD ι Γ R} {I : Ideal R} (h : P.Cont I) (f : R →+* R') {J : Ideal R'}
    (hf : I ≤ J.comap f) : (P.map f).Cont J := by
  intro i j N
  have hle : I ^ N ≤ (J ^ N).comap f :=
    (Ideal.pow_right_mono hf N).trans (Ideal.le_comap_pow f N)
  have := (h i j N).comp (Ideal.quotientMap (J ^ N) f hle)
  convert this using 1
  rfl

end

theorem Fr.IsPair.map {O Γ R R' : Type} [CommRing O] [Group Γ] [CommRing R] [CommRing R'] {Φ : Fr O Γ} {a : O →+* R}
    {P : PD Φ.ι Γ R} (h : Φ.IsPair a P) (f : R →+* R') : Φ.IsPair (f.comp a) (P.map f) := by
  refine ⟨fun g => isGSp_map f (h.mult g), ?_, h.nrm.map f.map_zero, ?_, ?_, ?_⟩
  · intro g hg
    rw [PD.map_r, h.kill g hg]
    exact Matrix.map_one _ f.map_zero f.map_one
  · intro v
    refine ⟨?_, ?_, ?_⟩
    · simpa [PD.map_n] using isGSp_map f (h.low v).1
    · intro i
      rw [PD.map_n, Matrix.map_apply, (h.low v).2.1, map_one]
    · intro i j hij
      rw [PD.map_n, Matrix.map_apply, (h.low v).2.2 i j hij, map_zero]
  · intro v s hs i j hij
    rw [PD.map_flag, Matrix.map_apply, h.flag v s hs i j hij, map_zero]
  · intro v s hs i
    rw [PD.map_ψ, h.mu v s hs i, map_one]

section
variable {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ]
  {a : O →+* Λ} (X : Space Φ a)

theorem Space.noeth : IsNoetherianRing X.A :=
  haveI := X.ft
  Algebra.FiniteType.isNoetherianRing X.B X.A

theorem Space.pair_map {R : Type} [CommRing R] [Algebra Λ R] (f : X.A →ₐ[Λ] R) :
    Φ.IsPair ((algebraMap Λ R).comp a) (X.P.map (f : X.A →+* R)) := by
  have := X.pair.map (f : X.A →+* R)
  convert this using 1
  ext x
  simp

theorem Space.cont_map {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (f : X.A →ₐ[Λ] R) :
    (X.P.map (f : X.A →+* R)).Cont (maximalIdeal R) := by
  refine X.cont.map _ (Ideal.map_le_iff_le_comap.2 fun b hb => ?_)
  show (f.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b ∈ maximalIdeal R
  rw [← res_eq_zero_iff Λ, res_map (O := Λ) (R := X.B), res_eq_zero_iff]
  exact hb

theorem Space.hom_ext {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (f f' : X.A →ₐ[Λ] R)
    (h : X.P.map (f : X.A →+* R) = X.P.map (f' : X.A →+* R)) : f = f' := by
  have hr : ∀ g i j, f (X.P.r g i j) = f' (X.P.r g i j) := by
    intro g i j
    have := congrArg (fun Q => Q.r g i j) h
    exact this
  have hn : ∀ v i j, f (X.P.n v i j) = f' (X.P.n v i j) := by
    intro v i j
    have := congrArg (fun Q => Q.n v i j) h
    exact this
  have hB : f.comp (IsScalarTower.toAlgHom Λ X.B X.A) = f'.comp (IsScalarTower.toAlgHom Λ X.B X.A) := by
    apply X.genB R
    · intro g n
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
      rw [← Polynomial.coeff_map, X.cp_map]
      have e : ∀ φ : X.A →ₐ[Λ] R, φ ((X.P.r g).charpoly.coeff n) =
          (((X.P.r g).map (φ : X.A →+* R)).charpoly).coeff n := by
        intro φ
        rw [Matrix.charpoly_map, Polynomial.coeff_map]
        rfl
      rw [e f, e f']
      exact congrArg (fun Q => (Q.r g).charpoly.coeff n) h
    · intro v i s hs
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
      rw [X.ψ_map v i s hs]
      have := congrArg (fun Q => Q.ψ v i s) h
      simp only [PD.map_ψ] at this
      exact this
  ext x
  have hx : x ∈ Algebra.adjoin X.B
      ((Set.range fun x : Γ × Fin 4 × Fin 4 => X.P.r x.1 x.2.1 x.2.2) ∪
        Set.range fun x : Φ.ι × Fin 4 × Fin 4 => X.P.n x.1 x.2.1 x.2.2) := by
    rw [X.gen]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with ⟨⟨g, i, j⟩, rfl⟩ | ⟨⟨v, i, j⟩, rfl⟩
    · exact hr g i j
    · exact hn v i j
  | algebraMap b =>
    exact DFunLike.congr_fun hB b
  | add y z _ _ hy hz => rw [map_add (f := _), map_add (f := _), hy, hz]
  | mul y z _ _ hy hz => rw [map_mul, map_mul, hy, hz]

end

end UpperTheory.V.Ws
end

section

noncomputable section

open UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Ws

section Mat

variable {R : Type} [CommRing R]

def cmp (m : Fin 4 → ℤ) (p : ℤ) : M4 R →ₗ[R] M4 R where
  toFun X := Matrix.of fun i j => if m i - m j = p then X i j else 0
  map_add' X Y := by ext i j; simp only [Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp
  map_smul' c X := by ext i j; simp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]; split_ifs <;> simp

theorem cmp_apply (m : Fin 4 → ℤ) (p : ℤ) (X : M4 R) (i j : Fin 4) :
    cmp m p X i j = if m i - m j = p then X i j else 0 := rfl

def FGe (m : Fin 4 → ℤ) (p : ℤ) (X : M4 R) : Prop := ∀ i j, m i - m j < p → X i j = 0

def Lim (m : Fin 4 → ℤ) (A A₀ : M4 R) : Prop := FGe m 0 A ∧ A₀ = cmp m 0 A

def Symp (m : Fin 4 → ℤ) : Prop := ∀ i : Fin 4, m i + m i.rev = m 0 + m 3

theorem FGe.mul {m : Fin 4 → ℤ} {p q : ℤ} {A B : M4 R} (hA : FGe m p A) (hB : FGe m q B) : FGe m (p + q) (A * B) :=
  _root_.UpperTheory.Reformulated.B.Qk42.mul hA hB

theorem cmp_mul {m : Fin 4 → ℤ} {p q : ℤ} {A B : M4 R} (hA : FGe m p A) (hB : FGe m q B) :
    cmp m (p + q) (A * B) = cmp m p A * cmp m q B := by
  ext i j
  simp only [cmp_apply, Matrix.mul_apply]
  split_ifs with h
  · refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h1 : m i - m l < p
    · simp [hA i l h1]
    · by_cases h2 : m l - m j < q
      · simp [hB l j h2]
      · rw [if_pos (by omega), if_pos (by omega)]
  · refine (Finset.sum_eq_zero fun l _ => ?_).symm
    split_ifs with h1 h2
    · omega
    all_goals simp

theorem FGe.add {m : Fin 4 → ℤ} {p : ℤ} {A B : M4 R} (hA : FGe m p A) (hB : FGe m p B) : FGe m p (A + B) :=
  fun i j h => by rw [Matrix.add_apply, hA i j h, hB i j h, add_zero]

theorem FGe.sub {m : Fin 4 → ℤ} {p : ℤ} {A B : M4 R} (hA : FGe m p A) (hB : FGe m p B) : FGe m p (A - B) :=
  fun i j h => by rw [Matrix.sub_apply, hA i j h, hB i j h, sub_zero]

theorem FGe.adj {m : Fin 4 → ℤ} (hm : Symp m) {p : ℤ} {A : M4 R} (hA : FGe m p A) : FGe m p (adj A) := by
  intro i j h
  have h1 := hm i
  have h2 := hm j
  rw [adj_apply, hA _ _ (by omega), smul_zero]

theorem cmp_adj {m : Fin 4 → ℤ} (hm : Symp m) (p : ℤ) (A : M4 R) : cmp m p (adj A) = adj (cmp m p A) := by
  ext i j
  have h1 := hm i
  have h2 := hm j
  simp only [cmp_apply, adj_apply]
  by_cases h : m i - m j = p
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega), smul_zero]

end Mat

namespace Fr

variable {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) {R : Type} [CommRing R]

def cmpT (m : Fin 4 → ℤ) (p : ℤ) : ((Γ → M4 R) × (Φ.ι → M4 R)) →ₗ[R] ((Γ → M4 R) × (Φ.ι → M4 R)) :=
  LinearMap.prodMap ((cmp m p).compLeft Γ) ((cmp m p).compLeft Φ.ι)

theorem cmpT_fst (m : Fin 4 → ℤ) (p : ℤ) (x : (Γ → M4 R) × (Φ.ι → M4 R)) (g : Γ) :
    (Φ.cmpT m p x).1 g = cmp m p (x.1 g) := rfl

theorem cmpT_snd (m : Fin 4 → ℤ) (p : ℤ) (x : (Γ → M4 R) × (Φ.ι → M4 R)) (v : Φ.ι) :
    (Φ.cmpT m p x).2 v = cmp m p (x.2 v) := rfl

variable [TopologicalSpace Γ]

def TanS (S : Finset (ℤ × ℤ)) (c : PD Φ.ι Γ R) : Submodule R ((Γ → M4 R) × (Φ.ι → M4 R)) where
  carrier := Φ.Tan S c
  add_mem' := by
    rintro x y ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩
    refine ⟨a1.add b1, fun g => add_mem (a2 g) (b2 g), fun g h => ?_, fun g h => ?_, a5.add b5, fun g i j h1 h2 => ?_,
      fun v => ⟨add_mem (a7 v).1 (b7 v).1, fun i j h => ?_⟩, fun v s hs i j h => ?_⟩
    · simp only [Prod.fst_add, Pi.add_apply, a3, b3, mul_add, add_mul]; abel
    · simp [a4 g h, b4 g h]
    · simp only [Prod.fst_add, Pi.add_apply, add_mul, Matrix.add_apply, a6 g i j h1 h2, b6 g i j h1 h2, add_zero]
    · simp only [Prod.snd_add, Pi.add_apply, add_mul, mul_add, Matrix.add_apply, (a7 v).2 i j h, (b7 v).2 i j h, add_zero]
    · have e : (x + y).1 s + c.r s * (x + y).2 v * c.r s⁻¹ - (x + y).2 v =
          (x.1 s + c.r s * x.2 v * c.r s⁻¹ - x.2 v) + (y.1 s + c.r s * y.2 v * c.r s⁻¹ - y.2 v) := by
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, add_mul]; abel
      rw [e, mul_add, add_mul, Matrix.add_apply, a8 v s hs i j h, b8 v s hs i j h, add_zero]
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ => zero_mem _, by simp, by simp, Matrix.isDiag_zero,
    fun g i j _ _ => by simp, fun v => ⟨zero_mem _, by simp⟩, fun v s _ i j _ => by simp⟩
  smul_mem' := by
    rintro t x ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
    refine ⟨a1.comp (t • ·), fun g => Submodule.smul_mem _ t (a2 g), fun g h => ?_, fun g h => ?_, a5.smul t,
      fun g i j h1 h2 => ?_, fun v => ⟨Submodule.smul_mem _ t (a7 v).1, fun i j h => ?_⟩, fun v s hs i j h => ?_⟩
    · simp only [Prod.smul_fst, Pi.smul_apply, a3, smul_add, Matrix.mul_smul, Matrix.smul_mul]
    · simp [a4 g h]
    · simp only [Prod.smul_fst, Pi.smul_apply, Matrix.smul_mul, Matrix.smul_apply, a6 g i j h1 h2, smul_zero]
    · simp only [Prod.smul_snd, Pi.smul_apply, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, (a7 v).2 i j h, smul_zero]
    · have e : (t • x).1 s + c.r s * (t • x).2 v * c.r s⁻¹ - (t • x).2 v =
          t • (x.1 s + c.r s * x.2 v * c.r s⁻¹ - x.2 v) := by
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_sub]
      rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, a8 v s hs i j h, smul_zero]

theorem span_Tan (S : Finset (ℤ × ℤ)) (c : PD Φ.ι Γ R) : Submodule.span R (Φ.Tan S c) = Φ.TanS S c :=
  Submodule.span_eq (Φ.TanS S c)

variable (a : O →+* R)

def OneOdd (S : Finset (ℤ × ℤ)) (c : PD Φ.ι Γ R) : Prop :=
  ∃ i₀ j₀ : Fin 4, wt i₀ j₀ ∈ oddRoots ∧ ∀ x ∈ Φ.Tan S c, (∀ g, x.1 g i₀ j₀ = 0) →
    ∀ i j : Fin 4, i ≤ j.rev → wt i j ∈ oddRoots → ∃ n, Φ.LocTriv a (wt i j) (fun g => x.1 g i j) n


omit [TopologicalSpace Γ] in
def splitPs (b : Φ.ι → R) : PD Φ.ι Γ R := ⟨(Φ.split a).r, fun v => 1 + b v • Xm R⟩

variable {Φ a}

theorem Ok.rt_wt (h : Φ.Ok a) (i j : Fin 4) (g : Γ) : Φ.rt (wt i j) g = Φ.χ i g * (Φ.χ j g)⁻¹ := by
  have h0 := h.mul 0 g
  have h1 := h.mul 1 g
  have e : Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g * (Φ.χ 0 g)⁻¹ := by
    have : Φ.χ 0 g * Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g := h0.trans h1.symm
    rw [← this, mul_comm (Φ.χ 0 g), mul_inv_cancel_right]
  apply Additive.ofMul.injective
  fin_cases i <;> fin_cases j <;>
    simp [Fr.rt, wt, lamW, muW, e] <;> abel

theorem Ok.conj_split (h : Φ.Ok a) (g : Γ) (Y : M4 R) (i j : Fin 4) :
    ((Φ.split a).r g * Y * (Φ.split a).r g⁻¹) i j = a (Φ.rt (wt i j) g) * Y i j := by
  have e : ∀ g, (Φ.split a).r g = Matrix.diagonal fun i => a (Φ.χ i g) := fun g => by
    ext i j
    simp only [Fr.split, mapRep_apply, diagRep, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.diagonal_apply]
    split_ifs <;> simp
  rw [e, e, Matrix.mul_diagonal, Matrix.diagonal_mul, h.rt_wt, map_inv, Units.val_mul, map_mul]
  ring

omit [TopologicalSpace Γ] in
theorem split_r_apply (g : Γ) (i j : Fin 4) : (Φ.split a).r g i j = if i = j then a (Φ.χ i g) else 0 := by
  simp only [Fr.split, mapRep_apply, diagRep, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.diagonal_apply]
  split_ifs <;> simp

end Fr

end UpperTheory.V.Ws

end
end
