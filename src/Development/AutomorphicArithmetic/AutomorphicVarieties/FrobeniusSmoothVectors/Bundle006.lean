module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem lc_of_open_ker {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (f : G →* H) (h : IsOpen (f.ker : Set G)) : IsLocallyConstant f :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f h

theorem UpperTheory.exists_locallyConstant_twistedCocycle_ne_zero_of_frameOk :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∃ u : F.G0 → k, IsLocallyConstant u ∧ (∀ g h : F.G0, u (g * h) = (F.Ψ h : k) * u g + u h) ∧ (∀ g : F.G0, u (F.star g) = (((F.Ψ g)⁻¹ : kˣ) : k) * u g) ∧ (∀ v, ∃ α : k, ∀ s, u (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - 1) * α) ∧ u ≠ 0 := by
  intro l _ k _ _ F C₀ h
  have hχ : ∀ g : F.G0, (F.Ψ⁻¹ * F.delK k) (g : F.Γ) = (F.Ψ g)⁻¹ := fun g => by
    have hg : F.del (g : F.Γ) = 1 := g.2
    simp [Frame.delK, hg]
  have hc : (F.Ψ⁻¹ * F.delK k) F.c = -1 := by
    apply Units.ext
    simp [Frame.delK, h.Ψ_c, h.del_c]
  have hl : ∀ v s, F.loc v s = ((F.loc0 v s : F.G0) : F.Γ) := fun _ _ => rfl
  obtain ⟨x, x1, x2, x3, x4, g₁, x5⟩ := UpperTheory.smooth_vector_fixed_by_open_subgroup h (F.Ψ⁻¹ * F.delK k) hc (fun v => by
    obtain ⟨s, hs⟩ := h.f3 v
    refine ⟨s, fun e => hs ?_⟩
    rw [hl, hχ, inv_eq_one] at e
    rw [hl, e, one_pow]) h.f4
  have x0 : x 1 = 0 := by
    have := x2 1 1
    simpa using this
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right h.c_sq
  refine ⟨fun g => x g * (F.Ψ g : k), ?_, fun g g' => ?_, fun g => ?_, fun v => ?_, fun e => x5 ?_⟩
  · exact (x1.mul ((lc_of_open_ker F.Ψ h.Ψ_open).comp Units.val)).comp_continuous continuous_subtype_val
  · show x ((g : F.Γ) * g') * (F.Ψ ((g : F.Γ) * g') : k) = _
    rw [x2, hχ, map_mul, Units.val_mul, Units.val_inv_eq_inv_val]
    have := (F.Ψ g).ne_zero
    field_simp
  · have hs : ((F.star g : F.G0) : F.Γ) = F.c * ((g : F.Γ)⁻¹ * F.c) := by
      show F.c * (g : F.Γ)⁻¹ * F.c⁻¹ = _
      rw [hci, mul_assoc]
    have h1 : x (g : F.Γ)⁻¹ + (F.Ψ g : k) * x g = 0 := by
      have := x2 (g : F.Γ)⁻¹ g
      rw [inv_mul_cancel, x0, map_inv, hχ, inv_inv] at this
      exact this.symm
    have hΨstar : F.Ψ (F.star g) = (F.Ψ g)⁻¹ := by
      have : ((F.star g : F.G0) : F.Γ) = F.c * (g : F.Γ)⁻¹ * F.c⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm]
    show x (F.star g) * (F.Ψ (F.star g) : k) = _
    rw [hΨstar, hs, x2, x2, x3, hc]
    simp only [Units.val_neg, Units.val_one]
    linear_combination (-(((F.Ψ g)⁻¹ : kˣ) : k)) * h1
  · obtain ⟨Y, hY⟩ := x4 v
    refine ⟨-Y, fun s => ?_⟩
    show x (F.loc v s) * (F.Ψ (F.loc v s) : k) = _
    rw [hY, hl, hχ, Units.val_inv_eq_inv_val]
    have := (F.Ψ (F.loc0 v s)).ne_zero
    field_simp
    ring
  · exact (mul_eq_zero.1 (congrFun e g₁)).resolve_right (F.Ψ g₁).ne_zero
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem w_rev (n : ℕ) (i : Fin n) : w n i.rev = - w n i := by
  have := i.isLt
  simp only [w, Fin.val_rev]
  split_ifs <;> omega

private theorem J_apply {K : Type} [CommRing K] {n : ℕ} (X : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (Jmat (R := K) n * Xᵀ * Jmat (R := K) n) i j = X j.rev i.rev := by
  simp only [Matrix.mul_apply, Jmat, Matrix.transpose_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have key : ∀ k : Fin n, (j = k.rev) ↔ (k = j.rev) := by
    intro k
    constructor
    · rintro rfl
      simp
    · rintro rfl
      simp
  simp only [key, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private def tw {K : Type} [CommRing K] (n : ℕ) (u : Kˣ) :
    Matrix (Fin n) (Fin n) K →ₐ[K] Matrix (Fin n) (Fin n) K where
  toFun X := Matrix.of fun i j => ((u ^ (w n i - w n j) : Kˣ) : K) * X i j
  map_one' := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  map_mul' X Y := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have : w n i - w n j = (w n i - w n a) + (w n a - w n j) := by ring
    rw [this, _root_.zpow_add, Units.val_mul]
    ring
  map_zero' := by ext i j; simp
  map_add' X Y := by ext i j; simp [mul_add]
  commutes' c := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.algebraMap_matrix_apply]

private theorem tw_apply {K : Type} [CommRing K] (n : ℕ) (u : Kˣ) (X : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    tw n u X i j = ((u ^ (w n i - w n j) : Kˣ) : K) * X i j := rfl

private theorem ordProd_tw {H K : Type} [CommRing K] {n : ℕ} (u : Kˣ)
    (r : H → Matrix (Fin n) (Fin n) K) (ψ : Fin n → H → K) (g : Fin n → H) :
    ordProd (fun s => tw n u (r s)) ψ g = tw n u (ordProd r ψ g) := by
  unfold ordProd
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp

theorem UpperTheory.V.Fr.alg_twist :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {K : Type} [CommRing K] (u : Kˣ) (ρ : NRep F n K), ∃ ρ' : NRep F n K, (∀ g i j, ρ'.r g i j = ((u ^ (w n i - w n j) : Kˣ) : K) * ρ.r g i j) ∧ ρ'.ψ = ρ.ψ := by
  intro l _ k _ F n K _ u ρ
  refine ⟨⟨(tw n u).toRingHom.toMonoidHom.comp ρ.r, ρ.ψ, ?_, ?_, ?_⟩, fun g i j => rfl, rfl⟩
  · intro g
    ext i j
    rw [J_apply]
    show tw n u (ρ.r (F.star g)) i j = tw n u (ρ.r g) j.rev i.rev
    rw [tw_apply, tw_apply, ρ.pol, J_apply, w_rev, w_rev]
    congr 3
    ring
  · intro i j h
    have := ρ.diag i j h
    rw [Matrix.sub_apply] at this ⊢
    show tw n u (ρ.r F.g0) i j - tw n u (ρ.r (F.star F.g0)) i j = 0
    rw [tw_apply, tw_apply, ← mul_sub, this, mul_zero]
  · intro v g
    have := ordProd_tw u (fun s => ρ.r (F.loc0 v s)) (fun i s => ((ρ.ψ v i s : Kˣ) : K)) g
    exact this.trans (by rw [ρ.ord, map_zero])
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem rbar_J {K : Type} [CommRing K] {n : ℕ} (X : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (Jmat (R := K) n * Xᵀ * Jmat (R := K) n) i j = X j.rev i.rev := by
  have h : ∀ x : Fin n, j = x.rev ↔ x = j.rev := fun x => by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp [Matrix.mul_apply, Jmat, h]

private theorem rbar_w {n : ℕ} (i : Fin n) : w n i.rev = - w n i := by
  have hi := i.2
  unfold w
  rw [Fin.val_rev]
  split_ifs with h <;> omega

private theorem rbar_prod {K : Type} [CommRing K] {n : ℕ} (L : List (Fin n → K)) :
    (L.map fun d => Matrix.diagonal d).prod = Matrix.diagonal L.prod := by
  induction L with
  | nil => simp [← Matrix.diagonal_one]
  | cons a L ih => rw [List.map_cons, List.prod_cons, ih, Matrix.diagonal_mul_diagonal, List.prod_cons]; rfl

private theorem rbar_ord {H K : Type} [CommRing K] {n : ℕ} (ψ : Fin n → H → K) (g : Fin n → H) :
    ordProd (fun s => Matrix.diagonal fun j => ψ j s) ψ g = 0 := by
  unfold ordProd
  have e : (List.ofFn fun i => (Matrix.diagonal fun j => ψ j (g i)) - ψ i (g i) • (1 : Matrix (Fin n) (Fin n) K)) =
      (List.ofFn fun i => fun j => ψ j (g i) - ψ i (g i)).map fun d => Matrix.diagonal d := by
    rw [List.map_ofFn]
    congr 1
    funext i
    ext a b
    by_cases h : a = b <;> simp [h, Matrix.one_apply]
  rw [e, rbar_prod, List.prod_ofFn, ← Matrix.diagonal_zero]
  congr 1
  funext j
  rw [Finset.prod_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)

theorem UpperTheory.V.Fr.rbar :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → ∃ ρ : NRep F n k, ρ.IsBar (RingHom.id k) ∧ ρ.IsDiag := by
  intro l _ k _ _ F C₀ n _
  have hs : ∀ g : F.G0, F.Ψ (F.star g) = (F.Ψ g)⁻¹ := fun g => by
    have : ((F.star g : F.G0) : F.Γ) = F.c * (g : F.Γ)⁻¹ * F.c⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm]
  refine ⟨{ r := { toFun := fun g => Matrix.diagonal fun i => ((F.Ψ g ^ w n i : kˣ) : k)
                   map_one' := by simp
                   map_mul' := fun g h => by simp [Matrix.diagonal_mul_diagonal, mul_zpow] }
            ψ := fun v i => (zpowGroupHom (w n i)).comp (F.Ψ.comp (F.loc v))
            pol := fun g => ?_
            diag := fun i j h => ?_
            ord := fun v g => ?_ }, ⟨fun g i => ?_, fun v i g => rfl⟩, fun g i j h => ?_⟩
  · ext i j
    rw [rbar_J]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, hs]
    by_cases h : i = j
    · subst h
      simp [rbar_w]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne]
      exact fun e => h (Fin.rev_injective e).symm
  · simp [Matrix.diagonal_apply_ne _ h]
  · exact rbar_ord (fun i s => ((F.Ψ (F.loc v s) ^ w n i : kˣ) : k)) g
  · simp
  · exact Matrix.diagonal_apply_ne _ h
end

section

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

def UpT {C : Type} [Zero C] {n : ℕ} (M : Matrix (Fin n) (Fin n) C) : Prop := ∀ i j, j < i → M i j = 0

def bor {K : Type} [CommRing K] {n : ℕ} (g : GL (Fin n) K) : Submodule K (Matrix (Fin n) (Fin n) K) where
  carrier := {X | UpT ((g : Matrix (Fin n) (Fin n) K) * X * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))}
  add_mem' {X Y} hX hY i j h := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, hX i j h, hY i j h, add_zero]
  zero_mem' i j _ := by simp
  smul_mem' c X hX i j h := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, hX i j h, smul_zero]

def lieT (K : Type) [CommRing K] (n : ℕ) : Matrix (Fin n) (Fin n) K := Matrix.diagonal fun i => ((w n i : ℤ) : K)

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k]

@[ext] structure Box (F : Frame l k) (n : ℕ) (C : Type) [CommRing C] where
  r : F.Γ →* GG (m := n) (R := C)
  nu : ∀ s, (r s).right = F.del s
  g : F.V → GL (Fin n) C
  tri : ∀ v s, UpT ((g v : Matrix (Fin n) (Fin n) C) * (r (F.loc v s)).mat *
    (((g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C))

variable {F : Frame l k} {n : ℕ}

namespace Box

variable {C C' : Type} [CommRing C] [CommRing C']

def map (f : C →+* C') (B : Box F n C) : Box F n C' where
  r := (GG.map f).comp B.r
  nu := B.nu
  g v := GeneralLinearGroup.map f (B.g v)
  tri v s i j h := by
    have e : ((GeneralLinearGroup.map f (B.g v) : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') *
        (((GG.map f).comp B.r) (F.loc v s)).mat *
        (((GeneralLinearGroup.map f (B.g v))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') =
        f.mapMatrix ((B.g v : Matrix (Fin n) (Fin n) C) * (B.r (F.loc v s)).mat *
          (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) := by
      rw [map_mul, map_mul, ← map_inv]
      rfl
    rw [e]
    exact (congrArg f (B.tri v s i j h)).trans (map_zero f)

theorem map_map {C'' : Type} [CommRing C''] (f : C →+* C') (f' : C' →+* C'') (B : Box F n C) :
    (B.map f).map f' = B.map (f'.comp f) := rfl

def Cont (I : Ideal C) (B : Box F n C) : Prop := ∀ i j, AdicCont I fun s => (B.r s).mat i j

structure Of (B : Box F n C) (ρ : NRep F n C) : Prop where
  atc : (B.r F.c).mat = 1
  res : ∀ s : F.G0, (B.r s).mat = ρ.r s
  psi : ∀ v i s, ((B.g v : Matrix (Fin n) (Fin n) C) * ρ.r (F.loc0 v s) *
    (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) i i = ρ.ψ v i s

theorem Of.map {B : Box F n C} {ρ : NRep F n C} (h : B.Of ρ) (f : C →+* C') : (B.map f).Of (ρ.map f) := by
  refine ⟨?_, ?_, ?_⟩
  · show ((B.r F.c).mat).map f = 1
    rw [h.atc]
    exact Matrix.map_one _ (map_zero f) (map_one f)
  · intro s
    show ((B.r s).mat).map f = _
    rw [h.res]
    rfl
  · intro v i s
    have e : (((B.map f).g v : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') * (ρ.map f).r (F.loc0 v s) *
        ((((B.map f).g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') =
        f.mapMatrix ((B.g v : Matrix (Fin n) (Fin n) C) * ρ.r (F.loc0 v s) *
          (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) := by
      rw [map_mul, map_mul]
      rfl
    rw [e]
    exact congrArg f (h.psi v i s)

def ad (B : Box F n C) : Representation C F.Γ (Matrix (Fin n) (Fin n) C) := adRep B.r

def b (B : Box F n C) (v : F.V) : Submodule C (Matrix (Fin n) (Fin n) C) := bor (B.g v)

end Box

structure NRep.Good {K : Type} [Field K] (ρ : NRep F n K) : Prop where
  two : (2 : K) ≠ 0
  zd : ∀ i j, i ≠ j → (ρ.r F.g0 - ρ.r (F.star F.g0)) i i ≠ (ρ.r F.g0 - ρ.r (F.star F.g0)) j j
  ψd : ∀ v, ∃ s, ∀ i j, i ≠ j → ρ.ψ v i s ≠ ρ.ψ v j s

section CO

variable (O : Type) [CommRing O] [IsLocalRing O]

abbrev NRep.bar {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (ρ : NRep F n C) : NRep F n (ResidueField O) :=
  ρ.map (res O C : C →+* ResidueField O)

abbrev Box.bar {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (B : Box F n C) : Box F n (ResidueField O) :=
  B.map (res O C : C →+* ResidueField O)

structure NRep.Univ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (ρ : NRep F n R) : Prop where
  cont : ρ.Cont (maximalIdeal R)
  univ : ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (ρ' : NRep F n C), ρ'.Cont (maximalIdeal C) →
    ρ'.bar O = ρ.bar O → ∃! g : R →ₐ[O] C, ρ.map (g : R →+* C) = ρ'

abbrev Tan (R : Type) [CommRing R] [Algebra O R] [IsCO O R] : Submodule (ResidueField O) (R →ₗ[O] ResidueField O) :=
  PtDer (res O R) (ResidueField O)

def Box.tanCo {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (B : Box F n R) :
    (R →ₗ[O] ResidueField O) →ₗ[ResidueField O] (F.Γ → Matrix (Fin n) (Fin n) (ResidueField O)) where
  toFun D s := (B.r s).mat.map D *
    ((((B.bar O).r s).left⁻¹ : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O))
  map_add' D D' := funext fun s => by
    rw [Pi.add_apply, ← Matrix.add_mul]
    rfl
  map_smul' c D := funext fun s => by
    rw [Pi.smul_apply, RingHom.id_apply, ← Matrix.smul_mul]
    rfl

structure IsSq {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (μ : ResidueField O →+ C) : Prop where
  mul : ∀ a c, μ (res O C a * c) = a * μ c
  mem : ∀ c, μ c ∈ maximalIdeal C

variable {O}


open Classical in
def evK {C : Type} [CommRing C] [Algebra O C] (K : Ideal C) (u : K →ₗ[O] ResidueField O) (x : C) : ResidueField O :=
  if h : x ∈ K then u ⟨x, h⟩ else 0

theorem evK_of_mem {C : Type} [CommRing C] [Algebra O C] {K : Ideal C} (u : K →ₗ[O] ResidueField O) {x : C}
    (h : x ∈ K) : evK K u x = u ⟨x, h⟩ := dite_eq_left h

variable {C' C : Type} [CommRing C'] [Algebra O C'] [IsCO O C'] [CommRing C] [Algebra O C]

structure SetLift (p : C' →ₐ[O] C) (B : Box F n C) where
  r : F.Γ → GL (Fin n) C'
  r_cont : ∀ i j, AdicCont (maximalIdeal C') fun s => r s i j
  r_map : ∀ s, GeneralLinearGroup.map (p : C' →+* C) (r s) = (B.r s).left
  g : F.V → GL (Fin n) C'
  g_map : ∀ v, GeneralLinearGroup.map (p : C' →+* C) (g v) = B.g v
  t : ∀ v, F.Gv v → GL (Fin n) C'
  t_cont : ∀ v i j, AdicCont (maximalIdeal C') fun s => t v s i j
  t_tri : ∀ v s, UpT (t v s : Matrix (Fin n) (Fin n) C')
  t_map : ∀ v s, GeneralLinearGroup.map (p : C' →+* C) (t v s) = B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹

namespace SetLift

variable {p : C' →ₐ[O] C} {B : Box F n C} (D : SetLift p B)

def om (x : F.Γ × F.Γ) : Matrix (Fin n) (Fin n) C' :=
  ((D.r x.1 * sgnAct n C' (F.del x.1) (D.r x.2) * (D.r (x.1 * x.2))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') - 1

def a (v : F.V) (s : F.Gv v) : Matrix (Fin n) (Fin n) C' :=
  ((D.r (F.loc v s) * ((D.g v)⁻¹ * D.t v s * D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') - 1

def co : (RingHom.ker p →ₗ[O] ResidueField O) →ₗ[ResidueField O]
    (F.Γ × F.Γ → Matrix (Fin n) (Fin n) (ResidueField O)) × (∀ v, F.Gv v → Matrix (Fin n) (Fin n) (ResidueField O)) where
  toFun u := (fun x => (D.om x).map (evK _ u), fun v s => (D.a v s).map (evK _ u))
  map_add' u u' := by
    have e : ∀ x, evK _ (u + u') x = evK _ u x + evK _ u' x := fun x => by
      unfold evK
      split_ifs <;> simp
    ext <;> simp [e]
  map_smul' c u := by
    have e : ∀ x, evK _ (c • u) x = c * evK _ u x := fun x => by
      unfold evK
      split_ifs <;> simp
    ext <;> simp [e]

end SetLift


variable (O) in
def HasObs (R : Type) [CommRing R] [Algebra O R] (H : Type) [AddCommGroup H] [Module (ResidueField O) H] : Prop :=
  ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (p : C' →ₐ[O] R), Function.Surjective p →
    maximalIdeal C' * RingHom.ker p = ⊥ →
    ∃ ob : (RingHom.ker p →ₗ[O] ResidueField O) →ₗ[ResidueField O] H, ∀ u, ob u = 0 →
      ∀ (C'' : Type) [CommRing C''] [Algebra O C''] [IsCO O C''] (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R),
        p''.comp q = p → Function.Surjective q → (∀ y : RingHom.ker p, u y = 0 → q y = 0) →
        ∃ s : R →ₐ[O] C'', p''.comp s = AlgHom.id O R

def IsMinPres {σ R : Type} [CommRing R] [Algebra O R] (p : MvPowerSeries σ O →ₐ[O] R) : Prop :=
  Function.Surjective p ∧ ∀ f ∈ RingHom.ker p, ∀ s, MvPowerSeries.coeff (Finsupp.single s 1) f ∈ maximalIdeal O

end CO

end UpperTheory.V.Fr
end
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.iwahori_factorization_lower_diag_upper :
    ∀ {H Q : Type} [CommRing Q] (r : H → Matrix (Fin 3) (Fin 3) Q) (ψ : Fin 3 → H → Q) (s₀ : H), (∀ i j, i ≠ j → IsUnit (ψ i s₀ - ψ j s₀)) → (∀ s i j, i < j → r s i j = 0) → (∀ s i, r s i i = ψ i s) → (∀ g, ordProd r ψ g = 0) → ∃ α β γ : Q, ∀ s, r s 1 0 = (ψ 0 s - ψ 1 s) * α ∧ r s 2 1 = (ψ 1 s - ψ 2 s) * β ∧ r s 2 0 = (ψ 0 s - ψ 2 s) * γ - (ψ 1 s - ψ 2 s) * (α * β) := by
  intro H Q _ r ψ s₀ hu hup hd h0
  have key : ∀ a b c : H, (r a - ψ 0 a • 1) * ((r b - ψ 1 b • 1) * (r c - ψ 2 c • 1)) = 0 := by
    intro a b c
    simpa [ordProd, List.ofFn_succ] using h0 ![a, b, c]
  obtain ⟨u', e1⟩ : ∃ u' : Q, (ψ 0 s₀ - ψ 1 s₀) * u' = 1 := ⟨_, (hu 0 1 (by decide)).mul_val_inv⟩
  obtain ⟨v', e2⟩ : ∃ v' : Q, (ψ 1 s₀ - ψ 2 s₀) * v' = 1 := ⟨_, (hu 1 2 (by decide)).mul_val_inv⟩
  obtain ⟨w', e3⟩ : ∃ w' : Q, (ψ 0 s₀ - ψ 2 s₀) * w' = 1 := ⟨_, (hu 0 2 (by decide)).mul_val_inv⟩
  have hx : ∀ s, r s 1 0 = (ψ 0 s - ψ 1 s) * (r s₀ 1 0 * u') := by
    intro s
    have e := congrFun (congrFun (key s₀ s s₀) 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, hd, hup _ 0 1 (by decide),
      hup _ 0 2 (by decide), hup _ 1 2 (by decide)] at e
    have F : r s₀ 1 0 * (ψ 0 s - ψ 1 s) = (ψ 0 s₀ - ψ 1 s₀) * r s 1 0 := by
      linear_combination w' * e - (r s₀ 1 0 * (ψ 0 s - ψ 1 s) - (ψ 0 s₀ - ψ 1 s₀) * r s 1 0) * e3
    linear_combination (-(r s 1 0)) * e1 - u' * F
  have hy : ∀ s, r s 2 1 = (ψ 1 s - ψ 2 s) * (r s₀ 2 1 * v') := by
    intro s
    have e := congrFun (congrFun (key s₀ s₀ s) 2) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, hd, hup _ 0 1 (by decide),
      hup _ 0 2 (by decide), hup _ 1 2 (by decide)] at e
    have G : r s₀ 2 1 * (ψ 1 s - ψ 2 s) = (ψ 1 s₀ - ψ 2 s₀) * r s 2 1 := by
      linear_combination (-w') * e - (r s₀ 2 1 * (ψ 1 s - ψ 2 s) - (ψ 1 s₀ - ψ 2 s₀) * r s 2 1) * e3
    linear_combination (-(r s 2 1)) * e2 - v' * G
  refine ⟨r s₀ 1 0 * u', r s₀ 2 1 * v',
    r s₀ 1 0 * u' * (r s₀ 2 1 * v') +
      ((ψ 1 s₀ - ψ 2 s₀) * r s₀ 2 0 - r s₀ 2 1 * r s₀ 1 0) * w' * v', fun s => ⟨hx s, hy s, ?_⟩⟩
  have e := congrFun (congrFun (key s₀ s₀ s) 2) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, hd, hup _ 0 1 (by decide),
    hup _ 0 2 (by decide), hup _ 1 2 (by decide)] at e
  have Z : (ψ 0 s₀ - ψ 2 s₀) * (ψ 1 s₀ - ψ 2 s₀) * r s 2 0 =
      (ψ 0 s₀ - ψ 2 s₀) * r s₀ 2 1 * r s 1 0 +
        (ψ 0 s - ψ 2 s) * ((ψ 1 s₀ - ψ 2 s₀) * r s₀ 2 0 - r s₀ 2 1 * r s₀ 1 0) := by
    linear_combination e
  linear_combination w' * v' * Z + r s₀ 2 1 * v' * hx s +
    (r s₀ 2 1 * v' * r s 1 0 - r s 2 0) * e3 - (ψ 0 s₀ - ψ 2 s₀) * w' * r s 2 0 * e2
end
