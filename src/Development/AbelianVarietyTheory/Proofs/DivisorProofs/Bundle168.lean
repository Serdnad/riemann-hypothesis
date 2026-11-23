module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle089
public import Mathlib.Data.Matrix.Basis
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle101
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TensorProduct.Maps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

@[expose] public section

section

namespace GlobalTheory.MoritaLocal

open GlobalTheory.Morita

theorem smul_eq_zero_of_equiv {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M]
    {n : ℕ} (e : M ≃ₗ[R] (Fin n → R ⧸ I)) {c : R} (hc : c ∈ I) (x : M) : c • x = 0 := by
  apply e.injective
  rw [map_smul, map_zero]
  funext i
  simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hc]

theorem corner_equiv {R : Type} [CommRing R] (I : Ideal R) (hI : IsLocalRing (R ⧸ I)) {m k : ℕ} (hm : 0 < m)
    (C : Type) [AddCommGroup C] [Module R C] (e : (Fin m → C) ≃ₗ[R] (Fin (m * k) → R ⧸ I)) :
    Nonempty (C ≃ₗ[R] (Fin k → R ⧸ I)) := by
  have hC : Module.IsTorsionBySet R C I := by
    intro x a
    have h := congrFun (smul_eq_zero_of_equiv I e a.2 (Pi.single (⟨0, hm⟩ : Fin m) x)) ⟨0, hm⟩
    simpa using h
  letI : Module (R ⧸ I) C := hC.module
  haveI : IsScalarTower R (R ⧸ I) C := hC.isScalarTower
  let e' : (Fin m → C) ≃ₗ[R ⧸ I] (Fin (m * k) → R ⧸ I) :=
    LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective e
  haveI : Module.Finite (R ⧸ I) (Fin m → C) := Module.Finite.equiv e'.symm
  haveI : Module.Free (R ⧸ I) (Fin m → C) := Module.Free.of_equiv e'.symm
  let i0 : C →ₗ[R ⧸ I] (Fin m → C) := LinearMap.single (R ⧸ I) (fun _ => C) ⟨0, hm⟩
  let p0 : (Fin m → C) →ₗ[R ⧸ I] C := LinearMap.proj ⟨0, hm⟩
  haveI : Module.Projective (R ⧸ I) C := Module.Projective.of_split i0 p0 (by ext x; simp [i0, p0])
  haveI : Module.Finite (R ⧸ I) C := Module.Finite.of_surjective p0 (fun x => ⟨Pi.single ⟨0, hm⟩ x, by simp [p0]⟩)
  haveI : Module.Free (R ⧸ I) C := Module.free_of_flat_of_isLocalRing
  have h1 : Module.finrank (R ⧸ I) (Fin m → C) = m * k := by
    rw [e'.finrank_eq, Module.finrank_fin_fun]
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  have h2 : Module.finrank (R ⧸ I) C = k := Nat.eq_of_mul_eq_mul_left hm h1
  exact ⟨(LinearEquiv.ofFinrankEq C (Fin k → R ⧸ I) (by rw [h2, Module.finrank_fin_fun])).restrictScalars R⟩

section
variable {R : Type} [CommRing R] {I : Ideal R} {m : ℕ} {O : Type} [Ring O] [Algebra R O]
  {φ : O →ₐ[R] Matrix (Fin m) (Fin m) (R ⧸ I)}
  {P : Type} [AddCommGroup P] [Module O P] [Module R P] [IsScalarTower R O P]

theorem act_congr (hker : ∀ b, φ b = 0 → b ∈ I • (⊤ : Submodule R O)) (hP : ∀ c ∈ I, ∀ x : P, c • x = 0)
    {b b' : O} (h : φ b = φ b') (x : P) : b • x = b' • x := by
  have hb : b - b' ∈ I • (⊤ : Submodule R O) := hker _ (by rw [map_sub, h, sub_self])
  have key : ∀ y ∈ I • (⊤ : Submodule R O), y • x = 0 := by
    intro y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro c hc o _
      rw [smul_assoc, hP c hc]
    · intro y z hy hz
      rw [add_smul, hy, hz, zero_add]
  have := key _ hb
  rwa [sub_smul, sub_eq_zero] at this

def units (hker : ∀ b, φ b = 0 → b ∈ I • (⊤ : Submodule R O)) (hP : ∀ c ∈ I, ∀ x : P, c • x = 0)
    (E : Fin m → Fin m → O) (hE : ∀ i j, φ (E i j) = Matrix.single i j 1) : MatrixUnits R P (Fin m) where
  E i j := Algebra.lsmul R R P (E i j)
  mul_eq i j k l := by
    by_cases h : j = k
    · subst h
      rw [if_pos rfl, ← map_mul]
      refine LinearMap.ext fun x => ?_
      show (E i j * E j l) • x = E i l • x
      exact act_congr hker hP (by rw [map_mul, hE, hE, hE, Matrix.single_mul_single_same, mul_one]) x
    · rw [if_neg h, ← map_mul]
      refine LinearMap.ext fun x => ?_
      show (E i j * E k l) • x = 0
      have := act_congr hker hP (b := E i j * E k l) (b' := 0)
        (by rw [map_mul, hE, hE, Matrix.single_mul_single_of_ne (h := h), map_zero]) x
      rwa [zero_smul] at this
  sum_diag := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.sum_apply]
    show ∑ i, E i i • x = x
    rw [← Finset.sum_smul]
    have := act_congr hker hP (b := ∑ i, E i i) (b' := 1)
      (by rw [map_sum, map_one]; simp only [hE]; exact Matrix.sum_single_one) x
    rwa [one_smul] at this

theorem units_E (hker : ∀ b, φ b = 0 → b ∈ I • (⊤ : Submodule R O)) (hP : ∀ c ∈ I, ∀ x : P, c • x = 0)
    (E : Fin m → Fin m → O) (hE : ∀ i j, φ (E i j) = Matrix.single i j 1) (i j : Fin m) (x : P) :
    (units hker hP E hE).E i j x = E i j • x := rfl

end

end GlobalTheory.MoritaLocal

namespace GlobalTheory.MoritaLocal

open GlobalTheory.Morita

theorem morita_local : ∀ (R : Type) [CommRing R] (I : Ideal R), IsLocalRing (R ⧸ I) → ∀ (m k : ℕ), 0 < m →
    ∀ (O : Type) [Ring O] [Algebra R O] (φ : O →ₐ[R] Matrix (Fin m) (Fin m) (R ⧸ I)), Function.Surjective φ →
    (∀ b, φ b = 0 → b ∈ I • (⊤ : Submodule R O)) →
    ∀ (M N : Type) [AddCommGroup M] [Module O M] [Module R M] [IsScalarTower R O M]
      [AddCommGroup N] [Module O N] [Module R N] [IsScalarTower R O N],
    (M ≃ₗ[R] (Fin (m * k) → R ⧸ I)) → (N ≃ₗ[R] (Fin (m * k) → R ⧸ I)) → Nonempty (M ≃ₗ[O] N) := by
  intro R _ I hI m k hm O _ _ φ hφ hker M N _ _ _ _ _ _ _ _ eM eN
  have hM : ∀ c ∈ I, ∀ x : M, c • x = 0 := fun c hc x => smul_eq_zero_of_equiv I eM hc x
  have hN : ∀ c ∈ I, ∀ x : N, c • x = 0 := fun c hc x => smul_eq_zero_of_equiv I eN hc x
  choose E hE using fun i j : Fin m => hφ (Matrix.single i j (1 : R ⧸ I))
  let UM := units hker hM E hE
  let UN := units hker hN E hE
  let a : Fin m := ⟨0, hm⟩
  obtain ⟨gM⟩ := corner_equiv I hI hm (UM.corner a) ((UM.toPi a).symm.trans eM)
  obtain ⟨gN⟩ := corner_equiv I hI hm (UN.corner a) ((UN.toPi a).symm.trans eN)
  let g := gM.trans gN.symm
  let Φ : M ≃ₗ[R] N := (UM.toPi a).trans ((LinearEquiv.piCongrRight fun _ => g).trans (UN.toPi a).symm)
  have hΦ : ∀ y, UN.toPi a (Φ y) = fun l => g (UM.toPi a y l) := by
    intro y
    simp only [Φ, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rfl
  have hΦE : ∀ i j (x : M), Φ (E i j • x) = E i j • Φ x := by
    intro i j x
    apply (UN.toPi a).injective
    have h1 := UM.toPi_E a i j x
    have h2 := UN.toPi_E a i j (Φ x)
    rw [units_E] at h1 h2
    rw [h2, hΦ, hΦ, h1]
    funext l
    by_cases hl : l = i
    · subst hl; simp
    · simp [Pi.single_apply, hl]
  have hΦO : ∀ (o : O) (x : M), Φ (o • x) = o • Φ x := by
    intro o x
    choose r hr using fun i j => Ideal.Quotient.mk_surjective (I := I) (φ o i j)
    have hφo : φ (∑ i, ∑ j, r i j • E i j) = φ o := by

      rw [map_sum]

      simp only [map_sum, map_smul, hE]
      refine (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_).trans
        (Matrix.matrix_eq_sum_single (φ o)).symm
      rw [Matrix.smul_single, ← hr i j, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
    rw [act_congr hker hM hφo.symm x, act_congr hker hN hφo.symm (Φ x)]

    simp only [Finset.sum_smul, smul_assoc, map_sum, map_smul, hΦE]
  exact ⟨{ Φ with map_smul' := fun o x => hΦO o x }⟩

end GlobalTheory.MoritaLocal
end

section

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.MatCount

open Matrix Module

variable {k : Type} [Field k] {n : ℕ}

section
variable {X : Type} [AddCommGroup X] [Module k X]
  (ρ : Matrix (Fin (n+1)) (Fin (n+1)) k →ₐ[k] Module.End k X)

theorem unit_mul (i j l p : Fin (n+1)) (x : X) :
    ρ (single i j 1) (ρ (single l p 1) x) = if j = l then ρ (single i p 1) x else 0 := by
  rw [← Module.End.mul_apply, ← map_mul]
  split_ifs with h
  · subst h; rw [single_mul_single_same, mul_one]
  · rw [single_mul_single_of_ne (h := h), map_zero, LinearMap.zero_apply]

theorem recon (x : X) : ∑ i, ρ (single i 0 1) (ρ (single 0 i 1) x) = x := by
  simp only [unit_mul, if_true]

  rw [← LinearMap.sum_apply, ← map_sum, sum_single_one, map_one, Module.End.one_apply]

abbrev corner : Submodule k X := LinearMap.range (ρ (single 0 0 1))

theorem unit_mem_corner (i : Fin (n+1)) (x : X) : ρ (single 0 i 1) x ∈ corner ρ :=
  ⟨ρ (single 0 i 1) x, by rw [unit_mul]; simp⟩

theorem unit_corner (v : corner ρ) (i : Fin (n+1)) :
    ρ (single 0 i 1) (v : X) = if i = 0 then (v : X) else 0 := by
  obtain ⟨y, hy⟩ := v.2
  rw [← hy, unit_mul]

def cut (i : Fin (n+1)) : X →ₗ[k] corner ρ :=
  (ρ (single 0 i 1)).codRestrict (corner ρ) (unit_mem_corner ρ i)

@[simp] theorem cut_coe (i : Fin (n+1)) (x : X) : ((cut ρ i x : corner ρ) : X) = ρ (single 0 i 1) x := rfl

theorem cut_unit (i l p : Fin (n+1)) (x : X) :
    cut ρ i (ρ (single l p 1) x) = if i = l then cut ρ p x else 0 := by
  apply Subtype.ext
  rw [cut_coe, unit_mul]
  split_ifs <;> simp

theorem cut_corner (i : Fin (n+1)) (v : corner ρ) : cut ρ i v = if i = 0 then v else 0 := by
  apply Subtype.ext
  rw [cut_coe, unit_corner]
  split_ifs <;> simp

def piEquiv : X ≃ₗ[k] (Fin (n+1) → corner ρ) :=
  LinearEquiv.ofLinear (LinearMap.pi fun i => cut ρ i)
    (∑ i, ρ (single i 0 1) ∘ₗ (corner ρ).subtype ∘ₗ LinearMap.proj i)
    (by
      refine LinearMap.ext fun v => funext fun j => ?_

      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, map_sum,
      Submodule.subtype_apply, LinearMap.proj_apply, cut_unit, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, cut_corner, LinearMap.id_apply])
    (by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply,
        cut_coe, Submodule.subtype_apply, LinearMap.proj_apply, LinearMap.id_apply]
      exact recon ρ x)

theorem finrank_eq [FiniteDimensional k X] : finrank k X = (n+1) * finrank k (corner ρ) := by
  rw [(piEquiv ρ).finrank_eq, Module.finrank_pi_fintype]
  simp
end

section
variable {X Y : Type} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
  (ρX : Matrix (Fin (n+1)) (Fin (n+1)) k →ₐ[k] Module.End k X)
  (ρY : Matrix (Fin (n+1)) (Fin (n+1)) k →ₐ[k] Module.End k Y)

theorem comm {T : X →ₗ[k] Y} (hT : T ∈ GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) (a : Matrix (Fin (n+1)) (Fin (n+1)) k)
    (x : X) : T (ρX a x) = ρY a (T x) :=
  (GlobalTheory.HTRho.mem_homO _ _ T).1 hT a x

theorem maps_corner (T : GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) :
    ∀ x ∈ corner ρX, (T : X →ₗ[k] Y) x ∈ corner ρY := by
  rintro _ ⟨y, rfl⟩
  exact ⟨(T : X →ₗ[k] Y) y, (comm ρX ρY T.2 _ y).symm⟩

def restr : GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom →ₗ[k] (corner ρX →ₗ[k] corner ρY) where
  toFun T := (T : X →ₗ[k] Y).restrict (maps_corner ρX ρY T)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restr_coe (T : GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) (v : corner ρX) :
    ((restr ρX ρY T v : corner ρY) : Y) = (T : X →ₗ[k] Y) v := rfl

def ext (S : corner ρX →ₗ[k] corner ρY) : X →ₗ[k] Y :=
  ∑ i, ρY (single i 0 1) ∘ₗ (corner ρY).subtype ∘ₗ S ∘ₗ cut ρX i

theorem ext_apply (S : corner ρX →ₗ[k] corner ρY) (x : X) :
    ext ρX ρY S x = ∑ i, ρY (single i 0 1) (S (cut ρX i x)) := by
  simp [ext, LinearMap.sum_apply]

theorem ext_unit (S : corner ρX →ₗ[k] corner ρY) (l p : Fin (n+1)) (x : X) :
    ext ρX ρY S (ρX (single l p 1) x) = ρY (single l p 1) (ext ρX ρY S x) := by

  rw [ext_apply, ext_apply, map_sum]
  simp only [cut_unit, unit_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single l (fun b _ hb => by rw [if_neg hb, map_zero, Submodule.coe_zero, map_zero])
    (by simp)]
  simp

theorem ext_mem (S : corner ρX →ₗ[k] corner ρY) :
    ext ρX ρY S ∈ GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom := by
  rw [GlobalTheory.HTRho.mem_homO]
  intro a x
  change ext ρX ρY S (ρX a x) = ρY a (ext ρX ρY S x)
  have ha : a = ∑ l, ∑ p, a l p • single l p (1 : k) := by
    conv_lhs => rw [matrix_eq_sum_single a]
    simp only [smul_single, smul_eq_mul, mul_one]
  rw [ha]

  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, ext_unit]

theorem restr_bij : Function.Bijective (restr ρX ρY) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun T hT => ?_
    apply Subtype.ext
    refine LinearMap.ext fun x => ?_
    have h0 : ∀ i, (T : X →ₗ[k] Y) (ρX (single 0 i 1) x) = 0 := fun i => by
      exact (congrArg Subtype.val (LinearMap.congr_fun hT ⟨_, unit_mem_corner ρX i x⟩) :)
    change (T : X →ₗ[k] Y) x = 0

    rw [← recon ρX x, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [comm ρX ρY T.2, h0, map_zero]
  · intro S
    refine ⟨⟨ext ρX ρY S, ext_mem ρX ρY S⟩, LinearMap.ext fun v => Subtype.ext ?_⟩
    rw [restr_coe]
    change ext ρX ρY S v = _
    rw [ext_apply]
    simp only [cut_corner]
    rw [Finset.sum_eq_single 0 (fun b _ hb => by rw [if_neg hb, map_zero, Submodule.coe_zero, map_zero])
      (by simp)]
    simp [unit_corner]

theorem finrank_homO [FiniteDimensional k X] [FiniteDimensional k Y] :
    finrank k (GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) = finrank k (corner ρX) * finrank k (corner ρY) := by
  rw [(LinearEquiv.ofBijective _ (restr_bij ρX ρY)).finrank_eq, Module.finrank_linearMap]
end

theorem count : ∀ (k : Type) [Field k] (m : ℕ) (X Y : Type) [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (ρX : Matrix (Fin m) (Fin m) k →ₐ[k] Module.End k X) (ρY : Matrix (Fin m) (Fin m) k →ₐ[k] Module.End k Y),
    m ^ 2 * Module.finrank k (GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) = Module.finrank k X * Module.finrank k Y := by
  intro k _ m X Y _ _ _ _ _ _ ρX ρY
  cases m with
  | zero =>
    have hX : Subsingleton X := by
      refine ⟨fun a b => ?_⟩
      have h : (1 : Module.End k X) = 0 := by
        rw [← map_one ρX, ← map_zero ρX]
        congr 1
        ext i
        exact i.elim0
      have ha := congrArg (fun f : Module.End k X => f a) h
      have hb := congrArg (fun f : Module.End k X => f b) h
      simp only [Module.End.one_apply, LinearMap.zero_apply] at ha hb
      rw [ha, hb]
    simp [finrank_zero_of_subsingleton]
  | succ n =>
    rw [finrank_homO, finrank_eq ρX, finrank_eq ρY]
    ring

end GlobalTheory.MatCount
end
end

section

open scoped TensorProduct
universe u

namespace GlobalTheory.HTRho

theorem mSub_top_eq_ker_smul :
    ∀ (k : Type) [Field k] (C : Type) [CommRing C] (H : Type u) [AddCommGroup H]
      [Module k H] (σ : C →+* Module.End k H) (χ : C →+* k),
      letI : Module (k ⊗[ℤ] C) H := Module.compHom H
        (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom
          (fun _ _ => Algebra.commutes _ _)).toRingHom
      ∀ x : H, x ∈ GlobalTheory.HTRho.mSub σ χ ⊤ ↔
        x ∈ (RingHom.ker (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom
          (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) • ⊤ : Submodule (k ⊗[ℤ] C) H) := by
  intro k _ C _ H _ _ σ χ x
  let : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H))
      σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom
  let L := Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom
    (fun _ _ => Algebra.commutes _ _)
  set φ : k ⊗[ℤ] C →ₐ[k] k := Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom
    (fun _ _ => Commute.all _ _) with hφdef
  have hsmul : ∀ (a : k ⊗[ℤ] C) (y : H), a • y = L a y := fun _ _ => rfl
  have hLt : ∀ (l : k) (c : C) (y : H), L (l ⊗ₜ c) y = l • σ c y := by
    intro l c y
    exact congrArg (fun f : Module.End k H => f y)
      (Algebra.TensorProduct.lift_tmul (Algebra.ofId k (Module.End k H))
        σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _) l c)
  have hφt : ∀ (l : k) (c : C), φ (l ⊗ₜ c) = l * χ c := by
    intro l c
    simp [hφdef, Algebra.TensorProduct.lift_tmul]
  have key : ∀ (a : k ⊗[ℤ] C) (y : H), L a y - φ a • y ∈ mSub σ χ ⊤ := by
    intro a y
    induction a using TensorProduct.inductionOn with
    | tmul l c =>
      rw [hLt, hφt, mul_smul, ← smul_sub]
      refine Submodule.smul_mem _ l (Submodule.subset_span ⟨c, y, trivial, ?_⟩)
      simp
    | add a b ha hb =>
      rw [map_add L, map_add φ, LinearMap.add_apply, add_smul, add_sub_add_comm]
      exact add_mem ha hb
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, y, -, rfl⟩ := hz
      have hmem : ((1 : k) ⊗ₜ c - (χ c) ⊗ₜ (1 : C)) ∈ RingHom.ker φ := by
        rw [RingHom.mem_ker]
        simp [hφt]
      have := Submodule.smul_mem_smul hmem (Submodule.mem_top (x := y))
      convert this using 1
      rw [hsmul, map_sub, LinearMap.sub_apply, hLt, hLt]
      simp
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul l z _ hz =>
      have : l • z = ((l ⊗ₜ (1 : C) : k ⊗[ℤ] C)) • z := by
        rw [hsmul, hLt]; simp
      rw [this]
      exact Submodule.smul_mem _ _ hz
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun a b ha hb => add_mem ha hb)
    rw [hsmul]
    have := key a y
    rwa [(RingHom.mem_ker).1 ha, zero_smul, sub_zero] at this

end GlobalTheory.HTRho
end

section

open GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isExcisionNbhd_trans :
    ∀ (A A' A'' : Type) [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A'] [Algebra A' A''] [Algebra A A'']
      [IsScalarTower A A' A''] (h : A), IsExcisionNbhd A A' h → IsExcisionNbhd A' A'' (algebraMap A A' h) →
        IsExcisionNbhd A A'' h := by
  intro A A' A'' _ _ _ _ _ _ _ h h1 h2
  obtain ⟨e1, s1, i1⟩ := h1
  obtain ⟨e2, s2, i2⟩ := h2
  have hsc : ∀ x : A, algebraMap A A'' x = algebraMap A' A'' (algebraMap A A' x) :=
    fun x => IsScalarTower.algebraMap_apply A A' A'' x
  refine ⟨Algebra.Etale.comp A A' A'', ?_, ?_⟩
  · intro a''
    obtain ⟨a', ha'⟩ := s2 a''
    obtain ⟨a, ha⟩ := s1 a'
    refine ⟨a, ?_⟩
    rw [Ideal.mem_span_singleton] at ha ha' ⊢
    obtain ⟨c, hc⟩ := ha
    have key : a'' - algebraMap A A'' a = (a'' - algebraMap A' A'' a') +
        algebraMap A' A'' (algebraMap A A' h) * algebraMap A' A'' c := by
      rw [← map_mul, ← hc, map_sub, hsc]
      ring
    rw [key, hsc]
    exact dvd_add ha' (dvd_mul_right _ _)
  · intro a ha
    rw [hsc, hsc] at ha
    exact i1 a (i2 _ ha)

end GlobalTheory.EtC
end
