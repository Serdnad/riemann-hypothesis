module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.DualNumber
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
public import Mathlib.RingTheory.Noetherian.Nilpotent
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.GroupTheory.Coset.Card
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Separable

@[expose] public section

section

open CategoryTheory Limits

namespace GlobalTheory

theorem natCard_eq_coker_mul_ker_of_exact {R : Type} [Ring R] {A A' B D D' : Type}
    [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup D] [AddCommGroup D']
    [Module R A] [Module R A'] [Module R B] [Module R D] [Module R D']
    (f : A →ₗ[R] A') (g : A' →ₗ[R] B) (d : B →ₗ[R] D) (h : D →ₗ[R] D')
    (e₁ : LinearMap.range f = LinearMap.ker g) (e₂ : LinearMap.range g = LinearMap.ker d)
    (e₃ : LinearMap.range d = LinearMap.ker h) :
    Nat.card B = Nat.card (A' ⧸ LinearMap.range f) * Nat.card (LinearMap.ker h) := by
  have h1 : Nat.card B = Nat.card (B ⧸ LinearMap.ker d) * Nat.card (LinearMap.ker d) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker d).toAddSubgroup
  rw [h1, Nat.card_congr d.quotKerEquivRange.toEquiv, e₃, e₁,
    Nat.card_congr g.quotKerEquivRange.toEquiv, e₂, mul_comm]

theorem natCard_homology_of_shortExact_mul : ∀ (p : ℕ) (C G : CochainComplex (ModuleCat.{0} ℤ) ℕ) (π : C ⟶ G) (hz : ((p : ℤ) • 𝟙 C) ≫ π = 0), (ShortComplex.mk ((p : ℤ) • 𝟙 C) π hz).ShortExact → ∀ n : ℕ, Nat.card (G.homology n) = Nat.card ((C.homology n) ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : C.homology n →ₗ[ℤ] C.homology n))) * Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : C.homology (n + 1) →ₗ[ℤ] C.homology (n + 1)))) := by
  intro p C G π hz hS n
  have hmul0 : ∀ k, HomologicalComplex.homologyMap ((p : ℤ) • 𝟙 C) k = (p : ℤ) • 𝟙 _ := by
    intro k
    have := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) k).map_zsmul
      (f := 𝟙 C) (r := (p : ℤ))
    rw [CategoryTheory.Functor.map_id] at this
    exact this
  have hmul : ∀ k, (HomologicalComplex.homologyMap ((p : ℤ) • 𝟙 C) k).hom
      = (p : ℤ) • (LinearMap.id : C.homology k →ₗ[ℤ] C.homology k) := by
    intro k
    rw [hmul0]
    ext x
    simp
  have e2 := (hS.homology_exact₂ n).moduleCat_range_eq_ker
  have e3 := (hS.homology_exact₃ n (n+1) rfl).moduleCat_range_eq_ker
  have e1 := (hS.homology_exact₁ n (n+1) rfl).moduleCat_range_eq_ker
  dsimp only at e1 e2 e3
  rw [hmul] at e1 e2
  exact natCard_eq_coker_mul_ker_of_exact _ _ _ _ e2 e3 e1

end GlobalTheory
end

section

open CategoryTheory Limits

noncomputable section

namespace GlobalTheory

abbrev pMultiples (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] : Submodule ℤ M :=
  LinearMap.range ((p : ℤ) • LinearMap.id : M →ₗ[ℤ] M)

lemma zmultiples_mkQ_p (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] :
    zmultiplesHom (M →+ M ⧸ pMultiples p M) (pMultiples p M).mkQ.toAddMonoidHom (p : ℤ) = 0 := by
  ext m
  simp only [zmultiplesHom_apply, AddMonoidHom.coe_smul, Pi.smul_apply, AddMonoidHom.zero_apply]
  show (p : ℤ) • Submodule.Quotient.mk m = (0 : M ⧸ pMultiples p M)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact ⟨m, by simp⟩

def modPPairing (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] :
    ZMod p →+ M →+ (M ⧸ pMultiples p M) :=
  ZMod.lift p ⟨zmultiplesHom _ (pMultiples p M).mkQ.toAddMonoidHom, zmultiples_mkQ_p p M⟩

lemma modPPairing_one (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] (m : M) :
    modPPairing p M 1 m = Submodule.Quotient.mk m := by
  have h := ZMod.lift_coe p (A := M →+ (M ⧸ pMultiples p M))
    ⟨zmultiplesHom _ (pMultiples p M).mkQ.toAddMonoidHom, zmultiples_mkQ_p p M⟩ 1
  simp only [Int.cast_one] at h
  unfold modPPairing
  rw [h]
  simp

abbrev zmodOverInt (p : ℕ) : ModuleCat.{0} ℤ :=
  (ModuleCat.restrictScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of (ZMod p) (ZMod p))

def tensorToModP (p : ℕ) (M : ModuleCat.{0} ℤ) :
    TensorProduct ℤ (zmodOverInt p) M →+ (M ⧸ pMultiples p M) :=
  TensorProduct.liftAddHom (modPPairing p M) (fun r a m => by
    have key : ∀ b : ZMod p, modPPairing p M ((r : ZMod p) * b) m = r • modPPairing p M b m := by
      intro b
      rw [← zsmul_eq_mul, map_zsmul]
      rfl
    refine (key a).trans ?_
    rw [← map_zsmul]
    congr 1
    exact (int_smul_eq_zsmul _ r m).symm)

lemma tensorToModP_unit (p : ℕ) (M : ModuleCat.{0} ℤ) (m : M) :
    tensorToModP p M
      (((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom m) =
      Submodule.Quotient.mk m := by
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  unfold tensorToModP
  exact (TensorProduct.liftAddHom_tmul _ _ _ _).trans (modPPairing_one p M m)

end GlobalTheory

end

noncomputable section

namespace GlobalTheory

def oneZ (p : ℕ) : zmodOverInt p := (1 : ZMod p)

lemma oneZ_tmul_surjective (p : ℕ) (M : ModuleCat.{0} ℤ) :
    ∀ t : TensorProduct ℤ (zmodOverInt p) M, ∃ m : M, oneZ p ⊗ₜ[ℤ] m = t := by
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul a m =>
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective (n := p) a
    have h1 := map_zsmul (AddMonoidHom.mk' (fun x : M => oneZ p ⊗ₜ[ℤ] x) (TensorProduct.tmul_add _)) k m
    have h2 := map_zsmul (AddMonoidHom.mk' (fun b : zmodOverInt p => b ⊗ₜ[ℤ] m)
      (fun b c => TensorProduct.add_tmul b c m)) k (oneZ p)
    refine ⟨_, (h1.trans h2.symm).trans (congrArg (fun x => x ⊗ₜ[ℤ] m) ?_)⟩
    show (k • (1 : ZMod p) : ZMod p) = a
    rw [zsmul_one]
    exact hk
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, (TensorProduct.tmul_add _ u v).trans (by rw [hu, hv])⟩

lemma unit_surjective_zmod (p : ℕ) (M : ModuleCat.{0} ℤ) :
    Function.Surjective ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom := by
  intro t
  obtain ⟨m, hm⟩ := oneZ_tmul_surjective p M t
  exact ⟨m, (ModuleCat.extendRestrictScalarsAdj_unit_app_apply _ _ _).trans hm⟩

lemma unit_kernel_zmod (p : ℕ) (M : ModuleCat.{0} ℤ) (y : M)
    (hy : ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom y = 0) :
    ∃ x : M, ((p : ℤ) • LinearMap.id : M →ₗ[ℤ] M) x = y := by
  have h := tensorToModP_unit p M y
  rw [hy] at h
  exact (Submodule.Quotient.mk_eq_zero _).mp (h.symm.trans (map_zero (tensorToModP p M)))

lemma oneZ_tmul_p (p : ℕ) (M : ModuleCat.{0} ℤ) (x : M) :
    oneZ p ⊗ₜ[ℤ] ((p : ℤ) • x) = 0 := by
  have h1 := map_zsmul (AddMonoidHom.mk' (fun y : M => oneZ p ⊗ₜ[ℤ] y) (TensorProduct.tmul_add _)) (p : ℤ) x
  have h2 := map_zsmul (AddMonoidHom.mk' (fun b : zmodOverInt p => b ⊗ₜ[ℤ] x)
      (fun b c => TensorProduct.add_tmul b c x)) (p : ℤ) (oneZ p)
  refine (h1.trans h2.symm).trans ((congrArg (fun b => b ⊗ₜ[ℤ] x) ?_).trans (TensorProduct.zero_tmul _ _))
  show ((p : ℤ) • (1 : ZMod p) : ZMod p) = 0
  simp

lemma unit_pmul_zmod (p : ℕ) (M : ModuleCat.{0} ℤ) (x : M) :
    ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom
      (((p : ℤ) • LinearMap.id : M →ₗ[ℤ] M) x) = 0 :=
  (ModuleCat.extendRestrictScalarsAdj_unit_app_apply _ _ _).trans (oneZ_tmul_p p M x)

lemma pmul_injective (p : ℕ) (M : ModuleCat.{0} ℤ) (h : ∀ x : M, (p : ℤ) • x = 0 → x = 0) :
    Function.Injective (ConcreteCategory.hom ((p : ℤ) • 𝟙 M)) := by
  intro a b hab
  have hab' : (p : ℤ) • a = (p : ℤ) • b := hab
  apply sub_eq_zero.mp
  apply h
  rw [zsmul_sub, hab', sub_self]

theorem shortExact_mul_p_modP :
    ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime],
      (∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0) →
      ∃ (π : C ⟶ ((ModuleCat.restrictScalars.{0} (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj C)) (hz : ((p : ℤ) • 𝟙 C) ≫ π = 0),
        (ShortComplex.mk ((p : ℤ) • 𝟙 C) π hz).ShortExact := by
  intro C p _ hinj
  let π : C ⟶ ((ModuleCat.restrictScalars.{0} (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj C) :=
    { f := fun n => (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app (C.X n)
      comm' := fun i j _ =>
        ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.naturality (C.d i j)) }
  have hz : ((p : ℤ) • 𝟙 C) ≫ π = 0 := by
    ext n x
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f,
      ModuleCat.hom_comp, ModuleCat.hom_zsmul, ModuleCat.hom_id, LinearMap.comp_apply,
      HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact unit_pmul_zmod p (C.X n) x
  refine ⟨π, hz, ?_⟩
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  apply ShortComplex.ShortExact.mk'
  · rw [ShortComplex.moduleCat_exact_iff]
    intro y hy
    simp only [ShortComplex.map_f, ShortComplex.map_g, HomologicalComplex.eval_map,
      HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f, ModuleCat.hom_zsmul,
      ModuleCat.hom_id] at hy ⊢
    exact unit_kernel_zmod p (C.X n) y hy
  · rw [ModuleCat.mono_iff_injective]
    exact pmul_injective p (C.X n) (hinj n)
  · rw [ModuleCat.epi_iff_surjective]
    exact unit_surjective_zmod p (C.X n)

end GlobalTheory

end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory

theorem pullbackCone_ker_fst_inf_ker_snd {A B C : CommRingCat.{0}} (f : A ⟶ C) (g : B ⟶ C) :
    RingHom.ker (CommRingCat.pullbackCone f g).fst.hom ⊓
      RingHom.ker (CommRingCat.pullbackCone f g).snd.hom = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_inf, RingHom.mem_ker, RingHom.mem_ker] at hx
  rw [Ideal.mem_bot]
  exact Subtype.ext (Prod.ext hx.1 hx.2)

theorem pow_le_ker_of_le_comap {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (I : Ideal R) (J : Ideal S) (k : ℕ) (hIJ : I ≤ Ideal.comap φ J) (hJ : J ^ k = 0) :
    I ^ k ≤ RingHom.ker φ :=
  calc I ^ k ≤ (Ideal.comap φ J) ^ k := Ideal.pow_right_mono hIJ k
    _ ≤ Ideal.comap φ (J ^ k) := Ideal.le_comap_pow φ k
    _ = RingHom.ker φ := by rw [hJ, Ideal.zero_eq_bot, ← RingHom.ker_eq_comap_bot]

theorem pullbackCone_fst_snd_ring_nilpotent {A B C : CommRingCat.{0}} (f : A ⟶ C) (g : B ⟶ C) :
    Function.Surjective f.hom → IsNilpotent (RingHom.ker f.hom) → Function.Surjective g.hom →
    IsNilpotent (RingHom.ker g.hom) →
    (Function.Surjective (CommRingCat.pullbackCone f g).fst.hom ∧
        IsNilpotent (RingHom.ker (CommRingCat.pullbackCone f g).fst.hom)) ∧
      (Function.Surjective (CommRingCat.pullbackCone f g).snd.hom ∧
        IsNilpotent (RingHom.ker (CommRingCat.pullbackCone f g).snd.hom)) ∧
      (Function.Surjective ((CommRingCat.pullbackCone f g).fst ≫ f).hom ∧
        IsNilpotent (RingHom.ker ((CommRingCat.pullbackCone f g).fst ≫ f).hom)) := by
  rintro hf ⟨n, hn⟩ hg ⟨m, hm⟩
  have hbot := pullbackCone_ker_fst_inf_ker_snd f g
  have hcomm : ∀ x : (CommRingCat.pullbackCone f g).pt,
      f.hom ((CommRingCat.pullbackCone f g).fst.hom x) =
        g.hom ((CommRingCat.pullbackCone f g).snd.hom x) := fun x => x.2
  have k1 : RingHom.ker (CommRingCat.pullbackCone f g).fst.hom ≤
      Ideal.comap (CommRingCat.pullbackCone f g).snd.hom (RingHom.ker g.hom) := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hcomm, hx, map_zero]
  have k2 : RingHom.ker (CommRingCat.pullbackCone f g).snd.hom ≤
      Ideal.comap (CommRingCat.pullbackCone f g).fst.hom (RingHom.ker f.hom) := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_comap, RingHom.mem_ker, hcomm, hx, map_zero]
  have k3 : RingHom.ker ((CommRingCat.pullbackCone f g).fst ≫ f).hom ≤
      Ideal.comap (CommRingCat.pullbackCone f g).fst.hom (RingHom.ker f.hom) := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simpa using hx
  have k4 : RingHom.ker ((CommRingCat.pullbackCone f g).fst ≫ f).hom ≤
      Ideal.comap (CommRingCat.pullbackCone f g).snd.hom (RingHom.ker g.hom) := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hcomm]
    simpa using hx
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro a
    obtain ⟨b, hb⟩ := hg (f.hom a)
    exact ⟨⟨(a, b), hb.symm⟩, rfl⟩
  · refine ⟨m + 1, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← hbot, pow_succ]
    exact (Ideal.mul_le_inf).trans
      (le_inf inf_le_right ((inf_le_left).trans (pow_le_ker_of_le_comap _ _ _ m k1 hm)))
  · intro b
    obtain ⟨a, ha⟩ := hf (g.hom b)
    exact ⟨⟨(a, b), ha⟩, rfl⟩
  · refine ⟨n + 1, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← hbot, pow_succ]
    exact (Ideal.mul_le_inf).trans
      (le_inf ((inf_le_left).trans (pow_le_ker_of_le_comap _ _ _ n k2 hn)) inf_le_right)
  · intro c
    obtain ⟨a, ha⟩ := hf c
    obtain ⟨b, hb⟩ := hg c
    exact ⟨⟨(a, b), ha.trans hb.symm⟩, ha⟩
  · refine ⟨n + m, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← hbot, pow_add]
    exact (Ideal.mul_le_inf).trans
      (le_inf ((inf_le_left).trans (pow_le_ker_of_le_comap _ _ _ n k3 hn))
        ((inf_le_right).trans (pow_le_ker_of_le_comap _ _ _ m k4 hm)))

end GlobalTheory
end

section

namespace GlobalTheory

open Matrix

theorem frobSemilinear_iterate_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι S) (N : ℕ), (∀ j i, IsNilpotent ((fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[N] (Pi.single j 1) i)) → ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[K] z = 0 := by
  intro p _ S _ _ ι _ _ Q N hN
  set L : (ι → S) → (ι → S) := fun w => Q.mulVec fun k => frobenius S p (w k) with hL
  let F : AddMonoid.End (ι → S) :=
    { toFun := L
      map_zero' := by
        simp only [L, Pi.zero_apply, map_zero]
        exact Matrix.mulVec_zero Q
      map_add' := by
        intro x y
        simp only [L, Pi.add_apply, map_add (f := _)]
        exact Matrix.mulVec_add Q _ _ }
  have hF : ∀ n, ⇑(F ^ n) = L^[n] := fun n => AddMonoid.End.coe_pow (M := ι → S) F n
  have hsmul : ∀ (a : S) (w : ι → S), L (a • w) = a ^ p • L w := by
    intro a w
    simp only [L]
    rw [← Matrix.mulVec_smul]
    congr 1
    ext k
    simp [frobenius_def, mul_pow]
  have hsmulN : ∀ n (a : S) (w : ι → S), L^[n] (a • w) = a ^ (p ^ n) • L^[n] w := by
    intro n
    induction n with
    | zero => intro a w; simp
    | succ n ih =>
      intro a w
      rw [Function.iterate_succ_apply, hsmul, ih, ← pow_mul, ← pow_succ', Function.iterate_succ_apply]
  have hdecomp : ∀ w : ι → S, L^[N] w = ∑ j, (w j) ^ (p ^ N) • L^[N] (Pi.single j 1) := by
    intro w
    conv_lhs => rw [← Finset.univ_sum_single w]

    rw [← hF, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hF, ← hsmulN]
    congr 1
    ext i
    by_cases h : i = j
    · subst h; simp
    · simp [Pi.single_apply, h]
  let J : Ideal S := Ideal.span (Set.range fun ji : ι × ι => L^[N] (Pi.single ji.1 1) ji.2)
  have hJnil : IsNilpotent J := by
    refine (Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span (Set.finite_range _))).2 ?_
    rw [Ideal.span_le]
    rintro _ ⟨⟨j, i⟩, rfl⟩
    exact (mem_nilradical).2 (hN j i)
  have hstep : ∀ k (w : ι → S), (∀ i, w i ∈ J ^ k) → ∀ i, L^[N] w i ∈ J ^ (k + 1) := by
    intro k w hw i
    rw [hdecomp w, Finset.sum_apply]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, pow_succ]
    exact Ideal.mul_mem_mul
      (Ideal.pow_mem_of_mem _ (hw j) _ (pow_pos (Fact.out : p.Prime).pos _))
      (Ideal.subset_span ⟨(j, i), rfl⟩)
  have hall : ∀ k (z : ι → S), ∀ i, L^[N * k] z i ∈ J ^ k := by
    intro k
    induction k with
    | zero => intro z i; simp
    | succ k ih =>
      intro z i
      rw [show N * (k + 1) = N + N * k by ring, Function.iterate_add_apply]
      exact hstep k _ (ih z) i
  obtain ⟨m, hm⟩ := hJnil
  refine ⟨N * m, fun z => ?_⟩
  funext i
  have h := hall m z i
  rw [hm, Ideal.zero_eq_bot, Ideal.mem_bot] at h
  exact h

end GlobalTheory
end

section

namespace GlobalTheory

open Polynomial

theorem ringHom_dualNumber_snd_eq_zero (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F]
    {R : Type} [CommRing R] (φ : F →+* DualNumber R) (a : F) : (φ a).snd = 0 := by
  classical
  let ψ : F →+* R := (TrivSqZeroExt.fstHom R R R).toRingHom.comp φ
  have hψ : ∀ x, ψ x = (φ x).fst := fun x => rfl
  have hcomp : φ.comp (algebraMap ℚ F) =
      (TrivSqZeroExt.inlHom R R).comp (ψ.comp (algebraMap ℚ F)) := RingHom.ext_rat _ _
  have hint : IsIntegral ℚ a := Algebra.IsIntegral.isIntegral a
  have hsep : (minpoly ℚ a).Separable := (minpoly.irreducible hint).separable
  have hf0 : aeval a (minpoly ℚ a) = 0 := minpoly.aeval ℚ a
  have hd : aeval a (derivative (minpoly ℚ a)) ≠ 0 := hsep.aeval_derivative_ne_zero hf0
  have hu : IsUnit (ψ (aeval a (derivative (minpoly ℚ a)))) := (isUnit_iff_ne_zero.mpr hd).map ψ
  have hsplit : φ a = TrivSqZeroExt.inl (φ a).fst + TrivSqZeroExt.inr (φ a).snd :=
    (TrivSqZeroExt.inl_fst_add_inr_snd_eq _).symm
  have hsq : (TrivSqZeroExt.inr (φ a).snd : DualNumber R) ^ 2 = 0 := by
    rw [sq, TrivSqZeroExt.inr_mul_inr]
  have hev : ∀ p : ℚ[X], (p.map (φ.comp (algebraMap ℚ F))).eval (TrivSqZeroExt.inl (φ a).fst) =
      TrivSqZeroExt.inl (ψ (aeval a p)) := by
    intro p
    rw [hcomp, eval_map, aeval_def, ← hψ, Polynomial.hom_eval₂]
    change eval₂ _ (TrivSqZeroExt.inlHom R R (ψ a)) p = TrivSqZeroExt.inlHom R R _
    rw [Polynomial.hom_eval₂]
  have hlhs : ((minpoly ℚ a).map (φ.comp (algebraMap ℚ F))).eval (φ a) = 0 := by
    rw [eval_map, ← Polynomial.hom_eval₂, ← aeval_def, hf0, map_zero]
  have key := eval_add_of_sq_eq_zero ((minpoly ℚ a).map (φ.comp (algebraMap ℚ F)))
    (TrivSqZeroExt.inl (φ a).fst) (TrivSqZeroExt.inr (φ a).snd) hsq
  rw [← hsplit, hlhs, derivative_map, hev, hev, hf0, map_zero] at key
  have h2 := congrArg TrivSqZeroExt.snd key
  simp only [TrivSqZeroExt.snd_zero, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    DualNumber.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inr,
    mul_zero, zero_add, add_zero] at h2
  exact (hu.mul_right_eq_zero).mp h2.symm

end GlobalTheory
end
