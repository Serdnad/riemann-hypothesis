module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle883
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle914
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle449
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle999
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle937
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle849
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem one_tmul_injective_field (K L M : Type) [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] :
    Function.Injective (fun m : M ↦ (1 : L) ⊗ₜ[K] m) := by
  have h1 : Function.Injective ((Algebra.linearMap K L).rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap K L).injective
  have h2 : (fun m : M ↦ (1 : L) ⊗ₜ[K] m) = ((Algebra.linearMap K L).rTensor M) ∘ (TensorProduct.lid K M).symm := by
    funext m; simp
  rw [h2]; exact h1.comp (TensorProduct.lid K M).symm.injective

theorem pullHO_injective_field (K L : Type) [Field K] [Field L] [Algebra K L] (X X' : Scheme.{0}) (s : X ⟶ Sp K)
    (s' : X' ⟶ Sp L) (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap K L))) (hs : IsSeparated s)
    (hq : QuasiCompact s) :
    Function.Injective (pullHO1 h.w) ∧ Function.Injective (pullHO2 h.w) := by
  obtain ⟨⟨e1, he1⟩, ⟨e2, he2⟩⟩ := GlobalTheory.T.structure_cohomology_flat_base_change K L X X' s s' φ h hs hq
  refine ⟨fun a b hab ↦ ?_, fun a b hab ↦ ?_⟩
  · apply one_tmul_injective_field K L
    apply e1.injective
    simp only [he1, hab]
  · apply one_tmul_injective_field K L
    apply e2.injective
    simp only [he2, hab]

theorem noPrimO2_axesO1_descend : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → (NoPrimitiveStructureSheafH2 B → NoPrimitiveStructureSheafH2 A) ∧ (AxesVanishingStructureSheafDegOne B → AxesVanishingStructureSheafDegOne A) := by
  intro K L _ _ _ A _ B _ φ hφ hA
  have hpA : IsProper A.hom := hA.proper
  have hpAA : IsProper (A ⊗ A).hom := by rw [Over.tensorObj_hom]; infer_instance
  obtain ⟨Φ, hΦ, hμ, hf, hs, ha1, ha2⟩ := GlobalTheory.T.grpPullback_prod_self_isPullback K L (algebraMap K L) A B φ hφ
  have injA := pullHO_injective_field K L A.left B.left A.hom B.hom φ hφ.1 inferInstance inferInstance
  have injAA := pullHO_injective_field K L (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom Φ hΦ
    inferInstance inferInstance
  have N := pull_over_baseChange_comm K L (algebraMap K L)
  refine ⟨fun hB z hz ↦ ?_, fun hB y h1 h2 ↦ ?_⟩
  · apply injA.2
    rw [map_zero]
    apply hB
    have e := congrArg (pullHO2 hΦ.w) hz
    rw [map_add (f := _)] at e
    rw [← (N A (A ⊗ A) B (B ⊗ B) μ[A] μ[B] φ Φ hφ.1.w hΦ.w hμ).2,
      ← (N A (A ⊗ A) B (B ⊗ B) (fst A A) (fst B B) φ Φ hφ.1.w hΦ.w hf).2,
      ← (N A (A ⊗ A) B (B ⊗ B) (snd A A) (snd B B) φ Φ hφ.1.w hΦ.w hs).2]
    exact e
  · apply injAA.1
    rw [map_zero]
    apply hB
    · rw [← (N (A ⊗ A) A (B ⊗ B) B _ _ Φ φ hΦ.w hφ.1.w ha1).1, h1, map_zero]
    · rw [← (N (A ⊗ A) A (B ⊗ B) B _ _ Φ φ hΦ.w hφ.1.w ha2).1, h2, map_zero]

end GlobalTheory.AbCoh
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

namespace GlobalTheory.Dieu.Integrality

variable {p : ℕ} [Fact p.Prime] (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem map_id' (G : PDivGroup p k) : T.map (𝟙 G) = LinearMap.id :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G G G trivial trivial trivial).1

theorem map_comp' {G H K : PDivGroup p k} (f : G ⟶ H) (g : H ⟶ K) :
    T.map (f ≫ g) = T.map f ∘ₗ T.map g :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G H K trivial trivial trivial).2.1 f g

theorem map_pow_smul' {G H : PDivGroup p k} (n : ℕ) (f : G ⟶ H) (m : T.M H) :
    T.map ((p : ℤ_[p]) ^ n • f) m = p ^ n • T.map f m :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G H H trivial trivial trivial).2.2.2.2.1 n f m

theorem red_map' {G H : PDivGroup p k} (f : G ⟶ H) (m : T.M H) :
    T.red G (T.map f m) = rigExtMap f (T.red H m) :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G H H trivial trivial trivial).2.2.2.2.2.1 f m

theorem eq_zero_of_pow_smul' {G : PDivGroup p k} (n : ℕ) (m : T.M G) (h : p ^ n • m = 0) : m = 0 :=
  (GlobalTheory.T.dieudonneFunctorBase_functor_properties p _ T.base k G G G trivial trivial trivial).2.2.2.2.2.2.2.2 n m h

def DivP {G H : PDivGroup p k} (f : G ⟶ H) : Prop := ∀ m, ∃ m', T.map f m = p • m'

theorem divP_comp {G' G H H' : PDivGroup p k} (a : G' ⟶ G) (f : G ⟶ H) (b : H ⟶ H')
    (hf : DivP T f) : DivP T (a ≫ f ≫ b) := by
  intro m
  obtain ⟨m', hm'⟩ := hf (T.map b m)
  refine ⟨T.map a m', ?_⟩
  rw [map_comp', map_comp', LinearMap.comp_apply, LinearMap.comp_apply, hm', map_nsmul]

theorem divP_iff_red {G H : PDivGroup p k} (f : G ⟶ H) : DivP T f ↔ rigExtMap f = 0 := by
  constructor
  · intro hf
    refine LinearMap.ext fun x => ?_
    obtain ⟨m, rfl⟩ := T.base.red_surjective H trivial x
    obtain ⟨m', hm'⟩ := hf m
    have h := (T.base.red_eq_zero G trivial (T.map f m)).2 ⟨m', hm'⟩
    change rigExtMap f (T.red H m) = 0
    exact (red_map' T f m).symm.trans h
  · intro hf m
    have h : T.red G (T.map f m) = 0 := by
      have h' := congrArg (fun φ => φ (T.red H m)) hf
      exact (red_map' T f m).trans h'
    exact (T.base.red_eq_zero G trivial _).1 h

theorem exists_of_isConn {G H : PDivGroup p k} (hG : G.IsConn) (f : G ⟶ H) (hf : DivP T f) :
    ∃ g : G ⟶ H, f = (p : ℤ_[p]) • g := by
  have hq : IsIsog ((p : ℤ_[p]) ^ 1 • 𝟙 G) := ((GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).1 1).1
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_factor_through_isogeny_of_dieudonne_range_le p T k G G H _ f hG hq (by
    rintro x ⟨m, rfl⟩
    obtain ⟨m', hm'⟩ := hf m
    refine ⟨m', ?_⟩
    rw [hm', map_pow_smul', map_id', LinearMap.id_apply, pow_one])
  refine ⟨g, ?_⟩
  rw [← hg, Linear.smul_comp, Category.id_comp, pow_one]

theorem exists_of_isEt {G H : PDivGroup p k} (hG : G.IsEt) (hH : H.IsEt) (f : G ⟶ H)
    (hf : DivP T f) : ∃ g : G ⟶ H, f = (p : ℤ_[p]) • g := by
  have h1 : rigExtMap (dualHom G H f) = 0 :=
    GlobalTheory.T.rigidifiedExtensionPullback_dualHom_eq_zero_of_isEt p k G H f hG hH ((divP_iff_red T f).1 hf)
  obtain ⟨g', hg'⟩ := exists_of_isConn T (PDivGroup.dual_isConn_of_isEt p k H hH) _
    ((divP_iff_red T _).2 h1)
  obtain ⟨g, rfl⟩ := (dualHom_bijective (G := G) (H := H)).2 g'
  refine ⟨g, (dualHom_bijective (G := G) (H := H)).1 ?_⟩
  rw [hg', map_smul]

theorem exists_of_divP {G H : PDivGroup p k} (f : G ⟶ H) (hf : DivP T f) :
    ∃ g : G ⟶ H, f = (p : ℤ_[p]) • g := by
  obtain ⟨G₀, G₁, i₀, q₀, i₁, q₁, hG₀, hG₁, -, -, hG⟩ :=
    PDivGroup.exists_isConn_isEt_splitting p k G
  obtain ⟨H₀, H₁, j₀, r₀, j₁, r₁, hH₀, hH₁, -, -, hH⟩ :=
    PDivGroup.exists_isConn_isEt_splitting p k H
  obtain ⟨g₀, hg₀⟩ := exists_of_isConn T hG₀ (i₀ ≫ f) (by
    simpa using divP_comp T i₀ f (𝟙 H) hf)
  obtain ⟨g₁, hg₁⟩ := exists_of_isEt T hG₁ hH₁ (i₁ ≫ f ≫ r₁) (divP_comp T i₁ f r₁ hf)
  have h0 : i₁ ≫ f ≫ r₀ = 0 := (PDivGroup.hom_eq_zero_of_isConn_of_isEt p k H₀ G₁ hH₀ hG₁).2 _
  have e1 : i₁ ≫ f = (i₁ ≫ f ≫ r₀) ≫ j₀ + (i₁ ≫ f ≫ r₁) ≫ j₁ := by
    conv_lhs => rw [← Category.comp_id f, ← hH]
    simp only [Preadditive.comp_add, Category.assoc]
  refine ⟨q₀ ≫ g₀ + q₁ ≫ g₁ ≫ j₁, ?_⟩
  conv_lhs => rw [← Category.id_comp f, ← hG]
  rw [Preadditive.add_comp, Category.assoc, Category.assoc, hg₀, e1, h0, hg₁, Limits.zero_comp,
    zero_add, Linear.smul_comp, Linear.comp_smul, Linear.comp_smul, smul_add]

theorem exists_pow_smul_and_faithful : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (G H : PDivGroup p k) (f : G ⟶ H), (∀ n : ℕ, (∀ m, ∃ m', T.map f m = p ^ n • m') →
      ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ n • g) ∧ (T.map f = 0 → f = 0) := by
  intro p _ T k _ _ _ G H f
  have part1 : ∀ (n : ℕ) (f : G ⟶ H), (∀ m, ∃ m', T.map f m = p ^ n • m') →
      ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ n • g := by
    intro n
    induction n with
    | zero => intro f _; exact ⟨f, by rw [pow_zero, one_smul]⟩
    | succ n ih =>
      intro f hf
      obtain ⟨g, rfl⟩ := exists_of_divP T f (fun m => by
        obtain ⟨m', hm'⟩ := hf m
        exact ⟨p ^ n • m', by rw [hm', pow_succ', mul_smul]⟩)
      obtain ⟨g', rfl⟩ := ih g (fun m => by
        obtain ⟨m', hm'⟩ := hf m
        refine ⟨m', eq_of_sub_eq_zero (eq_zero_of_pow_smul' T 1 _ ?_)⟩
        have h := map_pow_smul' T 1 g m
        simp only [pow_one] at h
        rw [pow_one, smul_sub, ← h, hm', pow_succ', mul_smul, sub_self])
      exact ⟨g', by rw [smul_smul, ← pow_succ']⟩
  refine ⟨fun n => part1 n f, fun h0 => ?_⟩
  refine hom_ext_conv fun n => ?_
  obtain ⟨g, rfl⟩ := part1 n f (fun m => ⟨0, by rw [h0, LinearMap.zero_apply, smul_zero]⟩)
  rw [pow_smul_conv, zero_conv]

end GlobalTheory.Dieu.Integrality
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.AutGrowth

noncomputable section

namespace GlobalTheory.CentreInherit

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

def stab (φ : Sm E n) : Subgroup (GL (Fin n) (Af E)) where
  carrier := {k | finRep E n k φ = φ}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
    rw [hy, hx]
  one_mem' := by simp
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

theorem ktype_of_central {ψ : Sm E n} (hk : FiniteDimensional ℂ (spanK E n ψ)) {z : Module.End ℂ (Sm E n)}
    (hz : z ∈ Zalg E n) (W' : Submodule ℂ (Kinf E n → ℂ))
    (hW : ∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ).1 g) ∈ W') (g : GA E n) :
    (fun k : Kinf E n => (cptRep E n k (z ψ)).1 g) ∈ W' := by
  let S := spanK E n ψ
  let ev : GA E n → Module.Dual ℂ S := fun h => (LinearMap.proj h).comp ((Sm E n).subtype.comp S.subtype)
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      have h2 : ∀ h, v.1.1 h = 0 := fun h => hv _ (Submodule.subset_span ⟨h, rfl⟩)
      rw [Submodule.mem_bot]
      exact Subtype.ext (Subtype.ext (funext h2))
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), h0,
      Submodule.dualAnnihilator_bot]
  have hmem : ∀ k, cptRep E n k ψ ∈ S := fun k => Submodule.subset_span ⟨k, rfl⟩
  have key : ∀ m ∈ Submodule.span ℂ (Set.range ev), (fun k => m ⟨cptRep E n k ψ, hmem k⟩) ∈ W' := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx => obtain ⟨h, rfl⟩ := hx; exact hW h
    | zero => exact W'.zero_mem
    | add x y _ _ hx hy => exact W'.add_mem hx hy
    | smul c x _ hx => exact W'.smul_mem c hx
  let ℓ : Module.Dual ℂ S := (LinearMap.proj g).comp ((Sm E n).subtype.comp (z.comp S.subtype))
  have e : (fun k : Kinf E n => (cptRep E n k (z ψ)).1 g) = fun k => ℓ ⟨cptRep E n k ψ, hmem k⟩ := by
    funext k
    have h1 := LinearMap.congr_fun (GlobalTheory.ZalgCpt.zalg_comm_cptRep E n k z hz) ψ
    simp only [Module.End.mul_apply] at h1
    show _ = (z (cptRep E n k ψ)).1 g
    rw [h1]
  rw [e]
  exact key ℓ (hspan ▸ Submodule.mem_top)

theorem central_of_tame {ψ : Sm E n} (hA : IsAutForm ψ) (htame : ψ ∈ tame E n) {z : Module.End ℂ (Sm E n)}
    (hz : z ∈ Zalg E n) (L' : Subgroup (GL (Fin n) (Af E))) (W' : Submodule ℂ (Kinf E n → ℂ))
    (hL : ∀ k ∈ L', finRep E n k ψ = ψ) (hW : ∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ).1 g) ∈ W') :
    IsAutForm (z ψ) ∧ (∀ k ∈ L', finRep E n k (z ψ) = z ψ) ∧
      ∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k (z ψ)).1 g) ∈ W' := by
  have hs : z ψ ∈ fixL E n (stab ψ) :=
    Zalg_stable (V := fixL E n (stab ψ)) (fun X _ h => lie_mem_fixL _ X h) hz ψ (fun k hk => hk)
  refine ⟨⟨Zalg_stable (V := leftInv E n) (fun X _ h => lie_mem_leftInv X h) hz ψ hA.left, ?_, ?_, ?_,
    growth_of_tame (Zalg_stable (V := tame E n) (fun X _ h => lie_mem_tame X h) hz ψ htame)⟩,
    Zalg_stable (V := fixL E n L') (fun X _ h => lie_mem_fixL L' X h) hz ψ hL,
    ktype_of_central hA.kfin hz W' hW⟩
  · exact isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (hA.level.mem_nhds (by simp)) fun k hk => hs k hk)
  · have := hA.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E n k ψ)).map z)
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
    have h1 := LinearMap.congr_fun (GlobalTheory.ZalgCpt.zalg_comm_cptRep E n k z hz) ψ
    simpa only [Module.End.mul_apply] using h1
  · have := hA.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun y : Module.End ℂ (Sm E n) => y ψ) '' Zalg E n)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z', hz', rfl⟩
    exact Submodule.subset_span ⟨z' * z, mul_mem hz' hz, rfl⟩

end GlobalTheory.CentreInherit

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.AutGrowth

namespace GlobalTheory.CentreInherit

theorem centre_preserves_forms : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ), (∀ (L' : Subgroup (GL (Fin n) (Af E))), IsOpen (L' : Set (GL (Fin n) (Af E))) → ∀ W' : Submodule ℂ (Kinf E n → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E n) → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E n L' W' X' N'))) → ∀ (L' : Subgroup (GL (Fin n) (Af E))) (W' : Submodule ℂ (Kinf E n → ℂ)) (ψ : Sm E n), IsAutForm ψ → (∀ k ∈ L', finRep E n k ψ = ψ) → (∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ).1 g) ∈ W') → ∀ ψ' ∈ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E n) => z ψ) '' Zalg E n), IsAutForm ψ' ∧ (∀ k ∈ L', finRep E n k ψ' = ψ') ∧ ∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ').1 g) ∈ W' := by
  intro E _ _ _ n hH L' W' ψ hA hL hW ψ' hψ'
  have htame : ψ ∈ tame E n := GlobalTheory.T.automorphicForm_GL_tame_of_finiteness_at_rank E n hH ψ hA
  induction hψ' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    exact central_of_tame hA htame hz L' W' hL hW
  | zero => exact ⟨GlobalTheory.HCF.FormsSub.isAutForm_zero, fun k _ => map_zero _, fun g => by
      convert W'.zero_mem using 1; funext k; simp⟩
  | add x y _ _ hx hy =>
    refine ⟨GlobalTheory.HCF.FormsSub.isAutForm_add hx.1 hy.1, fun k hk => by rw [map_add (f := _), hx.2.1 k hk, hy.2.1 k hk],
      fun g => ?_⟩
    convert W'.add_mem (hx.2.2 g) (hy.2.2 g) using 1
    funext k; simp [map_add (f := _)]
  | smul c x _ hx =>
    refine ⟨GlobalTheory.HCF.FormsSub.isAutForm_smul c hx.1, fun k hk => by rw [map_smul, hx.2.1 k hk], fun g => ?_⟩
    convert W'.smul_mem c (hx.2.2 g) using 1
    funext k; simp [map_smul]

end GlobalTheory.CentreInherit
end
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRowsTop


open GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum GlobalTheory.ColNorms GlobalTheory.PeriodClassSum GlobalTheory.LastPeriod in
theorem periodFun_le (hL : LastMapNorm) {X : Fields} (hX : X.Ok) {Pr : Primes X} (hPr : Pr.Ok) {R : Ranks} (W : Wts X Pr.Word R)
    (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ)
    (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) (hI : ∀ τ, Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ))
    (hS : ∀ τ, Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ)) (s : X.K →+* ℂ)
    (ψ : RowPt Pr R sel (mu0 X.F X.E X.K Sg) → Formalism.L2.DIV.VV X.K (W.lamTrue u R.m))
    (F : RowPt Pr R sel (mu0 X.F X.E X.K Sg) → Formalism.L2.DIV.VV X.K W.sgTrue) :
    ‖s (PtilFF W Ch sel (mu0 X.F X.E X.K Sg) P (mtildeOk W Ch sel (mu0 X.F X.E X.K Sg) hX P) u ψ F)‖ ^ 2 ≤
      Real.exp (lastLog W u) *
        GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt (evGSD W Ch sel (mu0 X.F X.E X.K Sg) P u) (GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.evOk W Ch sel Sg hX hPr P u) s ψ *
        GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt (mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P) (mtildeOk W Ch sel (mu0 X.F X.E X.K Sg) hX P) s F := by
  have hT : (0 : ℝ) < (Pr.T u : ℝ) := Nat.cast_pos.2 (hPr.T_prime u).pos
  have ht : ∀ τ, star (s (X.emb τ (star ((Pr.piT u : 𝓞 X.E) : X.E)))) * s (X.emb τ (star ((Pr.piT u : 𝓞 X.E) : X.E))) =
      ((Pr.T u : ℝ) : ℂ) := fun τ => by
    have h1 := hX.conjE (s.comp (X.emb τ)) (star ((Pr.piT u : 𝓞 X.E) : X.E))
    rw [star_star, RingHom.comp_apply, RingHom.comp_apply, starRingEnd_apply] at h1
    have h2 : ((Pr.piT u : 𝓞 X.E) : X.E) * star ((Pr.piT u : 𝓞 X.E) : X.E) = (Pr.T u : X.E) := by
      have := congrArg (fun z : 𝓞 X.E => (z : X.E)) (hPr.piT_norm u)
      simp only [map_mul, map_natCast] at this
      exact this
    rw [← h1, ← map_mul, ← map_mul, h2]
    simp
  have hB := coefOpLe_brAt hL s (N_m_succ R) (W.lamTrue u R.m) W.sgTrue hI hS _ hT _ ht
  set hM := mtildeOk W Ch sel (mu0 X.F X.E X.K Sg) hX P
  set hE := GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.evOk W Ch sel Sg hX hPr P u
  let _ := hM.fintypeCl
  have h := sum_pair_le s _ _ _ _ hB ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).toCSD hM).wt
    (fun c => ψ ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c))
    (fun c => F ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c))
  have e0 : PtilFF W Ch sel (mu0 X.F X.E X.K Sg) P hM u ψ F =
      ∑ c, ((((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).toCSD hM).wt c : ℕ) : X.K)⁻¹ *
        pairBK W.sgTrue (brC W u (ψ ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c)))
          (F ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c)) := by
    unfold PtilFF GSD.csOf
    exact (LinearMap.congr_fun (LinearMap.sum_apply _ _ _) _).trans (LinearMap.sum_apply _ _ _)
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt (evGSD W Ch sel (mu0 X.F X.E X.K Sg) P u) hE s ψ =
      ∑ c, ((((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).toCSD hM).wt c : ℕ) : ℝ)⁻¹ *
        sqAt s (W.lamTrue u R.m) (ψ ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c)) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt GSD.ipAt
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact (re_inv_mul _ _).trans
      (congrArg₂ (· * ·) rfl ((gram_posSemidef_and_sqAt X.E X.K X.Tau X.emb _ (W.lamTrue u R.m) s).2 _))
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt (mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P) hM s F =
      ∑ c, ((((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).toCSD hM).wt c : ℕ) : ℝ)⁻¹ *
        sqAt s W.sgTrue (F ((mtildeGSD W Ch sel (mu0 X.F X.E X.K Sg) P).outSec.rep c)) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt GSD.ipAt
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hg := (gram_posSemidef_and_sqAt X.E X.K X.Tau X.emb _ W.sgTrue s).2
    simp only [pairVr_one_eq, pairK_one_basis] at hg
    refine (re_inv_mul _ _).trans (congrArg₂ (· * ·) rfl (Eq.trans ?_ (hg _)))
    unfold GSD.pairAt
    rw [row_gramV]
    rfl
  rw [e0, e1, e2]
  refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ ?_) ?_)
  · rw [lastLog, Real.exp_add, mul_comm (-_ : ℝ), ← Real.rpow_def_of_pos hT, ← Int.cast_neg, Real.rpow_intCast]
    exact mul_le_mul_of_nonneg_left (Real.le_exp_log _) (by positivity)
  · exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (sqAt_nonneg _ _ _)
  · exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (sqAt_nonneg _ _ _)

theorem period_le (hL : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.LastMapNorm) {X : Fields} (hX : X.Ok) {Pr : Primes X} (hPr : Pr.Ok) {R : Ranks}
    (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} (mu : Tup X.F X.E X.K Sg) (hmu : mu = 1)
    (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) (hI : ∀ τ, Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ))
    (hS : ∀ τ, Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ))
    (hP : (mtildeGSD W Ch sel mu P).Ok) (hE : (evGSD W Ch sel mu P u).Ok) (v : InfinitePlace X.K)
    (ψ : RowPt Pr R sel mu → Formalism.L2.DIV.VV X.K (W.lamTrue u R.m)) (F : RowPt Pr R sel mu → Formalism.L2.DIV.VV X.K W.sgTrue) :
    v (PtilFF W Ch sel mu P hP u ψ F) ^ 2 ≤
      Real.exp (lastLog W u) * ((evGSD W Ch sel mu P u).ipAt hE v ψ ψ).re * ((mtildeGSD W Ch sel mu P).ipAt hP v F F).re := by
  subst hmu
  have h := periodFun_le hL hX hPr W Ch sel Sg P u hI hS v.embedding ψ F
  rw [InfinitePlace.norm_embedding_eq] at h
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.normSqAt, InfinitePlace.mk_embedding] at h
  exact h

theorem ipAt_nonneg_of_datFramed {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} {h : S.Ok} (hS : DatFramed S h)
    (v : InfinitePlace K) (ψ : S.EqFun) : 0 ≤ (S.ipAt h v ψ ψ).re := by
  obtain ⟨n, e, X, -, hX⟩ := hS
  obtain ⟨y, rfl⟩ := e.surjective ψ
  rw [← hX v y, Complex.ofReal_re]
  positivity

end GlobalTheory.ColRowsTop
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.quadraticTwist_cmCurve_model_discriminant_negPrimeCube : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ∈ F → ∀ V : ValuationSubring ℂ, ModelAt V F (shortTwist (if p % 8 = 3 then 1 else -(p : ℂ)) (-L.g₂ / 4) (-L.g₃ / 4)) (-(p : ℂ) ^ 3) := by
  first | exact @GlobalTheory.CMModel.twist_modelAt_all | exact GlobalTheory.CMModel.twist_modelAt_all | (intros; apply GlobalTheory.CMModel.twist_modelAt_all <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

theorem _root_.GlobalTheory.T.standardFrames_match_completedLattices_at_prime : ∀ {D : D7} {V V' : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (Q : principalLevelFrame.RowPsi V n) (Q' : principalLevelFrame.RowPsi V' n), StdPsi hF Q → StdPsi hF Q' → ∀ (P : Pl D.host.E) (e f : Formalism.L2.Theta.AE D), IsPrimeIdem P e f → V'.rank = V.rank ∧ ∃ (J : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (J' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), J * J' = 1 ∧ J' * J = 1 ∧ (∀ κ, finMat D.sp.cm.sig V'.gram (Q'.ψ κ) * J = J * finMat D.sp.cm.sig V.gram (Q.ψ κ)) ∧ ∀ y, finPart D f • y ∈ Formalism.L2.NTheta.LamHat V ↔ finPart D f • J.mulVec y ∈ Formalism.L2.NTheta.LamHat V' := by
  first | exact @GlobalTheory.LatMatch.frames_match_lattices | exact GlobalTheory.LatMatch.frames_match_lattices | (intros; apply GlobalTheory.LatMatch.frames_match_lattices <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.encard_small_sections_mul_le_quotient_power_twist : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, ∀ (N m : ℕ), (P.Bl N (m - c) 1).encard * (P.Bl 0 (b * N - c) 1).encard ≤ {f | f ∈ P.H N (-c) ∧ f * s ^ m ∈ P.Bl N (m - c) 2}.encard * (P.Bl 0 (b * N + m - c) 2).encard := by
  first | exact @GlobalTheory.HSNef.encard_mul_le_at_level_twist | exact GlobalTheory.HSNef.encard_mul_le_at_level_twist | (intros; apply GlobalTheory.HSNef.encard_mul_le_at_level_twist <;> assumption)
end
