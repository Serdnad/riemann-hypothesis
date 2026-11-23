module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Abelian.Exact
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
public import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle001

@[expose] public section

section

open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

noncomputable section

namespace GlobalTheory.UnimodTransvect

variable {R : Type} [CommRing R] {m : Type} [Fintype m] [DecidableEq m]

theorem vecMulVec_zero' (a : m → R) : vecMulVec a (0 : m → R) = 0 := by
  ext i j
  simp [vecMulVec]

def tv (a b : m → R) (h : b ⬝ᵥ a = 0) : GL m R where
  val := 1 + vecMulVec a b
  inv := 1 - vecMulVec a b
  val_inv := by
    rw [mul_sub, mul_one, add_mul, one_mul, vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero']; abel
  inv_val := by
    rw [sub_mul, one_mul, mul_add, mul_one, vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero']; abel

theorem tv_mulVec (a b : m → R) (h : b ⬝ᵥ a = 0) (v : m → R) :
    ((tv a b h : GL m R) : Matrix m m R) *ᵥ v = v + (b ⬝ᵥ v) • a := by
  change (1 + vecMulVec a b) *ᵥ v = _
  rw [add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem vecMul_tv_inv (a b : m → R) (h : b ⬝ᵥ a = 0) (f : m → R) :
    f ᵥ* (((tv a b h)⁻¹ : GL m R) : Matrix m m R) = f - (f ⬝ᵥ a) • b := by
  change f ᵥ* (1 - vecMulVec a b) = _
  rw [vecMul_sub, vecMul_one, vecMul_vecMulVec]

theorem reach_trans {v w u : m → R} (h1 : ∃ g : GL m R, (g : Matrix m m R) *ᵥ v = w)
    (h2 : ∃ g : GL m R, (g : Matrix m m R) *ᵥ w = u) : ∃ g : GL m R, (g : Matrix m m R) *ᵥ v = u := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨g2 * g1, ?_⟩
  rw [Units.val_mul, ← mulVec_mulVec, hg1, hg2]

variable {n : ℕ}

theorem reach_of_last_one (u : Fin (n + 1) → R) (hu : u (Fin.last n) = 1) :
    ∃ g : GL (Fin (n + 1)) R, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ u = Pi.single (Fin.last n) 1 := by
  refine ⟨tv (Pi.single (Fin.last n) 1 - u) (Pi.single (Fin.last n) 1) ?_, ?_⟩
  · rw [single_dotProduct, Pi.sub_apply, Pi.single_eq_same, hu]
    ring
  · rw [tv_mulVec, single_dotProduct, hu, one_mul, one_smul]
    abel

theorem reach_last_one (w : Fin (n + 1) → R) (c : Fin n → R)
    (hc : ∑ i, c i * w i.castSucc = 1) :
    ∃ g : GL (Fin (n + 1)) R, ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ w) (Fin.last n) = 1 := by
  obtain ⟨c', hc'⟩ : ∃ c' : Fin (n + 1) → R, c' = Fin.snoc c 0 := ⟨_, rfl⟩
  have hcl : c' (Fin.last n) = 0 := by simp [hc']
  have hcw : c' ⬝ᵥ w = 1 := by
    rw [dotProduct, Fin.sum_univ_castSucc, hcl, zero_mul, add_zero]
    simpa [hc'] using hc
  refine ⟨tv (Pi.single (Fin.last n) 1) ((1 - w (Fin.last n)) • c') ?_, ?_⟩
  · rw [dotProduct_single, Pi.smul_apply, hcl, smul_zero, zero_mul]
  · rw [tv_mulVec, smul_dotProduct, hcw, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
    simp only [smul_eq_mul]
    ring

theorem reach_first_unimod {s : ℕ} (hS : StableRangeLe R s) (hn : s ≤ n) (v f : Fin (n + 1) → R)
    (hfv : f ⬝ᵥ v = 1) :
    ∃ g : GL (Fin (n + 1)) R, ∃ c : Fin n → R, ∑ i, c i * ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ v) i.castSucc = 1 := by
  have hU : Unimodular R v := by
    unfold Unimodular
    rw [Ideal.eq_top_iff_one, ← hfv, Ideal.mem_span_range_iff_exists_fun]
    exact ⟨f, rfl⟩
  obtain ⟨t, ht⟩ := hS n hn v hU
  unfold Unimodular at ht
  have h1 : (1 : R) ∈ Ideal.span (Set.range fun i => v i.castSucc + t i * v (Fin.last n)) := by
    rw [ht]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
  obtain ⟨a, ha⟩ : ∃ a : Fin (n + 1) → R, a = Fin.snoc t 0 := ⟨_, rfl⟩
  have hal : a (Fin.last n) = 0 := by simp [ha]
  refine ⟨tv a (Pi.single (Fin.last n) 1) (by rw [single_dotProduct, hal, mul_zero]), c, ?_⟩
  refine (Finset.sum_congr rfl fun i _ => ?_).trans hc
  rw [tv_mulVec, single_dotProduct, one_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [ha, Fin.snoc_castSucc]
  ring

theorem main : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n : ℕ), s ≤ n → ∀ v f : Fin (n + 1) → R, f ⬝ᵥ v = 1 → ∃ g : GL (Fin (n + 1)) R, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ v = Pi.single (Fin.last n) 1 ∧ f ᵥ* ((g⁻¹ : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = Pi.single (Fin.last n) 1 := by
  intro R _ s hS n hn v f hfv
  obtain ⟨g1, c, hc⟩ := reach_first_unimod hS hn v f hfv
  obtain ⟨g2, hg2⟩ := reach_last_one _ c hc
  obtain ⟨g3, hg3⟩ := reach_of_last_one _ hg2
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin (n + 1)) R, g = g3 * g2 * g1 := ⟨_, rfl⟩
  have hgv : (g : Matrix _ _ R) *ᵥ v = Pi.single (Fin.last n) 1 := by
    rw [hg, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
    exact hg3
  obtain ⟨f', hf'⟩ : ∃ f' : Fin (n + 1) → R, f' = f ᵥ* ((g⁻¹ : GL _ R) : Matrix _ _ R) := ⟨_, rfl⟩
  have hfl : f' (Fin.last n) = 1 := by
    have : f' ⬝ᵥ ((g : Matrix _ _ R) *ᵥ v) = 1 := by
      rw [hf', ← dotProduct_mulVec, mulVec_mulVec, Units.inv_mul, one_mulVec, hfv]
    rwa [hgv, dotProduct_single, mul_one] at this
  have hb : (f' - Pi.single (Fin.last n) 1) ⬝ᵥ Pi.single (Fin.last n) (1 : R) = 0 := by
    rw [dotProduct_single, Pi.sub_apply, hfl, Pi.single_eq_same]
    ring
  refine ⟨tv (Pi.single (Fin.last n) 1) (f' - Pi.single (Fin.last n) 1) hb * g, ?_, ?_⟩
  · rw [Units.val_mul, ← mulVec_mulVec, hgv, tv_mulVec, hb, zero_smul, add_zero]
  · rw [_root_.mul_inv_rev, Units.val_mul, ← vecMul_vecMul, ← hf', vecMul_tv_inv, dotProduct_single,
      hfl, mul_one, one_smul]
    abel

end GlobalTheory.UnimodTransvect

end

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exists_GL_moving_unimodular_pair_to_last_basis : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n : ℕ), s ≤ n → ∀ v f : Fin (n + 1) → R, f ⬝ᵥ v = 1 → ∃ g : GL (Fin (n + 1)) R, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ v = Pi.single (Fin.last n) 1 ∧ f ᵥ* ((g⁻¹ : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = Pi.single (Fin.last n) 1 := by
  first
  | exact @GlobalTheory.UnimodTransvect.main
  | exact @GlobalTheory.UnimodTransvect.reach_first_unimod
  | exact @GlobalTheory.UnimodTransvect.reach_last_one
  | exact @GlobalTheory.UnimodTransvect.reach_of_last_one
  | exact @GlobalTheory.UnimodTransvect.reach_trans
  | exact @GlobalTheory.UnimodTransvect.vecMul_tv_inv
  | exact @GlobalTheory.UnimodTransvect.tv_mulVec
  | exact @GlobalTheory.UnimodTransvect.vecMulVec_zero'
end
end

section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem exists_free_shortExact : ∀ (k G : Type) [CommRing k] [Group G] (A : Rep k G), ∃ (ι : Type) (K : Rep k G) (i : K ⟶ Rep.free k G ι) (e : Rep.free k G ι ⟶ A) (h : i ≫ e = 0), (ShortComplex.mk i e h).ShortExact := by
  intro k G _ _ A
  let e : Rep.free k G A ⟶ A := Rep.freeLift k G A (fun x => x)
  have he : Epi e := (Rep.epi_iff_surjective e).2 fun x =>
    ⟨Finsupp.single x (MonoidAlgebra.single 1 1), by
      simp [e, Representation.freeLift_single_single]⟩
  exact ⟨A, kernel e, kernel.ι e, e, kernel.condition e,
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel e) inferInstance he⟩

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.exists_free_resolution_short_exact : ∀ (k G : Type) [CommRing k] [Group G] (A : Rep k G), ∃ (ι : Type) (K : Rep k G) (i : K ⟶ Rep.free k G ι) (e : Rep.free k G ι ⟶ A) (h : i ≫ e = 0), (ShortComplex.mk i e h).ShortExact := by
  first
  | exact @GlobalTheory.HomStab.exists_free_shortExact
end
end

section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.TruncFirstCycles

theorem main : ∀ (k G : Type) [CommRing k] [Group G] (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → Function.Exact (d 1).hom (d 0).hom → ∃ (Z : Rep k G) (ι : Z ⟶ C 1) (h : ι ≫ d 0 = 0) (b : C 2 ⟶ Z), (ShortComplex.mk ι (d 0) h).ShortExact ∧ b ≫ ι = d 1 ∧ Function.Surjective b.hom ∧ d 2 ≫ b = 0 ∧ (Function.Exact (d 2).hom (d 1).hom → Function.Exact (d 2).hom b.hom) := by
  intro k G _ _ C d hdd hsurj hex
  have hz0 : ∀ x : C 2, (d 0).hom ((d 1).hom x) = 0 := by
    intro x
    have h := congrArg (fun f => (Rep.Hom.hom f) x) (hdd 0)
    simpa [Rep.hom_comp] using h
  have hz1 : ∀ x : C 3, (d 1).hom ((d 2).hom x) = 0 := by
    intro x
    have h := congrArg (fun f => (Rep.Hom.hom f) x) (hdd 1)
    simpa [Rep.hom_comp] using h
  let K := (d 0).hom.ker
  let ι : Rep.of K.toRepresentation ⟶ C 1 :=
    Rep.ofHom (σ := (C 1).ρ) ⟨K.toSubmodule.subtype, fun g => by ext; rfl⟩
  let bl : C 2 →ₗ[k] K.toSubmodule :=
    (d 1).hom.toLinearMap.codRestrict K.toSubmodule (fun x => hz0 x)
  let b : C 2 ⟶ Rep.of K.toRepresentation :=
    Rep.ofHom (ρ := (C 2).ρ) ⟨bl, fun g => by
      ext x
      exact Rep.hom_comm_apply (d 1) g x⟩
  have hιd : ι ≫ d 0 = 0 := by
    apply Rep.hom_ext
    ext x
    exact x.2
  refine ⟨Rep.of K.toRepresentation, ι, hιd, b, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      { exact := (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful _ <|
          (ShortComplex.moduleCat_exact_iff _).2 fun x hx => ⟨⟨x, hx⟩, rfl⟩
        mono_f := (Rep.mono_iff_injective _).2 fun _ _ h => Subtype.ext h
        epi_g := (Rep.epi_iff_surjective _).2 hsurj }
  · apply Rep.hom_ext
    ext x
    rfl
  · intro z
    obtain ⟨y, hy⟩ := (hex z.1).1 z.2
    exact ⟨y, Subtype.ext hy⟩
  · apply Rep.hom_ext
    ext x
    exact hz1 x
  · intro h2 y
    rw [← h2 y]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end GlobalTheory.HomStab.TruncFirstCycles

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.exists_syzygy_factorization : ∀ (k G : Type) [CommRing k] [Group G] (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → Function.Exact (d 1).hom (d 0).hom → ∃ (Z : Rep k G) (ι : Z ⟶ C 1) (h : ι ≫ d 0 = 0) (b : C 2 ⟶ Z), (ShortComplex.mk ι (d 0) h).ShortExact ∧ b ≫ ι = d 1 ∧ Function.Surjective b.hom ∧ d 2 ≫ b = 0 ∧ (Function.Exact (d 2).hom (d 1).hom → Function.Exact (d 2).hom b.hom) := by
  first
  | exact @GlobalTheory.HomStab.TruncFirstCycles.main
end
end

section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
namespace GlobalTheory.HomStab

theorem isIso_map_succ_of_shortExact : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (φ : H →* G) (X : ShortComplex (Rep k H)) (Y : ShortComplex (Rep k G)), X.ShortExact → Y.ShortExact → ∀ (u₁ : X.X₁ ⟶ Rep.res φ Y.X₁) (u₂ : X.X₂ ⟶ Rep.res φ Y.X₂) (u₃ : X.X₃ ⟶ Rep.res φ Y.X₃), (∀ a, u₂.hom (X.f.hom a) = Y.f.hom (u₁.hom a)) → (∀ a, u₃.hom (X.g.hom a) = Y.g.hom (u₂.hom a)) → ∀ n : ℕ, IsZero (groupHomology X.X₂ (n + 1)) → IsZero (groupHomology Y.X₂ (n + 1)) → IsIso (groupHomology.map φ u₁ n) → IsIso (groupHomology.map φ u₂ n) → IsIso (groupHomology.map φ u₃ (n + 1)) := by
  intro k G H _ _ _ φ X Y hX hY u₁ u₂ u₃ h12 h23 n hX2 hY2 hb hc
  have c12 : groupHomology.chainsMap φ u₁ ≫ (groupHomology.chainsFunctor k G).map Y.f =
      (groupHomology.chainsFunctor k H).map X.f ≫ groupHomology.chainsMap φ u₂ := by
    show groupHomology.chainsMap φ u₁ ≫ groupHomology.chainsMap (MonoidHom.id G) Y.f =
      groupHomology.chainsMap (MonoidHom.id H) X.f ≫ groupHomology.chainsMap φ u₂
    rw [← groupHomology.chainsMap_comp, ← groupHomology.chainsMap_comp]
    exact groupHomology.chainsMap_congr (by ext; rfl) (by ext a; simpa using (h12 a).symm)
  have c23 : groupHomology.chainsMap φ u₂ ≫ (groupHomology.chainsFunctor k G).map Y.g =
      (groupHomology.chainsFunctor k H).map X.g ≫ groupHomology.chainsMap φ u₃ := by
    show groupHomology.chainsMap φ u₂ ≫ groupHomology.chainsMap (MonoidHom.id G) Y.g =
      groupHomology.chainsMap (MonoidHom.id H) X.g ≫ groupHomology.chainsMap φ u₃
    rw [← groupHomology.chainsMap_comp, ← groupHomology.chainsMap_comp]
    exact groupHomology.chainsMap_congr (by ext; rfl) (by ext a; simpa using (h23 a).symm)
  let Φ : X.map (groupHomology.chainsFunctor k H) ⟶ Y.map (groupHomology.chainsFunctor k G) :=
    { τ₁ := groupHomology.chainsMap φ u₁
      τ₂ := groupHomology.chainsMap φ u₂
      τ₃ := groupHomology.chainsMap φ u₃
      comm₁₂ := c12
      comm₂₃ := c23 }
  have sX := groupHomology.map_chainsFunctor_shortExact hX
  have sY := groupHomology.map_chainsFunctor_shortExact hY
  have hnat := HomologicalComplex.HomologySequence.δ_naturality Φ sX sY (n + 1) n rfl
  have hf : groupHomology.map φ u₁ n ≫
      HomologicalComplex.homologyMap ((groupHomology.chainsFunctor k G).map Y.f) n =
      HomologicalComplex.homologyMap ((groupHomology.chainsFunctor k H).map X.f) n ≫
        groupHomology.map φ u₂ n := by
    have h := congrArg (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) n).map c12
    exact ((HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) n).map_comp
      (groupHomology.chainsMap φ u₁) ((groupHomology.chainsFunctor k G).map Y.f)).symm.trans
      (h.trans ((HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) n).map_comp
        ((groupHomology.chainsFunctor k H).map X.f) (groupHomology.chainsMap φ u₂)))
  have hz := sY.δ_comp (n + 1) n rfl
  have monoX := groupHomology.mono_δ_of_isZero hX n hX2
  have monoY := groupHomology.mono_δ_of_isZero hY n hY2
  have exX := (ShortComplex.moduleCat_exact_iff _).mp (sX.homology_exact₁ (n + 1) n rfl)
  rw [ModuleCat.mono_iff_injective] at monoX monoY
  rw [ConcreteCategory.isIso_iff_bijective] at hb hc ⊢
  have e1 : ∀ x, ConcreteCategory.hom (groupHomology.map φ u₁ n)
      (ConcreteCategory.hom (groupHomology.δ hX (n + 1) n rfl) x) =
      ConcreteCategory.hom (groupHomology.δ hY (n + 1) n rfl)
        (ConcreteCategory.hom (groupHomology.map φ u₃ (n + 1)) x) := by
    intro x
    have h := ConcreteCategory.congr_hom hnat x
    exact h
  have e2 : ∀ x, ConcreteCategory.hom
      (HomologicalComplex.homologyMap ((groupHomology.chainsFunctor k G).map Y.f) n)
      (ConcreteCategory.hom (groupHomology.map φ u₁ n) x) =
      ConcreteCategory.hom (groupHomology.map φ u₂ n)
        (ConcreteCategory.hom
          (HomologicalComplex.homologyMap ((groupHomology.chainsFunctor k H).map X.f) n) x) := by
    intro x
    have h := ConcreteCategory.congr_hom hf x
    exact h
  have e3 : ∀ y, ConcreteCategory.hom
      (HomologicalComplex.homologyMap ((groupHomology.chainsFunctor k G).map Y.f) n)
      (ConcreteCategory.hom (groupHomology.δ hY (n + 1) n rfl) y) = 0 := by
    intro y
    have h := ConcreteCategory.congr_hom hz y
    exact h.trans rfl
  constructor
  · intro a b hab
    apply monoX
    apply hb.1
    rw [e1, e1, hab]
  · intro y
    obtain ⟨x1, hx1⟩ := hb.2 (ConcreteCategory.hom (groupHomology.δ hY (n + 1) n rfl) y)
    have h0 : ConcreteCategory.hom
        (HomologicalComplex.homologyMap ((groupHomology.chainsFunctor k H).map X.f) n) x1 = 0 := by
      apply hc.1
      rw [← e2, hx1, e3]
      exact (map_zero _).symm
    obtain ⟨x3, hx3⟩ := exX x1 h0
    refine ⟨x3, monoY ?_⟩
    exact (e1 x3).symm.trans ((congrArg _ hx3).trans hx1)

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.groupHomology_dimension_shift_isIso : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (φ : H →* G) (X : ShortComplex (Rep k H)) (Y : ShortComplex (Rep k G)), X.ShortExact → Y.ShortExact → ∀ (u₁ : X.X₁ ⟶ Rep.res φ Y.X₁) (u₂ : X.X₂ ⟶ Rep.res φ Y.X₂) (u₃ : X.X₃ ⟶ Rep.res φ Y.X₃), (∀ a, u₂.hom (X.f.hom a) = Y.f.hom (u₁.hom a)) → (∀ a, u₃.hom (X.g.hom a) = Y.g.hom (u₂.hom a)) → ∀ n : ℕ, IsZero (groupHomology X.X₂ (n + 1)) → IsZero (groupHomology Y.X₂ (n + 1)) → IsIso (groupHomology.map φ u₁ n) → IsIso (groupHomology.map φ u₂ n) → IsIso (groupHomology.map φ u₃ (n + 1)) := by
  first
  | exact @GlobalTheory.HomStab.isIso_map_succ_of_shortExact
end
end

section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem resFunctor_isEquivalence_of_bijective {k G H : Type} [CommRing k] [Group G] [Group H]
    (ψ : H →* G) (hψ : Function.Bijective ψ) : (Rep.resFunctor (k := k) ψ).IsEquivalence := by
  let e : H ≃* G := MulEquiv.ofBijective ψ hψ
  haveI : (Rep.resFunctor (k := k) ψ).Full := Rep.full_res ψ hψ.2
  haveI : (Rep.resFunctor (k := k) ψ).EssSurj := ⟨fun N => ⟨Rep.of (N.ρ.comp e.symm.toMonoidHom),
    ⟨Rep.mkIso (.mk (LinearEquiv.refl k N.V) fun h => by
      ext x
      change N.ρ (e.symm (ψ h)) x = N.ρ h x
      have : e.symm (ψ h) = h := e.symm_apply_apply h
      rw [this])⟩⟩⟩
  exact { }

theorem projective_res_of_injective {k G H : Type} [CommRing k] [Group G] [Group H]
    (φ : H →* G) (hφ : Function.Injective φ) (P : Rep k G) [Projective P] :
    Projective (Rep.res φ P) := by
  let ψ : H →* φ.range := φ.rangeRestrict
  have hψ : Function.Bijective ψ := ⟨φ.rangeRestrict_injective_iff.2 hφ, φ.rangeRestrict_surjective⟩
  haveI := resFunctor_isEquivalence_of_bijective (k := k) ψ hψ
  have h1 : Projective (Rep.res φ.range.subtype P) :=
    (Rep.resFunctor (k := k) φ.range.subtype).projective_obj_of_projective (X := P) inferInstance
  have h2 : Projective (Rep.res ψ (Rep.res φ.range.subtype P)) :=
    (Rep.resFunctor (k := k) ψ).projective_obj_of_projective h1
  exact h2

end GlobalTheory.HomStab

theorem GlobalTheory.HomStab.projective_res_free_of_injective : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (φ : H →* G), Function.Injective φ → ∀ ι : Type, Projective (Rep.res φ (Rep.free k G ι)) := by
  intro k G H _ _ _ φ hφ ι
  exact GlobalTheory.HomStab.projective_res_of_injective φ hφ _

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.projective_res_free_rep_of_injective : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (φ : H →* G), Function.Injective φ → ∀ ι : Type, Projective (Rep.res φ (Rep.free k G ι)) := by
  first
  | exact @GlobalTheory.HomStab.projective_res_free_of_injective
  | exact @GlobalTheory.HomStab.projective_res_of_injective
  | exact @GlobalTheory.HomStab.resFunctor_isEquivalence_of_bijective
end
end
