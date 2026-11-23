module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle018
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle001
public import Mathlib.Data.Finset.Powerset
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Mathlib.LinearAlgebra.Determinant
import GroundTheory.GlobalFields.HerbrandQuotients.RationalForm
import GroundTheory.LocalFields.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

section

open Matrix

namespace GlobalTheory.CompanionTheory.LinAlg

theorem exists_GL_lastRow_eq : ∀ (K : Type) [Field K] (n : ℕ) (a : Fin (n + 1) → K), a ≠ 0 →
    ∃ m : GL (Fin (n + 1)) K, vecMul (Pi.single (Fin.last n) 1) (m : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = a := by
  apply GlobalTheory.CompanionTheory.RowSect.exists_GL_last_row <;> assumption

end GlobalTheory.CompanionTheory.LinAlg
end

section

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField

namespace GlobalTheory.CompanionTheory.StdCharQ

end GlobalTheory.CompanionTheory.StdCharQ
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh

namespace GlobalTheory.CompanionTheory.Axis

def USt {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module R M] (z : ∀ T : C, M ⊗[R] F.obj T),
    (∀ (T T' : C) (φ : T ⟶ T'), z T' = (mp F φ).toLinearMap.lTensor M (z T)) →
    ∃! m : M, ∀ T, z T = m ⊗ₜ[R] (1 : F.obj T)

def evZ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {T T' : C} (φ : T ⟶ T') :
    Z1 F →ₗ[R] F.obj T' where
  toFun f := f.1 T T' φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end GlobalTheory.CompanionTheory.Axis
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Limits Simplicial

namespace GlobalTheory.CompanionTheory.Hodge.Nerve

variable {R : Type} [CommRing R]

section Cochains

variable {C : Type} [Category.{0} C]

abbrev NC (G : C ⥤ ModuleCat.{0} R) (n : ℕ) : Type :=
  ∀ c : Fin (n + 1) ⥤ C, G.obj (c.obj (Fin.last n))

def pullNC (G : C ⥤ ModuleCat.{0} R) {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) : NC G m →ₗ[R] NC G n :=
  LinearMap.pi fun c ↦ (G.map (c.map (homOfLE (Fin.le_last (θ (Fin.last m)))))).hom ∘ₗ
    LinearMap.proj (R := R) (φ := fun c : Fin (m + 1) ⥤ C ↦ (G.obj (c.obj (Fin.last m)) : Type))
      (θ.monotone.functor ⋙ c)

theorem pullNC_apply (G : C ⥤ ModuleCat.{0} R) {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) (f : NC G m)
    (c : Fin (n + 1) ⥤ C) :
    pullNC G θ f c = (G.map (c.map (homOfLE (Fin.le_last (θ (Fin.last m)))))).hom (f (θ.monotone.functor ⋙ c)) :=
  rfl

theorem map_map_chain (G : C ⥤ ModuleCat.{0} R) {n : ℕ} (c : Fin (n + 1) ⥤ C) {x y z : Fin (n + 1)} (a : x ≤ y)
    (b : y ≤ z) (v : G.obj (c.obj x)) :
    (G.map (c.map (homOfLE b))).hom ((G.map (c.map (homOfLE a))).hom v) =
      (G.map (c.map (homOfLE (a.trans b)))).hom v := by
  rw [← ModuleCat.comp_apply, ← G.map_comp, ← c.map_comp]
  rfl

def cosimp (G : C ⥤ ModuleCat.{0} R) : CosimplicialObject (ModuleCat.{0} R) where
  obj n := ModuleCat.of R (NC G n.len)
  map θ := ModuleCat.ofHom (pullNC G θ.toOrderHom)
  map_id n := by
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ funext fun c ↦ ?_)
    have e : c.map (homOfLE (Fin.le_last (Fin.last n.len))) = 𝟙 _ := c.map_id _
    change (G.map (c.map (homOfLE (Fin.le_last (Fin.last n.len))))).hom (f c) = f c
    rw [e, G.map_id]
    rfl
  map_comp {a b d} θ ψ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ funext fun c ↦ ?_)
    change (G.map (c.map _)).hom (f ((θ ≫ ψ).toOrderHom.monotone.functor ⋙ c)) =
      (G.map (c.map _)).hom ((G.map (c.map (homOfLE (ψ.toOrderHom.monotone (Fin.le_last (θ.toOrderHom (Fin.last a.len))))))).hom
        (f (θ.toOrderHom.monotone.functor ⋙ ψ.toOrderHom.monotone.functor ⋙ c)))
    exact (map_map_chain G c _ _ _).symm

def cosimpMap {G G' : C ⥤ ModuleCat.{0} R} (φ : G ⟶ G') : cosimp G ⟶ cosimp G' where
  app n := ModuleCat.ofHom (LinearMap.pi fun c ↦ (φ.app _).hom ∘ₗ
    LinearMap.proj (R := R) (φ := fun c : Fin (n.len + 1) ⥤ C ↦ (G.obj (c.obj (Fin.last n.len)) : Type)) c)
  naturality a b θ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ funext fun c ↦ ?_)
    exact congr(($(φ.naturality (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last a.len)))))).hom _))

def cosimpFunctor : (C ⥤ ModuleCat.{0} R) ⥤ CosimplicialObject (ModuleCat.{0} R) where
  obj := cosimp
  map := cosimpMap
  map_id _ := rfl
  map_comp _ _ := rfl

def nerveCx : (C ⥤ ModuleCat.{0} R) ⥤ CochainComplex (ModuleCat.{0} R) ℕ :=
  cosimpFunctor ⋙ AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{0} R)

instance : (nerveCx (R := R) (C := C)).PreservesZeroMorphisms where
  map_zero G G' := by
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun f ↦ funext fun c ↦ ?_)
    change (0 : G.obj _ ⟶ G'.obj _).hom (f c) = 0
    rfl

def dNC (G : C ⥤ ModuleCat.{0} R) (n : ℕ) : NC G n →ₗ[R] NC G (n + 1) :=
  ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) • pullNC G (Fin.succAboveOrderEmb i).toOrderHom

theorem nerveCx_d (G : C ⥤ ModuleCat.{0} R) (n : ℕ) :
    (nerveCx.obj G).d n (n + 1) = ModuleCat.ofHom (dNC G n) := by
  have h0 : (nerveCx.obj G).d n (n + 1) = AlgebraicTopology.AlternatingCofaceMapComplex.objD (cosimp G) n :=
    CochainComplex.of_d (fun n ↦ (cosimp G).obj ⦋n⦌) (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cosimp G)) n
  refine h0.trans ?_
  change (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (ModuleCat.ofHom (pullNC G (Fin.succAboveOrderEmb i).toOrderHom) :
    ModuleCat.of R (NC G n) ⟶ ModuleCat.of R (NC G (n + 1)))) = _
  refine ModuleCat.hom_ext ?_
  rw [ModuleCat.hom_ofHom, ModuleCat.hom_sum]
  unfold dNC
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h : ((-1 : R) ^ (i : ℕ)) = (((-1 : ℤ) ^ (i : ℕ) : ℤ) : R) := by push_cast; rfl
  rw [h, Int.cast_smul_eq_zsmul, ModuleCat.hom_zsmul, ModuleCat.hom_ofHom]

@[simps] def toMod (F : C ⥤ CommAlgCat.{0} R) : C ⥤ ModuleCat.{0} R where
  obj T := ModuleCat.of R (F.obj T)
  map φ := ModuleCat.ofHom (GlobalTheory.CatCoh.mp F φ).toLinearMap
  map_id T := ModuleCat.hom_ext (LinearMap.ext fun b ↦ GlobalTheory.CatCoh.mp_id F T b)
  map_comp φ ψ := ModuleCat.hom_ext (LinearMap.ext fun b ↦ GlobalTheory.CatCoh.mp_comp F φ ψ b)

end Cochains

section Cube

variable {P : Type} [SemilatticeInf P] {κ : Type} (e : κ → P)

def cubeRes (G : Pᵒᵖ ⥤ ModuleCat.{0} R) {s t : Finset κ} (h : s ⊆ t) :
    (∀ hs : PLift s.Nonempty, G.obj (op (s.inf' hs.down e))) →ₗ[R]
      ∀ ht : PLift t.Nonempty, G.obj (op (t.inf' ht.down e)) :=
  LinearMap.pi fun _ ↦ if hs : s.Nonempty then
    (G.map (homOfLE (Finset.inf'_mono e h hs)).op).hom ∘ₗ
      LinearMap.proj (R := R) (φ := fun hs : PLift s.Nonempty ↦ (G.obj (op (s.inf' hs.down e)) : Type)) ⟨hs⟩
  else 0

theorem cubeRes_apply (G : Pᵒᵖ ⥤ ModuleCat.{0} R) {s t : Finset κ} (h : s ⊆ t)
    (x : ∀ hs : PLift s.Nonempty, G.obj (op (s.inf' hs.down e))) (hs : s.Nonempty) (ht : PLift t.Nonempty) :
    cubeRes e G h x ht = (G.map (homOfLE (Finset.inf'_mono e h hs)).op).hom (x ⟨hs⟩) := by
  simp [cubeRes, hs]

theorem cubeRes_empty (G : Pᵒᵖ ⥤ ModuleCat.{0} R) {s t : Finset κ} (h : s ⊆ t)
    (x : ∀ hs : PLift s.Nonempty, G.obj (op (s.inf' hs.down e))) (hs : ¬ s.Nonempty) (ht : PLift t.Nonempty) :
    cubeRes e G h x ht = 0 := by
  simp [cubeRes, hs]

def cubeOf (G : Pᵒᵖ ⥤ ModuleCat.{0} R) : Cube.{0} κ R :=
  Cube.mk (fun s ↦ ModuleCat.of R (∀ hs : PLift s.Nonempty, G.obj (op (s.inf' hs.down e))))
    (fun h ↦ cubeRes e G h)
    (fun s x ↦ funext fun hs ↦ by
      rw [cubeRes_apply e G _ x hs.down hs]
      exact congr(($(G.map_id (op (s.inf' hs.down e)))).hom (x hs)))
    (fun {s t w} h h' x ↦ funext fun hw ↦ by
      by_cases hs : s.Nonempty
      · rw [cubeRes_apply e G h' _ (hs.mono h) hw, cubeRes_apply e G h x hs ⟨hs.mono h⟩,
          cubeRes_apply e G (h.trans h') x hs hw, ← ModuleCat.comp_apply, ← G.map_comp]
        rfl
      · rw [cubeRes_empty e G (h.trans h') x hs hw]
        by_cases ht : t.Nonempty
        · rw [cubeRes_apply e G h' _ ht hw, cubeRes_empty e G h x hs ⟨ht⟩, map_zero]
        · rw [cubeRes_empty e G h' _ ht hw])

def cubeOfMap {G G' : Pᵒᵖ ⥤ ModuleCat.{0} R} (φ : G ⟶ G') : cubeOf e G ⟶ cubeOf e G' :=
  Cube.homMk κ R (fun s ↦ LinearMap.pi fun hs ↦ (φ.app _).hom ∘ₗ
      LinearMap.proj (R := R) (φ := fun hs : PLift s.Nonempty ↦ (G.obj (op (s.inf' hs.down e)) : Type)) hs)
    (fun {s t} h x ↦ funext fun ht ↦ by
      by_cases hs : s.Nonempty
      · refine ((congrArg (φ.app _).hom (cubeRes_apply e G h x hs ht)).trans ?_).trans
          (cubeRes_apply e G' h _ hs ht).symm
        exact congr(($(φ.naturality (homOfLE (Finset.inf'_mono e h hs)).op)).hom (x ⟨hs⟩))
      · exact ((congrArg (φ.app _).hom (cubeRes_empty e G h x hs ht)).trans (map_zero _)).trans
          (cubeRes_empty e G' h _ hs ht).symm)

def cubeOfFunctor : (Pᵒᵖ ⥤ ModuleCat.{0} R) ⥤ Cube.{0} κ R where
  obj := cubeOf e
  map := cubeOfMap e
  map_id G := by
    ext s
    rfl
  map_comp φ ψ := by
    ext s
    rfl

def cechOf [LinearOrder κ] : (Pᵒᵖ ⥤ ModuleCat.{0} R) ⥤ CochainComplex (ModuleCat.{0} R) ℕ :=
  cubeOfFunctor e ⋙ cechFunctor κ R

instance : (cubeOfFunctor (R := R) e).PreservesZeroMorphisms := ⟨fun G G' ↦ by ext s; rfl⟩

instance [LinearOrder κ] : (cechOf (R := R) e).PreservesZeroMorphisms := by
  unfold cechOf
  infer_instance

end Cube

section Coinduced

variable {P : Type} [SemilatticeInf P]

def coind (M : P → ModuleCat.{0} R) : Pᵒᵖ ⥤ ModuleCat.{0} R where
  obj a := ModuleCat.of R (∀ b : {b : P // b ≤ a.unop}, M b.1)
  map {a a'} φ := ModuleCat.ofHom
    { toFun := fun f b ↦ f ⟨b.1, b.2.trans (leOfHom φ.unop)⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

def toCoind (G : Pᵒᵖ ⥤ ModuleCat.{0} R) : G ⟶ coind fun b ↦ G.obj (op b) where
  app a := ModuleCat.ofHom
    { toFun := fun x b ↦ (G.map (homOfLE b.2).op).hom x
      map_add' := fun x y ↦ funext fun b ↦ map_add _ x y
      map_smul' := fun r x ↦ funext fun b ↦ map_smul _ r x }
  naturality a a' φ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ funext fun b ↦ ?_)
    change (G.map (homOfLE b.2).op).hom ((G.map φ).hom x) = (G.map (homOfLE (b.2.trans (leOfHom φ.unop))).op).hom x
    rw [← ModuleCat.comp_apply, ← G.map_comp]
    rfl

end Coinduced

end GlobalTheory.CompanionTheory.Hodge.Nerve
end
end

section

open GlobalTheory.PRep

namespace GlobalTheory.CompanionTheory.PRep

theorem twKer_eq_map_of_surjective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (N : Subgroup G) (θ : N →* ℂˣ) (f : V →ₗ[ℂ] W) (hf : Function.Surjective f)
    (hint : ∀ g v, f (ρ g v) = σ g (f v)) : twKer σ N θ = (twKer ρ N θ).map f := by
  unfold GlobalTheory.PRep.twKer
  rw [Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨n, w', rfl⟩
    obtain ⟨v, rfl⟩ := hf w'
    exact ⟨ρ n v - (θ n : ℂ) • v, ⟨n, v, rfl⟩, by rw [map_sub, map_smul, hint]⟩
  · rintro ⟨_, ⟨n, v, rfl⟩, rfl⟩
    exact ⟨n, f v, by rw [map_sub, map_smul, hint]⟩

theorem twKer_map_closed : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (N : Subgroup G)
    (θ : N →* ℂˣ) (f : V →ₗ[ℂ] W), Function.Surjective f → (∀ g v, f (ρ g v) = σ g (f v)) →
    twKer σ N θ = (twKer ρ N θ).map f :=
  fun ρ σ N θ f hf hint => GlobalTheory.CompanionTheory.PRep.twKer_eq_map_of_surjective ρ σ N θ f hf hint

end GlobalTheory.CompanionTheory.PRep
end

section

noncomputable section

open GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.FineProd

variable {k : Type} [Field k]

def dropHom {r r' : ℕ} (d : Fin r → ℕ) (o : Fin r' → Fin r) :
    Levi k (fun j => Fin (d j)) →* Levi k (fun a => Fin (d (o a))) where
  toFun g a := g (o a)
  map_one' := rfl
  map_mul' _ _ := rfl

end GlobalTheory.CompanionTheory.FineProd

end
end

section

open Finset GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId

theorem score_tZero_level : ∀ {n : ℕ} (lev : Fin n → ℕ), Monotone lev → ∀ a : Fin n,
    score (tZero lev) a = ((univ.filter fun b => lev a < lev b).card : ℤ)
      - ((univ.filter fun b => lev b < lev a).card : ℤ) + ((a : ℕ) : ℤ) := by
  intro n lev hm a
  have hlt : ∀ b, lev a < lev b → a < b := fun b h => by
    by_contra hc
    exact absurd (hm (not_lt.mp hc)) (not_le.mpr h)
  have h1 : ((tZero lev).filter fun p => p.1 = a).card
      = (univ.filter fun b => lev a < lev b).card := by
    symm
    refine Finset.card_bij (fun b _ => (a, b)) ?_ ?_ ?_
    · intro b hb
      have hb' : lev a < lev b := (Finset.mem_filter.mp hb).2
      simp [tZero, prs, hb', hlt b hb']
    · intro b _ c _ h
      exact (Prod.ext_iff.mp h).2
    · rintro ⟨x, b⟩ hp
      simp only [tZero, prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨⟨_, h⟩, rfl⟩ := hp
      exact ⟨b, by simp [h], rfl⟩
  have h2 : (((prs n) \ tZero lev).filter fun p => p.2 = a).card
      = (univ.filter fun b => b < a ∧ lev b = lev a).card := by
    symm
    refine Finset.card_bij (fun b _ => (b, a)) ?_ ?_ ?_
    · intro b hb
      have hb' := (Finset.mem_filter.mp hb).2
      simp [tZero, prs, hb'.1, hb'.2]
    · intro b _ c _ h
      exact (Prod.ext_iff.mp h).1
    · rintro ⟨b, x⟩ hp
      simp only [tZero, prs, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, not_and,
        not_lt] at hp
      obtain ⟨⟨h, h'⟩, rfl⟩ := hp
      exact ⟨b, by simp [h, le_antisymm (hm h.le) (h' h)], rfl⟩
  have h3 : (univ.filter fun b : Fin n => b < a).card = (a : ℕ) := by
    simpa [Finset.filter_gt_eq_Iio] using Fin.card_Iio a
  have h4 : (univ.filter fun b => lev b < lev a).card
      + (univ.filter fun b => b < a ∧ lev b = lev a).card = (a : ℕ) := by
    rw [← h3, ← Finset.card_filter_add_card_filter_not (s := univ.filter fun b : Fin n => b < a)
      (fun b => lev b < lev a)]
    congr 2
    · ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        refine ⟨?_, h⟩
        by_contra hc
        exact absurd (hm (not_lt.mp hc)) (not_le.mpr h)
      · exact fun h => h.2
    · ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h, h'⟩
        exact ⟨h, fun hc => absurd h' (ne_of_lt hc)⟩
      · rintro ⟨h, h'⟩
        exact ⟨h, le_antisymm (hm h.le) (not_lt.mp h')⟩
  unfold score
  rw [h1, h2]
  have h4' : ((univ.filter fun b => lev b < lev a).card : ℤ)
      + ((univ.filter fun b => b < a ∧ lev b = lev a).card : ℤ) = ((a : ℕ) : ℤ) := by
    exact_mod_cast h4
  linarith

end GlobalTheory.CompanionTheory.CoefId
end

section

open Finset GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId

theorem prod_pairs_add_eq_sum_score {n : ℕ} (z : Fin n → ℂ) :
    ∏ p ∈ prs n, (z p.1 + z p.2) = ∑ T ∈ (prs n).powerset, ∏ a, z a ^ score T a := by
  have h1 : ∀ (S : Finset (Fin n × Fin n)) (f : Fin n × Fin n → Fin n),
      ∏ p ∈ S, z (f p) = ∏ a, z a ^ (S.filter fun p => f p = a).card := by
    intro S f
    rw [← Finset.prod_fiberwise_of_maps_to (g := f) (t := univ) (fun _ _ => mem_univ _)]
    refine prod_congr rfl fun a _ => ?_
    rw [prod_congr rfl (fun p hp => by rw [(mem_filter.1 hp).2]), prod_const]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [h1 T Prod.fst, h1 (prs n \ T) Prod.snd, ← prod_mul_distrib]
  refine prod_congr rfl fun a _ => ?_
  have : score T a = (((T.filter fun p => p.1 = a).card + ((prs n \ T).filter fun p => p.2 = a).card : ℕ) : ℤ) := by
    simp [score]
  rw [this, zpow_natCast, pow_add]

end GlobalTheory.CompanionTheory.CoefId
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

open MeasureTheory Matrix

theorem detW_eq_normSq_det_one_add_I_smul :
    ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian →
      detW b = Complex.normSq (Matrix.det (1 + Complex.I • b)) := by
  intro n b hb
  unfold detW
  have h1 : (1 + b * b : Matrix (Fin n) (Fin n) ℂ) = (1 + Complex.I • b) * (1 + Complex.I • b)ᴴ := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hb.eq,
      Complex.star_def, Complex.conj_I]
    simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_neg,
      Complex.I_mul_I, one_smul, neg_smul]
    abel
  rw [h1, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end
