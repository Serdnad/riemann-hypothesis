module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle264
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle292
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem disc_eq_trivV (N : ℕ) (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)) : V = trivV N (disc.obj F) := by
  ext n U x
  have h := congrArg
    (fun φ : (disc.obj F).obj (op (SimplexCategory.mk 0)) ⟶ (ofCat (glCat N)).obj n =>
      ConcreteCategory.hom (φ.app U) x)
    (V.naturality (SimplexCategory.const n.unop (SimplexCategory.mk 0) 0).op)
  simp at h
  show (ConcreteCategory.hom ((V.app n).app U)) x = _
  rw [h]
  generalize (ConcreteCategory.hom ((V.app (op (SimplexCategory.mk 0))).app U)) x = y
  refine CategoryTheory.Functor.ext (fun i => rfl) ?_
  intro i j f
  change (y : Fin 1 ⥤ (glCat N).obj (Scheme.Γ.obj U)).map (𝟙 (0 : Fin 1)) = _
  refine (CategoryTheory.Functor.map_id (y : Fin 1 ⥤ (glCat N).obj (Scheme.Γ.obj U)) 0).trans ?_
  change 𝟙 (SingleObj.star (GL (Fin N) (Scheme.Γ.obj U))) =
    eqToHom (rfl : SingleObj.star (GL (Fin N) (Scheme.Γ.obj U)) = _) ≫
      𝟙 (SingleObj.star (GL (Fin N) (Scheme.Γ.obj U))) ≫ eqToHom rfl
  erw [Category.id_comp, Category.id_comp]
  exact (eqToHom_refl _ _).symm

end GlobalTheory.EtC
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

def invP (q : ℕ) : PSh where
  obj U := PLift (IsUnit (q : Γ(U.unop, ⊤)))
  map f := TypeCat.ofHom fun h => ⟨by simpa using h.down.map f.unop.appTop.hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def fibQ (q N : ℕ) : Spc := pullback (trivV N (disc.obj (invP q))) (PGL.pr N)

def lineQ (q N : ℕ) : fibQ q N ⟶ ofCat (glCat 1) := pullback.snd _ _ ≫ PGL.line N

variable (R : Type) [CommRing R]

def cotPre (q N : ℕ) (I : Cx R) (n : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of (ULift.{1} R) (Cochain ((chains R).obj (sch.obj U.unop ⨯ fibQ q N)) I n)
  map f := ModuleCat.ofHom
    { toFun := fun α => (Cochain.ofHom ((chains R).map (prod.map (sch.map f.unop) (𝟙 (fibQ q N))))).comp α (zero_add n)
      map_add' := fun α β => Cochain.comp_add _ _ _ _
      map_smul' := fun r α => Cochain.comp_smul _ _ _ _ }
  map_id U := by
    ext α : 2
    simp
  map_comp f g := by
    ext α : 2
    change (Cochain.ofHom ((chains R).map (prod.map (sch.map (g.unop ≫ f.unop)) (𝟙 (fibQ q N))))).comp α (zero_add n) =
      (Cochain.ofHom ((chains R).map (prod.map (sch.map g.unop) (𝟙 (fibQ q N))))).comp
        ((Cochain.ofHom ((chains R).map (prod.map (sch.map f.unop) (𝟙 (fibQ q N))))).comp α (zero_add n)) (zero_add n)
    rw [show prod.map (sch.map (g.unop ≫ f.unop)) (𝟙 (fibQ q N)) =
      prod.map (sch.map g.unop) (𝟙 (fibQ q N)) ≫ prod.map (sch.map f.unop) (𝟙 (fibQ q N)) by simp,
      Functor.map_comp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

def cotD (q N : ℕ) (I : Cx R) (n : ℤ) : cotPre R q N I n ⟶ cotPre R q N I (n + 1) where
  app U := ModuleCat.ofHom
    { toFun := fun α => δ n (n + 1) α
      map_add' := fun α β => δ_add _ _ _ _
      map_smul' := fun r α => δ_smul _ _ _ _ }
  naturality U U' f := by
    ext α : 2
    revert α
    intro (α : Cochain ((chains R).obj (sch.obj U.unop ⨯ fibQ q N)) I n)
    change δ n (n + 1) ((Cochain.ofHom ((chains R).map (prod.map (sch.map f.unop) (𝟙 (fibQ q N))))).comp α (zero_add n)) =
      (Cochain.ofHom ((chains R).map (prod.map (sch.map f.unop) (𝟙 (fibQ q N))))).comp (δ n (n + 1) α) (zero_add (n + 1))
    rw [δ_zero_cochain_comp _ _ _ rfl, δ_ofHom, Cochain.zero_comp, smul_zero, add_zero]

theorem cotD_comp (q N : ℕ) (I : Cx R) (n : ℤ) : cotD R q N I n ≫ cotD R q N I (n + 1) = 0 := by
  ext U : 2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  change δ (n + 1) (n + 1 + 1) (δ n (n + 1) α) = 0
  exact δ_δ _ _ _ _

def Jcx (q N : ℕ) (I : Cx R) : Cx R :=
  CochainComplex.of (fun n => (presheafToSheaf Scheme.etaleTopology.{0} _).obj (cotPre R q N I n))
    (fun n => (presheafToSheaf Scheme.etaleTopology.{0} _).map (cotD R q N I n))
    (fun n => by rw [← Functor.map_comp, cotD_comp, Functor.map_zero])

variable {R}

def Jsec {q N : ℕ} {I : Cx R} {n : ℤ} {U : Scheme.{0}} (c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) :
    Sec ((Jcx R q N I).X n) U :=
  ((toSheafify Scheme.etaleTopology.{0} (cotPre R q N I n)).app (op U)).hom c

def twCast {q : ℕ} {i i' : ℤ} (h : i = i') {s : ℤ} {V : Scheme.{0}} (x : Sec ((res (ZMod q) (tw q i)).X s) V) :
    Sec ((res (ZMod q) (tw q i')).X s) V := h ▸ x

end GlobalTheory.EtC

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped ENNReal Classical

namespace GlobalTheory.WeilL2Words

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def arch1 (z : mixedEmbedding.mixedSpace F) : AdeleRing (𝓞 F) F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z, 0)

def IsStdInf (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : Prop :=
  ∃ ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ, (∀ z : mixedEmbedding.mixedSpace F, z ≠ 0 → ∃ u, ℓ (z * u) ≠ 0) ∧
    ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)

def arch (x : κ → mixedEmbedding.mixedSpace F) : κ → AdeleRing (𝓞 F) F := fun i => arch1 F (x i)

def archPair (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) :=
  (arch F h.1, arch F h.2)

def archPart (a : κ → AdeleRing (𝓞 F) F) : κ → mixedEmbedding.mixedSpace F :=
  fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1

def l2A (μ : @Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) : ℝ≥0∞ :=
  @lintegral _ (borel _) μ fun y => ∫⁻ x, ‖Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2

variable [Invertible (2 : AdeleRing (𝓞 F) F)]

def dS (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) : (κ → AdeleRing (𝓞 F) F) → ℂ :=
  fun a => deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) Φ a) 0

def word (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hs : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) : (κ → AdeleRing (𝓞 F) F) → ℂ :=
  hs.foldr (fun h g => dS F ψ h g) Φ

theorem word_cons (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (h) (hs) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    word F ψ (h :: hs) Φ = dS F ψ h (word F ψ hs Φ) := rfl

end GlobalTheory.WeilL2Words

end
end

section

noncomputable section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.LocMatrix

theorem tmul_smul_eq_cenMap_mul {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℚ_[ℓ]) (c : F) (v : B) :
    q ⊗ₜ[ℚ] (c • v) = cenMap ℓ F B (q ⊗ₜ c) * ((1 : ℚ_[ℓ]) ⊗ₜ v) := by
  rw [cenMap_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def]

def combMap {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (ℓ : ℕ) [Fact ℓ.Prime] {d : ℕ} (v : Fin d → B) :
    (Fin d → ℚ_[ℓ] ⊗[ℚ] F) →ₗ[ℚ_[ℓ]] ℚ_[ℓ] ⊗[ℚ] B where
  toFun c := ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ v i)
  map_add' c c' := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.smul_sum, smul_mul_assoc]

theorem combMap_apply {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (ℓ : ℕ) [Fact ℓ.Prime] {d : ℕ} (v : Fin d → B)
    (c : Fin d → ℚ_[ℓ] ⊗[ℚ] F) :
    combMap ℓ v c = ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ v i) := rfl

theorem combMap_surjective {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (ℓ : ℕ) [Fact ℓ.Prime] {d : ℕ} (v : Module.Basis (Fin d) F B) :
    Function.Surjective (combMap (F := F) ℓ v) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul q b =>
    rw [← v.sum_repr b, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun i _ => ⟨Pi.single i (q ⊗ₜ[ℚ] v.repr b i), ?_⟩
    rw [combMap_apply, Finset.sum_eq_single i
      (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]) (by simp),
      Pi.single_eq_same, ← tmul_smul_eq_cenMap_mul]
  | add x y hx hy => exact add_mem hx hy

theorem combMap_injective {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] [FiniteDimensional F B] (ℓ : ℕ) [Fact ℓ.Prime] {d : ℕ}
    (v : Module.Basis (Fin d) F B) : Function.Injective (combMap (F := F) ℓ v) := by
  haveI : FiniteDimensional ℚ B := Module.Finite.trans F B
  have hdim : Module.finrank ℚ_[ℓ] (Fin d → ℚ_[ℓ] ⊗[ℚ] F) = Module.finrank ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] B) := by
    rw [Module.finrank_pi_fintype, Module.finrank_baseChange, Module.finrank_baseChange,
      ← Module.finrank_mul_finrank ℚ F B, Module.finrank_eq_card_basis v]
    simp [mul_comm]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 (combMap_surjective ℓ v)

end GlobalTheory.LocMatrix

namespace GlobalTheory.LocMatrix

theorem exists_basis_mem {F B : Type} [Field F] [CharZero F] [Ring B] [Algebra F B] [FiniteDimensional F B]
    (Λ : Subring B) (hspan : ∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) :
    ∃ v : Module.Basis (Fin (Module.finrank F B)) F B, ∀ i, v i ∈ Λ := by
  let e := Module.finBasis F B
  choose m hm hmΛ using hspan
  let u : Fin (Module.finrank F B) → Fˣ := fun i =>
    Units.mk0 (m (e i) : F) (Nat.cast_ne_zero.2 (hm (e i)).ne')
  refine ⟨e.unitsSMul u, fun i => ?_⟩
  rw [Module.Basis.unitsSMul_apply, Units.smul_def]
  have h : (u i : F) • e i = (m (e i) : B) * e i := by
    simp [u, Algebra.smul_def]
  rw [h]
  exact hmΛ _

theorem exists_den {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    (Λ : Subring B) (hfin : Module.Finite ℤ Λ) {ι : Type} [Fintype ι] (v : Module.Basis ι F B) :
    ∃ D : ℕ, 0 < D ∧ ∀ x ∈ Λ, ∀ i, IsIntegral ℤ ((D : F) * v.repr x i) := by
  classical
  obtain ⟨s, hs⟩ := hfin.fg_top
  obtain ⟨D, hD, hDs⟩ := GlobalTheory.SepModel.exists_nat_integral
    (Finset.univ.image fun p : s × ι => v.repr ((p.1 : Λ) : B) p.2)
  refine ⟨D, hD, fun x hx => ?_⟩
  let P : Submodule ℤ Λ :=
    { carrier := {y | ∀ i, IsIntegral ℤ ((D : F) * v.repr (y : B) i)}
      add_mem' := by
        intro y z hy hz i
        simp only [Set.mem_setOf_eq, Subring.coe_add, map_add (f := _), Finsupp.add_apply, mul_add] at hy hz ⊢
        exact (hy i).add (hz i)
      zero_mem' := by
        intro i
        simp
        exact isIntegral_zero
      smul_mem' := by
        intro c y hy i
        simp only [Set.mem_setOf_eq] at hy ⊢
        have h2 : v.repr ((c • y : Λ) : B) i = (c : F) * v.repr (y : B) i := by
          rw [show ((c • y : Λ) : B) = c • (y : B) from rfl, map_zsmul, Finsupp.smul_apply,
            zsmul_eq_mul]
        have hc : IsIntegral ℤ (c : F) := by
          simpa using (isIntegral_algebraMap (R := ℤ) (A := F) (x := c))
        rw [h2, mul_left_comm]
        exact hc.mul (hy i) }
  have hsP : (s : Set Λ) ⊆ P := fun y hy i =>
    hDs _ (Finset.mem_image.2 ⟨(⟨y, hy⟩, i), Finset.mem_univ _, rfl⟩)
  have hmem : (⟨x, hx⟩ : Λ) ∈ P := by
    have h := Submodule.span_le.mpr hsP
    rw [hs] at h
    exact h Submodule.mem_top
  exact hmem

end GlobalTheory.LocMatrix

namespace GlobalTheory.LocMatrix

theorem exists_coeffs {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (ℓ : ℕ) [Fact ℓ.Prime] (Λ : Subring B) {d : ℕ}
    (v : Module.Basis (Fin d) F B) (D : ℕ)
    (hD : ∀ x ∈ Λ, ∀ i, IsIntegral ℤ ((D : F) * v.repr x i)) (hℓ : ¬ ℓ ∣ D)
    (z : ℚ_[ℓ] ⊗[ℚ] B) (hz : z ∈ locOrder ℓ Λ) :
    ∃ c : Fin d → cenOrder ℓ F, z = ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ v i) := by
  let S : Submodule ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] B) :=
    { carrier := {z | ∃ c : Fin d → cenOrder ℓ F, z = ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ v i)}
      add_mem' := by
        rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
        exact ⟨c + c', by simp [add_mul, Finset.sum_add_distrib]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r _ ⟨c, rfl⟩
        refine ⟨r • c, ?_⟩
        simp only [Pi.smul_apply, Subalgebra.coe_smul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← algebraMap_smul ℚ_[ℓ] r ((c i : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F), map_smul, smul_mul_assoc,
          algebraMap_smul] }
  have gen : ∀ x ∈ Λ, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] x ∈ S := by
    intro x hx
    refine ⟨fun i => ⟨_, GlobalTheory.SepModel.tmul_mem_cenOrder ℓ hℓ (hD x hx i)⟩, ?_⟩
    conv_lhs => rw [← v.sum_repr x, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact tmul_smul_eq_cenMap_mul ℓ 1 _ _
  have hz' : z ∈ Subalgebra.toSubmodule (locOrder ℓ Λ) := hz
  rw [locOrder, Algebra.adjoin_eq_span] at hz'
  have hcl : (Submonoid.closure ((fun b : B => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b) '' (Λ : Set B)) :
      Set (ℚ_[ℓ] ⊗[ℚ] B)) ⊆ S := by
    intro y hy
    have hy' : y ∈ Λ.toSubmonoid.map
        (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] B) := by
      refine (Submonoid.closure_le.2 ?_) hy
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hy'
    exact gen x hx
  exact Submodule.span_le.2 hcl hz'

theorem locOrder_free : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [FiniteDimensional F B] (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ),
    Module.Finite ℤ Λ → (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ;
      Module.Free (cenOrder ℓ F) (locOrder ℓ Λ) ∧
        Module.finrank (cenOrder ℓ F) (locOrder ℓ Λ) = Module.finrank F B := by
  intro F B _ _ _ _ _ _ _ Λ hΛ hfin hspan
  obtain ⟨v, hvΛ⟩ := exists_basis_mem (F := F) Λ hspan
  obtain ⟨D, hD, hDΛ⟩ := exists_den Λ hfin v
  refine ⟨D, hD, fun ℓ _ hℓ => ?_⟩
  letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
  let w : Fin (Module.finrank F B) → locOrder ℓ Λ := fun i =>
    ⟨(1 : ℚ_[ℓ]) ⊗ₜ v i, Algebra.subset_adjoin ⟨_, hvΛ i, rfl⟩⟩
  have hsmul : ∀ (c : cenOrder ℓ F) (x : locOrder ℓ Λ),
      ((c • x : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = cenMap ℓ F B c * x := fun c x => rfl
  have hsum : ∀ c : Fin (Module.finrank F B) → cenOrder ℓ F,
      ((∑ i, c i • w i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) =
        combMap (F := F) ℓ v (fun i => (c i : ℚ_[ℓ] ⊗[ℚ] F)) := by
    intro c
    rw [AddSubmonoidClass.coe_finsetSum, combMap_apply]
    exact Finset.sum_congr rfl fun i _ => hsmul _ _
  have hli : LinearIndependent (cenOrder ℓ F) w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 : combMap (F := F) ℓ v (fun i => (g i : ℚ_[ℓ] ⊗[ℚ] F)) = combMap (F := F) ℓ v 0 := by
      rw [← hsum, hg, map_zero]
      rfl
    exact Subtype.ext (congrFun (combMap_injective ℓ v h0) i)
  have hsp : ⊤ ≤ Submodule.span (cenOrder ℓ F) (Set.range w) := by
    rintro ⟨z, hz⟩ -
    obtain ⟨c, hc⟩ := exists_coeffs ℓ Λ v D hDΛ hℓ z hz
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨c, Subtype.ext ((hsum c).trans hc.symm)⟩
  haveI : Nontrivial (ℚ_[ℓ] ⊗[ℚ] F) := by
    apply Module.nontrivial_of_finrank_pos (R := ℚ_[ℓ])
    rw [Module.finrank_baseChange]
    exact Module.finrank_pos
  let bas := Module.Basis.mk hli hsp
  exact ⟨Module.Free.of_basis bas, by rw [Module.finrank_eq_card_basis bas, Fintype.card_fin]⟩

end GlobalTheory.LocMatrix
end
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.LocAcyc

theorem isZModTorsor_baseChange : ∀ (B B' D : Type) [CommRing B] [CommRing B'] [CommRing D]
    [Algebra B B'] [Algebra B D]
    (q : ℕ), 0 < q → ∀ (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.LocAcyc.IsZModTorsor B D q act →
    ∃ act' : Multiplicative (ZMod q) →* ((B' ⊗[B] D) ≃ₐ[B'] (B' ⊗[B] D)),
      (∀ (g : Multiplicative (ZMod q)) (b : B') (x : D), act' g (b ⊗ₜ[B] x) = b ⊗ₜ[B] act g x) ∧
      GlobalTheory.LocAcyc.IsZModTorsor B' (B' ⊗[B] D) q act' := by
  intro B B' D _ _ _ _ _ q hq act hD
  obtain ⟨h1, h2, h3, h4⟩ := hD
  haveI : NeZero q := ⟨hq.ne'⟩
  let act' : Multiplicative (ZMod q) →* ((B' ⊗[B] D) ≃ₐ[B'] (B' ⊗[B] D)) :=
    { toFun := fun g => Algebra.TensorProduct.congr (AlgEquiv.refl : B' ≃ₐ[B'] B') (act g)
      map_one' := by
        apply AlgEquiv.ext; intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b x => simp [Algebra.TensorProduct.congr_apply]
        | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      map_mul' := by
        intro g h
        apply AlgEquiv.ext; intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b x => simp [Algebra.TensorProduct.congr_apply, AlgEquiv.mul_apply]
        | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy] }
  have hact : ∀ (g : Multiplicative (ZMod q)) (b : B') (x : D),
      act' g (b ⊗ₜ[B] x) = b ⊗ₜ[B] act g x := by
    intro g b x
    simp [act', Algebra.TensorProduct.congr_apply]
  refine ⟨act', hact, inferInstance, inferInstance, inferInstance, ?_⟩
  let Φ := Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))
  let e := (LinearEquiv.ofBijective Φ.toLinearMap h4).lTensor B'
  let dBC := TensorProduct.AlgebraTensorModule.distribBaseChange B B' D D
  let pR := TensorProduct.piRight B B' B' (fun _ : Multiplicative (ZMod q) => D)
  have key : ∀ z, (Algebra.TensorProduct.productMap
      (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => B' ⊗[B] D) (fun _ => AlgHom.id B' _))
      (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => B' ⊗[B] D) (fun g => (act' g).toAlgHom)))
      (dBC z) = pR (e z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b t =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        funext g
        simp [dBC, pR, e, Φ, TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
          Algebra.TensorProduct.productMap_apply_tmul, hact, Algebra.TensorProduct.tmul_mul_tmul,
          LinearEquiv.ofBijective_apply]
        rfl
      | add s t hs ht => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hs, ht]
    | add s t hs ht => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hs, ht]
  have hfun : ⇑(Algebra.TensorProduct.productMap
      (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => B' ⊗[B] D) (fun _ => AlgHom.id B' _))
      (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => B' ⊗[B] D) (fun g => (act' g).toAlgHom)))
      = fun w => pR (e (dBC.symm w)) := by
    funext w
    rw [← key, dBC.apply_symm_apply]
  rw [hfun]
  exact pR.bijective.comp (e.bijective.comp dBC.symm.bijective)

end GlobalTheory.LocAcyc
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.eq_zero_of_upwardFamily_standardCover : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (t : C') (Sg : ∀ t', (t ⟶ t') → Prop), (∀ t' t'' (a : t ⟶ t') (b : t' ⟶ t''), Sg t' a → Sg t'' (a ≫ b)) → Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), Sg t' a ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) → Desc.Sep (G ⋙ F) Sg := by
  first | exact @GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.sep_of_covBy | exact GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.sep_of_covBy | (intros; apply GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.sep_of_covBy <;> assumption)
end
