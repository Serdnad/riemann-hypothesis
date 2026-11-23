module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle001
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbitt
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

@[expose] public section

section

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

section
variable {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R]
  [Algebra O R] (n : ℕ)

private theorem star_add' (y z : MonoidAlgebra R F.G₀) :
    F.star O R n (y + z) = F.star O R n y + F.star O R n z := by
  simp [GFrame.star]

private theorem star_zero' : F.star O R n 0 = 0 := by
  simp [GFrame.star]

end

private theorem star_single_eq_single_conj_inv_mul_eps_zpow {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) (r : R) :
    F.star O R n (MonoidAlgebra.single g r) =
      MonoidAlgebra.single (F.conj g)⁻¹ (r * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]

private theorem conjO_conjO_unimodular_class_representatives {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) : F.conj (F.conj g) = g := by
  have hc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right F.c_sq
  apply Subtype.ext
  simp [GFrame.conj, hc, ← mul_assoc, F.c_sq]
  rw [mul_assoc, F.c_sq, mul_one]

private theorem eps_conj' {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (g : F.G₀) : F.eps O R (F.conj g) = F.eps O R g := by
  simp [GFrame.eps, GFrame.conj]

private theorem algHom_eps_zpow_eq {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (R' : Type) [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R')
    (g : F.G₀) (k : ℤ) :
    f ((F.eps O R g ^ k : Rˣ) : R) = ((F.eps O R' g ^ k : R'ˣ) : R') := by
  have h : Units.map (f : R →* R') (F.eps O R g) = F.eps O R' g := by
    ext
    simp [GFrame.eps, pushCh]
  rw [← h, ← map_zpow (Units.map (f : R →* R')), Units.coe_map]
  rfl

theorem UpperTheory.V.AlgebraTools.Det.starApi :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ),
    (∀ y z, F.star O R n (y * z) = F.star O R n z * F.star O R n y) ∧ F.star O R n 1 = 1 ∧
    (∀ y z, F.star O R n (y + z) = F.star O R n y + F.star O R n z) ∧ (∀ (a : R) y, F.star O R n (a • y) = a • F.star O R n y) ∧
    (∀ y, F.star O R n (F.star O R n y) = y) ∧
    ∀ (R' : Type) [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R') (y : MonoidAlgebra R F.G₀),
      F.star O R' n (MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') y) = MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (F.star O R n y) := by
  intro l _ F O _ _ R _ _ n
  refine ⟨?_, ?_, star_add' F O R n, ?_, ?_, ?_⟩
  · intro y z
    simp only [GFrame.star, map_mul, MulOpposite.unop_mul]
  · simp [GFrame.star, map_one]
  · intro a y
    simp only [GFrame.star, map_smul, MulOpposite.unop_smul]
  · intro y
    induction y using MonoidAlgebra.induction_linear
    next => simp [star_zero']
    next y z hy hz => rw [star_add', star_add', hy, hz]
    next g r =>
      simp only [star_single_eq_single_conj_inv_mul_eps_zpow, map_inv, inv_inv, conjO_conjO_unimodular_class_representatives, eps_conj', _root_.inv_zpow]
      rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  · intro R' _ _ f y
    induction y using MonoidAlgebra.induction_linear
    next => simp [star_zero']
    next y z hy hz => rw [map_add (f := _), star_add', star_add', map_add (f := _), hy, hz]
    next g r =>
      simp only [star_single_eq_single_conj_inv_mul_eps_zpow, MonoidAlgebra.mapRingHom_single, RingHom.coe_coe, map_mul]
      rw [algHom_eps_zpow_eq]
end

section

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

private theorem star_mapRingHom_algHom_eq {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (B B' : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] [CommRing B'] [Algebra R B'] [Algebra O B'] [IsScalarTower O R B'] (f : B →ₐ[R] B') (x : MonoidAlgebra B F.G₀) : F.star O B' n (MonoidAlgebra.mapRingHom F.G₀ (f : B →+* B') x) = MonoidAlgebra.mapRingHom F.G₀ (f : B →+* B') (F.star O B n x) := by
  have he : ∀ g : F.G₀, Units.map (f : B →* B') (F.eps O B g) = F.eps O B' g := by
    intro g
    ext
    simp [GFrame.eps, pushCh, IsScalarTower.algebraMap_apply O R B, IsScalarTower.algebraMap_apply O R B']
  have hs : ∀ (C : Type) [CommRing C] [Algebra O C] (g : F.G₀) (b : C), F.star O C n (MonoidAlgebra.single g b) = MonoidAlgebra.single (F.conj g)⁻¹ (b * ↑(F.eps O C g ^ (1 - (n:ℤ)))) := by
    intro C _ _ g b
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, MonoidAlgebra.smul_single']
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp [GFrame.star]
  | add x y hx hy => simp only [map_add (f := _)] at hx hy ⊢; simp [GFrame.star, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
  | single g b =>
    rw [MonoidAlgebra.mapRingHom_single, hs, hs, MonoidAlgebra.mapRingHom_single, map_mul, ← he g, ← map_zpow]
    rfl

theorem UpperTheory.V.AlgebraTools.Det.starDet :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (D : GDet n R F.G₀), ∃ D' : GDet n R F.G₀,
    ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀), D'.D B y = D.D B (F.star O B n y) := by
  intro l _ F O _ _ R _ _ n D
  let E : ∀ (B : Type) [CommRing B] [Algebra R B], MonoidAlgebra B F.G₀ →* B := fun B _ _ =>
    letI : Algebra O B := ((algebraMap R B).comp (algebraMap O R)).toAlgebra
    { toFun := fun y => D.D B (F.star O B n y)
      map_one' := by simp [GFrame.star]
      map_mul' := fun x y => by
        have hm : F.star O B n (x * y) = F.star O B n y * F.star O B n x := by simp [GFrame.star, map_mul]
        simp only [hm, map_mul, mul_comm] }
  have hE : ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀), E B y = D.D B (F.star O B n y) := by
    intro B _ _ iO _ y
    have hi : ((algebraMap R B).comp (algebraMap O R)).toAlgebra = iO :=
      Algebra.algebra_ext _ _ (fun r => (IsScalarTower.algebraMap_apply O R B r).symm)
    subst hi
    rfl
  refine ⟨{ D := E, nat := ?_, homog := ?_ }, fun B _ _ _ _ y => hE B y⟩
  · intro B B' _ _ _ _ f x
    letI : Algebra O B := ((algebraMap R B).comp (algebraMap O R)).toAlgebra
    haveI : IsScalarTower O R B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI : Algebra O B' := ((algebraMap R B').comp (algebraMap O R)).toAlgebra
    haveI : IsScalarTower O R B' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    rw [hE B', hE B, star_mapRingHom_algHom_eq F O R n B B' f x, D.nat]
  · intro B _ _ b x
    letI : Algebra O B := ((algebraMap R B).comp (algebraMap O R)).toAlgebra
    haveI : IsScalarTower O R B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hsm : F.star O B n (b • x) = b • F.star O B n x := by simp [GFrame.star, map_smul]
    rw [hE B, hE B, hsm, D.homog]
end

section

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.flagRel :
    ∀ {k H : Type} [CommRing k] [Group H] {n : ℕ} (r : H →* GL (Fin n) k) (κ : Fin n → H →* kˣ), HasFlag r κ →
    (∀ s, (mat r s).charpoly = ∏ j, (X - C (κ j s : k))) ∧
    ∀ g : Fin n → H, (List.ofFn fun j => mat r (g j) - (κ j (g j) : k) • (1 : Matrix (Fin n) (Fin n) k)).prod = 0 := by
  intro k H _ _ n r κ ⟨P, hP⟩
  have hm : ∀ s, mat r s = (r s : Matrix (Fin n) (Fin n) k) := fun _ => rfl
  constructor
  · intro s
    have h1 : ((P * r s * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly = (mat r s).charpoly := by
      rw [hm, Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]
    have h2 : ((P * r s * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
      fun i j hij => (hP s).1 i j hij
    rw [← h1, Matrix.charpoly_of_upperTriangular _ h2]
    exact Finset.prod_congr rfl fun i _ => by rw [← (hP s).2 i]
  · intro g
    let W : ℕ → Submodule k (Fin n → k) := fun j =>
      { carrier := {v | ∀ i : Fin n, j ≤ i.val → ((P : Matrix (Fin n) (Fin n) k) *ᵥ v) i = 0}
        add_mem' := fun {a b} ha hb i hi => by
          rw [Matrix.mulVec_add, Pi.add_apply, ha i hi, hb i hi, add_zero]
        zero_mem' := fun i _ => by simp
        smul_mem' := fun c a ha i hi => by
          rw [Matrix.mulVec_smul, Pi.smul_apply, ha i hi, smul_zero] }
    have hW : ∀ j v, v ∈ W j ↔ ∀ i : Fin n, j ≤ i.val → ((P : Matrix (Fin n) (Fin n) k) *ᵥ v) i = 0 :=
      fun _ _ => Iff.rfl
    have key := UpperTheory.V.AlgebraTools.Det.flagKill n W
      (fun j => Matrix.toLinAlgEquiv' (mat r (g j) - (κ j (g j) : k) • (1 : Matrix (Fin n) (Fin n) k))) ?_ ?_ ?_
    · apply (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).injective
      rw [map_list_prod, map_zero, List.map_ofFn]
      exact key
    · rw [eq_bot_iff]
      intro v hv
      have h0 : (P : Matrix (Fin n) (Fin n) k) *ᵥ v = 0 := funext fun i => (hW 0 v).1 hv i (Nat.zero_le _)
      have : v = ((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ ((P : Matrix (Fin n) (Fin n) k) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [Submodule.mem_bot, this, h0, Matrix.mulVec_zero]
    · rw [eq_top_iff]
      intro v _
      exact (hW n v).2 fun i hi => absurd i.2 (not_lt.2 hi)
    · intro j v hv
      rw [hW] at hv ⊢
      intro i hi
      have e : (P : Matrix (Fin n) (Fin n) k) *ᵥ
          (Matrix.toLinAlgEquiv' (mat r (g j) - (κ j (g j) : k) • (1 : Matrix (Fin n) (Fin n) k)) v) =
          ((P * r (g j) * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ ((P : Matrix (Fin n) (Fin n) k) *ᵥ v)
            - (κ j (g j) : k) • ((P : Matrix (Fin n) (Fin n) k) *ᵥ v) := by
        rw [Matrix.toLinAlgEquiv'_apply, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
          Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm, Units.val_mul, Units.val_mul,
          Units.inv_mul_cancel_right]
      rw [e, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_zero]
      generalize (P : Matrix (Fin n) (Fin n) k) *ᵥ v = w at hv ⊢
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
      · rcases eq_or_lt_of_le hi with h | h
        · have : j = i := Fin.ext h
          subst this
          rw [← (hP (g j)).2 j]
        · rw [hv i h, mul_zero, mul_zero]
      · intro b _ hb
        rcases lt_or_gt_of_ne hb with h | h
        · have := (hP (g j)).1 i b h
          rw [this, zero_mul]
        · rw [hv b (by have : i.val < b.val := h; omega), mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
end

section

open Polynomial Matrix UpperTheory.V.W

private noncomputable def UpperTheory.V.AlgebraTools.Det.bnRep_lin {n : ℕ} {K G : Type} [Field K] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) K) : Representation K G (Fin n → K) where
  toFun g := Matrix.toLin' (ρ g)
  map_one' := by rw [map_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by rw [map_mul, Matrix.toLin'_mul]; rfl

private theorem UpperTheory.V.AlgebraTools.Det.bnRep_ss {n : ℕ} {K G : Type} [Field K] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) K)
    (h : ∀ W : Submodule K (Fin n → K), (∀ g, ∀ v ∈ W, ρ g *ᵥ v ∈ W) →
      ∃ W', (∀ g, ∀ v ∈ W', ρ g *ᵥ v ∈ W') ∧ IsCompl W W') :
    IsSemisimpleModule (MonoidAlgebra K G) (UpperTheory.V.AlgebraTools.Det.bnRep_lin ρ).asModule := by
  rw [← Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine ⟨fun W => ?_⟩
  obtain ⟨W', hW', hc⟩ := h W.toSubmodule (fun g v hv => W.apply_mem_toSubmodule g hv)
  refine ⟨⟨W', fun g v hv => hW' g v hv⟩, ?_, ?_⟩
  · rw [disjoint_iff]
    exact Subrepresentation.toSubmodule_injective hc.inf_eq_bot
  · rw [codisjoint_iff]
    exact Subrepresentation.toSubmodule_injective hc.sup_eq_top

theorem UpperTheory.V.AlgebraTools.Det.bnRep :
    ∀ {n : ℕ} {K G : Type} [Field K] [Group G] (ρ ρ' : G →* Matrix (Fin n) (Fin n) K),
    (∀ W : Submodule K (Fin n → K), (∀ g, ∀ v ∈ W, ρ g *ᵥ v ∈ W) → ∃ W', (∀ g, ∀ v ∈ W', ρ g *ᵥ v ∈ W') ∧ IsCompl W W') →
    (∀ W : Submodule K (Fin n → K), (∀ g, ∀ v ∈ W, ρ' g *ᵥ v ∈ W) → ∃ W', (∀ g, ∀ v ∈ W', ρ' g *ᵥ v ∈ W') ∧ IsCompl W W') →
    (∀ g, (ρ g).charpoly = (ρ' g).charpoly) → ∃ P : GL (Fin n) K, ∀ g, (P : Matrix (Fin n) (Fin n) K) * ρ' g = ρ g * P := by
  intro n K G _ _ ρ ρ' h h' hc
  obtain ⟨e, he⟩ := Formalism.IrreducibleCountingLemmas.Z.brauer_nesbitt K G (Fin n → K) (Fin n → K)
    (UpperTheory.V.AlgebraTools.Det.bnRep_lin ρ') (UpperTheory.V.AlgebraTools.Det.bnRep_lin ρ)
    (UpperTheory.V.AlgebraTools.Det.bnRep_ss ρ' h') (UpperTheory.V.AlgebraTools.Det.bnRep_ss ρ h) (fun g => by
      show (Matrix.toLin' (ρ' g)).charpoly = (Matrix.toLin' (ρ g)).charpoly
      rw [Matrix.charpoly_toLin', Matrix.charpoly_toLin']
      exact (hc g).symm)
  have h1 : LinearMap.toMatrix' (e.symm : (Fin n → K) →ₗ[K] (Fin n → K)) *
      LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  have h2 : LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)) *
      LinearMap.toMatrix' (e.symm : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  refine ⟨⟨_, _, h2, h1⟩, fun g => ?_⟩
  show LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)) * ρ' g =
    ρ g * LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K))
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  exact he g
end
