module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CocycleCrysAddAnn
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsCoefficientFieldOfFiniteLocalPadic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TriCrys
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsEps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle033
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Bundle002

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory

theorem tri_crys_push : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B' : Type} [CommRing B'] [IsLocalRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [TopologicalSpace B'] [IsModuleTopology ℚ_[l] B'] [IsTopologicalRing B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] {B : Type} [CommRing B] [IsLocalRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] (q : B' →ₐ[ℚ_[l]] B) (e : ℕ), 1 ≤ e → ∀ (κ : Fin 3 → G →* B'ˣ), (∀ i, Continuous fun g => (κ i g : B')) → (∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B' (φ g) ^ ((e : ℤ) * wt1 i)) → ∀ (x y z : G → B') (ρ : G →* GL (Fin 3) B'), Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B') = triM (fun i => κ i g) (x g) (y g) (z g)) → x ∈ Z1 (chRep (κ 0 / κ 1)) → y ∈ Z1 (chRep (κ 1 / κ 2)) → ∀ σ : G, ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ → (∀ b, (((κ 0 / κ 1) σ : B'ˣ) - (cycA l l B' (φ σ) : B')) * b = 0 → q b = 0) → (∀ b, (((κ 1 / κ 2) σ : B'ˣ) - (cycA l l B' (φ σ) : B')) * b = 0 → q b = 0) → IsCr φ (colRep ((Matrix.GeneralLinearGroup.map (q : B' →+* B)).comp ρ)) := by
  intro hP l _ G _ _ _ φ hφ B' _ _ _ _ _ _ _ _ _ B _ _ _ _ q e he κ hκ hI x y z ρ hz hρ hx hy σ hσ hqx hqy

  obtain ⟨E', _, _, _, _, _, π', hπ'⟩ := GlobalTheory.exists_coefficientField_of_finite_local_padic (l := l) B'
  obtain ⟨E, _, _, _, _, _, π, hπ⟩ := GlobalTheory.exists_coefficientField_of_finite_local_padic (l := l) B
  letI : Algebra ℤ_[l] E' := ((algebraMap ℚ_[l] E').comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] E' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra ℤ_[l] E := ((algebraMap ℚ_[l] E).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra ℤ_[l] B := ((algebraMap ℚ_[l] B).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B

  have hqc : Continuous (q : B' → B) := IsModuleTopology.continuous_of_linearMap (q.toLinearMap)
  let qm : B' →* B := (q : B' →+* B)
  let κB : Fin 3 → G →* Bˣ := fun i => (Units.map qm).comp (κ i)
  have hqcyc : ∀ h : GQ l, Units.map qm (cycA l l B' h) = cycA l l B h := by
    intro h
    apply Units.ext
    change q (algebraMap ℤ_[l] B' _) = algebraMap ℚ_[l] B (algebraMap ℤ_[l] ℚ_[l] _)
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B', q.commutes]

  have hw01 : ∀ g, φ g ∈ Iq l → (κ 0 / κ 1) g = cycA l l B' (φ g) ^ (e : ℤ) := by
    intro g hg
    rw [MonoidHom.div_apply, hI g hg 0, hI g hg 1]
    simp [wt1]
  have hw12 : ∀ g, φ g ∈ Iq l → (κ 1 / κ 2) g = cycA l l B' (φ g) ^ (e : ℤ) := by
    intro g hg
    rw [MonoidHom.div_apply, hI g hg 1, hI g hg 2]
    simp [wt1]
  have hcdiv : ∀ i j, Continuous fun g => (((κ i / κ j) g : B'ˣ) : B') := by
    intro i j
    have : (fun g => (((κ i / κ j) g : B'ˣ) : B')) = fun g => (κ i g : B') * (κ j g⁻¹ : B') := by
      funext g
      rw [MonoidHom.div_apply, div_eq_mul_inv, Units.val_mul, ← map_inv]
    rw [this]
    exact (hκ i).mul ((hκ j).comp continuous_inv)
  have he : (1 : ℤ) ≤ (e : ℤ) := by exact_mod_cast he

  obtain ⟨cx, hcx, hxf, -⟩ := GlobalTheory.CrysAnn.cocycle_crys_add_ann hP φ hφ π' hπ' (κ 0 / κ 1) (hcdiv 0 1) e he hw01 σ hσ x hx
  obtain ⟨cy, hcy, hyf, -⟩ := GlobalTheory.CrysAnn.cocycle_crys_add_ann hP φ hφ π' hπ' (κ 1 / κ 2) (hcdiv 1 2) e he hw12 σ hσ y hy
  have push : ∀ (i j : Fin 3) (c : G → B'), c ∈ finiteCocycles φ (chRep (κ i / κ j)) →
      (fun g => q (c g)) ∈ finiteCocycles φ (chRep (κB i / κB j)) := by
    intro i j c hc
    refine (z1fMap φ (chRep (κ i / κ j)) (chRep (κB i / κB j))).2 q.toLinearMap (fun g v => ?_) c hc
    show q ((((κ i / κ j) g : B'ˣ) : B') * v) = (((κB i / κB j) g : Bˣ) : B) * q v
    rw [map_mul]
    congr 1
    simp only [κB, MonoidHom.div_apply, MonoidHom.comp_apply, ← _root_.map_div, Units.coe_map]
    rfl
  have hxB : (fun g => q (x g)) ∈ finiteCocycles φ (chRep (κB 0 / κB 1)) := by
    have h := push 0 1 _ hxf
    convert h using 2 with g
    simp [hqx _ (hcx g)]
  have hyB : (fun g => q (y g)) ∈ finiteCocycles φ (chRep (κB 1 / κB 2)) := by
    have h := push 1 2 _ hyf
    convert h using 2 with g
    simp [hqy _ (hcy g)]
  refine GlobalTheory.tri_crys hP φ hφ π hπ e (by exact_mod_cast he) κB (fun i => hqc.comp (hκ i)) ?_ (fun g => q (x g))
    (fun g => q (y g)) (fun g => q (z g)) ((Matrix.GeneralLinearGroup.map (q : B' →+* B)).comp ρ) (hqc.comp hz) ?_ hxB hyB
  · intro g hg i
    simp only [κB, MonoidHom.comp_apply, hI g hg i, map_zpow, hqcyc]
  · intro g
    rw [MonoidHom.comp_apply]
    show (ρ g : Matrix (Fin 3) (Fin 3) B').map q = _
    rw [hρ g]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triM, κB, qm]

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc.DcrOrd

variable {O G : Type} [CommRing O] [Group G]

def Cond (Ψ : G →* Oˣ) (I : Subgroup G) {C : Type} [CommRing C] [Algebra O C] (r : G →* GG (m := 3) (R := C)) : Prop :=
  (∀ s ∈ I, (r s).mat.charpoly = ∏ a, (X - Polynomial.C (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ a s)))) ∧
    ∀ s : Fin 3 → G, (∀ a, s a ∈ I) →
      ((r (s 0)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ 0 (s 0)))) *
        ((r (s 1)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ 1 (s 1)))) *
        ((r (s 2)).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ 2 (s 2)))) = 0

theorem cond_tri (Ψ : G →* Oˣ) (I : Subgroup G) {C : Type} [CommRing C] [Algebra O C] (u : G →* GG (m := 3) (R := C))
    (ht : ∀ g a b, wt a b < 0 → (u g).mat a b = 0)
    (hd : ∀ s ∈ I, ∀ a, (u s).mat a a = algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi Ψ a s)) : Cond Ψ I u := by
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · rw [Matrix.charpoly_of_isUpperTriangular]
    · simp only [hd s hs]
    · intro a b hab
      apply ht
      have : (b : ℕ) < a := hab
      simp only [wt, wt1]
      omega
  · have h10 := fun g => ht g 1 0 (by decide)
    have h20 := fun g => ht g 2 0 (by decide)
    have h21 := fun g => ht g 2 1 (by decide)
    have e0 := hd _ (hs 0) 0
    have e1 := hd _ (hs 1) 1
    have e2 := hd _ (hs 2) 2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, e0, e1, e2]

theorem cond_conj (Ψ : G →* Oˣ) (I : Subgroup G) {C : Type} [CommRing C] [Algebra O C] (u : G →* GG (m := 3) (R := C))
    (hu : ∀ s ∈ I, (u s).right = 1) (n : GL (Fin 3) C) (h : Cond Ψ I u) : Cond Ψ I (conjBy n u) := by
  have hm : ∀ s ∈ I, (conjBy n u s).mat =
      (n : Matrix (Fin 3) (Fin 3) C) * (u s).mat * ((n⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
    intro s hs
    have : (conjBy n u s).left = n * (u s).left * n⁻¹ := by
      simp [conjBy, hu s hs]
    simp only [GG.mat, this, Units.val_mul]
  have hc : ∀ (A : Matrix (Fin 3) (Fin 3) C) (c : C),
      (n : Matrix (Fin 3) (Fin 3) C) * A * ((n⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) - Matrix.scalar _ c =
      (n : Matrix (Fin 3) (Fin 3) C) * (A - Matrix.scalar _ c) *
        ((n⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
    intro A c
    rw [mul_sub, sub_mul, ← (Matrix.scalar_commute c (fun _ => Commute.all _ _) _).eq, mul_assoc (Matrix.scalar _ c),
      Units.mul_inv, mul_one]
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · rw [hm s hs, ← h.1 s hs, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  · rw [hm _ (hs 0), hm _ (hs 1), hm _ (hs 2), hc, hc, hc]
    have := h.2 s hs
    generalize (u (s 0)).mat - _ = A at *
    generalize (u (s 1)).mat - _ = B at *
    generalize (u (s 2)).mat - _ = D at *
    simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc B, ← mul_assoc A, ← mul_assoc A, this, zero_mul, mul_zero]

theorem ordIdeal_eq_bot {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C)) (h : Cond D.Ψ (Iq l) r) :
    GlobalTheory.OrdLoc.ordIdeal D r = ⊥ := by
  rw [eq_bot_iff, GlobalTheory.OrdLoc.ordIdeal, Ideal.span_le]
  rintro x (⟨s, hs, i, rfl⟩ | ⟨s, hs, i, j, rfl⟩)
  · rw [h.1 s hs.2, sub_self, Polynomial.coeff_zero]
    exact Submodule.zero_mem _
  · have := h.2 s fun a => (hs a).2
    simp only [GlobalTheory.OrdLoc.sh, this]
    exact Submodule.zero_mem _

end GlobalTheory.OrdLoc.DcrOrd


open GlobalTheory.OrdLoc.DcrOrd in
theorem GlobalTheory.OrdLoc.ordIdeal_eq_bot_of_inDcr : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (r : GQ l →* GG (m := 3) (R := B)), D.InDcr (π : B →+* E) r → GlobalTheory.OrdLoc.ordIdeal D r = ⊥ := by
  intro hL l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ r hr
  obtain ⟨u, m, hu, -, -, rfl⟩ := (ordEq hL D E B π hπ r).1 hr
  exact ordIdeal_eq_bot D _ (cond_conj _ _ u (fun s hs => (hu.mult s).trans (D.η_unr s hs)) m
    (cond_tri _ _ u hu.tri (triDiag D E B π hπ u hu)))
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.triangular_rank_three_crystalline_after_push : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B' : Type} [CommRing B'] [IsLocalRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [TopologicalSpace B'] [IsModuleTopology ℚ_[l] B'] [IsTopologicalRing B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] {B : Type} [CommRing B] [IsLocalRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] (q : B' →ₐ[ℚ_[l]] B) (e : ℕ), 1 ≤ e → ∀ (κ : Fin 3 → G →* B'ˣ), (∀ i, Continuous fun g => (κ i g : B')) → (∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B' (φ g) ^ ((e : ℤ) * wt1 i)) → ∀ (x y z : G → B') (ρ : G →* GL (Fin 3) B'), Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B') = triM (fun i => κ i g) (x g) (y g) (z g)) → x ∈ Z1 (chRep (κ 0 / κ 1)) → y ∈ Z1 (chRep (κ 1 / κ 2)) → ∀ σ : G, ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ → (∀ b, (((κ 0 / κ 1) σ : B'ˣ) - (cycA l l B' (φ σ) : B')) * b = 0 → q b = 0) → (∀ b, (((κ 1 / κ 2) σ : B'ˣ) - (cycA l l B' (φ σ) : B')) * b = 0 → q b = 0) → IsCr φ (colRep ((Matrix.GeneralLinearGroup.map (q : B' →+* B)).comp ρ)) := by
  first | exact @GlobalTheory.tri_crys_push | exact GlobalTheory.tri_crys_push | (intros; apply GlobalTheory.tri_crys_push <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.ordIdeal_eq_bot_of_crystalline_deformation : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (r : GQ l →* GG (m := 3) (R := B)), D.InDcr (π : B →+* E) r → D.ordIdeal r = ⊥ := by
  first | exact @GlobalTheory.OrdLoc.ordIdeal_eq_bot_of_inDcr | exact GlobalTheory.OrdLoc.ordIdeal_eq_bot_of_inDcr | (intros; apply GlobalTheory.OrdLoc.ordIdeal_eq_bot_of_inDcr <;> assumption)

end
end
