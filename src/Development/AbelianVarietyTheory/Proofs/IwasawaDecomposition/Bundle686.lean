module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle125
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Mathlib.Data.Finset.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetSquaresConeOfCompactPosDef
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
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle667
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Antichain
public import Mathlib.Order.WellFoundedSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle668
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle012

@[expose] public section

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

namespace CellRay

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m' : ℕ}

theorem inCell {n : ℕ} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hγ' : IsCell bar φ γ')
    {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X) (hβp : ∀ i y, 0 ≤ β i y y)
    {a : Fin n → ℝ} {b : Fin m' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hlin : evalR φ (∑ i, a i • toReal (β i)) = ∑ i, a i * φ.evalZ (β i))
    (hrel : ∑ i, a i • toReal (β i) = ∑ j, b j • toReal (γ' j)) :
    ∀ i, a i ≠ 0 → ∃ (k : ℕ) (d : Fin m' → ℕ), 0 < k ∧ k • β i = ∑ j, d j • γ' j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ'.strict
  have hsum : ∑ i, a i * (ℓ (β i) : ℝ) = ∑ j, b j * (ℓ (γ' j) : ℝ) := by
    have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim β γ') (c := Sum.elim a (-b)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrel,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  have hφ : ∑ i, a i * φ.evalZ (β i) = ∑ j, b j * φ.evalZ (γ' j) := by
    rw [← hlin, hrel]; exact (linearOn_iff φ γ').1 hγ'.linear b hb
  have hterm : ∑ i, a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsum, show ∑ i, a i * (N * φ.evalZ (β i)) = N * ∑ i, a i * φ.evalZ (β i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hφ, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [h1]; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) := fun i _ =>
    mul_nonneg (ha i) (sub_nonneg.2 (h2 _ (hβ i) (hβp i)))
  intro i hi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm i (Finset.mem_univ _)
  have he : (N : ℝ) * φ.evalZ (β i) = ℓ (β i) := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hi
    · linarith
  exact h3 _ (hβ i) (hβp i) he

end CellRay

end GlobalTheory.PolFan


open GlobalTheory.PolFan.CellRay in
theorem GlobalTheory.PolFan.cell_gen_on_ray : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] (m n : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X)
    (c : Fin n → ℝ), IsCell bar φ δ → IsCell bar φ γ → LinearIndependent ℤ δ → (∀ j, 0 ≤ c j) →
    ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ j) → ∀ i, ∃ (j : Fin n) (a b : ℕ), 0 < a ∧ 0 < b ∧ a • δ i = b • γ j := by
  intro O _ bar φ X _ _ _ m n δ γ c hδ hγ hli hc hrel i
  classical

  obtain ⟨k, d, hk, hkd⟩ := inCell hγ hδ.mem hδ.nonneg (a := fun _ => (1 : ℝ)) (b := c) (fun _ => zero_le_one) hc
    ((linearOn_iff φ δ).1 hδ.linear (fun _ => 1) fun _ => zero_le_one) (by simpa using hrel) i one_ne_zero

  have hB : ∀ j, ∃ (kj : ℕ) (e : Fin m → ℕ), 0 < kj ∧ (d j ≠ 0 → kj • γ j = ∑ l, e l • δ l) := by
    intro j
    by_cases hd : d j = 0
    · exact ⟨1, 0, one_pos, fun h => absurd hd h⟩
    obtain ⟨kj, e, hkj, he⟩ := inCell (a := fun j => (d j : ℝ)) (b := Pi.single i (k : ℝ)) hδ hγ.mem hγ.nonneg
      (fun j => Nat.cast_nonneg _) (fun l => by by_cases h : l = i <;> simp [h])
      ((linearOn_iff φ γ).1 hγ.linear _ fun j => Nat.cast_nonneg _) (by
        refine LinearMap.ext₂ fun a b => ?_
        have := LinearMap.congr_fun₂ hkd a b
        simp only [LinearMap.smul_apply, LinearMap.sum_apply, toReal_apply, nsmul_eq_mul] at this ⊢
        simp only [Pi.single_apply, ite_smul, zero_smul, LinearMap.smul_apply, toReal_apply, smul_eq_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul]
        exact_mod_cast this.symm) j (by exact_mod_cast hd)
    exact ⟨kj, e, hkj, fun _ => he⟩
  choose kk e hkk he using hB
  set K := ∏ j, kk j with hKdef
  let Kj : Fin n → ℕ := fun j => ∏ j' ∈ Finset.univ.erase j, kk j'
  have hK : ∀ j, kk j * Kj j = K := fun j => Finset.mul_prod_erase Finset.univ kk (Finset.mem_univ j)
  have hKpos : 0 < K := Finset.prod_pos fun j _ => hkk j
  have hKj : ∀ j, Kj j ≠ 0 := fun j h => by
    have := hK j
    rw [h, mul_zero] at this
    omega
  have hterm : ∀ j, (K * d j) • γ j = ∑ l, (d j * Kj j * e j l) • δ l := by
    intro j
    by_cases hd : d j = 0
    · simp [hd]
    rw [← hK j, show kk j * Kj j * d j = (d j * Kj j) * kk j by ring, ← smul_smul, he j hd, Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [smul_smul]
  have key : (K * k) • δ i = ∑ l, (∑ j, d j * Kj j * e j l) • δ l := by
    rw [← smul_smul, hkd, Finset.smul_sum]
    simp only [smul_smul, hterm]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => (Finset.sum_smul).symm
  have hFG := Fintype.linearIndependent_iffₛ.1 hli (fun l => ((∑ j, d j * Kj j * e j l : ℕ) : ℤ))
    (fun l => if l = i then ((K * k : ℕ) : ℤ) else 0) (by
      simp only [Nat.cast_smul_eq_nsmul, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact key.symm)
  have hoff : ∀ l, l ≠ i → ∀ j, d j * Kj j * e j l = 0 := by
    intro l hl j
    have := hFG l
    simp only [if_neg hl, Nat.cast_eq_zero] at this
    exact (Finset.sum_eq_zero_iff.1 this) j (Finset.mem_univ _)
  have hon : ∑ j, d j * Kj j * e j i ≠ 0 := by
    have := hFG i
    rw [if_pos rfl, Nat.cast_inj] at this
    rw [this]
    exact (Nat.mul_pos hKpos hk).ne'
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hon
  have hdj : d j ≠ 0 := fun h => hj (by rw [h]; ring)
  have hej : e j i ≠ 0 := fun h => hj (by rw [h]; ring)
  have hel : ∀ l, l ≠ i → e j l = 0 := fun l hl => by
    have := hoff l hl j
    rcases Nat.mul_eq_zero.1 this with h | h
    · rcases Nat.mul_eq_zero.1 h with h' | h'
      · exact absurd h' hdj
      · exact absurd h' (hKj j)
    · exact h
  have hγj : kk j • γ j = e j i • δ i := by
    rw [he j hdj, Finset.sum_eq_single i (fun l _ hl => by rw [hel l hl, zero_smul]) (by simp)]
  exact ⟨j, e j i, kk j, Nat.pos_of_ne_zero hej, hkk j, hγj.symm⟩
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Sub

variable {O : Type} [CommRing O] (bar : O → O) (q : ℕ)

def LinOnCells (φ χ : InvFun O) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ → χ.LinearOn γ

def Subordinate (φ' φ : InvFun O) : Prop :=
  ∀ χ : InvFun O, LinOnCells bar q φ χ → LinOnCells bar q φ' χ

def SimpLab (φ lab : InvFun O) : Prop :=
  (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ k : ℕ, 0 < k → lab.evalZ ((k : ℤ) • β) = lab.evalZ β) ∧
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ →
      ∃ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ X), IsCell bar φ δ ∧ LinearIndependent ℤ δ ∧
        Function.Injective (fun i => lab.evalZ (δ i)) ∧
        ∀ j, ∃ a : Fin m' → ℝ, (∀ i, 0 ≤ a i) ∧ toReal (γ j) = ∑ i, a i • toReal (δ i)

variable {bar q}

theorem linOnCells_self (φ : InvFun O) : LinOnCells bar q φ φ := fun _ _ _ _ _ _ _ _ h => h.linear

theorem Subordinate.refl (φ : InvFun O) : Subordinate bar q φ φ := fun _ h => h

theorem Subordinate.trans {φ'' φ' φ : InvFun O} (h₁ : Subordinate bar q φ'' φ') (h₂ : Subordinate bar q φ' φ) :
    Subordinate bar q φ'' φ := fun χ h => h₁ χ (h₂ χ h)

theorem Subordinate.linearOn {φ' φ : InvFun O} (h : Subordinate bar q φ' φ) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] (hX : Module.finrank O X ≤ q) {m : ℕ}
    {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCell bar φ' γ) : φ.LinearOn γ :=
  h φ (linOnCells_self φ) X hX m γ hγ

end Sub

section Inhab

def zeroFun (O : Type) [CommRing O] : InvFun O where
  toFun _ _ := 0
  inv _ _ _ _ _ := rfl
  zero _ := rfl

@[simp] theorem zeroFun_evalZ {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    (β : LinearMap.BilinForm ℤ X) : (zeroFun O).evalZ β = 0 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  simp only [InvFun.evalZ, (zeroFun O).eval_eq hr]
  rfl

end Inhab

end GlobalTheory.PolFan
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiDoubleCoord

open GlobalTheory.PeriodBalance GlobalTheory.PsiTauCoordRel MonoidalCategory CartesianMonoidalCategory MonObj GrpObj

section
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem val_cub (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J : (Spec (CommRingCat.of (FractionRing R)) ⟶ D.P.A.left) → D.P.L.ι}
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (a a' b : D.X) :
    ∃ w : Rˣ, val (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t (𝟙 (Spec (CommRingCat.of (FractionRing R))) ≫ D.pt3 a a' b) ξ J =
      Units.map (cst ξ).toMonoidHom w := by
  have hp : 𝟙 (Spec (CommRingCat.of (FractionRing R))) ≫ D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left := by
    simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]
  rw [hp]
  refine val_int (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) ξ hJc D.cub.t _ fun k => ?_
  show (_ ≫ (psum _ _ _).left) ≫ _ = _
  rw [Category.assoc, Over.w, Over.w]; rfl

theorem val_sym (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (y : D.X) :
    ∃ w : Rˣ, val (LB.pullGen D.P.L _ _ D.sym (D.xK y)) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J = Units.map (cst ξ).toMonoidHom w := by
  rw [val_pull hJ]
  have hx : 𝟙 (Spec (CommRingCat.of (FractionRing R))) ≫ D.xK y = jK R ≫ (D.c y).left := by rw [Category.id_comp]; exact DVR.QForm.ptK_eq D y
  rw [hx]
  refine val_int ξ hJc D.sym _ fun k => ?_
  obtain ⟨q, hq⟩ : ∃ q : D.P.A ⟶ D.P.A, (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k = q.left := by
    fin_cases k
    · exact ⟨_, rfl⟩
    · exact ⟨𝟙 _, rfl⟩
  rw [hq, Category.assoc, Over.w q, Over.w]; rfl

theorem val_rig (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) :
    ∃ w : Rˣ, val D.rigK (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J = Units.map (cst ξ).toMonoidHom w := by
  unfold DegPre.rigK
  rw [val_pull hJ]
  have : 𝟙 (Spec (CommRingCat.of (FractionRing R))) ≫ (toUnit (TK R)).left = jK R ≫ 𝟙 _ := by rw [toUnit_left]; simp
  rw [this]
  exact val_int ξ hJc D.rig (𝟙 _) fun _ => by rw [Category.id_comp]; exact Over.w η[D.P.A]

end

theorem alg {G : Type} [CommGroup G] (A0 Ay Am A2 Vr C0 C1 S : G)
    (h1 : Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹ * C0 = Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹ * (Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹))
    (h2 : Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹ * C1 = A2 * Ay⁻¹ * Ay⁻¹ * Vr⁻¹ * (A0 * Am⁻¹ * Ay⁻¹ * Vr⁻¹))
    (h3 : Am * S = Ay) :
    A2 = C0 * C0 * C1 * Vr * Vr * Vr * S⁻¹ * Ay ^ 4 := by
  have hC0 := mul_left_cancel h1
  have hAm : Am = Ay * S⁻¹ := eq_mul_inv_of_mul_eq h3
  subst hC0 hAm
  have e : A2 = Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹ * C1 * (Ay⁻¹ * Ay⁻¹ * Vr⁻¹ * (A0 * (Ay * S⁻¹)⁻¹ * Ay⁻¹ * Vr⁻¹))⁻¹ := by
    rw [h2]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

theorem val_cubP {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (a a' b : D.X) :
    ∃ w : Rˣ, val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b))
      (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J = Units.map (cst ξ).toMonoidHom w := by
  obtain ⟨w, hw⟩ := val_cub D ξ hJc a a' b
  exact ⟨w, (val_pull hJ _ _ _).trans hw⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegData R I)
    (y : D.toPre.X) (r s : R), PsiCoord D.toPre y r → PsiCoord D.toPre (2 • y) s → Associated s (r ^ 4) := by
  intro R _ _ _ I D y r s hr hs
  haveI : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.toPre.P.isLB D.toPre.P.A.hom
  have b1 := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (D.tau_bimult 0 0 y) (𝟙 _)).trans (val_mul hJ _ _ _))
  have b2 := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (D.tau_bimult y (-y) y) (𝟙 _)).trans (val_mul hJ _ _ _))
  have ev := (val_mul hJ _ _ _).symm.trans (val_corr hJ (D.psi_even y) (𝟙 _))
  have vt : ∀ a b : D.toPre.X, val (D.toPre.tau a b) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J = val (D.toPre.psi (a + b)) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J *
      (val (D.toPre.psi a) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J)⁻¹ * (val (D.toPre.psi b) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J)⁻¹ * (val D.toPre.rigK (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J)⁻¹ :=
    fun a b => GlobalTheory.PeriodBalance.val_tau D.toPre ξ hJ a b
  obtain ⟨w0, hw0⟩ := val_cubP D.toPre ξ hJ hJc 0 0 y
  obtain ⟨w1, hw1⟩ := val_cubP D.toPre ξ hJ hJc y (-y) y
  obtain ⟨w5, hw5⟩ := val_rig D.toPre ξ hJ hJc
  obtain ⟨w6, hw6⟩ := val_sym D.toPre ξ hJ hJc y
  rw [hw6] at ev
  rw [hw0, vt, vt, hw5] at b1
  rw [hw1, vt, vt, vt, hw5] at b2
  rw [add_zero, zero_add] at b1
  rw [add_neg_cancel, zero_add, neg_add_cancel, ← two_nsmul] at b2
  have key := alg _ _ _ _ _ _ _ _ b1 b2 ev
  obtain ⟨u1, g1⟩ : ∃ u : Rˣ, (val (D.toPre.psi y) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J).val = cst ξ (u * r) := val_psi D.toPre ξ hJ hJc y r hr
  obtain ⟨u2, g2⟩ : ∃ u : Rˣ, (val (D.toPre.psi (2 • y)) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J).val = cst ξ (u * s) := val_psi D.toPre ξ hJ hJc (2 • y) s hs
  obtain ⟨W, key2⟩ : ∃ W : Rˣ, val (D.toPre.psi (2 • y)) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J =
      Units.map (cst ξ).toMonoidHom W * (val (D.toPre.psi y) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J) ^ 4 :=
    ⟨w0 * w0 * w1 * w5 * w5 * w5 * w6⁻¹, by rw [key]; simp only [map_mul, map_inv]⟩
  have e : cst ξ (u2 * s) = cst ξ (W * (u1 * r) ^ 4) := by
    rw [← g2, key2, map_mul, map_pow, ← g1, Units.val_mul, Units.val_pow_eq_pow_val]; rfl
  have e2 := cst_injective ξ e
  refine ⟨u2 * (W * u1 ^ 4)⁻¹, ?_⟩
  have h3 : ((W * u1 ^ 4 : Rˣ) : R) * r ^ 4 = u2 * s := by push_cast; rw [e2]; ring
  rw [Units.val_mul, ← _root_.mul_assoc, _root_.mul_comm s, ← h3, _root_.mul_comm, ← _root_.mul_assoc, Units.inv_mul,
    _root_.one_mul]

end GlobalTheory.PsiDoubleCoord
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

theorem GlobalTheory.lbIso_of_generic_normal_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsNoetherianRing R → IsIntegrallyClosed R → ∀ (H : Scheme.{0}) (p : H ⟶ Sp R) (e : Sp R ⟶ H), Smooth p → QuasiCompact p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ L M : LB H, L.IsLB → M.IsLB → LBIso (L.pull (pullback.fst p (jK R))) (M.pull (pullback.fst p (jK R))) → LBIso L M := by
  intro R _ _ _ hN hI H p e hs _ hg he L M hL hM h
  haveI : IsNoetherianRing R := hN
  haveI : IsIntegrallyClosed R := hI
  have hD := LB.isLB_div hM hL
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  obtain ⟨t, ht⟩ := GenericExtend.exists_isGen_of_densePart (Sp R) _ (jK R) (ZJ.isNormalScheme_sp R) h₁ h₂
    DVR.isDominant_jK inferInstance (Over.mk p) e (LB.div M L) he hs hg hD
    (DVR.exists_gen_of_isLB_local _ (LB.isLB_pull hD _)) ((IsoExtend.lbIso_pull_iff_gen L M _).1 h)
  exact ⟨t, ht⟩
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory

theorem dickson_finite_below_every {ι : Type} (n : ℕ) (f : ι → Fin n → ℕ) :
    ∃ F : Finset ι, ∀ i, ∃ j ∈ F, f j ≤ f i := by
  classical
  set s : Set (Fin n → ℕ) := Set.range f
  have hpwo : s.IsPWO := Set.isPWO_of_wellQuasiOrderedLE s
  set m : Set (Fin n → ℕ) := {x | Minimal (· ∈ s) x}
  have hm : m.Finite := (setOf_minimal_antichain (· ∈ s)).finite_of_partiallyWellOrderedOn
    (hpwo.mono (fun x hx => hx.prop))
  have hpre : ∀ x ∈ m, ∃ j, f j = x := fun x hx => hx.prop
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨∅, fun i => isEmptyElim i⟩
  choose! g hg using hpre
  refine ⟨hm.toFinset.image g, fun i => ?_⟩
  obtain ⟨x, hxi, hx⟩ := hpwo.exists_le_minimal (Set.mem_range_self i)
  exact ⟨g x, Finset.mem_image_of_mem g (hm.mem_toFinset.mpr hx), by rw [hg x hx]; exact hxi⟩

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory

theorem bilinForm_exists_primitive_of_ne_zero (X : Type) [AddCommGroup X]
    (σ : LinearMap.BilinForm ℤ X) (hσ : σ ≠ 0) :
    ∃ (g : ℕ) (β₀ : LinearMap.BilinForm ℤ X), 0 < g ∧ (g : ℤ) • β₀ = σ ∧
      ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β₀ → k = 1 := by
  classical
  obtain ⟨a, b, hab⟩ : ∃ a b, σ a b ≠ 0 := by
    by_contra h
    apply hσ
    ext a b
    by_contra h'
    exact h ⟨a, b, by simpa using h'⟩
  have hbound : ∀ k : ℕ, (∃ β' : LinearMap.BilinForm ℤ X, (k : ℤ) • β' = σ) →
      k ≤ (σ a b).natAbs := by
    rintro k ⟨β', hβ'⟩
    have h1 : σ a b = (k : ℤ) * β' a b := by
      rw [← hβ']
      simp
    have h2 : k ∣ (σ a b).natAbs := Int.natCast_dvd.mp ⟨β' a b, h1⟩
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hab) h2
  let P : ℕ → Prop := fun k => ∃ β' : LinearMap.BilinForm ℤ X, (k : ℤ) • β' = σ
  have hP1 : P 1 := ⟨σ, by simp⟩
  have h1le : 1 ≤ (σ a b).natAbs := hbound 1 hP1
  have hg : P (Nat.findGreatest P (σ a b).natAbs) := Nat.findGreatest_spec h1le hP1
  have hg1 : 1 ≤ Nat.findGreatest P (σ a b).natAbs := Nat.le_findGreatest h1le hP1
  have hmax : ∀ k, P k → k ≤ Nat.findGreatest P (σ a b).natAbs :=
    fun k hk => Nat.le_findGreatest (hbound k hk) hk
  generalize Nat.findGreatest P (σ a b).natAbs = g at hg hg1 hmax
  obtain ⟨β₀, hβ₀⟩ := hg
  refine ⟨g, β₀, hg1, hβ₀, ?_⟩
  intro k β' hk
  have hgk : P (g * k) := ⟨β', by rw [Nat.cast_mul, mul_smul, hk, hβ₀]⟩
  have hle := hmax _ hgk
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hσ
    rw [← hβ₀, ← hk]
    simp
  have hk1 : k ≤ 1 := by
    have : g * k ≤ g * 1 := by simpa using hle
    exact Nat.le_of_mul_le_mul_left this hg1
  omega

end GlobalTheory
end

section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_finset_squares_cone_of_compact_posDef : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (𝒦 : Set (Matrix ι ι ℝ)), IsCompact 𝒦 → (∀ P ∈ 𝒦, P.PosDef) → ∃ S : Finset (ι → ℤ), ∀ P ∈ 𝒦, ∃ c : (ι → ℤ) → ℝ, (∀ l, 0 ≤ c l) ∧ P = ∑ l ∈ S, c l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ)) := by
  first | exact @GlobalTheory.ConeSq.exists_finset_cone | exact GlobalTheory.ConeSq.exists_finset_cone | (intros; apply GlobalTheory.ConeSq.exists_finset_cone <;> assumption)
end
