module

public import Formalism.IncomingBounds.Bundle002
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle044
public import Formalism.LocalToGlobal.CharacterGerms.Bundle003
public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Mathlib.RingTheory.DedekindDomain.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle047
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle033
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.DualLattices.Bundle007
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
import ReciprocityTheory.DualLattices.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

@[expose] public section

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.jetAt0_prod_subst_disjoint_variables : ∀ (C : Type) [Field C] (Orb : Type) [Fintype Orb] (σ : Orb → Type) [∀ o, Fintype (σ o)] (τ : Type) (e : ∀ o, σ o → τ), Function.Injective (fun x : (Σ o, σ o) => e x.1 x.2) → ∀ (P : ∀ o, MvPolynomial (σ o) C) (F : ∀ o, MvPowerSeries (σ o) C), jetAt0 (∏ o, MvPolynomial.rename (e o) (P o)) (∏ o, MvPowerSeries.subst (fun x : σ o => (MvPowerSeries.X (e o x) : MvPowerSeries τ C)) (F o)) = ∏ o, jetAt0 (P o) (F o) := by
  first | exact @GlobalTheory.JetProdSubst.jetAt0_prod_subst | exact GlobalTheory.JetProdSubst.jetAt0_prod_subst | (intros; apply GlobalTheory.JetProdSubst.jetAt0_prod_subst <;> assumption)
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.exists_ladic_separating_sequence_embeddings : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → (∃ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) ∧ (∀ a, V.MM (em a ε - 1)) ∧ ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y) → ∃ s : ℕ → O, (∀ n, ∃ y, s (n + 1) - s n = (V.l : O) ^ n * y) ∧ (∀ (a : ZMod d) (K : ℕ), ∃ n0, ∀ n ≥ n0, V.Ge K (1 - em a (s n))) ∧ ∀ φ : O →+* C, (∀ x, V.Ge 0 (φ x)) → (∀ a, ∃ x, V.v (em a x - φ x) = 0) → ∀ K : ℕ, ∃ n0, ∀ n ≥ n0, V.Ge K (0 - φ (s n)) := by
  first | exact @GlobalTheory.SeparatingSeq.main | exact GlobalTheory.SeparatingSeq.main | (intros; apply GlobalTheory.SeparatingSeq.main <;> assumption)
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.admissibleRows_value_eq_rowGauge : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ) (H : X.Hyps V) (N : ℕ) (P : MvPolynomial (Fin N × WV I) C) (kind : Fin N → Option (Fin 2 × ZMod d × ZMod d)), RowsOK (X.rowData H).G (X.rowData H).Alt P kind → ∀ gr : Fin N → MvPowerSeries (WV I) C, ValOf (X.rowData H).hL P kind gr = jetAt0 P (∏ ρ, (rowCopy ρ (gr ρ) * mvExp (rowCopy ρ X.hRow))) := by
  first | exact @GlobalTheory.RowVal.valOf_eq_hRow | exact GlobalTheory.RowVal.valOf_eq_hRow | (intros; apply GlobalTheory.RowVal.valOf_eq_hRow <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocalFactorFree

private theorem aux {R S M I : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite R M] [Module.Free R M]
    [Finite I] (e : S) (he : IsIdempotentElem e) [IsDomain (S ⧸ Ideal.span {1 - e})]
    [IsPrincipalIdealRing (S ⧸ Ideal.span {1 - e})]
    (b : Module.Basis I R (LinearMap.range (LinearMap.mulLeft R e))) :
    ∃ (h : ℕ) (y : Fin h → M), LinearIndependent R (fun q : I × Fin h => (b q.1 : S) • y q.2) ∧
      ∀ m : M, m ∈ Submodule.span R (Set.range fun q : I × Fin h => (b q.1 : S) • y q.2) ↔ (1 - e) • m = 0 := by
  classical
  let f : LinearMap.range (LinearMap.mulLeft R e) →ₗ[R] (S ⧸ Ideal.span {1 - e}) :=
    (Ideal.Quotient.mkₐ R (Ideal.span {1 - e})).toLinearMap ∘ₗ (Submodule.subtype _)
  have hf : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨_, s, rfl⟩ hs
      have h1 : e * s ∈ Ideal.span {1 - e} := Ideal.Quotient.eq_zero_iff_mem.1 hs
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 h1
      apply Subtype.ext
      change e * s = 0
      have h2 : e * (e * s) = e * s := by rw [← _root_.mul_assoc, he.eq]
      rw [← h2, ← ht]
      linear_combination t * he.mul_one_sub_self
    · intro a
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
      refine ⟨⟨e * s, s, rfl⟩, ?_⟩
      change Ideal.Quotient.mk _ (e * s) = Ideal.Quotient.mk _ s
      rw [Ideal.Quotient.eq]
      exact Ideal.mem_span_singleton'.2 ⟨-s, by ring⟩
  let bA : Module.Basis I R (S ⧸ Ideal.span {1 - e}) := b.map (LinearEquiv.ofBijective f hf)
  haveI : Module.Finite R (S ⧸ Ideal.span {1 - e}) := Module.Finite.of_basis bA
  haveI : Module.Free R (S ⧸ Ideal.span {1 - e}) := Module.Free.of_basis bA
  let N : Submodule S M := Submodule.torsionBy S M (1 - e)
  haveI : Module.Finite R N := Module.Finite.of_injective (N.subtype.restrictScalars R) Subtype.val_injective
  letI : Module (S ⧸ Ideal.span {1 - e}) N := inferInstanceAs (Module (S ⧸ Submodule.span S {1 - e}) (Submodule.torsionBy S M (1 - e)))
  have hsm : ∀ (s : S) (n : N), (Ideal.Quotient.mk (Ideal.span {1 - e}) s) • n = s • n := fun _ _ => rfl
  haveI : IsScalarTower R (S ⧸ Ideal.span {1 - e}) N := ⟨fun r a n => by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : r • Ideal.Quotient.mk (Ideal.span {1 - e}) s = Ideal.Quotient.mk (Ideal.span {1 - e}) (r • s) := rfl
    rw [this, hsm, hsm, smul_assoc]⟩
  haveI : Module.Finite (S ⧸ Ideal.span {1 - e}) N := Module.Finite.of_restrictScalars_finite R _ _
  haveI : Module.IsTorsionFree (S ⧸ Ideal.span {1 - e}) N := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro a n han
    by_cases ha : a = 0
    · exact Or.inl ha
    right
    obtain ⟨r, hr, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R) a).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ha)
    have h1 : r • n = 0 := by
      rw [← algebraMap_smul (S ⧸ Ideal.span {1 - e}) r n, hc, mul_comm, mul_smul, han, smul_zero]
    have h2 : r • (n : M) = 0 := congrArg Subtype.val h1
    exact Subtype.ext ((smul_eq_zero.1 h2).resolve_left hr)
  let y := Module.finBasis (S ⧸ Ideal.span {1 - e}) N
  let B := bA.smulTower y
  have hB : (fun q : I × Fin _ => (b q.1 : S) • (y q.2 : M)) = (N.subtype.restrictScalars R) ∘ B := by
    funext q
    simp only [B, Function.comp, Module.Basis.smulTower_apply]
    rfl
  refine ⟨_, fun j => (y j : M), ?_, fun m => ?_⟩
  · rw [hB]
    exact B.linearIndependent.map' _ (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  · rw [hB, Set.range_comp, ← Submodule.map_span, B.span_eq, Submodule.map_top]
    constructor
    · rintro ⟨n, rfl⟩
      exact n.2
    · intro hm
      exact ⟨⟨m, hm⟩, rfl⟩

private theorem aux2 {R S I κ : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CommRing S] [Algebra R S]
    [Fintype κ] [DecidableEq κ]
    [Finite I] (e : S) (he : IsIdempotentElem e) [IsDomain (S ⧸ Ideal.span {1 - e})]
    [IsPrincipalIdealRing (S ⧸ Ideal.span {1 - e})]
    (b : Module.Basis I R (LinearMap.range (LinearMap.mulLeft R e))) (ρ : S →ₐ[R] Matrix κ κ R) :
    ∃ (h : ℕ) (y : Fin h → κ → R), LinearIndependent R (fun q : I × Fin h => ρ (b q.1 : S) *ᵥ y q.2) ∧
      Submodule.span R (Set.range fun q : I × Fin h => ρ (b q.1 : S) *ᵥ y q.2) =
        LinearMap.range (Matrix.mulVecLin (ρ e)) := by
  letI : Module S (κ → R) := Module.compHom (κ → R) (ρ : S →+* Matrix κ κ R)
  have hsm : ∀ (s : S) (v : κ → R), s • v = ρ s *ᵥ v := fun _ _ => rfl
  haveI : IsScalarTower R S (κ → R) := ⟨fun r s v => by
    rw [hsm, hsm, map_smul, Matrix.smul_mulVec]⟩
  obtain ⟨h, y, h1, h2⟩ := aux (M := κ → R) e he b
  refine ⟨h, y, h1, ?_⟩
  ext m
  refine (h2 m).trans ⟨fun hm => ⟨m, ?_⟩, ?_⟩
  · change e • m = m
    rw [sub_smul, one_smul, sub_eq_zero] at hm
    exact hm.symm
  · rintro ⟨v, rfl⟩
    change (1 - e) • e • v = 0
    rw [← mul_smul, he.one_sub_mul_self, zero_smul]

theorem exists_free_generators : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (w : PlaceU p OE) (b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))) (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] Matrix κ κ ℤ_[p]), ∃ (h : ℕ) (y : Fin h → κ → ℤ_[p]), LinearIndependent ℤ_[p] (fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) ∧ Submodule.span ℤ_[p] (Set.range fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) = LinearMap.range (Matrix.mulVecLin (ρ w.e)) := by
  intro p _ OE _ _ _ _ _ w b κ _ _ ρ
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.padic_unit_quotient_principal_basis p OE w
  exact aux2 w.e w.idem b ρ

end GlobalTheory.LocalFactorFree
end

section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BiextSym

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_gen_of_iso {X : Scheme.{0}} {L : LB X} {F : X ⟶ X} (h : LBIso L (L.pull F)) :
    ∃ s : LB.Gen (LB.LinComb L (K := Fin 2) ![F, 𝟙 X] ![1, -1]), s.IsGen := by
  obtain ⟨w, hw⟩ := h
  have hp := (isGen_iff w).1 hw
  have le : ∀ j : Fin 2 → L.ι, LB.wchart L (K := Fin 2) ![F, 𝟙 X] j ≤ (L.pull F).U (fun _ => j 0) ⊓ L.U (j 1) :=
    fun j x hx => ⟨mem_pull.2 (Set.mem_iInter.1 hx 0), Set.mem_iInter.1 hx 1⟩
  refine ⟨⟨fun j => res (le j) (w.s (fun _ => j 0, j 1))⟩, fun j j' => unit_ext fun y hy => ?_⟩
  have a := hp _ (𝟙 X) y (j 0) (j' 0) (j 1) (j' 1) (mem_pull.1 (le j hy.1).1) (mem_pull.1 (le j' hy.2).1)
    (le j hy.1).2 (le j' hy.2).2
  refine ((gm_res _ y _ hy _).trans (gm_res (𝟙 X) y (le j) hy.1 _)).trans (a.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L _ _ (𝟙 X) y j j' hy.1 hy.2).trans ?_)
    ((gm_res _ y _ hy _).trans (gm_res (𝟙 X) y (le j') hy.2 _)))
  rw [Fin.prod_univ_two]
  show gm (𝟙 X ≫ F) y _ (L.g (j 0) (j' 0)) ^ (1 : ℤ) * gm (𝟙 X ≫ 𝟙 X) y _ (L.g (j 1) (j' 1)) ^ (-1 : ℤ) = _
  rw [_root_.zpow_neg, _root_.zpow_one, _root_.zpow_one, Category.id_comp (𝟙 X)]

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

omit [GrpObj A] [IsCommMonObj A] in
theorem prod_sym {T : Over S} (x y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ (A ⊗ A).left) → U) :
    ∏ i : Fin 2, h ((lift x y).left ≫ ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] i) ^ (![1, -1] i : ℤ) =
      h (lift y x).left * (h (lift x y).left)⁻¹ := by
  have e : lift x y ≫ lift (snd A A) (fst A A) = lift y x := by rw [comp_lift, lift_fst, lift_snd]
  rw [Fin.prod_univ_two]
  show h (lift x y ≫ lift (snd A A) (fst A A)).left ^ (1 : ℤ) * h ((lift x y).left ≫ 𝟙 _) ^ (-1 : ℤ) = _
  rw [e, Category.comp_id, _root_.zpow_neg, _root_.zpow_one, _root_.zpow_one]

theorem biextension_first_law_product {T : Over S} (x x' y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ (A ⊗ A).left) → U) :
    ∏ i, h ((lift x (lift x' y)).left ≫ law1φ A (x3 A 0) (x3 A 1) (x3 A 2) i) ^ lawε i =
      h (lift (x * x') y).left * (h (lift x y).left)⁻¹ * (h (lift x' y).left)⁻¹ := by
  have a₀ : lift x (lift x' y) ≫ x3 A 0 = x := by simp [x3]
  have a₁ : lift x (lift x' y) ≫ x3 A 1 = x' := by simp [x3]
  have a₂ : lift x (lift x' y) ≫ x3 A 2 = y := by simp [x3]
  have b : lift x (lift x' y) ≫ padd A (x3 A 0) (x3 A 1) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁])
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _
    (fun i => h ((lift x (lift x' y)).left ≫ law1φ A (x3 A 0) (x3 A 1) (x3 A 2) ⟨i⟩) ^ lawε ⟨i⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift x (lift x' y) ≫ lift (padd A (x3 A 0) (x3 A 1)) (x3 A 2)).left ^ (1 : ℤ) *
    h (lift x (lift x' y) ≫ lift (x3 A 0) (x3 A 2)).left ^ (-1 : ℤ) *
    h (lift x (lift x' y) ≫ lift (x3 A 1) (x3 A 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, b, a₀, a₁, a₂]
  simp only [_root_.zpow_neg, _root_.zpow_one]

theorem biextension_second_law_product {T : Over S} (x y y' : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ (A ⊗ A).left) → U) :
    ∏ i, h ((lift x (lift y y')).left ≫ law2φ A (x3 A 0) (x3 A 1) (x3 A 2) i) ^ lawε i =
      h (lift x (y * y')).left * (h (lift x y).left)⁻¹ * (h (lift x y').left)⁻¹ := by
  have a₀ : lift x (lift y y') ≫ x3 A 0 = x := by simp [x3]
  have a₁ : lift x (lift y y') ≫ x3 A 1 = y := by simp [x3]
  have a₂ : lift x (lift y y') ≫ x3 A 2 = y' := by simp [x3]
  have b : lift x (lift y y') ≫ padd A (x3 A 1) (x3 A 2) = y * y' := (MonObj.comp_mul _ _ _).trans (by rw [a₁, a₂])
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _
    (fun i => h ((lift x (lift y y')).left ≫ law2φ A (x3 A 0) (x3 A 1) (x3 A 2) ⟨i⟩) ^ lawε ⟨i⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift x (lift y y') ≫ lift (x3 A 0) (padd A (x3 A 1) (x3 A 2))).left ^ (1 : ℤ) *
    h (lift x (lift y y') ≫ lift (x3 A 0) (x3 A 1)).left ^ (-1 : ℤ) *
    h (lift x (lift y y') ≫ lift (x3 A 0) (x3 A 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, b, a₀, a₁, a₂]
  simp only [_root_.zpow_neg, _root_.zpow_one]

theorem exists_norm {P : LB (A ⊗ A).left} (hP : P.IsLB) (h : LBIso P (P.pull (lift (snd A A) (fst A A)).left)) :
    ∃ s : LB.Gen (LB.LinComb P (K := Fin 2) ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] ![1, -1]), s.IsGen ∧
      ∀ (T : Over S) (z : T.left) (J), Good P z J → val s (lift (1 : T ⟶ A) (1 : T ⟶ A)).left z J = 1 := by
  obtain ⟨t, ht⟩ := exists_gen_of_iso h
  obtain ⟨s, hs, hv⟩ := exists_gen hP (K' := Fin 2) (φ' := ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left])
    (ε' := ![1, -1]) (fun V _ k => by
      have p := prod_sym (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A) k
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _
        (c := ∏ i : Fin 2, k (![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] i) ^ (![1, -1] i : ℤ)) rfl
        (DVR.prod_neg _ _ p)) ?_
      rw [mul_inv_cancel, inv_one, _root_.mul_one])
    (LB.mulGen P _ _ _ _ t (LB.invGen P _ _ (LB.pullGen P _ _ t (lift (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨s, hs, fun T z J hJ => ?_⟩
  rw [hv _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, ← Over.comp_left, comp_lift, MonObj.comp_one, mul_inv_cancel]

theorem val_pull₂ {X : Scheme.{0}} {P : LB X} {K : Type} [Fintype K] {B C : Over S} {φ : K → ((B ⊗ C).left ⟶ X)}
    {ε : K → ℤ} (u : LB.Gen (LB.LinComb P φ ε)) {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J} (hJ : Good P z J)
    (a : T ⟶ B) (b : T ⟶ C) :
    val (LB.pullGen P φ ε u (lift a b).left) ρ.left z J = val u (lift (ρ ≫ a) (ρ ≫ b)).left z J := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift]

theorem val_pull₃ {X : Scheme.{0}} {P : LB X} {K : Type} [Fintype K] {B C D : Over S}
    {φ : K → ((B ⊗ C ⊗ D).left ⟶ X)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb P φ ε)) {T T' : Over S} (ρ : T' ⟶ T)
    {z : T'.left} {J} (hJ : Good P z J) (a : T ⟶ B) (b : T ⟶ C) (c : T ⟶ D) :
    val (LB.pullGen P φ ε u (lift a (lift b c)).left) ρ.left z J =
      val u (lift (ρ ≫ a) (lift (ρ ≫ b) (ρ ≫ c))).left z J := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift, comp_lift]

theorem law_origin {P : LB (A ⊗ A).left} (β : IsBiext A P) {T : Over S} {z : T.left} {J} (hJ : Good P z J) :
    val β.law1 (lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (1 : T ⟶ A))).left z J =
      val β.law2 (lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (1 : T ⟶ A))).left z J := by
  let ρ := lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (1 : T ⟶ A)))
  have a₀ : ρ ≫ x4 A 0 = 1 := by simp [ρ, x4]
  have a₁ : ρ ≫ x4 A 1 = 1 := by simp [ρ, x4]
  have a₂ : ρ ≫ x4 A 2 = 1 := by simp [ρ, x4]
  have a₃ : ρ ≫ x4 A 3 = 1 := by simp [ρ, x4]
  have b₀ : ρ ≫ padd A (x4 A 0) (x4 A 1) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁, _root_.mul_one])
  have b₁ : ρ ≫ padd A (x4 A 2) (x4 A 3) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [a₂, a₃, _root_.mul_one])
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    (val_pull₃ β.law1 ρ hJ _ _ _) (val_pull₃ β.law2 ρ hJ _ _ _))) (val_pull₃ β.law2 ρ hJ _ _ _))).symm.trans
    ((val_corr hJ β.compat ρ.left).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_pull₃ β.law2 ρ hJ _ _ _) (val_pull₃ β.law1 ρ hJ _ _ _))) (val_pull₃ β.law1 ρ hJ _ _ _))))
  rw [b₀, b₁, a₀, a₁, a₂, a₃, mul_comm (val β.law2 _ z J) (val β.law1 _ z J)] at e
  exact (mul_left_cancel e).symm

theorem main :
  (ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme A →
    ∀ (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (A ⊗ A).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext A P),
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso P (P.pull (lift (snd A A) (fst A A)).left) →
    ∃ s : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb P (K := Fin 2) ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] ![1, -1]), s.IsGen ∧ ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ (A ⊗ A).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J → ∀ x x' y : T ⟶ A,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift y x).left z J = 1 ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift x (lift x' y)).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift (x * x') y).left z J =
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x' y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift y (lift x x')).left z J) := by
  intro hG S A _ _ hA P β hs
  obtain ⟨s, hs, h1⟩ := exists_norm β.isLB hs
  refine ⟨s, hs, fun T z J hJ x x' y => ⟨?_, ?_⟩⟩
  · have ev : ∀ {T' : Over S} (σ : T' ⟶ A ⊗ A) {z : T'.left} {J}, Good P z J →
        val (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ s (lift (fst A A) (snd A A)).left)
          (LB.pullGen P _ _ s (lift (snd A A) (fst A A)).left)) σ.left z J =
          val s (lift (σ ≫ fst A A) (σ ≫ snd A A)).left z J * val s (lift (σ ≫ snd A A) (σ ≫ fst A A)).left z J :=
      fun σ z J hJ => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull₂ s σ hJ _ _) (val_pull₂ s σ hJ _ _))
    let e : 𝟙_ (Over S) ⟶ A ⊗ A := lift 1 1
    have sj : Function.Surjective ((snd A A).left ≫ A.hom).appTop.hom := surj_comp (surj_snd hG hA _) (hG _ _ hA).2
    have he : e.left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by rw [Over.w]; exact Over.w e
    have key := gen_unique' β.isLB (u' := LB.oneGen P (Y := (A ⊗ A).left)) (fun V _ k => by
        refine (Fintype.prod_empty _).trans (Eq.symm ?_)
        refine (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_sym (fst A A) (snd A A) k)
          (prod_sym (snd A A) (fst A A) k)).trans ?_
        rw [_root_.mul_assoc, inv_mul_cancel_left, mul_inv_cancel]) _ e.left he sj
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hs _) (DVR.pullGen_isGen _ _ _ _ hs _))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
      (fun y I hI => by
        refine (ev e hI).trans (Eq.trans ?_ (val_one _).symm)
        rw [lift_fst, lift_snd, h1 _ y I hI, _root_.mul_one]) _ (lift x y).left z J hJ
    have := (ev (lift x y) hJ).symm.trans (key.trans (val_one _))
    rwa [lift_fst, lift_snd] at this
  · let p₀ := x3 A 0
    let p₁ := x3 A 1
    let p₂ := x3 A 2
    have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 A) {z : T'.left} {J}, Good P z J →
        val (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ β.law1 (lift p₀ (lift p₁ p₂)).left)
          (LB.pullGen P _ _ s (lift (p₀ * p₁) p₂).left)) σ.left z J =
          val β.law1 (lift (σ ≫ p₀) (lift (σ ≫ p₁) (σ ≫ p₂))).left z J * val s (lift (σ ≫ (p₀ * p₁)) (σ ≫ p₂)).left z J ∧
        val (LB.mulGen P _ _ _ _ (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ s (lift p₀ p₂).left)
          (LB.pullGen P _ _ s (lift p₁ p₂).left)) (LB.pullGen P _ _ β.law2 (lift p₂ (lift p₀ p₁)).left)) σ.left z J =
          val s (lift (σ ≫ p₀) (σ ≫ p₂)).left z J * val s (lift (σ ≫ p₁) (σ ≫ p₂)).left z J *
            val β.law2 (lift (σ ≫ p₂) (lift (σ ≫ p₀) (σ ≫ p₁))).left z J := fun σ z J hJ =>
      ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull₃ β.law1 σ hJ _ _ _) (val_pull₂ s σ hJ _ _)),
        (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) (val_pull₂ s σ hJ _ _) (val_pull₂ s σ hJ _ _))) (val_pull₃ β.law2 σ hJ _ _ _))⟩
    let e : 𝟙_ (Over S) ⟶ G3 A := lift 1 (lift 1 1)
    have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
    have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
    have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
    have sj : Function.Surjective ((snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom).appTop.hom :=
      surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)
    have he : e.left ≫ (snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by
      rw [Over.w, Over.w]; exact Over.w e
    let ρ : T ⟶ G3 A := lift x (lift x' y)
    have r₀ : ρ ≫ p₀ = x := by simp [ρ, p₀, x3]
    have r₁ : ρ ≫ p₁ = x' := by simp [ρ, p₁, x3]
    have r₂ : ρ ≫ p₂ = y := by simp [ρ, p₂, x3]
    have o₁ : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
    have s₁ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
    have := (ev ρ hJ).1.symm.trans (Eq.trans (gen_unique' β.isLB (fun V _ k => by
        refine (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := ULift.{0} (Fin 3)) (U := V) _
          (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_sym p₀ p₂ k) (prod_sym p₁ p₂ k))
          (biextension_second_law_product p₂ p₀ p₁ k)).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := ULift.{0} (Fin 3)) (K' := Fin 2) (U := V) _
            (biextension_first_law_product p₀ p₁ p₂ k) (prod_sym (p₀ * p₁) p₂ k)).symm)
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel) _ e.left he sj
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ β.isGen1 _) (DVR.pullGen_isGen _ _ _ _ hs _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.pullGen_isGen _ _ _ _ hs _) (DVR.pullGen_isGen _ _ _ _ hs _)) (DVR.pullGen_isGen _ _ _ _ β.isGen2 _))
      (fun y I hI => by
        refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
        rw [o₁, e₀, e₁, e₂, h1 _ y I hI, law_origin β hI, _root_.mul_one, _root_.one_mul, _root_.one_mul])
      _ ρ.left z J hJ) (ev ρ hJ).2)
    rwa [s₁, r₀, r₁, r₂] at this

end GlobalTheory.BiextSym
end
end
