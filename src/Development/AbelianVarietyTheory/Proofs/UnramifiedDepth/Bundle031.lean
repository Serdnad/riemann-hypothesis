module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle024
public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle027
public import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle025
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Nat.Defs
public import ReciprocityTheory.DualLattices.Bundle022
public import ReciprocityTheory.DualLattices.Bundle012
public import ReciprocityTheory.DualLattices.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DualTowerMapExists
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle019
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle018
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalChart
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle017
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTateMatricesLink
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FinEtaleFormallyUnramified
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FinOfLocalAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle020
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ModPToValuationResidueFieldSurjective
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilpotentCoordinates
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicEndApply
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle003
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Formalism.IncomingBounds.Bundle001
import Development.AbelianVarietyTheory.Statements.ChartPoints.ChartPt
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import ReciprocityTheory.DualLattices.Bundle023

@[expose] public section

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

theorem _root_.GlobalTheory.T.exists_unimodular_mul_eq_neg_of_independent_mod_maximal : ∀ (C : Type) [Field C] (V : VF C) (n n0 : ℕ) (Φ : Fin n → Fin n0 → C), (∀ b c, V.Ge 0 (Φ b c)) → IndepMod V (fun c b => Φ b c) → n0 ≤ n ∧ ∃ Y : Matrix (Fin n) (Fin n) C, (∀ b b', V.Ge 0 (Y b b')) ∧ V.v Y.det = 0 ∧ ∀ (b : Fin n) (c : Fin n0), b.val < n0 → ∑ b', Y b b' * Φ b' c = if b.val = c.val then -1 else 0 := by
  first | exact @GlobalTheory.exists_unimodular_mul_eq_neg_of_indepMod | exact GlobalTheory.exists_unimodular_mul_eq_neg_of_indepMod | (intros; apply GlobalTheory.exists_unimodular_mul_eq_neg_of_indepMod <;> assumption)
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

theorem _root_.GlobalTheory.T.powerSemilinear_rank_nullity_mod_maxIdeal : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (σ : Type) (m k Q : ℕ), 1 ≤ Q → ∀ Y : Fin m → σ → C, (∀ δ x, V.Ge 0 (Y δ x)) → (∀ (N : ℕ) (x : Fin N → Fin m → C), (∀ ν δ, V.Ge 0 (x ν δ)) → IndepMod V x → (∀ ν s, V.MM (∑ δ, x ν δ ^ Q * Y δ s)) → N ≤ k) → ∃ (m' : ℕ) (cc : Fin m' ↪ Fin m), m ≤ m' + k ∧ IndepMod V (fun ν => Y (cc ν)) := by
  first | exact @GlobalTheory.SemilinearNullity.rank_nullity | exact GlobalTheory.SemilinearNullity.rank_nullity | (intros; apply GlobalTheory.SemilinearNullity.rank_nullity <;> assumption)
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

theorem _root_.GlobalTheory.T.coeff_leafGauge_sub_mainTerm_eq_zero_on_first_axis : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) (i : ℕ) (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C) (Φ : ι' → ι → C) (μ : ι ⊕ ι' →₀ ℕ), (∀ b, μ (Sum.inr b) = 0) → MvPowerSeries.coeff μ (X.hM g a i e v' - mainM V i Φ) = 0 := by
  first | exact @GlobalTheory.MainTerm.Axis.coeff_hM_sub_mainM_eq_zero | exact GlobalTheory.MainTerm.Axis.coeff_hM_sub_mainM_eq_zero | (intros; apply GlobalTheory.MainTerm.Axis.coeff_hM_sub_mainM_eq_zero <;> assumption)
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

theorem _root_.GlobalTheory.T.pderiv_leafGauge_eq_pairing_add_integral : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d) (i : ℕ), Odd i → i < d → ∀ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C), (∀ c x, (X.G g).ty (Sum.inl x) ≠ a → e c x = 0) → (∀ b k, V.Ge 0 (v' b k)) → (∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + (i : ZMod d) → v' b k = 0) → ∀ b : ι', ∃ γ : MvPowerSeries (WV I) C, (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) ∧ MvPowerSeries.pderiv (R := C) (Sum.inr b) (X.hM g a i e v') = MvPowerSeries.subst (fun w : WV I => hPullW (upG w.1 (t w.1 w.2)) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))) γ + ∑ κ : J g, (∑ k, X.pair g κ k * v' b k) • hPullW (upG g ((S g).ze (t g) κ)) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) := by
  first | exact @GlobalTheory.GaugeDeriv.pderiv_hM | exact GlobalTheory.GaugeDeriv.pderiv_hM | (intros; apply GlobalTheory.GaugeDeriv.pderiv_hM <;> assumption)
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

theorem _root_.GlobalTheory.T.coeffIntegralOnExponents_subst_of_lower_set : ∀ (C : Type) [Field C] (V : VF C) (σ τ : Type) [Fintype σ] [Fintype τ] (P : (σ →₀ ℕ) → Prop), (∀ μ ν, ν ≤ μ → P μ → P ν) → ∀ (γ : MvPowerSeries τ C) (T : τ → MvPowerSeries σ C), (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) → (∀ w, MvPowerSeries.constantCoeff (T w) = 0) → (∀ w μ, P μ → V.Ge 0 (MvPowerSeries.coeff μ (T w))) → ∀ μ, P μ → V.Ge 0 (MvPowerSeries.coeff μ (MvPowerSeries.subst T γ)) := by
  first | exact @GlobalTheory.LowerSubst.subst_int_on_lower | exact GlobalTheory.LowerSubst.subst_int_on_lower | (intros; apply GlobalTheory.LowerSubst.subst_int_on_lower <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChTor

namespace GlobalTheory.ChTor

theorem exists_tate_of_character :
    ∀ (Γ : Type) [Group Γ] (U : Type) [CommGroup U] (p : ℕ), 1 ≤ p → (∀ a b : Γ, a * b = b * a) → ∀ e : ℕ → Γ → Γ → U, (∀ k : ℕ, 1 ≤ k → (∀ (l : ℕ) (z s : Γ), 1 ≤ l → z ^ k = 1 → s ^ (k * l) = 1 → e (k * l) z s = e k z (s ^ l)) ∧ ∀ κ : Γ → U, (∀ z z', z ^ k = 1 → z' ^ k = 1 → κ (z * z') = κ z * κ z') → ∃! s : Γ, s ^ k = 1 ∧ ∀ z, z ^ k = 1 → e k z s = κ z) → ∀ κ : Γ → U, (∀ z z', (∃ m, z ^ (p ^ m) = 1) → (∃ m, z' ^ (p ^ m) = 1) → κ (z * z') = κ z * κ z') → ∃ s : ℕ → Γ, (∀ m, s m ^ (p ^ m) = 1 ∧ s (m + 1) ^ p = s m) ∧ ∀ m z, z ^ (p ^ m) = 1 → e (p ^ m) z (s m) = κ z := by
  intro Γ _ U _ p hp hc e he κ hκ
  have hpm : ∀ m : ℕ, 1 ≤ p ^ m := fun m => Nat.one_le_pow _ _ hp
  have key : ∀ m : ℕ, ∃! s : Γ, s ^ (p ^ m) = 1 ∧ ∀ z, z ^ (p ^ m) = 1 → e (p ^ m) z s = κ z :=
    fun m => (he (p ^ m) (hpm m)).2 κ (fun z z' hz hz' => hκ z z' ⟨m, hz⟩ ⟨m, hz'⟩)
  choose s hs hu using key
  refine ⟨s, fun m => ⟨(hs m).1, ?_⟩, fun m => (hs m).2⟩
  have h1 : s (m + 1) ^ (p ^ m * p) = 1 := by rw [← pow_succ]; exact (hs (m + 1)).1
  apply hu m
  refine ⟨by rw [← pow_mul, mul_comm]; exact h1, fun z hz => ?_⟩
  rw [← (he (p ^ m) (hpm m)).1 p z (s (m + 1)) hp hz h1, ← pow_succ]
  apply (hs (m + 1)).2
  rw [pow_succ, pow_mul, hz, one_pow]

end GlobalTheory.ChTor
end

section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodDatum

theorem exists_basis_of_card (p : ℕ) [hp : Fact p.Prime] (g : ℕ) (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (hcV : Nat.card V = p ^ (2 * g)) :
    ∃ f : Ix g → V, ∀ x : V, ∃! t : Ix g → ZMod p, x = ∑ j, (t j).val • f j := by
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hcV]; exact pow_ne_zero _ hp.out.ne_zero)
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hrk : Module.finrank (ZMod p) V = Fintype.card (Ix g) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [hcV, Nat.card_zmod] at h
    have h2 := Nat.pow_right_injective hp.out.two_le h
    rw [← h2, Fintype.card_sum, Fintype.card_fin, two_mul]
  let b : Module.Basis (Ix g) (ZMod p) V :=
    (Module.finBasisOfFinrankEq (ZMod p) V hrk).reindex (Fintype.equivFin (Ix g)).symm
  have hsm : ∀ (t : ZMod p) (y : V), t.val • y = t • y := fun t y => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  refine ⟨b, fun x => ⟨b.equivFun x, ?_, fun t ht => ?_⟩⟩
  · simp only [hsm]
    rw [← b.equivFun_symm_apply, LinearEquiv.symm_apply_apply]
  · simp only [hsm] at ht
    rw [← b.equivFun_symm_apply] at ht
    rw [ht, LinearEquiv.apply_symm_apply]

theorem exists_compatible_basis (p : ℕ) [hp : Fact p.Prime] (g : ℕ) (Γ : Type) [AddCommGroup Γ]
    (hdiv : ∀ x : Γ, ∃ y, p • y = x) (hcard : Nat.card {x : Γ // p • x = 0} = p ^ (2 * g)) :
    ∃ τ : Ix g → ℕ → Γ, (∀ i n, (p ^ (n + 1)) • τ i n = 0) ∧ (∀ i n, τ i n = p • τ i (n + 1)) ∧
      ∀ x : Γ, p • x = 0 → ∃! t : Ix g → ZMod p, x = ∑ j, (t j).val • τ j 0 := by
  obtain ⟨V, hV⟩ : ∃ V : AddSubgroup Γ, ∀ x : Γ, x ∈ V ↔ p • x = 0 :=
    ⟨(nsmulAddMonoidHom p : Γ →+ Γ).ker, fun x => Iff.rfl⟩
  have hcV : Nat.card V = p ^ (2 * g) :=
    (Nat.card_congr (Equiv.subtypeEquivRight hV)).trans hcard
  obtain ⟨b, hb⟩ := @exists_basis_of_card p _ g V _
    (AddCommGroup.zmodModule (fun x => Subtype.ext ((hV _).1 x.2))) hcV
  choose d hd using hdiv
  let τ : Ix g → ℕ → Γ := fun i n => d^[n] (b i : Γ)
  have hτp : ∀ i n, τ i n = p • τ i (n + 1) := fun i n => by
    simp only [τ, Function.iterate_succ_apply', hd]
  have hsum : ∀ t : Ix g → ZMod p, ((∑ j, (t j).val • b j : V) : Γ) = ∑ j, (t j).val • τ j 0 :=
    fun t => by
      rw [AddSubmonoidClass.coe_finsetSum]
      rfl
  refine ⟨τ, fun i n => ?_, hτp, fun x hx => ?_⟩
  · induction n with
    | zero => rw [zero_add, pow_one]; exact (hV _).1 (b i).2
    | succ n ih => rw [pow_succ, mul_smul, ← hτp i n, ih]
  · obtain ⟨t, ht, hu⟩ := hb ⟨x, (hV x).2 hx⟩
    refine ⟨t, ?_, fun t' ht' => hu t' (Subtype.ext ?_)⟩
    · exact (congrArg Subtype.val ht).trans (hsum t)
    · exact ht'.trans (hsum t').symm

theorem main :
  (∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) (g : ℕ)
    (G : Over (Spec (CommRingCat.of (Ainf.R0 p O ε)))) [GrpObj G] [IsCommMonObj G] (B : BX (Ainf.R0 p O ε))
    (e : ∀ R : LAlg (Ainf.R0 p O ε), B.G R → (sp (R₀ := (Ainf.R0 p O ε)) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg (Ainf.R0 p O ε)} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    SmoothOfRelativeDimension g G.hom → IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left →
    (∀ x : B.G (Ainf.ainfTowerL p O hv ε hε).O, ∃ y, p • y = x) → Nat.card {x : B.G (Ainf.ainfTowerL p O hv ε hε).O // p • x = 0} = p ^ (2 * g) →
    (∀ x : B.G (Ainf.ainfTowerL p O hv ε hε).O, p • x = 0 → (∀ y : B.G (Ainf.ainfTowerL p O hv ε hε).O, p • y = 0 → B.IsPairing p x y 1) → x = 0) →
    ∀ [Algebra ℤ_[p] ((Ainf.ainfTowerL p O hv ε hε).O : Type)] (O₀ : Type) [CommRing O₀] (cj : O₀ ≃ₐ[ℤ] O₀) (Ad : O₀ → OAdj B (Ainf.ainfTowerL p O hv ε hε).O),
    (∀ a, (Ad a).ab = (Ad (cj a)).a) → (∀ a, cj (cj a) = a) →
    (∀ {R : LAlg (Ainf.R0 p O ε)} (s : LHom (Ainf.ainfTowerL p O hv ε hε).O R) (x : B.G R), (Ad 1).a.f s x = x ∧ ∀ a b, (Ad (a + b)).a.f s x = (Ad a).a.f s x + (Ad b).a.f s x ∧
      (Ad (a * b)).a.f s x = (Ad a).a.f s ((Ad b).a.f s x)) →
    ∃ (Dt : DualTower (Ainf.ainfTowerL p O hv ε hε)) (D : Dat p g B (Ainf.ainfTowerL p O hv ε hε) Dt (ℤ_[p] ⊗[ℤ] O₀) (Algebra.TensorProduct.congr (AlgEquiv.refl : ℤ_[p] ≃ₐ[ℤ_[p]] ℤ_[p]) cj) (Ainf.ainfTowerL p O hv ε hε).c),
      D.H.P = 0 ∧ D.H.PL = 0 ∧
      (∀ a {R S : LAlg (Ainf.R0 p O ε)} (s : LHom (Ainf.ainfTowerL p O hv ε hε).O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker),
      (∀ k, (m k : (R : Type)) = s.1 (D.H.ρL (1 ⊗ₜ[ℤ] a) k l) * i) →
      (Ad a).a.f s (B.tg π hπ (D.ch.gb l ⊗ₜ[(Ainf.R0 p O ε)] i)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[(Ainf.R0 p O ε)] m k)) ∧
      ∀ a j n, (Ad a).a.f (LHom.id (Ainf.ainfTowerL p O hv ε hε).O) (D.L.τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (D.H.ρ (1 ⊗ₜ[ℤ] a) k j)).val • D.L.τ k n) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε g G _ _ B e hbij hadd hnat hsm hfin hflat hdiv hcard hperf
    _ O₀ _ cj Ad hab hcj hAd
  haveI : IsLocalRing (Ainf.R0 p O ε) := WdAinf.ainf_thetaQuotRing_isLocalRing p O hv ε hε
  haveI : IsDomain ((Ainf.ainfTowerL p O hv ε hε).O : Type) := Ainf.ainfTower_isDomain p O hv ε hε
  have hsm' : Smooth G.hom := SmoothOfRelativeDimension.smooth g G.hom
  obtain ⟨K, wd, hnil, hK, hKl⟩ :=
    GlobalTheory.wData_ainfTower_exists GlobalTheory.WittQuot.teichmuller_quot p O hv ε hε
  obtain ⟨ch⟩ := GlobalTheory.FormalChartOf.exists_formalChart GlobalTheory.NilCoord.nilpotent_coordinates
    (GlobalTheory.ChLaw.groupLaw_powerSeries GlobalTheory.nEval_basic
      (GlobalTheory.exists_series_of_natural_on_nilpotent GlobalTheory.nEval_basic))
    G g B e hbij hadd hnat hsm K hK hKl
  have sm := GlobalTheory.SmoothNilLift.main G B e hbij hadd hnat hsm' K wd.W wd.ρW hnil
  obtain ⟨fin⟩ := @GlobalTheory.FinOf.main GlobalTheory.finRep_kernel_mul_finite_free GlobalTheory.finite_algebra_split_local
    GlobalTheory.finEtale_main _ _ G _ _ (Ainf.ainfTowerL p O hv ε hε).O p B e hbij hadd hnat hfin hflat hsm'
    C _ _ _ v (inferInstanceAs (Algebra O C)) hv (Fact.out : p.Prime).ne_zero
  obtain ⟨Dt⟩ := GlobalTheory.exists_dualTower (Ainf.ainfTowerL p O hv ε hε)
  obtain ⟨τ, hτ, hτp, hbas⟩ := exists_compatible_basis p g _ hdiv hcard
  obtain ⟨dL, hdL⟩ := GlobalTheory.exists_endDifferential_ringHom B _ ch.gb O₀ (fun a => (Ad a).a) hAd
  obtain ⟨A, H, L, hP, hPL, hL, hρL, hρ⟩ := GlobalTheory.exists_tateMatrices_link GlobalTheory.tate_basis_matrix
    GlobalTheory.tateBasis_gram GlobalTheory.PadicOrderAction.main B (Ainf.ainfTowerL p O hv ε hε) Dt ch.gb O₀ cj Ad dL
    (WdAinf.thetaBar_surj p O hv ε hε) hab hcj hAd hdL
    (fun n => Ideal.mk_ker (I := Ideal.span {(p : O) ^ (n + 1)}))
    (fun n => IsPrimitiveRoot.coe_units_iff.1 (Ainf.zeta_primitive p O hv ε hε n))
    (fun n => Units.ext (Ainf.zeta_succ_pow p O ε n))
    τ hτ hτp hbas hperf
  refine ⟨Dt,
    { K := K
      ρO := wd.ρ1.comp ((Ainf.ainfTowerL p O hv ε hε).q 0)
      ch := ch
      wd := wd
      ρO_eq := rfl
      sm := sm
      fin := fin
      A := A
      H := H
      L := L
      tower_zero_surjective := surjective_ainfTower_zero p O hv ε hε
      tower_zero_ker := ker_ainfTower_zero p O hv ε hε
      zeta0 := ainf_zeta0 p O hv ε hε }, hP, hPL, ?_, ?_⟩
  · intro a R S s π hπ l i m hm
    exact hdL a s π hπ l i m (fun k => by rw [hm k]; exact congrArg (fun M => s.1 (M k l) * (i : (R : Type))) (hρL a))
  · intro a j n
    subst hL
    exact hρ a j n

end GlobalTheory.PeriodDatum
end
end
