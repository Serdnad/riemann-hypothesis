module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle219
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle290
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle291
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle314

@[expose] public section

section

open Matrix

theorem _root_.GlobalTheory.T.zarhin_kernel_linearAlgebra_trivial : ∀ (d : ℕ) (GA GB : Type) [CommGroup GA] [CommGroup GB] (f : GA →* GB) (g : GB →* GA), 0 < d → (∀ a, g (f a) = a ^ d) → ∀ (u : Fin 4 → GA) (v : Fin 4 → GB), (∀ i, f (u i) * ∏ j, v j ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ j, f (∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i) * v j ^ d = 1) → ((∀ j, v j = 1) → ∀ j, ∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ i, u i = 1) ∧ ∀ j, v j = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.zarhin_kernel_trivial) | (exact GlobalTheory.ZarhinFam.zarhin_kernel_trivial) | (intros; apply GlobalTheory.ZarhinFam.zarhin_kernel_trivial  <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages

theorem _root_.GlobalTheory.T.glued_blocks_mul_inv_integral_unit_det : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (ι : Type) (lab : Fin d → ι)
    (S : ι → Finset (Fin d)) (x y : ι → Matrix (Fin d) (Fin d) C),
    (∀ i a, a ∈ S i → lab a = i) →
    (∀ i a b, x i a b ≠ 0 → a ∈ S i ∧ b ∈ S i) → (∀ i a b, y i a b ≠ 0 → a ∈ S i ∧ b ∈ S i) →
    (∀ i a b, IsIntV v (x i a b)) → (∀ i a b, IsIntV v (y i a b)) →
    (∀ i a c, a ∈ S i → c ∈ S i → ∑ b, x i a b * y i b c = if a = c then 1 else 0) →
    (∀ a b, IsIntV v (glue lab S x a b)) ∧ glue lab S x * glue lab S y = 1 ∧
      v (glue lab S x).det = 0 := by
  first | exact @GlobalTheory.GlueBlocks.glue_mul_glue_inv | exact GlobalTheory.GlueBlocks.glue_mul_glue_inv | (intros; apply GlobalTheory.GlueBlocks.glue_mul_glue_inv <;> assumption)
end

section

open GlobalTheory.CasimirOrder

theorem _root_.GlobalTheory.T.integralCasimirElement_central : ∀ {O : Type} [Ring O] {r : ℕ} (x : Module.Basis (Fin r) ℤ O) (s : O →+ O) (φ : O →+ ℤ), (∀ a b, s (a * b) = s b * s a) → (∀ a, s (s a) = a) → (∀ a b, φ (a * b) = φ (b * a)) → (∀ a, φ (s a) = φ a) → (∀ a, a ≠ 0 → 0 < φ (s a * a)) → ∀ a, a * casimir (⇑x) s φ = casimir (⇑x) s φ * a := by
  first | (exact @GlobalTheory.CasimirOrder.casimir_central) | (exact GlobalTheory.CasimirOrder.casimir_central) | (intros; apply GlobalTheory.CasimirOrder.casimir_central  <;> assumption)
end

section

open GlobalTheory.CasimirOrder

theorem _root_.GlobalTheory.T.integralCasimirElement_mul_pos : ∀ {O : Type} [Ring O] {r : ℕ} (x : Module.Basis (Fin r) ℤ O) (s : O →+ O) (φ : O →+ ℤ), (∀ a b, s (a * b) = s b * s a) → (∀ a, s (s a) = a) → (∀ a b, φ (a * b) = φ (b * a)) → (∀ a, φ (s a) = φ a) → (∀ a, a ≠ 0 → 0 < φ (s a * a)) → ∀ u, u ≠ 0 → 0 < φ (s (casimir (⇑x) s φ * u) * u) := by
  first | (exact @GlobalTheory.CasimirOrder.casimir_mul_pos) | (exact GlobalTheory.CasimirOrder.casimir_mul_pos) | (intros; apply GlobalTheory.CasimirOrder.casimir_mul_pos  <;> assumption)
end

section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory.FormalOrigin.Extend

theorem list_foldr_iterate_single_of_nodup {A : Type} {n : ℕ} (d : Fin n → A → A) (j : Fin n) (f : A) :
    ∀ l : List (Fin n), l.Nodup →
      l.foldr (fun i g => (d i)^[(Finsupp.single j 1 : Fin n →₀ ℕ) i] g) f = if j ∈ l then d j f else f := by
  intro l hl
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    rw [List.foldr_cons, ih hl.2]
    by_cases hij : i = j
    · subst hij
      simp [hl.1]
    · have hji : j ≠ i := fun h => hij h.symm
      simp [Finsupp.single_apply, hij, hji]

theorem taylor_coeff_single (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B)
    (ds : Fin n → Derivation ℤ A A) (j : Fin n) (f : A) :
    MvPowerSeries.coeff (Finsupp.single j 1) (taylor ev (fun i => ⇑(ds i)) f) = ev (ds j f) := by
  have hit : iterOp (fun i => ⇑(ds i)) (Finsupp.single j 1) f = ds j f := by
    unfold iterOp
    rw [list_foldr_iterate_single_of_nodup _ j f _ (List.nodup_finRange n)]
    simp [List.mem_finRange]
  have hprod : (∏ i, (((Finsupp.single j 1 : Fin n →₀ ℕ) i).factorial : ℚ)) = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    by_cases h : j = i
    · subst h; simp
    · simp [Finsupp.single_apply, h]
  show (∏ i, (((Finsupp.single j 1 : Fin n →₀ ℕ) i).factorial : ℚ))⁻¹ • ev (iterOp (fun i => ⇑(ds i)) (Finsupp.single j 1) f) = _
  rw [hit, hprod, inv_one, one_smul]

end GlobalTheory.FormalOrigin.Extend
end

section

open IsLocalRing GlobalTheory.FormalOrigin

theorem _root_.GlobalTheory.T.derivationTaylorPowerSeries_of_derivations_kill : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A) (c : A), (∀ i, ds i c = 0) → taylor ev (fun i => ⇑(ds i)) c = MvPowerSeries.C (ev c) := by
  first | exact @GlobalTheory.FormalOrigin.taylor_const | exact GlobalTheory.FormalOrigin.taylor_const | (intros; apply GlobalTheory.FormalOrigin.taylor_const <;> assumption)
end

section

open IsLocalRing GlobalTheory.FormalOrigin

theorem _root_.GlobalTheory.T.derivationTaylorPowerSeries_derivation_eq_pderiv : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A), (∀ a b f, ds a (ds b f) = ds b (ds a f)) → ∀ a f, taylor ev (fun i => ⇑(ds i)) (ds a f) = MvPowerSeries.pderiv (R := B) a (taylor ev (fun i => ⇑(ds i)) f) := by
  first | exact @GlobalTheory.FormalOrigin.TaylorDeriv.taylor_deriv_eq_pderiv | exact GlobalTheory.FormalOrigin.TaylorDeriv.taylor_deriv_eq_pderiv | (intros; apply GlobalTheory.FormalOrigin.TaylorDeriv.taylor_deriv_eq_pderiv <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.isAffineCombinationInChart_unique : ∀ (Y : Scheme.{0}) (V : Y.Opens), IsAffineOpen V → ∀ (S : Type) [CommRing S] (ι : Type) [Fintype ι]
    (u c c' : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S),
    GlobalTheory.SecGlue.IsCombIn V u c w a → GlobalTheory.SecGlue.IsCombIn V u c' w a → c = c' := by
  first | exact @GlobalTheory.SecGlue.combIn_unique | exact GlobalTheory.SecGlue.combIn_unique | (intros; apply GlobalTheory.SecGlue.combIn_unique <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.isAffineCombinationInChart_specMap_comp : ∀ (Y : Scheme.{0}) (V : Y.Opens) (S S' : Type) [CommRing S] [CommRing S'] (g : S →+* S') (ι : Type) [Fintype ι]
    (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S), GlobalTheory.SecGlue.IsCombIn V u c w a →
    GlobalTheory.SecGlue.IsCombIn V (spMap g ≫ u) (spMap g ≫ c) (fun i => spMap g ≫ w i) (fun i => g (a i)) := by
  first | exact @GlobalTheory.SecGlue.isCombIn_spMap_comp | exact GlobalTheory.SecGlue.isCombIn_spMap_comp | (intros; apply GlobalTheory.SecGlue.isCombIn_spMap_comp <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_affineCombination_squareZero_lifts_chart : ∀ (Y : Scheme.{0}) (V : Y.Opens), IsAffineOpen V →
    ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (ι : Type) [Fintype ι] (u : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S), u ⁻¹ᵁ V = ⊤ →
    (∀ i, spMap q ≫ w i = spMap q ≫ u) →
    ∃ c : Sp S ⟶ Y, GlobalTheory.SecGlue.IsCombIn V u c w a ∧ spMap q ≫ c = spMap q ≫ u ∧
      ∀ (R' : Type) [CommRing R'] (p : Y ⟶ Sp R'), (∀ i, w i ≫ p = u ≫ p) → c ≫ p = u ≫ p := by
  first | exact @GlobalTheory.SecGlue.CombEx.exists_comb | exact GlobalTheory.SecGlue.CombEx.exists_comb | (intros; apply GlobalTheory.SecGlue.CombEx.exists_comb <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_smooth_section_lift_basicOpen_affine : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ p : PrimeSpectrum R, ∃ f ∉ p.asIdeal, ∃ V : X.left.Opens, IsAffineOpen V ∧ GlobalTheory.SecLift.LiftIn π X g₀ f V := by
  first | exact @GlobalTheory.SecLift.exists_liftIn | exact GlobalTheory.SecLift.exists_liftIn | (intros; apply GlobalTheory.SecLift.exists_liftIn <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

theorem _root_.GlobalTheory.T.exists_basicOpen_cover_idealRepresents : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ z : S, ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ K : Ideal Γ(S, U),
    ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'), P R' (spMap f ≫ hU.fromSpec) ↔ K ≤ RingHom.ker f) →
  ∀ (V : S.Opens) (hV : IsAffineOpen V), ∃ s : Finset Γ(S, V), Ideal.span (s : Set Γ(S, V)) = ⊤ ∧
    ∀ a ∈ s, ∃ J : Ideal (Localization.Away a),
      Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
        ptQ P V hV R' (h.comp (algebraMap Γ(S, V) (Localization.Away a)))) J := by
  first | exact @GlobalTheory.PtClosed.affine_local_represents | exact GlobalTheory.PtClosed.affine_local_represents | (intros; apply GlobalTheory.PtClosed.affine_local_represents; all_goals assumption)
end
