module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShiftedSectionDivMonomialOverChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle209
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle201
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2826
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermsWitnessesBaseChangeAlongTower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3223
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceUniqueLiftAnyField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3222
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3220
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_shifted_section_div_monomial_over_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ (mu α : P.D.toPre.X) (n : Fin m → ℕ) (ψ₀ : LB.Gen (LB.LinComb P.D.toPre.P.L (K := PUnit) (fun _ => (P.D.toPre.c mu).left) fun _ => -1)) τ₀, GlobalTheory.LogKSChart.IsUnitPart P.D.toPre (bdParam k m d) gam mu n ψ₀ → IsUnitTau P.D.toPre (bdParam k m d) gam mu α τ₀ → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → (∀ i, 0 ≤ (e : ℤ) * n i + gam i mu α) ∧ ∀ σ : P.D.toPre.SecB e α, ∃ σ₁ σ₁u : P.D.toPre.SecB e (α + e • mu), ShiftEq P.D.toPre e mu α σ σ₁ 0 σ₁ ∧ (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁ x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ ((e : ℤ) * n i + gam i mu α).toNat)) * sval σ₁u x z J) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (ChartRing k m d)) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁u (r ≫ (P.D.toPre.c 0).left) z J = ((val ψ₀ r z J) ^ e * val τ₀ r z J * (val P.D.toPre.rig r z J) ^ e).val * sval σ (r ≫ (P.D.toPre.c mu).left) z J := by
  first | exact @GlobalTheory.ShiftUnitPart.exists_shift_div_monomial | exact GlobalTheory.ShiftUnitPart.exists_shift_div_monomial | (intros; apply GlobalTheory.ShiftUnitPart.exists_shift_div_monomial <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.heatOperator_connection_closedFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (e : ℕ), 1 ≤ e → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.D.toPre.P.A.left), IsGrpPullback A₀ P.D.toPre.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∃ (V : h.J → P.D.toPre.P.A.left.Opens) (ed : ∀ W : P.D.toPre.P.A.left.Opens, Γ(P.D.toPre.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.D.toPre.P.A P.D.toPre.P.L A₀ m₀ (fun r => (ρ r).snd) V h.j ed pb ∧ (∀ i, h.W i = Y.q.left ⁻¹ᵁ V i) ∧ ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → (∀ (W : P.D.toPre.P.A.left.Opens) (f : Γ(P.D.toPre.P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) → ∃ c : P.D.toPre.X →+ k, ∀ (α : P.D.toPre.X) (σ σ' : P.D.toPre.SecB e α), TActs Y h e α σ σ' → ∀ (i : Fin 4 → h.J) (T : Fin 4 → (A₀.left ⟶ A₀.left)), (∀ j, T j ≫ m₀ = m₀ ≫ P.D.toPre.famφB α j) → (∀ j, T j ≫ A₀.hom = A₀.hom) → ∀ O : A₀.left.Opens, O ≤ m₀ ⁻¹ᵁ LB.wchart P.D.toPre.P.L (P.D.toPre.famφB α) (fun j => h.j (i j)) → (∀ j, O ≤ T j ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i j))) → pbT m₀ (σ'.f (fun j => h.j (i j))) O = 2 * (e : Γ(A₀.left, O)) * (rsT (ed _ (σ.f (fun j => h.j (i j)))) O + pbT m₀ (σ.f (fun j => h.j (i j))) O * (∑ j, ((DegPre.famε e j : ℤ) : Γ(A₀.left, O)) * pbT (T j) (pb (i j)) O + constFn A₀.hom O (c α))) := by
  first | exact @GlobalTheory.HeatConn.heat_connection | exact GlobalTheory.HeatConn.heat_connection | (intros; apply GlobalTheory.HeatConn.heat_connection <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.heatOperator_shift_div_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ (e : ℕ), 1 ≤ e → ∀ (mu α : P.D.toPre.X) (N : Fin m → ℕ) (σ σ' : P.D.toPre.SecB e α) (σ₁ σ₁u σ₁' σ₁u' : P.D.toPre.SecB e (α + e • mu)), TActs Y h e α σ σ' → ShiftEq P.D.toPre e mu α σ σ₁ 0 σ₁ → ShiftEq P.D.toPre e mu α σ' σ₁' 0 σ₁' → (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁ x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval σ₁u x z J) → (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁' x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval σ₁u' x z J) → ∃ σ₁u'' : P.D.toPre.SecB e (α + e • mu), TActs Y h e (α + e • mu) σ₁u σ₁u'' ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁u'' x z J = sval σ₁u' x z J - gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (2 * (e : ChartRing k m d) * ∑ i, (N i : ChartRing k m d) * q i)) * sval σ₁u x z J := by
  first | exact @GlobalTheory.Heat.heat_div_monomial | exact GlobalTheory.Heat.heat_div_monomial | (intros; apply GlobalTheory.Heat.heat_div_monomial <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.Thru

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_stalkHom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (z : M.Z) :
    spMap (M.stalkHom z) ≫ M.Z.fromSpecStalk z = M.pt := by
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) M.pt
  have h2 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (M.pt_specializes (IsLocalRing.closedPoint Ω) z)
  refine Eq.trans ?_ h1
  rw [← h2, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem isFractionRing_stalk {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (z : M.Z) :
    letI : Algebra (M.Z.presheaf.stalk z) Ω := (M.stalkHom z).toAlgebra
    IsFractionRing (M.Z.presheaf.stalk z) Ω := by
  letI : Algebra (M.Z.presheaf.stalk z) Ω := (M.stalkHom z).toAlgebra
  have : FaithfulSMul (M.Z.presheaf.stalk z) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (M.stalkHom_injective z)
  refine IsFractionRing.of_field _ _ fun x => ?_
  obtain ⟨a, b, -, hx⟩ := IsFractionRing.div_surjective (A := M.O z) x
  refine ⟨(M.stalkEquiv z).symm a, (M.stalkEquiv z).symm b, ?_⟩
  have h : ∀ c : M.O z, algebraMap (M.Z.presheaf.stalk z) Ω ((M.stalkEquiv z).symm c) = c := fun c => by
    change M.stalkHom z _ = _
    rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
  rw [h, h, ← hx]
  rfl

theorem exists_cdvr_thru {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] [CharZero Ω]
    (M : RatModel o Ω) (z : M.Z) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : M.Z.presheaf.stalk z →+* V)
      (e : Ω →+* FractionRing V), IsAdicComplete (maximalIdeal V) V ∧ CharZero V ∧ IsLocalHom φ ∧
      (∀ r, e (M.stalkHom z r) = algebraMap V (FractionRing V) (φ r)) ∧
      jK V ≫ spMap φ ≫ M.Z.fromSpecStalk z = spMap e ≫ M.pt := by
  letI : Algebra (M.Z.presheaf.stalk z) Ω := (M.stalkHom z).toAlgebra
  haveI := isFractionRing_stalk M z
  haveI : CharZero (M.Z.presheaf.stalk z) := (M.stalkHom z).charZero
  haveI := M.lft
  haveI : IsLocallyNoetherian (Sp o) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of o)))
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨V₀, _, _, _, φ₀, ⟨hdvr, hcpl, hchar⟩, hinj₀, hmax⟩ :=
    GlobalTheory.ClosedPol.exists_cdvr (M.Z.presheaf.stalk z) (maximalIdeal _)
  have hl : IsLocalHom φ₀ := ((IsLocalRing.local_hom_tfae φ₀).out 1 5).2 hmax
  have hg₀ : Function.Injective ((algebraMap V₀ (FractionRing V₀)).comp φ₀) :=
    (IsFractionRing.injective V₀ (FractionRing V₀)).comp hinj₀
  let emb : Ω →+* FractionRing V₀ := IsFractionRing.lift (A := M.Z.presheaf.stalk z) hg₀
  have hemb : ∀ r, emb (M.stalkHom z r) = algebraMap V₀ (FractionRing V₀) (φ₀ r) := fun r =>
    IsFractionRing.lift_algebraMap (A := M.Z.presheaf.stalk z) hg₀ r
  refine ⟨V₀, inferInstance, inferInstance, hdvr, φ₀, emb, hcpl, hchar, hl, hemb, ?_⟩
  rw [← spMap_stalkHom, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [show jK V₀ = spMap (algebraMap V₀ (FractionRing V₀)) from rfl, spMap_spMap, spMap_spMap]
  congr 1
  ext r
  exact (hemb r).symm

theorem exists_gMem_of_trait : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), GlobalTheory.GSep.ZHAbove X₁ Y πY → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → CharZero V → ∀ (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), IsLocalHom ev → ∀ (ξ : Sp V ⟶ Y.Z) (e : X₁.Ω₁ →+* FractionRing V), ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ → jK V ≫ ξ = spMap e ≫ Y.pt → ∃ (X : Type) (_ : AddCommGroup X) (t : X → V) (δ : I → X → X), Nonempty (GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) := by
  intro I X₁ z₁ act hact Y πY hY V _ _ _ hcpl hchar ev hev ξ e hξ hjξ
  obtain ⟨U₀, EE, ⟨O⟩, hO, -, hhom, -⟩ := hY
  have hπ : Y.pt ≫ πY = X₁.M.pt :=
    hhom.trans ((congrArg (· ≫ X₁.M.pt) (Spec.map_id _)).trans (Category.id_comp _))
  obtain ⟨ψ, hψ, hψL, hψE⟩ := GlobalTheory.T.zarhinModel_genericFibre_isPullback_thetaSystem X₁ Y U₀ EE O hO
  have hab : (ξ ⁻¹' abLocus O.G).Nonempty := by
    refine ⟨jK V (closedPoint (FractionRing V)), ?_⟩
    have e1 : ξ (jK V (closedPoint (FractionRing V))) = Y.pt (spMap e (closedPoint (FractionRing V))) :=
      congrArg (fun f : Sp (FractionRing V) ⟶ Y.Z => f (closedPoint (FractionRing V))) hjξ
    rw [Set.mem_preimage, e1]
    exact GlobalTheory.Mum.CoverPull.pt_mem_abLocus _ _ X₁.S X₁.ρ Y U₀ EE hO O _
  obtain ⟨D, A, U, β, hβ, hβL, hβE⟩ := GlobalTheory.T.exists_uniformisation_at_completeTrait_of_model X₁ Y U₀ EE O V hcpl hchar ξ e hjξ hab
  have hpt : jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ = spMap e ≫ X₁.M.pt := by
    rw [← hξ, ← Category.assoc, hjξ, Category.assoc, hπ]
  have hend : ∀ a, ∃ E : EndU U.toUnifPre, E.aA.left ≫ (β ≫ ψ) = (β ≫ ψ) ≫ (act a).left := by
    intro a
    obtain ⟨F, hF, hFψ⟩ := hψE (act a) (hact a)
    obtain ⟨E, hE⟩ := hβE F hF
    refine ⟨E, ?_⟩
    rw [← Category.assoc, hE, Category.assoc, hFψ, Category.assoc]
  choose E hE using hend
  have hV : IsCN V := ⟨inferInstance, inferInstance, hcpl, hchar⟩
  have hpsi : ∀ mu : D.toPre.X, ∃ r : V, Formalism.L2.Pj.PsiCoord D.toPre mu r := fun mu => by
    obtain ⟨r, hr, -⟩ := (PsiCoordLocal.main V D hV.2.1 mu).1
    exact ⟨r, hr⟩
  choose t ht using hpsi
  obtain ⟨wl, hwl⟩ := LBIso.trans A.isLB (pull_isLB (pull_isLB O.L.isLB _) _) (pull_isLB X₁.ρ.P.isLB _) hβL
    (lbIso_pull_comp hψL β)
  refine ⟨D.toPre.X, inferInstance, t, fun a => (E a).h, ⟨{
    cn := hV
    loc := hev
    reg := fun a _ => ?_
    yK := e.comp X₁.S.R.val.toRingHom
    yK_eq := fun a => ?_
    D := D
    e₈ := AddEquiv.refl _
    G := (Over.pullback ξ).obj O.G
    semi := IsSemiAbelian.pullback _ _ O.semi
    A := A
    U := U
    φ := β ≫ ψ
    cart := (hβ.comp hψ).congr (spMap_spMap e X₁.S.R.val.toRingHom) rfl
    wl := wl
    wl_gen := hwl
    equiv := fun a => ⟨E a, hE a, fun _ => rfl⟩
    psi := fun mu => ⟨1, by simpa using ht mu⟩ }⟩⟩
  · rw [hpt]
    change a ∈ X₁.M.O (X₁.M.pt ((spMap e) (closedPoint (FractionRing V))))
    rw [X₁.M.pt_apply, RatModel.O_genericPoint]
    trivial
  · rw [hpt, GlobalTheory.FieldPts.val_spMap, RatModel.val_pt]
    rfl

theorem exists_gMem_thru : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), GlobalTheory.GSep.ZHAbove X₁ Y πY → ∀ y : Y.Z, πY y = z₁ → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (_ : IsDiscreteValuationRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) (_ : AddCommGroup X) (t : X → V) (δ : I → X → X) (𝔫 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (ξ : Sp V ⟶ Y.Z), ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ∧ ξ (closedPoint V) = y ∧ Function.Injective ev := by
  intro I X₁ z₁ act hact Y πY hY y hy
  subst hy
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  obtain ⟨V, _, _, hdvr, φ₀, emb, hcpl, hchar, hl₀, -, hptY⟩ := exists_cdvr_thru Y y
  have hπ : Y.pt ≫ πY = X₁.M.pt := by
    obtain ⟨-, -, -, -, -, hhom, -⟩ := hY
    refine Eq.trans hhom ?_
    exact (congrArg (· ≫ X₁.M.pt) (Spec.map_id _)).trans (Category.id_comp _)
  let s : X₁.M.Z.presheaf.stalk (πY y) →+* Y.Z.presheaf.stalk y := (πY.stalkMap y).hom
  have hs : spMap s ≫ X₁.M.Z.fromSpecStalk (πY y) = Y.Z.fromSpecStalk y ≫ πY :=
    Scheme.SpecMap_stalkMap_fromSpecStalk πY
  haveI hsl : IsLocalHom s := inferInstanceAs (IsLocalHom (πY.stalkMap y).hom)
  let ev : X₁.M.Z.presheaf.stalk (πY y) →+* V := φ₀.comp s
  have hξ : (spMap φ₀ ≫ Y.Z.fromSpecStalk y) ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) := by
    rw [Category.assoc, ← hs, ← Category.assoc, spMap_spMap]
  have hjξ : jK V ≫ spMap φ₀ ≫ Y.Z.fromSpecStalk y = spMap emb ≫ Y.pt := hptY
  have hpt' : jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) = spMap emb ≫ X₁.M.pt := by
    calc jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) = jK V ≫ (spMap φ₀ ≫ Y.Z.fromSpecStalk y) ≫ πY := by rw [hξ]
      _ = (jK V ≫ spMap φ₀ ≫ Y.Z.fromSpecStalk y) ≫ πY := by simp only [Category.assoc]
      _ = (spMap emb ≫ Y.pt) ≫ πY := by rw [hjξ]
      _ = spMap emb ≫ X₁.M.pt := by rw [Category.assoc, hπ]
  have hinj : Function.Injective ev := by
    have h1 : spMap ((algebraMap V (FractionRing V)).comp ev) ≫ X₁.M.Z.fromSpecStalk (πY y) =
        spMap (emb.comp (X₁.M.stalkHom (πY y))) ≫ X₁.M.Z.fromSpecStalk (πY y) := by
      rw [← spMap_spMap (algebraMap V (FractionRing V)) ev, ← spMap_spMap emb (X₁.M.stalkHom (πY y)), Category.assoc,
        Category.assoc, spMap_stalkHom]
      exact hpt'
    have h2 := (cancel_mono _).1 h1
    have h3 : (algebraMap V (FractionRing V)).comp ev = emb.comp (X₁.M.stalkHom (πY y)) :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
    intro a b hab
    apply X₁.M.stalkHom_injective
    apply emb.injective
    have ha := RingHom.congr_fun h3 a
    have hb := RingHom.congr_fun h3 b
    simp only [RingHom.comp_apply] at ha hb
    rw [← ha, ← hb, hab]
  obtain ⟨X, _, t, δ, ⟨𝔫⟩⟩ := exists_gMem_of_trait I X₁ (πY y) act hact Y πY hY V hcpl hchar ev
    (RingHom.isLocalHom_comp _ _) _ emb hξ hjξ
  refine ⟨V, inferInstance, inferInstance, inferInstance, hdvr, ev, X, inferInstance, t, δ, 𝔫,
    spMap φ₀ ≫ Y.Z.fromSpecStalk y, hξ, ?_, hinj⟩
  change Y.Z.fromSpecStalk y (spMap φ₀ (closedPoint V)) = y
  have : spMap φ₀ (closedPoint V) = closedPoint (Y.Z.presheaf.stalk y) := IsLocalRing.comap_closedPoint φ₀
  rw [this]
  exact Scheme.fromSpecStalk_closedPoint

end GlobalTheory.GSep.Thru
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem exists_div_torsion : ∀ (X₁ : GlobalTheory.GSep.GSet) (z : X₁.M.Z) (k : ℕ), 2 ≤ k → k ∣ X₁.S.r * X₁.S.N →
    ∃ a : X₁.S.Gam, k • a = 0 ∧ X₁.M.Div X₁.S.th a z := by
  intro X z₀ k hk hd
  haveI := X.M.qc
  haveI : CompactSpace X.M.Z := QuasiCompact.compactSpace_of_compactSpace X.M.s
  obtain ⟨z, hz', hcl⟩ := (isClosed_closure (s := {z₀})).exists_closed_singleton ⟨z₀, subset_closure rfl⟩
  have hsp : z₀ ⤳ z := specializes_iff_mem_closure.2 hz'
  obtain ⟨U, hne, hU⟩ := GlobalTheory.T.exists_nonempty_open_thetaRing_regular X
  obtain ⟨p, _, y, hy, hyU⟩ := exists_cen_main _ _ X.M z hcl U hne
  obtain ⟨hL, hL2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨hTU, hUT⟩ := GlobalTheory.ZH.thmU_and_uTors
  have hle : X.S.R ≤ X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) := hU _ (hyU ⟨_, rfl⟩)
  have hsw : ∀ w, (gPt p ≫ y) w ⤳ (gPt p ≫ y) (closedPoint (PadicAlgCl p)) := fun w => by
    rw [Subsingleton.elim w (closedPoint (PadicAlgCl p))]
  let y₀ : X.S.R →+* PadicAlgCl p :=
    (RatModel.valHomOf (gPt p ≫ y) _ hsw).comp (Subalgebra.inclusion hle).toRingHom
  have hy₀ : ∀ a : X.S.R, y₀ a = X.M.val (gPt p ≫ y) a := fun _ => rfl
  have hint : ∀ a : X.o₁, ‖y₀ (algebraMap X.o₁ X.S.R a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one hy ((X.M.O z).algebraMap_mem a)
  obtain ⟨u, l, τ, hτ, -⟩ :=
    (hasTests_of_real GlobalTheory.SS.semistableReductionSt hTU hL hL2 hUT X.o₁ X.Ω₁ X.S X.ρ).2 p y₀ ∅ hint
  have hq : ∀ w, 0 ≤ l.q w := fun w => by
    obtain ⟨e, he, -⟩ := hτ
    have h := τ.q_nonneg (e.symm w)
    rwa [he, AddEquiv.apply_symm_apply] at h
  obtain ⟨sc, h0, h₁, -, h₃⟩ := TestVal.exists_scale hL hL2 u l hint
  have hδ := (GlobalTheory.UnitTheta.closure_unit_theta hL hL2 hUT _ _ _ X.ρ p y₀ u l hint).1
  have hle' : ∀ a, ‖y₀ ⟨X.S.th a, X.S.th_mem a⟩‖ ≤ sc := fun a => by
    obtain ⟨w, -, hw⟩ := h₁ a
    exact hw.trans (mul_le_of_le_one_right h0 (Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg (hq w) (by positivity)))))
  have hsc : 0 < sc := hδ.trans_le (Real.iSup_le hle' h0)
  obtain ⟨a, -, ha, hn⟩ := h₃ k hk hd 0 (zero_mem _)
  refine ⟨a, by simpa using ha, RatModel.Div.of_specializes ?_ hsp⟩
  obtain ⟨d, hdv⟩ := X.div z
  refine (hdv.div_iff_isUnit a).2 ((RatModel.norm_val_eq_one_iff hy (hdv.2 a)).1 ?_)
  have hs := RatModel.gPt_specializes hy
  have e : ‖y₀ ⟨X.S.th a, X.S.th_mem a⟩‖ =
      ‖y₀ ⟨X.S.th d, X.S.th_mem d⟩‖ * ‖X.M.val (gPt p ≫ y) (X.S.th a / X.S.th d)‖ := by
    rw [hy₀, hy₀, ← norm_mul, ← RatModel.val_mul hsw (hle (X.S.th_mem d))
      (RatModel.O_le_of_specializes (hs _) (hdv.2 a))]
    congr 2
    have := hdv.1
    field_simp
  have b₁ := RatModel.norm_val_le_one hy (hdv.2 a)
  have b₂ := hle' d
  refine le_antisymm b₁ (not_lt.1 fun hlt => ?_)
  have := mul_le_mul_of_nonneg_right b₂ (norm_nonneg (X.M.val (gPt p ≫ y) (X.S.th a / X.S.th d)))
  nlinarith

end GlobalTheory.GSep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
open GlobalTheory

theorem _root_.GlobalTheory.T.mem_system_of_order_ge_along_traits : UTraitExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (φ : InvFun (𝓞 E)) (d : ℕ) (J : C.Z.IdealSheafData), UValOn Xo c C.i φ J d → ∀ (M : Scheme.{0}) (z₁ : M) (U : M.Opens) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (N₁ : ℕ) (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] N₁ (M.presheaf.stalk z₁)), GlobalTheory.GSep.HasTraitsOn ζ Φ.pre U → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ev' : M.presheaf.stalk z₁ →+* V), IsLocalHom ev' → Set.range (jK V ≫ spMap ev' ≫ M.fromSpecStalk z₁) ⊆ (U : Set M) → ∀ y' : Sp (FractionRing V) ⟶ Xo.XF c, y' ≫ C.iF = spMap ((algebraMap V (FractionRing V)).comp ev') ≫ ζ → ∀ (D e : ℕ) (f : M.presheaf.stalk z₁), Φ.OrdGe φ (D * (2 * d)) e f → ev' f ∈ idlAlong J (spMap ev' ≫ ζ ≫ pullback.fst C.z (spMap C.b)) ^ D ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map ev') ^ e := by
  first | exact @GlobalTheory.USepStrait.mem_of_ordGe_on | exact GlobalTheory.USepStrait.mem_of_ordGe_on | (intros; apply GlobalTheory.USepStrait.mem_of_ordGe_on <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms


theorem _root_.GlobalTheory.T.termsWitnesses_baseChange_along_tower : ∀ {I : Type} (X₁ : GlobalTheory.GSep.GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₁ : X₁.M.Z)
    (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type)
      (lab : C → X₁.S.Gam)
      (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1)
      (w₀ : W0 𝔪.U.toUnifPre) (s : Fam 𝔪.D.toPre (FractionRing V) 1) (g' : C → GtPtF 𝔪.D.toPre (FractionRing V))
      (w : ∀ c, GlobalTheory.UT.Frm 𝔪.D.toPre (FractionRing V) 1 (g' c).b),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
      (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀.IsGen →
      𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s →
      (∀ c, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero) ∧ (w c).IsGen ∧
        𝔪.Over' w₀ (g' c) (w c) (x (lab c)) (fr (lab c))) →
    ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : GlobalTheory.GSep.GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ)
      (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre)
      (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → ∀ (wψ : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), wψ.IsGen →
      𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U →
      (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) →
      𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) =
        pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∀ ρ : X₁.S.Gam → (FractionRing V')ˣ, (∀ b, FrPull wψ f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b) (ρ b)) →
    ∃ (th₂ : SecA 𝔪₂.A (FractionRing V') 1) (w₀₂ : W0 𝔪₂.U.toUnifPre) (s₂ : Fam 𝔪₂.D.toPre (FractionRing V') 1)
      (g'₂ : C → GtPtF 𝔪₂.D.toPre (FractionRing V')) (w₂ : ∀ c, GlobalTheory.UT.Frm 𝔪₂.D.toPre (FractionRing V') 1 (g'₂ c).b)
      (K : FractionRing V'),
      (∀ a, ValAt th₂ (x₂ a) (fr₂ a) (𝔪₂.yK ⟨𝔗.X₂.S.th a, 𝔗.X₂.S.th_mem a⟩)) ∧ w₀₂.IsGen ∧
      𝔪₂.U.ExpandsF (FractionRing V') 1 w₀₂ th₂ s₂ ∧
      (∀ c, (∃ o, GtPtF.IsNsmul (𝔗.X₂.S.r * 𝔗.X₂.S.N) (g'₂ c) o ∧ o.IsZero) ∧ (w₂ c).IsGen ∧
        𝔪₂.Over' w₀₂ (g'₂ c) (w₂ c) (x₂ (𝔗.lam (lab c))) (fr₂ (𝔗.lam (lab c)))) ∧
      (∀ mu c, coef s₂ (g'₂ c) (w₂ c) (𝔪₂.e₈ mu) * (ρ (lab c) : FractionRing V') = K * f (coef s (g' c) (w c) (𝔪.e₈ mu))) ∧
      ∀ b, 𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam b), 𝔗.X₂.S.th_mem _⟩ * (ρ b : FractionRing V') = K * f (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) := by
  first | exact @GlobalTheory.GSep.TermsTrans.terms_witnesses_baseChange | exact GlobalTheory.GSep.TermsTrans.terms_witnesses_baseChange | (intros; apply GlobalTheory.GSep.TermsTrans.terms_witnesses_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep.DivBound

theorem mo_ne_zero {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {V : Type} [CommRing V]
    [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {X : Type} [AddCommGroup X] {t : X → V}
    {δ : I → X → X} (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (mu : X) : t mu ≠ 0 :=
  let ⟨_, h⟩ := 𝔪.psi mu
  right_ne_zero_of_mul (PsiCoordLocal.ne_zero_of_coord h)

theorem theta_pow_le : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ))), (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) → (∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1) → ∀ c : WithZero (Multiplicative ℤ), (∀ b, ν (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) ≤ c) → ∀ a, ∃ w : X, 𝔪.YY a w ∧ ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) ^ ((X₁.S.r * X₁.S.N) ^ 2) ≤ c ^ ((X₁.S.r * X₁.S.N) ^ 2) * ν (algebraMap V (FractionRing V) (t w)) := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 ν h1 h2 c hc a
  obtain ⟨yy1, -, yy3, -⟩ := GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level I X₁ z₁ act V ev X t δ 𝔪
  by_cases hm : maximalIdeal V = ⊥
  · obtain ⟨w, hw⟩ := yy1 a
    refine ⟨w, hw, ?_⟩
    have hu : IsUnit (t w) := by
      by_contra hn
      exact mo_ne_zero 𝔪 w ((Submodule.mem_bot V).1 (hm ▸ (mem_maximalIdeal _).2 hn))
    have h1' : ν (algebraMap V (FractionRing V) (t w)) = 1 := by
      refine le_antisymm (h1 _) ?_
      have e : ν (algebraMap V (FractionRing V) (t w)) * ν (algebraMap V (FractionRing V) (hu.unit⁻¹ : Vˣ)) = 1 := by
        rw [← map_mul, ← map_mul, hu.mul_val_inv, map_one, map_one]
      calc (1 : WithZero (Multiplicative ℤ)) = _ := e.symm
        _ ≤ ν (algebraMap V (FractionRing V) (t w)) * 1 := mul_le_mul' le_rfl (h1 _)
        _ = _ := _root_.mul_one _
    rw [h1', _root_.mul_one]
    exact pow_le_pow_left' (hc a) _
  · obtain ⟨V', _, _, _, _, j, k, hcn, hj, hjl, hk, hν⟩ := GlobalTheory.T.exists_completeDVR_valuation_completeNormalLocal V 𝔪.cn ν h1 h2 hm
    obtain ⟨𝔫, hyk, hyy⟩ := GlobalTheory.T.uniformisedMember_baseChange_injective_localHom I X₁ z₁ act V ev X t δ 𝔪 V' j k hcn hj hjl hk
    obtain ⟨b, hb⟩ := GlobalTheory.T.exists_thetaConstant_dvd_pow_over_dvr I X₁ z₁ act V' (j.comp ev) X (fun i => j (t i)) δ 𝔫
    obtain ⟨w, r, hw, he⟩ := hb a
    obtain ⟨mu, hmu⟩ := yy1 a
    have hn3 := (GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level I X₁ z₁ act V' (j.comp ev) X (fun i => j (t i)) δ 𝔫).2.2.1
    have hw' : 𝔪.YY a w := (yy3 a mu w hmu).2 ((hn3 a mu w (hyy a mu hmu)).1 hw)
    refine ⟨w, hw', ?_⟩
    have key := hν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2))
      (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) * algebraMap V (FractionRing V) (t w))
      ⟨r, by rw [map_pow, ← hyk, he, map_mul, map_pow, ← hyk, hk]; ring⟩
    rw [map_pow, map_mul, map_pow] at key
    exact key.trans (mul_le_mul' (pow_le_pow_left' (hc b) _) le_rfl)

end GlobalTheory.GSep.DivBound
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_centred_pure_extension_tower_member : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), (∀ m : ℕ, m ≠ 0 → IsUnit (m : V)) → IsCN V → IsLocalHom ev → GlobalTheory.GSep.RegAt X₁ z₁ ev → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ (∀ J : Ideal V, (J.map io).comap io = J) ∧ 𝔗.Ext ev io ev₂ := by
  first | exact @GlobalTheory.GSep.exists_centred_ext_tower | exact GlobalTheory.GSep.exists_centred_ext_tower | (intros; apply GlobalTheory.GSep.exists_centred_ext_tower <;> assumption)
end
