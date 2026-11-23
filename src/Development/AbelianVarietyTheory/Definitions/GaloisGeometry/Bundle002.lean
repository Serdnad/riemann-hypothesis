module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle001
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle001
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.NumberTheory.LocalField.Basic

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {d : ℕ}

def pw (f : Fin d → R) : Submonoid R := Submonoid.powers (∏ j, f j)

def omitted (f : Fin d → R) (M : Type) [AddCommGroup M] [Module R M] : Submodule R (LocalizedModule (pw f) M) :=
  Submodule.span R {z | ∃ (j : Fin d) (k : ℕ) (m : M), z = LocalizedModule.mk (f j ^ k • m) ⟨(∏ l, f l) ^ k, by exact ⟨k, rfl⟩⟩}

abbrev LC (f : Fin d → R) (M : Type) [AddCommGroup M] [Module R M] : Type :=
  LocalizedModule (pw f) M ⧸ omitted f M

def frac (f : Fin d → R) {M : Type} [AddCommGroup M] [Module R M] (m : M) (k : ℕ) : LC f M :=
  Submodule.Quotient.mk (LocalizedModule.mk m ⟨(∏ l, f l) ^ k, by exact ⟨k, rfl⟩⟩)

theorem frac_prod_smul (f : Fin d → R) (m : M) (k : ℕ) : frac f ((∏ l, f l) • m) (k + 1) = frac f m k := by
  unfold frac
  congr 1
  rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, smul_smul, pow_succ]

theorem frac_zero_of_pos (f : Fin d → R) (hd : 0 < d) (m : M) : frac f m 0 = 0 := by
  unfold frac
  rw [Submodule.Quotient.mk_eq_zero]
  apply Submodule.subset_span
  exact ⟨⟨0, hd⟩, 0, m, by simp⟩

def IsRes {B : Type} [CommRing B] [Algebra ℂ B] (s : Fin d → B) (e : B →ₐ[ℂ] MvPowerSeries (Fin d) ℂ)
    (ρ : LC s (Om ℂ B d) →ₗ[ℂ] ℂ) : Prop :=
  (∀ j, e (s j) = MvPowerSeries.X j) ∧
  (∀ ω : Om ℂ B d, ∃ h : B, ω = h • exteriorPower.ιMulti B d fun j => D ℂ B (s j)) ∧
  ∀ (k : ℕ) (h : B), ρ (frac s (h • exteriorPower.ιMulti B d fun j => D ℂ B (s j)) (k + 1)) =
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm fun _ => k) (e h)

namespace IsRes

variable {B : Type} [CommRing B] [Algebra ℂ B] {s : Fin d → B} {e : B →ₐ[ℂ] MvPowerSeries (Fin d) ℂ}
  {ρ : LC s (Om ℂ B d) →ₗ[ℂ] ℂ}

end IsRes

end GlobalTheory.W1

namespace GlobalTheory.W1.Ex

def rho0 (s : Fin 0 → ℂ) : LC s (Om ℂ ℂ 0) →ₗ[ℂ] ℂ :=
  (Submodule.liftQ (omitted s (Om ℂ ℂ 0))
    ((exteriorPower.zeroEquiv ℂ Ω[ℂ⁄ℂ]).toLinearMap ∘ₗ
      LocalizedModule.lift (pw s) LinearMap.id (fun u => by
        obtain ⟨n, hn⟩ := u.2
        have : (u : ℂ) = 1 := by simpa using hn.symm
        rw [this, map_one]; exact isUnit_one))
    (by
      have : omitted s (Om ℂ ℂ 0) = ⊥ := by
        unfold omitted
        rw [Submodule.span_eq_bot]
        rintro z ⟨j, _, _, _⟩
        exact j.elim0
      rw [this]; exact bot_le))

end GlobalTheory.W1.Ex
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.ThetaGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def ThetaPair (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin n) k) W) :
    Prop :=
  ∃ B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V, B ≠ 0 ∧
    ∀ (g : GL (Fin r) k) (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin r) k)),
      (Φ' : Matrix (Fin n) (Fin r) k → ℂ) = om μ g h Φ → ∀ F : W, B Φ' (π h F) = σ g (B Φ F)

def OmQuot (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W) :
    Prop :=
  ∃ f : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] V ⊗[ℂ] W, f ≠ 0 ∧
    ∀ (g : GL (Fin r) k) (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin r) k)),
      (Φ' : Matrix (Fin n) (Fin r) k → ℂ) = om μ g h Φ → f Φ' = TensorProduct.map (σ g) (τ h) (f Φ)

def IsParahoricVec {t : ℕ} (χ : kˣ →* ℂˣ) (π : Representation ℂ (GL (Fin (r + t)) k) W) (v : W) : Prop :=
  ∀ h ∈ KO k (Fin (r + t)),
    (∀ (i : Fin t) (j : Fin r), valuation k (h.val (Fin.natAdd r i) (Fin.castAdd t j)) < 1) →
    ∀ u : kˣ, (u : k) = (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det → π h v = (χ u : ℂ) • v

end GlobalTheory.ThetaGL
end
end

section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.Et

section Transfer

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

def alongS (F : Shv R) (n : ℕ) {Z X : Scheme.{0}} (t : (freeOn R).obj X ⟶ (freeOn R).obj Z) : HS R F n Z →+ HS R F n X where
  toFun x := (Abelian.Ext.mk₀ t).comp x (zero_add n)
  map_zero' := Abelian.Ext.comp_zero _ _ _ _ _
  map_add' _ _ := Abelian.Ext.comp_add _ _ _ _

def push (n : ℕ) {Z X : Scheme.{0}} (t : (freeOn R).obj X ⟶ (freeOn R).obj Z) : H R n Z →ₗ[R] H R n X where
  toFun x := (Abelian.Ext.mk₀ t).comp (x : HS R (coef R) n Z) (zero_add n)
  map_add' _ _ := Abelian.Ext.comp_add _ _ _ _
  map_smul' r _ := Abelian.Ext.comp_smul _ _ _ (ULift.up r : ULift.{1} R)

end Transfer

section Mu

variable (n : ℕ) [NeZero n]

def Mu (A : Type) [CommRing A] : Type := Additive (rootsOfUnity n A)


end Mu

def IsStrictlySemistable {O : Type} [CommRing O] (ϖ : O) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O)) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (m r : ℕ) (_ : 1 ≤ r) (_ : r ≤ m)
    (ψ : (MvPolynomial (Fin m) O ⧸ Ideal.span (Set.singleton ((∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) -
      MvPolynomial.C ϖ))) →+* Γ(X, U)),
    ψ.Etale ∧ ψ.comp (algebraMap O _) = ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ p.appLE ⊤ U le_top).hom

end GlobalTheory.Et

end
end

section

noncomputable section

namespace GlobalTheory.Cong

variable {k : Type} [NormedField k]

def PolyApprox [IsUltrametricDist k] {J : Type} (θ : J → k) (S : Set (J → k)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (s : Finset (J → k)) (c : (J → k) → k), (s : Set (J → k)) ⊆ S ∧
    ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ η ∈ s, c η * MvPolynomial.aeval η P‖ ≤ ε

def trc {Γ A : Type} [Group Γ] [CommRing A] {a : ℕ} (r : Γ →* GL (Fin a) A) (g : Γ) : A :=
  ((r g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A).trace

def LinApprox {Γ : Type} [Group Γ] {a : ℕ} (r : Γ →* GL (Fin a) k) (C : Set (Γ →* GL (Fin a) k)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (s : Finset (Γ →* GL (Fin a) k)) (c : (Γ →* GL (Fin a) k) → k), (s : Set (Γ →* GL (Fin a) k)) ⊆ C ∧
    ∀ g : Γ, ‖trc r g - ∑ ρ ∈ s, c ρ * trc ρ g‖ ≤ ε

def opOf {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (f : Γ →₀ ℂ) (v : V) : V :=
  f.sum fun g c => c • ρ g v

theorem PolyApprox.mono [IsUltrametricDist k] {J : Type} {θ : J → k} {S T : Set (J → k)} (h : PolyApprox θ S)
    (hST : S ⊆ T) : PolyApprox θ T := fun ε hε => by
  obtain ⟨s, c, hs, hP⟩ := h ε hε
  exact ⟨s, c, hs.trans hST, hP⟩

variable [NormOneClass k] [IsUltrametricDist k]

theorem aeval_sub_le {J : Type} {x y : J → k} {δ : ℝ} (hδ : 0 ≤ δ) (hx : ∀ j, ‖x j‖ ≤ 1) (hy : ∀ j, ‖y j‖ ≤ 1)
    (hxy : ∀ j, ‖x j - y j‖ ≤ δ) (P : MvPolynomial J ℤ) :
    ‖MvPolynomial.aeval x P‖ ≤ 1 ∧ ‖MvPolynomial.aeval y P‖ ≤ 1 ∧
      ‖MvPolynomial.aeval x P - MvPolynomial.aeval y P‖ ≤ δ := by
  first
  | exact @_root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le
  | exact _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le
  | (apply _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le ..)

end GlobalTheory.Cong

end
end

section

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL
namespace GlobalTheory.LocGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ}


variable (k N) in
abbrev AdGL : Type := GL (Fin N) k ⧸ Subgroup.center (GL (Fin N) k)

def CoeffLp (p : ℝ) (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : Measure (AdGL k N)), μ.IsHaarMeasure →
    ∀ (v : V) (l : Module.Dual ℂ V), IsOpen {g : GL (Fin N) k | l ∘ₗ π g = l} →
      ∃ F : AdGL k N → ℝ, (∀ g : GL (Fin N) k, F (QuotientGroup.mk g) = ‖l (π g v)‖) ∧ MemLp F (ENNReal.ofReal p) μ

def IsSqIntCoeff (π : Representation ℂ (GL (Fin N) k) V) : Prop := CoeffLp 2 π

def IsTemperedCoeff (π : Representation ℂ (GL (Fin N) k) V) : Prop := ∀ ε : ℝ, 0 < ε → CoeffLp (2 + ε) π

end GlobalTheory.LocGL
end
end
