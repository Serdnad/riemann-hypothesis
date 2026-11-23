module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldBasisToroidalModelSnc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle211
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3404
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentCompatibility
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004

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

theorem _root_.GlobalTheory.T.exists_logVectorField_basis_toroidalModel_snc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (x : Y.X), x ∈ U.1 → ∃ (f : Γ(Y.X, U.1)) (W : Y.X.affineOpens) (hW : W.1 ≤ U.1) (m : ℕ) (t : Fin m → Γ(Y.X, W.1)) (b : Module.Basis (Fin Dw.dim) Γ(Y.X, W.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) W)), x ∈ W.1 ∧ W.1 = Y.X.basicOpen f ∧ (∀ g ∈ (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal W, g ∈ Ideal.span {∏ i, t i}) ∧ ∏ i, t i ∈ (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal W ∧ ∀ (i : Fin m) (k : Fin Dw.dim), ((b k).1 : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1)) (t i) = if (k : ℕ) = i then t i else 0 := by
  first | exact @GlobalTheory.LogBasis.exists_logDer_basis | exact GlobalTheory.LogBasis.exists_logDer_basis | (intros; apply GlobalTheory.LogBasis.exists_logDer_basis <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_uniformised_member_through_point_of_model_above : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ y : Y.Z, πY y = z₁ → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (_ : IsDiscreteValuationRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) (_ : AddCommGroup X) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔫 : UMem X₁ z₁ act V ev X t δ) (ξ : Sp V ⟶ Y.Z), ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ∧ ξ (closedPoint V) = y := by
  first | exact @GlobalTheory.Poinc.Sep.Cmp.Thru.exists_uMem_thru | exact GlobalTheory.Poinc.Sep.Cmp.Thru.exists_uMem_thru | (intros; apply GlobalTheory.Poinc.Sep.Cmp.Thru.exists_uMem_thru <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.exists_principal_siegel_adjoint_action_pullback : ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (bar : O → O) (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B) (f : S' ⟶ S) (z : SiegPre h M ζ s) (act : O → (z.A ⟶ z.A)), f ≫ s = s' → z.Principal → IsRAct z.A act → Adj z.A z.P bar act → ∃ (w : SiegPre h M ζ s') (actw : O → (w.A ⟶ w.A)), w.Principal ∧ IsRAct w.A actw ∧ Adj w.A w.P bar actw ∧ ActPB w actw z act f := by
  first | (exact @GlobalTheory.UPel.HT.siegPre_actPB_pullback) | (exact GlobalTheory.UPel.HT.siegPre_actPB_pullback) | (intros; apply GlobalTheory.UPel.HT.siegPre_actPB_pullback  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.zarhinTrick_principal_objects_iso_unique : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∀ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : GlobalTheory.ZarhinFam.ord d → (z₁.A ⟶ z₁.A)) (act₂ : GlobalTheory.ZarhinFam.ord d → (z₂.A ⟶ z₂.A)), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z₁.Principal → z₂.Principal → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → Adj z₁.A z₁.P (GlobalTheory.ZarhinFam.bar d) act₁ → Adj z₂.A z₂.P (GlobalTheory.ZarhinFam.bar d) act₂ → ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z₁ act₁ → ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z₂ act₂ → ActPB z₁ act₁ z₂ act₂ (𝟙 S) := by
  first | (exact @GlobalTheory.ZarhinFam.actPB_of_zRel) | (exact GlobalTheory.ZarhinFam.actPB_of_zRel) | (intros; apply GlobalTheory.ZarhinFam.actPB_of_zRel  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.siegel_pullback_with_action_cancellation : ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (S S₁ S₂ : Scheme.{0}) (s : S ⟶ Sp B) (s₁ : S₁ ⟶ Sp B) (s₂ : S₂ ⟶ Sp B) (z : SiegPre h M ζ s) (act : O → (z.A ⟶ z.A)) (g₁ : S₁ ⟶ S) (y : S₂ ⟶ S₁) (w₁ : SiegPre h M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A)) (w₂ : SiegPre h M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)), ActPB w₁ act₁ z act g₁ → ActPB w₂ act₂ z act (y ≫ g₁) → ActPB w₂ act₂ w₁ act₁ y := by
  first | exact @GlobalTheory.UPel.HT.actPB_cancel | exact GlobalTheory.UPel.HT.actPB_cancel | (intros; apply GlobalTheory.UPel.HT.actPB_cancel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.idempotent_image_relation_of_pullback : ∀ (h h' M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp B) (s₂ : S₂ ⟶ Sp B) (y : S₂ ⟶ S₁) (c₁ : SiegPre h M ζ s₁) (w₁ : SiegPre h' M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A)) (c₂ : SiegPre h M ζ s₂) (w₂ : SiegPre h' M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)), ActPB w₂ act₂ w₁ act₁ y → SiegPB c₂ c₁ y → ZRel e jl o κ c₁ w₁ act₁ → ZRel e jl o κ c₂ w₂ act₂ := by
  first | (exact @GlobalTheory.UPel.HT.zRel_of_pullback) | (exact GlobalTheory.UPel.HT.zRel_of_pullback) | (intros; apply GlobalTheory.UPel.HT.zRel_of_pullback  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.siegel_pullback_of_idempotent_images_and_action_pullback : ∀ (h h' M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp B) (s₂ : S₂ ⟶ Sp B) (y : S₂ ⟶ S₁) (c₁ : SiegPre h M ζ s₁) (w₁ : SiegPre h' M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A)) (c₂ : SiegPre h M ζ s₂) (w₂ : SiegPre h' M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)), ActPB w₂ act₂ w₁ act₁ y → ZRel e jl o κ c₁ w₁ act₁ → ZRel e jl o κ c₂ w₂ act₂ → SiegPB c₂ c₁ y := by
  first | (exact @GlobalTheory.UPel.HT.siegPB_of_zRel_actPB) | (exact GlobalTheory.UPel.HT.siegPB_of_zRel_actPB) | (intros; apply GlobalTheory.UPel.HT.siegPB_of_zRel_actPB  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.level_sections_formulas_of_idempotent_image_pullback : ∀ (h h' M : ℕ) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' T : Scheme.{0}) (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)) (w' : SiegPre h' M (zetaAway M) (g ≫ t)) (actw' : O → (w'.A ⟶ w'.A)), ActPB w' actw' z act g → ZRel e jl o κ c' w' actw' → (∀ a, g ≫ (z.lev (jl a) ≫ act e).left = g ≫ (z.lev (jl a)).left) ∧ ∀ a, g ≫ (z.lev a).left = g ≫ ((List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left := by
  first | (exact @GlobalTheory.ZRelLevs.zrel_levs) | (exact GlobalTheory.ZRelLevs.zrel_levs) | (intros; apply GlobalTheory.ZRelLevs.zrel_levs  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

variable {k : Type} [Field k]

def coordSub (A₀ : Over (Sp k)) [GrpObj A₀] (S : Submodule k (HdR A₀)) :
    Submodule (DualNumber k) (Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀) where
  carrier := {d | ∃ u ∈ S, ∃ v ∈ S, ∀ c : primDR A₀,
    d ((constMor A₀).pull c) = TrivSqZeroExt.inl (u c) + TrivSqZeroExt.inr (v c)}
  add_mem' := by
    rintro d d' ⟨x, hx, y, hy, e⟩ ⟨x', hx', y', hy', e'⟩
    refine ⟨x + x', add_mem hx hx', y + y', add_mem hy hy', fun c => ?_⟩
    rw [LinearMap.add_apply, e, e']
    ext <;> simp <;> ring
  zero_mem' := ⟨0, zero_mem _, 0, zero_mem _, fun c => by
    rw [LinearMap.zero_apply]
    ext <;> simp⟩
  smul_mem' := by
    rintro r d ⟨x, hx, y, hy, e⟩
    refine ⟨r.fst • x, Submodule.smul_mem _ _ hx, r.fst • y + r.snd • x,
      add_mem (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hx), fun c => ?_⟩
    rw [LinearMap.smul_apply, e, smul_eq_mul]
    ext <;> simp <;> ring

theorem coords_unique {A₀ : Over (Sp k)} [GrpObj A₀] {u v u' v' : HdR A₀}
    (h : ∀ c : primDR A₀, TrivSqZeroExt.inl (u c) + TrivSqZeroExt.inr (v c)
      = (TrivSqZeroExt.inl (u' c) + TrivSqZeroExt.inr (v' c) : DualNumber k)) : u = u' ∧ v = v' := by
  constructor
  · refine LinearMap.ext fun c => ?_
    have := congrArg TrivSqZeroExt.fst (h c)
    simpa using this
  · refine LinearMap.ext fun c => ?_
    have := congrArg TrivSqZeroExt.snd (h c)
    simpa using this

theorem graphFil_exists_isCompl : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ →
    ∀ f : HdR A₀ →ₗ[k] HdR A₀, ∃ M : Submodule (DualNumber k) (Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀),
      IsCompl (GlobalTheory.HTRealise.graphFil A₀ f) M := by
  intro k _ A₀ _ hA f
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (Fil A₀)
  refine ⟨coordSub A₀ W, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro d ⟨x, hx, y, hy, e⟩ ⟨u, hu, v, hv, e'⟩
    obtain ⟨h1, h2⟩ := coords_unique (u := x) (v := f x + y) (u' := u) (v' := v)
      (fun c => by rw [LinearMap.add_apply]; exact (e c).symm.trans (e' c))
    subst h1
    have hx0 : x = 0 := (Submodule.disjoint_def.1 hW.disjoint) x hx hu
    subst hx0
    rw [map_zero, zero_add] at h2
    subst h2
    have hy0 : y = 0 := (Submodule.disjoint_def.1 hW.disjoint) y hy hv
    subst hy0
    refine crys_ext hA fun c => ?_
    rw [e' c]
    ext <;> simp <;> rfl
  · rw [codisjoint_iff, eq_top_iff]
    intro d _
    obtain ⟨u, v, hd⟩ := exists_coords d
    have htop : Fil A₀ ⊔ W = ⊤ := hW.sup_eq_top
    obtain ⟨x, hx, w, hw, hxw⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : u ∈ Fil A₀ ⊔ W)
    obtain ⟨y, hy, w', hw', hyw⟩ :=
      Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : v - f x ∈ Fil A₀ ⊔ W)
    obtain ⟨d₁, h₁⟩ := exists_crys hA x (f x + y)
    obtain ⟨d₂, h₂⟩ := exists_crys hA w w'
    have hsum : d = d₁ + d₂ := by
      refine crys_ext hA fun c => ?_
      rw [LinearMap.add_apply, hd c, h₁ c, h₂ c, ← hxw]
      have hv : v = f x + (y + w') := by rw [hyw]; abel
      rw [hv]
      ext <;> simp <;> ring
    rw [hsum]
    exact Submodule.add_mem_sup ⟨x, hx, y, hy, h₁⟩ ⟨w, hw, w', hw', h₂⟩

end GlobalTheory.HTRealise
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

theorem push_constMor_pull {k : Type} [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (g : A₀ ⟶ A₀)
    [IsMonHom g] (c : primDR A₀) :
    primPull (epsDP k) (GlobalTheory.DeRham.epsRed k) g ((constMor A₀).pull c) =
      (constMor A₀).pull (primPull (dp0 k) (𝟙 _) g c) := by
  have K := (constMor A₀).isMor.comp (homMor (epsDP k) (GlobalTheory.DeRham.epsRed k) g).isMor
  apply Subtype.ext
  exact (IsMor.pullback1_comp (constMor A₀).isMor
    (homMor (epsDP k) (GlobalTheory.DeRham.epsRed k) g).isMor K (fun _ ↦ rfl) rfl c.1).trans
    (IsMor.pullback1_comp (homMor (dp0 k) (𝟙 _) g).isMor (constMor A₀).isMor K
      (fun _ ↦ rfl) (by simp) c.1).symm

theorem push_mem_graphFil : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (g : A₀ ⟶ A₀) [IsMonHom g] (f : HdR A₀ →ₗ[k] HdR A₀), (∀ x ∈ Fil A₀, f (push (dp0 k) (𝟙 _) g x) - push (dp0 k) (𝟙 _) g (f x) ∈ Fil A₀) → ∀ d ∈ GlobalTheory.HTRealise.graphFil A₀ f, push (epsDP k) (GlobalTheory.DeRham.epsRed k) g d ∈ GlobalTheory.HTRealise.graphFil A₀ f := by
  intro k _ A₀ _ g _ f hf d hd
  obtain ⟨x, hx, y, hy, e⟩ := hd
  refine ⟨push (dp0 k) (𝟙 _) g x, push_mem_Fil g hx,
    push (dp0 k) (𝟙 _) g (f x) - f (push (dp0 k) (𝟙 _) g x) + push (dp0 k) (𝟙 _) g y,
    add_mem (by rw [← neg_sub]; exact neg_mem (hf x hx)) (push_mem_Fil g hy), fun c ↦ ?_⟩
  rw [push_apply, push_constMor_pull, e]
  simp only [push_apply, LinearMap.add_apply, LinearMap.sub_apply]
  congr 2
  ring

end GlobalTheory.HTRealise
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

variable {k : Type} [Field k]

theorem crysRed_pull_constMor_pull (A₀ : Over (Sp k)) [GrpObj A₀] (c : primDR A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀).pull ((constMor A₀).pull c) = c := by
  rw [GrpMor.pull_pull (constMor A₀) (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀)
    (homMor (dp0 k) (𝟙 _) (𝟙 A₀)) (fun _ ↦ rfl) (by simp) c]
  exact Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)



theorem mem_Fil_iff_exists_graphFil_corr (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (f : HdR A₀ →ₗ[k] HdR A₀) (y : HdR A₀) :
    y ∈ Fil A₀ ↔ ∃ d ∈ graphFil A₀ f,
      (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀).Corr d y := by
  constructor
  · intro hy
    obtain ⟨d, hd⟩ := exists_crys hA y (f y)
    refine ⟨d, ⟨y, hy, 0, zero_mem _, fun c ↦ by rw [hd c]; simp⟩, fun c ↦ ?_⟩
    obtain ⟨z, rfl⟩ := (isBC_constMor hA).2 c
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, TrivSqZeroExt.fst_zero]
    | add a b ha hb => simp only [map_add (f := _), ha, hb, TrivSqZeroExt.fst_add]
    | tmul a c =>
      rw [liftSemi_tmul, map_smulₛₗ, map_smul, crysRed_pull_constMor_pull, map_smul, hd c]
      simp
  · rintro ⟨d, ⟨x, hx, y', -, e⟩, hc⟩
    have : y = x := LinearMap.ext fun c ↦ by
      have h1 := hc ((constMor A₀).pull c)
      rw [crysRed_pull_constMor_pull, e c] at h1
      simpa using h1
    exact this ▸ hx

end GlobalTheory.HTRealise
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTRealise

theorem pairing_eps_eq_zero {k : Type} [Field k] {M : Type*} [AddCommGroup M] [Module (DualNumber k) M]
    (χ : M →ₗ[DualNumber k] M →ₗ[DualNumber k] DualNumber k) {X Z X' Z' : M} {a b c e : k}
    (h₁ : χ X X' = algebraMap k (DualNumber k) a) (h₂ : χ X Z' = algebraMap k (DualNumber k) b)
    (h₃ : χ Z X' = algebraMap k (DualNumber k) c) (h₄ : χ Z Z' = algebraMap k (DualNumber k) e)
    (ha : a = 0) (hbc : b + c = 0) :
    χ (X + (DualNumber.eps : DualNumber k) • Z) (X' + (DualNumber.eps : DualNumber k) • Z') = 0 := by
  simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, h₁, h₂, h₃, h₄, smul_eq_mul]
  subst ha
  ext
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
    linear_combination hbc



theorem graphFil_isotropic : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ →
    ∀ (P : LB (A₀ ⊗ A₀).left), P.IsLB → ∀ (φ : LinearMap.BilinForm k (HdR A₀)),
    GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) A₀ A₀ P φ → ∀ f : HdR A₀ →ₗ[k] HdR A₀,
    (∀ x ∈ Fil A₀, ∀ y ∈ Fil A₀, φ (f x) y + φ x (f y) = 0) →
    ∀ φ' : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀ →ₗ[DualNumber k] Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀ →ₗ[DualNumber k] DualNumber k,
    GlobalTheory.AbDual.IsCorrForm (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀ A₀ P φ' →
    ∀ d ∈ GlobalTheory.HTRealise.graphFil A₀ f, ∀ d' ∈ GlobalTheory.HTRealise.graphFil A₀ f, φ' d d' = 0 := by
  intro k _ A₀ _ hA P hP φ hφ f hf φ' hφ' d hd d' hd'
  have := hA.smooth
  obtain ⟨g, hg⟩ := GlobalTheory.SerreDim.exists_dim_of_grpObj A₀
  have iso := GlobalTheory.PrincipalPolPairing.isotropic GlobalTheory.abelianDeRham hA hg hP hφ
  have C : GlobalTheory.AbDual.CupSquare (epsDP k) (GlobalTheory.DeRham.epsRed k) (A₀ ⊗ A₀) := by
    obtain ⟨C, _, φ, j, hφ, hic, -⟩ := exists_const (A₀ ⊗ A₀)
    have hAB := AbelianSchemeGerms.isAbelianScheme_tensor A₀ A₀ hA hA
    have hC : IsAbelianScheme C := by
      have := hAB.comm
      refine { comm := ?_, smooth := MorphismProperty.of_isPullback (P := @Smooth) hφ.1 hAB.smooth
               proper := MorphismProperty.of_isPullback (P := @IsProper) hφ.1 hAB.proper
               geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) hφ.1 hAB.geomConnected }
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hφ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hφ.2 T x y (pushPt hφ.1.w x) (pushPt hφ.1.w y) rfl rfl,
        ← hφ.2 T y x (pushPt hφ.1.w y) (pushPt hφ.1.w x) rfl rfl, _root_.mul_comm]
    have gC := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hφ.1 (GlobalTheory.AbDual.smooth_prod hg hg)
    have su : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom := fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
    exact GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys GlobalTheory.abelianDeRham.1 GlobalTheory.abelianDualCrystal.2
      (isDPNilpotent_squareZero _) su rfl hC gC hic.1 (liftMor (epsDP k) hic)
  have e : LBIso (P.pull (𝟙 _)) P :=
    (CechPic.cls_eq_iff (pull_isLB hP _) hP).1 (by rw [CechPic.cls_pull hP, CechPic.pull_id])
  obtain ⟨χ, hχ, hk⟩ := hφ.pull hP (constMor A₀) (constMor A₀) (h := 𝟙 _) (by simp) (by simp) hP e
  obtain rfl := hχ.unique C hP hφ'
  have hm := isBC_constMor hA
  obtain ⟨x, hx, y, hy, ed⟩ := mem_graphFil.1 hd
  obtain ⟨x', hx', y', hy', ed'⟩ := mem_graphFil.1 hd'
  obtain ⟨X, hX⟩ := hm.exists x
  obtain ⟨Z, hZ⟩ := hm.exists (f x + y)
  obtain ⟨X', hX'⟩ := hm.exists x'
  obtain ⟨Z', hZ'⟩ := hm.exists (f x' + y')
  have dE : d = X + (DualNumber.eps : DualNumber k) • Z := crys_ext hA fun c => by
    rw [ed c, LinearMap.add_apply, LinearMap.smul_apply, hX c, hZ c]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have dE' : d' = X' + (DualNumber.eps : DualNumber k) • Z' := crys_ext hA fun c => by
    rw [ed' c, LinearMap.add_apply, LinearMap.smul_apply, hX' c, hZ' c]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have h₁ : φ x x' = 0 := iso x hx x' hx'
  have h₂ : φ x (f x' + y') + φ (f x + y) x' = 0 := by
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, iso x hx y' hy', iso y hy x' hx', add_zero, add_zero, add_comm]
    exact hf x hx x' hx'
  rw [dE, dE']
  exact pairing_eps_eq_zero χ (hk _ _ _ _ hX hX') (hk _ _ _ _ hX hZ') (hk _ _ _ _ hZ hX') (hk _ _ _ _ hZ hZ') h₁ h₂

end GlobalTheory.HTRealise
end
end
