module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseRangeOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle049
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.PieriBlockIdeals.BlockIdealBound5Derived
import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt
import Formalism.PieriBlockIdeals.MertensReciprocalElementary
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.Published.CharAboveModel
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD

namespace GlobalTheory.ExpFrame.Tests

section Jumps

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]


variable (Ω) in
theorem exists_bridge (τ : E →+* Qbar l) : ∃ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (_ : IsPlaceOver A w)
    (LL : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL LL)), GlobalTheory.Pst.Induces Bw ∧
      IsInduced Bw τ (AlgHom.id ℚ_[l] ↥Bw.Kw.1) := by
  first
  | exact @_root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge
  | exact _root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge
  | (apply _root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge <;> assumption)
  | (intros; apply _root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PlaceBallNormLemmas.exists_bridge ..)

end Jumps

section RankOne

variable (l : ℕ) [Fact l.Prime]

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

end RankOne

section Small

end Small

end GlobalTheory.ExpFrame.Tests

end
end

section

set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CatCoh GlobalTheory.PeriodFamily

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

@[reducible] def Charts.std {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] (F : Fam I g Λ)
    (Q : Opens (Tot I g) → Prop) : Charts F where
  K := {W : Opens (Tot I g) // (∀ p ∈ W, p.1 ∈ F.V) ∧ Q W}
  W k := k.1
  base k := k.2.1
  le l k' k := ∀ p ∈ k'.1, F.shift l p ∈ k.1
  le_refl k p hp := by rwa [F.shift_zero]
  le_trans h h' p hp := by rw [F.shift_add]; exact h _ (h' p hp)
  maps h := h

section Fibre

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

@[reducible] def fibFam (u : HolUnif A L g) : Fam Empty g u.Λ where
  V := ⊤
  τ := { toFun x := fun _ ↦ (x : Fin g → ℂ), map_zero' := rfl, map_add' _ _ := rfl }
  hol _ := analyticOnNhd_const

def fibUnif (u : HolUnif A L g) : Unif (fibFam u) (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol (fibFam u).V)) where
  E p := (u.ex p.2).left
  w p hp := by
    have e : (Hol.ev p.1 hp).toRingHom.comp (algebraMap ℂ (Hol (fibFam u).V)) = RingHom.id ℂ :=
      RingHom.ext fun c ↦ (Hol.ev p.1 hp).commutes c
    rw [e, Cris.spMap_id, Category.comp_id]
    exact Over.w (u.ex p.2)
  per l p _ := by
    change (u.ex (p.2 + (l : Fin g → ℂ))).left = _
    rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
  hol U f := ⟨by
    have := (u.hol U f).1.preimage (continuous_snd (X := Empty → ℂ))
    convert this using 1
    exact Set.ext fun p ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨trivial, h⟩⟩,
    (u.hol U f).2.comp differentiableOn_snd fun _ h ↦ h.2⟩

def IsPeriodHom (u : HolUnif A L g) (P : u.Λ →+ HdR A) : Prop :=
  ∀ c : primDR A, IsPeriod (fibUnif u) c.1
    { toFun x := algebraMap ℂ (Hol (fibFam u).V) (P x c)
      map_zero' := by rw [map_zero, LinearMap.zero_apply, map_zero]
      map_add' x y := by
        rw [map_add P x y, LinearMap.add_apply]
        exact (algebraMap ℂ (Hol (fibFam u).V)).map_add _ _ }

end Fibre

def PExist : Prop :=
  ∀ (I : Type) [Fintype I] (g : ℕ) (Λ : Type) [AddCommGroup Λ] (F : Fam I g Λ) (B : Type) [CommRing B] (X : Scheme.{0})
    (s : X ⟶ Sp B) [IsSeparated s] (σ : B →+* Hol F.V) (u : Unif F s σ), u.Based → ∀ c : FirstDeRham s, ∃ per, IsPeriod u c per

def PUniq : Prop :=
  ∀ (I : Type) [Fintype I] (g : ℕ) (Λ : Type) [AddCommGroup Λ] (F : Fam I g Λ) (B : Type) [CommRing B] (X : Scheme.{0})
    (s : X ⟶ Sp B) [IsSeparated s] (σ : B →+* Hol F.V) (u : Unif F s σ) (c : FirstDeRham s) (per per' : Λ →+ Hol F.V),
    IsPeriod u c per → IsPeriod u c per' → per = per'

def PHom : Prop :=
  ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → ∀ (L : LB A.left) (u : HolUnif A L g), ∃ P, IsPeriodHom u P

def PLie : Prop :=
  ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (L : LB A.left) (u : HolUnif A L g) (P : u.Λ →+ HdR A), IsPeriodHom u P →
    ∀ x : u.Λ, ∃ v, IsLieImage (P x) v ∧ u.IsDiff x v

def PEnd : Prop :=
  ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    ∀ (L : LB A.left) (u : HolUnif A L g) (P : u.Λ →+ HdR A), IsPeriodHom u P →
    ∀ (α : A ⟶ A) [IsMonHom α] (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ w, u.ex (M w) = u.ex w ≫ α) →
      ∀ x x' : u.Λ, (x' : Fin g → ℂ) = M x → push (dp0 ℂ) (𝟙 _) α (P x) = P x'

def PChern (ε : ℤˣ) : Prop :=
  ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    ∀ (L : LB A.left) (u : HolUnif A L g) (P : u.Λ →+ HdR A), IsPeriodHom u P →
    ∀ (M : LB A.left) (u' : HolUnif A M g), M.IsLB → u'.ex = u.ex →
    ∀ (H : Matrix (Fin g) (Fin g) ℂ) (χ : u'.Λ → ℂ) (ψ : LinearMap.BilinForm ℂ (HdR A)), u'.IsAH H χ →
      IsPolForm (dp0 ℂ) (𝟙 _) A M ψ → ∀ x x' : u.Λ,
        ψ (P x) (P x') = ((ε : ℤ) : ℂ) * (2 * Real.pi * Complex.I) *
          (((x : Fin g → ℂ) ⬝ᵥ H.mulVec (star (x' : Fin g → ℂ))).im : ℂ)

def PSpan : Prop :=
  ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (L : LB A.left) (u : HolUnif A L g) (P : u.Λ →+ HdR A), IsPeriodHom u P →
    Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (HdR A) = 2 * g

def PFix : Prop :=
  ∀ (I : Type) [Fintype I] (g : ℕ) (Λ : Type) [AddCommGroup Λ] (F : Fam I g Λ) (B : Type) [CommRing B]
    (𝒜 : Over (Sp B)) [GrpObj 𝒜], IsAbelianScheme 𝒜 → ∀ (σ : B →+* Hol F.V) (e : Unif F (𝒜.hom ≫ 𝟙 _) σ)
    (z : I → ℂ), z ∈ F.V → ∀ (y : B →+* ℂ), (∀ b, y b = (σ b).fn z) →
    ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (φ : A.left ⟶ 𝒜.left)
      (m : GrpMor (dp0 B) (𝟙 _) 𝒜 (dp0 ℂ) (𝟙 _) A y (spMap y) φ) (L : LB A.left) (u : HolUnif A L g),
      (∀ w, e.E (z, w) = (u.ex w).left ≫ φ) → ∀ τ : Λ →+ u.Λ, (∀ l, (τ l : Fin g → ℂ) = F.τ l z) →
    ∀ (P : u.Λ →+ HdR A), IsPeriodHom u P → ∀ (c : primDR 𝒜) (per : Λ →+ Hol F.V), IsPeriod e c.1 per →
      ∀ l, P (τ l) (m.pull c) = (per l).fn z

def PTaylor : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (g : ℕ) (B : Type) [CommRing B] [Algebra ℂ B]
    (𝒜 : Over (Sp B)) [GrpObj 𝒜], IsAbelianScheme 𝒜 → SmoothOfRelativeDimension g 𝒜.hom →
    ∀ (y₀ : B →ₐ[ℂ] ℂ) (A₀ : Over (Sp ℂ)) [GrpObj A₀] (φ₀ : A₀.left ⟶ 𝒜.left),
      IsGrpPullback A₀ 𝒜 (spMap (y₀ : B →+* ℂ)) φ₀ → ∀ (L₀ : LB A₀.left) (u₀ : HolUnif A₀ L₀ g)
      (F : Fam I g u₀.Λ) (σ : B →ₐ[ℂ] Hol F.V) (e : Unif F (𝒜.hom ≫ 𝟙 _) (σ : B →+* Hol F.V)), 0 ∈ F.V →
      (∀ b, y₀ b = (σ b).fn 0) → (∀ w, e.E (0, w) = (u₀.ex w).left ≫ φ₀) → (∀ x, F.τ x 0 = x) →
    ∀ (P₀ : u₀.Λ →+ HdR A₀), IsPeriodHom u₀ P₀ →
    ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ →
      (∀ a : ℂ, π (algebraMap ℂ D a) = a) →
      ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) →
      ∀ (j : B →ₐ[ℂ] D), (∀ b, j b = GlobalTheory.PeriodFamily.taylor N t (σ b).fn) →
      ∀ (A' : Over (Sp D)) [GrpObj A'] (φ' : A'.left ⟶ 𝒜.left), IsGrpPullback A' 𝒜 (spMap (j : B →+* D)) φ' →
      ∀ (m' : GrpMor (dp0 B) (𝟙 _) 𝒜 (dp0 D) (𝟙 _) A' (j : B →+* D) (spMap (j : B →+* D)) φ')
        (i : A₀.left ⟶ A'.left) (h : IsGrpPullback A₀ A' (spMap π) i), i ≫ φ' = φ₀ →
      ∀ (k : GrpMor (dp0 ℂ) (𝟙 _) A₀ κ (spMap π) A₀ (algebraMap ℂ D) (𝟙 _) (Over.Hom.left (𝟙 A₀)))
        (x : u₀.Λ) (d : Crys κ (spMap π) A₀), k.Corr (P₀ x) d → ∀ (c : primDR 𝒜) (per : u₀.Λ →+ Hol F.V),
        IsPeriod e c.1 per → crysToDR κ h d (m'.pull c) = GlobalTheory.PeriodFamily.taylor N t (per x).fn

end GlobalTheory.AnPer
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def htInf (y : GL (Fin a) (Cinf E)) : ℝ :=
  ∏ w : InfinitePlace E, htGL (Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) y)

def kerInf {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E))
    (F : GA E a → ℂ) (g : GA E a) : ℂ := ∫ x, k x * F (g * infGL E a (γ x)) ∂ν

def rspan (π : CuspSub E a) : Submodule ℂ (GA E a → ℂ) :=
  sInf {S | (∀ φ ∈ π.V, φ.1 ∈ S) ∧ (∀ F ∈ S, ∀ h : GA E a, (fun g => F (g * h)) ∈ S) ∧
    (∀ F ∈ S, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → kerInf ν k γ F ∈ S)}

theorem mem_rspan {π : CuspSub E a} {φ : Sm E a} (h : φ ∈ π.V) : φ.1 ∈ rspan π :=
  Submodule.mem_sInf.2 fun _ hS => hS.1 φ h

theorem rt_mem_rspan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ rspan π) (h : GA E a) :
    (fun g => F (g * h)) ∈ rspan π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.1 F (Submodule.mem_sInf.1 hF S hS) h

theorem kerInf_mem_rspan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ rspan π) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    kerInf ν k γ F ∈ rspan π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.2 F (Submodule.mem_sInf.1 hF S hS) X ν k γ hk

theorem rspan_le {π : CuspSub E a} {S : Submodule ℂ (GA E a → ℂ)} (h₁ : ∀ φ ∈ π.V, φ.1 ∈ S)
    (h₂ : ∀ F ∈ S, ∀ h : GA E a, (fun g => F (g * h)) ∈ S)
    (h₃ : ∀ F ∈ S, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → kerInf ν k γ F ∈ S) : rspan π ≤ S :=
  sInf_le ⟨h₁, h₂, h₃⟩

theorem one_le_htInf (y : GL (Fin a) (Cinf E)) : 1 ≤ htInf y := by
  unfold htInf
  calc (1 : ℝ) = ∏ _w : InfinitePlace E, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun w _ => one_le_htGL _

theorem htInf_pos (y : GL (Fin a) (Cinf E)) : 0 < htInf y := lt_of_lt_of_le one_pos (one_le_htInf y)

theorem htGL_le_htInf (y : GL (Fin a) (Cinf E)) (w : InfinitePlace E) :
    htGL (Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) y) ≤ htInf y := by
  classical
  unfold htInf
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
  refine le_mul_of_one_le_right (htGL_pos _).le ?_
  calc (1 : ℝ) = ∏ _w ∈ Finset.univ.erase w, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun w _ => one_le_htGL _

theorem norm_entry_le_htInf (y : GL (Fin a) (Cinf E)) (i j : Fin a) (w : InfinitePlace E) :
    ‖(y : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ≤ htInf y ∧
      ‖((y⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ≤ htInf y := by
  set p : GL (Fin a) (Cinf E) →* GL (Fin a) ℂ := Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)
  refine ⟨(norm_entry_le_htGL (p y) i j).trans (htGL_le_htInf y w), ?_⟩
  have e : ((y⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j w =
      (((p y)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j := by
    rw [← map_inv]; rfl
  rw [e]
  exact (norm_entry_le_htGL _ i j).trans ((htGL_inv (p y)).le.trans (htGL_le_htInf y w))

theorem height_le_htInf (y : GL (Fin a) (Cinf E)) : height y ≤ 3 * htInf y := by
  have h0 := (htInf_pos y).le
  have h1 : ‖toL y.val‖ ≤ htInf y :=
    pi_norm_le_iff_of_nonneg h0 |>.2 fun i => pi_norm_le_iff_of_nonneg h0 |>.2 fun j =>
      pi_norm_le_iff_of_nonneg h0 |>.2 fun w => (norm_entry_le_htInf y i j w).1
  have h2 : ‖toL (y⁻¹).val‖ ≤ htInf y :=
    pi_norm_le_iff_of_nonneg h0 |>.2 fun i => pi_norm_le_iff_of_nonneg h0 |>.2 fun j =>
      pi_norm_le_iff_of_nonneg h0 |>.2 fun w => (norm_entry_le_htInf y i j w).2
  unfold height
  linarith [one_le_htInf y]

theorem IsRapidInf.of_htInf {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)}
    (hk : Measurable k) (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)) i j)
    (hm : ∀ N : ℕ, Integrable (fun x => ‖k x‖ * htInf (γ x) ^ N) ν) : IsRapidInf ν k γ := by
  refine ⟨hk, Measurable.of_eval fun i => Measurable.of_eval fun j => hγ i j, fun N => ?_⟩
  refine ((hm N).const_mul (3 ^ N)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine (hk.norm.mul ?_).aestronglyMeasurable
    have hm' : Measurable fun x => toL (γ x).val :=
      Measurable.of_eval fun i => Measurable.of_eval fun j => hγ i j
    have hi : Measurable fun x => toL ((γ x)⁻¹).val := by
      refine Measurable.of_eval fun i => Measurable.of_eval fun j => Measurable.of_eval fun w => ?_
      set p : GL (Fin a) (Cinf E) →* GL (Fin a) ℂ :=
        Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)
      have e : (fun x => toL ((γ x)⁻¹).val i j w) =
          fun x => (((p (γ x))⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j := by
        funext x
        rw [← map_inv]; rfl
      rw [e]
      exact measurable_comp_GL (F := fun g : GL (Fin a) ℂ => ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)
        ((Units.continuous_coe_inv : Continuous fun g : GL (Fin a) ℂ =>
          ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)).matrix_elem i j)
        fun i' j' => (measurable_pi_apply w).comp (hγ i' j')
    unfold height
    exact ((measurable_const.add hm'.norm).add hi.norm).pow_const N
  · have h0 : 0 ≤ height (γ x) := by unfold height; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖k x‖ * height (γ x) ^ N ≤ ‖k x‖ * (3 * htInf (γ x)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (height_le_htInf _) N) (norm_nonneg _)
      _ = 3 ^ N * (‖k x‖ * htInf (γ x) ^ N) := by rw [mul_pow]; ring

theorem measurable_chart {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) : Measurable (chart φ g) := by
  classical
  have e : chart φ g = (invSet E a).piecewise (chart φ g) (fun _ => 0) := by
    funext x
    by_cases hx : x ∈ invSet E a
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
      exact dif_neg hx
  rw [e]
  exact (hφ g).continuousOn.measurable_piecewise continuousOn_const isOpen_invSet.measurableSet

theorem measurable_comp_infGL {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) {X : Type} [MeasurableSpace X]
    {γ : X → GL (Fin a) (Cinf E)} (hγ : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) :
    Measurable fun x => φ (g * infGL E a (γ x)) := by
  have h : Measurable fun x => toL (γ x).val := hγ
  have e : (fun x => φ (g * infGL E a (γ x))) = fun x => chart φ g (toL (γ x).val) :=
    funext fun x => (chart_val φ g (γ x)).symm
  rw [e]
  exact (measurable_chart hφ g).comp h

theorem IsRapidInf.integrable {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) {g : GA E a}
    (hg : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * infGL E a y)‖ ≤ C * height y ^ N) :
    Integrable (fun x => k x * φ (g * infGL E a (γ x))) ν := by
  obtain ⟨C, N, hC⟩ := hg
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N := pow_pos (by unfold height; positivity) N
    exact nonneg_of_mul_nonneg_left h hp
  refine ((hk.2.2 N).const_mul C).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (hk.1.mul (measurable_comp_infGL hφ g hk.2.1)).aestronglyMeasurable
  · rw [norm_mul]
    calc ‖k x‖ * ‖φ (g * infGL E a (γ x))‖ ≤ ‖k x‖ * (C * height (γ x) ^ N) :=
          mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
      _ = C * (‖k x‖ * height (γ x) ^ N) := by ring

theorem rspan_ne_bot (π : CuspSub E a) : rspan π ≠ ⊥ := by
  obtain ⟨φ, hφ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  intro hb
  have h := mem_rspan hφ
  rw [hb, Submodule.mem_bot] at h
  exact h0 (Subtype.ext h)

theorem rspan_le_leftInv (π : CuspSub E a) : rspan π ≤ SpanModel.leftInv E a := by
  refine rspan_le (fun φ hφ => (π.cusp φ hφ).1.left) (fun F hF h γ g => ?_) fun F hF X _ ν _ k γ _ γ' g => ?_
  · change F (ratGL E a γ * g * h) = F (g * h)
    rw [mul_assoc]; exact hF γ _
  · change kerInf ν k γ F (ratGL E a γ' * g) = kerInf ν k γ F g
    simp only [kerInf, mul_assoc]
    congr 1
    funext x
    rw [hF γ']

theorem rspan_left (π : CuspSub E a) {F : GA E a → ℂ} (hF : F ∈ rspan π) (γ : GL (Fin a) E) (g : GA E a) :
    F (ratGL E a γ * g) = F g :=
  rspan_le_leftInv π hF γ g

theorem rspan_eq_mspanR (π : CuspSub E a) : rspan π = mspanR π := by
  refine le_antisymm (rspan_le ?_ ?_ ?_) ?_
  · exact fun φ hφ => Submodule.mem_sInf.2 fun _ hS => hS.1 φ hφ
  · exact fun F hF h => Submodule.mem_sInf.2 fun S hS => hS.2.1 F (Submodule.mem_sInf.1 hF S hS) h
  · exact fun F hF X _ ν _ k γ hk => Submodule.mem_sInf.2 fun S hS => hS.2.2 F (Submodule.mem_sInf.1 hF S hS) X _ ν inferInstance k γ hk
  · refine sInf_le ⟨fun φ hφ => mem_rspan hφ, fun F hF h => rt_mem_rspan hF h, fun F hF X _ ν _ k γ hk => ?_⟩
    exact kerInf_mem_rspan hF ν hk


open Classical in
def plS (w : InfinitePlace E) : ℂ →ₙ+* Cinf E where
  toFun z := Pi.single w z
  map_mul' z z' := by ext w'; by_cases h : w' = w <;> simp [Pi.single_apply, h]
  map_zero' := by ext w'; simp [Pi.single_apply]
  map_add' z z' := by ext w'; by_cases h : w' = w <;> simp [Pi.single_apply, h]

def plGL (w : InfinitePlace E) : GL (Fin a) ℂ →* GL (Fin a) (Cinf E) := cornerGL a (plS w)



theorem isRapidInf_dirac (y : GL (Fin a) (Cinf E)) :
    IsRapidInf (Measure.dirac ()) (fun _ : Unit => (1 : ℂ)) (fun _ => y) :=
  ⟨measurable_const, measurable_const, fun _ => integrable_const _⟩

theorem kerInf_dirac (y : GL (Fin a) (Cinf E)) (F : GA E a → ℂ) (g : GA E a) :
    kerInf (Measure.dirac ()) (fun _ : Unit => (1 : ℂ)) (fun _ => y) F g = F (g * infGL E a y) := by
  simp [kerInf]

end GlobalTheory.JSW
end
end
