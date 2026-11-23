module

import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle017
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
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
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GenModel

open AlgebraicGeometry CategoryTheory

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X}

private theorem iota_multi_mem_span_of_mem_span {R : Subring Ω} {r : ℕ} {e : Fin r → E} (b : Fin r → E)
    (hb : ∀ i, b i ∈ Submodule.span R (Set.range e)) :
    exteriorPower.ιMulti Ω r b ∈ Submodule.span R {exteriorPower.ιMulti Ω r e} := by
  suffices H : ∀ s : Finset (Fin r), ∀ b : Fin r → E, (∀ i, b i ∈ Submodule.span R (Set.range e)) →
      (∀ i, i ∉ s → b i ∈ Set.range e) →
      exteriorPower.ιMulti Ω r b ∈ Submodule.span R {exteriorPower.ιMulti Ω r e} from
    H Finset.univ b hb (fun i hi => absurd (Finset.mem_univ i) hi)
  intro s
  refine Finset.induction_on s ?_ ?_
  · intro b _ hb'
    choose g hg using fun i => hb' i (Finset.notMem_empty i)
    have hbg : b = e ∘ g := funext fun i => (hg i).symm
    subst hbg
    by_cases hinj : Function.Injective g
    · have hσ := Finite.injective_iff_bijective.1 hinj
      have he : e ∘ g = e ∘ ⇑(Equiv.ofBijective g hσ) := rfl
      rw [he, AlternatingMap.map_perm, Units.smul_def]
      exact zsmul_mem (Submodule.mem_span_singleton_self _) _
    · rw [AlternatingMap.map_eq_zero_of_not_injective _ _ (fun h => hinj h.of_comp)]
      exact Submodule.zero_mem _
  · intro a s ha ih b hb hb'
    have key : ∀ y ∈ Submodule.span R (Set.range e),
        exteriorPower.ιMulti Ω r (Function.update b a y) ∈
          Submodule.span R {exteriorPower.ιMulti Ω r e} := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        apply ih
        · intro i
          rcases eq_or_ne i a with rfl | hi
          · simpa using Submodule.subset_span hy
          · rw [Function.update_of_ne hi]
            exact hb i
        · intro i hi
          rcases eq_or_ne i a with rfl | hia
          · simpa using hy
          · rw [Function.update_of_ne hia]
            exact hb' i (by simp [hia, hi])
      | zero =>
        rw [AlternatingMap.map_update_zero]
        exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        rw [AlternatingMap.map_update_add]
        exact Submodule.add_mem _ hx hy
      | smul c x _ hx =>
        rw [Subring.smul_def, AlternatingMap.map_update_smul, ← Subring.smul_def]
        exact Submodule.smul_mem _ c hx
    have hk := key (b a) (hb a)
    rwa [Function.update_eq_self] at hk

theorem wedge_of_frame {L : Lat ξ E} {r : ℕ} {e : Fin r → E} {x : Cpt ξ} (h : L.IsFrameAt e x) :
    L.wedge r x = Submodule.span (regAt ξ x) {exteriorPower.ιMulti Ω r e} := by
  obtain ⟨-, hL⟩ := h
  change Submodule.span (regAt ξ x)
    {w | ∃ b : Fin r → E, (∀ i, b i ∈ L x) ∧ w = exteriorPower.ιMulti Ω r b} = _
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro w ⟨b, hb, rfl⟩
    rw [hL] at hb
    exact iota_multi_mem_span_of_mem_span b hb
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine Submodule.subset_span ⟨e, fun i => ?_, rfl⟩
    rw [hL]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem ιMulti_ne_zero {r : ℕ} {e : Fin r → E} (h : LinearIndependent Ω e) :
    exteriorPower.ιMulti Ω r e ≠ 0 := by
  apply PositivityTheory.Xgn.ComponentDegreeAlt.wedge_ne_zero <;> assumption

end General

section Int

open CptModel

end Int

end GlobalTheory.CompanionTheory.Ar.Flat.GenModel
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def EmbedsGeneric {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {κ : Type}
    (x : κ → Ω) : Prop :=
  ∀ p : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r p) → (∃ i, InChart ξ x i p) ∧ ∀ i, InChart ξ x i p →
    (∀ a ∈ regAt ξ p, ∃ s ∈ Algebra.adjoin ℚ (Set.range fun j => x j / x i), unitAt ξ p s ∧
      s * a ∈ Algebra.adjoin ℚ (Set.range fun j => x j / x i)) ∧
    ∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → InChart ξ x i q →
      (∀ s ∈ Algebra.adjoin ℚ (Set.range fun j => x j / x i), unitAt ξ p s ↔ unitAt ξ q s) → p = q

structure RefGeo (Y : Model Xo c β) where

  Ω : Type
  [fld : Field Ω]
  [cz : CharZero Ω]

  K : Type
  [finK : Fintype K]

  J : K → Type
  [finJ : ∀ k, Fintype (J k)]

  y : (Σ k, J k) → Ω

  𝔐 : HodgeCpt Y ∅ y

  Fl : 𝔐.Flag
  deg_one : Fl.deg = 1

  xdeg : RootIx D → K → ℤ

  e : RootIx D → Ω
  lines : Fl.RootLines xdeg e

  bd : Ideal (MRing J)
  snc : Cmp.IsSncModel y (Top.dimFl (CMType H) (D.p + D.q)) bd
  bd_iff : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ mcPts bd ↔ ¬ 𝔐.Interior z)

  k₀ : K
  embeds : EmbedsGeneric 𝔐.ξ fun i : J k₀ => y ⟨k₀, i⟩

attribute [instance] RefGeo.fld RefGeo.cz RefGeo.finK RefGeo.finJ

structure RefGeo.An {Y : Model Xo c β} (G : RefGeo Y) where

  sing : RootIx D → HermLine G.J
  sing_deg : ∀ r, (sing r).a = G.xdeg r
  hodge : ∀ r, G.Fl.IsHodgeLine r (G.e r) (sing r)

  Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))

  Re : PB.Realis Sys (mCoordIdeal G.y)
  J_top : Re.J = ⊤
  deg_one : Re.deg = 1
  π_bij : Function.Bijective Re.π
  embedded : Cmp.IsEmbedded Re.R.A (mCoordIdeal G.y) Re.R.U Re.R.lift
  interior : ∀ x (z : Spec (CommRingCat.of ℂ) ⟶ G.𝔐.X), CoordsAt G.𝔐.ξ G.y z (Re.R.lift x x) →
    (G.𝔐.Interior z ↔ Re.π x ∈ Sys.open')
  fund_deg : ∀ τ i, (Re.ref (some (τ, i))).a = -∑ k ∈ Finset.Iic i, G.xdeg (τ, k)
  fund_sing : ∀ τ i x, Re.π x ∈ Sys.open' →
    Real.log ((Re.ref (some (τ, i))).h (Re.R.lift x x)) + Sys.ph (some (τ, i)) (Re.π x) =
      -∑ k ∈ Finset.Iic i, Real.log ((sing (τ, k)).h (Re.R.lift x x))
  conj : ∀ a t, IsSmoothHerm (Re.line a t) ∧ IsConjInvariantH (Re.line a t)
  none_deg : (Re.ref none).a G.k₀ = 1 ∧ ∀ k, k ≠ G.k₀ → (Re.ref none).a k = 0
  none_h : ∀ z, (Re.ref none).h z = Real.sqrt (∑ i, ‖z ⟨G.k₀, i⟩‖ ^ 2)
  pos : ReciprocityTheory.AnForm.M.IsPosPot Sys.A (Sys.th none)
  ph_none : ∀ x, Sys.ph none x = 0 ∧ ∀ t, Sys.phT none t x = 0
  flat : ∀ τ (i : Fin (D.p + D.q)), (i : ℕ) + 1 = D.p + D.q → ∀ t,
    ReciprocityTheory.AnForm.M.IsPsh Sys.A ((Sys.potT (some (τ, i)) t).rsmul (-1)) ∧
      ReciprocityTheory.AnForm.M.IsPsh Sys.A (Sys.potT (some (τ, i)) t)

def RefGeo.IsEff {Y : Model Xo c β} (G : RefGeo Y) (n : RootIx D → ℤ) (q' : ℕ) (s : G.Ω) : Prop :=
  ∀ p : Cpt G.𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre G.𝔐.ξ r p) → ∀ (i : G.J G.k₀) (t : G.Ω),
    InChart G.𝔐.ξ (fun i' : G.J G.k₀ => G.y ⟨G.k₀, i'⟩) i p → (Lat.tens G.Fl.rootLat fun r => -n r).IsGenAt p t →
      s * G.y ⟨G.k₀, i⟩ ^ q' / t ∈ regAt G.𝔐.ξ p ∧
        (p.1 ∉ abLocus G.𝔐.t.G → ¬ unitAt G.𝔐.ξ p (s * G.y ⟨G.k₀, i⟩ ^ q' / t))

end GlobalTheory.CompanionTheory.Ar
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct

section General

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

def TorsVal (P : RigLB G) {n : ℕ} (s : Out.H0 P.L n) {F : Type} [Field F] {b : Sp F ⟶ S} (y : Over.mk b ⟶ G)
    (N : ℕ) (T : F) : Prop :=
  1 ≤ N ∧ y ^ N = 1 ∧
  ∃ (w : LB.Gen (LB.LinComb P.L (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)]))
    (i₀ i : P.L.ι), w.IsGen ∧ ⊤ ≤ (1 : Over.mk b ⟶ G).left ⁻¹ᵁ P.L.U i₀ ∧ ⊤ ≤ y.left ⁻¹ᵁ P.L.U i ∧
    T * (valF (1 : Over.mk b ⟶ G).left _ (w.s ![i₀, i₀]).val *
        valF (X := (𝟙_ (Over S)).left) b _ (P.rig.s fun _ => i₀).val ^ (N ^ 2)) ^ n =
      valF y.left _ (s.f fun _ => i) ^ (N ^ 2) * valF y.left _ (w.s ![i₀, i]).val ^ n

structure ArchFrame (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ) where

  A : Over (Sp ℂ)
  [grp : GrpObj A]

  φ : A.left ⟶ G.left
  cart : IsGrpPullback A G z φ

  u : HolUnif A (P.L.pull φ) g

  Hm : Matrix (Fin g) (Fin g) ℂ

  χ : u.Λ → ℂ
  ah : u.IsAH Hm χ
  rig : ∀ i : P.L.ι, ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i →
    u.fr (fun _ => i) 0 = valF (X := (𝟙_ (Over S)).left) z _ (P.rig.s fun _ => i).val

attribute [instance] ArchFrame.grp

namespace ArchFrame

variable {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ} (a : ArchFrame P z g)

def pt (w : Fin g → ℂ) : Sp ℂ ⟶ G.left := (a.u.ex w).left ≫ a.φ

def IsFn {n : ℕ} (s : Out.H0 P.L n) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (i : P.L.ι) (w : Fin g → ℂ), ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i →
    valF (a.pt w) _ (s.f fun _ => i) = θ w * a.u.fr (fun _ => i) w ^ n

def herm (w w' : Fin g → ℂ) : ℂ := w ⬝ᵥ a.Hm.mulVec (star w')

def nrm (n : ℕ) (θ : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) : ℝ :=
  ‖θ w‖ * Real.exp (-(Real.pi * n / 2) * (a.herm w w).re)

def IsTheta (n : ℕ) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  Differentiable ℂ θ ∧ ∀ (l : a.u.Λ) (w : Fin g → ℂ),
    θ (w + l) = (a.χ l * Complex.exp (Real.pi * a.herm w l + Real.pi / 2 * a.herm l l)) ^ n * θ w

def IsThetaMeanSquareNorm (θ : (Fin g → ℂ) → ℂ) (b : ℝ) : Prop :=
  0 < b ∧ ∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain a.u.Λ Fd volume →
    b ^ 2 = (∫ w in Fd, a.nrm 1 θ w ^ 2) / (volume Fd).toReal

def IsTan (c : Fin g → ℂ) (v : epsAt z ⟶ G) : Prop :=
  ∃ v' : epsR ℂ ⟶ a.A, v'.left ≫ a.φ = v.left ∧ a.u.IsDiff c v'

end ArchFrame

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

structure PPData (H : Host E) (L : Type) [Field L] [NumberField L] where

  t : SAB H (Sp (𝓞 L))

  tK : SAB H (Sp L)
  m : SABMap tK t (spMap (algebraMap (𝓞 L) L))
  princ : IsPrincipal tK

  B : HermitianBundle.{0} L
  MB : LieModel t.G (𝟙 _) B.carrier
  fib : IsFibre (HodgeIP t.G t.PP.L) (𝟙 _) B MB

abbrev emb {L : Type} [Field L] [NumberField L] (σ : L →+* ℂ) : Sp ℂ ⟶ Sp (𝓞 L) :=
  spMap (σ.comp (algebraMap (𝓞 L) L))

def mean (L : Type) [Field L] [NumberField L] (f : (L →+* ℂ) → ℝ) : ℝ := (∑ σ : L →+* ℂ, f σ) / Module.finrank ℚ L

namespace PPData

variable {H : Host E} {L : Type} [Field L] [NumberField L] (D : PPData H L)

def g : ℕ := Module.finrank (𝓞 L) D.B.carrier

def hp : ℝ := max (-D.B.normDegree ⊤) 0

abbrev Frame (σ : L →+* ℂ) := ArchFrame D.t.PP (emb σ) D.g

def len (σ : L →+* ℂ) (x : D.B.carrier) : ℝ :=
  Real.sqrt ((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) : ℂ).re

def IsVec {σ : L →+* ℂ} (a : D.Frame σ) (x : D.B.carrier) (c : Fin D.g → ℂ) : Prop :=
  ∃ v : epsAt (emb σ) ⟶ D.t.G, (v.left ≫ (𝟙 D.t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt x).left) ∧ a.IsTan c v

abbrev Ext {L' : Type} [Field L'] [NumberField L'] [Algebra L L'] (D' : PPData H L') :=
  SABMap D'.t D.t (spMap (algebraMap (𝓞 L) (𝓞 L')))

def HasTheta (th : Out.H0 D.t.PP.L 1) (Φ : ℝ) : Prop :=
  ∃ b : (L →+* ℂ) → ℝ, (∀ (σ : L →+* ℂ) (a : D.Frame σ) θ, a.IsFn th θ → a.IsThetaMeanSquareNorm θ (b σ)) ∧
    mean L (fun σ => Real.log (b σ)) ≤ Φ

def SupLe {n : ℕ} (s : Out.H0 D.t.PP.L n) (M : (L →+* ℂ) → ℝ) : Prop :=
  ∀ (σ : L →+* ℂ) (a : D.Frame σ) θ, a.IsFn s θ → ∀ w, a.nrm n θ w ≤ M σ

end PPData

def KeyDegSt : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L]
    [NumberField L] (D : PPData H L), 1 ≤ D.g →
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (D' : PPData H L') (_ : D.Ext D')
      (th : Out.H0 D'.t.PP.L 1), D'.HasTheta th (D.hp / 2 + C * D.g)

def LineSt : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L]
    [NumberField L] (D : PPData H L) (x : D.B.carrier), x ≠ 0 →
    -mean L (fun σ => Real.log (D.len σ x)) ≤ C * Real.log (2 + D.g + D.hp)

end GlobalTheory.CompanionTheory.Ar.Sl
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.ModelTest

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

theorem bar_eq (H : Host E) (a : 𝓞 E) : RingOfIntegers.mapRingEquiv (cmConj E) a = H.bar a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq a]
  rfl

theorem overZp_of_inFibre {p : ℕ} (hp : p.Prime) (q : Cpt 𝔐.ξ) (hq : InFibre 𝔐.ξ p q) : OverZp 𝔐 p q := by
  intro r hr hrq
  by_contra hne
  have hloc : IsLocalRing (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q) :=
    IsLocalRing.of_surjective' (GlobalTheory.CompanionTheory.Ar.genMap 𝔐.ξ q).rangeRestrict
      (GlobalTheory.CompanionTheory.Ar.genMap 𝔐.ξ q).rangeRestrict_surjective
  have key : ∀ m : ℕ, GlobalTheory.CompanionTheory.Ar.InFibre 𝔐.ξ m q → ¬ IsUnit ((m : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q)) := by
    intro m hm hu
    apply hm
    obtain ⟨u, hu'⟩ := hu
    have h1 : (m : Ω) * (((u⁻¹ : (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q)ˣ) : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q) : Ω) = 1 := by
      have h2 := congrArg (fun x : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q => (x : Ω)) u.mul_inv
      simpa [hu'] using h2
    have h0 : (m : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    refine ⟨h0, natCast_mem _ m, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact SetLike.coe_mem _
  have hcop : Nat.Coprime r p := (Nat.coprime_primes hr hp).2 hne
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q))
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
  · exact key r hrq (by simpa using isUnit_of_mul_isUnit_right h)
  · exact key p hq (by simpa using isUnit_of_mul_isUnit_right h)

variable {𝔐} {p : ℕ} {o : Type} [CommRing o] [Algebra o Ω]
  {Dc Dc' : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0},
      HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)}

end GlobalTheory.CompanionTheory.Ar.HT.ModelTest
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TowerOriginModel

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l}

variable {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {T : Top.RootTower (CMType H) (D.p + D.q)}

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y' : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (D.p + D.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y' Sys}

theorem pi_pt_ne (o : RootOrigin Y' S RM Fx) (x : o.Re.R.X) :
    ∃ a : ℂ, a ≠ 0 ∧ (fun i => o.Re.R.lift x x ⟨o.k₀, o.ix i⟩) = a • Fx.pt (o.Re.π x) := by
  obtain ⟨a, ha⟩ := o.π_pt x
  refine ⟨a, ?_, ha⟩
  rintro rfl
  obtain ⟨hnz, -⟩ := o.Re.R.mem x x (o.Re.R.mem_U x)
  obtain ⟨i, hi⟩ := hnz o.k₀
  apply hi
  have h := congrFun ha (o.ix.symm i)
  simp only [Equiv.apply_symm_apply, zero_smul, Pi.zero_apply] at h
  exact h

end GlobalTheory.CompanionTheory.Ar.TowerOriginModel
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

def HodgeCpt.OmVB {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω]
    {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) : Prop :=
  ∀ p ∈ S, (𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p)).IsVBOn {q | InFibre 𝔐.ξ p q} (Module.finrank Ω 𝔐.Li) ⊤ ∧
    ∀ s, ((𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p)).map (𝔐.Vgen s).dualRestrict).IsVBOn {q | InFibre 𝔐.ξ p q}
      (labelRk D s) ⊤

def IsTowerOf (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (D.p + D.q)) : Prop :=
  ∃ o : TowerOrigin Y T, ∀ B a, (o.Or B a).𝔐.OmVB

def SplitComps {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) : Prop :=
  ∀ (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ Y.X) (cst : c.F →+* Ω), IsCptGen ξ →
    ξ ≫ Y.s = spMap (cst.comp β) → ∀ a : Ω, IsAlgebraic ℤ a → a ∈ cst.range

end GlobalTheory.CompanionTheory.Ar
end
end
