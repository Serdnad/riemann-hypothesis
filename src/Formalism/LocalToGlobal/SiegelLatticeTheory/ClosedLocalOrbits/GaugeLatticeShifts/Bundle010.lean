module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle009
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.PeriodIntegrals.Bundle003
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq

@[expose] public section

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ScalarFrameCT : Prop :=
  ∀ (D : D7) (Z : LocDat D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' F'' : LFlag (D.sp.Y 0) D.R.rS T') (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (Tn T'n : ℕ),
    FixedHyp D Λ F → IsLift Λ F' → IsLift Λ F'' → IsFixedConv Λ (gS D) F' → IsFixedConv Λ (gS D) F'' →
    IsAdmissible Λ (gS D) F F' → IsAdmissible Λ (gS D) F F'' →
    IsPair Λ F F' F'' β (gS D) → IsGeneric Λ (gS D) F F' → IsGeneric Λ (gS D) F F'' →
    Lat.s0 Λ F F' F'' β D.R.k = 1 → IsScalar Λ F F' F'' β → Gval F F' ≠ 0 → Gval F F'' ≠ 0 →
    T ≠ 0 → T' ≠ 0 →
    ∀ p : PlF D, (locH Z p).IsScalarPair (locTerm Z p Λ F F' Tn T'n) (locTerm Z p Λ F F'' Tn T'n)

def IotaStep : Prop :=
  ∀ (D : D7) (Z : LocDat D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' F'' : LFlag (D.sp.Y 0) D.R.rS T') (β : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    FixedHyp D Λ F → IsLift Λ F' → IsLift Λ F'' → IsFixedConv Λ (gS D) F' → IsFixedConv Λ (gS D) F'' →
    IsAdmissible Λ (gS D) F F' → IsAdmissible Λ (gS D) F F'' →
    IsPair Λ F F' F'' β (gS D) → IsGeneric Λ (gS D) F F' → IsGeneric Λ (gS D) F F'' →
    Lat.s0 Λ F F' F'' β D.R.k = 1 → IsScalar Λ F F' F'' β → Gval F F' ≠ 0 → Gval F F'' ≠ 0 →
    T ≠ 0 → T' ≠ 0 →
    ∀ p : PlF D, IotaEl Z p Λ (frame F) (frameAct (frame F') (admXi D Λ F F')⁻¹)
      (frameAct (frame F'') (admXi D Λ F F'')⁻¹) β

end Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  Formalism.L2.SG.Pf.ScalarFramePf

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal Matrix

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

def DimG : Prop :=
  ∀ k r : ℕ, Module.finrank ℝ (Formalism.MainNotions.S.lieE (UH (Hpk k r))) =
    2 * Module.finrank ℝ (Formalism.MainNotions.S.lieE (Nset k r)) + 2 * r + Module.finrank ℝ (Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r))

def LieG : Prop :=
  ∀ k r : ℕ, Formalism.MainNotions.S.lieOf (UH (Hpk k r)) = {X | Hpk k r * Xᴴ * Hpk k r + X = 0}

def LieWb : Prop :=
  ∀ k r : ℕ, Formalism.MainNotions.S.lieOf (Formalism.FourierDecayAlt.B2.UWb k r) = {X | Hpk k r * Xᴴ * Hpk k r + X = 0 ∧
    ∀ a : Fin r, X *ᵥ bvec (eI k r a) = 0 ∧ X *ᵥ bvec (esI k r a) = 0}

def expL (k r : ℕ) (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (Y : Formalism.MainNotions.S.lieE S) : Mt k r :=
  fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (Y : EuclideanSpace ℝ _)) i j

def RhoN : Prop :=
  ∀ (k r : ℕ) (Y : Formalism.MainNotions.S.lieE (Nset k r)), rhoS k r (Nset k r) (expL k r (Nset k r) Y) = (‖Y‖₊ : ℝ≥0∞)

def RhoMeas : Prop :=
  ∀ (k r : ℕ) (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)), Measurable (rhoS k r S)

def ModelVol : Prop :=
  ∀ (E1 E2 : Type) [NormedAddCommGroup E1] [InnerProductSpace ℝ E1] [FiniteDimensional ℝ E1] [MeasurableSpace E1]
    [BorelSpace E1] [NormedAddCommGroup E2] [InnerProductSpace ℝ E2] [FiniteDimensional ℝ E2] [MeasurableSpace E2]
    [BorelSpace E2] (r : ℕ) (s : ℝ), 0 < s →
    ∫⁻ c : Fin r → ℂ, ∫⁻ y1 : E1, ∫⁻ y2 : E2, ∫⁻ y3 : E1,
      (if (‖y1‖₊ : ℝ≥0∞) ^ 2 + ENNReal.ofReal (2 * ∑ a, ‖c a - 1‖ ^ 2) + (‖y2‖₊ : ℝ≥0∞) ^ 2 + (‖y3‖₊ : ℝ≥0∞) ^ 2 <
          ENNReal.ofReal (s ^ 2) then (1 : ℝ≥0∞) else 0) =
      ENNReal.ofReal ((2 : ℝ) ^ r)⁻¹ *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * Module.finrank ℝ E1 + 2 * r + Module.finrank ℝ E2))) s)

def BallDim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (s : ℝ),
    volume (Metric.ball (0 : E) s) = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) s)

end Formalism.L2.SG.Pf.BH
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section GenericX

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem identResp_generic {r : ℕ} (abelian₂ : Submodule M.L.O V) (f₀ f₁ f₂ : Fin (r + 1) → V) (T T' : F)
    (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w)
    (h12 : ∀ x ∈ H.X f₁, e x ∈ H.X f₂) (h21 : ∀ y ∈ H.X f₂, e.symm y ∈ H.X f₁)
    (hX0 : ∀ a ∈ H.X f₀, ∀ b ∈ H.X f₀, H.h a b = 0) (hX2 : ∀ a ∈ H.X f₂, ∀ b ∈ H.X f₂, H.h a b = 0)
    (hL : ∀ x ∈ abelian₂, e x ∈ abelian₂) (hL' : ∀ x ∈ abelian₂, e.symm x ∈ abelian₂)
    (hW0 : ∀ w ∈ H.W0 f₀ f₁, ∃ w₂ ∈ H.W0 f₀ f₂, w - w₂ ∈ H.X f₀ ∧ e w - w₂ ∈ H.X f₂)
    (homp : H.Dl f₀ f₂ (r + 1) • H.om' f₀ f₁ - H.Dl f₀ f₁ (r + 1) • H.om' f₀ f₂ ∈ H.X f₀)
    (hom : M.L.cj (H.Dl f₀ f₂ (r + 1)) • e (H.om f₀ f₁) - M.L.cj (H.Dl f₀ f₁ (r + 1)) • H.om f₀ f₂ ∈ H.X f₂)
    (hrat : H.Dl f₀ f₁ r * H.Dl f₀ f₂ (r + 1) = H.Dl f₀ f₂ r * H.Dl f₀ f₁ (r + 1))
    (hz : e (f₁ (Fin.last r)) - f₂ (Fin.last r) ∈ H.X f₂)
    (hI : ∀ g, M.split = some g → IotaG H (algebraMap F E (g.q : F)) abelian₂ f₀ f₁ f₂ e) :
    H.Ident (⟨abelian₂, f₀, f₁, T, T'⟩ : Loc.Term V M r) ⟨abelian₂, f₀, f₂, T, T'⟩ (LinearEquiv.refl _ _)
        (qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21) ∧
      H.Respects (⟨abelian₂, f₀, f₁, T, T'⟩ : Loc.Term V M r) ⟨abelian₂, f₀, f₂, T, T'⟩ (LinearEquiv.refl _ _)
        (qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hrat⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x y x₂ y₂ hx hy
    exact h_eq_of_sub_mem H _ hX0 x.2 y.2 ((mk_eq_iff H _ x x₂).1 hx) ((mk_eq_iff H _ y y₂).1 hy)
  · intro x y x₂ y₂ hx hy
    have hx' : e x - x₂ ∈ H.X f₂ := (mk_eq_iff H _ _ x₂).1 hx
    have hy' : e y - y₂ ∈ H.X f₂ := (mk_eq_iff H _ _ y₂).1 hy
    rw [h_eq_of_sub_mem H _ hX2 (perp_map H e hiso _ _ h21 x.2) (perp_map H e hiso _ _ h21 y.2) hx' hy',
      hiso]
  · intro w hw
    obtain ⟨w₂, hw₂, h1, h2⟩ := hW0 w hw
    refine ⟨w₂, hw₂, ?_, ?_⟩
    · intro x x₂ hx hx₂
      apply smul_mk_eq H
      rw [one_smul, one_smul, hx, hx₂]
      exact h1
    · intro x x₂ hx hx₂
      apply smul_mk_eq H
      show (1 : E) • e x - (1 : E) • (x₂ : V) ∈ H.X f₂
      rw [one_smul, one_smul, hx, hx₂]
      exact h2
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    rw [hx, hx₂]
    exact homp
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    show M.L.cj (H.Dl f₀ f₂ (r + 1)) • e x - M.L.cj (H.Dl f₀ f₁ (r + 1)) • (x₂ : V) ∈ H.X f₂
    rw [hx, hx₂]
    exact hom
  · ext w
    simp
  · intro x x₂ hx hx₂
    have : x = x₂ := Subtype.ext (hx.trans hx₂.symm)
    rw [this]
    rfl
  · ext w
    constructor
    · rintro ⟨_, ⟨x, hxΛ, rfl⟩, rfl⟩
      exact ⟨perpEquiv H e hiso _ _ h12 h21 x, hL _ hxΛ, rfl⟩
    · rintro ⟨x₂, hx₂Λ, rfl⟩
      refine ⟨H.mkW _ ⟨e.symm x₂, perp_map_symm H e hiso _ _ h12 x₂.2⟩,
        ⟨⟨e.symm x₂, perp_map_symm H e hiso _ _ h12 x₂.2⟩, hL' _ hx₂Λ, rfl⟩, ?_⟩
      show qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21 (Submodule.Quotient.mk _) = Submodule.Quotient.mk x₂
      rw [qEquiv_mk]
      congr 1
      exact Subtype.ext (e.apply_symm_apply x₂)
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    show (1 : E) • e x - (1 : E) • (x₂ : V) ∈ H.X f₂
    rw [one_smul, one_smul, hx, hx₂]
    exact hz
  · intro g hg
    obtain ⟨hA, hB⟩ := hI g hg
    ext ⟨a, b⟩
    constructor
    · rintro ⟨⟨a0, b0⟩, ⟨x', x, hx'Λ, hxΛ, hq, heq⟩, hmap⟩
      obtain ⟨y, y'', hyΛ, hy''Λ, hyp, hy''p, hxy, hxy'', hyq⟩ := hA x x' hxΛ hx'Λ x.2 x'.2 hq
      refine ⟨⟨y'', hy''p⟩, ⟨y, hyp⟩, hy''Λ, hyΛ, hyq, ?_⟩
      simp only [Prod.map, Prod.mk.injEq] at hmap heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨rfl, rfl⟩ := hmap
      refine Prod.ext ?_ ?_
      · show qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21 (Submodule.Quotient.mk x') = Submodule.Quotient.mk _
        rw [qEquiv_mk, mk_eq_iff]
        exact hxy''
      · show Submodule.Quotient.mk x = Submodule.Quotient.mk _
        rw [mk_eq_iff]
        exact hxy
    · rintro ⟨x'', x, hx''Λ, hxΛ, hq, heq⟩
      obtain ⟨y, y', hyΛ, hy'Λ, hyp, hy'p, hxy, hxy', hyq⟩ := hB x x'' hxΛ hx''Λ x.2 x''.2 hq
      refine ⟨(H.mkW _ ⟨y', hy'p⟩, H.mkW _ ⟨y, hyp⟩), ⟨⟨y', hy'p⟩, ⟨y, hyp⟩, hy'Λ, hyΛ, hyq, rfl⟩, ?_⟩
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      refine Prod.ext ?_ ?_
      · show qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21 (Submodule.Quotient.mk _) = Submodule.Quotient.mk x''
        rw [qEquiv_mk, mk_eq_iff]
        have h := h12 _ hxy'
        rw [map_sub, LinearEquiv.apply_symm_apply] at h
        have h' := Submodule.neg_mem _ h
        rwa [neg_sub] at h'
      · show Submodule.Quotient.mk _ = Submodule.Quotient.mk x
        rw [mk_eq_iff]
        have h' := Submodule.neg_mem _ hxy
        rwa [neg_sub] at h'

end GenericX

section ConcreteX

variable {D : D7} (Z : LocDat D) (p : PlF D)

def phiP (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hG : GFacts Λ f g1 g2 β) :
    (locH Z p).Wb (fun b => sF' Z p b • baseChange₂ D p (g1 b)) ≃ₗ[(D.s.atP p).Ep]
      (locH Z p).Wb (fun b => sF' Z p b • baseChange₂ D p (g2 b)) :=
  qEquiv (locH Z p) (betaP p β) (betaP_iso Z p β hG.iso) _ _
    (fun x hx => betaP_mem_X Z p β g1 g2 (sF' Z p) (isUnit_sF' Z p) hG.xmap hx)
    (fun y hy => betaP_symm_mem_X Z p β g1 g2 (sF' Z p) (isUnit_sF' Z p) hG.xmap' hy)

theorem identResp_lt (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Tn T'n : ℕ) (hG : GFacts Λ f g1 g2 β)
    (hI : IotaEl Z p Λ f g1 g2 β) :
    (locH Z p).Ident (lt Z p Λ f g1 Tn T'n) (lt Z p Λ f g2 Tn T'n) (LinearEquiv.refl _ _) (phiP Z p Λ f g1 g2 β hG) ∧
      (locH Z p).Respects (lt Z p Λ f g1 Tn T'n) (lt Z p Λ f g2 Tn T'n) (LinearEquiv.refl _ _)
        (phiP Z p Λ f g1 g2 β hG) := by
  have hiso : ∀ v w, (locH Z p).h (betaP p β v) (betaP p β w) = (locH Z p).h v w := betaP_iso Z p β hG.iso
  refine identResp_generic (locH Z p) (lattice₂ D Z.M p Λ) (fun a => sF Z p a • baseChange₂ D p (f a))
    (fun b => sF' Z p b • baseChange₂ D p (g1 b)) (fun b => sF' Z p b • baseChange₂ D p (g2 b)) _ _ (betaP p β) hiso
    (fun x hx => betaP_mem_X Z p β g1 g2 (sF' Z p) (isUnit_sF' Z p) hG.xmap hx)
    (fun y hy => betaP_symm_mem_X Z p β g1 g2 (sF' Z p) (isUnit_sF' Z p) hG.xmap' hy) ?_ ?_
    (fun x hx => betaP_lat Z p β Λ hG.lam hx) (fun x hx => betaP_symm_lat Z p β Λ hG.lam' hx)
    (fun w hw => scalar_frame_w_zero_exists Z p Λ f g1 g2 β hG hw) ?_ ?_ ?_ ?_ hI
  · apply iso_span
    intro i j
    rw [h_bcP, brS, hG.fiso j i, map_zero, mul_zero]
  · apply iso_span
    intro i j
    rw [h_bcP, brS, hG.g2iso j i, map_zero, mul_zero]
  ·
    rw [om'_loc, om'_loc, dl_loc Z p f g2 (sF Z p) (sF' Z p) _ le_rfl,
      dl_loc Z p f g1 (sF Z p) (sF' Z p) _ le_rfl]
    rw [omp_combine]
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p f (sF Z p) (isUnit_sF Z p) hG.omp)
  ·
    rw [om_loc, om_loc, dl_loc Z p f g2 (sF Z p) (sF' Z p) _ le_rfl,
      dl_loc Z p f g1 (sF Z p) (sF' Z p) _ le_rfl, map_smul, betaP_bc]
    rw [om_combine]
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p g2 (sF' Z p) (isUnit_sF' Z p) hG.om)
  ·
    rw [dl_loc Z p f g1 (sF Z p) (sF' Z p) _ (Nat.le_succ _), dl_loc Z p f g2 (sF Z p) (sF' Z p) _ le_rfl,
      dl_loc Z p f g2 (sF Z p) (sF' Z p) _ (Nat.le_succ _), dl_loc Z p f g1 (sF Z p) (sF' Z p) _ le_rfl]
    have h := congrArg (D.s.atP p).ιE hG.ratio
    rw [map_mul, map_mul] at h
    linear_combination ((∏ i : Fin D.R.rS, (Z.M p).L.cj (sF Z p (Fin.castLE (Nat.le_succ _) i))) *
      (∏ i : Fin D.R.rS, sF' Z p (Fin.castLE (Nat.le_succ _) i)) *
      ((∏ i : Fin (D.R.rS + 1), (Z.M p).L.cj (sF Z p (Fin.castLE le_rfl i))) *
      (∏ i : Fin (D.R.rS + 1), sF' Z p (Fin.castLE le_rfl i)))) * h
  ·
    show betaP p β (sF' Z p (Fin.last _) • baseChange₂ D p (g1 (Fin.last _))) -
      sF' Z p (Fin.last _) • baseChange₂ D p (g2 (Fin.last _)) ∈ _
    rw [map_smul, betaP_bc, ← smul_sub, ← map_sub]
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p g2 (sF' Z p) (isUnit_sF' Z p) hG.zmap)

end ConcreteX

end Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  Formalism.L2.SG.Pf.ScalarFramePf

end Formalism.L2.SG.Pf
end
end

section

namespace Formalism.L2.SG.Pf.GE

theorem existsGaugeNormalizedStabilizer : ExistsGaugeMeasureForEachRank := (show PI.ExistsGaugeMeasureForEachRank.ExistsGaugeMeasureForEachRank ↔ ExistsGaugeMeasureForEachRank from Iff.rfl).mp _root_.exists_gaugeNormalizedStabilizer

end Formalism.L2.SG.Pf.GE
end

section

noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting

namespace Formalism.L2.SG.NormCut

section Phase

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

def scOf {u : D.what₂.Word} {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X u rs) (ρ : c.Cl) :
    Iof TR :=
  levi TR (((c.h (c.base (c.lamOf ρ)) : X.B.I.Gf) * X.xu u)⁻¹ * ((c.h ρ : X.B.I.Gf) * X.xu u))

def Aset {u : D.what₂.Word} {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X u rs)
    (q : {Λ // Λ ∈ rs}) : Set (Iof TR) :=
  {x | ∃ γ : Formalism.L2.SG.PoincareInHH.PoincareSetting.Gam X u,
    ((c.h (c.base q.1) : X.B.I.Gf) * X.xu u)⁻¹ * (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u γ : X.B.I.Gf) *
        ((c.h (c.base q.1) : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset ∧
      x = levi TR (((c.h (c.base q.1) : X.B.I.Gf) * X.xu u)⁻¹ *
        (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u γ : X.B.I.Gf) * ((c.h (c.base q.1) : X.B.I.Gf) * X.xu u))}

variable {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')


variable (F0 F0') in
def LeviCols : Prop :=
  ∀ (t : GTerm X u u' F0 F0' what₂ rows') (ρ : cs.Cl) (ρ' : cs'.Cl), cs.lamOf ρ = t.lam → cs'.lamOf ρ' = t.lam' →
    levi TR (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt) =
      (scOf TR cs ρ)⁻¹ * iotaOf TR cs cs' t * scOf TR cs' ρ'


variable (F0 F0') in
def PhaseAt : Prop :=
  ∀ (t : GTerm X u u' F0 F0' what₂ rows') (ρ : cs.Cl) (ρ' : cs'.Cl), cs.lamOf ρ = t.lam → cs'.lamOf ρ' = t.lam' →
    (if kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt ∈ X.K2 then
      chiL X (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt) else 0) =
    psiG TR (levi TR (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt))

theorem colPhase_of (hL : LeviCols TR F0 F0' cs cs') (hP : PhaseAt TR F0 F0' cs cs') :
    ColPhase F0 F0' TR cs cs' (scOf TR cs) (scOf TR cs') := by
  intro t ρ ρ' hρ hρ'
  rw [hP t ρ ρ' hρ hρ', hL t ρ ρ' hρ hρ']

end Phase

end Formalism.L2.SG.NormCut
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.Act

open Formalism.L2.SG.Pf Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.Saturated

section FrameFix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}

theorem frame_mapLF {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F : FlagG (VS D) D.R.rS T) (a : Fin (D.R.rS + 1)) : frame (mapLF γ (lf D F)) a = γ (F.fvec a) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp [frame, FlagG.fvec, Formalism.L2.SG.TermOp.mapFlag]
  · simp [frame, FlagG.fvec, Formalism.L2.SG.TermOp.mapFlag]

end FrameFix

end Formalism.L2.SG.Pf.Act
end
end
