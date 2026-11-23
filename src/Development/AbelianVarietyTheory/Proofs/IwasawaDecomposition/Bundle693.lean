module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle387
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle388
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle681
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle627
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenFrameBasePointLiftsUniqueFlagSpace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle667
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.UnfInv

theorem one_mem_bor {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) (r : ℕ) :
    (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) ∈ ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r := by
  intro τ
  refine ⟨?_, fun a b hab => ?_⟩
  · change ¬ (1 : Matrix (Fin r) (Fin r) ℂ).det = 0
    simp
  · simp [Matrix.one_apply, (ne_of_lt hab).symm]

theorem rmul_one {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) (r : ℕ) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    ReciprocityTheory.ChartRestriction.G.FD.rmul x (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) = x := by
  funext τ
  show ReciprocityTheory.ChartRestriction.G.FD.mat x τ * ReciprocityTheory.ChartRestriction.G.FD.mat (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) τ = x τ
  rw [show ReciprocityTheory.ChartRestriction.G.FD.mat (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) τ = 1 from rfl,
    Matrix.mul_one]
  rfl

theorem psi_moebI_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ γ ∈ gammaU (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ), ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ψ (flat (moebI γ (unflat v))) = ψ v := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ γ hγ v hv
  obtain ⟨-, hk, -, h4, -⟩ := hU
  have hp0 : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hk k).1]; omega
  haveI : IsOpenImmersion j := hL.1
  have hinj : Function.Injective (GlobalTheory.LieBase.cxOf (Z := T.Z) e σ hj) := by
    intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    exact (cancel_mono j).1 this
  obtain ⟨γ₀, hγ₀, rfl⟩ := Subgroup.mem_map.1 hγ
  obtain ⟨x, hx, hxv⟩ := FrameOnto.frame_onto E (Dw.p + Dw.q) Dw.p (U.X k) (Nat.le_add_right Dw.p Dw.q)
    (U.X k).Ψ (Equiv.refl _) hp0 (unflat v) hv
  have hx' : ReciprocityTheory.ChartRestriction.G.FD.lact γ₀ x ∈ (U.X k).dom := GlobalTheory.Reg.GenericFrameDensity.lact_mem_dom _ hγ₀ hx
  have hdom : domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) (ReciprocityTheory.ChartRestriction.G.FD.lact γ₀ x) =
      moebI (toUpq (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) γ₀) (unflat v) := by
    rw [domPt_lact (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) hp0 γ₀ hx]
    exact congrArg _ hxv
  have h1 := hψ ⟨x, hx⟩
  have h2 := hψ ⟨_, hx'⟩
  simp only at h1 h2
  rw [hxv] at h1
  rw [hdom] at h2
  apply hinj
  have h1' : GlobalTheory.LieBase.cxOf (Z := T.Z) e σ hj (ψ v) = cxPt T.Z (U.un k ⟨x, hx⟩) := h1
  rw [h2, h1']
  apply GlobalTheory.ShFam.cxPt_congr
  have hx'' : (⟨k, (⟨ReciprocityTheory.ChartRestriction.G.FD.lact γ₀ x, hx'⟩ : (U.X k).dom).1⟩ : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ (Dw.p + Dw.q)) =
      ⟨k, ReciprocityTheory.ChartRestriction.G.FD.rmul (ReciprocityTheory.ChartRestriction.G.FD.lact γ₀ (⟨x, hx⟩ : (U.X k).dom).1)
        (fun _ => (1 : Matrix (Fin (Dw.p + Dw.q)) (Fin (Dw.p + Dw.q)) ℂ))⟩ := by
    rw [rmul_one]
  obtain ⟨t, ht⟩ := (h4 k k ⟨x, hx⟩ ⟨_, hx'⟩).2 ⟨γ₀, hγ₀, _, one_mem_bor _ _, hx''⟩
  exact ht.1

end GlobalTheory.UnfInv
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.UnifFibre

theorem fibre_gamma : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ∀ w ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ψ v = ψ w → ∃ γ ∈ gammaU (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ), moebI γ (unflat v) = unflat w := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ v hv w hw hvw
  have hjr : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right Dw.p Dw.q
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by
    have := (hU.2.1 k).1
    omega
  have hflat : ∀ u : (U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ, flat (unflat u) = u := by
    intro u; funext ⟨i, a, b⟩; rfl
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.TrueCx.FrameOnto.frame_onto E (Dw.p + Dw.q) Dw.p (U.X k) hjr (U.X k).Ψ
    (Equiv.refl _) hp (unflat v) hv
  obtain ⟨x', hx', hxw⟩ := GlobalTheory.TrueCx.FrameOnto.frame_onto E (Dw.p + Dw.q) Dw.p (U.X k) hjr (U.X k).Ψ
    (Equiv.refl _) hp (unflat w) hw
  have h1 := hψ ⟨x, hx⟩
  have h2 := hψ ⟨x', hx'⟩
  simp only at h1 h2
  rw [hxv, hflat] at h1
  rw [hxw, hflat] at h2
  have h3 : cxPt T.Z (U.un k ⟨x, hx⟩) = cxPt T.Z (U.un k ⟨x', hx'⟩) := by
    rw [← h1, ← h2, hvw]
  have h4 : (U.un k ⟨x, hx⟩).x = (U.un k ⟨x', hx'⟩).x := by
    have h5 := congrArg Subtype.val h3
    simp only [cxPt] at h5
    haveI := T.Z.jQ_open
    have h6 := (cancel_mono T.Z.jQ).1 h5
    have h7 := congrArg (· ≫ CategoryTheory.Limits.pullback.fst _ _) h6
    simp only [GlobalTheory.AllWt.ptF] at h7
    rwa [CategoryTheory.Limits.pullback.lift_fst, CategoryTheory.Limits.pullback.lift_fst] at h7
  obtain ⟨b, hb, hb0, hm, t, ht⟩ := GlobalTheory.PointOfFrames.exists_frBor U hU hG k ⟨x, hx⟩ _ h4
  obtain ⟨γ, hγ, b', hb', heq⟩ := (hU.2.2.2.1 k k ⟨_, hm⟩ ⟨x', hx'⟩).1 ⟨t, ht⟩
  have hx'eq : x' = ReciprocityTheory.ChartRestriction.G.FD.rmul (ReciprocityTheory.ChartRestriction.G.FD.lact γ (ReciprocityTheory.ChartRestriction.G.FD.rmul x b)) b' :=
    eq_of_heq (Sigma.mk.inj_iff.1 heq).2
  refine ⟨GlobalTheory.TrueCx.toUpq (U.X k) hjr (Equiv.refl (U.X k).Ψ) γ, Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩, ?_⟩
  rw [← hxv, ← hxw, hx'eq, GlobalTheory.TrueCx.domPt_rmul _ _ _ hb', GlobalTheory.TrueCx.domPt_lact _ _ _ hp γ hm]
  rw [hp] at hb0
  rw [GlobalTheory.PointOfFrames.domPt_rmul_block _ _ _ _ b hb hb0]

end GlobalTheory.UnifFibre
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.LieBase.UnifExists

open Formalism.MJ ReciprocityTheory.ChartRestriction.G.AR.Up

theorem flat_inj {ι : Type} {p q : ℕ} {z z' : ι → Matrix (Fin p) (Fin q) ℂ} (h : flat z = flat z') : z = z' := by
  funext t a b
  exact congrFun h (t, a, b)

theorem exists_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∃ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL
  obtain ⟨hoi, hfj, -⟩ := hL
  haveI := hoi
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := first_index_eq_of_unfolded U hU rfl k
  have hle : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right Dw.p Dw.q
  have hrange : ∀ x : (U.X k).dom, Set.range (cxPt T.Z (U.un k x)).1 ⊆ Set.range j := by
    rintro x _ ⟨s, rfl⟩
    obtain ⟨y, hy⟩ := Φ.label k x s
    refine ⟨f y, ?_⟩
    show (f ≫ j) y = _
    rw [hfj]
    exact hy
  let lf : (U.X k).dom → CxPts X.str (σ.comp e.toRingHom) := fun x =>
    ⟨IsOpenImmersion.lift j (cxPt T.Z (U.un k x)).1 (hrange x), by
      rw [← hj, ← Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc, (cxPt T.Z (U.un k x)).2,
        ← Spec.map_comp]
      rfl⟩
  have hlf : ∀ x, cxOf e σ hj (lf x) = cxPt T.Z (U.un k x) := fun x =>
    Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
  have hwell : ∀ x x' : (U.X k).dom,
      domPt (U.X k) hle (Equiv.refl (U.X k).Ψ) x.1 = domPt (U.X k) hle (Equiv.refl (U.X k).Ψ) x'.1 →
      cxPt T.Z (U.un k x) = cxPt T.Z (U.un k x') := by
    intro x x' h
    have h5 : ∀ τ, moeb (frameCo (U.X k) hle x.1 τ) 0 = moeb (frameCo (U.X k) hle x'.1 τ) 0 :=
      fun τ => congrFun h τ
    exact cxPt_congr (PointWell.pt_eq_of_block hU hσ k x x'
      (fun τ => PointWell.block_of_moeb_eq _ hle hp x.2 x'.2 τ (h5 τ))
      (fun τ => PointWell.block_of_moeb_eq _ hle hp x'.2 x.2 τ (h5 τ).symm))
  let x0 : (U.X k).dom := ⟨x0F (U.X k), IW.orth_mem_dom (U.X k) _ (isOrth_x0F (U.X k))⟩
  refine ⟨fun v => if h : ∃ x : (U.X k).dom,
      flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1) = v then lf h.choose else lf x0,
    fun x => ?_⟩
  have h : ∃ x' : (U.X k).dom, flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x'.1) =
      flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1) := ⟨x, rfl⟩
  simp only [dif_pos h]
  rw [hlf]
  exact hwell _ _ (flat_inj h.choose_spec)

end GlobalTheory.LieBase.UnifExists
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PrimRay

theorem eq_of_toReal_eq_smul : ∀ {X : Type} [AddCommGroup X] (x y : LinearMap.BilinForm ℤ X) (d : ℝ), 0 < d →
  (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = x → k = 1) → (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = y → k = 1) →
  toReal x = d • toReal y → x = y ∧ d = 1 := by
  intro X _ x y d hd hx hy h
  have hx0 : x ≠ 0 := fun h0 => by
    have := hx 0 0 (by simp [h0])
    simp at this
  have hy0 : y ≠ 0 := fun h0 => by
    have := hy 0 0 (by simp [h0])
    simp at this
  obtain ⟨a, b, ha, hb, hab⟩ := GlobalTheory.T.exists_pos_rat_multiple_of_pos_real_multiple_intForm x y d hd hy0 h
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hcop0 := Nat.coprime_div_gcd_div_gcd (m := a) (n := b) hg
  obtain ⟨a', ha'⟩ := Nat.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ := Nat.gcd_dvd_right a b
  generalize Nat.gcd a b = g at hg hcop0 ha' hb'
  subst ha' hb'
  have hcop : Nat.Coprime a' b' := by
    have := hcop0
    have e1 : g * a' / g = a' := Nat.mul_div_cancel_left a' hg
    have e2 : g * b' / g = b' := Nat.mul_div_cancel_left b' hg
    rwa [e1, e2] at this
  obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hgz : ((g : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have h1 : ∀ p q, (a' : ℤ) * x p q = (b' : ℤ) * y p q := fun p q => by
    have := LinearMap.congr_fun₂ hab p q
    simp only [LinearMap.smul_apply, smul_eq_mul] at this
    push_cast at this
    apply mul_left_cancel₀ hgz
    linear_combination this
  set z : LinearMap.BilinForm ℤ X := u • y + w • x with hz
  have hxz : ((b' : ℕ) : ℤ) • z = x := by
    ext p q
    simp only [hz, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
    linear_combination (-u) * h1 p q + (x p q) * huw
  have hyz : ((a' : ℕ) : ℤ) • z = y := by
    ext p q
    simp only [hz, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
    linear_combination w * h1 p q + (y p q) * huw
  have hb1 : b' = 1 := hx b' z hxz
  have ha1 : a' = 1 := hy a' z hyz
  have hxy : x = y := by
    ext p q
    simpa [ha1, hb1] using h1 p q
  refine ⟨hxy, ?_⟩
  subst hxy
  obtain ⟨p, q, hpq⟩ : ∃ p q, x p q ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx0 (LinearMap.ext₂ hc)
  have := LinearMap.congr_fun₂ h p q
  simp only [toReal_apply, LinearMap.smul_apply, smul_eq_mul] at this
  have hne : (x p q : ℝ) ≠ 0 := by exact_mod_cast hpq
  have := mul_right_cancel₀ hne (this.symm.trans (one_mul _).symm)
  exact this

end GlobalTheory.PrimRay
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.intBilinFormToReal_mem_balancedPsdCone : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (β : LinearMap.BilinForm ℤ X), β ∈ balForms H.bar X → (∀ y, 0 ≤ β y y) → toReal β ∈ psdCone (bar := H.bar) (X := X) := by
  first | exact @GlobalTheory.PolFan.toReal_mem_psdCone_of_nonneg | exact GlobalTheory.PolFan.toReal_mem_psdCone_of_nonneg | (intros; apply GlobalTheory.PolFan.toReal_mem_psdCone_of_nonneg <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.balancedPsdRationalRadicalCone_subset_intCone : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] [Module.Free ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X], psdCone (bar := bar) (X := X) ⊆ psdCone (bar := (id : ℤ → ℤ)) (X := X) := by
  first | exact @GlobalTheory.PolFan.psdCone_subset_psdCone_int | exact GlobalTheory.PolFan.psdCone_subset_psdCone_int | (intros; apply GlobalTheory.PolFan.psdCone_subset_psdCone_int <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.realConeCoords_integral_of_partOfIntBasis : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (hu : ∀ i, u i ∈ balForms (id : ℤ → ℤ) X), IsPartOfBasis (fun i => (⟨u i, hu i⟩ : balForms (id : ℤ → ℤ) X)) → ∀ (β : LinearMap.BilinForm ℤ X) (t : Fin m → ℝ), toReal β = ∑ i, t i • toReal (u i) → ∀ i, ∃ z : ℤ, t i = z := by
  first | exact @GlobalTheory.cone_coords_int_of_isPartOfBasis | exact GlobalTheory.cone_coords_int_of_isPartOfBasis | (intros; apply GlobalTheory.cone_coords_int_of_isPartOfBasis <;> assumption)
end

section

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan.ConeSpan

theorem exists_margin {ι : Type} [Fintype ι] (M : ι → ι → ℝ)
    (hM : ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * M i j) :
    ∃ η : ℝ, 0 < η ∧ ∀ E : ι → ι → ℝ, (∀ i j, |E i j| ≤ η) → ∀ c : ι → ℝ, c ≠ 0 →
      0 < ∑ i, ∑ j, c i * c j * (M i j + E i j) := GlobalTheory.T.exists_margin_quadForm_pos_of_perturbation M hM

theorem exists_rat_span {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (B : L →ₗ[ℤ] L →ₗ[ℤ] ℝ) : ∃ (n : ℕ) (w : Fin n → ℝ) (Q : Fin n → LinearMap.BilinForm ℤ L),
      B = ∑ j, w j • toReal (Q j) ∧ ∀ j, ∃ g : ℝ →+ ℝ, ∀ y z, (Q j y z : ℝ) = g (B y z) := GlobalTheory.T.exists_realBilinForm_eq_sum_additive_image_intForms B

theorem free_finite_int (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O] (X₁ : Type)
    [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] [Module.Projective O X₁] :
    Module.Free ℤ X₁ ∧ Module.Finite ℤ X₁ := by
  have : Module.Finite ℤ X₁ := Module.Finite.trans O X₁
  refine ⟨?_, this⟩
  have : Module.IsTorsionFree O X₁ := Module.Flat.isTorsionFree
  have : Module.IsTorsionFree ℤ X₁ :=
    Module.IsTorsionFree.comap (S := O) (Int.castRingHom O)
      (fun r hr => IsRegular.of_ne_zero (by
        intro h0
        have : r = 0 := by simpa using h0
        subst this
        exact (not_isRegular_zero (R := ℤ)) hr))
      (fun r m => Int.cast_smul_eq_zsmul O r m)
  exact Module.free_of_finite_type_torsion_free'

theorem nonneg_of_near {ι L : Type} [Fintype ι] [AddCommGroup L] (b : Module.Basis ι ℤ L)
    {B₁ : L →ₗ[ℤ] L →ₗ[ℤ] ℝ} (h : IsPosDef B₁) : ∃ η : ℝ, 0 < η ∧ ∀ (P : LinearMap.BilinForm ℤ L) (D : ℝ), 0 < D →
      (∀ i j, |(P (b i) (b j) : ℝ) / D - B₁ (b i) (b j)| ≤ η) → ∀ x, 0 ≤ P x x := by
  obtain ⟨η, hη, hE⟩ := exists_margin (fun i j => B₁ (b i) (b j)) ((isPosDef_iff_basis b B₁).1 h)
  refine ⟨η, hη, fun P D hD hP x => ?_⟩
  have hP' : IsPosDef (toReal P) := (isPosDef_iff_basis b _).2 fun c hc => by
    have h1 := hE (fun i j => (P (b i) (b j) : ℝ) / D - B₁ (b i) (b j)) hP c hc
    simp only [add_sub_cancel] at h1
    simp only [toReal_apply]
    have e : ∑ i, ∑ j, c i * c j * ((P (b i) (b j) : ℝ) / D) = (∑ i, ∑ j, c i * c j * (P (b i) (b j) : ℝ)) / D := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e] at h1
    exact (div_pos_iff_of_pos_right hD).1 h1
  have := hP'.nonneg x
  simpa using this

theorem exists_nonneg_comb_of_mem_psdCone (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ)
    (hB : B ∈ psdCone (bar := bar) (X := X)) : ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ),
      (∀ i, γ i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ γ i y y) ∧ (∀ i, 0 ≤ c i) ∧ B = ∑ i, c i • toReal (γ i) := by
  obtain ⟨X₁, _, _, _, r, B₁, hr, hB₁, hpos, hBr⟩ := hB
  have : Module.Finite O X₁ := Module.Finite.of_surjective r hr
  obtain ⟨_, _⟩ := free_finite_int O X₁
  let b := Module.Free.chooseBasis ℤ X₁
  obtain ⟨η, hη, hnear⟩ := nonneg_of_near b hpos
  obtain ⟨n, w, Q, hw, hg⟩ := exists_rat_span B₁
  have hwv : ∀ y z, B₁ y z = ∑ k, w k * (Q k y z : ℝ) := fun y z => by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hw y z
  have hQ : ∀ k, Q k ∈ balForms bar X₁ := fun k => by
    obtain ⟨g, hg⟩ := hg k
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · exact_mod_cast (hg y z).trans ((congrArg g (hB₁.1 y z)).trans (hg z y).symm)
    · exact_mod_cast (hg _ _).trans ((congrArg g (hB₁.2 a y z)).trans (hg _ _).symm)
  set K : ℝ := ∑ k, ∑ i, ∑ j, |(Q k (b i) (b j) : ℝ)| with hK
  have hKsum : ∀ i j, ∑ k, |(Q k (b i) (b j) : ℝ)| ≤ K := fun i j => Finset.sum_le_sum fun k _ =>
    (Finset.single_le_sum (f := fun j => |(Q k (b i) (b j) : ℝ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, |(Q k (b i) (b j) : ℝ)|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  have hKle : ∀ k i j, |(Q k (b i) (b j) : ℝ)| ≤ K := fun k i j =>
    (Finset.single_le_sum (f := fun k => |(Q k (b i) (b j) : ℝ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ k)).trans (hKsum i j)
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨D, hD⟩ := exists_nat_gt (2 * (n + 1) * K / η)
  have hDpos : (0 : ℝ) < D := lt_of_le_of_lt (by positivity) hD
  have hDK : 2 * (n + 1) * K ≤ D * η := by rw [div_lt_iff₀ hη] at hD; linarith
  set a : Fin n → ℤ := fun k => ⌊(D : ℝ) * w k⌋ with ha
  set δ : Fin n → ℝ := fun k => D * w k - a k with hδ
  have hδ0 : ∀ k, 0 ≤ δ k := fun k => sub_nonneg.2 (Int.floor_le _)
  have hδ1 : ∀ k, δ k ≤ 1 := fun k => by
    have := Int.lt_floor_add_one ((D : ℝ) * w k)
    simp only [hδ, ha]; linarith
  set R : LinearMap.BilinForm ℤ X₁ := ∑ k, a k • Q k with hR
  have hRv : ∀ y z, (R y z : ℝ) = D * B₁ y z - ∑ k, δ k * (Q k y z : ℝ) := fun y z => by
    simp only [hR, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul, hwv,
      Finset.mul_sum, ← Finset.sum_sub_distrib, hδ]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hSb : ∀ i j, |∑ k, δ k * (Q k (b i) (b j) : ℝ)| ≤ K := fun i j =>
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun k _ => by
      rw [abs_mul, abs_of_nonneg (hδ0 k)]
      exact mul_le_of_le_one_left (abs_nonneg _) (hδ1 k)).trans (hKsum i j))
  have hRnn : ∀ x, 0 ≤ R x x := hnear R D hDpos fun i j => by
    rw [hRv, show (D * B₁ (b i) (b j) - ∑ k, δ k * (Q k (b i) (b j) : ℝ)) / D - B₁ (b i) (b j) =
      -(∑ k, δ k * (Q k (b i) (b j) : ℝ)) / D by field_simp; ring, abs_div, abs_neg, abs_of_pos hDpos,
      div_le_iff₀ hDpos]
    nlinarith [hSb i j]
  let N : ℤ := n + 1
  have hQnn : ∀ k x, 0 ≤ (R + N • Q k) x x := fun k => hnear _ D hDpos fun i j => by
    have e : ((R + N • Q k) (b i) (b j) : ℝ) / D - B₁ (b i) (b j) =
        (N * (Q k (b i) (b j) : ℝ) - ∑ l, δ l * (Q l (b i) (b j) : ℝ)) / D := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul, hRv]
      field_simp; ring
    rw [e, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
    have h1 := abs_sub (N * (Q k (b i) (b j) : ℝ)) (∑ l, δ l * (Q l (b i) (b j) : ℝ))
    rw [abs_mul] at h1
    have h2 : |(N : ℝ)| = n + 1 := by simp [N]; positivity
    rw [h2] at h1
    nlinarith [hSb i j, hKle k i j]
  let γ₁ : Fin (n + 1) → LinearMap.BilinForm ℤ X₁ := Fin.cons R fun k => R + N • Q k
  let c : Fin (n + 1) → ℝ := Fin.cons ((1 + ∑ k, (1 - δ k)) / (N * D)) fun k => δ k / (N * D)
  have hN : (0 : ℝ) < N := by simp [N]; positivity
  refine ⟨n + 1, fun i => pull r (γ₁ i), c, fun i => pull_mem r ?_, fun i y => ?_, fun i => ?_, ?_⟩
  · refine Fin.cases ?_ (fun k => ?_) i
    · exact (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hQ k) : R ∈ _)
    · show R + N • Q k ∈ _
      exact Submodule.add_mem _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hQ k))
        (Submodule.smul_mem _ _ (hQ k))
  · simp only [pull_apply]
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hRnn _
    · exact hQnn k _
  · refine Fin.cases ?_ (fun k => ?_) i
    · refine div_nonneg (add_nonneg zero_le_one (Finset.sum_nonneg fun k _ => sub_nonneg.2 (hδ1 k))) (by positivity)
    · exact div_nonneg (hδ0 k) (by positivity)
  · refine LinearMap.ext₂ fun y z => ?_
    simp only [hBr, LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, pull_apply, smul_eq_mul,
      Fin.sum_univ_succ, γ₁, c, Fin.cons_zero, Fin.cons_succ, LinearMap.add_apply, Int.cast_add, Int.cast_mul]
    rw [hRv]
    set u := B₁ (r y) (r z)
    set S := ∑ k, δ k * (Q k (r y) (r z) : ℝ)
    have e1 : ∑ k, δ k / (N * D) * (D * u - S + N * (Q k (r y) (r z) : ℝ)) =
        (∑ k, δ k) * (D * u - S) / (N * D) + S / D := by
      rw [Finset.sum_mul, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp
    have e2 : ∑ k, (1 - δ k) = n - ∑ k, δ k := by
      rw [Finset.sum_sub_distrib]; simp
    rw [e1, e2]
    have hN' : (N : ℝ) = n + 1 := by simp [N]
    rw [hN']
    field_simp
    ring

end GlobalTheory.PolFan.ConeSpan
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

theorem _root_.GlobalTheory.T.eigenFrameBasePoint_lifts_unique_flagSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z) (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn) (S' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn) (φ : B.Fn →ₐ[F] C.Y.Fn) (f : C.Y.X ⟶ B.X), j ≫ genStr Z ≫ spMap e.toRingHom = B.str → C.π = f ≫ j → Tied e B j f₀ S A₀ → Tied e C.Y C.π C.f0 S' A₁ → f₀.Coord (φ : B.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) → Refines S S' φ f → ∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z) (x' : Sp K ⟶ B.X), x' ≫ j = x → x ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g := by
  first | exact @GlobalTheory.ShFam.flagex_lifts | exact GlobalTheory.ShFam.flagex_lifts | (intros; apply GlobalTheory.ShFam.flagex_lifts <;> assumption)
end
