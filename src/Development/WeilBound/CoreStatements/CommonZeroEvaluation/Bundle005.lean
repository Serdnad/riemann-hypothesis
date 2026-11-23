module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsVanBdOfMemExtVanZ
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle385
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle300
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.TestMem
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace ModelDimension


open GlobalTheory.FlatLine GlobalTheory.CompHS in
theorem evR_eq_of_sec₀_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) {e : Ix Dw → ℤ}
    (f g : secZ Xo c e) (h : sec₀ X Z e f = sec₀ X Z e g) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (hy : LiesOn Z y) : evR Xo c f.1 y = evR Xo c g.1 y := by
  by_cases ht : Tested y
  swap
  · unfold evR evalAt
    rw [dite_eq_right ht, dite_eq_right ht]
  have key : ∀ a : Rul Xo c, evR Xo c (idem Z * a) y = evR Xo c a y := fun a => by
    have e : evR Xo c (idem Z * a) y = evR Xo c (idem Z) y * evR Xo c a y :=
      evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (idem Z) a y
    rw [e, evR_idem hy ht, one_mul]
  have hm := idem_mul_mem Z (f - g).2
  have h0 : sec₀ X Z e ⟨_, hm.1⟩ = 0 := by
    rw [sec₀_mul X Z (zero_add e) ⟨idem Z, idem_mem_secZ Z⟩ (f - g) ⟨_, hm.1⟩ rfl, map_sub (sec₀ X Z e), h,
      sub_self, map_zero]
  have h1 : idem Z * (f.1 - g.1) = 0 := congrArg Subtype.val (eq_zero_of_sec₀ X Z (f := ⟨_, hm.1⟩) hm.2 h0)
  rw [mul_sub, sub_eq_zero] at h1
  rw [← key f.1, h1, key]

theorem cusp_form_extension_vanishing : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : GlobalTheory.CompHS.TorFlag Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), ∀ f ∈ GlobalTheory.CompanionTheory.Ar.OntoDef.extVanZ TF.X (exOf (T.Q.Dw j) u 0), ∃ g ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0), ∀ σ : Y.d.c₂.F →+* ℂ, GoodEmb Y.d.c₂ σ → ∀ w ∈ framesOn (Y.U σ) Z, rdU (Y.U σ) f w.1 w.2 = rdU (Y.U σ) g w.1 w.2 := by
  intro D T j Y e o hG hf Z TF u f hfv
  have hfs := GlobalTheory.CompanionTheory.Ar.OntoDef.extVanZ_le_secZ TF.X _ hfv
  obtain ⟨s, hs, hsf⟩ := GlobalTheory.CompanionTheory.Ar.OntoDef.exists_vanBd_of_mem_extVanZ (X := TF.X) (la := u) (f := ⟨f, hfs⟩) hfv Z
  obtain ⟨g, hg⟩ := GlobalTheory.HSApp.vanBd_le_space D T j Y e o hG hf Z TF u hs
  refine ⟨g.1, g.2, fun σ _ w hw => ?_⟩
  obtain ⟨k, y⟩ := w
  obtain ⟨hd, hl⟩ := hw
  have h := evR_eq_of_sec₀_eq TF.X Z ⟨f, hfs⟩ ⟨g.1, GlobalTheory.CompHS.cusp_le_secZ Z Y.U u g.2⟩ (hsf.symm.trans hg.symm) _ hl
  simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hd]
  exact congrArg _ h

end ModelDimension
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem ModelDimension.regular_chart_nonzero_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (h : GenFrEx Xo c) (C : GlobalTheory.Reg.FChart h), ∃ g₀ : C.R, g₀ ≠ 0 ∧ ∀ (A : Subring (Om C.Z)) (hA : ∀ r : C.R, (r : Om C.Z) ∈ A), (g₀ : Om C.Z)⁻¹ ∈ A → ∀ (L : Type) [Field L] (io : c.F →+* L) (ev : A →+* L), letI := io.toAlgebra; ∀ (ψ : C.R →ₐ[c.F] L), (∀ r : C.R, ψ r = ev ⟨r, hA r⟩) → ∀ (z y : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ C.y z → FrBor t z y → FinTr.RegAt h C.Z io A ev y := by
  intro E _ _ _ H Dw l Xo c hL h C
  classical
  obtain ⟨q, φ₀, y₀, hy₀⟩ := hL.test _ (genFr h C.Z)
  choose a ha b hb hb0 hab using C.frac
  let x : Fin q.n ⊕ Ix Dw → Om C.Z := fun k => match k with
    | .inl i => φ₀ (Ideal.Quotient.mk q.I (MvPolynomial.X i))
    | .inr k => (((C.t k)⁻¹ : (Om C.Z)ˣ) : Om C.Z)
  let bb : Fin q.n ⊕ Ix Dw → C.R := fun k => ⟨b (x k), hb (x k)⟩
  have hbb : ∀ k, bb k ≠ 0 := fun k h0 => hb0 (x k) (congrArg Subtype.val h0)
  refine ⟨∏ k, bb k, Finset.prod_ne_zero_iff.2 fun k _ => hbb k, fun A hA hg L _ io ev => ?_⟩
  letI := io.toAlgebra
  intro ψ hψ z y t hz hb'
  have hx : ∀ k, x k ∈ A := fun k => by
    have e1 : ((∏ k, bb k : C.R) : Om C.Z) = b (x k) * ((∏ j ∈ Finset.univ.erase k, bb j : C.R) : Om C.Z) := by
      rw [← Finset.mul_prod_erase _ bb (Finset.mem_univ k)]; rfl
    have hne : ((∏ k, bb k : C.R) : Om C.Z) ≠ 0 := fun h0 =>
      Finset.prod_ne_zero_iff.2 (fun k _ => hbb k) (Subtype.ext h0)
    have e2 : x k = a (x k) * ((∏ j ∈ Finset.univ.erase k, bb j : C.R) : Om C.Z) *
        ((∏ k, bb k : C.R) : Om C.Z)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hne, e1, ← mul_assoc, hab]
    rw [e2]
    exact A.mul_mem (A.mul_mem (hA ⟨_, ha _⟩) (hA _)) hg
  have hc : ∀ a : c.F, algebraMap c.F (Om C.Z) a ∈ A := fun a => hA (algebraMap c.F C.R a)
  have hev : ∀ (a : c.F) (h : algebraMap c.F (Om C.Z) a ∈ A), ev ⟨_, h⟩ = io a := fun a h => by
    have := hψ (algebraMap c.F C.R a)
    rw [ψ.commutes] at this
    exact this.symm
  have hφ : ∀ r, φ₀ r ∈ A := ModelDimension.Spread.test_mem q φ₀ A hc (fun i => hx (.inl i))
  let ψq := ModelDimension.Spread.evAlg φ₀ A hφ ev hev
  obtain ⟨zq, hzq⟩ := hL.bc _ _ ψq y₀
  obtain ⟨t', ht'⟩ := ModelDimension.Spread.spec_bor φ₀ C.R.val hy₀ C.gen C.bor A hφ hA (fun k => hx (.inr k)) ev ψq ψ
    (fun _ => rfl) hψ hzq hz
  exact ⟨fun a => ⟨hc a, hev a _⟩, q, φ₀, ψq, y₀, zq, _, hy₀, hzq, fun r => ⟨hφ r, rfl⟩,
    (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L).2.1 _ _ _ _ _ ht' hb'⟩
end
