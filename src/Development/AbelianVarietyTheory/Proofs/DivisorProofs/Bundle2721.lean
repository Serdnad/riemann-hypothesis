module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2635
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2487
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle167
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle032
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartDer

namespace GlobalTheory.BoundaryPoint

theorem isClosed_of_isMaximal {X : Scheme.{0}} [JacobsonSpace X] {U : X.Opens} (hU : IsAffineOpen U)
    {m : Ideal Γ(X, U)} (hm : m.IsMaximal) {x : X} (hx : x ∈ U) (h : ∀ f ∈ m, x ∉ X.basicOpen f) :
    IsClosed ({x} : Set X) := by
  have e := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have hle : m ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := fun f hf => by
    by_contra hc
    refine h f hf ?_
    have h₁ : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact hc
    have h₂ : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f := h₁
    rwa [e] at h₂
  have hmax : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.IsMaximal :=
    hm.eq_of_le (hU.primeIdealOf ⟨x, hx⟩).isPrime.ne_top hle ▸ hm
  have hc := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hmax
  have h₃ : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹' closedPoints X := by
    rw [hU.fromSpec.isOpenEmbedding.preimage_closedPoints]
    exact hc
  have h₄ : IsClosed ({hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩)} : Set X) := h₃
  rwa [e] at h₄

theorem exists_closed_boundary_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim (genStr Y) → ∀ (U : Y.X.affineOpens) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → ∀ x : Y.X, x ∉ interior Y → x ∈ U.1 → (∀ f ∈ m, x ∉ Y.X.basicOpen f) → ∃ x' : gen Y, genι Y x' = x ∧ x' ∈ genBd Y ∧ IsClosed ({x'} : Set (gen Y)) := by
  intro E _ _ _ H Dw l Xo c Y hs U m hm x hx hU h
  have hi : IsIso (genι Y) := GlobalTheory.LogKS.isIso_fst Y
  have : Smooth (genStr Y) := SmoothOfRelativeDimension.smooth Dw.dim _
  have : JacobsonSpace Y.X := LocallyOfFiniteType.jacobsonSpace (inv (genι Y) ≫ genStr Y)
  have hc := isClosed_of_isMaximal U.2 hm hU h
  obtain ⟨x', rfl⟩ := (genι Y).homeomorph.surjective x
  refine ⟨x', rfl, mem_genBd_iff.2 fun h' => hx ?_, ?_⟩
  · rw [← coe_interior] at h'
    exact h'
  · rw [← (genι Y).homeomorph.isClosed_image, Set.image_singleton]
    exact hc

end GlobalTheory.BoundaryPoint
end

section



noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

namespace GlobalTheory.FlatTwisting

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem wtOf_parWt_anti (w : Psi H → ℤ) (τ : E →+* ℂ) (i j : ℕ) (hij : i ≤ j) (hj : j < Dw.mult τ) :
    (wtOf Dw (parWt Dw w) 0).1 (τ, j) ≤ (wtOf Dw (parWt Dw w) 0).1 (τ, i) := by
  by_cases h : τ (H.rt : E) = H.rt0
  · have hp : j < Dw.p := by simpa [Datum.mult, h] using hj
    have e1 := wtOf_big (parWt Dw w) 0 ⟨τ, h⟩ j hp
    have e2 := wtOf_big (parWt Dw w) 0 ⟨τ, h⟩ i (by omega)
    exact (e1.trans e2.symm).le
  · have hq : j < Dw.q := by simpa [Datum.mult, h] using hj
    have e1 := wtOf_small (parWt Dw w) 0 ⟨conjEmb τ, conj_mem h⟩ j hq
    have e2 := wtOf_small (parWt Dw w) 0 ⟨conjEmb τ, conj_mem h⟩ i (by omega)
    simp only [_root_.GlobalTheory.AllWt.conjEmb_conjEmb] at e1 e2
    exact (e1.trans e2.symm).le

theorem wtOf_parWt_neg (w : Psi H → ℤ) : wtOf Dw (parWt Dw (-w)) 0 = -wtOf Dw (parWt Dw w) 0 := by
  have h := wtOf_add' (Dw := Dw) (parWt Dw (-w)) (parWt Dw w)
  have h0 : parWt Dw (-w) + parWt Dw w = 0 := by funext τ i; simp [parWt]
  rw [h0, wtOf_zero] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem mul_sig_mem_cuspOn (hK : Nonempty (KeySec Xo c)) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hpq : 1 ≤ Dw.p + Dw.q) {Z : Comp Xo c} {w : Psi H → ℤ} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ}
    (s : ConstSec U x Z (parWt Dw w) δ) :
    ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z G, f * s.sig ∈ cuspOn U Z (G + wtOf Dw (parWt Dw w) 0) :=
  GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd E H Dw l Xo c r U x Z _ s.sig hK hU hpq (even_wtOf _ _) (wtOf_parWt_anti w) s.sig_mem
    s.sig_mem_suppOn fun σ hσ => ⟨s.cInf σ, by
      have e : goodOf c σ = σ := if_pos hσ
      have h : ∀ z ∈ framesOn (U (goodOf c σ)) Z,
          homN (U (goodOf c σ)) x (wtOf Dw (parWt Dw w) 0) s.sig z ≤ s.cInf σ := fun z hz => (s.homN_eq hz).le
      rw [e] at h
      exact h⟩

theorem exists_twSec_of_const {B : Finset ℕ} (hK : Nonempty (KeySec Xo c)) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hpq : 1 ≤ Dw.p + Dw.q) (hB : UnramPts Xo c B) (Z : Comp Xo c) (w : Psi H → ℤ)
    (δ : HeightOneSpectrum (𝓞 c.F) → ℝ) (s : ConstSec U x Z (parWt Dw w) δ) (hδ : (Function.support δ).Finite) :
    ∃ t : TwSec U x Z (wtOf Dw (parWt Dw w) 0),
      t.sig = s.sig ∧ t.cInf = s.cInf ∧ t.lo = δ + s.rho_vw ∧ t.hi = t.lo ∧ IntOff B t.lo := by
  refine ⟨TwSec.ofConst s hδ (mul_sig_mem_cuspOn hK hU hpq s) fun G hG f hf => ?_, rfl, rfl, rfl, rfl,
    intOff_of_unramPts E H Dw l Xo c r U x B hB Z _ δ s⟩
  have h := mul_sig_mem_cuspOn hK hU hpq (w := -w) (s.symm.copy rfl rfl) (G + wtOf Dw (parWt Dw w) 0)
    (Even.add hG (even_wtOf _ _)) f hf
  rw [wtOf_parWt_neg, add_neg_cancel_right] at h
  exact h

theorem finite_sum_flDefect (w : Psi H → ℤ) :
    (Function.support (∑ τ, (-w τ) • flDefect_vw Dw c τ)).Finite := by
  refine (Set.finite_iUnion fun τ => finite_flDefect_vw (Dw := Dw) (c := c) τ).subset fun la hla => ?_
  by_contra hn
  simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn
  exact hla (by simp [Finset.sum_apply, hn])

theorem finsum_sum_flDefect (w : Psi H → ℤ) :
    ∑ᶠ la, (∑ τ, (-w τ) • flDefect_vw Dw c τ) la * lw c.F la =
      -((Dw.q : ℝ) * (lrd E - Real.log H.d) * ∑ τ, (w τ : ℝ)) := by
  have h1 : ∀ la, (∑ τ, (-w τ) • flDefect_vw Dw c τ) la * lw c.F la =
      ∑ τ, (-(w τ : ℝ)) * (flDefect_vw Dw c τ la * lw c.F la) := fun la => by
    rw [Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Pi.smul_apply, zsmul_eq_mul]; push_cast; ring
  rw [finsum_congr h1, finsum_sum_comm _ _ fun τ _ =>
    (fin_mul (finite_flDefect_vw τ) (lw c.F)).subset (Function.support_mul_subset_right _ _),
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← mul_finsum, sum_flDefect_vw]; ring

theorem twSec_of_flat (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (x : ℝ) (B : Finset ℕ) (hK : Nonempty (KeySec Xo c)) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hpq : 1 ≤ Dw.p + Dw.q) (hB : UnramPts Xo c B) :
    (∀ (Z : Comp Xo c) (w : Psi H → ℤ) (δ : HeightOneSpectrum (𝓞 c.F) → ℝ) (s : ConstSec U x Z (parWt Dw w) δ),
      (Function.support δ).Finite → ∃ t : TwSec U x Z (wtOf Dw (parWt Dw w) 0),
        t.sig = s.sig ∧ t.cInf = s.cInf ∧ t.lo = δ + s.rho_vw ∧ t.hi = t.lo ∧ IntOff B t.lo) ∧
    (FlatExists U x → ∀ (Z : Comp Xo c) (w : Psi H → ℤ), HasPts U Z →
      ∃ t : TwSec U x Z (wtOf Dw (parWt Dw w) 0), IntOff B t.lo ∧
        t.degLo = (∑ τ, (w τ : ℝ) * c1 U x τ) - (Dw.q : ℝ) * (lrd E - Real.log H.d) * (∑ τ, (w τ : ℝ)) ∧
        (∑ τ, (w τ : ℝ) * c1 U x τ) - (Dw.q : ℝ) * lrd E * (∑ τ, |(w τ : ℝ)|) ≤ t.degLo) := by
  refine ⟨exists_twSec_of_const hK hU hpq hB, fun hF Z w hp => ?_⟩
  have sF : ∀ τ, FlatSec U x Z τ := fun τ => (hF.nonempty Z τ).some
  have hδ := finite_sum_flDefect (Dw := Dw) (c := c) w
  obtain ⟨s, hdeg⟩ : ∃ s : ConstSec U x Z (parWt Dw w) (∑ τ, (-w τ) • flDefect_vw Dw c τ),
      s.deg = ∑ τ, (w τ : ℝ) * c1 U x τ :=
    ⟨(FlatSec.shift hp sF w).copy rfl (by congr; exact Subsingleton.elim _ _), (hF.deg_shift hp sF w).trans (by congr; exact Subsingleton.elim _ _)⟩
  obtain ⟨t, -, h2, h3, -, h5⟩ := exists_twSec_of_const hK hU hpq hB Z w _ s hδ
  have key := lineDeg_mul (r := 1) (fun _ => one_pos) s.cInf_pos hδ s.finite_rho
  rw [one_mul] at key
  have hd : t.degLo =
      (∑ τ, (w τ : ℝ) * c1 U x τ) - (Dw.q : ℝ) * (lrd E - Real.log H.d) * (∑ τ, (w τ : ℝ)) := by
    have h1 : lineDeg (1 : (c.F →+* ℂ) → ℝ) (∑ τ, (-w τ) • flDefect_vw Dw c τ) =
        -((Dw.q : ℝ) * (lrd E - Real.log H.d) * ∑ τ, (w τ : ℝ)) := by
      rw [lineDeg, finsum_sum_flDefect]; simp
    rw [TwSec.degLo, h2, h3, key, h1, ← hdeg, ConstSec.deg]; ring
  refine ⟨t, h5, hd, ?_⟩
  have hA := GlobalTheory.T.abs_logRootDisc_sub_log_hostPrime_le E H
  have hs : (lrd E - Real.log H.d) * ∑ τ, (w τ : ℝ) ≤ lrd E * ∑ τ, |(w τ : ℝ)| := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun τ _ => (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hA (abs_nonneg _)
  have := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) Dw.q)
  rw [hd, mul_assoc, mul_assoc]
  linarith

end GlobalTheory.FlatTwisting
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JetsCharZero

theorem num_le (dF R N r g0 g1 cst : ℝ) (hR : 0 ≤ R) (hN : 0 ≤ N) (hr : 0 ≤ r) (hg0 : 0 < g0) (hle : g0 ≤ g1)
    (h : R * N ^ 3 * (r * N / 4 + 2 * dF ^ 2) / g0 ≤ cst) : dF ^ 2 * (R * N ^ 3) / g1 ≤ cst := by
  have hX : 0 ≤ R * N ^ 3 := by positivity
  refine le_trans ?_ h
  calc dF ^ 2 * (R * N ^ 3) / g1 ≤ dF ^ 2 * (R * N ^ 3) / g0 := div_le_div_of_nonneg_left (by positivity) hg0 hle
    _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hg0.le
        have : dF ^ 2 ≤ r * N / 4 + 2 * dF ^ 2 := by nlinarith [sq_nonneg dF, mul_nonneg hr hN]
        nlinarith [mul_le_mul_of_nonneg_left this hX]

theorem exists_thRule_value_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G), P.TorsionIso → CharZero (IsLocalRing.ResidueField T.V) → ∀ (φ : ℝ), GlobalTheory.SlopeRec.HasPhi y φ → ∀ (α : 𝓞 E) (q : ℕ), α * star α = ((q : ℕ) : 𝓞 E) → q ∣ l.M → l.Mb ≤ Ideal.span {star α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∑ f : Lt1 Dw, 2 * rk f ≤ n → 1 ≤ n → ∀ (N cst : ℝ), ((Module.finrank ℚ E * Dw.q : ℕ) : ℝ) ≤ N → 4 * DF Dw a + 4 ≤ q → (DF Dw a : ℝ) * (2 * Real.sqrt N) < q → (DF Dw a : ℝ) ^ 2 * ((|(discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) / (2 * Module.finrank ℚ E) * N ^ 3) / q ≤ cst → ∃ f ∈ thGen Xo c nab a n, evI y f ≠ 0 ∧ (vV T.V (evI y f) : ℝ) ≤ cst * φ := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab T io y C hTr P hP hch φ hφ α q hα hq hMb a n hanti hs hn N cst hρN h4 hM0 hcst
  obtain ⟨P₁, hP₁, hB⟩ := GlobalTheory.T.exists_harmonicPoly_localInvariant_nonpos_char0 E H Dw l Xo c a n hanti hs
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  obtain ⟨⟨Q, hQ⟩, -⟩ := GlobalTheory.PowData.exists_powData E H Dw l Xo c T io y C P ϖ hϖ
  obtain ⟨ρ, hρ, hSB⟩ := GlobalTheory.ShortPhi.exists_shortBasis E H Dw l Xo c T io y φ hφ C P ϖ hϖ Q hQ
  set R : ℝ := |(discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E) / (2 * Module.finrank ℚ E) with hR
  have hR0 : 0 ≤ R := by positivity
  have hρN' : (ρ : ℝ) ≤ N := le_trans (by exact_mod_cast hρ) hρN
  have hρ0 : (0 : ℝ) ≤ ρ := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := hρ0.trans hρN'
  have hM0' : (DF Dw a : ℝ) * (2 * Real.sqrt ρ) < q := lt_of_le_of_lt (by gcongr) hM0
  have hup := GlobalTheory.T.iInf_thetaRule_le_localValue_charZero E H Dw l Xo c nab hnab T io y C hTr P hP hch ϖ hϖ Q hQ ρ _ _ hSB α q hα hq hMb a n 1 hn one_pos h4
    hM0' P₁ hP₁
  have hloc := hB T io y C hch 1 l.M one_pos
  have hφ0 := hφ.nonneg
  have hq0 : (0 : ℝ) < q := by
    have h : 0 < q := by omega
    exact_mod_cast h
  set B : ℝ := (DF Dw a : ℝ) ^ 2 * (R * (ρ : ℝ) ^ 3 * φ) / q / ((1 : ℕ) : ℝ) with hBdef
  have hBle : B ≤ cst * φ := by
    rw [hBdef, Nat.cast_one, div_one]
    calc (DF Dw a : ℝ) ^ 2 * (R * (ρ : ℝ) ^ 3 * φ) / q ≤ (DF Dw a : ℝ) ^ 2 * (R * N ^ 3 * φ) / q := by gcongr
      _ = (DF Dw a : ℝ) ^ 2 * (R * N ^ 3) / q * φ := by ring
      _ ≤ cst * φ := by gcongr
  have hinf : (⨅ (f : Rul Xo c) (_ : ∃ x : Fin n → Dw.La, IsThRule Xo c nab x P₁ f), nval T.V 1 (evI y f)) ≤
      ((B : ℝ) : EReal) := by
    refine hup.trans ?_
    calc _ ≤ (0 : EReal) + ((B : ℝ) : EReal) := add_le_add hloc le_rfl
      _ = _ := zero_add _
  by_contra hne
  push_neg at hne
  have hlow : (((⌊B⌋ + 1 : ℤ) : ℝ) : EReal) ≤
      ⨅ (f : Rul Xo c) (_ : ∃ x : Fin n → Dw.La, IsThRule Xo c nab x P₁ f), nval T.V 1 (evI y f) := by
    refine le_iInf₂ fun f ⟨x, hx⟩ => ?_
    have hf : f ∈ thGen Xo c nab a n := ⟨x, P₁, hP₁, hx⟩
    by_cases h0 : evI y f = 0
    · rw [h0, nval_zero]; exact le_top
    have h1 := hne f hf h0
    rw [nval_of_ne h0, Nat.cast_one, div_one, EReal.coe_le_coe_iff]
    have h2 : B < (vV T.V (evI y f) : ℝ) := lt_of_le_of_lt hBle h1
    have h3 : ⌊B⌋ < vV T.V (evI y f) := Int.floor_lt.2 h2
    exact_mod_cast h3
  have h5 := EReal.coe_le_coe_iff.1 (hlow.trans hinf)
  push_cast at h5
  linarith [Int.lt_floor_add_one B]

end GlobalTheory.JetsCharZero

end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TautRigid

def dlog (k : Type) [Field k] : (DualNumber k)ˣ →* Multiplicative k where
  toFun x := Multiplicative.ofAdd ((x : DualNumber k).snd / (x : DualNumber k).fst)
  map_one' := by simp
  map_mul' x y := by
    have fne : ∀ x : (DualNumber k)ˣ, (x : DualNumber k).fst ≠ 0 := fun x h => by
      have := congrArg TrivSqZeroExt.fst x.mul_inv
      rw [TrivSqZeroExt.fst_mul, h, zero_mul, TrivSqZeroExt.fst_one] at this
      exact zero_ne_one this
    have hx := fne x
    have hy := fne y
    rw [← ofAdd_add]
    congr 1
    simp only [Units.val_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    field_simp
    ring

theorem fst_ne_zero {k : Type} [Field k] (x : (DualNumber k)ˣ) : (x : DualNumber k).fst ≠ 0 := fun h => by
  have := congrArg TrivSqZeroExt.fst x.mul_inv
  rw [TrivSqZeroExt.fst_mul, h, zero_mul, TrivSqZeroExt.fst_one] at this
  exact zero_ne_one this

theorem dlog_apply {k : Type} [Field k] (x : (DualNumber k)ˣ) :
    Multiplicative.toAdd (dlog k x) = (x : DualNumber k).snd / (x : DualNumber k).fst := rfl

def onePlus {k : Type} [Field k] (s : k) : (DualNumber k)ˣ where
  val := 1 + TrivSqZeroExt.inr s
  inv := 1 - TrivSqZeroExt.inr s
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

theorem dlog_onePlus {k : Type} [Field k] (s : k) : Multiplicative.toAdd (dlog k (onePlus s)) = s := by
  rw [dlog_apply]; simp [onePlus]

end GlobalTheory.TautRigid

namespace GlobalTheory.TautRigid

open GlobalTheory.RigChart GlobalTheory.ToricData

variable {R : Type} [CommRing R] [IsDomain R]

def lamC (Q : DegPre R) {k : Type} [Field k] {B' : Scheme.{0}} {π₁ π₂ : B' ⟶ Q.P.A.left}
    (w : LB.Iso (Q.P.L.pull π₁) (Q.P.L.pull π₂)) (c' : Q.X → (Sp (DualNumber k) ⟶ B')) (y z : Q.X)
    (zz : Sp (DualNumber k)) (J : (Sp (DualNumber k) ⟶ Q.P.A.left) → Q.P.L.ι) : ((Sp (DualNumber k)).presheaf.stalk zz)ˣ :=
  gm (c' (y + z)) zz _ (w.s (fun _ => J (c' (y + z) ≫ π₂), fun _ => J (c' (y + z) ≫ π₁))) *
    (gm (c' y) zz _ (w.s (fun _ => J (c' y ≫ π₂), fun _ => J (c' y ≫ π₁))))⁻¹ *
    (gm (c' z) zz _ (w.s (fun _ => J (c' z ≫ π₂), fun _ => J (c' z ≫ π₁))))⁻¹ *
    gm (c' 0) zz _ (w.s (fun _ => J (c' 0 ≫ π₂), fun _ => J (c' 0 ≫ π₁)))

def AbConst (Q : DegPre R) {k : Type} [Field k] (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B']
    (π₁ π₂ : B'.left ⟶ Q.P.A.left) (w : LB.Iso (Q.P.L.pull π₁) (Q.P.L.pull π₂)) (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)) :
    Prop :=
  IsGrpPullback B' Q.P.A (spMap ρ) π₁ ∧ IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂ ∧
    (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k),
      x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) ∧
    w.IsGen ∧ (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (Q.c y).left ∧
      c' y ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left)

end GlobalTheory.TautRigid
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.ChartHartogs

theorem stalk_normal (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (p : PrimeSpectrum R) :
    IsDomain ((Spec.structureSheaf R).presheaf.stalk p) ∧ IsIntegrallyClosed ((Spec.structureSheaf R).presheaf.stalk p) :=
  ⟨IsLocalization.isDomain_of_le_nonZeroDivisors (R := R) (M := p.asIdeal.primeCompl) (S := (Spec.structureSheaf R).presheaf.stalk p) (hM := p.asIdeal.primeCompl_le_nonZeroDivisors),
    isIntegrallyClosed_of_isLocalization _ p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors⟩

theorem chart_normal (σ : Setup) (x : Sp σ.R) :
    IsLocallyNoetherian (σ.C x).G.left ∧ ∀ z : (σ.C x).G.left, IsIntegrallyClosed ((σ.C x).G.left.presheaf.stalk z) := by
  have hs : Smooth (σ.C x).G.hom := (σ.C x).semi.smooth
  obtain ⟨h1, h2⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (σ.C x).R
  refine ⟨LocallyOfFiniteType.isLocallyNoetherian (σ.C x).G.hom, fun z => ?_⟩
  have := (stalk_normal (σ.C x).R ((σ.C x).G.hom z)).1
  have := (stalk_normal (σ.C x).R ((σ.C x).G.hom z)).2
  exact (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_of_smooth (σ.C x).G.hom z).2

theorem mem_sec_iff : ∀ (σ : Setup) (x : Sp σ.R) (k : ℕ) (v : (σ.C x).G.left.functionField), v ∈ Sec (σ.D₁ x) k ↔ (∀ z : (σ.V x).toScheme, (k • σ.D₁ x).RegularAt ((σ.V x).ι z) v) ∧ ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → RegAt z v := by
  intro σ x k v
  have hV1 : ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → (k • σ.D₁ x).IsEqn z 1 := fun z hz => by
    simpa using (σ.noVert x z hz).nsmul k
  constructor
  · intro h
    refine ⟨fun z => h _, fun z hz => ?_⟩
    have := (hV1 z hz).regularAt_iff.1 (h z)
    simpa using this
  · rintro ⟨h1, h2⟩ y
    obtain ⟨hLN, hN⟩ := chart_normal σ x
    obtain ⟨g, hg⟩ := (k • σ.D₁ x).exists_isEqn y
    obtain ⟨U, hyU, hU⟩ := hg.exists_nhds
    refine hg.regularAt_iff.2 (GlobalTheory.Hartogs.regAt_of_forall_dvr _ hN _ y fun z hzy hdvr => ?_)
    have hgz := hU z (hzy.mem_open U.isOpen hyU)
    by_cases hzV : z ∈ σ.V x
    · have := h1 ⟨z, hzV⟩
      rw [Scheme.Opens.ι_apply] at this
      exact hgz.regularAt_iff.1 this
    · have hv : Vert (σ.C x).G.hom (σ.ρ x σ.f) z :=
        ⟨IsDiscreteValuationRing.ringKrullDim_eq_one _, not_not.1 fun h => hzV ((σ.hV x z).2 h)⟩
      exact hgz.regularAt_iff.1 ((hV1 z hv).regularAt_iff.2 (by simpa using h2 z hv))

end GlobalTheory.Desc.ChartHartogs
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem gp_comp_eq_spMap_cst (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (p : X ⟶ Sp R) :
    gp X ≫ p = spMap (cst p) := by
  have h : p = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop) := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
    simp [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  conv_lhs => rw [h]
  rw [gp]
  erw [Scheme.fromSpecStalk_toSpecΓ_assoc]
  erw [← Spec.map_comp]
  rfl

end GlobalTheory.Desc
end
