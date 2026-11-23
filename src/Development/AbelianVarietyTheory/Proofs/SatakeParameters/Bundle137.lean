module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
public import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.Bundle001
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle056
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle055
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle080
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle083
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle111
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle121
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle130
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle129
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.MvPowerSeries.Rename
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

theorem _root_.GlobalTheory.T.tameIwahoriEigenvector_jacquetQuotient_ne_zero : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (v : π.V) (θ : Fin n → kˣ →* ℂˣ), v ≠ 0 → IsIwVec θ π.π v → (Submodule.Quotient.mk v : Jacquet π.π (unipB k (Fin n))) ≠ 0 := by
  first | exact @GlobalTheory.TameIwahori.JacquetNonzero.jacquet_mk_ne_zero | exact GlobalTheory.TameIwahori.JacquetNonzero.jacquet_mk_ne_zero | (intros; apply GlobalTheory.TameIwahori.JacquetNonzero.jacquet_mk_ne_zero <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem acris0_le_sa : ∀ (l : ℕ) [Fact l.Prime] (ϖ : _root_.Formalism.Per.Fl l), ϖ.untilt = ((l : ℕ) : _root_.Formalism.Per.OC l) →
    ∀ a : _root_.Formalism.Per.Acris0 l, (a : _root_.Formalism.Per.AinfP l) ∈ Sa ϖ := by
  intro l _ ϖ hϖ a
  obtain ⟨_, _, -, -, hK, -⟩ := GlobalTheory.AinfChecks.padicComplex l
  have hk : RingHom.ker (Per.θ l) = Ideal.span {((l : ℕ) : _root_.Formalism.Per.Ainf l) - _root_.Formalism.Per.tm ϖ} := (hK ϖ hϖ).1
  refine GlobalTheory.RingIface.acris0_le l (Sa ϖ) ?_ a.2
  intro x hx n y hn
  have hx2 : x ∈ Ideal.span {((l : ℕ) : _root_.Formalism.Per.Ainf l) - _root_.Formalism.Per.tm ϖ} := hk ▸ RingHom.mem_ker.2 hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx2
  obtain ⟨c', hc⟩ := GlobalTheory.RingBasics.exists_pow_div_factorial l n
  have hc' : ((n.factorial : ℕ) : _root_.Formalism.Per.AinfP l) * algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) (_root_.Formalism.Per.zA l c') =
      ((l : ℕ) : _root_.Formalism.Per.AinfP l) ^ n := by
    have h := congrArg ((algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l)).comp (_root_.Formalism.Per.zA l)) hc
    rwa [map_mul, map_natCast, map_pow, map_natCast, RingHom.comp_apply] at h
  have hX : algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) (c * (((l : ℕ) : _root_.Formalism.Per.Ainf l) - _root_.Formalism.Per.tm ϖ)) =
      -algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) c * (((l : ℕ) : _root_.Formalism.Per.AinfP l) * beta ϖ) := by
    rw [l_mul_beta, map_mul, map_sub, map_natCast]; ring
  have key : y = algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) (_root_.Formalism.Per.zA l c') *
      (-algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) c) ^ n * beta ϖ ^ n := by
    apply (GlobalTheory.RingBasics.isUnit_nat l n.factorial n.factorial_ne_zero).mul_left_cancel
    rw [hn, hX, mul_pow, mul_pow, ← hc']
    ring
  rw [key]
  exact mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem (neg_mem (Subalgebra.algebraMap_mem _ _)) _))
    (pow_mem (Algebra.self_mem_adjoin_singleton _ _) _)

end GlobalTheory.Pst.StLat
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.Pst.StLat.BetaDiv

variable {l : ℕ} [Fact l.Prime]

theorem Sa_decomp (ϖ : _root_.Formalism.Per.Fl l) (x : _root_.Formalism.Per.AinfP l) (hx : x ∈ Sa ϖ) :
    ∃ a : _root_.Formalism.Per.Ainf l, ∃ y ∈ Sa ϖ, x = algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) a + beta ϖ * y := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, one_mem _, by rw [hx, map_zero, zero_add, mul_one]⟩
  | algebraMap r => exact ⟨r, 0, zero_mem _, by rw [mul_zero, add_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, u, hu, rfl⟩ := hx
    obtain ⟨b, v, hv, rfl⟩ := hy
    exact ⟨a + b, u + v, add_mem hu hv, by rw [map_add (f := _)]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, u, hu, rfl⟩ := hx
    obtain ⟨b, v, hv, rfl⟩ := hy
    have hb : beta ϖ ∈ Sa ϖ := Algebra.subset_adjoin (Set.mem_singleton _)
    refine ⟨a * b, algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) a * v + u * algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) b
      + beta ϖ * u * v, ?_, by rw [map_mul]; ring⟩
    exact add_mem (add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) hv)
      (mul_mem hu (Subalgebra.algebraMap_mem _ _))) (mul_mem (mul_mem hb hu) hv)

theorem Sa_cancel_beta (ϖ : _root_.Formalism.Per.Fl l) (hϖ : ϖ.untilt = ((l : ℕ) : _root_.Formalism.Per.OC l))
    (hk : Per.kerP l = Ideal.span {beta ϖ}) (c : _root_.Formalism.Per.AinfP l) (hc : beta ϖ * c ∈ Sa ϖ) : c ∈ Sa ϖ := by
  obtain ⟨i1, i2, -, -, hK, -⟩ := GlobalTheory.AinfChecks.padicComplex l
  obtain ⟨hsurj, hker, hA, -, hdom, hinj, -⟩ := thetaP_facts l
  obtain ⟨hK1, hK2, -⟩ := hK ϖ hϖ
  obtain ⟨a, y, hy, hxy⟩ := Sa_decomp ϖ _ hc

  have ha : algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) a ∈ Per.kerP l := by
    rw [hk, Ideal.mem_span_singleton']
    exact ⟨c - y, by linear_combination hxy⟩
  have hθ : Per.θ l a = 0 := by
    rw [← hker, RingHom.mem_ker, hA] at ha
    exact Subtype.ext (by simpa using ha)
  have hmem : a ∈ RingHom.ker (Per.θ l) := hθ
  have hK1' : RingHom.ker (Per.θ l) = Ideal.span {((l : ℕ) : _root_.Formalism.Per.Ainf l) - _root_.Formalism.Per.tm ϖ} := hK1
  rw [hK1', Ideal.mem_span_singleton'] at hmem
  obtain ⟨d, hd⟩ := hmem

  have hne : ((l : ℕ) : _root_.Formalism.Per.Ainf l) - _root_.Formalism.Per.tm ϖ ≠ 0 := nonZeroDivisors.ne_zero hK2
  have hβ : beta ϖ ≠ 0 := by
    intro h0
    apply hne
    apply hinj
    have := l_mul_beta ϖ
    rw [h0, mul_zero] at this
    rw [map_sub, map_natCast, map_zero]
    linear_combination this
  have hlb := l_mul_beta ϖ
  have e : beta ϖ * c = beta ϖ * (y - ((l : ℕ) : _root_.Formalism.Per.AinfP l) * algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) d) := by
    rw [hxy, ← hd, map_mul, map_sub, map_natCast]
    linear_combination (algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) d) * hlb
  rw [mul_left_cancel₀ hβ e]
  exact sub_mem hy (mul_mem (natCast_mem _ _) (Subalgebra.algebraMap_mem _ _))

theorem Sa_cancel_beta_pow (ϖ : _root_.Formalism.Per.Fl l) (hϖ : ϖ.untilt = ((l : ℕ) : _root_.Formalism.Per.OC l))
    (hk : Per.kerP l = Ideal.span {beta ϖ}) (i : ℕ) : ∀ c : _root_.Formalism.Per.AinfP l, beta ϖ ^ i * c ∈ Sa ϖ → c ∈ Sa ϖ := by
  induction i with
  | zero => intro c hc; simpa using hc
  | succ i ih =>
    intro c hc
    refine Sa_cancel_beta ϖ hϖ hk c (ih _ ?_)
    rwa [← mul_assoc, ← pow_succ]

theorem Sg_div_betaD_pow : ∀ (l : ℕ) [Fact l.Prime] (ϖ : _root_.Formalism.Per.Fl l), ϖ.untilt = ((l : ℕ) : _root_.Formalism.Per.OC l) → Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, _root_.Formalism.Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ s ∈ Sg ϖ, ∀ i : ℕ, betaD ϖ ^ i ∣ s → ∃ s' ∈ Sg ϖ, s = betaD ϖ ^ i * s' := by
  intro l _ ϖ hϖ hk hF s hs i hd
  obtain ⟨s₀, hs₀, rfl⟩ := Subring.mem_map.1 hs
  have hβ : beta ϖ ∈ Per.kerP l := by rw [hk]; exact Ideal.mem_span_singleton_self _
  have h2 : s₀ ∈ Per.kerP l ^ i := by
    obtain ⟨z, hz⟩ := hd
    have hb : betaD ϖ ^ i = algebraMap (_root_.Formalism.Per.AinfP l) (_root_.Formalism.Per.BdRp l) (beta ϖ ^ i) := by rw [map_pow, betaD]
    have h1 := congrArg (Per.ev l i) hz
    rw [hb, map_mul, GlobalTheory.MemLoc.ev_algebraMap, GlobalTheory.MemLoc.ev_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hβ i), zero_mul] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  rw [hk, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h2
  obtain ⟨c, hc⟩ := h2
  have hcS : c ∈ Sa ϖ := Sa_cancel_beta_pow ϖ hϖ hk i c (by rw [mul_comm, hc]; exact hs₀)
  refine ⟨algebraMap (_root_.Formalism.Per.AinfP l) (_root_.Formalism.Per.BdRp l) c, Subring.mem_map.2 ⟨c, hcS, rfl⟩, ?_⟩
  rw [← hc, map_mul, map_pow, mul_comm, betaD]

end GlobalTheory.Pst.StLat.BetaDiv
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem ker_localizedTheta_eq_span_beta : ∀ (l : ℕ) [Fact l.Prime] (ϖ : _root_.Formalism.Per.Fl l), ϖ.untilt = ((l : ℕ) : _root_.Formalism.Per.OC l) →
    Per.kerP l = Ideal.span {beta ϖ} := by
  intro l _ ϖ hϖ
  obtain ⟨_, _, -, -, hK, -⟩ := GlobalTheory.AinfChecks.padicComplex l
  have hk : RingHom.ker (Per.θ l) = Ideal.span {((l : ℕ) : _root_.Formalism.Per.Ainf l) - _root_.Formalism.Per.tm ϖ} := (hK ϖ hϖ).1
  obtain ⟨-, hker, hA, -⟩ := thetaP_facts l
  have hu := GlobalTheory.RingBasics.isUnit_l l
  have hmem : ∀ a : _root_.Formalism.Per.Ainf l, Per.θ l a = 0 →
      algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) a ∈ Per.kerP l := by
    intro a ha
    rw [← hker, RingHom.mem_ker, hA, ha]
    rfl
  have h0 : Per.θ l (((l : ℕ) : _root_.Formalism.Per.Ainf l) - _root_.Formalism.Per.tm ϖ) = 0 := by
    have : ((l : ℕ) : _root_.Formalism.Per.Ainf l) - _root_.Formalism.Per.tm ϖ ∈ RingHom.ker (Per.θ l) := by
      rw [hk]; exact Ideal.mem_span_singleton_self _
    exact this
  have hlb : ((l : ℕ) : _root_.Formalism.Per.AinfP l) * beta ϖ =
      -algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) (((l : ℕ) : _root_.Formalism.Per.Ainf l) - _root_.Formalism.Per.tm ϖ) := by
    rw [l_mul_beta, map_sub, map_natCast]; ring
  refine le_antisymm (fun y hy => ?_) ?_
  · rw [← hker, RingHom.mem_ker] at hy
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj ((l : ℕ) : _root_.Formalism.Per.Ainf l) y
    rw [map_natCast] at h
    have ha : Per.θ l a = 0 := by
      apply Subtype.ext
      rw [← hA, ← h, map_mul, hy, zero_mul]
      rfl
    have h2 : a ∈ Ideal.span {((l : ℕ) : _root_.Formalism.Per.Ainf l) - _root_.Formalism.Per.tm ϖ} := hk ▸ ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h2
    rw [← Ideal.mul_unit_mem_iff_mem _ (hu.pow n), h, map_mul]
    have : algebraMap (_root_.Formalism.Per.Ainf l) (_root_.Formalism.Per.AinfP l) (((l : ℕ) : _root_.Formalism.Per.Ainf l) - _root_.Formalism.Per.tm ϖ) =
        -(((l : ℕ) : _root_.Formalism.Per.AinfP l) * beta ϖ) := by rw [hlb, neg_neg]
    rw [this]
    exact Ideal.mul_mem_left _ _ (neg_mem (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
  · rw [Ideal.span_singleton_le_iff_mem]
    have h3 : ((l : ℕ) : _root_.Formalism.Per.AinfP l) * beta ϖ ∈ Per.kerP l := by
      rw [hlb]; exact neg_mem (hmem _ h0)
    have h4 : linv l * (((l : ℕ) : _root_.Formalism.Per.AinfP l) * beta ϖ) = beta ϖ := by
      rw [← mul_assoc, mul_comm (linv l), mul_linv, one_mul]
    rw [← h4]
    exact Ideal.mul_mem_left _ _ h3

end GlobalTheory.Pst.StLat
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.eq_zero_of_mem_clos_of_pow_mul_mul_mem_clos : ∀ {R : Type} [CommRing R] [IsDomain R] (p : ℕ), p.Prime → IsUnit ((p : ℕ) : R) → ∀ (π : R), π ≠ 0 →
  (∀ x : R, (∀ n : ℕ, π ^ n ∣ x) → x = 0) → ∀ (S : Subring R),
  (∀ s ∈ S, ∀ i : ℕ, π ^ i ∣ s → ∃ s' ∈ S, s = π ^ i * s') →
  (∀ y : R, (∀ k : ℕ, ∃ s ∈ S, π ∣ y - ((p : ℕ) : R) ^ k * s) → π ∣ y) →
  ∀ u : R, (∀ m : ℕ, 1 ≤ m → ∃ s ∈ S, ∃ e : R, (e = 1 ∨ e = -1) ∧
    π ^ (2 * p ^ m) ∣ ((p : ℕ) : R) * (((p : ℕ) : R) ^ (m - 1) * u - s) - e * π ^ (p ^ m)) →
  ∀ (a : R) (r : ℕ), a ∈ Clos S π → ((p : ℕ) : R) ^ r * a * u ∈ Clos S π → a = 0 := by
  first | exact @GlobalTheory.Pst.StLat.clos_eq_zero_of_mul_mem | exact GlobalTheory.Pst.StLat.clos_eq_zero_of_mul_mem | (intros; apply GlobalTheory.Pst.StLat.clos_eq_zero_of_mul_mem <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

theorem _root_.GlobalTheory.T.exists_projForm_nonvanishing_genericPoint_complexPoints : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (N : ℕ) (ι : X ⟶ PSpace ℂ N) (n : ℕ)
    (F : Finset (CxPts p (RingHom.id ℂ))), ∃ f ∈ GlobalTheory.ProjSpace.grading ℂ N n,
      genericPoint X ∈ GlobalTheory.EtProj.fOpen ι f ∧ ∀ z ∈ F, z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι f) := by
  first | (exact @GlobalTheory.EtProj.exists_form_genericPoint_cxPts) | (exact GlobalTheory.EtProj.exists_form_genericPoint_cxPts) | (intros; apply GlobalTheory.EtProj.exists_form_genericPoint_cxPts  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

theorem _root_.GlobalTheory.T.ratio_span_cotangent_change_denominator : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (N : ℕ) (ι : X ⟶ PSpace ℂ N), IsClosedImmersion ι → ∀ (n : ℕ), 0 < n →
    ∀ (k : ℕ) (f : Fin k → MvPolynomial (Fin (N + 1)) ℂ) (a b : MvPolynomial (Fin (N + 1)) ℂ)
      (hf : ∀ j, f j ∈ GlobalTheory.ProjSpace.grading ℂ N n) (ha : a ∈ GlobalTheory.ProjSpace.grading ℂ N n)
      (hb : b ∈ GlobalTheory.ProjSpace.grading ℂ N n) (z : CxPts p (RingHom.id ℂ))
      (hza : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι a))
      (hzb : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι b)),
      RingHom.ker (CxPts.evHom hza) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (f j) a (hf j) ha) ⊔
          RingHom.ker (CxPts.evHom hza) ^ 2 →
      RingHom.ker (CxPts.evHom hzb) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (f j) b (hf j) hb) ⊔
          RingHom.ker (CxPts.evHom hzb) ^ 2 := by
  first | (exact @GlobalTheory.EtProj.span_ratio_of_span_ratio) | (exact GlobalTheory.EtProj.span_ratio_of_span_ratio) | (intros; apply GlobalTheory.EtProj.span_ratio_of_span_ratio  <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

namespace GlobalTheory.OnePlace

open MvPowerSeries Formalism.MainNotions.GL3Theta

theorem coeffsWp_mul {τ : Type} {p : ℕ} [Fact p.Prime] {f g : MvPowerSeries τ ℂ_[p]}
    (hf : ∀ m, coeff m f ∈ Wp p) (hg : ∀ m, coeff m g ∈ Wp p) : ∀ m, coeff m (f * g) ∈ Wp p := by
  intro m
  rw [coeff_mul]
  exact Subring.sum_mem _ fun x _ => Subring.mul_mem _ (hf _) (hg _)

theorem coeffsWp_one {τ : Type} {p : ℕ} [Fact p.Prime] : ∀ m, coeff m (1 : MvPowerSeries τ ℂ_[p]) ∈ Wp p := by
  intro m
  rw [coeff_one]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem coeffsWp_pow {τ : Type} {p : ℕ} [Fact p.Prime] {f : MvPowerSeries τ ℂ_[p]}
    (hf : ∀ m, coeff m f ∈ Wp p) (k : ℕ) : ∀ m, coeff m (f ^ k) ∈ Wp p := by
  induction k with
  | zero => simpa using coeffsWp_one
  | succ k ih => rw [pow_succ]; exact coeffsWp_mul ih hf

theorem coeffsWp_subst {σ τ : Type} {p : ℕ} [Fact p.Prime] {a : σ → MvPowerSeries τ ℂ_[p]} (ha : HasSubst a)
    (hA : ∀ i m, coeff m (a i) ∈ Wp p) {f : MvPowerSeries σ ℂ_[p]} (hf : ∀ m, coeff m f ∈ Wp p) :
    ∀ m, coeff m (subst a f) ∈ Wp p := by
  intro e
  rw [coeff_subst ha]
  refine finsum_induction (fun w => w ∈ Wp p) (Subring.zero_mem _) (fun x y hx hy => Subring.add_mem _ hx hy) ?_
  intro d
  refine Subring.mul_mem _ (hf d) ?_
  have hP : ∀ m, coeff m (d.prod fun s k => a s ^ k) ∈ Wp p := by
    unfold Finsupp.prod
    induction d.support using Finset.induction_on with
    | empty => simpa using coeffsWp_one
    | insert i S hi ih => rw [Finset.prod_insert hi]; exact coeffsWp_mul (coeffsWp_pow (hA i) _) ih
  exact hP e

theorem coeffsWp_X {τ : Type} {p : ℕ} [Fact p.Prime] (t : τ) : ∀ m, coeff m (X t : MvPowerSeries τ ℂ_[p]) ∈ Wp p := by
  intro m
  rw [coeff_X]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem hasSubst_copy {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (a : Fin r0) (b : Fin r1) :
    HasSubst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) := by
  have hinj : Function.Injective (fun s : ZMod n' => ((s, a, b) : ZMod n' × Fin r0 × Fin r1)) := by
    intro s t h
    simpa using h
  haveI : Filter.TendstoCofinite (fun s : ZMod n' => ((s, a, b) : ZMod n' × Fin r0 × Fin r1)) := ⟨hinj.tendsto_cofinite⟩
  exact HasSubst.X_comp (fun s : ZMod n' => ((s, a, b) : ZMod n' × Fin r0 × Fin r1))

theorem xiE_props {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p])
    (hx : ∀ r, IntegralW (x r) ∧ constantCoeff (x r) = 0) (i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) :
    constantCoeff (xiE x i) = 0 ∧ ∀ m, coeff m (xiE x i) ∈ Wp p := by
  rcases i with ⟨r, a, b⟩ | ⟨r, a, b⟩
  · exact ⟨constantCoeff_subst_eq_zero (hasSubst_copy a b) (fun _ => constantCoeff_X _) (hx _).2,
      coeffsWp_subst (hasSubst_copy a b) (fun _ => coeffsWp_X _) (hx _).1⟩
  · exact ⟨constantCoeff_subst_eq_zero (hasSubst_copy a b) (fun _ => constantCoeff_X _) (hx _).2,
      coeffsWp_subst (hasSubst_copy a b) (fun _ => coeffsWp_X _) (hx _).1⟩

theorem xiE_integral : ∀ {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]), (∀ r, Formalism.MainNotions.GL3Theta.IntegralW (x r) ∧ MvPowerSeries.constantCoeff (x r) = 0) → (∀ i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, MvPowerSeries.constantCoeff (xiE x i) = 0) ∧ ∀ F : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p), IntS p F → ∀ m, ‖MvPowerSeries.coeff m (MvPowerSeries.subst (xiE x) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) F))‖ ≤ 1 := by
  intro p _ n' r0 r1 x hx
  have hP := xiE_props (r0 := r0) (r1 := r1) x hx
  refine ⟨fun i => (hP i).1, ?_⟩
  intro F hF m
  obtain ⟨g, rfl⟩ := hF
  have hs : HasSubst (xiE x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1 → _) :=
    hasSubst_of_constantCoeff_zero fun i => (hP i).1
  have hG : ∀ d, coeff d (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p)
      (MvPowerSeries.map (algebraMap (FormalGroupSystem.WW p) (FormalGroupSystem.K0 p)) g)) ∈ Wp p := by
    intro d
    rw [coeff_map, coeff_map]
    rw [Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap]
    exact Formalism.L2.G.Pend.wToC_mem_Wp p _
  exact GlobalTheory.BeProps.norm_le_one_of_mem_Wp (coeffsWp_subst hs (fun i => (hP i).2) hG m)

end GlobalTheory.OnePlace
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

theorem congr_at_d : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ (ι : ℂ ≃+* ℂ_[p]) (cE s : D.host.E ≃+* D.host.E) (δ : D.host.E), (∀ y, cE y = D.host.conj y) → δ ^ 2 = -(p : D.host.E) → s δ = -δ → (∀ y, s (s y) = y) → (∀ (t : HH D) (y : D.host.E), TaylorLogMetric.embT D (tauPl D (true, t)) y = TaylorLogMetric.embT D (tauPl D (false, t)) (s (cE y))) → (∀ (τ : D.what₂.Tau) (y : D.host.E), s y = y → ι (TaylorLogMetric.embT D τ y) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) → (‖ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))‖ ≤ 1 ∧ ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ)) ≠ 0) ∧ ∀ (t : HH D) (y : 𝓞 D.host.E), ‖GlobalTheory.DFrame.rho D ι (false, t) (D.host.conj (y : D.host.E)) - GlobalTheory.DFrame.rho D ι (true, t) (y : D.host.E)‖ ≤ ‖ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))‖ := by
  intro D p _ hpd ι cE s δ hcE hδ hsδ hss hpair hK
  set th : ℂ_[p] := ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ)) with hth
  have hp0 : (0 : ℝ) < ‖(p : ℂ_[p])‖ := Formalism.L2.Th1.GD.norm_p_pos
  have hp1 : ‖(p : ℂ_[p])‖ < 1 := Formalism.L2.Th1.GD.norm_p_lt_one
  have hsq : th ^ 2 = -(p : ℂ_[p]) := by
    rw [hth, ← map_pow, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), ← hpd]
    simp
  have hnorm2 : ‖th‖ ^ 2 = ‖(p : ℂ_[p])‖ := by
    rw [← norm_pow, hsq, norm_neg]
  have hnth : ‖th‖ = ‖(p : ℂ_[p])‖ ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← hnorm2, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · by_contra h
    push_neg at h
    have : 1 < ‖th‖ ^ 2 := by nlinarith
    linarith
  · intro h
    rw [h, norm_zero] at hnorm2
    simp at hnorm2
    linarith
  · intro t y
    have hp2 : p ≠ 2 := by
      have h := hypOdd_of_hostHyp D.host.hyp
      obtain ⟨-, -, h1, h2, h3⟩ := h
      omega
    have hI := Formalism.L2.Th1.GD.InertiaRam_proof p hp2 D.host.E s δ (rho D ι (false, t)) hδ hsδ hss
      (fun y hy => hK _ y hy)
    let y' : 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv y
    have hy' : ((y' : 𝓞 D.host.E) : D.host.E) = D.host.conj (y : D.host.E) := rfl
    have h2 := hI.2.1 y'
    rw [hy'] at h2
    have htrue : rho D ι (true, t) (y : D.host.E) = rho D ι (false, t) (s (D.host.conj (y : D.host.E))) := by
      show ι (TaylorLogMetric.embT D (tauPl D (true, t)) (y : D.host.E)) = ι (TaylorLogMetric.embT D (tauPl D (false, t)) _)
      rw [hpair t, hcE]
    rw [htrue, hnth]
    exact h2

end GlobalTheory.DFrame
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.mem_integralFiniteAdelesTensor_iff_localOrders : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (z : Af F ⊗[F] E), z ∈ intA F E ↔ ∀ v : HeightOneSpectrum (𝓞 F), evF E v z ∈ ordAt E v := by
  first | exact @GlobalTheory.PlaceComp.IntLocal.mem_intA_iff | exact GlobalTheory.PlaceComp.IntLocal.mem_intA_iff | (intros; apply GlobalTheory.PlaceComp.IntLocal.mem_intA_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.stabilises_completedLattice_iff_localMatrix_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (h : GL (Fin V.rank) (Fv F v ⊗[F] E)), IsFrameAt V v h → ∀ g, (∀ w, w ≠ v → locMat hc V w g = 1) → (Stab hc V g ↔ h⁻¹ * locMat hc V v g * h ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range) := by
  first | exact @GlobalTheory.PlaceComp.StabLoc.stab_iff | exact GlobalTheory.PlaceComp.StabLoc.stab_iff | (intros; apply GlobalTheory.PlaceComp.StabLoc.stab_iff <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.isTame_of_mem_weilDeligneListSum : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (l : List (WD h)), IsTameWD (sumList l) → ∀ y ∈ l, IsTameWD y := by
  first | (exact @GlobalTheory.TameSum.isTameWD_of_mem_sumList) | (exact GlobalTheory.TameSum.isTameWD_of_mem_sumList) | (intros; apply GlobalTheory.TameSum.isTameWD_of_mem_sumList  <;> assumption)
end
