module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle045
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantFamilyNorms
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ConjugateConjugate
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealEmbeddingCharacters
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle008
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle014
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem frChg_calculus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S], (∀ (g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s s' : S) (y y' y'' : FrPt Xo c S), FrChg g s y y' → (FrChg g' s' y' y'' ↔ FrChg (fun τ => g' τ * g τ) (s' * s) y y'')) ∧ (∀ y : FrPt Xo c S, FrChg (fun _ => 1) 1 y y) ∧ (∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s : S) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T), FrChg g s y y' → FrMap φ y z → (FrMap φ y' z' ↔ FrChg (fun τ => (g τ).map φ) (φ s) z z')) ∧ ∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' ↔ ∃ g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : S)) ∧ (∀ τ i j, i < j → g τ i j = 0) ∧ FrChg g (t none : S) y y' := by
  intro E _ _ _ H Dw l Xo c S _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g g' s s' y y' y'' h
    refine ⟨fun h' => (frChg_refl_and_comp E H Dw l Xo c S y y' y'').2 g g' s s' h h', fun h' => ?_⟩
    have hx : y'.x = y.x := h.1
    have hx' : y''.x = y.x := h'.1
    obtain ⟨g₀, a₀, hg₀, h₀⟩ := (frChg_exists_unique E H Dw l Xo c S y y').1 hx
    obtain ⟨rfl, rfl⟩ := (frChg_exists_unique E H Dw l Xo c S y y').2 _ _ _ _ h h₀
    obtain ⟨k, b, -, hk⟩ := (frChg_exists_unique E H Dw l Xo c S y' y'').1 (hx'.trans hx.symm)
    have hc := (frChg_refl_and_comp E H Dw l Xo c S y y' y'').2 _ _ _ _ h hk
    obtain ⟨e₁, e₂⟩ := (frChg_exists_unique E H Dw l Xo c S y y'').2 _ _ _ _ h' hc
    have e₃ : g' = k := by
      funext τ
      exact ((Matrix.isUnit_iff_isUnit_det _).2 (hg₀ τ)).mul_right_cancel (congrFun e₁ τ)
    have e₄ : s' = (b : S) := a₀.isUnit.mul_right_cancel e₂
    rw [e₃, e₄]
    exact hk
  · intro y
    exact (frChg_refl_and_comp E H Dw l Xo c S y y y).1
  · intro T _ _ φ g s y y' z z' h hm
    exact ChgBC.frChg_baseChange E H Dw l Xo c S T φ y y' z z' g s h hm
  · intro t y y'
    rw [(frBor_calculus E H Dw l Xo c S y y' y').1 t]
    exact ⟨fun ⟨g, a, b, c⟩ => ⟨g, b, a, c⟩, fun ⟨g, a, b, c⟩ => ⟨g, b, a, c⟩⟩

end GlobalTheory.Frames
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ

section FlowNorm

open ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds

theorem sum_step_telescope (L : ℕ → ℝ) (m : ℝ) {p r : ℕ} (hp : p ≤ r) :
    ∑ k ∈ Finset.range r, (if p ≤ k then m else -m) * (L (k + 1) - L k) = m * (L r + L 0 - 2 * L p) := by
  rw [← Finset.sum_range_add_sum_Ico _ hp]
  have h1 : ∑ k ∈ Finset.range p, (if p ≤ k then m else -m) * (L (k + 1) - L k) = -m * (L p - L 0) := by
    rw [← Finset.sum_range_sub L p, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_neg (by have := Finset.mem_range.mp hk; omega)]
  have h2 : ∑ k ∈ Finset.Ico p r, (if p ≤ k then m else -m) * (L (k + 1) - L k) = m * (L r - L p) := by
    rw [← Finset.sum_Ico_sub L hp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_pos (Finset.mem_Ico.mp hk).1]
  rw [h1, h2]; ring

theorem nfac_parallel_flowV {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (e : X.Ψ → Fin r → ℂ) (he : X.IsIsoV e) (la : Wt X.Ψ r) (m : ℝ)
    (hla : ∀ τ (j : Fin r), (la τ j : ℝ) = if X.p0 ≤ (j : ℕ) then m else -m)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hT : X.flowV e s x ∈ X.dom) :
    X.nfac la (X.flowV e s x) * (∏ τ, (X.ttV e (X.flowV e s x) τ)⁻¹) ^ m =
      X.nfac la x * (∏ τ, (X.ttV e x τ)⁻¹) ^ m := by
  have hρ : ∀ τ, 0 < rho X e s x τ X.p0 := fun τ => rho_pos X e he hx s hT τ _ X.p0_le
  have hr : ∀ τ, rfac X la x (X.flowV e s x) τ = (rho X e s x τ X.p0)⁻¹ ^ m := by
    intro τ
    have hsg := hsg_of X hx τ
    rw [rfac_eq X e he hx s hT τ la]
    set L : ℕ → ℝ := fun i => Real.log (rho X e s x τ i) with hLdef
    have hL0 : L 0 = 0 := by simp [L, rho, mN_zero]
    have hLr : L r = 0 := by
      simp [L, rho, mN_top (hG_of X τ) X.p0 (mat x τ) (hx τ).1 hsg (e τ) (he τ).1]
    have hsum : ∑ i : Fin r, (la τ i : ℝ) / 2 *
        (Real.log (rho X e s x τ ((i : ℕ) + 1)) - Real.log (rho X e s x τ i)) =
        ∑ k ∈ Finset.range r, (if X.p0 ≤ k then m / 2 else -(m / 2)) * (L (k + 1) - L k) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun k => (if X.p0 ≤ k then m / 2 else -(m / 2)) * (L (k + 1) - L k)) r]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hla]
      split_ifs <;> simp only [L] <;> ring
    rw [hsum, sum_step_telescope L (m / 2) X.p0_le, hL0, hLr,
      Real.rpow_def_of_pos (inv_pos.mpr (hρ τ)), Real.log_inv]
    congr 1
    simp only [L]; ring
  have hm : ∀ τ, 0 < mN τ.1 X.Gm (mat x τ) (e τ) X.p0 := fun τ =>
    mN_pos (hG_of X τ) X.p0 X.p0_le (mat x τ) (hx τ).1 (hsg_of X hx τ) (e τ) (he τ).1 (he τ).2
  have htpos : ∀ τ, 0 ≤ (X.ttV e x τ)⁻¹ := fun τ => by
    have := hm τ
    have := c_pos X τ
    rw [Data.ttV, maj_eq X hx e τ (he τ).1]
    positivity
  have ht : ∀ τ, (X.ttV e (X.flowV e s x) τ)⁻¹ = (rho X e s x τ X.p0)⁻¹ * (X.ttV e x τ)⁻¹ := by
    intro τ
    have h1 := hρ τ
    have h2 := hm τ
    have h3 := c_pos X τ
    rw [Data.ttV, Data.ttV, maj_flow X hx e τ (he τ).1 s h1.ne', maj_eq X hx e τ (he τ).1]
    simp only [rho] at h1 ⊢
    field_simp
  have hN := FlowCoefficientBounds.nfac_pos X hT la
  have hdiv := nfac_div X la x (X.flowV e s x)
  rw [div_eq_iff hN.ne', Finset.prod_congr rfl fun τ _ => hr τ,
    Real.finsetProd_rpow _ _ (fun τ _ => (inv_pos.mpr (hρ τ)).le)] at hdiv
  rw [hdiv, Finset.prod_congr rfl fun τ _ => ht τ, Finset.prod_mul_distrib,
    Real.mul_rpow (Finset.prod_nonneg fun τ _ => (inv_pos.mpr (hρ τ)).le)
      (Finset.prod_nonneg fun τ _ => htpos τ)]
  ring

end FlowNorm

theorem nfac_parallel_flow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (n : ℕ) (ξ' : Fin r → E), Even n → (U.X k).IsIso ξ' → ∀ x ∈ (U.X k).dom, ∀ s : (U.X k).Ψ → ℂ, (U.X k).flow ξ' s x ∈ (U.X k).dom → (U.X k).nfac (laU U 0 n k) ((U.X k).flow ξ' s x) * (∏ τ, ((U.X k).tt ξ' ((U.X k).flow ξ' s x) τ)⁻¹) ^ ((n : ℝ) / 2) = (U.X k).nfac (laU U 0 n k) x * (∏ τ, ((U.X k).tt ξ' x τ)⁻¹) ^ ((n : ℝ) / 2) := by
  intro E _ _ _ H Dw l Xo c σ r U k n ξ' hn hξ x hx s hT
  have hiso : (U.X k).IsIsoV ((U.X k).embV ξ') := fun τ =>
    ⟨by rw [show (U.X k).embV ξ' τ = Data.emb τ.1 ξ' from rfl, hermC_emb, hξ.2.1, map_zero],
      emb_ne_zero τ.1 hξ.2.2⟩
  refine nfac_parallel_flowV (U.X k) ((U.X k).embV ξ') hiso (laU U 0 n k) ((n : ℝ) / 2) ?_ hx s hT
  intro τ j
  obtain ⟨m, rfl⟩ := hn
  have h2 : (m + m) / 2 = m := by omega
  simp only [laU, h2]
  split_ifs <;> simp

end GlobalTheory.ArcQ
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.factor_exponent_commutator_eq_of_quasiPeriodic : ∀ (g : ℕ) (θ ρ : (Fin g → ℂ) → ℂ) (la mu : Fin g → ℂ) (A₁ A₂ B₁ B₂ : (Fin g → ℂ) →ₗ[ℂ] ℂ) (a₁ a₂ b₁ b₂ : ℂ), Differentiable ℂ θ → θ ≠ 0 → Differentiable ℂ ρ → (∀ z, ρ z ≠ 0) → a₁ ≠ 0 → a₂ ≠ 0 → (∀ z, θ (z + la) = a₁ * Complex.exp (A₁ z) * θ z) → (∀ z, θ (z + mu) = a₂ * Complex.exp (A₂ z) * θ z) → (∀ z, θ (z + la) * ρ (z + la) = b₁ * Complex.exp (B₁ z) * (θ z * ρ z)) → (∀ z, θ (z + mu) * ρ (z + mu) = b₂ * Complex.exp (B₂ z) * (θ z * ρ z)) → B₁ mu - A₁ mu = B₂ la - A₂ la := by
  first | exact @GlobalTheory.factor_commutator_eq_of_nonvanishing | exact GlobalTheory.factor_commutator_eq_of_nonvanishing | (intros; apply GlobalTheory.factor_commutator_eq_of_nonvanishing <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.tangentVector_pow_scale_inv_eq : ∀ (P : Out.PolAV (Sp ℂ)) (v : epsR ℂ ⟶ P.A) (n : ℕ), 0 < n → IsTangent v → spMap (epsScaleR ((n : ℂ)⁻¹)) ≫ (v ^ n).left = v.left := by
  first | exact @GlobalTheory.AbelianLetters.scale_tangent_pow | exact GlobalTheory.AbelianLetters.scale_tangent_pow | (intros; apply GlobalTheory.AbelianLetters.scale_tangent_pow <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.FrameCompare

open GlobalTheory.PullHermitian

section Val

variable {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) {L : LB Y} {L' : LB X} (φ : X ⟶ Y)

abbrev ix (j : L.ι) (i : L'.ι) : (LB.div (L.pull φ) L').ι := (fun _ => j, i)

lemma ix_chart (j : L.ι) (i : L'.ι) (hj : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j) (hi : ⊤ ≤ x ⁻¹ᵁ L'.U i) :
    ⊤ ≤ x ⁻¹ᵁ (LB.div (L.pull φ) L').U (ix φ j i) :=
  inf_of x (wchart_of x L φ j hj) hi

lemma val_iso_pull (w : LB.Iso L' (L.pull φ)) (hw : w.IsGen) (j j' : L.ι) (i i' : L'.ι)
    (hj : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j')
    (hi : ⊤ ≤ x ⁻¹ᵁ L'.U i) (hi' : ⊤ ≤ x ⁻¹ᵁ L'.U i') :
    valAt' x _ (w.s (ix φ j i)).val * valAt' x (L'.U i ⊓ L'.U i') (L'.g i i').val =
      valAt' (x ≫ φ) (L.U j ⊓ L.U j') (L.g j j').val * valAt' x _ (w.s (ix φ j' i')).val := by
  have c := wchart_of x L φ j hj
  have c' := wchart_of x L φ j' hj'
  have h := unitVal_iso x w hw (fun _ => j) (fun _ => j') i i' c c' hi hi'
  have h3 := unitVal_linComb x L φ 1 j j' (inf_of x c c') (inf_of _ hj hj')
  replace h := h.trans (congrArg (fun a => a * _ * _) h3)
  rw [valAt'_eq_unitVal x (ix_chart x φ j i hj hi),
    valAt'_eq_unitVal x (ix_chart x φ j' i' hj' hi'),
    valAt'_eq_unitVal x (inf_of x hi hi'), valAt'_eq_unitVal _ (inf_of _ hj hj')]
  have h4 := congrArg Units.val h
  simp only [Units.val_mul, zpow_one, Units.val_inv_eq_inv_val] at h4
  refine (congrArg (· * _) h4).trans ?_
  field_simp

lemma val_ne_zero (w : LB.Iso L' (L.pull φ)) (j : L.ι) (i : L'.ι)
    (hj : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j) (hi : ⊤ ≤ x ⁻¹ᵁ L'.U i) :
    valAt' x _ (w.s (ix φ j i)).val ≠ 0 := by
  rw [valAt'_eq_unitVal x (ix_chart x φ j i hj hi)]
  exact Units.ne_zero _

end Val

theorem exists_entire_unit_automorphy :
    ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (X : Scheme.{0}) (L : LB X) (L' : LB A'.left), L.IsLB → L'.IsLB → ∀ (φ : A'.left ⟶ X) (w : LB.Iso L' (L.pull φ)), w.IsGen → ∀ (g g' : ℕ) (u : HolUnif A' L' g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∀ (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), (∀ z, (u.ex (F z)).left ≫ φ = e z) → ∀ (fr : L.ι → (Fin g → ℂ) → ℂ) (th : L.Sec) (θ : (Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.U j}) → (∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → fr j z ≠ 0) → (∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L.U j ⊓ L.U j') → fr j z = valAt' (e z) (L.U j ⊓ L.U j') (L.g j j').val * fr j' z) → (∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → valAt' (e z) (L.U j) (th.f j) = θ z * fr j z) → ∃ ρ : (Fin g → ℂ) → ℂ, Differentiable ℂ ρ ∧ (∀ z, ρ z ≠ 0) ∧ ∀ (la : Fin g → ℂ) (l : u.Λ), F la = l → ∀ z, θ (z + la) * ρ (z + la) = χ l * Complex.exp (Real.pi * hermForm Hm (F z) l + Real.pi / 2 * hermForm Hm l l) * (θ z * ρ z) := by
  intro A' _ X L L' hL hL' φ w hw g g' u Hm χ hu e F he fr th θ hd hne hc hθ
  obtain rfl : e = fun z => (u.ex (F z)).left ≫ φ := funext fun z => (he z).symm
  have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  obtain ⟨r, hr, hrφ⟩ := exists_glue
    (fun p : L.ι × L'.ι => F ⁻¹' ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ L.U p.1)} ∩
      {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U p.2}))
    (fun p => ((u.hol _ 0).1.inter (u.hol _ 0).1).preimage hFd.continuous)
    (fun z => by
      obtain ⟨j, hj⟩ := exists_chart ((u.ex (F z)).left ≫ φ) hL
      obtain ⟨i, hi⟩ := exists_chart (u.ex (F z)).left hL'
      exact ⟨(j, i), hj, hi⟩)
    (fun p z => fr p.1 z / (valAt' (u.ex (F z)).left _ (w.s (ix φ p.1 p.2)).val * u.fr p.2 (F z)))
    (fun p => by
      have d1 := (u.hol _ (w.s (ix φ p.1 p.2)).val).2.comp
        (s := F ⁻¹' ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ L.U p.1)} ∩
          {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U p.2})) hFd.differentiableOn
        fun z hz => ix_chart _ φ _ _ hz.1 hz.2
      have d2 := (u.fr_hol p.2).comp
        (s := F ⁻¹' ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ L.U p.1)} ∩
          {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U p.2}))
        hFd.differentiableOn fun z hz => hz.2
      have d3 := (hd p.1).mono
        (s := F ⁻¹' ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ L.U p.1)} ∩
          {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U p.2})) fun z hz => hz.1
      simp only [div_eq_mul_inv]
      exact d3.mul ((d1.mul d2).inv fun z hz =>
        mul_ne_zero (val_ne_zero _ φ w _ _ hz.1 hz.2) (u.fr_ne p.2 _ hz.2)))
    (fun p q z hp hq => by
      have h := val_iso_pull (u.ex (F z)).left φ w hw p.1 q.1 p.2 q.2 hp.1 hq.1 hp.2 hq.2
      have h1 := hc p.1 q.1 z (inf_of _ hp.1 hq.1)
      have h2 := u.fr_compat p.2 q.2 (F z) (inf_of _ hp.2 hq.2)
      rw [div_eq_div_iff (mul_ne_zero (val_ne_zero _ φ w _ _ hp.1 hp.2) (u.fr_ne _ _ hp.2))
        (mul_ne_zero (val_ne_zero _ φ w _ _ hq.1 hq.2) (u.fr_ne _ _ hq.2)),
        h1, h2, ← _root_.mul_assoc (valAt' _ _ (w.s (ix φ p.1 p.2)).val), h]
      ring)
  have hchart : ∀ z, ∃ j i, ⊤ ≤ ((u.ex (F z)).left ≫ φ) ⁻¹ᵁ L.U j ∧
      ⊤ ≤ (u.ex (F z)).left ⁻¹ᵁ L'.U i := fun z => by
    obtain ⟨j, hj⟩ := exists_chart ((u.ex (F z)).left ≫ φ) hL
    obtain ⟨i, hi⟩ := exists_chart (u.ex (F z)).left hL'
    exact ⟨j, i, hj, hi⟩
  refine ⟨r, hr, fun z => ?_, fun la l hl z => ?_⟩
  · obtain ⟨j, i, hj, hi⟩ := hchart z
    rw [hrφ (j, i) z ⟨hj, hi⟩]
    exact div_ne_zero (hne _ _ hj) (mul_ne_zero (val_ne_zero _ φ w _ _ hj hi) (u.fr_ne _ _ hi))
  · obtain ⟨j, i, hj, hi⟩ := hchart z
    have hper : u.ex (F (z + la)) = u.ex (F z) := by
      rw [map_add (f := _), hl, u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
    have hj' : ⊤ ≤ ((u.ex (F (z + la))).left ≫ φ) ⁻¹ᵁ L.U j := by rwa [hper]
    have hi' : ⊤ ≤ (u.ex (F (z + la))).left ⁻¹ᵁ L'.U i := by rwa [hper]
    have h1 := hu.2.2.2 l i (F z) hi
    have t1 := hθ j z hj
    have t2 := hθ j (z + la) hj'
    have n1 := u.fr_ne _ _ hi
    have n2 := u.fr_ne _ _ hi'
    have n3 := val_ne_zero _ φ w _ _ hj hi
    rw [hrφ (j, i) z ⟨hj, hi⟩, hrφ (j, i) (z + la) ⟨hj', hi'⟩]
    simp only [hper] at t2 ⊢
    rw [← mul_div_assoc, ← mul_div_assoc, ← t1, ← t2]
    rw [map_add (f := _), hl] at n2 ⊢
    rw [h1] at n1 ⊢
    have n4 := left_ne_zero_of_mul n1
    simp only [hermForm]
    generalize χ l * Complex.exp _ = c at n4 ⊢
    generalize valAt' _ _ (w.s (ix φ j i)).val = a at n3 ⊢
    beta_reduce
    field_simp

end GlobalTheory.FrameCompare
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.thetaCharOff_ne_zero_differentiable_quasiPeriodic' : ∀ (g : ℕ) (S : Finset (Fin g)) (τ : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → (∀ k ∈ S, c₁ k = 0) → thetaCharOff S τ c₁ c₂ ≠ 0 ∧ Differentiable ℂ (thetaCharOff S τ c₁ c₂) ∧ ∀ m n : Fin g → ℤ, (∀ k ∈ S, n k = 0) → ∃ a : ℂ, a ≠ 0 ∧ ∀ z, thetaCharOff S τ c₁ c₂ (z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) = a * Complex.exp (-(2 * Real.pi * Complex.I) * ((fun i => (n i : ℂ)) ⬝ᵥ z)) * thetaCharOff S τ c₁ c₂ z := by
  first | exact @GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic | exact GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic | (intros; apply GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.FjFreq

open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem exists_emb_of_freq (la : Wt X.Ψ r) (ν : X.Ψ → ℝ)
    (hν : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k) :
    ∃ ω : E, ∀ τ : X.Ψ, (ν τ : ℂ) = τ.1 ω := by
  refine X.exists_emb_eq (fun τ => (ν τ : ℂ)) fun γ => ?_
  have hN : ((X.m * X.chiOrd la : ℕ) : ℝ) ≠ 0 := by
    have := Nat.mul_pos X.m_pos (chiOrd_pos X la); positivity
  have hγ : IsIntegral ℤ (γ : E) := RingOfIntegers.isIntegral_coe γ
  have hcγ : IsIntegral ℤ (cc (γ : E)) := map_isIntegral_int (IsCMField.complexConj E) hγ
  have ha : cc ((γ : E) + cc (γ : E)) = (γ : E) + cc (γ : E) := by
    rw [cc_add', cc_cc', add_comm]
  obtain ⟨k, hk⟩ := hν _ ((mem_periods_iff X la _).2 ⟨_, ha, hγ.add hcγ, rfl⟩)
  refine ⟨(k : ℚ) / (4 * (X.m * X.chiOrd la : ℕ)), ?_⟩
  have h1 : ∑ τ, ν τ * per X la ((γ : E) + cc (γ : E)) τ =
      2 * ((X.m * X.chiOrd la : ℕ) : ℝ) * ∑ τ : X.Ψ, ν τ * (τ.1 (γ : E)).re := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [per, map_add (f := _), emb_cc', Complex.add_re, Complex.conj_re]
    ring
  rw [h1] at hk
  simp only [Complex.re_sum, Complex.re_ofReal_mul]
  rw [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast, ← hk]
  field_simp
  norm_num

theorem fj_transv (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    (ν : X.Ψ → ℝ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {s : E} (hs : cc s = s) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    (hγm : (γ : Matrix (Fin r) (Fin r) E) = transvMat X.Gm ξ (s * X.κ0)) (hχ : X.χ la γ = 1) :
    X.fj la ξ ν P (X.flow ξ (fun τ => (((τ.1 s).re : ℝ) : ℂ)) x) = X.fj la ξ ν P x := by
  have hact : ∀ y, lact γ y = X.flow ξ (fun τ => (((τ.1 s).re : ℝ) : ℂ)) y := by
    intro y
    funext τ
    simp only [lact, Data.flow]
    rw [hγm, transvMat_map X ξ τ _ _ ?_]
    rw [map_mul, emb_kappa, ← emb_real hs]
    ring
  have key : ∀ t : X.Ψ → ℝ, P (X.flow ξ (fun τ => (t τ : ℂ)) (X.flow ξ (fun τ => (((τ.1 s).re : ℝ) : ℂ)) x)) =
      P (X.flow ξ (fun τ => (t τ : ℂ)) x) := by
    intro t
    rw [flow_flow X hξ.2.1, add_comm, ← flow_flow X hξ.2.1, ← hact]
    exact (hP.2.2 γ hγ _ (flow_real_mem_dom X hξ.2.1 t x hx)).trans (by rw [hχ, one_mul]; rfl)
  unfold Data.fj
  simp only [key]

end GlobalTheory.FjFreq

namespace GlobalTheory.FjFreq

open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters

theorem freq_real_nonneg_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsBddSec la P → ∀ ξ, X.IsIso ξ → ∀ (ν : X.Ψ → ℝ), ∀ x ∈ X.dom, X.fj la ξ ν P x ≠ 0 → ∃ ν₀ : E, cc ν₀ = ν₀ ∧ (∀ τ : X.Ψ, ν τ = (τ.1 ν₀).re) ∧ (∀ τ : E →+* ℂ, 0 ≤ (τ ν₀).re) ∧ ∀ s : E, cc s = s → (∃ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = transvMat X.Gm ξ (s * X.κ0) ∧ X.χ la γ = 1) → ∃ m : ℤ, Algebra.trace ℚ E (ν₀ * s) = m := by
  intro E _ _ _ r X la P hP ξ hξ ν x hx hne
  have hν : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k := by
    by_contra h
    exact hne (by unfold Data.fj; rw [if_neg h])
  obtain ⟨ω, hω⟩ := exists_emb_of_freq X la ν hν
  have hre : ∀ τ : X.Ψ, ν τ = (τ.1 ω).re := fun τ => by rw [← hω, Complex.ofReal_re]
  obtain ⟨C, hC⟩ := hP.2
  have hnn := (moderateCoefficientPositivity_holds r X la P C 0 hP.1 (fun y hy => by simpa using hC y hy)).1 ξ hξ ν x hx hne
  refine ⟨ω, ?_, hre, ?_, ?_⟩
  · obtain ⟨τ⟩ := X.nonempty_Psi
    apply τ.1.injective
    rw [emb_cc', ← hω, Complex.conj_ofReal]
  · intro σ
    by_cases hσ : σ ∈ X.Ψ
    · exact (hre ⟨σ, hσ⟩) ▸ hnn ⟨σ, hσ⟩
    · have hc : ComplexEmbedding.conjugate σ ∈ X.Ψ := (X.conj_mem_iff σ).2 hσ
      have h1 := hnn ⟨_, hc⟩
      rw [hre] at h1
      simpa [ComplexEmbedding.conjugate_coe_eq] using h1
  · rintro s hs ⟨γ, hγ, hγm, hχ⟩
    have h1 := X.fj_flow_real la ξ hξ ν P hP.1 hP.2 x hx (fun τ => (τ.1 s).re)
    rw [fj_transv X la P hP.1 hξ ν hx hs hγ hγm hχ] at h1
    have h2 : Complex.exp (4 * Real.pi * Complex.I * ∑ τ, (ν τ : ℂ) * (((τ.1 s).re : ℝ) : ℂ)) = 1 :=
      mul_right_cancel₀ hne (by rw [one_mul]; exact h1.symm)
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2
    refine ⟨n, ?_⟩
    have h3 : ((Algebra.trace ℚ E (ω * s) : ℚ) : ℂ) = 2 * ∑ τ, (ν τ : ℂ) * (((τ.1 s).re : ℝ) : ℂ) := by
      rw [X.trace_eq_Psi, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [map_mul, ← hω, emb_real hs, Complex.ofReal_re, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
      ring
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    have h4 : ((Algebra.trace ℚ E (ω * s) : ℚ) : ℂ) = (n : ℂ) := by
      apply mul_right_cancel₀ hpi
      rw [h3, ← hn]
      ring
    exact_mod_cast h4

end GlobalTheory.FjFreq
end
