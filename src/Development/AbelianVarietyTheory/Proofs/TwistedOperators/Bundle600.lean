module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle589
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle379
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle874
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle198
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle490
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmEqSumLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle508
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle583
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle006
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle342
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSeriesSchwartzBruhatContinuousSchrodinger
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle709
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
import Mathlib.RingTheory.PiTensorProduct
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

open Finset GlobalTheory.FunObj.SqNum

namespace GlobalTheory.RowClaim

theorem sqRatio_mem_grid {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T)
    (W : G.Weil) (S : GridChoice W Set.univ) (ρ : RealMatch W) (c : Fin D.R.m → Fin D.R.m → T → ℂ)
    (hN : NumbersIn D.what₂.embLL S μ₀)
    (hC : ∀ i j t, SquareNonzero W S.B ρ t i j ∧ c i j t ≠ 0) (hK : ∀ i j t, IsSquareConst W S.B ρ t i j (c i j t))
    (hLN : ∀ i j : Fin D.R.m, (∀ t, ∃ Λ, GlobalTheory.CMVal.IsHeckeL (SqNum.nuH G t i j) Λ ∧
      ∀ s : ℤ, 1 - (GlobalTheory.SqTop.e0 D i j : ℤ) ≤ s → s ≤ halfRank D i j → Λ s ≠ 0))
    (hTX : ∀ i j : Fin D.R.m, ∃ (A A' WW : HSp D) (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X ∧ X.IsConst W.ψ W.θ c0)
    (hTW : ∀ (i j : Fin D.R.m) (t : T) (c c₀ : ℂ) (A A' WW : HSp D) (X : Tri T A A' WW)
      (c0 : T → ℂ) (Λ Λ₀ : ℂ → ℂ), SquareNonzero W S.B ρ t i j → IsSquareConst W S.B ρ t i j c → SquareNonzero W S.B ρ μ₀ i j →
      IsSquareConst W S.B ρ μ₀ i j c₀ → IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 → GlobalTheory.CMVal.IsHeckeL (SqNum.nuH G t i j) Λ →
      GlobalTheory.CMVal.IsHeckeL (SqNum.nuH G μ₀ i j) Λ₀ → ∃ u : Fin (GlobalTheory.SqTop.pp D j + GlobalTheory.SqTop.qq D j) → ℂ,
        (∀ k, GlobalTheory.Square.StepRatio D.what₂.embLL (GlobalTheory.SqTop.Qn G t) G.pl.S0 (SqNum.condExp G.pl)
          (fun v => Ideal.absNorm v.asIdeal) (u k) 1) ∧
        ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (GlobalTheory.SqTop.Qn G t) ζ ∧
          c / c₀ * ∏ k ∈ range (GlobalTheory.SqTop.qq D j), Λ (GlobalTheory.SqTop.eTop D i j + k + 1 : ℕ) / Λ₀ (GlobalTheory.SqTop.eTop D i j + k + 1 : ℕ) =
            D.what₂.embLL ζ * (∏ k, u k) * (c0 t / c0 μ₀) *
              ∏ k ∈ range (GlobalTheory.SqTop.pp D j), Λ (GlobalTheory.SqTop.eTop D i j + GlobalTheory.SqTop.qq D j - k : ℕ) /
                Λ₀ (GlobalTheory.SqTop.eTop D i j + GlobalTheory.SqTop.qq D j - k : ℕ))
    (hBF : ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X →
      ∃ lam : T → ℂ, GlobalTheory.ConstRatio.Factor X W.ψ W.θ lam)
    (i j : Fin D.R.m) (t : T) : c i j t / c i j μ₀ ∈ Set.range D.what₂.embLL := by
  have hF : ∀ z : ℂ, z ∈ Set.range D.what₂.embLL ↔ z ∈ D.what₂.embLL.fieldRange := fun z => Iff.rfl

  obtain ⟨A₀, A₀', WW₀, X₀, -, hX₀, -⟩ := hTX i j
  obtain ⟨A, A', WW, X, hX, hS⟩ := hN.bottom i j ⟨A₀, A₀', WW₀, X₀, hX₀⟩
  obtain ⟨lam, hlam⟩ := hBF i j A A' WW X hX
  have hI := hX.is
  have hi' : ∀ t P g, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P g) X.fd' X.m' := fun t P g =>
    (GlobalTheory.T.thetaIntegral_definiteSource_converges_continuous_invariant D W.ψ false A' WW _ _ (X.ω' t) X.m' X.fd' _ (hI.weil' t) (GlobalTheory.ConstRatio.posDef_of_std hX.std')
      hI.meas'.1 hI.meas'.2 (GlobalTheory.Chain.InnerSteps.theta_pureTensorO hI.isVac.1 hI.isVac.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B
        (GlobalTheory.ConstRatio.theta_f hI t).2 P)).1 g
  have hr := hS.rationalSums (fun t P g => hlam.2.choose_spec.choose_spec.choose_spec.choose_spec.2.2.1 t P g) hi'
  have hrat := GlobalTheory.ConstRatio.ratIn_of_definite hI (GlobalTheory.ConstRatio.posDef_of_std hX.std) (GlobalTheory.ConstRatio.posDef_of_std hX.std')
    (GlobalTheory.ConstRatio.posDef_of_std hX.stdW) hlam hr μ₀
  haveI : Nonempty T := ⟨μ₀⟩
  have hcst : X.IsConst W.ψ W.θ lam := hlam.isConst

  obtain ⟨Λ, hΛ, hΛne⟩ := hLN i j t
  obtain ⟨Λ₀, hΛ₀, hΛ₀ne⟩ := hLN i j μ₀
  obtain ⟨u, hu, ζ, -, heq⟩ := hTW i j t (c i j t) (c i j μ₀) A A' WW X lam Λ Λ₀ (hC i j t).1 (hK i j t) (hC i j μ₀).1
    (hK i j μ₀) hX hcst hΛ hΛ₀
  rw [hF]
  obtain ⟨hn1, -, -, hn4, -, -, -, hn8, hn9⟩ := GlobalTheory.SqTop.Model.tower_numbers (D := D) i j
  have hne : ∀ L : ℂ → ℂ, (∀ s : ℤ, 1 - (GlobalTheory.SqTop.e0 D i j : ℤ) ≤ s → s ≤ halfRank D i j → L s ≠ 0) →
      ∀ n : ℕ, 1 ≤ n → n ≤ halfRank D i j → L (n : ℂ) ≠ 0 := fun L h n h1 h2 => by
    have := h n (by omega) (by exact_mod_cast h2)
    simpa using this
  have hs : ∀ n : ℕ, 1 ≤ n → n ≤ halfRank D i j →
      Λ (n : ℂ) / Λ₀ (n : ℂ) ∈ D.what₂.embLL.fieldRange ∧ Λ (n : ℂ) / Λ₀ (n : ℂ) ≠ 0 := fun n h1 h2 =>
    ⟨(hF _).1 (hN.ratios i j t Λ Λ₀ hΛ hΛ₀ n h1 (by omega) (hne Λ₀ hΛ₀ne n h1 h2)),
      div_ne_zero (hne Λ hΛne n h1 h2) (hne Λ₀ hΛ₀ne n h1 h2)⟩
  have hP1 : ∀ k ∈ range (GlobalTheory.SqTop.qq D j), Λ ((GlobalTheory.SqTop.eTop D i j + k + 1 : ℕ) : ℂ) /
      Λ₀ ((GlobalTheory.SqTop.eTop D i j + k + 1 : ℕ) : ℂ) ∈ D.what₂.embLL.fieldRange ∧
      Λ ((GlobalTheory.SqTop.eTop D i j + k + 1 : ℕ) : ℂ) / Λ₀ ((GlobalTheory.SqTop.eTop D i j + k + 1 : ℕ) : ℂ) ≠ 0 := fun k hk =>
    hs _ (by omega) (by have := mem_range.1 hk; omega)
  have hP2 : ∀ k ∈ range (GlobalTheory.SqTop.pp D j), Λ ((GlobalTheory.SqTop.eTop D i j + GlobalTheory.SqTop.qq D j - k : ℕ) : ℂ) /
      Λ₀ ((GlobalTheory.SqTop.eTop D i j + GlobalTheory.SqTop.qq D j - k : ℕ) : ℂ) ∈ D.what₂.embLL.fieldRange := fun k hk =>
    (hs _ (by have := mem_range.1 hk; omega) (by omega)).1
  have hU : (∏ k, u k) ∈ D.what₂.embLL.fieldRange := prod_mem fun k _ => by
    obtain ⟨b, g, g', -, -, h⟩ := hu k
    rw [h, mul_one]
    exact RingHom.mem_fieldRange.2 ⟨_, rfl⟩
  have hl : lam t / lam μ₀ ∈ D.what₂.embLL.fieldRange := by
    obtain ⟨-, y, hy⟩ := hrat t
    exact RingHom.mem_fieldRange.2 ⟨_, hy⟩
  rw [eq_div_of_mul_eq (prod_ne_zero_iff.2 fun k hk => (hP1 k hk).2) heq]
  exact div_mem (mul_mem (mul_mem (mul_mem (RingHom.mem_fieldRange.2 ⟨ζ, rfl⟩) hU) hl) (prod_mem hP2))
    (prod_mem fun k hk => (hP1 k hk).1)


end GlobalTheory.RowClaim

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CMNorm

theorem sqrt_absNorm_le_prod_tauE : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (u : 𝓞 D.host.E), u ∈ 𝔪 → u ≠ 0 → Real.sqrt (Ideal.absNorm 𝔪) ≤ ∏ τ, ‖tauE D τ (u : D.host.E)‖ := by
  intro D 𝔪 u hu hu0
  have hnorm : ∏ τ, ‖tauE D τ (u : D.host.E)‖ ^ 2 = |((Algebra.norm ℚ (u : D.host.E) : ℚ) : ℝ)| := by
    rw [← Rat.cast_abs, ← NumberField.InfinitePlace.prod_eq_abs_norm]
    refine (Fintype.prod_bijective _ (GlobalTheory.LevelSeries.mk_tauE_bij D) _ _ (fun τ => ?_))
    rw [NumberField.InfinitePlace.mult, if_neg (GlobalTheory.LevelSeries.mk_tauE_complex D τ)]
    rfl
  have hspan : Ideal.span {u} ≤ 𝔪 := (Ideal.span_singleton_le_iff_mem _).2 hu
  have hne : Ideal.absNorm (Ideal.span {u}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hu0
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hspan
  have hle : Ideal.absNorm 𝔪 ≤ Ideal.absNorm (Ideal.span {u}) := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
  have habs : ((Ideal.absNorm (Ideal.span {u}) : ℕ) : ℝ) = |((Algebra.norm ℚ (u : D.host.E) : ℚ) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton]
    rw [← Algebra.coe_norm_int]
    push_cast
    simp
  have hle' : ((Ideal.absNorm 𝔪 : ℕ) : ℝ) ≤ (∏ τ, ‖tauE D τ (u : D.host.E)‖) ^ 2 := by
    rw [← Finset.prod_pow, hnorm, ← habs]; exact_mod_cast hle
  calc Real.sqrt (Ideal.absNorm 𝔪) ≤ Real.sqrt ((∏ τ, ‖tauE D τ (u : D.host.E)‖) ^ 2) := Real.sqrt_le_sqrt hle'
    _ = ∏ τ, ‖tauE D τ (u : D.host.E)‖ := Real.sqrt_sq (Finset.prod_nonneg fun τ _ => norm_nonneg _)

end GlobalTheory.CMNorm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.HalfCosetCount



theorem halfCoset_reps_card : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), (∀ y ∈ R, IsHalf (cA D e) y ∧ k • y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∀ y : WO S T, IsHalf (cA D e) y → k • y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃! r, r ∈ R ∧ y - r ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ R.card ∣ k ^ (D.R.f * S.rank * T.rank) := by
  intro D S T ΛS ΛT hS hT e P he k hk
  classical
  obtain ⟨⟨es, hes, rfl⟩, hec⟩ := he
  set Λ := (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ
  set c := cA D (∑ Q ∈ P, es Q) with hcdef
  have hc : c = ∑ Q ∈ P, cA D (es Q) := map_sum _ _ _
  have hes_orth : ∀ Q ∈ P, ∀ Q' ∈ P, Q ≠ Q' → es Q * es Q' = 0 := fun Q hQ Q' hQ' hne =>
    (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (hes Q hQ).1 (hes Q' hQ').1).resolve_left fun h => hne
      (HeightOneSpectrum.ext (Ideal.ext fun x => by
        by_cases hx : x = 0
        · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
        · rw [(hes Q hQ).2 x hx, (hes Q' hQ').2 x hx, h]))
  have hidem : ∀ Q ∈ P, cA D (es Q) * cA D (es Q) = cA D (es Q) := fun Q hQ => by
    rw [← map_mul, (hes Q hQ).1.1]
  have horth : ∀ Q ∈ P, ∀ Q' ∈ P, Q ≠ Q' → cA D (es Q) * cA D (es Q') = 0 := fun Q hQ Q' hQ' hne => by
    rw [← map_mul, hes_orth Q hQ Q' hQ' hne, map_zero]
  have hstab : ∀ Q ∈ P, ∀ u ∈ Λ, cA D (es Q) • u ∈ Λ := fun Q hQ u hu =>
    GlobalTheory.PlaceModelSum.idem_smul_latO (hidem Q hQ) hu
  have hch : ∀ Q : ↥P, ∃ w : HeightOneSpectrum (𝓞 D.host.F), ∃ π : AE D →+* Fv D.host.F w,
      GlobalTheory.SplitHecke.Chart (cA D (es Q)) w π := fun Q =>
    GlobalTheory.SplitChart.exists_chart _ (GlobalTheory.PlaceModelSum.isSplitIdem_cA (hes Q Q.2).1)
  choose v π hπ using hch
  have hvinj : Function.Injective v :=
    GlobalTheory.T.conjugate_idempotent_chart_places_injective _ P es (fun Q hQ => hes Q hQ) rfl hec v fun Q => ⟨π Q, hπ Q⟩

  have hcount : (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex
      (Λ ⊓ GlobalTheory.PlaceModel.half S T c) =
      (∏ Q : ↥P, Nat.card ((v Q).adicCompletionIntegers D.host.F ⧸
        Ideal.span {(k : (v Q).adicCompletionIntegers D.host.F)})) ^ (S.rank * T.rank) := by
    rw [hc, GlobalTheory.T.relIndex_nsmul_half_orthogonal_idempotent_sum S T Λ P (fun Q => cA D (es Q)) hidem horth hstab k, ← Finset.prod_pow,
      ← Finset.prod_attach P]
    refine Finset.prod_congr rfl fun Q _ => ?_
    exact GlobalTheory.T.relIndex_nsmul_idempotentHalf_at_splitPlace S T ΛS ΛT
      (by first | exact GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S ΛS hS
                | exact (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S ΛS hS).toIsLattice)
      (by first | exact GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T ΛT hT
                | exact (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T ΛT hT).toIsLattice) _ (v Q) (π Q)
      (GlobalTheory.PlaceModelSum.isSplitIdem_cA (hes Q Q.2).1) (hπ Q) k hk
  have hdvd : (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex
      (Λ ⊓ GlobalTheory.PlaceModel.half S T c) ∣ k ^ (D.R.f * S.rank * T.rank) := by
    have h1 := GlobalTheory.T.prod_card_adicCompletionIntegers_quot_dvd_pow_finrank D.host.F (Finset.univ.image v) k hk
    rw [Finset.prod_image fun x _ y _ h => hvinj h, Formalism.MainNotions.J.finrank_F_eq] at h1
    rw [hcount, mul_assoc, pow_mul k D.R.f]
    exact pow_dvd_pow_of_dvd h1 _

  set M := Λ ⊓ GlobalTheory.PlaceModel.half S T c with hM
  set Y := Λ.comap (nsmulAddMonoidHom k) ⊓ GlobalTheory.PlaceModel.half S T c with hY
  have hinj : Function.Injective (nsmulAddMonoidHom k : WO S T →+ WO S T) := fun x y h => nsmul_cancel_mx hk h
  have hu : IsUnit (k : AE D) := by
    rw [← map_natCast (algebraMap D.host.F (AE D))]
    exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hk.ne')).map _
  have hYM : Y.map (nsmulAddMonoidHom k) = M := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hy1, hy2⟩ := AddSubgroup.mem_inf.1 hy
      exact AddSubgroup.mem_inf.2 ⟨hy1, (GlobalTheory.PlaceModel.half S T c).nsmul_mem hy2 k⟩
    · intro hx
      obtain ⟨hx1, hx2⟩ := AddSubgroup.mem_inf.1 hx
      have key : k • ((↑hu.unit⁻¹ : AE D) • x) = x := by
        rw [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, IsUnit.mul_val_inv, one_smul]
      refine ⟨(↑hu.unit⁻¹ : AE D) • x, AddSubgroup.mem_inf.2 ⟨?_, ?_⟩, key⟩
      · rw [AddSubgroup.mem_comap]
        change k • _ ∈ Λ
        rw [key]; exact hx1
      · refine (GlobalTheory.PlaceModel.mem_half S T).2 ?_
        have hx3 : c • x = x := (GlobalTheory.PlaceModel.mem_half S T).1 hx2
        rw [smul_comm c (↑hu.unit⁻¹ : AE D) x, hx3]
  have hMY : M.relIndex Y = (M.map (nsmulAddMonoidHom k)).relIndex M := by
    rw [← AddSubgroup.relIndex_map_map_of_injective (f := (nsmulAddMonoidHom k : WO S T →+ WO S T)) M Y hinj, hYM]
  have hne : (M.addSubgroupOf Y).index ≠ 0 := by
    change M.relIndex Y ≠ 0
    rw [hMY]
    exact fun h => (pow_pos hk _).ne' (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  haveI : Finite (↥Y ⧸ M.addSubgroupOf Y) := AddSubgroup.index_ne_zero_iff_finite.1 hne
  obtain ⟨R, hRc, hRY, hRu⟩ := GlobalTheory.SplitLinear.exists_reps M Y
  refine ⟨R, fun y hy => ?_, fun y hy1 hy2 => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 (hRY y hy)
    exact ⟨(GlobalTheory.PlaceModel.isHalf_iff S T).2 h2, h1⟩
  · have hyY : y ∈ Y := AddSubgroup.mem_inf.2 ⟨hy2, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy1⟩
    obtain ⟨r, ⟨hr, hyr⟩, huniq⟩ := hRu y hyY
    refine ⟨r, ⟨hr, (AddSubgroup.mem_inf.1 hyr).1⟩, fun r' hr' => huniq r' ⟨hr'.1, AddSubgroup.mem_inf.2 ⟨hr'.2, ?_⟩⟩⟩
    exact sub_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hy1) (AddSubgroup.mem_inf.1 (hRY r' hr'.1)).2
  · rw [hRc, hMY]
    exact hdvd

end GlobalTheory.HalfCosetCount
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

open scoped Matrix

namespace GlobalTheory.RealColAct

variable {D : D7}

theorem gramAt_of_gram_one {V : HSp D} (hV : HSpace.gram V = 1) (τ : D.what₂.Tau) : gramAt D V τ = 1 := by
  unfold gramAt
  rw [hV]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem compAt_mem_unitary {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (hV : HSpace.gram V = 1) (g : GA D V)
    (τ : D.what₂.Tau) : compAt θ τ (Formalism.L2.Theta.mt V g) ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := by
  have h := GlobalTheory.StdUnn.CartanMove.compAt_isom hθ V g τ
  rw [gramAt_of_gram_one hV, Matrix.mul_one] at h
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  exact h

theorem transpose_mem_unitary {n : ℕ} {K : Matrix (Fin n) (Fin n) ℂ} (hK : K ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Kᵀ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have h2 : K * star K = 1 := Matrix.mem_unitaryGroup_iff.1 hK
  rw [Matrix.mem_unitaryGroup_iff']
  have e : star Kᵀ = (star K)ᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]; rfl
  rw [e, ← Matrix.transpose_mul, h2, Matrix.transpose_one]

def realCol (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (hV : HSpace.gram V = 1) :
    GinfC V →* (D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ) where
  toFun g τ := ⟨(compAt θ τ (Formalism.L2.Theta.mt V ((g : GA D V)⁻¹)))ᵀ,
    transpose_mem_unitary (compAt_mem_unitary hθ hV _ τ)⟩
  map_one' := by
    funext τ
    apply Subtype.ext
    simp only [OneMemClass.coe_one, inv_one, GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.transpose_one, Pi.one_apply]
  map_mul' g h := by
    funext τ
    apply Subtype.ext
    simp only [Subgroup.coe_mul, mul_inv_rev, GlobalTheory.StdUnn.CartanMove.compAt_mt_mul, Matrix.transpose_mul, Pi.mul_apply]
    rfl

theorem realCol_apply (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (hV : HSpace.gram V = 1) (g : GinfC V) (τ : D.what₂.Tau) :
    (realCol θ hθ V hV g τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) = (compAt θ τ (Formalism.L2.Theta.mt V ((g : GA D V)⁻¹)))ᵀ := rfl

end GlobalTheory.RealColAct
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.CharSumHalf

open GlobalTheory.Core.Rk.ThetaOf GlobalTheory.DownLift.GenQuot



theorem charSum_detects_multiple : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D) (k : ℕ) (R : Finset (WO S T)), 0 < k → (∀ u ∈ Λ, IsHalf e u → ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T u y) = 1) → (∀ x : WO S T, IsHalf e x → (∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) → x ∈ Λ) → (∀ y ∈ R, IsHalf (cA D e) y ∧ k • y ∈ Λ) → (∀ y : WO S T, IsHalf (cA D e) y → k • y ∈ Λ → ∃! r, r ∈ R ∧ y - r ∈ Λ) → ∀ t ∈ Λ, IsHalf e t → ((∃ u ∈ Λ, IsHalf e u ∧ t = k • u) → ∑ r ∈ R, ψ (symplO S T t r) = R.card) ∧ ((¬ ∃ u ∈ Λ, IsHalf e u ∧ t = k • u) → ∑ r ∈ R, ψ (symplO S T t r) = 0) := by
  intro D ψ S T Λ e k R hk hpair hann hR hU t htΛ hte
  classical
  have half_sub : ∀ {c : AE D} {x y : WO S T}, IsHalf c x → IsHalf c y → IsHalf c (x - y) :=
    fun hx hy i j => by simp only [Matrix.sub_apply, mul_sub, hx i j, hy i j]
  have half_add : ∀ {c : AE D} {x y : WO S T}, IsHalf c x → IsHalf c y → IsHalf c (x + y) :=
    fun hx hy i j => by simp only [Matrix.add_apply, mul_add, hx i j, hy i j]
  have half_nsmul : ∀ {c : AE D} {x : WO S T} (n : ℕ), IsHalf c x → IsHalf c (n • x) :=
    fun n hx i j => by rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hx i j]
  have half_smul : ∀ {c : AE D} {x : WO S T} (a : AE D), IsHalf c x → IsHalf c (a • x) :=
    fun a hx i j => by simp only [Matrix.smul_apply, smul_eq_mul]; rw [mul_left_comm, hx i j]
  have pair_add : ∀ x y y' : WO S T,
      ψ (symplO S T x (y + y')) = ψ (symplO S T x y) * ψ (symplO S T x y') := by
    intro x y y'; rw [symplO_add_right, AddChar.map_add_eq_mul]
  constructor
  · rintro ⟨u, huΛ, hue, rfl⟩
    have h1 : ∀ r ∈ R, ψ (symplO S T (k • u) r) = 1 := fun r hr => by
      rw [symplO_nsmul_swap]
      exact hpair u huΛ hue _ (hR r hr).2 (half_nsmul k (hR r hr).1)
    rw [Finset.sum_congr rfl h1]; simp
  · intro hnot
    have hex : ∃ r₀ ∈ R, ψ (symplO S T t r₀) ≠ 1 := by
      by_contra hall
      push_neg at hall
      apply hnot
      set a : AE D := algebraMap D.host.F (AE D) ((k : D.host.F)⁻¹) with ha
      have hka : k • a = 1 := by
        rw [ha, ← map_nsmul, nsmul_eq_mul, mul_inv_cancel₀ (by exact_mod_cast hk.ne'), map_one]
      have hkx : ∀ x : WO S T, k • (a • x) = x := fun x => by
        rw [← smul_assoc, hka, one_smul]
      refine ⟨a • t, ?_, half_smul a hte, (hkx t).symm⟩
      apply hann _ (half_smul a hte)
      intro y hyΛ hyc
      obtain ⟨r, ⟨hrR, hdiff⟩, -⟩ := hU (a • y) (half_smul a hyc) (by rw [hkx]; exact hyΛ)
      have hsw : symplO S T (a • t) y = symplO S T t (a • y) := by
        conv_lhs => rw [← hkx y]
        rw [← symplO_nsmul_swap, hkx]
      rw [hsw, show a • y = (a • y - r) + r by abel, pair_add, hall r hrR, mul_one]
      exact hpair t htΛ hte _ hdiff (half_sub (half_smul a hyc) (hR r hrR).1)
    obtain ⟨r₀, hr₀R, hr₀⟩ := hex
    obtain ⟨rep, rep_spec⟩ : ∃ rep : WO S T → WO S T,
        ∀ y, IsHalf (cA D e) y → k • y ∈ Λ → rep y ∈ R ∧ y - rep y ∈ Λ := by
      refine ⟨fun y => if h : IsHalf (cA D e) y ∧ k • y ∈ Λ then (hU y h.1 h.2).exists.choose else 0, ?_⟩
      intro y h1 h2
      dsimp only
      rw [dite_eq_left (And.intro h1 h2)]
      exact (hU y h1 h2).exists.choose_spec
    have rep_eq : ∀ y r, IsHalf (cA D e) y → k • y ∈ Λ → r ∈ R → y - r ∈ Λ → rep y = r :=
      fun y r h1 h2 hr hd => (hU y h1 h2).unique (rep_spec y h1 h2) ⟨hr, hd⟩
    have hadd : ∀ r ∈ R, ∀ s ∈ R, IsHalf (cA D e) (r + s) ∧ k • (r + s) ∈ Λ := fun r hr s hs =>
      ⟨half_add (hR r hr).1 (hR s hs).1, by rw [nsmul_add]; exact Λ.add_mem (hR r hr).2 (hR s hs).2⟩
    have hsub : ∀ r ∈ R, ∀ s ∈ R, IsHalf (cA D e) (r - s) ∧ k • (r - s) ∈ Λ := fun r hr s hs =>
      ⟨half_sub (hR r hr).1 (hR s hs).1, by rw [nsmul_sub]; exact Λ.sub_mem (hR r hr).2 (hR s hs).2⟩
    have key : ∑ r ∈ R, ψ (symplO S T t r₀) * ψ (symplO S T t r) = ∑ r ∈ R, ψ (symplO S T t r) := by
      apply Finset.sum_nbij' (fun r => rep (r + r₀)) (fun r => rep (r - r₀))
      · intro r hr; exact (rep_spec _ (hadd r hr r₀ hr₀R).1 (hadd r hr r₀ hr₀R).2).1
      · intro r hr; exact (rep_spec _ (hsub r hr r₀ hr₀R).1 (hsub r hr r₀ hr₀R).2).1
      · intro r hr
        obtain ⟨h1, h2⟩ := rep_spec _ (hadd r hr r₀ hr₀R).1 (hadd r hr r₀ hr₀R).2
        have hs := hsub _ h1 r₀ hr₀R
        refine rep_eq _ r hs.1 hs.2 hr ?_
        have : rep (r + r₀) - r₀ - r = -((r + r₀) - rep (r + r₀)) := by abel
        rw [this]; exact Λ.neg_mem h2
      · intro r hr
        obtain ⟨h1, h2⟩ := rep_spec _ (hsub r hr r₀ hr₀R).1 (hsub r hr r₀ hr₀R).2
        have hs := hadd _ h1 r₀ hr₀R
        refine rep_eq _ r hs.1 hs.2 hr ?_
        have : rep (r - r₀) + r₀ - r = -((r - r₀) - rep (r - r₀)) := by abel
        rw [this]; exact Λ.neg_mem h2
      · intro r hr
        obtain ⟨h1, h2⟩ := rep_spec _ (hadd r hr r₀ hr₀R).1 (hadd r hr r₀ hr₀R).2
        have hrep : rep (r + r₀) = (r + r₀) + -((r + r₀) - rep (r + r₀)) := by abel
        have hhalf : IsHalf (cA D e) (-((r + r₀) - rep (r + r₀))) := by
          have := half_sub (hadd r hr r₀ hr₀R).1 (hR _ h1).1
          intro i j; simp only [Matrix.neg_apply, mul_neg, this i j]
        show _ = ψ (symplO S T t (rep (r + r₀)))
        rw [hrep, pair_add, pair_add, hpair t htΛ hte _ (Λ.neg_mem h2) hhalf, mul_one, mul_comm]
    rw [← Finset.mul_sum] at key
    have h0 : (ψ (symplO S T t r₀) - 1) * ∑ r ∈ R, ψ (symplO S T t r) = 0 := by
      rw [sub_mul, key, one_mul, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hr₀)

end GlobalTheory.CharSumHalf
end
