module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle043
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle042
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle044
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle031
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle036
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreIsotropicPointsInjectiveRoots
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibrePrincipalBundleSignEq
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ReadsExistsUniqueTheta
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle028
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle043
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelOneThetaEqSmulOfSelfDualLattice
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PolyDerivVanishesOfTranslationInvariance
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle066
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumEqZeroOfRankZero
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsHarmonicAndMemMinorSpan
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle065
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle042
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaCharacteristicsIffTestFunctionThetaSeries
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle045
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RowsCongrOfTrivialAtLevel
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle014
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem reads_isUUOver_isVtOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (N : ℕ), Odd N → ∀ θ, A.Reads 1 y.s θ → (∀ a₁ a₂ : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a₁ = (2 : ℕ) • u) → (∃ u ∈ L, (N ^ 2 : ℕ) • a₂ = (2 : ℕ) • u) → ∀ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)), IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (A.ex (pv X idx x a₁)) (A.ex (pv X idx x a₂)) F → A.Reads ((N : ℤ) ^ 2) F (fun z => fock X bas idx x 1 (pv X idx x ((N : E) • a₂)) (fock X bas idx x 1 (pv X idx x ((N : E) • a₁)) θ) ((N : ℂ) • z))) ∧ ∀ a : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a = (2 : ℕ) • u) → ∀ (t : (ptO Xo y.x) ⟶ Xo.univ.t.G) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), IsVtOver Xo.univ.t.G Xo.univ.t.PP N (fun t' => t' = A.ex (pv X idx x a)) y.s t F → A.Reads ((N : ℤ) ^ 2) F (fun z => fock X bas idx x 1 (pv X idx x ((N : E) • a)) θ ((N : ℂ) • z)) := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL N hN θ hθ
  have hpv : ∀ (n : ℕ) (a : Fin r → E), pv X idx x ((n : E) • a) = (n : ℂ) • pv X idx x a := by
    intro n a
    rw [(hx_laws E r X g bas idx 0 hs ⟨0, rfl⟩ x hx).2.2.2.2.1]
    funext j
    simp
  have hfk : ∀ (φ : (Fin g → ℂ) → ℂ) (a : Fin r → E),
      Dict.fock X bas idx x (N ^ 2) (pv X idx x a) (fun z => φ ((N : ℂ) • z)) =
        fun z => Dict.fock X bas idx x 1 (pv X idx x ((N : E) • a)) φ ((N : ℂ) • z) := by
    intro φ a
    rw [hpv]
    exact (fock_laws E r X g bas idx 0 hs ⟨0, rfl⟩ x hx 1 φ).2.2.1 N _
  obtain ⟨Φ, he, -, hlat, -, -, hrd, hf⟩ := GlobalTheory.Dict.AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  have hχ : ∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1 := fun a ha =>
    (GlobalTheory.AnVal.chi_eq_sign E H Dw l Xo c y g _ e Φ a ha).1
  have htw : ∀ α₀ α s₁, α₀.IsGen → IsNormMul Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig N α₀ →
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ α
        (LB.pullGen Xo.univ.t.PP.L _ _ α₀ (snd (ptO Xo y.x) Xo.univ.t.G).left) →
      IsTwistPull Xo.univ.t.G Xo.univ.t.PP.L (mulT Xo.univ.t.G (ptO Xo y.x) N)
        (snd (ptO Xo y.x) Xo.univ.t.G ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α y.s s₁ →
      A.Reads ((N : ℤ) ^ 2) s₁ (fun z => θ ((N : ℂ) • z)) := by
    intro α₀ α s₁ hg hn hc ht
    exact (hrd _ _ _).1
      (GlobalTheory.T.normalisedPullbackMulN_reads_theta _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr N α₀ α y.s s₁ θ hg hn hc ht ((hrd _ _ _).2 hθ))
  have hsy : ∀ a : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a = (2 : ℕ) • u) →
      ∀ U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x),
      SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) (A.ex (pv X idx x a)) U →
      ∀ (s s' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (φ : (Fin g → ℂ) → ℂ),
      IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) U s s' →
      A.Reads ((N : ℤ) ^ 2) s (fun z => φ ((N : ℂ) • z)) →
      A.Reads ((N : ℤ) ^ 2) s'
        (fun z => Dict.fock X bas idx x 1 (pv X idx x ((N : E) • a)) φ ((N : ℂ) • z)) := by
    rintro a ⟨u, hu, hau⟩ U hU s s' φ hA hs'
    have h2 : ((N ^ 2 : ℕ) : ℂ) • pv X idx x a = (2 : ℂ) • pv X idx x u := by
      have h3 := hpv 2 u
      rw [← hpv, Nat.cast_smul_eq_nsmul, hau, ← Nat.cast_smul_eq_nsmul E, h3]
      norm_num
    rw [← he] at hU
    have h4 := GlobalTheory.T.symmetric_lift_odd_order_acts_as_translation _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr hχ ((N : ℤ) ^ 2) (N ^ 2) U
      (pv X idx x a) (pv X idx x u) s s' _ hN.pow ((hlat _).2 ⟨u, hu, rfl⟩) h2 hU hA ((hrd _ _ _).2 hs')
    have h5 := hf (N ^ 2) (pv X idx x a) (fun z => φ ((N : ℂ) • z))
    rw [Nat.cast_pow, hfk] at h5
    rw [h5] at h4
    exact (hrd _ _ _).1 h4
  refine ⟨?_, ?_⟩
  · rintro a₁ a₂ h₁ h₂ F ⟨α₀, α, s₁, s₂, U₁, U₂, hg, hn, hc, ht, hU₁, hA₁, hU₂, hA₂⟩
    exact hsy a₂ h₂ U₂ hU₂ s₂ F _ hA₂ (hsy a₁ h₁ U₁ hU₁ s₁ s₂ _ hA₁ (htw α₀ α s₁ hg hn hc ht))
  · rintro a h t F ⟨t', α₀, α, s₁, U, -, rfl, hg, hn, hc, ht, hU, hA⟩
    exact hsy a h U hU s₁ F _ hA (htw α₀ α s₁ hg hn hc ht)

end GlobalTheory.Dict
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.analyticFibre_isotropic_points_injective_roots : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (n N : ℕ) (Λ : Lt E n), 0 < N → (∀ (Jx : Type) (u : Jx → Matrix (Fin n) (Fin r) E), (∀ i, u i ∈ tens Λ L ∧ ∀ b, ∃ u' ∈ L, N • u i b = (2 : ℕ) • u') → (∀ i i', (∀ b, ∃ u' ∈ L, u i b - u i' b = N • u') → i = i') → (∀ i, InZh Xo (⟨Λ⟩ : GenLat E n) N (fun b => A.ex (pv X idx x ((N : E)⁻¹ • u i b)))) ∧ GeoInj Xo y.x (fun i b => A.ex (pv X idx x ((N : E)⁻¹ • u i b)))) ∧ ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → A.Marked mk → l.M ∣ N → ∀ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y → ∀ q b, A.ex (pv X idx x ((N : E)⁻¹ • Y q b)) ^ N = levPt Xo y.x (levRep (q b)) ∧ (∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (A.ex (pv X idx x ((N : E)⁻¹ • Y q b)))) ∧ ∃ u ∈ L, (N ^ 2 : ℕ) • ((N : E)⁻¹ • Y q b) = (2 : ℕ) • u := by
  first | exact @GlobalTheory.Dict.points_inZh_geoInj_roots | exact GlobalTheory.Dict.points_inZh_geoInj_roots | (intros; apply GlobalTheory.Dict.points_inZh_geoInj_roots <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem thetaSignExpEF_inv_of_selfDual_lattice {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (L : Lt E r) (hL : SelfD X L) (w : 𝓞 E) (v : Fin r → E) (hv : v ∈ L) :
    (eps1 X (w : E) v)⁻¹ = eps1 X (w : E) v := by
  have hwv : (w : E) • v ∈ L := by
    have h := L.smul_mem w hv
    rwa [← algebraMap_smul E w v] at h
  obtain ⟨k, hk⟩ := (hL.2 v).1 hv ((w : E) • v) hwv
  unfold eps1
  rw [hk, ← Complex.exp_neg, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-k, ?_⟩
  push_cast
  ring

theorem isTheta1_of_reads_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ θ, A.Reads 1 y.s θ → IsTheta1 X bas idx (H.w0 : E) x L θ := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL θ hθ
  obtain ⟨-, hall⟩ := reads_existsUnique_theta E H Dw l Xo c r g X bas idx e x L y A hs hx hL 1 y.s
  obtain ⟨hd, hper⟩ := hall θ hθ
  refine ⟨hd, fun v hv => ?_⟩
  have h := hper v hv
  rw [analyticFibre_principalBundle_sign_eq E H Dw l Xo c r g X bas idx e x L y A hs hx hL v hv, pow_one,
    thetaSignExpEF_inv_of_selfDual_lattice X L hL H.w0 v hv] at h
  exact h

end GlobalTheory.Dict
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ColHeis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

theorem hx_sum_left (x : Frame X.Ψ r) (z : Fin n → Fin g → ℂ) (w : Fin g → ℂ) :
    hx X bas idx x (∑ k, z k) w = ∑ k, hx X bas idx x (z k) w := by
  unfold hx
  rw [Matrix.mulVec_sum, sum_dotProduct]

theorem hx_sum_right (x : Frame X.Ψ r) (z : Fin g → ℂ) (w : Fin n → Fin g → ℂ) :
    hx X bas idx x z (∑ k, w k) = ∑ k, hx X bas idx x z (w k) := by
  unfold hx
  rw [Matrix.mulVec_sum, star_sum, Matrix.mulVec_sum, dotProduct_sum]

theorem hAct_eq_sum (h : Matrix (Fin n) (Fin n) E) (z : Fin n → Fin g → ℂ) (k : Fin n) :
    GlobalTheory.Dict.hAct X idx h z k = ∑ a, fun j => rowType X (idx j) (h k a) * z a j := by
  funext j
  rw [Finset.sum_apply]
  rfl

theorem hAct_add_smul (h : Matrix (Fin n) (Fin n) E) (z w : Fin n → Fin g → ℂ) (c : ℂ) (k : Fin n) :
    GlobalTheory.Dict.hAct X idx h (fun a => z a + c • w a) k =
      GlobalTheory.Dict.hAct X idx h z k + c • GlobalTheory.Dict.hAct X idx h w k := by
  funext j
  simp only [GlobalTheory.Dict.hAct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem sum_hx_hAct (x : Frame X.Ψ r)
    (hadj : ∀ (a : E) z w, hx X bas idx x (fun j => rowType X (idx j) a * z j) w =
      hx X bas idx x z (fun j => rowType X (idx j) (cc a) * w j))
    (h : Matrix (Fin n) (Fin n) E) (hh : ccT h * h = 1) (z w : Fin n → Fin g → ℂ) :
    ∑ k, hx X bas idx x (GlobalTheory.Dict.hAct X idx h z k) (GlobalTheory.Dict.hAct X idx h w k) =
      ∑ k, hx X bas idx x (z k) (w k) := by

  have key : ∀ k, hx X bas idx x (GlobalTheory.Dict.hAct X idx h z k) (GlobalTheory.Dict.hAct X idx h w k) =
      ∑ a, ∑ b, hx X bas idx x (z a) (fun j => rowType X (idx j) (cc (h k a) * h k b) * w b j) := by
    intro k
    rw [hAct_eq_sum, hAct_eq_sum, hx_sum_left]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hx_sum_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hadj]
    congr 1
    funext j
    rw [map_mul, _root_.mul_assoc]

  have hcol : ∀ a b, ∑ k, cc (h k a) * h k b = (1 : Matrix (Fin n) (Fin n) E) a b := by
    intro a b
    rw [← hh, Matrix.mul_apply]
    rfl
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  simp only [← hx_sum_right]
  congr 1
  funext j
  have hj : ∀ b, ∑ k, rowType X (idx j) (cc (h k a) * h k b) * w b j =
      rowType X (idx j) ((1 : Matrix (Fin n) (Fin n) E) a b) * w b j := by
    intro b

    rw [← Finset.sum_mul, ← map_sum, hcol]
  simp only [Finset.sum_apply, hj, Matrix.one_apply, apply_ite, map_one, map_zero, ite_mul,
    _root_.one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem pv_mul_row (x : Frame X.Ψ r)
    (hsm : ∀ (a : E) v, pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j)
    (h : Matrix (Fin n) (Fin n) E) (y : Matrix (Fin n) (Fin r) E) (k : Fin n) :
    pv X idx x ((h * y) k) = GlobalTheory.Dict.hAct X idx h (fun a => pv X idx x (y a)) k := by
  have hrow : (h * y) k = ∑ a, h k a • y a := by
    funext i
    simp [Matrix.mul_apply, Finset.sum_apply]

  have hadd : pv X idx x (∑ a, h k a • y a) = ∑ a, pv X idx x (h k a • y a) := by
    funext j
    rw [Finset.sum_apply]
    exact (congrFun (map_sum (perLin X x) (fun a => h k a • y a) Finset.univ) (idx j)).trans
      (Finset.sum_apply _ _ _)
  rw [hrow, hadd, hAct_eq_sum]
  exact Finset.sum_congr rfl fun a _ => hsm (h k a) (y a)

end GlobalTheory.Dict.ColHeis


open GlobalTheory.Dict.ColHeis in
theorem GlobalTheory.Dict.thA_heisG_hAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ φ φ' : TF n g, IsSB φ → IsSB φ' → ∀ t : ℂ, ∀ x ∈ X.dom, (∀ z, thA X bas idx φ' x (hAct X idx h z) = t * thA X bas idx φ x z) → ∀ (y : Matrix (Fin n) (Fin r) E) z, thA X bas idx (heisG X bas (h * y) φ') x (hAct X idx h z) = t * thA X bas idx (heisG X bas y φ) x z := by
  intro E _ _ _ r X g bas idx n hS hn h hh φ φ' hφ hφ' t x hxd hrel y z
  obtain ⟨-, -, -, hadj, hsm, -⟩ := GlobalTheory.T.hermitianFormAtFrame_laws E r X g bas idx n hS hn x hxd
  have HL := (heisG_laws E r X g bas idx n hS hn).2.2.2
  rw [((HL (h * y) φ' hφ').2.2.2.2) x hxd (hAct X idx h z), ((HL y φ hφ).2.2.2.2) x hxd z]

  have hP : ∀ k, per X x ((h * y) k) ∘ idx = hAct X idx h (fun a => pv X idx x (y a)) k :=
    fun k => pv_mul_row X idx x hsm h y k
  simp only [hP]

  have hT : thA X bas idx φ' x (fun k => hAct X idx h z k + hAct X idx h (fun a => pv X idx x (y a)) k) =
      t * thA X bas idx φ x (fun k => z k + per X x (y k) ∘ idx) := by
    refine Eq.trans ?_ (hrel (fun k => z k + pv X idx x (y k)))
    congr 1
    funext k
    simpa using (hAct_add_smul X idx h z (fun a => pv X idx x (y a)) 1 k).symm
  rw [hT, mul_left_comm]
  refine congrArg (t * ·) (congrArg (· * _) (congrArg cexp (congrArg (fun s : ℂ => -((Real.pi : ℂ) * s)) ?_)))

  have hE : ∀ k, hAct X idx h z k + (1 / 2 : ℂ) • hAct X idx h (fun a => pv X idx x (y a)) k =
      hAct X idx h (fun a => z a + (1 / 2 : ℂ) • pv X idx x (y a)) k :=
    fun k => (hAct_add_smul X idx h z _ _ k).symm
  simp only [hE]
  exact sum_hx_hAct X bas idx x hadj h hh (fun a => z a + (1 / 2 : ℂ) • pv X idx x (y a))
    (fun a => pv X idx x (y a))
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.levelOne_theta_eq_smul_of_selfDual_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ x ∈ X.dom, ∀ θ θ' : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx w x L θ → IsTheta1 X bas idx w x L θ' → θ' ≠ 0 → ∃ a : ℂ, θ = a • θ' := by
  first | exact @GlobalTheory.Dict.ThetaOne.exists_eq_smul_of_isTheta1 | exact GlobalTheory.Dict.ThetaOne.exists_eq_smul_of_isTheta1 | (intros; apply GlobalTheory.Dict.ThetaOne.exists_eq_smul_of_isTheta1 <;> assumption)
end

section

section

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr

namespace GlobalTheory.Dict.CuspAny

theorem mem_minorSpan_of_rowHighest {T : Type} [Fintype T] {p q n : ℕ} {c : T → Fin p → ℕ}
    {c' : T → Fin q → ℕ} {P : Harm.Poly ℂ T p q (Fin n)} (hP : P ∈ Harm.rowHighest ℂ c c') :
    P ∈ GaussGauge.minorSpan (Fin n) c c' := by
  classical
  have h : p + q ≤ n + (p + q) := Nat.le_add_left _ _
  let A : Matrix (Fin n) (Fin (n + (p + q))) ℂ :=
    (1 : Matrix _ _ ℂ).submatrix (Fin.castAdd (p + q)) id
  have hA : A * Aᵀ = 1 := by
    ext i j
    simp [A, Matrix.mul_apply, Matrix.one_apply, eq_comm]
  have h1 : Harm.colSubst (fun _ : T => A) (fun _ => Aᵀ) P ∈ GaussGauge.minorSpan _ c c' :=
    GaussGauge.orbitSpan_le_minorSpan h c c'
      (Harm.rowHighest_eq_orbitSpan h c c' ℂ ▸ Harm.colSubst_mem_rowHighest (fun _ => hA) hP)
  have h2 : Harm.colSubst (fun _ : T => Aᵀ) (fun _ => A)
      (Harm.colSubst (fun _ : T => A) (fun _ => Aᵀ) P) = P := by
    rw [← AlgHom.comp_apply, Harm.colSubst_comp]
    simp only [hA]
    rw [Harm.colSubst_one, AlgHom.id_apply]
  rw [← h2]
  refine (Submodule.span_le (p := (GaussGauge.minorSpan (Fin n) c c').comap
    (Harm.colSubst (fun _ : T => Aᵀ) (fun _ => A)).toLinearMap)).2 ?_ h1
  rintro _ ⟨x, rfl⟩
  change Harm.colSubst (fun _ : T => Aᵀ) (fun _ => A) (Harm.minorProd c c' x.1 x.2) ∈
    GaussGauge.minorSpan (Fin n) c c'
  rw [Harm.colSubst_minorProd]
  exact GaussGauge.minorProd_mem_minorSpan _ _ _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {g : ℕ}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
  {q0 : ℕ} (hr : X.p0 + q0 = r) {n : ℕ} {c : X.Ψ → Fin q0 → ℕ} {c' : X.Ψ → Fin X.p0 → ℕ}

theorem exists_expansion_of_rowHighest (hs : IsSympl X bas) (hn : Even n)
    (hc : ∃ τ, (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨
      ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i)
    (a b : Fin n → Fin g → ℝ) {P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)}
    (hP : P ∈ Harm.rowHighest ℂ c c') {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) :
    ∃ (A : (Fin n → Fin g → ℤ) → ℂ) (ν : (Fin n → Fin g → ℤ) → X.Ψ → ℝ),
      (Summable fun m => ‖A m‖) ∧
      (∀ s : X.Ψ → ℝ, HasSum (fun m => A m * cexp (4 * Real.pi * I * ∑ τ, (ν m τ : ℂ) * s τ))
        (thFr X hr bas idx n a b P (X.flow ξ (fun τ => (s τ : ℂ)) x))) ∧
      ∀ m, A m ≠ 0 → ν m ≠ 0 := by
  obtain ⟨bas', S, hs', hA⟩ := exists_isAdapted hs hξ.2.1
  obtain ⟨a', b', κ, -, -, hκ⟩ := exists_thFr_eq_mul idx hr hs hs' hn a b
  obtain ⟨A, hA1, hA2, hA3⟩ := hA.exists_expansion hr idx hs' hξ n a' b'
    (Harm.isHarmonic_of_mem_rowHighest hP) (mem_minorSpan_of_rowHighest hP) hc hx
  refine ⟨fun m => κ * A m, _, ?_, fun s => ?_,
    fun m hm h0 => hm (mul_eq_zero_of_right κ (hA3 m h0))⟩
  · simpa only [norm_mul] using hA1.mul_left ‖κ‖
  · have hxs := (FlowCoefficientBounds.flow_real X hξ hx s 0).1
    rw [hκ P _ hxs]
    simpa only [mul_assoc] using (hA2 _ hxs).mul_left κ

theorem mem_SS_of_eq_sum_thFr {J : Type} (s : Finset J) (t : J → ℂ) (a b : J → Fin n → Fin g → ℝ)
    {P : J → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)} {Q : Frame X.Ψ r → ℂ} (hs : IsSympl X bas)
    (hn : Even n)
    (hc : ∃ τ, (∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ c τ i) ∨
      ∃ i : Fin X.p0, i.val + 1 = X.p0 ∧ 1 ≤ c' τ i)
    (hP : ∀ j ∈ s, P j ∈ Harm.rowHighest ℂ c c')
    (hQ : ∀ x ∈ X.dom, Q x = ∑ j ∈ s, t j * thFr X hr bas idx n (a j) (b j) (P j) x)
    (hΓ : ∀ ga ∈ X.Γ, ∀ x ∈ X.dom, Q (lact ga x) = X.χ (wtOf X hr c c' n) ga * Q x) :
    Q ∈ X.SS (wtOf X hr c c' n) := by
  have hsec := isSec_of_eq_sum_thFr idx hr s t a b hs hP hQ hΓ
  refine FJZero.mem_SS_of_isModerate X _ Q hsec
    (isModerate_of_eq_sum_thFr idx hr s t a b hs hn hP hQ) fun ξ hξ x hx => ?_
  choose A ν h1 h2 h3 using fun j : s =>
    exists_expansion_of_rowHighest idx hr hs hn hc (a j) (b j) (hP j j.2) hξ hx
  have h4 (j : s) : Summable fun m => ‖t j * A j m‖ := by
    simpa only [norm_mul] using (h1 j).mul_left ‖t j‖
  refine FJZero.fj_eq_zero_of_isSec X _ Q hsec hξ hx
    (fun p : s × (Fin n → Fin g → ℤ) => t p.1 * A p.1 p.2)
    (hasSum_prod_of_fintype h4 fun j => (h4 j).of_norm.hasSum).1 (fun p => ν p.1 p.2)
    (fun u => ?_) 0 fun p hp => h3 _ _ (right_ne_zero_of_mul hp)
  rw [hQ _ (FlowCoefficientBounds.flow_real X hξ hx u 0).1, ← Finset.sum_coe_sort]
  refine (hasSum_prod_of_fintype
    (f := fun (j : s) m => t j * A j m * cexp (4 * Real.pi * I * ∑ τ, (ν j m τ : ℂ) * u τ))
    (fun j => ?_) fun j => ?_).2
  · refine (h4 j).congr fun m => ?_
    have h := FJZero.norm_expo (ν j m) u
    rw [FJZero.expo] at h
    rw [norm_mul (t j * A j m), h, mul_one]
  · simpa only [mul_assoc] using (h2 j u).mul_left (t j)

end GlobalTheory.Dict.CuspAny

end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.CuspAny

theorem mem_SS_of_eq_thP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ((∃ τ, ∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ k τ i) ∨ q0 = 0) → ∀ φ : TF n g, IsSB φ → ∀ P ∈ Harm.rowHighest ℂ k k', ∀ Q : Frame X.Ψ r → ℂ, (∀ x ∈ X.dom, Q x = thP X hr bas idx φ P x) → (∀ ga ∈ X.Γ, ∀ x ∈ X.dom, Q (lact ga x) = X.χ (wtOf X hr k k' n) ga * Q x) → Q ∈ X.SS (wtOf X hr k k' n) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn k k' hk φ hφ P hP Q hQ hΓ
  obtain ⟨m, a, b, t, h⟩ := (GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic E r X g q0 hr bas idx n hs hn).2 φ hφ
  rcases hk with ⟨τ, hτ⟩ | h0
  · exact CuspAny.mem_SS_of_eq_sum_thFr idx hr Finset.univ t (fun j k i => (a j k i : ℝ))
      (fun j k i => (b j k i : ℝ)) (P := fun _ => P) hs hn ⟨τ, Or.inl hτ⟩ (fun _ _ => hP)
      (fun x hx => (hQ x hx).trans (h P x hx)) hΓ
  · exact ThFr.mem_SS_of_eq_sum_thFr idx hr Finset.univ t (fun j k i => (a j k i : ℝ))
      (fun j k i => (b j k i : ℝ)) (P := fun _ => P) hs hn
      (Or.inr (CuspClass.not_isIso_of_definite X (by omega))) (fun _ _ => hP)
      (fun x hx => (hQ x hx).trans (h P x hx)) hΓ

end GlobalTheory.Dict.CuspAny
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.thetaSeries_testFunction_holomorphic_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (φ : TF n g), IsSB φ → ∀ P ∈ Harm.rowHighest ℂ c c', DifferentiableOn ℂ (thP X hr bas idx φ P) X.dom ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, thP X hr bas idx φ P (rmul x b) = bchar (wtOf X hr c c' n) b * thP X hr bas idx φ P x) ∧ (∀ γ, IsUn X γ → ∀ x ∈ X.dom, thP X hr bas idx (wG X bas idx γ φ) P (lact γ x) = thP X hr bas idx φ P x) ∧ ∀ x ∈ X.dom, AnalyticOnNhd ℂ (thA X bas idx φ x) Set.univ := by
  first | exact @GlobalTheory.SW.theta_holomorphic_weight | exact GlobalTheory.SW.theta_holomorphic_weight | (intros; apply GlobalTheory.SW.theta_holomorphic_weight <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rows_congr_of_trivial_at_level : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ∀ y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E, finW S T y' - actO S T h g (finW S T y) ∈ hatA S T (tens Λ (Lv.𝔪 • L)) → ∀ k, Cong C.X Lv.𝔪 (y' k) (y k) := by
  first | exact @GlobalTheory.Ker.LevCong.cong_of_act | exact GlobalTheory.Ker.LevCong.cong_of_act | (intros; apply GlobalTheory.Ker.LevCong.cong_of_act <;> assumption)
end
