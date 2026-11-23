module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArchimedeanUniqueness.MetricDef
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle035
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle015
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle040
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle027
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2FamilyUniformCompare
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Mathlib.Topology.Separation.CompletelyRegular
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ArcCM.Split

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

def quo (θ : A → A → A → U) (k : ℕ) (x b : A) : U := cubN θ k 1 x b * (cubN θ k 1 b x)⁻¹

variable (h : IsCub θ)
include h

theorem coc_four (a b c d x : A) :
    θ (a * b) (c * d) x * θ a b x * θ c d x = θ (a * c) (b * d) x * θ a c x * θ b d x := by
  have e₁ := h.coc a b (c * d) x
  have e₂ := h.coc b c d x
  have e₃ := h.coc a c (b * d) x
  have e₄ := h.coc c b d x
  rw [mul_left_comm c b d] at e₃
  rw [mul_comm c b, h.s01 c b] at e₄
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃; have a₄ := E e₄
  simp only [ofMul_mul] at *
  linear_combination (norm := abel) a₁ - a₂ - a₃ + a₄

theorem cubN_mul_left (k : ℕ) (m m' x : A) :
    cubN θ k 1 (m * m') x * θ m m' x ^ k = θ (m ^ k) (m' ^ k) x * cubN θ k 1 m x * cubN θ k 1 m' x := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have c := coc_four h (m ^ k) (m' ^ k) m m' x
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ m, pow_succ m', pow_succ (θ m m' x), mul_pow]
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul] at ih' c' ⊢
    linear_combination (norm := abel) ih' + c'

theorem quo_one (k : ℕ) (b : A) : quo θ k 1 b = 1 := by
  rw [quo, h.N_one, inv_one, _root_.mul_one]
  exact Finset.prod_eq_one fun _ _ => h.face₂ _ _

theorem quo_mul_left {k : ℕ} {x x' : A} (hx : x ^ k = 1) (b : A) :
    quo θ k (x * x') b * θ x x' (b ^ k) = quo θ k x b * quo θ k x' b := by
  have e₁ := cubN_mul_left h k x x' b
  have e₂ := h.N_add k 1 b x x'
  rw [hx, h.face] at e₁
  rw [h.face, _root_.one_mul, h.s01 b, h.s12 x b, h.s01 (b ^ k), h.s12 x (b ^ k)] at e₂
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  simp only [quo, ofMul_mul, ofMul_inv, ofMul_one] at a₁ a₂ ⊢
  linear_combination (norm := abel) a₁ - a₂

theorem quo_mul_right {k : ℕ} {x : A} (hx : x ^ k = 1) (b b' : A) :
    quo θ k x (b * b') * θ x (b ^ k) (b' ^ k) = quo θ k x b * quo θ k x b' := by
  have e₁ := cubN_mul_left h k b b' x
  have e₂ := h.N_add k 1 x b b'
  rw [hx, h.face, _root_.one_mul, h.face] at e₂
  rw [h.s12 b, h.s01 b, h.s12 (b ^ k), h.s01 (b ^ k)] at e₁
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  simp only [quo, ofMul_mul, ofMul_inv, ofMul_one] at a₁ a₂ ⊢
  linear_combination (norm := abel) a₂ - a₁

end Alg

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {n : ℕ}

theorem val_cubAtT {T : Over (Sp R)} {y : T.left} {J} (hJ : Good D.P.L y J) (x x' w : T ⟶ D.P.A) :
    val (DegPre.cubAtT D T x x' w) (𝟙 _) y J = th D y J x x' w := by
  have := val_cub D.cub (𝟙 T) hJ x x' w
  rwa [Category.id_comp, Category.id_comp, Category.id_comp] at this

theorem prod_gtT {T : Over (Sp R)} (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.gtφT D T b χ i) ^ DegPre.gtε i =
      (h (cP D _ χ * b).left)⁻¹ * h (cP D _ χ).left * h b.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four]
  show h (cP D _ χ * b).left ^ (-1 : ℤ) * h (cP D _ χ).left ^ (1 : ℤ) * h b.left ^ (1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

variable (hc : ∀ y, D.c y ^ n = 1)
include hc

theorem cPoint_pow_eq_one (T : Over (Sp R)) (χ : D.X) : cP D T χ ^ n = 1 :=
  (cPoint_nsmul D T n χ).symm.trans (GlobalTheory.TauTwist.cPoint_nsmul_eq_one hc T χ)

theorem exists_coord (T : Over (Sp R)) (b : T ⟶ D.P.A) (χ : D.X) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T (b ^ n) χ) DegPre.gtε), t.IsGen ∧
      ∀ (T' : Over (Sp R)) (ρ : T' ⟶ T) (z : T'.left) (J), Good D.P.L z J →
        val t ρ.left z J = quo (th D z J) n (cP D T' χ) (ρ ≫ b) := by
  obtain ⟨t, ht, hv⟩ := exists_cubN D.cub 1 (cP D T χ) b n
  obtain ⟨u, hu, hw⟩ := exists_cubN D.cub 1 b (cP D T χ) n
  obtain ⟨t', ht', hv'⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T (b ^ n) χ) (ε' := DegPre.gtε) (fun U _ h => by
      rw [prod_gtT, cPoint_pow_eq_one hc, mul_comm (cP D T χ) (b ^ n), mul_comm b (cP D T χ)]
      apply Additive.ofMul.injective
      simp [Fintype.prod_sum_type, Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module) (LB.mulGen D.P.L _ _ _ _ t (LB.invGen D.P.L _ _ u))
    (mulGen_isGen _ _ _ _ _ _ _ ht (invGen_isGen _ _ _ _ hu))
  refine ⟨t', ht', fun T' ρ z J hJ => (hv' _ _ z J hJ).trans ((val_mul hJ _ _ _).trans
    ((congrArg₂ (· * ·) (hv T' ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (hw T' ρ z J hJ)))).trans ?_))⟩
  rw [MonObj.comp_one, comp_cP]
  rfl

theorem val_coord (T : Over (Sp R)) (b : T ⟶ D.P.A) (χ : D.X) {z : T.left} {J} (hJ : Good D.P.L z J) :
    val (exists_coord hc T b χ).choose (𝟙 _) z J = quo (th D z J) n (cP D T χ) b := by
  have := (exists_coord hc T b χ).choose_spec.2 T (𝟙 T) z J hJ
  rwa [Category.id_comp] at this

def liftPt (T : Over (Sp R)) (b : T ⟶ D.P.A) : GtPt D T where
  b := b ^ n
  s χ := (exists_coord hc T b χ).choose
  isGen χ := (exists_coord hc T b χ).choose_spec.1
  s_zero := corr_of_val D.P.isLB fun y J hJ => (val_coord hc T b 0 hJ).trans (Eq.trans (by
    rw [cPoint_zero]; exact quo_one (isCub_cubV D.cub hJ) n b) (val_one _).symm)
  mult χ χ' := corr_of_val D.P.isLB fun y J hJ =>
    (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_coord hc T b _ hJ) (val_cubAtT hJ _ _ _)).trans (Eq.trans (by
      rw [cPoint_add]; exact quo_mul_left (isCub_cubV D.cub hJ) (cPoint_pow_eq_one hc T χ) b)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_coord hc T b _ hJ) (val_coord hc T b _ hJ))).symm))

theorem isSplit_liftPt : IsSplit D n (liftPt hc) := by
  refine ⟨fun _ _ => rfl, fun T b b' => ⟨mul_pow b b' n, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩,
    fun T T' h b => ⟨?_, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩
  · exact (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_coord hc T _ _ hJ) (val_cubAtT hJ _ _ _)).trans
      ((quo_mul_right (isCub_cubV D.cub hJ) (cPoint_pow_eq_one hc T χ) b b').trans
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_coord hc T b _ hJ) (val_coord hc T b' _ hJ))).symm))
  · exact congrArg (fun q : T' ⟶ D.P.A => q.left) (map_pow (preHom h) b n).symm
  · refine (val_coord hc T' _ _ hJ).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    rw [Category.id_comp]
    exact ((exists_coord hc T b χ).choose_spec.2 T' h y J hJ).symm

end GlobalTheory.ArcCM.Split

namespace GlobalTheory.ArcCM

open AlgebraicGeometry CategoryTheory MonObj ReciprocityTheory.ChartRestriction.G

theorem exists_isSplit : Known → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D₀ : Out.DegPre R) (n : ℕ),
    0 < n → (∀ y, D₀.c y ^ n = 1) → ∃ sB, IsSplit D₀ n sB :=
  fun _ _ _ _ _ _ _ _ hc => ⟨_, Split.isSplit_liftPt hc⟩

end GlobalTheory.ArcCM
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArchNormUnique

open MeasureTheory GlobalTheory.ArchMetricCompare GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms

theorem mean_eq {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {Fd : Set (Fin g → ℂ)} (hF : IsAddFundamentalDomain Λ Fd volume) {f : (Fin g → ℂ) → ℝ}
    (hf : ∀ a ∈ Λ, ∀ x, f (x + a) = f x) :
    (∫ z in Fd, f z) / (volume Fd).toReal = latticeMean Λ f := by
  rw [latticeMean_eq Λ volume hF hf, ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF, smul_eq_mul,
    div_eq_inv_mul]
  rfl

theorem archimedean_l2_norm_unique (hU : ThetaUnifAV) {K : Type} [Field K] {P : Out.PolAV (Sp K)} {σ : K →+* ℂ}
    {rig : LB.Gen (P.L.pull (eSec P.A))} {s : P.L.Sec} {v v' : ℝ} (h : IsL2SquareIntegralProblem P rig σ s v)
    (h' : IsL2SquareIntegralProblem P rig σ s v') : v = v' := by
  obtain ⟨-, A, _, φ, u, Hm, χ, θ, Fd, hp, hu, o, hθ, hF, -, -, -, rfl⟩ := h
  obtain ⟨-, A', _, φ', u', Hm', χ', θ', Fd', hp', hu', o', hθ', hF', -, -, -, rfl⟩ := h'
  obtain ⟨e, he, heψ⟩ := grpPullback_iso hp hp'
  obtain ⟨-, -, -, -, t1, t2, -⟩ := AHWeil.tangent_and_weil_of_isAH hU (pullPol P hp') P.g u' Hm' χ' hu'
  obtain ⟨F, hFe, hFΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom A A' (pullPol P hp).isAb (pullPol P hp').isAb
    _ _ P.g P.g u u' t1 t2 e.hom he
  have hL := pull_isLB P.isLB φ
  have hL' := pull_isLB P.isLB φ'
  obtain ⟨t, ht⟩ : LBIso ((P.L.pull φ').pull e.hom.left) (P.L.pull φ) := by
    have h0 : LBIso (P.L.pull φ') (P.L.pull φ') := ⟨idIso _, idIso_isGen hL'⟩
    have h1 := (PolFibre.lbIso_pull_comp h0 e.hom.left).symm
    rwa [heψ] at h1
  have hHH : ∀ z w, hermForm Hm' (F z) (F w) = hermForm Hm z w := fun z w => by
    simpa using hermForm_pull_eq_of_lbIso_pow A A' _ _ hL hL' _ _ u u' Hm χ Hm' χ' hu hu' e.hom F hFe 1 1
      ⟨LB.linCombIso t _ _, DVR.linCombIso_isGen t ht _ _⟩ z w
  have hinj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun z hz => by
    by_contra hne
    have h1 := hu.2.1 z hne
    have h2 := hHH z z
    rw [hz] at h2
    change 0 < (hermForm Hm z z).re at h1
    rw [← h2] at h1
    simp [hermForm] at h1
  let T := LinearEquiv.ofInjectiveEndo F hinj
  have hT : ∀ z, T z = F z := fun _ => rfl
  have hx : ∀ z, (u'.ex (F z)).left ≫ φ' = (u.ex z).left ≫ φ := fun z => by
    rw [hFe, Over.comp_left, Category.assoc, heψ]
  have hΛ : ∀ z, F z ∈ u'.Λ ↔ z ∈ u.Λ := fun z => ⟨fun hz => by
    rw [← u'.ker, hFe, ← (u'.ker 0).2 u'.Λ.zero_mem, ← map_zero F, hFe, cancel_mono] at hz
    rw [← u.ker, hz, u.ker]
    exact u.Λ.zero_mem, hFΛ z⟩
  let U : P.L.ι → (Fin P.g → ℂ) → Prop := fun j z => ⊤ ≤ (u.ex z).left ⁻¹ᵁ (P.L.pull φ).U fun _ => j
  have U' : ∀ j z, U j z → ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ (P.L.pull φ').U fun _ => j := fun j z hz =>
    (le_pull_iff _ _ _ _).2 ((hx z).symm ▸ (le_pull_iff _ _ _ _).1 hz)
  have Uc : ∀ z, ∃ j, U j z := fun z => by
    obtain ⟨j, hj⟩ := exists_chart_at hL (u.ex z).left
    exact ⟨j PUnit.unit, hj⟩
  let Pm : u.Λ →+ (Fin P.g → ℂ) := u.Λ.subtype.toAddMonoidHom
  have hr : Set.range Pm = u.Λ := Subtype.range_coe
  have hr' : Pm.range = u.Λ.toAddSubgroup := SetLike.coe_injective hr
  have hfr : ∀ j z, U j z → u'.fr (fun _ => j) (F z) = u.fr (fun _ => j) z :=
    GeneratorNorm.frames_eq Pm (by rw [hr']; exact u.discrete) (by rw [hr]; exact u.full) U (fun j => (u.hol _ 0).1) Uc
      (fun j z a hz => by
        have := ex_add_period u z a
        simp only [U] at hz ⊢
        exact this ▸ hz)
      (fun j j' z => valAt' ((u.ex z).left ≫ φ) (P.L.U j ⊓ P.L.U j') (P.L.g j j').val)
      (fun j => u.fr fun _ => j) (fun j z => u'.fr (fun _ => j) (F z))
      (fun a z => Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re))
      (fun j => u.fr_hol _)
      (fun j => (u'.fr_hol _).comp (LinearMap.toContinuousLinearMap F).differentiable.differentiableOn (U' j))
      (fun j z => u.fr_ne _ z)
      (fun j j' z h1 h2 => by
        have h3 := (top_le_preimage_inf _ _ _).2 ⟨h1, h2⟩
        rw [u.fr_compat _ _ z h3, val_pull_g _ _ _ _ _ h3])
      (fun j j' z h1 h2 => by
        have h3 := (top_le_preimage_inf _ _ _).2 ⟨U' j z h1, U' j' z h2⟩
        show u'.fr _ (F z) = _ * u'.fr _ (F z)
        rw [u'.fr_compat _ _ _ h3, val_pull_g _ _ _ _ _ h3, hx])
      (fun j hj => by
        have h0 : ⊤ ≤ (P.L.pull (eSec P.A)).U fun _ => j := by
          have h1 := (le_pull_iff _ _ _ _).1 hj
          rw [TangentOrigin.ex_zero_left] at h1
          refine (le_spMap_iff σ _).1 ((le_pull_iff _ _ _ _).2 ?_)
          exact PolBaseChange.eSec_comm hp ▸ h1
        show u'.fr _ (F 0) = _
        rw [map_zero, o' j h0, o j h0])
      (fun a j z hz => by
        show ‖u.fr _ z‖ = _ * ‖u.fr _ (z + a)‖
        rw [hu.2.2.2 a _ z hz, norm_mul, norm_mul, hu.2.2.1, _root_.one_mul]
        exact congrArg (· * _) (GeneratorNorm.norm_factor Hm z a))
      (fun a j z hz => by
        show ‖u'.fr _ (F z)‖ = _ * ‖u'.fr _ (F (z + a))‖
        rw [hu'.2.2.2 ⟨F a, hFΛ a a.2⟩ _ _ (U' j z hz), norm_mul, norm_mul, hu'.2.2.1, _root_.one_mul, map_add (f := _),
          ← hHH, ← hHH]
        exact congrArg (· * _) (GeneratorNorm.norm_factor Hm' (F z) (F a)))
  have hθθ : ∀ z, θ' (F z) = θ z := fun z => by
    obtain ⟨j, hj⟩ := Uc z
    have h1 := hθ' j (F z) ((le_pull_iff _ _ _ _).1 (U' j z hj))
    rw [hx, hθ j z ((le_pull_iff _ _ _ _).1 hj), hfr j z hj] at h1
    exact (mul_right_cancel₀ (u.fr_ne _ z hj) h1).symm
  have hff : ∀ z, ‖θ' (F z)‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm' (F z)) =
      ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z) := fun z => by
    rw [hθθ, show hermSq Hm' (F z) = hermSq Hm z from congrArg Complex.re (hHH z z)]
  have hper : ∀ a ∈ u.Λ, ∀ z, ‖θ (z + a)‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm (z + a)) =
      ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z) := fun a ha z => by
    obtain ⟨th, hth⟩ := sec_pull_down ((isGen_iff _).1 (idIso_isGen hL)) P.isLB hL s
    have hth := KeyPow.appLE_eq_of_stalk _ s th (hth _ (𝟙 _))
    refine weight_periodic hL hu (s := th) (fun j z hz => ?_) ⟨a, ha⟩ z
    have e := val_via _ s th hth (u.ex z).left (j PUnit.unit) j ((top_le_preimage_inf _ _ _).2 ⟨hz, hz⟩)
    refine Eq.trans ?_ (hθ (j PUnit.unit) z ((le_pull_iff _ _ _ _).1 hz))
    rw [e]
    exact ((congrArg (· * _) (val_g_self hL _ j hz)).trans (_root_.one_mul _)).symm
  have hper' : ∀ a ∈ u'.Λ, ∀ z, ‖θ' (z + a)‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm' (z + a)) =
      ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm' z) := fun a ha z => by
    obtain ⟨a, rfl⟩ := T.surjective a
    obtain ⟨z, rfl⟩ := T.surjective z
    rw [← map_add (f := _), hT, hT, hff, hff, hper a ((hΛ a).1 ha)]
  haveI := u.discrete
  haveI := u'.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  haveI : IsZLattice ℝ u'.Λ := ⟨u'.full⟩
  rw [mean_eq u.Λ hF hper, mean_eq u'.Λ hF' hper',
    ← latticeMean_comp_equiv u.Λ u'.Λ (T.restrictScalars ℝ).toContinuousLinearEquiv hΛ hper']
  exact congrArg _ (funext fun z => (hff z).symm)

theorem norms_unique : Known → ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (σ : K →+* ℂ) (v v' : ℝ), (∀ (rig : LB.Gen (P.L.pull (eSec P.A))) (th : P.L.Sec), rig.IsGen → Arch.IsThNormAt P rig th σ v → Arch.IsThNormAt P rig th σ v' → v = v') ∧ ∀ η' : epsR K ⟶ P.A, IsTangent η' → Arch.IsLieNormAt P η' σ v → Arch.IsLieNormAt P η' σ v' → v = v' := by
  intro hK K _ P σ v v'
  refine ⟨fun rig th _ h h' => archimedean_l2_norm_unique hK.theta ((isL2Sq_iff_isThNormAt P rig σ th v).2 h)
    ((isL2Sq_iff_isThNormAt P rig σ th v').2 h'), ?_⟩
  rintro t ht ⟨Q, φ, w, x, hp, hw, hx, u, Hm, χ, z, hu, hz, rfl⟩ ⟨Q', φ', w', x', hp', hw', hx', u', Hm', χ', z', hu', hz', rfl⟩
  have e := CM.LieMetric.hermForm_eq hK.theta (P := P) (s := σ) ⟨g_eq hp, hp, LBIso.symm ⟨w, hw⟩⟩
    ⟨g_eq hp', hp', LBIso.symm ⟨w', hw'⟩⟩ hu hu' (I := PUnit) (v := fun _ => t) (fun _ => ht)
    (w := fun _ => x) (w' := fun _ => x') (W := fun _ => z) (W' := fun _ => z') (fun _ => ⟨hx, hz⟩) (fun _ => ⟨hx', hz'⟩)
    PUnit.unit PUnit.unit
  exact congrArg (fun c : ℂ => Real.log (Real.pi * c.re) / 2) e

end GlobalTheory.ArchNormUnique
end

section

noncomputable section

namespace GlobalTheory.SplitBC

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

section One

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {n : ℕ}
  {s : ∀ T : Over (Sp R), (T ⟶ D.P.A) → GtPt D T} (hs : IsSplit D n s)
include hs

theorem cv_one (T : Over (Sp R)) (χ : D.X) {y : T.left} {J} (hJ : Good D.P.L y J) : cv (s T 1) χ y J = 1 := by
  have e := ((TorusModel.isAdd_iff _ _ _).1 (hs.2.1 T 1 1)).2 χ y J hJ
  have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
  rw [_root_.mul_one, hs.1, one_pow, C.face₃, _root_.mul_one] at e
  exact (mul_eq_left.1 e.symm)

theorem val_univ {T : Over (Sp R)} (b : T ⟶ D.P.A) (χ : D.X) {Z : Scheme.{0}} (r : Z ⟶ T.left) {z : Z} {J}
    (hJ : Good D.P.L z J) : val ((s T b).s χ) r z J = val ((s D.P.A (𝟙 _)).s χ) (r ≫ b.left) z J := by
  have e := hs.2.2 D.P.A T b (𝟙 _)
  rw [Category.comp_id] at e
  exact (val_corr hJ (e.2 χ) r).trans (val_pull hJ _ _ _)

theorem val_univ_one (T : Over (Sp R)) (χ : D.X) {y : T.left} {J} (hJ : Good D.P.L y J) :
    val ((s D.P.A (𝟙 _)).s χ) (1 : T ⟶ D.P.A).left y J = 1 := by
  have e := val_univ hs (1 : T ⟶ D.P.A) χ (𝟙 _) hJ
  rw [Category.id_comp] at e
  exact e.symm.trans (cv_one hs T χ hJ)

theorem gtTanR_split {v : epsR R ⟶ D.P.A} (hv : IsTangent v) : GtTanR (s (epsR R) v) := by
  let o : Over.mk (𝟙 (Sp R)) ⟶ epsR R := Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom)
    ((spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun _ => rfl)).trans (Spec.map_id (CommRingCat.of R))))
  have ho : o ≫ v = 1 := Over.OverMorphism.ext (hv.trans (Category.id_comp _).symm)
  have e := hs.2.2 _ _ o v
  rw [ho] at e
  refine ⟨s _ 1, ⟨(hs.1 _ _).trans (one_pow n), fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩, e⟩
  exact (cv_one hs _ χ hJ).trans (val_one _).symm

end One

section Two

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'} {D₀ : DegPre R}
  {D₁ : DegPre R'} (p : IsPullDeg f D₀ D₁) {n : ℕ} {s₀ : ∀ T : Over (Sp R), (T ⟶ D₀.P.A) → GtPt D₀ T}
  {s₁ : ∀ T : Over (Sp R'), (T ⟶ D₁.P.A) → GtPt D₁ T}

theorem univ_corr (hG : GlobalFnsSt) (h₀ : IsSplit D₀ n s₀) (h₁ : IsSplit D₁ n s₁) (χ : D₁.X) :
    (∀ k, DegPre.gtφT D₁ D₁.P.A (s₁ D₁.P.A (𝟙 _)).b χ k ≫ prj p =
      prj p ≫ DegPre.gtφT D₀ D₀.P.A (s₀ D₀.P.A (𝟙 _)).b (p.xe χ) k) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ D₁.P.A.left) (z : Z) J J', Good D₀.P.L z J → Good D₁.P.L z J' →
      val ((s₀ D₀.P.A (𝟙 _)).s (p.xe χ)) (r ≫ prj p) z J =
        (∏ k, ConstFam.wVal p.w z J J' (r ≫ DegPre.gtφT D₁ D₁.P.A (s₁ D₁.P.A (𝟙 _)).b χ k) ^ DegPre.gtε k) *
          val ((s₁ D₁.P.A (𝟙 _)).s χ) r z J' := by
  have gp := pull_grp p
  obtain ⟨g, hg⟩ := ConstPoint.exists_gtPt_through hG gp p.w_gen p.xe.toAddMonoidHom p.c_pr
    (T := D₀.P.A) (T' := D₁.P.A) (prj p) gp.1.w (s₀ D₀.P.A (𝟙 _))
  let ρ : Over.mk (D₁.P.A.hom ≫ spMap f) ⟶ D₀.P.A := Over.homMk (prj p) gp.1.w
  have hρ : pushHom gp D₁.P.A (𝟙 _) = ρ := Over.OverMorphism.ext (Category.id_comp _)
  have r₁ : pushHom gp D₁.P.A g.b = ρ ≫ (s₀ D₀.P.A (𝟙 _)).b := Over.OverMorphism.ext ((hg 0).1 2)
  have hb : g.b = (s₁ D₁.P.A (𝟙 _)).b := ConstGrp.push_injective gp _ (by
    rw [r₁, h₀.1, h₁.1, map_pow, hρ, MonObj.comp_pow, Category.comp_id])
  have he : (1 : 𝟙_ (Over (Sp R')) ⟶ D₁.P.A).left ≫ D₁.P.A.hom = 𝟙 _ := Over.w _
  have key := gen_unique' D₁.P.isLB (u := g.s χ) (u' := (s₁ D₁.P.A (𝟙 _)).s χ) (fun U _ k => by rw [hb]) D₁.P.A.hom _ he
    (hG _ _ D₁.P.isAb).2 (g.isGen χ) ((s₁ D₁.P.A (𝟙 _)).isGen χ) (fun y J' hJ' => by
      obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D₀.P.isLB y
      have v := (hg χ).2 _ (1 : 𝟙_ (Over (Sp R')) ⟶ D₁.P.A).left y J J' hJ hJ'
      have o : (1 : 𝟙_ (Over (Sp R')) ⟶ D₁.P.A).left ≫ prj p =
          (1 : Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap f) ⟶ D₀.P.A).left :=
        congrArg (fun q => q.left) (map_one (pushHom gp (𝟙_ (Over (Sp R')))))
      have q := FormalPoint.prod_gtφT (1 : 𝟙_ (Over (Sp R')) ⟶ D₁.P.A) g.b χ (ConstFam.wVal p.w y J J')
      rw [hb, h₁.1, MonObj.comp_pow, Category.comp_id, one_pow, _root_.mul_one, inv_mul_cancel, _root_.one_mul,
        mul_inv_cancel, ← h₁.1, ← hb] at q
      rw [o, q, _root_.one_mul] at v
      exact v.symm.trans ((val_univ_one h₀ (Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap f)) _ hJ).trans
        (val_univ_one h₁ _ χ hJ').symm))
  refine ⟨fun k => hb ▸ (hg χ).1 k, fun Z r z J J' hJ hJ' => ?_⟩
  rw [← key Z r z J' hJ', ← hb]
  exact (hg χ).2 Z r z J J' hJ hJ'

theorem letBC_split (hG : GlobalFnsSt) (h₀ : IsSplit D₀ n s₀) (h₁ : IsSplit D₁ n s₁) {v : epsR R ⟶ D₀.P.A}
    {v₁ : epsR R' ⟶ D₁.P.A} (hv : v₁.left ≫ prj p = spMap (dualMap f) ≫ v.left) :
    LetBC p (s₀ (epsR R) v) (s₁ (epsR R') v₁) := by
  have a₀ : ∀ x k, DegPre.gtφT D₀ _ (s₀ (epsR R) v).b x k = v.left ≫ DegPre.gtφT D₀ _ (s₀ D₀.P.A (𝟙 _)).b x k := by
    intro x k
    have e := (h₀.2.2 _ _ v (𝟙 _)).1
    rw [Category.comp_id] at e
    rw [(TorusCoord.comp_eq_of_left _ (s₀ (epsR R) v).b v.left (𝟙 _) (e.symm.trans (Category.id_comp _).symm)).1 x k,
      Category.id_comp, TorusCoord.gtφT_eq]
  have a₁ : ∀ x k, DegPre.gtφT D₁ _ (s₁ (epsR R') v₁).b x k = v₁.left ≫ DegPre.gtφT D₁ _ (s₁ D₁.P.A (𝟙 _)).b x k := by
    intro x k
    have e := (h₁.2.2 _ _ v₁ (𝟙 _)).1
    rw [Category.comp_id] at e
    rw [(TorusCoord.comp_eq_of_left _ (s₁ (epsR R') v₁).b v₁.left (𝟙 _) (e.symm.trans (Category.id_comp _).symm)).1 x k,
      Category.id_comp, TorusCoord.gtφT_eq]
  have hψ : ∀ χ k, DegPre.gtφT D₁ _ (s₁ (epsR R') v₁).b χ k ≫ prj p =
      spMap (dualMap f) ≫ DegPre.gtφT D₀ _ (s₀ (epsR R) v).b (p.xe χ) k := fun χ k => by
    rw [a₀, a₁, Category.assoc, (univ_corr p hG h₀ h₁ χ).1, ← Category.assoc, hv, Category.assoc]
  refine (ArcQBC.letBC_iff p _ _).2 ⟨hψ 0 2, fun χ => ⟨hψ χ, ArcQBC.pmaps_of_val p.w_gen D₀.P.isLB D₁.P.isLB (hψ χ)
    ((s₁ _ v₁).isGen χ) ((s₀ _ v).isGen _) fun y J J' hJ hJ' => ?_⟩⟩
  have e := (univ_corr p hG h₀ h₁ χ).2 _ v₁.left y J J' hJ hJ'
  rw [hv] at e
  refine (val_univ h₀ v _ _ hJ).trans ?_
  rw [val_univ h₁ v₁ χ _ hJ']
  simp only [Category.id_comp, a₁]
  exact e

end Two

theorem split_baseChange : Known → ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] (f : R →+* R') (D₀ : Out.DegPre R) (D₁ : Out.DegPre R') (p : Out.IsPullDeg f D₀ D₁) (n : ℕ) (s₀ : ∀ T : Over (Sp R), (T ⟶ D₀.P.A) → Out.GtPt D₀ T) (s₁ : ∀ T : Over (Sp R'), (T ⟶ D₁.P.A) → Out.GtPt D₁ T), Function.Injective f → IsSplit D₀ n s₀ → IsSplit D₁ n s₁ → ∀ (v : epsR R ⟶ D₀.P.A) (v₁ : epsR R' ⟶ D₁.P.A), v₁.left ≫ prj p = spMap (dualMap f) ≫ v.left → (IsTangent v → GtTanR (s₀ (epsR R) v)) ∧ LetBC p (s₀ (epsR R) v) (s₁ (epsR R') v₁) :=
  fun hK _ _ _ _ _ _ _ _ _ _ _ p _ _ _ _ h₀ h₁ _ _ hv =>
    ⟨fun ht => gtTanR_split h₀ ht, letBC_split p hK.laws.globalFns h₀ h₁ hv⟩

end GlobalTheory.SplitBC
end
end
