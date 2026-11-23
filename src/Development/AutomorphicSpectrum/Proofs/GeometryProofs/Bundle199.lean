module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle195
public import Development.WeilBound.CoreStatements.SesquilinearFractions.GIntFrame
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle011
public import Development.WeilBound.CoreStatements.SesquilinearFractions.GOntoKer
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle044
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilOpenChart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle064
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NatCastSmulMemHtLat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkLoc
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle040
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle196
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle197
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle013
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.SumRoots

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smooth_ofWeight (u : ((Σ k, ι k) → ℂ) → ℝ)
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) (hs : SmoothFn u) :
    IsSmoothHerm (HermLine.ofWeight u hu) :=
  ContDiffOn.exp hs.neg

theorem smooth_tensor {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) :=
  ContDiffOn.mul hA hB

theorem homog_one : IsMultiHomog (1 : MRing ι) (fun _ => 0) := by
  intro m hm k
  rw [← C_1, C_apply] at hm
  have := Finset.mem_singleton.mp (support_monomial_subset hm)
  simp [this]

theorem inter_ofWeight {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι}
    (hW : IsArithVar W (n + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (u : ((Σ k, ι k) → ℂ) → ℝ)
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) (hs : SmoothFn u) :
    I W (n + 1) (Fin.snoc L (HermLine.ofWeight u hu)) = -ptsIntegral W (pot L) u := by
  have h1 : (1 : MRing ι) ∉ W := (Ideal.ne_top_iff_one W).mp hW.2.1.1.ne_top
  rw [hI.2.2 W n L _ 1 (fun _ => 0) hW hL (smooth_ofWeight u hu hs) (fun k => by simp [HermLine.ofWeight])
    homog_one h1]
  have hd : divSupp W (1 : MRing ι) = ∅ := by
    ext V
    simp [divSupp, Ideal.minimalPrimes_top]
  have hl : logNorm (HermLine.ofWeight u hu) (1 : MRing ι) = u := by
    funext z
    simp [logNorm, HermLine.ofWeight]
  unfold recR arInt
  rw [hd, hl]
  simp only [finsum_mem_empty, zero_sub]
  rfl

noncomputable def tens : (N : ℕ) → (Fin N → HermLine ι) → HermLine ι
  | 0, _ => HermLine.ofWeight (fun _ => 0) (fun _ _ _ => rfl)
  | N + 1, x => (tens N (fun i => x i.castSucc)).tensor (x (Fin.last N))

theorem tens_a : ∀ (N : ℕ) (x : Fin N → HermLine ι), (tens N x).a = ∑ i, (x i).a
  | 0, _ => by simp [tens, HermLine.ofWeight]
  | N + 1, x => by
    rw [Fin.sum_univ_castSucc, ← tens_a N (fun i => x i.castSucc)]
    rfl

theorem tens_h : ∀ (N : ℕ) (x : Fin N → HermLine ι) z, (tens N x).h z = ∏ i, (x i).h z
  | 0, _, _ => by simp [tens, HermLine.ofWeight]
  | N + 1, x, z => by
    rw [Fin.prod_univ_castSucc, ← tens_h N (fun i => x i.castSucc)]
    rfl

theorem tens_smooth : ∀ (N : ℕ) (x : Fin N → HermLine ι), (∀ i, IsSmoothHerm (x i)) → IsSmoothHerm (tens N x)
  | 0, _, _ => smooth_ofWeight _ _ contDiffOn_const
  | N + 1, x, hx => smooth_tensor (tens_smooth N _ fun _ => hx _) (hx _)

theorem ptsIntegral_zero (W : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral W φ (fun _ => 0) = 0 := by
  unfold ptsIntegral
  split_ifs with h
  · have : ∀ y w, sheetDensity W h.choose φ (fun _ => 0) y w = 0 := fun y w => by
      unfold sheetDensity
      split_ifs <;> simp
    simp [ptsIntegralAt, this]
  · rfl

theorem inter_tens {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι}
    (hW : IsArithVar W (n + 1)) (hL : ∀ j, IsSmoothHerm (L j)) :
    ∀ (N : ℕ) (x : Fin N → HermLine ι), (∀ i, IsSmoothHerm (x i)) →
      I W (n + 1) (Fin.snoc L (tens N x)) = ∑ i, I W (n + 1) (Fin.snoc L (x i))
  | 0, _, _ => by
    rw [tens, inter_ofWeight hI hW hL _ _ contDiffOn_const, ptsIntegral_zero]
    simp
  | N + 1, x, hx => by
    rw [tens, hI.2.1 W n L _ _ hW hL (tens_smooth N _ fun _ => hx _) (hx _),
      inter_tens hI hW hL N _ (fun _ => hx _), Fin.sum_univ_castSucc]

end GlobalTheory.CompanionTheory.Ar.Flat.SumRoots

theorem GlobalTheory.CompanionTheory.Ar.Flat.sum_roots_eq : PtsIntegrableStatement → MetricLocalStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (S : FlatHerm y φ A) (d N : ℕ) (x : Fin N → HermLine ι) (v : ((Σ k, ι k) → ℂ) → ℝ), IsIntersectionFamily I → IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W → IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → (∀ i, IsSmoothHerm (x i)) → (∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → v (fun p => c p.1 * z p) = v z) → SmoothFn v → ∑ i, (x i).a = A.a → (∀ z ∈ mcPts W, ∏ i, (x i).h z = A.h z * Real.exp (-v z)) → ∑ i, I W (n + 1) (Fin.snoc L (x i)) = S.ht * ptsIntegral W (pot L) (fun _ => 1) - ptsIntegral W (pot L) v := by
  intro hP hM K _ ι _ Ω _ F _ _ y φ I W n L A S d N x v hI hV hO hyW hW hL hA hx hv hs ha hh
  open GlobalTheory.CompanionTheory.Ar.Flat.SumRoots in
  have hsn : ∀ B : HermLine ι, IsSmoothHerm B →
      ∀ j, IsSmoothHerm ((Fin.snoc L B : Fin (n + 1) → HermLine ι) j) := fun B hB j => by
    induction j using Fin.lastCases with
    | last => simpa using hB
    | cast j => simpa using hL j
  open GlobalTheory.CompanionTheory.Ar.Flat.SumRoots in
  have hloc : I W (n + 1) (Fin.snoc L (tens N x)) =
      I W (n + 1) (Fin.snoc L (A.tensor (HermLine.ofWeight v hv))) := by
    refine hM K ι I hI W (n + 1) _ _ hW (hsn _ (tens_smooth N x hx))
      (hsn _ (smooth_tensor hA (smooth_ofWeight v hv hs))) (fun j => ?_) (fun j z hz => ?_)
    · induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        rw [tens_a, ha]
        simp [HermLine.tensor, HermLine.ofWeight]
      | cast j => simp only [Fin.snoc_castSucc]
    · induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        rw [tens_h, hh z hz]
        rfl
      | cast j => simp only [Fin.snoc_castSucc]
  open GlobalTheory.CompanionTheory.Ar.Flat.SumRoots in
  rw [← inter_tens hI hW hL N x hx, hloc, hI.2.1 W n L _ _ hW hL hA (smooth_ofWeight v hv hs),
    inter_ofWeight hI hW hL v hv hs,
    GlobalTheory.T.intersection_family_flat_herm hP K ι Ω F y φ I W n L A S d hI hV hO hyW hW hL hA, sub_eq_add_neg]
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.HtLink

open PositivityTheory.HtPt.Htat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.BT hiding genPt
open GlobalTheory.CompanionTheory.Ar.HTTie
open GlobalTheory.CompanionTheory.Ar.HTChart (dual_comp snd_epsMul)

section Alg

variable {A Ω : Type} [CommRing A] [Field Ω] [Algebra A Ω] {L₀ : Type} [AddCommGroup L₀] [Module A L₀]

theorem clear_denom [Module.Finite A L₀] (hinj : Function.Injective (algebraMap A Ω)) (B : Subring Ω)
    (hB : ∀ b ∈ B, ∃ u a : A, algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ B ∧
      algebraMap A Ω u * b = algebraMap A Ω a)
    (w : L₀ →ₗ[A] Ω) (hw : ∀ b, w b ∈ B) :
    ∃ (u : A) (w₀ : Module.Dual A L₀), algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ B ∧
      ∀ b, algebraMap A Ω (w₀ b) = algebraMap A Ω u * w b := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := L₀)
  have key : ∀ s : Finset L₀, ∃ u : A, algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ B ∧
      ∀ b ∈ s, ∃ a, algebraMap A Ω a = algebraMap A Ω u * w b := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by simp, by simp, by simp⟩
    | insert b s _ ih =>
      obtain ⟨u, h1, h2, h3⟩ := ih
      obtain ⟨u', a, h1', h2', h3'⟩ := hB _ (hw b)
      refine ⟨u * u', by rw [map_mul]; exact mul_ne_zero h1 h1', by rw [map_mul, mul_inv]; exact mul_mem h2 h2',
        fun c hc => ?_⟩
      rcases Finset.mem_insert.1 hc with rfl | hc
      · exact ⟨u * a, by rw [map_mul, map_mul, ← h3']; ring⟩
      · obtain ⟨a', ha'⟩ := h3 c hc
        exact ⟨u' * a', by rw [map_mul, map_mul, ha']; ring⟩
  obtain ⟨u, h1, h2, h3⟩ := key s
  have hall : ∀ b, ∃ a, algebraMap A Ω a = algebraMap A Ω u * w b := by
    intro b
    have hb : b ∈ Submodule.span A (s : Set L₀) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem c hc => exact h3 c hc
    | zero => exact ⟨0, by simp⟩
    | add c d _ _ hc hd =>
      obtain ⟨a, ha⟩ := hc
      obtain ⟨a', ha'⟩ := hd
      exact ⟨a + a', by rw [map_add (f := _), map_add (f := _), ha, ha', mul_add]⟩
    | smul r c _ hc =>
      obtain ⟨a, ha⟩ := hc
      exact ⟨r * a, by rw [map_mul, map_smul, ha, Algebra.smul_def]; ring⟩
  choose w₀ hw₀ using hall
  refine ⟨u, ⟨⟨w₀, fun a b => hinj ?_⟩, fun r a => hinj ?_⟩, h1, h2, hw₀⟩
  · rw [map_add (f := _), hw₀, hw₀, hw₀, map_add (f := _), mul_add]
  · show algebraMap A Ω (w₀ (r • a)) = algebraMap A Ω (r * w₀ a)
    rw [map_mul, hw₀, hw₀, map_smul, Algebra.smul_def]; ring

variable {Li : Type} [AddCommGroup Li] [Module Ω Li] [Module A Li] [IsScalarTower A Ω Li]

theorem exists_dualBC [IsDomain A] [IsFractionRing A Ω] [Module.Finite A L₀] (j₀ : L₀ →ₗ[A] Li)
    (hj₀ : IsBaseChange Ω j₀) :
    ∃ j : Module.Dual A L₀ →ₗ[A] Module.Dual Ω Li, IsBaseChange Ω j ∧
      ∀ w b, j w (j₀ b) = algebraMap A Ω (w b) := by
  have hinj := IsFractionRing.injective A Ω
  let J : Module.Dual A L₀ → Module.Dual Ω Li := fun w => hj₀.lift (Algebra.linearMap A Ω ∘ₗ w)
  have hJ : ∀ w b, J w (j₀ b) = algebraMap A Ω (w b) := fun w b => hj₀.lift_eq _ b
  have hext : ∀ w w' : Module.Dual Ω Li, (∀ b, w (j₀ b) = w' (j₀ b)) → w = w' := fun w w' h => hj₀.algHom_ext _ _ h
  have hsm : ∀ (a : A) (w : Module.Dual Ω Li) e, (a • w) e = algebraMap A Ω a * w e := fun a w e => by
    rw [← algebraMap_smul Ω a w]; rfl
  let j : Module.Dual A L₀ →ₗ[A] Module.Dual Ω Li :=
    { toFun := J
      map_add' := fun w w' => hext _ _ fun b => by simp [hJ]
      map_smul' := fun a w => hext _ _ fun b => by simp [hJ, hsm] }
  refine ⟨j, (isLocalizedModule_iff_isBaseChange (nonZeroDivisors A) Ω j).1 ⟨fun s => ?_, fun w => ?_, ?_⟩, hJ⟩
  · have hs : algebraMap A Ω s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    rw [Module.End.isUnit_iff]
    refine ⟨fun w w' h => ?_, fun w => ⟨(algebraMap A Ω s)⁻¹ • w, ?_⟩⟩
    · have h' : (s : A) • w = (s : A) • w' := h
      rw [← algebraMap_smul Ω, ← algebraMap_smul Ω (s : A) w'] at h'
      exact smul_right_injective _ hs h'
    · show (s : A) • ((algebraMap A Ω s)⁻¹ • w) = w
      rw [← algebraMap_smul Ω, smul_smul, mul_inv_cancel₀ hs, one_smul]
  · obtain ⟨u, w₀, h1, -, h3⟩ := clear_denom hinj ⊤ (fun b _ => by
      obtain ⟨a, u, hu, rfl⟩ := IsFractionRing.div_surjective (A := A) b
      have := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := Ω) hu
      exact ⟨u, a, this, trivial, by field_simp⟩) ((w.restrictScalars A) ∘ₗ j₀) (fun _ => trivial)
    refine ⟨⟨w₀, ⟨u, mem_nonZeroDivisors_of_ne_zero fun h => h1 (by rw [h, map_zero])⟩⟩, hext _ _ fun b => ?_⟩
    show ((u : A) • w) (j₀ b) = J w₀ (j₀ b)
    rw [hsm, hJ, h3]; rfl
  · intro w w' h
    refine ⟨1, ?_⟩
    have : w = w' := LinearMap.ext fun b => hinj (by rw [← hJ, ← hJ]; exact LinearMap.congr_fun h _)
    rw [this]

end Alg

section Geo

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {A : Type} [CommRing A] [Algebra A Ω] {x : Spec (CommRingCat.of A) ⟶ X}

theorem regAt_frac (hξ : IsCptGen ξ) (hk : Function.Injective (algebraMap A Ω))
    (hx : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ x = ξ) (p : PrimeSpectrum A) (q : Cpt ξ) (hp : x p = q.1)
    (hsub : ∀ a, algebraMap A Ω a ∈ regAt ξ q) :
    (∀ u ∉ p.asIdeal, algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ regAt ξ q) ∧
      ∀ b ∈ regAt ξ q, ∃ u a : A, u ∉ p.asIdeal ∧ algebraMap A Ω u * b = algebraMap A Ω a := by
  obtain ⟨_, hS, -, hg⟩ := stalk_loc hξ _ hk x hx p q hp hsub
  have hg' : ∀ a, genMap ξ q (algebraMap A _ a) = algebraMap A Ω a := RingHom.congr_fun hg
  refine ⟨fun u hu => ?_, ?_⟩
  · obtain ⟨t, ht⟩ := (IsLocalization.map_units (X.presheaf.stalk q.1)
      (⟨u, hu⟩ : p.asIdeal.primeCompl)).exists_right_inv
    have h1 : algebraMap A Ω u * genMap ξ q t = 1 := by rw [← hg', ← map_mul, ht, map_one]
    exact ⟨left_ne_zero_of_mul_eq_one h1, t, (eq_inv_of_mul_eq_one_right h1)⟩
  · rintro _ ⟨c, rfl⟩
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj p.asIdeal.primeCompl c
    exact ⟨s, a, s.2, by rw [← hg', ← hg', ← h, map_mul, mul_comm]⟩

variable {G : Over X} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {Li : Type} [AddCommGroup Li] [Module Ω Li]
  (M : LieModel G ξ Li) {L₀ : Type} [AddCommGroup L₀] [Module A L₀] (M₀ : LieModel G x L₀)

omit [IsCommMonObj G] in
theorem exists_lieBC (hx : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ x = ξ) [Module A Li]
    [IsScalarTower A Ω Li] : ∃ j₀ : L₀ →ₗ[A] Li, IsBaseChange Ω j₀ ∧ ∀ v, (M.pt (j₀ v)).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left := by
  subst hx
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear X G A Ω (algebraMap A Ω) x L₀ Li M₀ M
  have hj' : ∀ v, (M.pt (j v)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left :=
    fun v => (Category.comp_id _).symm.trans (hj v)
  let j₀ : L₀ →ₗ[A] Li :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun a v => by rw [j.map_smulₛₗ, algebraMap_smul]; rfl }
  exact ⟨j₀, (lie_proj X G A x L₀ M₀).2.2 Ω Li M j₀ hj', hj'⟩

omit [IsCommMonObj G] [Smooth G.hom] in
theorem tan_ext {O : Type} [CommRing O] [Algebra A O] {z : Spec (CommRingCat.of O) ⟶ X}
    (hzs : Spec.map (CommRingCat.ofHom (algebraMap A O)) ≫ x = z) (g : O →+* Ω)
    (hg : g.comp (algebraMap A O) = algebraMap A Ω) (j₀ : L₀ → Li)
    (hj : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left)
    (b : L₀) : ∃ v : epsAt z ⟶ G, IsTanAt G z v ∧
      (M.pt (j₀ b)).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left := by
  let ψ := LieCarrier.epsHom (algebraMap A O) x _ hzs
  have hleft : (ψ ≫ M₀.pt b).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap A O))) ≫ (M₀.pt b).left := rfl
  refine ⟨ψ ≫ M₀.pt b, ?_, ?_⟩
  · have t : _ ≫ (M₀.pt b).left = _ := M₀.tan b
    rw [one_left] at t
    show _ ≫ (ψ ≫ M₀.pt b).left = _
    rw [hleft, one_left, ← Category.assoc, ← spec_comp, dual_fst, spec_comp, Category.assoc, t]
    simp only [Over.mk_hom]
    rw [← Category.assoc, hzs]
  · rw [hleft, hj, ← Category.assoc, ← spec_comp, dual_comp, hg]

theorem tan_denom {O : Type} [CommRing O] [Algebra A O] (S : Submonoid A) [IsLocalization S O]
    {z : Spec (CommRingCat.of O) ⟶ X}
    (hzs : Spec.map (CommRingCat.ofHom (algebraMap A O)) ≫ x = z) (g : O →+* Ω)
    (hg : g.comp (algebraMap A O) = algebraMap A Ω) (j₀ : L₀ → Li)
    (hj : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left)
    (e : Li) (v : epsAt z ⟶ G) (hv : IsTanAt G z v)
    (he' : (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left) :
    ∃ u ∈ S, ∃ b, algebraMap A Ω u • e = j₀ b := by
  obtain ⟨u, hu, b, hub⟩ := exists_denom lie_proj G S x M₀ hzs v hv
  have hgu : g (algebraMap A O u) = algebraMap A Ω u := RingHom.congr_fun hg u
  refine ⟨u, hu, b, hgu ▸ M.inj (Over.OverMorphism.ext ?_)⟩
  rw [M.smul, he', hj, ← hg, ← dual_comp, spec_comp, Category.assoc, ← hub, ← Category.assoc, ← Category.assoc,
    ← spec_comp, ← spec_comp, dual_eps]

theorem mem_omLat_iff (hξ : IsCptGen ξ) (hk : Function.Injective (algebraMap A Ω))
    (hx : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ x = ξ) (j₀ : L₀ → Li)
    (hj : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left)
    (q : Cpt ξ) (hq : q.1 ∈ Set.range x) (hsub : ∀ a, algebraMap A Ω a ∈ regAt ξ q) (w : Module.Dual Ω Li) :
    w ∈ M.omLat q ↔ ∀ b, w (j₀ b) ∈ regAt ξ q := by
  obtain ⟨p, hp⟩ : ∃ p : PrimeSpectrum A, x p = q.1 := hq
  obtain ⟨_, hS, hzs, hg⟩ := stalk_loc hξ _ hk x hx p q hp hsub
  have hlat := (lieLat_carrier X G Ω ξ Li M q).1
  refine ⟨fun h b => h _ ((hlat _).2 ?_), fun h e he => ?_⟩
  · exact tan_ext M M₀ hzs (genMap ξ q) hg j₀ hj b
  · obtain ⟨v, hv, he'⟩ := (hlat e).1 he
    obtain ⟨u, hu, b, hje⟩ := tan_denom M M₀ p.asIdeal.primeCompl hzs (genMap ξ q) hg j₀ hj e v hv he'
    obtain ⟨h1, h2⟩ := (regAt_frac hξ hk hx p q hp hsub).1 u hu
    have : w e = (algebraMap A Ω u)⁻¹ * w (j₀ b) := by
      rw [← hje, map_smul, smul_eq_mul, ← _root_.mul_assoc, inv_mul_cancel₀ h1, _root_.one_mul]
    rw [this]
    exact mul_mem h2 (h b)

end Geo

end GlobalTheory.CompanionTheory.HtLink
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.CompanionTheory.Relay.tangent_vectors_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (F F' : Type) [Field F] [Field F'] (f : F →+* F') (x : Sp F ⟶ S) (x' : Sp F' ⟶ S) (τ : 𝓞 E →+* F) (n : ℕ) (v : Fin n → (epsAt x ⟶ t.G)), x' = spMap f ≫ x → (∃ v' : Fin n → (epsAt x' ⟶ t.G), ∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) ∧ ∀ v' : Fin n → (epsAt x' ⟶ t.G), (∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) → (IsEigFrame t.act x τ v ↔ IsEigFrame t.act x' (f.comp τ) v') := by
  first | exact @PositivityTheory.Xgf.tangent_vectors_base_change | exact PositivityTheory.Xgf.tangent_vectors_base_change
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_component_lattice_map_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (i : Ω₀ →+* Ω) (ι : 𝔐₀.Li →+ 𝔐.Li) (W : Subring Ω) (φ : W →+* ℂ) (z₁ : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (z₂ : Spec (CommRingCat.of ℂ) ⟶ 𝔐₀.X) (σ₁ : 𝔐.X.presheaf.stalk (centre z₁) →+* W) (σ₂ : 𝔐₀.X.presheaf.stalk (centre z₂) →+* W), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → (∀ (e : 𝔐₀.Li) (e' : 𝔐.Li), (𝔐.M.pt e').left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt e).left ≫ 𝔐₀.m.φ ↔ e' = ι e) → (∀ s, (σ₁ s : Ω) = genMap 𝔐.ξ ⟨centre z₁, 𝔐.all _⟩ s) → (∀ s, (σ₂ s : Ω) = i (genMap 𝔐₀.ξ ⟨centre z₂, 𝔐₀.all _⟩ s)) → (∀ s, φ (σ₁ s) = (Scheme.stalkClosedPointTo z₁).hom s) → (∀ s, φ (σ₂ s) = (Scheme.stalkClosedPointTo z₂).hom s) → spMap σ₁ ≫ 𝔐.X.fromSpecStalk (centre z₁) ≫ 𝔐.f = spMap σ₂ ≫ 𝔐₀.X.fromSpecStalk (centre z₂) ≫ 𝔐₀.f → ∀ (Vz : Type) [AddCommGroup Vz] [Module ℂ Vz] (MR : LieModel 𝔐.t.G z₁ Vz), ∃ (Lm : Submodule W 𝔐.Li) (val : 𝔐.Li → Vz), val 0 = 0 ∧ (∀ e ∈ Lm, ∀ e' ∈ Lm, val (e + e') = val e + val e') ∧ (∀ a : W, ∀ e ∈ Lm, val ((a : Ω) • e) = φ a • val e) ∧ (∀ (e : 𝔐.Li) (v : epsAt z₁ ⟶ 𝔐.t.G), 𝔐.M.ValAt z₁ e v → e ∈ Lm ∧ v = MR.pt (val e)) ∧ ∀ (e₀ : 𝔐₀.Li) (v₀ : epsAt z₂ ⟶ 𝔐₀.t.G), 𝔐₀.M.ValAt z₂ e₀ v₀ → ι e₀ ∈ Lm ∧ (MR.pt (val (ι e₀))).left ≫ 𝔐.m.φ = v₀.left ≫ 𝔐₀.m.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SingVal.value_map | exact GlobalTheory.CompanionTheory.Ar.SingVal.value_map | (intros; apply GlobalTheory.CompanionTheory.Ar.SingVal.value_map <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.isPrincipal_base_change_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L L' : Type) [Field L] [Field L'] (e : L →+* L') (t : SAB H (Sp L)) (t' : SAB H (Sp L')) (_ : SABMap t' t (spMap e)), IsPrincipal t' ↔ IsPrincipal t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isPrincipal_iff_of_sabMap_field | exact GlobalTheory.CompanionTheory.Ar.isPrincipal_iff_of_sabMap_field | (intros; apply GlobalTheory.CompanionTheory.Ar.isPrincipal_iff_of_sabMap_field <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.CompanionTheory.Relay.lie_model_extends_over_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (K : Type) [Field K] (V : Subring K) [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V K] (y : Sp K ⟶ Xo.XF c) (T : SAB H (Sp V)) (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y)) (m' : SABMap tK T (spMap (algebraMap V K))) (U : Type) [AddCommGroup U] [Module K U] (M : LieModel Xo.univ.t.G (under y) U) (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (I : Type) [Fintype I] (n r : ℕ) (e : Fin n ≃ I) (uV : Fin n → (epsAt (𝟙 (Sp V)) ⟶ T.G)) (u : I → U) (v : Fin r → U), M.IsActOf Xo.univ.t.act.act ρ → (∀ a : 𝓞 E, σ (a : E) ∈ V) → (∀ k, IsTanAt T.G _ (uV k)) → (∀ w, IsTanAt T.G _ w → ∃! cc : Fin n → V, IsComb cc uV w) → (∀ k, ∃ s : Sp (DualNumber K) ⟶ tK.G.left, s ≫ m.φ = (M.pt (u (e k))).left ∧ s ≫ m'.φ = spMap (dualMap (algebraMap V K)) ≫ (uV k).left) → LinearIndependent K v → Submodule.span V (Set.range u) ⊓ (HT.eigSp ρ σ).restrictScalars V = Submodule.span V (Set.range v) → LinearIndependent K u ∧ IsIntFrame m m' (σ.comp (algebraMap (𝓞 E) E)) (fun a => M.pt (v a)) := by
  first | exact @PositivityTheory.Xgf.lie_model_extends_over_dvr | exact PositivityTheory.Xgf.lie_model_extends_over_dvr
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem _root_.GlobalTheory.T.riemann_lattice_over_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X) (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ), IsOver 𝔐 z κ p → FibreLat Xo.univ.t p R → FibreLat 𝔐.t z R := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.fibreLat_of_isOver | exact GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.fibreLat_of_isOver | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.fibreLat_of_isOver <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

theorem _root_.GlobalTheory.T.hodge_comp_compare_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (Fl₀ : 𝔐₀.Flag) (i : Ω₀ →+* Ω), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → ∃ ι : 𝔐₀.Li →+ 𝔐.Li, IsExtOver i ι ∧ Submodule.span Ω (Set.range ι) = ⊤ ∧ (∀ (e : 𝔐₀.Li) (e' : 𝔐.Li), (𝔐.M.pt e').left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt e).left ≫ 𝔐₀.m.φ ↔ e' = ι e) ∧ ∀ (W : Subring Ω) (q : Cpt 𝔐.ξ) (q₀ : Cpt 𝔐₀.ξ), (∀ a ∈ regAt 𝔐.ξ q, a ∈ W) → (∀ a ∈ regAt 𝔐₀.ξ q₀, i a ∈ W) → 𝔐.f q.1 = 𝔐₀.f q₀.1 → Submodule.span W ((𝔐.M.lat q : Set 𝔐.Li)) = Submodule.span W (ι '' (𝔐₀.M.lat q₀ : Set 𝔐₀.Li)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrVert.LieCmp.lie_cmp | exact GlobalTheory.CompanionTheory.Ar.OrVert.LieCmp.lie_cmp | (intros; apply GlobalTheory.CompanionTheory.Ar.OrVert.LieCmp.lie_cmp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem curve0_z_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : ℂ) (Z : Curve0 H ρ), Z.z ≠ 0 :=
  @PositivityTheory.Xgf.curve_z_ne_zero

end GlobalTheory.CompanionTheory.Ar.Fl
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.CompanionTheory.Relay.cm_pack_torsion_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (N : ℕ) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))), 0 < N → (∀ y : (FU.Di i).La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : (FU.Di i).La))) → (∀ y : Over.mk (spMap ((algebraMap X.K ℂ).comp (algebraMap (𝓞 X.K) X.K))) ⟶ X.B.t.G, ∃ x : ∀ k, Over.mk (spMap ((algebraMap X.K ℂ).comp (algebraMap (𝓞 X.K) X.K))) ⟶ (X.C (b k)).P.A, y = (List.ofFn fun k => x k ≫ X.ψ (b k) (a k)).prod) ∧ ∀ x : ∀ k, Over.mk (spMap ((algebraMap X.K ℂ).comp (algebraMap (𝓞 X.K) X.K))) ⟶ (X.C (b k)).P.A, (List.ofFn fun k => x k ≫ X.ψ (b k) (a k)).prod = 1 → ∀ k, x k ^ N = 1 := by
  first | exact @PositivityTheory.Xgf.cm_pack_torsion_points | exact PositivityTheory.Xgf.cm_pack_torsion_points
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_pullback_smooth : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X'), IsCptGen ξ → IsCptGen ξ' → ∀ (f : X' ⟶ X) (i : Ω →+* Ω') (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → Smooth G.hom → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (E' : Type) [AddCommGroup E'] [Module Ω' E'] (M' : LieModel G' ξ' E') (j : E →+ E'), (∀ v, (M'.pt (j v)).left ≫ φ = spMap (dualMap i) ≫ (M.pt v).left) → ∀ q' : Cpt ξ', ∃ (r : ℕ) (B : Module.Basis (Fin r) Ω E) (B' : Module.Basis (Fin r) Ω' E') (v : Fin r → (epsAt (X.fromSpecStalk (f q'.1)) ⟶ G)) (v' : Fin r → (epsAt (X'.fromSpecStalk q'.1) ⟶ G')), (∀ k, B' k = j (B k)) ∧ M.lat ⟨f q'.1, hd.specializes q'⟩ = Submodule.span (regAt ξ ⟨f q'.1, hd.specializes q'⟩) (Set.range B) ∧ M'.lat q' = Submodule.span (regAt ξ' q') (Set.range B') ∧ (∀ k, M.Extends ⟨f q'.1, hd.specializes q'⟩ (B k) (v k)) ∧ (∀ k, M'.Extends q' (B' k) (v' k)) ∧ ∀ k, (v' k).left ≫ φ = spMap (dualMap (f.stalkMap q'.1).hom) ≫ (v k).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LiePull.frame | exact GlobalTheory.CompanionTheory.Ar.LiePull.frame | (intros; apply GlobalTheory.CompanionTheory.Ar.LiePull.frame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.T.arith_variety_prime_torsion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω ∧ ∃ x : Spec (CommRingCat.of (CR O y c')) ⟶ 𝔐.X, spMap (algebraMap (CR O y c') Ω) ≫ x = 𝔐.ξ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.ChartFacts.chartRing_over_place_facts | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.ChartFacts.chartRing_over_place_facts | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.ChartFacts.chartRing_over_place_facts <;> assumption)
end
