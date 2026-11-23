module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle456
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle491
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle464
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle488
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle493
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepMetricSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleRationalExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle435
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle465
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominanceOfWeylCharacterCoeff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightPolynomialTraceIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle494
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle480
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430

@[expose] public section

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

theorem _root_.GlobalTheory.T.points_eq_iff_same_torus_orbit : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y y' : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z z' : (Σ k, Bk n k) → ℂ),
    IsUnder (PtsOver.map i rfl _ y) z → IsUnder (PtsOver.map i rfl _ y') z' → (y = y' ↔ SameOrbit z z') := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.Orbit.eq_iff_sameOrbit | exact GlobalTheory.CompanionTheory.MixZ.Orbit.eq_iff_sameOrbit | (intros; apply GlobalTheory.CompanionTheory.MixZ.Orbit.eq_iff_sameOrbit <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

theorem _root_.GlobalTheory.T.frames_sum_by_first_vector : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞), ∑' X : framesOne σ J n, f X.1 = ∑' Y : framesE σ J (0 : Matrix (Fin n) (Fin n) E), ∑' a : Fin 1 → Fin n → E, f (consA a Y.1) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.FrOne.tsum_framesOne | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.FrOne.tsum_framesOne | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.FrOne.tsum_framesOne <;> assumption)
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

theorem sameOrbit_of_segre_eq {K : Type*} [Fintype K] {κ : K → Type*} [∀ k, Fintype (κ k)]
    {z z' : (Σ k, κ k) → ℂ} (hz : ∀ k, ∃ a, z ⟨k, a⟩ ≠ 0) (h : segre z = segre z') :
    SameOrbit z z' := by
  classical
  choose a ha using hz
  have hs : ∀ b : ∀ k, κ k, ∏ k, z ⟨k, b k⟩ = ∏ k, z' ⟨k, b k⟩ := fun b => congrFun h b
  have hpa : ∏ k, z ⟨k, a k⟩ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => ha k
  have ha' : ∀ k, z' ⟨k, a k⟩ ≠ 0 := fun k => by
    have h' : ∏ k, z' ⟨k, a k⟩ ≠ 0 := hs a ▸ hpa
    exact Finset.prod_ne_zero_iff.1 h' k (Finset.mem_univ _)
  refine ⟨fun k => z ⟨k, a k⟩ / z' ⟨k, a k⟩, fun k => div_ne_zero (ha k) (ha' k), ?_⟩
  funext p
  rcases p with ⟨k, j⟩
  show z ⟨k, j⟩ = z ⟨k, a k⟩ / z' ⟨k, a k⟩ * z' ⟨k, j⟩
  have split : ∀ w : (Σ k, κ k) → ℂ, ∏ l, w ⟨l, Function.update a k j l⟩ =
      w ⟨k, j⟩ * ∏ l ∈ Finset.univ.erase k, w ⟨l, a l⟩ := by
    intro w
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
    congr 1
    · simp
    · exact Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  have split0 : ∀ w : (Σ k, κ k) → ℂ, ∏ l, w ⟨l, a l⟩ =
      w ⟨k, a k⟩ * ∏ l ∈ Finset.univ.erase k, w ⟨l, a l⟩ := fun w =>
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)).symm
  have e1 := hs (Function.update a k j)
  rw [split z, split z'] at e1
  have e2 := hs a
  rw [split0 z, split0 z'] at e2
  have hP : ∏ l ∈ Finset.univ.erase k, z ⟨l, a l⟩ ≠ 0 := by
    rw [split0 z] at hpa
    exact right_ne_zero_of_mul hpa
  rw [div_mul_eq_mul_div, eq_div_iff (ha' k)]
  apply mul_right_cancel₀ hP
  linear_combination z' ⟨k, a k⟩ * e1 - z' ⟨k, j⟩ * e2

theorem finsum_fibre_eq (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n)
    [IsClosedImmersion i] (D : ℕ) (Ψ : LinProj n D) (N : Pol n)
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (ptIdeal (i (genericPoint X))) (D + 1))
    (hΨ : IsGoodProj (ptIdeal (i (genericPoint X))) Ψ) {ι : Type}
    (e : ι → OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ))
    (Γ : ι → (Fin D → ℂ) → (Σ k, Bk n k) → ℂ) (S : ι → Set (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀))
    (hpc : ∀ l, IsPiece i Ψ N (e l) (Γ l)) (hS : ∀ l, S l ⊆ (e l).source)
    (hd : Pairwise (Function.onFun Disjoint S)) (v : Fin D → ℂ)
    (hcov : ∀ z ∈ mcPts (ptIdeal (i (genericPoint X))), Ψ (segre z) = Fin.cons 1 v →
        ∃ y, Over i y z ∧ y ∈ ⋃ l, S l)
    (h : (((k : Fin (m + 1)) → Bk n k) → ℂ) → ℝ) (T : ι → ℝ)
    (hT : ∀ l, v ∈ (e l) '' S l → h (segre (Γ l v)) = T l) :
    ∑ᶠ w ∈ fibre (ptIdeal (i (genericPoint X))) Ψ v, h w =
      ∑' l, ((e l) '' S l).indicator (fun _ => T l) v := by
  classical
  set P := ptIdeal (i (genericPoint X)) with hPdef
  let Lv : Set ι := {l | v ∈ (e l) '' S l}
  let f : ι → (((k : Fin (m + 1)) → Bk n k) → ℂ) := fun l => segre (Γ l v)
  have hy : ∀ l ∈ Lv, (e l).symm v ∈ S l ∧ v ∈ (e l).target := by
    rintro l ⟨y, hyS, rfl⟩
    exact ⟨by rw [(e l).left_inv (hS l hyS)]; exact hyS, (e l).map_source (hS l hyS)⟩
  have hpc' : ∀ l ∈ Lv, Over i ((e l).symm v) (Γ l v) ∧ Γ l v ∈ mcPts P ∧
      Ψ (segre (Γ l v)) = Fin.cons 1 v := by
    intro l hl
    obtain ⟨_, _, hp⟩ := hpc l
    obtain ⟨h1, h2, h3, -⟩ := hp v (hy l hl).2
    exact ⟨h1, h2, h3⟩
  have himg : fibre P Ψ v = f '' Lv := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl, hzv⟩
      obtain ⟨y, hyz, hyS⟩ := hcov z hz hzv
      obtain ⟨l, hl⟩ := Set.mem_iUnion.1 hyS
      have hys := hS l hl
      have hvt : (e l) y ∈ (e l).target := (e l).map_source hys
      obtain ⟨_, _, hp⟩ := hpc l
      obtain ⟨o1, o2, o3, -⟩ := hp ((e l) y) hvt
      rw [(e l).left_inv hys] at o1
      have hso : SameOrbit z (Γ l ((e l) y)) :=
        (GlobalTheory.CompanionTheory.MixZ.Orbit.eq_iff_sameOrbit m n X i y y z _ hyz o1).1 rfl
      have hvv : v = (e l) y := by
        have r1 := ratios_of_proj Ψ hzv
        have r2 := ratios_of_proj Ψ o3
        have r3 := ratios_eq_of_sameOrbit Ψ hso (by rw [o3]; simp)
        rw [← r1, r3, r2]
      refine ⟨l, ⟨y, hl, hvv.symm⟩, ?_⟩
      show segre (Γ l v) = segre z
      rw [hvv]
      obtain ⟨c, hc, hzc⟩ := hso
      have hseg := segre_orbit hzc
      have h1 : (∏ k, c k) = 1 := by
        have h0 := congrArg (fun u => u 0) (congrArg Ψ hseg)
        simp only [map_smul, hzv, o3, Pi.smul_apply, Fin.cons_zero, smul_eq_mul, mul_one] at h0
        exact h0.symm
      rw [hseg, h1, one_smul]
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨_, h2, h3⟩ := hpc' l hl
      exact ⟨Γ l v, h2, rfl, h3⟩
  have hinj : Set.InjOn f Lv := by
    intro l hl l' hl' hll
    obtain ⟨o1, o2, -⟩ := hpc' l hl
    obtain ⟨o1', -, -⟩ := hpc' l' hl'
    have hso := sameOrbit_of_segre_eq o2.1 hll
    have hyy := (GlobalTheory.CompanionTheory.MixZ.Orbit.eq_iff_sameOrbit m n X i _ _ _ _ o1 o1').2 hso
    by_contra hne
    exact Set.disjoint_left.1 (hd hne) (hy l hl).1 (by rw [hyy]; exact (hy l' hl').1)
  have hfin : (fibre P Ψ v).Finite := ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite _ _ _ _ Ψ hP hΨ v
  have hLfin : Lv.Finite := Set.Finite.of_finite_image (himg ▸ hfin) hinj
  rw [himg, finsum_mem_image hinj]
  have hind : ∀ l, ((e l) '' S l).indicator (fun _ => T l) v = Lv.indicator T l := by
    intro l
    by_cases hl : l ∈ Lv
    · have hl' : v ∈ (e l) '' S l := hl
      simp [hl, hl']
    · have hl' : v ∉ (e l) '' S l := hl
      simp [hl, hl']
  simp_rw [hind]
  rw [tsum_eq_finsum (hLfin.subset Set.support_indicator_subset), ← finsum_mem_def]
  exact finsum_mem_congr rfl fun l hl => hT l hl

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

theorem exists_form_of_mem_open : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (U : X.Opens), genericPoint X ∈ U → ∃ (j : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog j a ∧
      j ∉ ptIdeal (i (genericPoint X)) ∧ ∀ (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ),
        GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z → eval z (map (Int.castRingHom ℂ) j) ≠ 0 → y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ U := by
  intro m n X _ i _ U hU
  classical
  have hx : i (genericPoint X) ∈ mchart (ptChart (i (genericPoint X))) :=
    Set.mem_iInter.2 fun k => mem_ptChart _ k
  have hcl : IsClosed (i '' (U : Set X)ᶜ) :=
    i.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl
  let V : (MP ℤ m n).Opens := ⟨(i '' (U : Set X)ᶜ)ᶜ, hcl.isOpen_compl⟩
  have hV : i (genericPoint X) ∈ V := by
    rintro ⟨x, hxU, hxe⟩
    exact hxU (i.isClosedEmbedding.injective hxe ▸ hU)
  obtain ⟨g, hgV, hgx⟩ := (SmoothRep.gen m n (ptChart (i (genericPoint X)))).1.exists_basicOpen_le ⟨_, hV⟩ hx
  obtain ⟨F0, rfl⟩ := ExRat.dehomog_surjective _ g
  obtain ⟨a, F, hF, e⟩ := ExRat.exists_homog (ptChart (i (genericPoint X))) F0
  rw [← e] at hgV hgx
  have hm := homog_mul hF (ExRat.isMultiHomog_mono (ptChart (i (genericPoint X))) 1)
  refine ⟨F * ExRat.mono (ptChart (i (genericPoint X))) 1, _, hm, ?_, ?_⟩
  · rw [mem_ptIdeal_iff_aeval_ptCoord m n _ _ _ hm, FnForm.aeval_ptCoord_eq_mul _ _ hx hm]
    simp only [ptCoord_ptChart, one_pow, Finset.prod_const_one, one_mul, map_mul, ExRat.dehomog_mono, mul_one]
    exact (Scheme.evaluation_ne_zero_iff_mem_basicOpen _ _ hx _).2 hgx
  · intro y z hyz hne
    have hz : ∀ k, z ⟨k, ptChart (i (genericPoint X)) k⟩ ≠ 0 := by
      intro k h0
      apply hne
      have : eval z (map (Int.castRingHom ℂ) (ExRat.mono (ptChart (i (genericPoint X))) 1)) = 0 := by
        simp only [ExRat.mono, Pi.one_apply, pow_one, map_prod, map_X]
        exact Finset.prod_eq_zero (Finset.mem_univ k) ((eval_X _).trans h0)
      rw [map_mul, map_mul, this, mul_zero]
    have hF0 : eval z (map (Int.castRingHom ℂ) F) ≠ 0 := by
      intro h0
      apply hne
      rw [map_mul, map_mul, h0, zero_mul]
    have hw : PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart (ptChart (i (genericPoint X)))) :=
      mem_ptsIn.2 (Set.mem_iInter.2 fun k => mem_ptsIn.1 ((hyz k _).1.2 (hz k)))
    have hev : ev (mpStr ℤ m n) σ₀ _ (dehomog (ptChart (i (genericPoint X))) F) (PtsOver.map i rfl _ y) ≠ 0 := by
      rw [GlobalTheory.T.dehomogenized_eval_eq_ratio m n _ F a hF _ z hyz hw]
      exact div_ne_zero hF0 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k))
    have hb := mem_ptsIn.1 ((mem_ptsIn_basicOpen hw _).2 hev)
    have hp := hgV hb
    rw [mem_ptsIn]
    by_contra h
    exact hp ⟨_, h, rfl⟩

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCount.Tope

theorem _root_.GlobalTheory.T.dominance_of_weyl_character_coeff : ∀ {n : ℕ} (lam : Fin n → ℤ), Antitone lam → ∀ p : LP n, p * altL (delZ n) ^ 2 = pPL n * altL (lam + delZ n) ^ 2 →
    ∀ μ, p.coeff μ ≠ 0 → DomLE (wtR μ) (m0 lam) := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.DomA.domLE_of_mul_eq | exact GlobalTheory.CompanionTheory.RealCountG.DomA.domLE_of_mul_eq | (intros; apply GlobalTheory.CompanionTheory.RealCountG.DomA.domLE_of_mul_eq <;> assumption)
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCount.Tope

theorem _root_.GlobalTheory.T.weight_polynomial_trace_identity : ∀ {n : ℕ} (lam : Fin n → ℤ) (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T →
    (⨆ μ, wtDual E μ) = ⊤ → iSupIndep (wtDual E) → ∀ s : Finset (Fin n → ℤ), (∀ μ, wtDual E μ ≠ ⊥ → μ ∈ s) →
      cPoly s (fun μ => trOn (wtDual E μ) (dualT E 1 : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ))) * altL (delZ n) ^ 2 =
          pPL n * altL (lam + delZ n) ^ 2 ∧
        cPoly s (fun μ => trOn (wtDual E μ) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ))) * frL n (altL (delZ n)) =
          pPL n * frL n (altL (lam + delZ n)) := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.Tope.Ident.lefK_laurent_ident | exact GlobalTheory.CompanionTheory.RealCount.Tope.Ident.lefK_laurent_ident | (intros; apply GlobalTheory.CompanionTheory.RealCount.Tope.Ident.lefK_laurent_ident <;> assumption)
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

theorem _root_.GlobalTheory.T.clifford_vector_spin_weight : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c →
    ∀ q : ι → ℂ, (∀ a b, a < b → c b a *ᵥ q = 0) →
    (∀ a, spinM c a a *ᵥ q = ((-(rhoV n a) : ℝ) : ℂ) • q) ∧ ∀ a b, a < b → spinM c b a *ᵥ q = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.spinM_vacuum_lowest | exact GlobalTheory.CompanionTheory.RealCount.spinM_vacuum_lowest | (intros; apply GlobalTheory.CompanionTheory.RealCount.spinM_vacuum_lowest <;> assumption)
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

private theorem tendsto_mul_zero_of_tendsto_zero_of_mem_compact {K : Type} [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] {L : Set K} (hL : IsCompact L) {f g : ℕ → K}
    (hf : Filter.Tendsto f Filter.atTop (nhds 0)) (hg : ∀ j, g j ∈ L) :
    Filter.Tendsto (fun j => f j * g j) Filter.atTop (nhds 0) := by
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨V, hVU, hVo, h0V⟩ := mem_nhds_iff.mp hU
  have hsub : ({0} : Set K) ×ˢ L ⊆ (fun q : K × K => q.1 * q.2) ⁻¹' V := by
    rintro ⟨x, y⟩ ⟨hx, -⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    show 0 * y ∈ V
    rw [zero_mul]
    exact h0V
  obtain ⟨u, w, hu, -, h0u, hLw, huw⟩ :=
    generalized_tube_lemma isCompact_singleton hL (hVo.preimage continuous_mul) hsub
  have hev : ∀ᶠ j in Filter.atTop, f j ∈ u := hf (hu.mem_nhds (h0u (Set.mem_singleton 0)))
  filter_upwards [hev] with j hj
  exact hVU (huw (Set.mk_mem_prod hj (hLw (hg j))))

theorem GlobalTheory.CompanionTheory.AvgFree.not_linearIndependent_of_near {K : Type} [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] (S : Finset (Kˣ × K))
    (hS : ∀ p ∈ S, p.2 ≠ 0 ∧ Filter.Tendsto (fun j : ℕ => p.2 * (p.1 : K) ^ j) Filter.atTop (nhds 0))
    {O L : Set K} (hO : IsCompact O) (hL : IsCompact L) {n M : ℕ} (X : Fin n → Fin M → K)
    (hX : ∀ j : ℕ, ∃ p ∈ S, ∃ (l : Fin n) (a : Fin n → K), (∀ i, a i ∈ O) ∧ a l = 1 ∧
      ∀ k, ∑ i, X i k * a i ∈ (fun x => (p.1 : K) ^ j * x) '' L) :
    ¬ LinearIndependent K X := by
  classical
  intro hli
  choose p hpS l a haO hal hmem using hX
  choose w hwL hweq using hmem
  obtain ⟨⟨p₀, l₀⟩, hinf⟩ := Finite.exists_infinite_fiber (fun j : ℕ => ((⟨p j, hpS j⟩ : S), l j))
  set J := (fun j : ℕ => ((⟨p j, hpS j⟩ : S), l j)) ⁻¹' {(p₀, l₀)} with hJdef
  have hJ : Set.Infinite J := Set.infinite_coe_iff.mp hinf
  have hJp : ∀ j ∈ J, p j = (p₀ : Kˣ × K) ∧ l j = l₀ := by
    intro j hj
    have h := Set.mem_singleton_iff.mp (Set.mem_preimage.mp hj)
    exact ⟨congrArg Subtype.val (Prod.ext_iff.mp h).1, (Prod.ext_iff.mp h).2⟩
  haveI hNe : (Filter.atTop ⊓ Filter.principal J).NeBot := by
    have h := Nat.frequently_atTop_iff_infinite.mpr hJ
    exact Filter.frequently_iff_neBot.mp h
  have hcomp : IsCompact (Set.pi Set.univ (fun _ : Fin n => O)) := isCompact_univ_pi (fun _ => hO)
  have hin : Filter.Tendsto a (Filter.atTop ⊓ Filter.principal J)
      (Filter.principal (Set.pi Set.univ (fun _ : Fin n => O))) :=
    Filter.tendsto_principal.mpr (Filter.Eventually.of_forall fun j i _ => haO j i)
  obtain ⟨a₀, -, hclus⟩ := hcomp hin
  have hp₀ := hS _ p₀.2
  have ha₀l : a₀ l₀ = 1 := by
    have hC : IsClosed {x : Fin n → K | x l₀ = 1} := isClosed_eq (continuous_apply l₀) continuous_const
    have hle : Filter.map a (Filter.atTop ⊓ Filter.principal J) ≤ Filter.principal {x : Fin n → K | x l₀ = 1} := by
      refine Filter.tendsto_principal.mpr ?_
      refine Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall fun j hj => ?_)
      show a j l₀ = 1
      rw [← (hJp j hj).2]
      exact hal j
    have hcl := hclus.mono hle
    rw [← mem_closure_iff_clusterPt, hC.closure_eq] at hcl
    exact hcl
  have hzero : ∀ k, p₀.1.2 * ∑ i, X i k * a₀ i = 0 := by
    intro k
    have hcont : Continuous (fun x : Fin n → K => p₀.1.2 * ∑ i, X i k * x i) := by
      fun_prop
    have htend : Filter.Tendsto (fun j => p₀.1.2 * ∑ i, X i k * a j i) (Filter.atTop ⊓ Filter.principal J) (nhds 0) := by
      have h0 := (tendsto_mul_zero_of_tendsto_zero_of_mem_compact hL hp₀.2 (fun j => hwL j k)).mono_left
        (inf_le_left : Filter.atTop ⊓ Filter.principal J ≤ Filter.atTop)
      refine h0.congr' ?_
      refine Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall fun j hj => ?_)
      show p₀.1.2 * (p₀.1.1 : K) ^ j * w j k = p₀.1.2 * ∑ i, X i k * a j i
      have hw := hweq j k
      simp only at hw
      rw [← hw, (hJp j hj).1, mul_assoc]
    have hcl := hclus.map hcont.continuousAt (Filter.tendsto_map'_iff.mpr htend)
    exact eq_of_nhds_neBot hcl
  have hsum : ∑ i, (p₀.1.2 * a₀ i) • X i = 0 := by
    ext k
    rw [Finset.sum_apply, Pi.zero_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← hzero k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h0 := Fintype.linearIndependent_iff.mp hli (fun i => p₀.1.2 * a₀ i) hsum l₀
  rw [ha₀l, mul_one] at h0
  exact hp₀.1 h0

theorem GlobalTheory.CompanionTheory.AvgFree.free_tuple_mem_goodT : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (O : Subring (Fv F v ⊗[F] E)) (S : Finset ((Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E))), IsOrdData (Fv F v) σ b lv O S → ∀ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) → IsOpen (L : Set (Fv F v ⊗[F] E)) → ∀ (n M : ℕ), tupIn (Fv F v) (L : Set (Fv F v ⊗[F] E)) ∩ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} ⊆ ⋃ j, (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) := by
  intro F E _ _ _ _ _ σ hσ d b v lv hv O S hOrd L hLc hLo n M X hX
  obtain ⟨hXin, hXli⟩ := hX
  by_contra hnot
  simp only [Set.mem_iUnion, not_exists] at hnot
  refine GlobalTheory.CompanionTheory.AvgFree.not_linearIndependent_of_near S
    (fun p hp => ⟨(hOrd.2.2.2.1 p hp).2.1, (hOrd.2.2.2.1 p hp).2.2.2.1⟩) hOrd.1 hLc X ?_ hXli
  intro j
  have hmem : X ∈ ⋃ p ∈ S, nearNF (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) (p.1 : Fv F v ⊗[F] E) j := by
    by_contra h'
    exact hnot j ⟨hXin, h'⟩
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨p, hp, -, l, a, haO, hal, hk⟩ := hmem
  exact ⟨p, hp, l, a, haO, hal, hk⟩
end
