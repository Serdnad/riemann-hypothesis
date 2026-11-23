module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle464
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle492
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalChartSheetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle493
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualWeightSpacesSpan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCliffordLowestVector
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle480
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import Mathlib.Order.CompletePartialOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle217
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle003
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430

@[expose] public section

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

theorem _root_.GlobalTheory.T.rational_section_log_norm_on_sheet : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : GlobalTheory.HermLB (mpStr ℤ m n)) (A : HermLine (Bk n)) (X : Scheme.{0}) [IsIntegral X]
    (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (r : (M.restr i).B.ι → X.functionFieldˣ) (hr : IsRatSec (M.restr i).B r)
    (f g : Pol n), IsRatSectionOn (ptIdeal (i (genericPoint X))) A f g → RatOf M A r f g →
    ∀ (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z →
      eval z (map (Int.castRingHom ℂ) f) ≠ 0 → eval z (map (Int.castRingHom ℂ) g) ≠ 0 →
      y ∈ offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr) ∧
      GlobalTheory.Cartier.logNorm ((M.restr i).φ σ₀) r y = logNormRat A f g z := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.value_of_ne_zero | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.value_of_ne_zero | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.value_of_ne_zero <;> assumption)
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

theorem _root_.GlobalTheory.T.sheet_density_log_norm_formula : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (P : Ideal (Pol n)) (D : ℕ) (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D)
    (B A : HermLine (Bk n)) (f g : Pol n), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (D + 1) → IsGoodProj P Ψ → IsSmoothHerm B →
    IsRatSectionOn P A f g → ∀ᵐ v : Fin D → ℂ, ∀ w γ, IsSheet P Ψ v w γ →
      sheetDensity P Ψ (pot fun _ : Fin D => B) (logNormRat A f g) v w =
        logNormRat A f g (γ v) * maDensity (fun _ y' => Real.log (B.h (γ y'))) v := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.sheetDensity_eq_of_isSheet | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.sheetDensity_eq_of_isSheet | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.sheetDensity_eq_of_isSheet <;> assumption)
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

theorem _root_.GlobalTheory.T.local_chart_sheet_decomposition : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (Nh : GlobalTheory.HermLB (mpStr ℤ m n)) (B : HermLine (Bk n)), IsHermRep Nh B → IsSmoothHerm B →
    ∀ (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
      [SecondCountableTopology (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)]
      (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D) (N : Pol n)
      (e : OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ)) (Γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ),
      GlobalTheory.CompanionTheory.MixZ.ArchEq.IsPiece i Ψ N e Γ →
      ContinuousOn (maDensity (fun _ y' => Real.log (B.h (Γ y')))) e.target ∧
      ∀ ε : ℤˣ, (((Nh.restr i).φ σ₀).chernPart D ε).restrict e.source =
        ((volume.restrict e.target).withDensity fun v =>
          ENNReal.ofReal (((ε : ℤ) : ℝ) * maDensity (fun _ y' => Real.log (B.h (Γ y'))) v)).map e.symm := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.Dens.piece_density | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.Dens.piece_density | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.Dens.piece_density <;> assumption)
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

theorem _root_.GlobalTheory.T.spin_gl_relations_adjoint : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c →
    Formalism.REAL.GlRel (spinM c) ∧ ∀ a b, (spinM c a b)ᴴ = spinM c b a := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.SpinRel.spinRel | exact GlobalTheory.CompanionTheory.RealCount.SpinRel.spinRel | (intros; apply GlobalTheory.CompanionTheory.RealCount.SpinRel.spinRel <;> assumption)
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCount.Tope

theorem _root_.GlobalTheory.T.dual_weight_spaces_span : ∀ {n : ℕ} (E : KMod n), (⨆ μ, wtDual E μ) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.Tope.iSup_wtDual_eq_top | exact GlobalTheory.CompanionTheory.RealCount.Tope.iSup_wtDual_eq_top | (intros; apply GlobalTheory.CompanionTheory.RealCount.Tope.iSup_wtDual_eq_top <;> assumption)
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

theorem _root_.GlobalTheory.T.exists_clifford_lowest_vector : ∀ n : ℕ, ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (c : Fin n → Fin n → Matrix ι ι ℂ),
    IsCliff c ∧ ∃ q : ι → ℂ, q ≠ 0 ∧ ∀ a b, a < b → c b a *ᵥ q = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CliffModel.exists_cliff_model | exact GlobalTheory.CompanionTheory.CliffModel.exists_cliff_model | (intros; apply GlobalTheory.CompanionTheory.CliffModel.exists_cliff_model <;> assumption)
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

namespace GlobalTheory.CompanionTheory.AvgFree

theorem exists_lattice_of_compact {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (O : Subring K) (hOc : IsCompact (O : Set K)) (hOo : IsOpen (O : Set K)) {C : Set K} (hC : IsCompact C) :
    ∃ L : Submodule O K, IsCompact (L : Set K) ∧ IsOpen (L : Set K) ∧ C ⊆ (L : Set K) := by
  classical
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x : K => (fun y => y - x) ⁻¹' (O : Set K))
    (fun x => hOo.preimage (continuous_id.sub continuous_const))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simpa using O.zero_mem⟩)
  let s : Finset K := insert 1 t
  let L : Submodule O K := Submodule.span O (s : Set K)
  have h1 : (1 : K) ∈ L := Submodule.subset_span (by simp [s])
  have hO : ∀ a ∈ O, a ∈ L := fun a ha => by
    have := L.smul_mem (⟨a, ha⟩ : O) h1
    simpa [Subring.smul_def] using this
  refine ⟨L, ?_, ?_, ?_⟩
  · haveI : CompactSpace O := isCompact_iff_compactSpace.1 hOc
    have hr : (L : Set K) = Set.range (fun c : s → O => ∑ i, (c i : K) * (i : K)) := by
      ext x
      have hs : (s : Set K) = Set.range (Subtype.val : s → K) := by simp
      change x ∈ Submodule.span O (s : Set K) ↔ _
      rw [hs, Submodule.mem_span_range_iff_exists_fun]
      rfl
    rw [hr]
    refine isCompact_range ?_
    fun_prop
  · have hopen : IsOpen ((L.toAddSubgroup : AddSubgroup K) : Set K) := by
      refine AddSubgroup.isOpen_mono (H₁ := O.toAddSubgroup) (fun a ha => hO a ha) hOo
    exact hopen
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    have hyL : y ∈ L := Submodule.subset_span (by simp [s, hy])
    have : x = (x - y) + y := by ring
    rw [this]
    exact L.add_mem (hO _ hxy) hyL

end GlobalTheory.CompanionTheory.AvgFree

theorem GlobalTheory.CompanionTheory.AvgFree.exists_lattice_tupIn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (O : Subring (Fv F v ⊗[F] E)), IsCompact (O : Set (Fv F v ⊗[F] E)) → IsOpen (O : Set (Fv F v ⊗[F] E)) → ∀ (n M : ℕ) (A : Set (Fin n → Fin M → (Fv F v ⊗[F] E))), IsCompact A → ∃ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) ∧ IsOpen (L : Set (Fv F v ⊗[F] E)) ∧ A ⊆ tupIn (Fv F v) (L : Set (Fv F v ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hσ v O hOc hOo n M A hA
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  obtain ⟨a1, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  have hC : IsCompact (⋃ i : Fin n, ⋃ k : Fin M, (fun X : Fin n → Fin M → Fv F v ⊗[F] E => X i k) '' A) :=
    isCompact_iUnion fun i => isCompact_iUnion fun k => hA.image (by fun_prop)
  obtain ⟨L, h1, h2, h3⟩ := exists_lattice_of_compact O hOc hOo hC
  refine ⟨L, h1, h2, fun X hX i k => h3 ?_⟩
  exact Set.mem_iUnion₂.2 ⟨i, k, X, hX, rfl⟩
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

namespace GlobalTheory.CompanionTheory.AvgFree

section Clopen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace (R ⊗[F] E)] [IsTopologicalRing (R ⊗[F] E)]

theorem isOpen_tupIn_of_isOpen {M n : ℕ} {L : Set (R ⊗[F] E)} (hL : IsOpen L) :
    IsOpen (tupIn (M := M) (n := n) R L) := by
  have : tupIn (M := M) (n := n) R L = ⋂ i, ⋂ k, {X | X i k ∈ L} := by
    ext X
    simp [tupIn]
  rw [this]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => ?_
  exact hL.preimage (show Continuous (fun X : Fin n → Fin M → R ⊗[F] E => X i k) from
    (continuous_apply k).comp (continuous_apply i))

theorem isOpen_unit_pow_image {L : Set (R ⊗[F] E)} (hL : IsOpen L) (t : (R ⊗[F] E)ˣ) (j : ℕ) :
    IsOpen ((fun x => (t : R ⊗[F] E) ^ j * x) '' L) := by
  have : (fun x => (t : R ⊗[F] E) ^ j * x) '' L =
      (fun x => ((t⁻¹ ^ j : (R ⊗[F] E)ˣ) : R ⊗[F] E) * x) ⁻¹' L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h : ((t⁻¹ ^ j : (R ⊗[F] E)ˣ) : R ⊗[F] E) * ((t : R ⊗[F] E) ^ j * y) = y := by
        rw [← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel,
          Units.val_one, one_mul]
      simpa only [Set.mem_preimage, h] using hy
    · intro hx
      refine ⟨_, hx, ?_⟩
      show (t : R ⊗[F] E) ^ j * (((t⁻¹ ^ j : (R ⊗[F] E)ˣ) : R ⊗[F] E) * x) = x
      rw [← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, mul_inv_cancel,
        Units.val_one, one_mul]
  rw [this]
  exact hL.preimage (continuous_const.mul continuous_id)

theorem isOpen_nearNF {M n : ℕ} (O : Set (R ⊗[F] E)) {L : Set (R ⊗[F] E)} (hL : IsOpen L)
    (t : (R ⊗[F] E)ˣ) (j : ℕ) :
    IsOpen (nearNF (M := M) (n := n) R O L (t : R ⊗[F] E) j) := by
  have hT := isOpen_unit_pow_image R hL t j
  have : nearNF (M := M) (n := n) R O L (t : R ⊗[F] E) j =
      tupIn R L ∩ ⋃ (l : Fin n), ⋃ (a : Fin n → R ⊗[F] E), ⋃ (_ : (∀ i, a i ∈ O) ∧ a l = 1),
        ⋂ k, {X : Fin n → Fin M → R ⊗[F] E | ∑ i, X i k * a i ∈
          (fun x => (t : R ⊗[F] E) ^ j * x) '' L} := by
    ext X
    simp only [nearNF, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter,
      exists_prop]
    constructor
    · rintro ⟨h1, l, a, h2, h3, h4⟩
      exact ⟨h1, l, a, ⟨h2, h3⟩, h4⟩
    · rintro ⟨h1, l, a, ⟨h2, h3⟩, h4⟩
      exact ⟨h1, l, a, h2, h3, h4⟩
  rw [this]
  refine (isOpen_tupIn_of_isOpen R hL).inter ?_
  refine isOpen_iUnion fun l => isOpen_iUnion fun a => isOpen_iUnion fun _ => ?_
  refine isOpen_iInter_of_finite fun k => hT.preimage ?_
  fun_prop

theorem isClosed_nearNF [T2Space (R ⊗[F] E)] {M n : ℕ} {O L : Set (R ⊗[F] E)} (hO : IsCompact O)
    (hL : IsCompact L) (t : R ⊗[F] E) (j : ℕ) :
    IsClosed (nearNF (M := M) (n := n) R O L t j) := by
  have hT : IsClosed ((fun x => t ^ j * x) '' L) :=
    (hL.image (continuous_const.mul continuous_id)).isClosed
  let C : Fin n → Set ((Fin n → Fin M → R ⊗[F] E) × (Fin n → R ⊗[F] E)) := fun l =>
    (tupIn R L ×ˢ Set.pi Set.univ fun _ => O) ∩
      ({p | p.2 l = 1} ∩ ⋂ k, {p | ∑ i, p.1 i k * p.2 i ∈ (fun x => t ^ j * x) '' L})
  have hC : ∀ l, IsCompact (C l) := by
    intro l
    refine ((isCompact_tupIn R hL).prod (isCompact_univ_pi fun _ => hO)).inter_right ?_
    refine (isClosed_eq ?_ continuous_const).inter (isClosed_iInter fun k => hT.preimage ?_)
    · exact (continuous_apply l).comp continuous_snd
    · fun_prop
  have : nearNF (M := M) (n := n) R O L t j = ⋃ l, Prod.fst '' C l := by
    ext X
    simp only [nearNF, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨h1, l, a, h2, h3, h4⟩
      refine ⟨l, (X, a), ⟨⟨h1, fun i _ => h2 i⟩, h3, ?_⟩, rfl⟩
      exact Set.mem_iInter.2 h4
    · rintro ⟨l, ⟨X', a⟩, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
      exact ⟨h1, l, a, fun i => h2 i trivial, h3, Set.mem_iInter.1 h4⟩
  rw [this]
  exact (isCompact_iUnion fun l => (hC l).image continuous_fst).isClosed

theorem goodT_compact_open [T2Space (R ⊗[F] E)] {M n : ℕ} {O L : Set (R ⊗[F] E)} (hO : IsCompact O)
    (hLc : IsCompact L) (hLo : IsOpen L) (S : Finset ((R ⊗[F] E)ˣ × (R ⊗[F] E))) (j : ℕ) :
    IsCompact (goodT (M := M) (n := n) R O L S j) ∧ IsOpen (goodT (M := M) (n := n) R O L S j) := by
  constructor
  · refine (isCompact_tupIn R hLc).diff ?_
    exact isOpen_biUnion fun p _ => isOpen_nearNF R O hLo p.1 j
  · refine (isOpen_tupIn_of_isOpen R hLo).sdiff ?_
    exact S.finite_toSet.isClosed_biUnion fun p _ => isClosed_nearNF R hO hLc _ j

end Clopen

end GlobalTheory.CompanionTheory.AvgFree

theorem GlobalTheory.CompanionTheory.AvgFree.goodT_isClopen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (O : Subring (Fv F v ⊗[F] E)) (S : Finset ((Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E))), IsOrdData (Fv F v) σ b lv O S → ∀ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) → IsOpen (L : Set (Fv F v ⊗[F] E)) → ∀ (n M j : ℕ), IsCompact (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) ∧ IsOpen (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv O S hOS L hLc hLo n M j
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  obtain ⟨a1, -, -, a4, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a4
  exact goodT_compact_open (Fv F v) hOS.1 hLc hLo S j
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem pow_mul_mem_submodule (O : Subring (R ⊗[F] E)) (L : Submodule O (R ⊗[F] E))
    {t : R ⊗[F] E} (ht : t ∈ O) (k : ℕ) {x : R ⊗[F] E} (hx : x ∈ L) : t ^ k * x ∈ L := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    exact L.smul_mem (⟨t, ht⟩ : O) ih

theorem sum_mul_mem_submodule (O : Subring (R ⊗[F] E)) (L : Submodule O (R ⊗[F] E)) {n : ℕ}
    (x a : Fin n → R ⊗[F] E) (hx : ∀ i, x i ∈ L) (ha : ∀ i, a i ∈ O) : ∑ i, x i * a i ∈ L := by
  refine L.sum_mem fun i _ => ?_
  rw [mul_comm]
  exact L.smul_mem (⟨a i, ha i⟩ : O) (hx i)

theorem nearNF_anti (O : Subring (R ⊗[F] E)) (L : Submodule O (R ⊗[F] E))
    {t : R ⊗[F] E} (ht : t ∈ O) {M n : ℕ} {j j' : ℕ} (h : j ≤ j') :
    nearNF (M := M) (n := n) R (O : Set (R ⊗[F] E)) (L : Set (R ⊗[F] E)) t j' ⊆
      nearNF R (O : Set (R ⊗[F] E)) (L : Set (R ⊗[F] E)) t j := by
  rintro X ⟨hX, l, a, ha, hl, hk⟩
  refine ⟨hX, l, a, ha, hl, fun k => ?_⟩
  obtain ⟨y, hy, hyk⟩ := hk k
  refine ⟨t ^ (j' - j) * y, pow_mul_mem_submodule R O L ht _ hy, ?_⟩
  rw [← hyk]
  change t ^ j * (t ^ (j' - j) * y) = t ^ j' * y
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

theorem goodT_mono (O : Subring (R ⊗[F] E)) (L : Submodule O (R ⊗[F] E))
    (S : Finset ((R ⊗[F] E)ˣ × (R ⊗[F] E))) (hS : ∀ p ∈ S, (p.1 : R ⊗[F] E) ∈ O) (M n : ℕ) :
    Monotone (fun j => goodT (M := M) (n := n) R (O : Set (R ⊗[F] E)) (L : Set (R ⊗[F] E)) S j) := by
  intro j j' h X hX
  refine ⟨hX.1, fun hmem => hX.2 ?_⟩
  simp only [Set.mem_iUnion] at hmem ⊢
  obtain ⟨p, hp, hXp⟩ := hmem
  exact ⟨p, hp, nearNF_anti R O L (hS p hp) h hXp⟩

theorem goodT_free (O : Subring (R ⊗[F] E)) (L : Submodule O (R ⊗[F] E))
    (S : Finset ((R ⊗[F] E)ˣ × (R ⊗[F] E)))
    (hfix : ∀ p ∈ S, ∀ x, p.2 * x = 0 → (p.1 : R ⊗[F] E) * x = x) {M n : ℕ}
    (hdet : ∀ X : Fin n → Fin M → R ⊗[F] E, ¬ LinearIndependent (R ⊗[F] E) X →
      ∃ p ∈ S, ∃ (l : Fin n) (a : Fin n → R ⊗[F] E), (∀ i, a i ∈ O) ∧ a l = 1 ∧
        ∀ k, p.2 * ∑ i, X i k * a i = 0) (j : ℕ) :
    goodT (M := M) (n := n) R (O : Set (R ⊗[F] E)) (L : Set (R ⊗[F] E)) S j ⊆
      {X | LinearIndependent (R ⊗[F] E) X} := by
  intro X hX
  by_contra hli
  obtain ⟨p, hp, l, a, ha, hl, hk⟩ := hdet X hli
  refine hX.2 ?_
  simp only [Set.mem_iUnion]
  refine ⟨p, hp, hX.1, l, a, ha, hl, fun k => ?_⟩
  have hxL : ∑ i, X i k * a i ∈ L :=
    sum_mul_mem_submodule R O L (fun i => X i k) a (fun i => hX.1 i k) ha
  refine ⟨_, hxL, ?_⟩
  have hfx := hfix p hp _ (hk k)
  have hpow : ∀ m : ℕ, (p.1 : R ⊗[F] E) ^ m * ∑ i, X i k * a i = ∑ i, X i k * a i := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, mul_assoc, hfx, ih]
  exact hpow j

end Gen

theorem goodT_mono_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (O : Subring (Fv F v ⊗[F] E)) (S : Finset ((Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E))), IsOrdData (Fv F v) σ b lv O S → ∀ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) → IsOpen (L : Set (Fv F v ⊗[F] E)) → ∀ (n M : ℕ), Monotone (fun j => (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j)) ∧ ∀ j, (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) ⊆ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} := by
  intro F E _ _ _ _ _ σ _ d b v lv _ O S hO L _ _ n M
  obtain ⟨-, -, -, hS, hdet⟩ := hO
  exact ⟨goodT_mono (Fv F v) O L S (fun p hp => (hS p hp).1) M n,
    fun j => goodT_free (Fv F v) O L S (fun p hp => (hS p hp).2.2.1) (hdet n M) j⟩

end GlobalTheory.CompanionTheory.AvgFree
end
end

section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ModelS

theorem DR_one_of_eqv (n : ℕ) (lev : Fin n → ℕ) (f h : SmF n) (_hf : f ∈ Eqv lev f.1) (_hf1 : f.1 1 = 1)
    (hh : h ∈ Eqv lev f.1) (X : Mat n) (hX : ∀ a b, lev a < lev b → X a b = 0) :
    (DR X h).1 1 = (DR X f).1 1 * h.1 1 := by
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have dh := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth h.2.1 h1).hasFDerivAt
  have df := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth f.2.1 h1).hasFDerivAt
  have hc : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • X) X 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : Mat n)
    simp only [one_smul] at this
    exact this
  have hc0 : (1 : Mat n) = (fun t : ℝ => (1 : Mat n) + t • X) 0 := by simp
  have Dh := dh.comp_hasDerivAt_of_eq (0 : ℝ) hc hc0
  have Df := (df.comp_hasDerivAt_of_eq (0 : ℝ) hc hc0).mul_const (h.1 1)
  have hev : ∀ᶠ t : ℝ in nhds 0, (1 : Mat n) + t • X ∈ GLs n :=
    hc.continuousAt.eventually_mem (by
      have hm : (1 : Mat n) + (0 : ℝ) • X = 1 := by simp
      rw [hm]
      exact GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds h1)
  have heq : (h.1 ∘ fun t : ℝ => (1 : Mat n) + t • X) =ᶠ[nhds 0]
      fun t => (f.1 ∘ fun t : ℝ => (1 : Mat n) + t • X) t * h.1 1 := by
    filter_upwards [hev] with t ht
    have hp : (1 : Mat n) + t • X ∈ Pb lev := by
      refine ⟨ht, fun a b hab => ?_⟩
      have hne : a ≠ b := fun e => (e ▸ hab : lev a < lev a).false
      simp [hX a b hab, Matrix.one_apply_ne hne]
    have := hh _ hp 1 h1
    simpa using this
  have key := (Dh.congr_of_eventuallyEq heq.symm).unique Df
  rw [DR_apply _ _ h1, DR_apply _ _ h1]
  show fderiv ℝ h.1 1 (1 * X) = fderiv ℝ f.1 1 (1 * X) * h.1 1
  rw [one_mul]
  exact key

end GlobalTheory.CompanionTheory.ModelS
end
end
