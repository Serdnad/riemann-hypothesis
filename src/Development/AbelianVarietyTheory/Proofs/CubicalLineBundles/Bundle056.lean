module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle052
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle054
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle053
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle027
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle018
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNumberFieldDefiningCmCurveHoms
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.DiffCoord

variable {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G']

theorem isTangent_comp_hom (f : G ⟶ G') [IsMonHom f] {v : epsR R ⟶ G} (hv : IsTangent v) : IsTangent (v ≫ f) := by
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]

theorem isLieComb_comp_hom (f : G ⟶ G') [IsMonHom f] {n : ℕ} {c : Fin n → R} {v : Fin n → (epsR R ⟶ G)}
    {w : epsR R ⟶ G} (h : IsLieComb c v w) : IsLieComb c (fun i => v i ≫ f) (w ≫ f) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => u i ≫ f, fun i => ?_, ?_⟩
  · rw [Over.comp_left, Over.comp_left, hu, Category.assoc]
  · exact (map_list_prod (IsMonHom.monoidHom f (epsR R)) (List.ofFn u)).trans (by rw [List.map_ofFn]; rfl)

theorem exists_linearMap [IsCommMonObj G'] (f : G ⟶ G') [IsMonHom f] {n m : ℕ} {v : Fin n → (epsR R ⟶ G)}
    {v' : Fin m → (epsR R ⟶ G')} (hv : IsLieBasis v) (hv' : IsLieBasis v') :
    ∃ M : (Fin n → R) →ₗ[R] (Fin m → R), ∀ c w, IsLieComb c v w → IsLieComb (M c) v' (w ≫ f) := by
  choose A hA using fun i => (hv'.2 _ (isTangent_comp_hom f (hv.1 i))).exists
  refine ⟨Fintype.linearCombination R A, fun c w h => ?_⟩
  rw [Fintype.linearCombination_apply]
  exact (LieComb.lieComb_algebra R G' m v' hv'.1).2.2.1 n A _ c _ hA (isLieComb_comp_hom f h)

theorem existsUnique_isDiffOf : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P)
    (P' : Out.PolAV (Sp (𝓞 K))) (F' : GenFib P') (f : P.A ⟶ P'.A), IsMonHom f → (∃! M, F.IsDiffOf F' f M) ∧
    ∃ f₀ : F.P₀.A ⟶ F'.P₀.A, IsMonHom f₀ ∧ f₀.left ≫ F'.φ = F.φ ≫ f.left ∧
      ∀ M, F.IsDiffOf F' f M → ∀ c w, IsLieComb c F.v w → IsLieComb (M c) F'.v (w ≫ f₀) := by
  intro K _ _ P F P' F' f hf
  obtain ⟨f₀, hf₀, e⟩ := DerivZero.exists_lift_isMonHom F.fib.2.1 F'.fib.2.1 f
  have := F'.P₀.isAb.comm
  obtain ⟨M, hM⟩ := exists_linearMap f₀ F.basis F'.basis
  have hd : F.IsDiffOf F' f M := by
    rintro u c ⟨hu, w, hw, hc⟩
    refine ⟨isTangent_comp_hom f hu, w ≫ f₀, ?_, hM c w hc⟩
    unfold IsVecOver at hw ⊢
    rw [Over.comp_left, Over.comp_left, Category.assoc, e, ← Category.assoc, hw, Category.assoc]
  have hcoord : ∀ u c c', F'.IsCoord u c → F'.IsCoord u c' → c = c' := by
    rintro u c c' ⟨-, w, hw, hc⟩ ⟨-, w', hw', hc'⟩
    obtain rfl : w = w' := Over.OverMorphism.ext (F'.fib.2.1.1.hom_ext (hw.trans hw'.symm) ((Over.w _).trans (Over.w _).symm))
    exact (F'.basis.2 w ((LieComb.lieComb_algebra K _ _ F'.v F'.basis.1).2.1 c w hc)).unique hc hc'
  have huniq : ∀ N, F.IsDiffOf F' f N → N = M := fun N hN => by
    refine LinearMap.ext_on (GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K P F).2 fun c hc => ?_
    refine Submodule.span_induction (p := fun c _ => N c = M c) ?_ ?_ ?_ ?_ hc
    · rintro c ⟨u, hu⟩
      exact hcoord _ _ _ (hN u c hu) (hd u c hu)
    · simp
    · intro x y _ _ hx hy
      rw [map_add (f := _), map_add (f := _), hx, hy]
    · intro r x _ hx
      rw [← algebraMap_smul K r x, map_smul, map_smul, hx]
  refine ⟨⟨M, hd, huniq⟩, f₀, hf₀, e, fun N hN => ?_⟩
  rw [huniq N hN]
  exact hM

end GlobalTheory.CM.DiffCoord
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem isModelAt_integral_iff_mem_lieLat : ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (p : HeightOneSpectrum (𝓞 K)) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), IsModelAt A x φ p M → ∀ c : Fin x.P.g → K, (∀ m, p.valuation K (Matrix.vecMul c M⁻¹ m) ≤ 1) ↔ ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat := by
  intro K _ _ A x φ hf p M hM c
  obtain ⟨R, _, _, _, _, _, ρ, xR, φR, hg, hρ, hval, hfib, hdet, hw⟩ := hM
  letI : Algebra (𝓞 K) R := ρ.toAlgebra
  haveI : IsScalarTower (𝓞 K) R K := IsScalarTower.of_algebraMap_eq' hρ.symm
  haveI : IsLocalization p.asIdeal.primeCompl R := (range_eq_valuationRing_iff_isLocalization K p R).1 hval
  have hG : IsGrpPullback xR.P.A A.A (spMap (algebraMap (𝓞 K) R)) φR := hfib.1
  have n : IsGrpPullback x.P.A A.A (spMap (algebraMap R K) ≫ spMap (algebraMap (𝓞 K) R)) φ :=
    hf.2.1.congr (by rw [spMap_comp_spMap]; exact congrArg spMap hρ.symm) rfl
  have w : φ ≫ A.A.hom = (x.P.A.hom ≫ spMap (algebraMap R K)) ≫ spMap (algebraMap (𝓞 K) R) :=
    n.1.w.trans (Category.assoc _ _ _).symm
  have e₁ := hG.1.lift_fst _ _ w
  have e₂ := hG.1.lift_snd _ _ w
  generalize hG.1.lift _ _ w = ψ at e₁ e₂
  have hψ : IsGrpPullback x.P.A xR.P.A (spMap (algebraMap R K)) ψ := hG.cancel (e₁ ▸ n) e₂
  choose wK hwK hwK' using hw
  have hb : IsLieBasis (fun k : Fin x.P.g => xR.v (k.cast hg.symm)) := by
    have key : ∀ (m : ℕ) (h : xR.P.g = m), IsLieBasis (fun k : Fin m => xR.v (k.cast h.symm)) := by
      intro m h
      subst h
      exact xR.basis
    exact key _ hg
  have hov : ∀ k, IsVecOver (algebraMap R K) ψ (xR.v (k.cast hg.symm)) (wK k) := by
    intro k
    refine hG.1.hom_ext ?_ ?_
    · rw [Category.assoc, e₁, hwK' k, Category.assoc, points_sums_eq_products.2]
    · rw [Category.assoc, Category.assoc, e₂, Over.w (xR.v _), ← Category.assoc, Over.w (wK k)]
      exact (PolFibre.spMap_dual_hom _).symm
  obtain ⟨h1, h2⟩ := GlobalTheory.T.lieLattice_localization_modelLieAlgebra K A (GenFib.mk x.P φ hf x.v x.basis) R p.asIdeal.primeCompl xR.P.A φR ψ _ wK M
    hG hψ e₁ hb fun i => ⟨hov i, hwK i⟩
  have hU : IsUnit M.det := hdet.isUnit
  constructor
  · intro hc
    choose a ha using fun m => (hval _).2 (hc m)
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples_of_finite p.asIdeal.primeCompl a
    choose b hb' using ht
    choose s hs hs' using h1
    have hcM : c = ∑ i, Matrix.vecMul c M⁻¹ i • M i := by
      rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hU, Matrix.vecMul_one]
    refine ⟨(∏ i, s i) * t, Submonoid.mul_mem p.asIdeal.primeCompl (Submonoid.prod_mem _ fun i _ => hs i) t.2, ?_⟩
    rw [hcM, Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have e : (t : 𝓞 K) • Matrix.vecMul c M⁻¹ i = algebraMap (𝓞 K) K (b i) := by
      rw [← ha, IsScalarTower.algebraMap_apply (𝓞 K) R K, hb', Algebra.smul_def, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply]
    rw [mul_smul, ← smul_assoc (t : 𝓞 K), e, algebraMap_smul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul,
      smul_comm (s i)]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hs' i))
  · rintro ⟨s, hs, hc⟩ m
    obtain ⟨a, ha⟩ := h2 _ hc
    have e : s • Matrix.vecMul c M⁻¹ = fun i => algebraMap R K (a i) := by
      rw [← Matrix.smul_vecMul]
      erw [ha]
      rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hU, Matrix.vecMul_one]
    have e' : algebraMap (𝓞 K) K s * Matrix.vecMul c M⁻¹ m = algebraMap R K (a m) := by
      rw [← Algebra.smul_def]
      exact congrFun e m
    have h3 := (hval _).1 ⟨a m, e'.symm⟩
    rwa [map_mul, (p.valuation_eq_one_iff_notMem (K := K)).2 hs, _root_.one_mul] at h3

end GlobalTheory.LamF
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane
theorem _root_.GlobalTheory.T.exists_numberField_defining_cm_curve_homs : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (K
    : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ₀
    : K →+* ℂ), ¬ ComplexEmbedding.IsReal σ₀ → ∀ (𝔟 : ClassGroup (𝓞 K) → nonZeroDivisors (Ideal (𝓞
    K))), (∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (κ : K →+* M) (P : Out.PolAV (Sp (𝓞
    M))) (v : epsR (𝓞 M) ⟶ P.A) (L₀ : (𝓞 M →+* ℂ) → PeriodPair) (Q : ClassGroup (𝓞
    K) → Out.PolAV (Sp (𝓞 M))) (t : ∀ C, epsR (𝓞 M) ⟶ (Q C).A) (L : ClassGroup (𝓞 K) → (𝓞 M →+*
    ℂ) → PeriodPair) (δ : ClassGroup (𝓞 K) → (𝓞 M)ˣ), (∀ a, (κ a : ℂ) = σ₀ a) ∧ (P.g = 1 ∧
    IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ'
    : P'.A.left ⟶ P.A.left) (v'
    : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞
    M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u'
    : HolUnif P'.A P'.L P'.g) (w'
    : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L₀
    s').lattice ↔ z • w' ∈ u'.Λ)) ∧ (∀ C, ((Q C).g = 1 ∧ IsLieBasis ![(t C)] ∧ (∀ (R'
    : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ (Q
    C).A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' (Q C) P' φ' → IsVecOver f' φ' (t
    C) v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ (Q
    C).A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w'
    : Fin P'.g → ℂ), IsPolFibre s' (Q C) P' φ' → IsVecOver s' φ' (t
    C) v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L C s').lattice ↔ z • w' ∈ u'.Λ))) ∧ (∀ C s, (L
    C s).g₂ ^ 3 - 27 * (L C s).g₃ ^ 2 = s (δ C : 𝓞 M)) ∧ (∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ (L₀ ((algebraMap
    M ℂ).comp (algebraMap (𝓞 M) M))).lattice ↔ ∃ a : 𝓞 K, z = c * σ₀ (a : K)) ∧ ∃ β : ClassGroup (𝓞
    K) → ℂ, (∀ C, β C ≠ 0) ∧ (∀ C (x : K), (∀ b ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ (x * (b
    : K))) → ∀ z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice, β C * σ₀ x * z ∈ (L C
    ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice) ∧ ∀ C, ∀ y ∈ (𝔟 C : Ideal (𝓞
    K)), ∀ z ∈ (L C ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice, (β C)⁻¹ * σ₀ (y
    : K) * z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice) → ∃ (M
    : IntermediateField ℚ ℂ) (_ : NumberField M) (κ : K →+* M) (P : Out.PolAV (Sp (𝓞 M))) (v
    : epsR (𝓞 M) ⟶ P.A) (L₀ : (𝓞 M →+* ℂ) → PeriodPair) (Q : ClassGroup (𝓞 K) → Out.PolAV (Sp (𝓞
    M))) (t : ∀ C, epsR (𝓞 M) ⟶ (Q C).A) (L : ClassGroup (𝓞 K) → (𝓞 M →+* ℂ) → PeriodPair) (δ
    : ClassGroup (𝓞 K) → (𝓞 M)ˣ), (∀ a, (κ a : ℂ) = σ₀ a) ∧ (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R'
    : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ'
    : P'.A.left ⟶ P.A.left) (v'
    : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞
    M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u'
    : HolUnif P'.A P'.L P'.g) (w'
    : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L₀
    s').lattice ↔ z • w' ∈ u'.Λ)) ∧ (∀ C, ((Q C).g = 1 ∧ IsLieBasis ![(t C)] ∧ (∀ (R'
    : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ (Q
    C).A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' (Q C) P' φ' → IsVecOver f' φ' (t
    C) v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ (Q
    C).A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w'
    : Fin P'.g → ℂ), IsPolFibre s' (Q C) P' φ' → IsVecOver s' φ' (t
    C) v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L C s').lattice ↔ z • w' ∈ u'.Λ))) ∧ (∀ C s, (L
    C s).g₂ ^ 3 - 27 * (L C s).g₃ ^ 2 = s (δ C : 𝓞 M)) ∧ (∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ (L₀ ((algebraMap
    M ℂ).comp (algebraMap (𝓞 M) M))).lattice ↔ ∃ a : 𝓞 K, z = c * σ₀ (a : K)) ∧ ∃ β : ClassGroup (𝓞
    K) → M, (∀ C, β C ≠ 0) ∧ (∀ a : 𝓞 K, (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁
    : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ P.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁
    : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M)
    M) P Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M)
    M) ψ₁ v t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![κ (a : K)] ![t₁] (v₁ ≫
    f₁))) ∧ (∀ C (x : K), (∀ b ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K))) → (∀ (P₁ Q₁
    : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ (Q C).A.left) (v₁
    : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M)
    M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) (Q C) Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M)
    M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ (t
    C) t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![β C * κ x] ![t₁] (v₁ ≫
    f₁))) ∧ ∀ C, ∀ y ∈ (𝔟 C : Ideal (𝓞 K)), (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ (Q
    C).A.left) (ψ₁ : Q₁.A.left ⟶ P.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁
    : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) (Q C) P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M)
    M) P Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ (t C) v₁ → IsVecOver (algebraMap (𝓞 M)
    M) ψ₁ v t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![(β C)⁻¹ * κ (y : K)] ![t₁] (v₁ ≫
    f₁)) := by
  first | exact @GlobalTheory.CommonField.exists_common_field | exact GlobalTheory.CommonField.exists_common_field | (intros; apply GlobalTheory.CommonField.exists_common_field <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

namespace GlobalTheory

theorem room_neg_log_epStar (f d L M k0 S : ℝ) (hf : 1 ≤ f) (hd : 1 ≤ d) (hL : 0 ≤ L)
    (hM : 0 < M) (hk : 0 < k0) (hS : 1 ≤ S)
    (h : Real.log (M * k0) ≤ 19 * L + 3 + Real.log d) :
    0 < epStar M f S k0 ∧ epStar M f S k0 ≤ 1 ∧
      -Real.log (epStar M f S k0) ≤ 19 * L + 6 + Real.log d + f + Real.log S := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hfS : 1 ≤ f * S := one_le_mul_of_one_le_of_one_le hf hS
  have hld : 0 ≤ Real.log d := Real.log_nonneg hd
  have hlS : 0 ≤ Real.log S := Real.log_nonneg hS
  have hpi := Real.pi_gt_three
  have hD : 0 < M * (f * S + 2) * k0 * Real.log 2 := by positivity
  unfold epStar
  refine ⟨lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  rcases min_choice 1 (Real.pi / (M * (f * S + 2) * k0 * Real.log 2)) with h1 | h1 <;> rw [h1]
  · rw [Real.log_one]; linarith
  · have hMk : 0 < M * k0 := by positivity
    have e : M * (f * S + 2) * k0 * Real.log 2 = (M * k0) * ((f * S + 2) * Real.log 2) := by ring
    rw [Real.log_div (by positivity) hD.ne', e, Real.log_mul hMk.ne' (by positivity)]
    have h2 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith)
    have h3 : Real.log ((f * S + 2) * Real.log 2) ≤ Real.log (3 * f * S) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have h6 : Real.log (3 * f * S) = Real.log 3 + Real.log f + Real.log S := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    have h4 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)
    have h5 := Real.log_le_sub_one_of_pos (show (0:ℝ) < f by positivity)
    linarith

theorem room_log_radius (f r : ℕ) (d e S : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hd : 1 ≤ d)
    (he : 0 < e) (hS : 1 ≤ S) :
    0 < 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (Real.sqrt e / Real.sqrt f)) (3 * frameRadius S r / 5) ∧
    Real.log (2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (Real.sqrt e / Real.sqrt f)) (3 * frameRadius S r / 5)) =
      Real.log (1600 / 3) + Real.log r + (1 / 2) * Real.log f + (1 / 2) * Real.log S
        + 3 * Real.log ((f : ℝ) * r) + Real.log d - (1 / 2) * Real.log e := by
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hS' : (0 : ℝ) < S := by linarith
  have hd' : (0 : ℝ) < d := by linarith
  have h1 : 0 < Real.sqrt e := Real.sqrt_pos.2 he
  have h2 : 0 < Real.sqrt f := Real.sqrt_pos.2 hf'
  have h3 : 0 < Real.sqrt r := Real.sqrt_pos.2 hr'
  have h4 : 0 < Real.sqrt (S * r) := Real.sqrt_pos.2 (by positivity)
  have E : 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (Real.sqrt e / Real.sqrt f)) (3 * frameRadius S r / 5) =
      1600 / 3 * Real.sqrt r * Real.sqrt f * Real.sqrt (S * r) * ((f : ℝ) * r) ^ 3 * d / Real.sqrt e := by
    unfold ReciprocityTheory.MultiplicativeHeights.approxR d5mu frameRadius
    field_simp
    norm_num
  rw [E]
  refine ⟨by positivity, ?_⟩
  rw [Real.log_div (by positivity) h1.ne', Real.log_mul (by positivity) hd'.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) h4.ne',
    Real.log_mul (by positivity) h2.ne', Real.log_mul (by positivity) h3.ne',
    Real.log_pow, Real.log_sqrt he.le, Real.log_sqrt hf'.le, Real.log_sqrt hr'.le,
    Real.log_sqrt (by positivity), Real.log_mul hS'.ne' hr'.ne']
  push_cast
  ring

theorem room_of_constants : ∃ C0 : ℝ, 0 < C0 ∧ ∀ (f r p0 : ℕ) (d L Om M k0 S : ℝ), 1 ≤ f → 1 ≤ r → p0 ≤ r → 1 ≤ d → 0 ≤ L → 0 < M → 0 < k0 → 1 ≤ S → Real.log (M * k0) ≤ 19 * L + 3 + Real.log d → 1 ≤ frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5) ∧ ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t ≤ S → ∀ C A : ℝ, C0 ≤ C → 2 ≤ A → (Formalism.L2.LamCM.pDeg Om + (1 / 2) * Real.log (frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5))) * (s + t) + s * Real.log ((r : ℝ) * frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5)) ≤ C * ((f : ℝ) * r + L + Real.log d + |Om|) ^ A * (1 + Real.log S) * S := by
  refine ⟨3000, by norm_num, ?_⟩
  intro f r p0 d L Om M k0 S hf hr hp hd hL hM hk hS h
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hp' : (p0 : ℝ) ≤ r := by exact_mod_cast hp
  obtain ⟨he0, he1, he2⟩ := room_neg_log_epStar f d L M k0 S hf' hd hL hM hk hS h
  obtain ⟨hX0, hX⟩ := room_log_radius f r d _ S hf hr hd he0 hS
  unfold frameBasisRadius
  set X := 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (Real.sqrt (epStar M f S k0) / Real.sqrt f))
    (3 * frameRadius S r / 5) with hXdef
  clear_value X
  have hle : Real.log (epStar M f S k0) ≤ 0 := Real.log_nonpos he0.le he1
  have hn : (1 : ℝ) ≤ (f : ℝ) * r := one_le_mul_of_one_le_of_one_le hf' hr'
  have hfn : (f : ℝ) ≤ (f : ℝ) * r := le_mul_of_one_le_right (by linarith) hr'
  have hrn : (r : ℝ) ≤ (f : ℝ) * r := le_mul_of_one_le_left (by linarith) hf'
  have a1 : 0 ≤ Real.log d := Real.log_nonneg hd
  have a2 : 0 ≤ Real.log S := Real.log_nonneg hS
  have a3 : 0 ≤ Real.log (f : ℝ) := Real.log_nonneg hf'
  have a4 : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hr'
  have a5 : 0 ≤ Real.log ((f : ℝ) * r) := Real.log_nonneg hn
  have a6 : 0 ≤ Real.log (1600 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have b3 := Real.log_le_sub_one_of_pos (show (0:ℝ) < f by linarith)
  have b4 := Real.log_le_sub_one_of_pos (show (0:ℝ) < r by linarith)
  have b5 := Real.log_le_sub_one_of_pos (show (0:ℝ) < (f : ℝ) * r by linarith)
  have b6 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1600 / 3 by norm_num)
  have hX1 : 0 ≤ Real.log X := by rw [hX]; linarith
  have hX1' : 1 ≤ X := by
    by_contra hc
    have := Real.log_neg hX0 (not_le.1 hc)
    linarith
  refine ⟨one_le_pow₀ hX1', ?_⟩
  intro s t hs ht hst C A hC hA
  have hOm := abs_nonneg Om
  set Z : ℝ := (f : ℝ) * r + L + Real.log d + |Om| with hZ
  have hZn : (f : ℝ) * r ≤ Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hXZ : Real.log X ≤ 600 * Z + Real.log S := by rw [hX]; linarith
  have hXZ' : Real.log X ≤ 600 * (Z * (1 + Real.log S)) := by
    have : Real.log S ≤ Z * Real.log S := le_mul_of_one_le_left a2 hZ1
    linarith
  have hpd : Formalism.L2.LamCM.pDeg Om ≤ Z := by unfold Formalism.L2.LamCM.pDeg; linarith
  have hlog : Real.log (X ^ (2 * p0 + 1)) ≤ 1800 * (Z ^ 2 * (1 + Real.log S)) := by
    rw [Real.log_pow]
    push_cast
    calc (2 * (p0 : ℝ) + 1) * Real.log X ≤ (3 * Z) * (600 * (Z * (1 + Real.log S))) :=
          mul_le_mul (by linarith) hXZ' hX1 (by linarith)
      _ = _ := by ring
  have hlog0 : 0 ≤ Real.log (X ^ (2 * p0 + 1)) := Real.log_nonneg (one_le_pow₀ hX1')
  rw [Real.log_mul (by positivity) (by positivity)]
  have hZW : Z ≤ Z ^ 2 * (1 + Real.log S) :=
    (le_self_pow₀ hZ1 (by norm_num)).trans (le_mul_of_one_le_right (by positivity) (by linarith))
  have hZA : Z ^ 2 ≤ Z ^ A := by
    have := Real.rpow_le_rpow_of_exponent_le hZ1 hA
    rwa [Real.rpow_two] at this
  set W := Z ^ 2 * (1 + Real.log S) with hW
  set Y := Real.log (X ^ (2 * p0 + 1)) with hY
  have hW0 : 0 ≤ W := by linarith
  have c1 : (Formalism.L2.LamCM.pDeg Om + 1 / 2 * Y) * (s + t) ≤ (901 * W) * S :=
    mul_le_mul (by linarith) hst (by linarith) (by linarith)
  have c2 : s * (Real.log r + Y) ≤ S * (1801 * W) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have c3 : 3000 * W ≤ C * Z ^ A * (1 + Real.log S) := by
    have : 3000 * Z ^ 2 ≤ C * Z ^ A := mul_le_mul hC hZA (by positivity) (by linarith)
    calc 3000 * W = (3000 * Z ^ 2) * (1 + Real.log S) := by rw [hW]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this (by linarith)
  have c4 : 3000 * W * S ≤ C * Z ^ A * (1 + Real.log S) * S :=
    mul_le_mul_of_nonneg_right c3 (by linarith)
  have c5 : 0 ≤ W * S := mul_nonneg hW0 (by linarith)
  linarith

end GlobalTheory
end
