module

public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementB
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementS
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle001
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.OneLeAbsNormOfLeOne
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
import Mathlib.Algebra.Module.StablyFree.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Hermitian
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory IsLocalRing Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open scoped nonZeroDivisors ComplexOrder

namespace GlobalTheory

theorem cmLowerBound_of_coeffBound :
    (∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (H : (K →+* ℂ) → Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (La logOm : ℝ) (V : Type) [Fintype V] (c : V → Fin x.P.g) (G : MvPolynomial V K) (μ : V →₀ ℕ) (n : ℕ) (S : (K →+* ℂ) → ℝ) (Rr : ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → U.det ≠ 0 → 1 ≤ La → (∀ σ, (H σ).PosDef) → (∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re) → (∀ p : HeightOneSpectrum (𝓞 K), ∃ (cd : K) (cl : Fin x.P.g → K), IsLocGen p cd abelian₂.I ∧ (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧ p.valuation K ((∏ j, cl j) * U.det) ≤ p.valuation K cd) → (∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (U j)) ≤ (La * (ℓ j).n σ) ^ 2) → (∀ j, (ℓ j).ndeg = logOm / 2) → AddMonoidAlgebra.coeff G μ ≠ 0 → AddMonoidAlgebra.coeff G μ ∈ (lineNN T.dual ℓ c μ n).I → (∀ σ, 0 < S σ) → 0 < Rr → (∀ (σ : K →+* ℂ) (z : V → ℂ), (∀ v, ‖z v‖ * (ℓ (c v)).n σ ≤ 1) → ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n ≤ S σ * Rr ^ (∑ v, μ v)) → - ((pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (x.P.g : ℝ) * n)) - (∑ v, (μ v : ℝ)) * Real.log Rr ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ)) → ReciprocityTheory.MultiplicativeHeights.LemmaHStatement → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (e : (Σ b, Fin (m b)) ≃ Fin x.P.g) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (G : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ) (n r : ℕ) (La logOm : ℝ) (S : (K →+* ℂ) → ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → (∀ j, (ℓ j).ndeg = logOm / 2) → U.det ≠ 0 → G ≠ 0 → 1 ≤ La → 1 ≤ r → (∀ b, m b ≤ r) → (∀ σ, 0 < S σ) → (∀ p, Step5Loc e T.dual abelian₂ ℓ U G n p) → (∀ σ, Step5Arch e T.dual abelian₂ ℓ U G a n La (S σ) σ) → - ((pDeg logOm + (1 / 2) * Real.log La) * (((∑ b, ∑ i, a b i : ℕ) : ℝ) + (x.P.g : ℝ) * n)) - ((∑ b, ∑ i, a b i : ℕ) : ℝ) * Real.log ((r : ℝ) * La) ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ) := by
  intro hLK hH K _ _ x T abelian₂ B _ _ m e ℓ U G a n r La logOm S hT hLam hloc harch hℓ hℓdeg hU hG hLa hr hmr hS hS5L hS5A
  classical
  obtain ⟨μ, hμ⟩ := MvPolynomial.ne_zero_iff.mp hG
  have hTd : T.dual.Good := (degree_algebraic K T T hT hT).2.2.1
  obtain ⟨σ₀⟩ : Nonempty (K →+* ℂ) := inferInstance

  have hsum : ∑ v, μ v = ∑ b, ∑ i, a b i := by
    obtain ⟨H₀, -, -, -, heq, -⟩ := hS5A σ₀
    refine subst_homogeneous B m a (MvPolynomial.map σ₀ G) (fun _ => 1) heq μ ?_
    rw [substFr_one, MvPolynomial.coeff_map]
    exact (map_ne_zero σ₀).mpr hμ
  unfold Step5Arch at hS5A
  choose Hs hHs using hS5A
  have hRr : (0 : ℝ) < (r : ℝ) * La := mul_pos (Nat.cast_pos.mpr hr) (by linarith)

  have hmem : AddMonoidAlgebra.coeff G μ ∈ (lineNN T.dual ℓ (fun v : FrVar m => e ⟨v.1, v.2.2⟩) μ n).I := by
    refine coeff_mem_of_local K x.P.g ℓ T.dual (FrVar m) _ μ n _ hTd hℓ fun p => ?_
    obtain ⟨t, cd, cl, ht, hcd, hcl, hv, V, K', _, _, _, _, _, _, f, Ub, hVc, hfin, hind, hUb, hclUb, hW⟩ := hS5L p
    refine ⟨t, cl, ht, hcl, ?_⟩
    have htn : t ^ n ≠ 0 := pow_ne_zero _ ht.1
    have hftn : f (t ^ n) ≠ 0 := (map_ne_zero f).mpr htn
    obtain ⟨w, hw⟩ := coeff_integral_local V K' B m (MvPolynomial.map f G) Ub (fun b j => f (cl (e ⟨b, j⟩)))
      (f (t ^ n)) hVc hfin hftn hUb hclUb hW μ
    have hrange : f (AddMonoidAlgebra.coeff G μ * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) ∈
        Set.range (algebraMap V K') := by
      refine ⟨w, ?_⟩
      rw [map_div₀, map_mul, map_prod]
      simp only [map_pow]
      rw [← map_pow f t n, ← MvPolynomial.coeff_map, hw, mul_div_cancel_left₀ _ hftn]
    have h1 := (hind _).mp hrange
    calc p.valuation K (AddMonoidAlgebra.coeff G μ * ∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v)
        = p.valuation K (AddMonoidAlgebra.coeff G μ * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) *
            p.valuation K (t ^ n) := by
          rw [← map_mul, div_mul_cancel₀ _ htn]
      _ ≤ p.valuation K (t ^ n) := mul_le_of_le_one_left' h1

  have harch' : ∀ (σ : K →+* ℂ) (z : FrVar m → ℂ),
      (∀ v, ‖z v‖ * (ℓ ((fun v : FrVar m => e ⟨v.1, v.2.2⟩) v)).n σ ≤ 1) →
      ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n ≤ S σ * ((r : ℝ) * La) ^ (∑ v, μ v) := by
    intro σ z hz
    obtain ⟨hpd, -, hbd, heq, hY⟩ := hHs σ
    have hTn : 0 < T.dual.n σ ^ n := pow_pos (hTd.2 σ) n
    have hA := ArchTie_of hH B m a (MvPolynomial.map σ G) (fun b => gramBlock e U (Hs σ) σ b) (fun _ => 1)
      (fun b j => (ℓ (e ⟨b, j⟩)).n σ) (S σ / T.dual.n σ ^ n) La r
      (fun b => gramBlock_posDef e U (Hs σ) σ b hpd hU) heq
      (fun X hX => by rw [le_div_iff₀ hTn]; exact hY X hX)
      (fun b j => (hℓ _).2 σ) (by linarith) hmr
      (fun b j => (hermitian_form_gramBlock_basis e U (Hs σ) σ b j).le.trans (hbd _)) z hz
    rw [substFr_one] at hA
    rw [hsum]
    calc ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n
        ≤ S σ / T.dual.n σ ^ n * ((r : ℝ) * La) ^ (∑ b, ∑ i, a b i) * T.dual.n σ ^ n :=
          mul_le_mul_of_nonneg_right hA hTn.le
      _ = S σ * ((r : ℝ) * La) ^ (∑ b, ∑ i, a b i) := by
          rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hTn.ne']
  unfold Step5Loc at hS5L
  have key := hLK K x T abelian₂ ℓ U Hs La logOm (FrVar m) (fun v => e ⟨v.1, v.2.2⟩) G μ n S ((r : ℝ) * La)
    hT hLam hloc harch hℓ hU hLa (fun σ => (hHs σ).1) (fun σ => (hHs σ).2.1)
    (fun p => by
      obtain ⟨t, cd, cl, ht, hcd, hcl, hv, -⟩ := hS5L p
      exact ⟨cd, cl, hcd, hcl, hv⟩)
    (fun σ j => (hHs σ).2.2.1 j) hℓdeg hμ hmem hS hRr harch'
  have hc : (∑ v, (μ v : ℝ)) = ((∑ b, ∑ i, a b i : ℕ) : ℝ) := by
    rw [← hsum, Nat.cast_sum]
  rw [hc] at key
  exact key

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.eigenLattice_numberField_baseChange : ∀ (K K' O : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [CommRing O] (j : K →+* K') (n : ℕ) (Λ : Submodule (𝓞 K) (Fin n → K)) (r : O → Matrix (Fin n) (Fin n) K) (τ : O → K) (c' : Fin n → K'), Λ.FG → (c' ∈ Submodule.span (𝓞 K') ((fun c i => j (c i)) '' {c | c ∈ Λ ∧ ∀ a, (r a).mulVec c = τ a • c}) ↔ c' ∈ Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (Λ : Set (Fin n → K))) ∧ ∀ a, ((r a).map j).mulVec c' = j (τ a) • c') := by
  first | exact @GlobalTheory.CM.eigenLattice_baseChange | exact GlobalTheory.CM.eigenLattice_baseChange | (intros; apply GlobalTheory.CM.eigenLattice_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.symmetric_lineBundle_of_regular_section : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (θ : L.Sec), L.IsLB → (∀ (i : L.ι) (V : Scheme.Opens A.left) (h : V ≤ L.U i), resG A.left h (θ.f i) ∈ nonZeroDivisors Γ(A.left, V)) → (∀ (T : Scheme.{0}) (t : T ⟶ A.left) (i : L.ι) (h : ⊤ ≤ t ⁻¹ᵁ L.U i), (t.appLE (L.U i) ⊤ h).hom (θ.f i) = 0 ↔ t = t ≫ A.hom ≫ eSec A) → Out.Sym A L := by
  first | exact @GlobalTheory.SymOfZeroDivisor.sym_of_regular_section | exact GlobalTheory.SymOfZeroDivisor.sym_of_regular_section | (intros; apply GlobalTheory.SymOfZeroDivisor.sym_of_regular_section <;> assumption)
end

section

noncomputable section

open MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexOrder

namespace GlobalTheory.UnimodVol

def stdRealBasis (g : ℕ) : Module.Basis (Σ _ : Fin g, Fin 2) ℝ (Fin g → ℂ) :=
  Pi.basis fun _ => Complex.basisOneI

theorem volume_fundamentalDomain_stdRealBasis (g : ℕ) :
    volume (ZSpan.fundamentalDomain (stdRealBasis g)) = 1 := by
  have h : ZSpan.fundamentalDomain (stdRealBasis g) =
      Set.pi Set.univ fun _ : Fin g =>
        Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext z
    simp [ZSpan.fundamentalDomain, stdRealBasis, Pi.basis_repr, Sigma.forall, Fin.forall_fin_two]
  rw [h, volume_pi_pi]
  refine Finset.prod_eq_one fun _ _ => ?_
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet]
  simp [Measure.volume_eq_prod]

theorem re_dotProduct_star {g : ℕ} (z w : Fin g → ℂ) :
    (z ⬝ᵥ star w).re = ∑ k, (stdRealBasis g).repr z k * (stdRealBasis g).repr w k := by
  simp [stdRealBasis, Pi.basis_repr, Fintype.sum_sigma, Fin.sum_univ_two, dotProduct]

theorem im_hermForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    (hermForm Hm z w).im = (z ⬝ᵥ star ((Complex.I • Hm.map star) *ᵥ w)).re := by
  have : star ((Complex.I • Hm.map star) *ᵥ w) = (-Complex.I) • Hm *ᵥ star w := by
    ext k
    simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [this, dotProduct_smul, hermForm]
  simp

theorem det_gram_im {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (v : (Σ _ : Fin g, Fin 2) → Fin g → ℂ) :
    (Matrix.of fun i j => (hermForm Hm (v i) (v j)).im).det =
      ((stdRealBasis g).det v) ^ 2 * ‖Hm.det‖ ^ 2 := by
  set T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
    (Matrix.toLin' (Complex.I • Hm.map star)).restrictScalars ℝ with hT
  have h : (Matrix.of fun i j => (hermForm Hm (v i) (v j)).im) =
      ((stdRealBasis g).toMatrix v)ᵀ * (stdRealBasis g).toMatrix (T ∘ v) := by
    ext i j
    rw [Matrix.of_apply, im_hermForm, re_dotProduct_star, Matrix.mul_apply]
    rfl
  have hd : LinearMap.det T = ‖Hm.det‖ ^ 2 := by
    have : (Hm.map star).det = star Hm.det := ((starRingEnd ℂ).map_det Hm).symm
    rw [hT, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, Matrix.det_smul, this]
    simp
  rw [h, Matrix.det_mul, Matrix.det_transpose, ← Module.Basis.det_apply, ← Module.Basis.det_apply,
    Module.Basis.det_comp, hd]
  ring

theorem posDef_of_hermForm {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) : Hm.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have h1 := hpos (star x) (by simpa using hx)
  have h2 := hH.im_star_dotProduct_mulVec_self x
  rw [hermForm, star_star] at h1
  exact Complex.pos_iff.2 ⟨h1, h2.symm⟩

theorem det_re_pos {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) :
    0 < Hm.det.re ∧ ‖Hm.det‖ = Hm.det.re := by
  have h := (posDef_of_hermForm hH hpos).det_pos
  exact ⟨(Complex.pos_iff.1 h).1, (Complex.re_eq_norm.2 h.le).symm⟩

end GlobalTheory.UnimodVol

namespace GlobalTheory

open UnimodVol

theorem volume_mul_det_eq_one_of_unimodular (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (Fd : Set (Fin g → ℂ))
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hE : ∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) (hbij : Function.Bijective Ef)
    (hFd : IsAddFundamentalDomain Λ Fd volume) : (volume Fd).toReal * Hm.det.re = 1 := by
  have : IsZLattice ℝ Λ := ⟨hfull⟩
  let b₁ := Module.Free.chooseBasis ℤ Λ
  let b := b₁.reindex ((b₁.ofZLatticeBasis ℝ Λ).indexEquiv (stdRealBasis g))
  have hvol : (volume Fd).toReal = |(stdRealBasis g).det (Subtype.val ∘ b)| := by
    have h1 := ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hFd
    rw [ZLattice.covolume_eq_det_mul_measureReal Λ volume b (stdRealBasis g), Measure.real,
      volume_fundamentalDomain_stdRealBasis] at h1
    simpa [Measure.real] using h1.symm
  have hu := LinearEquiv.isUnit_det (LinearEquiv.ofBijective Ef hbij) b b.dualBasis
  set M := LinearMap.toMatrix b b.dualBasis (LinearEquiv.ofBijective Ef hbij : Λ →ₗ[ℤ] Module.Dual ℤ Λ)
    with hM
  have hG : (Matrix.of fun i j => (hermForm Hm ((Subtype.val ∘ b) i) ((Subtype.val ∘ b) j)).im) =
      ((Int.castRingHom ℝ).mapMatrix M)ᵀ := by
    ext i j
    simp [hM, LinearMap.toMatrix_apply, hE]
  have hdet := det_gram_im Hm (Subtype.val ∘ b)
  rw [hG, Matrix.det_transpose, ← RingHom.map_det] at hdet
  obtain ⟨hp, hn⟩ := det_re_pos hH hpos
  have habs : |((M.det : ℤ) : ℝ)| = 1 := by
    rcases Int.isUnit_iff.1 hu with h | h <;> simp [h]
  rw [hn, eq_intCast] at hdet
  rw [hdet, ← mul_pow, abs_of_nonneg (sq_nonneg _), ← sq_abs, abs_mul, abs_of_pos hp,
    pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero] at habs
  rw [hvol, habs]

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.EigenNorm

variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) in
theorem _root_.GlobalTheory.EigenNorm.hermForm_add_left (z z' w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (z + z') w = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w + _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z' w := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, add_dotProduct]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) in
theorem _root_.GlobalTheory.EigenNorm.hermForm_add_right (z w w' : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z (w + w') = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w + _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w' := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) in
theorem _root_.GlobalTheory.EigenNorm.hermForm_smul_left (r : ℂ) (z w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (r • z) w = r * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, smul_dotProduct, smul_eq_mul]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) in
theorem _root_.GlobalTheory.EigenNorm.hermForm_smul_right (r : ℂ) (z w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z (r • w) = starRingEnd ℂ r * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  rfl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) in
theorem _root_.GlobalTheory.EigenNorm.hermForm_conj (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm w z = starRingEnd ℂ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w) := by

  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun (congrFun hH i) j
  simp only [Matrix.conjTranspose_apply] at h
  rw [← h]
  simp [Pi.star_apply, Complex.star_def]
  ring

theorem conj_eq_neg_of_sq {ρ : ℂ} {d : ℕ} (hd : d ≠ 0) (h : ρ ^ 2 = -(d : ℂ)) : starRingEnd ℂ ρ = -ρ := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [pow_two] at h1 h2
  have h3 : ρ.re * ρ.im = 0 := by linarith [mul_comm ρ.re ρ.im]
  have h4 : ρ.re = 0 := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact h
    · rw [h] at h1; nlinarith [mul_self_nonneg ρ.re]
  apply Complex.ext <;> simp [h4]

end GlobalTheory.EigenNorm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.TopDifferential

theorem eq_dualMapR {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {F : DualNumber R →+* DualNumber R'}
    (h₁ : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) (h₂ : F DualNumber.eps = DualNumber.eps) :
    F = Chart.dualMapR f := by
  refine RingHom.ext fun x => ?_
  have e : x = algebraMap R _ x.fst + algebraMap R _ x.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e, map_add (f := _), map_mul, h₁, h₁, h₂, ← e]
  ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem det_gram {g : ℕ} (Hm W : Matrix (Fin g) (Fin g) ℂ) :
    (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W j) (W i)).det.re = Real.pi ^ g * ‖W.det‖ ^ 2 * Hm.det.re := by
  have e : (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W j) (W i)) =
      (Real.pi : ℂ) • (W * (Hm * W.conjTranspose)).transpose := rfl
  rw [e, Matrix.det_smul, Matrix.det_transpose, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
    Fintype.card_fin, mul_left_comm W.det, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    mul_comm Hm.det, ← _root_.mul_assoc, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.re_ofReal_mul]

end GlobalTheory.CM.TopDifferential
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CM.ConjDatum

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem emb_bar (H : Host E) (τ : E →+* ℂ) (a : 𝓞 E) :
    τ ((H.bar a : 𝓞 E) : E) = starRingEnd ℂ (τ (a : E)) := by
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]

def ConjLat {H : Host E} (D : Datum H) : Type := D.La

instance {H : Host E} (D : Datum H) : AddCommGroup (ConjLat D) := D.acg

instance {H : Host E} (D : Datum H) : Module (𝓞 E) (ConjLat D) :=
  Module.compHom D.La (H.bar : 𝓞 E →+* 𝓞 E)

def toLat {H : Host E} (D : Datum H) : ConjLat D ≃+ D.La := AddEquiv.refl _

theorem toLat_smul {H : Host E} (D : Datum H) (s : 𝓞 E) (a : ConjLat D) :
    toLat D (s • a) = H.bar s • toLat D a := rfl

theorem finite {H : Host E} (D : Datum H) : Module.Finite (𝓞 E) (ConjLat D) := by
  have := D.fin
  let f : D.La →ₛₗ[(H.bar : 𝓞 E →+* 𝓞 E)] ConjLat D :=
    { toFun := (toLat D).symm
      map_add' := map_add _
      map_smul' := fun s a => by
        apply (toLat D).injective
        rw [toLat_smul]
        simp [bar_bar] }
  exact Module.Finite.of_surjective f (toLat D).symm.surjective

theorem projective {H : Host E} (D : Datum H) : Module.Projective (𝓞 E) (ConjLat D) := by
  have := D.proj
  have i1 : RingHomInvPair (H.bar : 𝓞 E →+* 𝓞 E) (H.bar : 𝓞 E →+* 𝓞 E) :=
    ⟨RingHom.ext (bar_bar H), RingHom.ext (bar_bar H)⟩
  let f : D.La ≃ₛₗ[(H.bar : 𝓞 E →+* 𝓞 E)] ConjLat D :=
    { (toLat D).symm with
      map_smul' := fun s a => by
        apply (toLat D).injective
        rw [toLat_smul]
        simp [bar_bar] }
  exact Module.Projective.of_equiv f

theorem finrank_eq {H : Host E} (D : Datum H) :
    Module.finrank (𝓞 E) (ConjLat D) = Module.finrank (𝓞 E) D.La := by
  unfold Module.finrank
  rw [rank_eq_of_equiv_equiv H.bar (toLat D) H.bar.bijective (toLat_smul D)]

def conj {H : Host E} (D : Datum H) : Datum H where
  La := ConjLat D
  fin := finite D
  proj := projective D
  EF := D.EF
  alt := D.alt
  unimod := D.unimod
  adj := fun a x y => D.adj (H.bar a) x y
  p := D.q
  q := D.p
  rank := by rw [finrank_eq, D.rank]; push_cast; ring
  dom := by
    obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
    refine ⟨J, h1, h2, h3, fun a A t hA ht => h4 (H.bar a) A t hA ?_⟩
    rw [ht]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [emb_bar, Complex.conj_conj, add_comm]

end GlobalTheory.CM.ConjDatum

namespace GlobalTheory.CM

end GlobalTheory.CM
end
end
