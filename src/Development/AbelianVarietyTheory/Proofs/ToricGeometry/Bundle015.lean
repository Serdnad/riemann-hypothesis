module

public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RelAmpleThetaBundleProjectiveModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
theorem _root_.GlobalTheory.T.relAmple_thetaBundle_projectiveModel : (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X : Over (Sp ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧ (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D c), (∀ c' z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 → valAt' (ex z).left (D c) (r c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) / theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin g → Fin N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g → ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠ 0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → Even N → ∀ [GrpObj X], (∀ z w, ex (z + w) = ex z * ex w) → ∀ a b : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) → ∀ (L : LB X.left) (u : HolUnif X L g), L.IsLB → (u.ex = ex ∧ (∀ z, z ∈ u.Λ ↔ z ∈ periodLattice τ) ∧ (∀ (n n' : Fin g → ℤ) i z, ⊤ ≤ (ex z).left ⁻¹ᵁ L.U i → u.fr i z = autFactor a b τ n n' z * u.fr i (z + τ *ᵥ ofIntVec n + ofIntVec n')) ∧ (∀ i, ∃ h F : (Fin g → ℂ) → ℂ, (Differentiable ℂ h ∧ ∀ (n n' : Fin g → ℤ) z, h (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * h z) ∧ Differentiable ℂ F ∧ (∀ (n n' : Fin g → ℤ) z, F (z + τ *ᵥ ofIntVec n + ofIntVec n') = autFactor a b τ n n' z * eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * F z) ∧ ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ L.U i ↔ h z ≠ 0 ∧ F z ≠ 0) ∧ u.fr i z = h z / F z)) → Out.RelAmple X L) := by
  first | exact @GlobalTheory.ThetaAmple.relAmple_thetaBundle | exact GlobalTheory.ThetaAmple.relAmple_thetaBundle | (intros; apply GlobalTheory.ThetaAmple.relAmple_thetaBundle <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Matrix

namespace GlobalTheory.PeriodConn

open NumberField Matrix in
theorem _root_.GlobalTheory.PeriodConn.hermForm_conj_mul {g : ℕ} (Hm N : Matrix (Fin g) (Fin g) ℂ)
    (z w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Nᵀ * Hm * N.map star) z w = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (N.mulVec z) (N.mulVec w) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  congr 2
  ext i
  simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}


open NumberField Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
theorem _root_.GlobalTheory.PeriodConn.isPeriod_mulVec {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (hP : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P) {A : Matrix (Fin g) (Fin g) ℂ} (hA : A.det ≠ 0)
    (hty : ∀ i j, ty i ≠ ty j → A i j = 0) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty ((A.mulVecLin).toAddMonoidHom.comp P) := by
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hHm, hpos, him⟩ := hP
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hcancel : ∀ v, A⁻¹ *ᵥ (A *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hu, Matrix.one_mulVec]
  have hcancel' : ∀ v, A *ᵥ (A⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hu, Matrix.one_mulVec]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a x i
    simp only [AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe, Function.comp_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hlin, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : ty i = ty j
    · rw [h]; ring
    · rw [hty i j h]; simp
  · intro x y hxy
    apply hinj
    have := congrArg (fun v => A⁻¹ *ᵥ v) hxy
    simpa [hcancel] using this
  · let f : (A.mulVecLin.toAddMonoidHom.comp P).range → P.range := fun v =>
      ⟨A⁻¹ *ᵥ (v : Fin g → ℂ), by
        obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp v.2
        refine AddMonoidHom.mem_range.mpr ⟨x, ?_⟩
        rw [← hx]
        exact (hcancel (P x)).symm⟩
    refine DiscreteTopology.of_continuous_injective (f := f) ?_ ?_
    · exact (continuous_const.matrix_mulVec continuous_subtype_val).subtype_mk _
    · intro v w hvw
      apply Subtype.ext
      have := congrArg (fun u : P.range => A *ᵥ (u : Fin g → ℂ)) hvw
      simpa [f, hcancel'] using this
  · have hr : Set.range ⇑(A.mulVecLin.toAddMonoidHom.comp P) =
        ((A.mulVecLin).restrictScalars ℝ) '' Set.range ⇑P := by
      rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact fun v => ⟨A⁻¹ *ᵥ v, hcancel' v⟩
  · have hct : ∀ N : Matrix (Fin g) (Fin g) ℂ, (N.map star)ᴴ = Nᵀ := fun N => by
      ext i j; simp
    have hct' : ∀ N : Matrix (Fin g) (Fin g) ℂ, (Nᵀ)ᴴ = N.map star := fun N => by
      ext i j; simp
    refine ⟨(A⁻¹)ᵀ * Hm * (A⁻¹).map star, ?_, ?_, ?_⟩
    · unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hHm.eq, hct, hct',
        Matrix.mul_assoc]
    · intro z hz
      rw [_root_.GlobalTheory.PeriodConn.hermForm_conj_mul]
      refine hpos _ fun h => hz ?_
      simpa [hcancel'] using congrArg (fun v => A *ᵥ v) h
    · intro x y
      change (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm _ (A *ᵥ P x) (A *ᵥ P y)).im = _
      rw [_root_.GlobalTheory.PeriodConn.hermForm_conj_mul, hcancel, hcancel]
      exact him x y


open NumberField Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
theorem _root_.GlobalTheory.PeriodConn.entry_eq_zero {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {P P' : D.La →+ (Fin g → ℂ)}
    (hP : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P) (hP' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P') {A : Matrix (Fin g) (Fin g) ℂ}
    (h : ∀ x, P' x = A.mulVec (P x)) (i j : Fin g) (hij : ty i ≠ ty j) : A i j = 0 := by
  obtain ⟨hlin, -, -, hspan, -⟩ := hP
  have hlin' := hP'.1
  have key : ∀ a : 𝓞 E, A i j * ((ty j) (a : E) - (ty i) (a : E)) = 0 := by
    intro a
    set d : Fin g → ℂ := fun k => (ty k) (a : E) - (ty i) (a : E) with hd
    let φ : (Fin g → ℂ) →ₗ[ℝ] ℂ :=
      ((LinearMap.proj i).comp (A.mulVecLin.comp (Matrix.diagonal d).mulVecLin)).restrictScalars ℝ
    have hφ : φ = 0 := by
      refine LinearMap.ext_on_range hspan fun x => ?_
      have h1 := hlin' a x i
      rw [h (a • x), h x] at h1
      have hvec : Matrix.diagonal d *ᵥ P x = P (a • x) - (ty i) (a : E) • P x := by
        funext k
        simp [Matrix.mulVec_diagonal, hd, hlin, sub_mul]
      simp only [φ, LinearMap.restrictScalars_apply, LinearMap.comp_apply, LinearMap.proj_apply,
        Matrix.mulVecLin_apply, LinearMap.zero_apply, hvec, Matrix.mulVec_sub,
        Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h1, sub_self]
    have := LinearMap.congr_fun hφ (Pi.single j 1)
    simpa [φ, hd, Matrix.mulVec_single, Matrix.mulVec, dotProduct, Matrix.diagonal,
      Pi.single_apply] using this
  by_contra hA
  apply hij
  refine (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) ?_).symm
  ext a
  have := key a
  simp only [RingHom.comp_apply]
  exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hA))

end GlobalTheory.PeriodConn
end
