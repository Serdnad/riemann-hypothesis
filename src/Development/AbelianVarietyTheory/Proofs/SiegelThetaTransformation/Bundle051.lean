module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle049
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaTestFunctionNoCoinvariantsIsotropic
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaTestFunctionNormAndOverlapBound
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaTestFunctionOverlapEqZeroOutsideLevel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumMultiplierTrivialPrincipalCongruence
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle004
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle050
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle003
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle040
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColTorusA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain

@[expose] public section

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.twisted_siegelWeil_difference_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → ∀ (M R : ℕ) (φ : Fam E n (N + 1)), admitted M R φ → ∃ C : ℝ, ∀ 𝔛 : Lt E (N + 1), 𝔛.FG → Agree (R * M) 𝔛 (stdL E (N + 1)) → ∀ Z ∈ Hn Ψ (N + 1), gidx 𝔛 ^ ((n : ℝ) / 2) * ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) ≤ C := by
  first | exact @GlobalTheory.SW.twist_swd_bounded | exact GlobalTheory.SW.twist_swd_bounded | (intros; apply GlobalTheory.SW.twist_swd_bounded <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.eisensteinSeries_term_unitary_graph : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ γ : GL (Fin r) E, IsUn X γ → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, ∀ z₁ w : Fin n → Fin g → ℂ, kZero X idx x₁ x₂ z₁ w * eisTerm X.Ψ (iota X 1 γ) (dbl X bas idx φ₁ φ₂) (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w) = dbl X bas idx φ₁ (wG X bas idx γ φ₂) 0 * kZero X idx x₁ (lact γ x₂) z₁ w := by
  first | exact @GlobalTheory.SW.eisTerm_graph | exact GlobalTheory.SW.eisTerm_graph | (intros; apply GlobalTheory.SW.eisTerm_graph <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.thetaTestFunction_no_coinvariants_isotropic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ ξ : Fin r → E, ξ ≠ 0 → herm X.Gm ξ ξ = 0 → ∀ L ∈ D.lats, ∀ Λ ∈ Vset E n M, ∃ (s : Finset (Fin n → E)) (a : (Fin n → E) → ℂ), ∑ v ∈ s, a v ≠ 0 ∧ ∑ v ∈ s, a v • heisG X bas (vecMulVec v ξ) (D.phi bas hn v₀ L Λ) = 0 := by
  first | exact @GlobalTheory.SW.Coinv.phi_no_coinvariants | exact GlobalTheory.SW.Coinv.phi_no_coinvariants | (intros; apply GlobalTheory.SW.Coinv.phi_no_coinvariants <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.thetaTestFunction_norm_and_overlap_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ L ∈ D.lats, ∀ Λ ∈ Vset E n M, ip (D.phi bas hn v₀ L Λ) (D.phi bas hn v₀ L Λ) = (Nat.card D.J : ℂ) ∧ ∀ L' ∈ D.lats, ‖ip (D.phi bas hn v₀ L Λ) (D.phi bas hn v₀ L' Λ)‖ ≤ (Nat.card D.J : ℝ) * (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ^ (-(n : ℝ) / 2) := by
  first | exact @GlobalTheory.SW.PhiNorm.phi_norm_overlap | exact GlobalTheory.SW.PhiNorm.phi_norm_overlap | (intros; apply GlobalTheory.SW.PhiNorm.phi_norm_overlap <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.thetaTestFunction_overlap_eq_zero_outside_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ γ, IsUn X γ → γ ∉ D.grp → ∀ L ∈ D.lats, ∀ L' ∈ D.lats, ∀ Λ ∈ Vset E n M, ip (D.phi bas hn v₀ L Λ) (wG X bas idx γ (D.phi bas hn v₀ L' Λ)) = 0 := by
  first | exact @GlobalTheory.SW.phi_overlap_eq_zero | exact GlobalTheory.SW.phi_overlap_eq_zero | (intros; apply GlobalTheory.SW.phi_overlap_eq_zero <;> assumption)
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

theorem _root_.GlobalTheory.T.vacuumMultiplier_trivial_principalCongruence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (H : Host E) (Dw : Datum H) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), r = Dw.p + Dw.q → Function.Injective φ → Submodule.span E (Set.range φ) = ⊤ → (∀ a b, ((Dw.EF a b : ℤ) : ℚ) = EF X (φ a) (φ b)) → ∀ L : Lt E r, SelfD X L → ∀ (M : ℕ), 3 ≤ M → ∀ ga : GL (Fin r) E, IsUn X ga → mapL ga L = L → (∀ u ∈ L, ∃ u' ∈ L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u') → ∀ v : TF n g, IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → wG X bas idx ga v = v := by
  first | exact @GlobalTheory.VacMult.wG_vac_eq | exact GlobalTheory.VacMult.wG_vac_eq | (intros; apply GlobalTheory.VacMult.wG_vac_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.FockOrigin

theorem prod_C_mul_X {σ σ' : Type} [DecidableEq σ'] (c : σ → ℂ) (f : σ → σ') (L : List σ) :
    (L.map fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v)).prod =
      (L.map c).prod • MvPolynomial.monomial (Multiset.toFinsupp ((L.map f : List σ') : Multiset σ')) (1 : ℂ) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.map_cons,
      ← Multiset.cons_coe, ← Multiset.singleton_add, map_add, Multiset.toFinsupp_singleton,
      MvPolynomial.X, MvPolynomial.C_mul', smul_mul_smul_comm, MvPolynomial.monomial_mul, one_mul]

theorem polyDeriv_aeval_monomial {σ σ' W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (c : σ → ℂ) (f : σ → σ') (u : σ' → W) {θ : W → ℂ} (hθ : ContDiff ℂ (⊤ : ℕ∞) θ) (m : σ →₀ ℕ) (x : W) :
    _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.aeval (fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v))
      (MvPolynomial.monomial m (1 : ℂ))) u θ x =
      ((Finsupp.toMultiset m).toList.map c).prod *
        I2.itD θ ((Finsupp.toMultiset m).toList.map fun v => u (f v)) x := by
  have h1 := prod_C_mul_X (fun _ : σ => (1 : ℂ)) id (Finsupp.toMultiset m).toList
  simp only [map_one, one_mul, id, List.map_id, List.map_const',
    List.prod_replicate, one_pow, one_smul, Multiset.coe_toList, Finsupp.toMultiset_toFinsupp] at h1
  rw [← h1, map_list_prod, List.map_map]
  have h2 : (⇑(MvPolynomial.aeval (fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v)) :
      MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ' ℂ) ∘ fun v => MvPolynomial.X v) =
      fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v) := by
    funext v; simp
  rw [h2, prod_C_mul_X, I2.polyDeriv_smul, I2.polyDeriv_monomial_one, I2.pdTerm_eq_itD,
    Multiset.toFinsupp_toMultiset]
  congr 1
  refine congrFun (I2.ct_itD_perm hθ ?_) x
  have h3 : ((Finsupp.toMultiset m).toList.map fun v => u (f v)) =
      ((Finsupp.toMultiset m).toList.map f).map u := by rw [List.map_map]; rfl
  rw [h3]
  refine List.Perm.map u ?_
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList]

theorem fvec_zero_eq_polyDeriv : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ (G : WO S T → ℂ) (θ : (Fin S.rank → Fin C.g → ℂ) → ℂ), Differentiable ℂ θ → (∀ w, IsRealPt w → G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * θ (C.zOf (C.xB B) w)) → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, C.fvec B G Q 0 = _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (C.toH Q) (letterDir C.X C.hr C.idx) θ 0 := by
  intro D S T C B hB G θ hθ hG Q
  obtain ⟨R, -, -, hadd, -⟩ := GlobalTheory.KerReal.real_points D S T C
  obtain ⟨-, -, -, -, hdir, -⟩ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB
  set x := C.xB B with hx0
  let f : FVar D T.rank S.rank → Harm.Var C.X.Ψ C.q0 C.X.p0 (Fin S.rank) :=
    fun v => (C.m.e v.1, (rowIdx C.hr).symm v.2.1, v.2.2)
  let c : FVar D T.rank S.rank → ℂ := fun v => ((2 / fockScale D v.1 : ℝ) : ℂ)
  let u : FVar D T.rank S.rank → Fin S.rank → Fin C.g → ℂ := fun v => letterDir C.X C.hr C.idx (f v)
  let lam : FVar D T.rank S.rank → (Fin S.rank → Fin C.g → ℂ) → ℂ := fun v z =>
    -(π * ∑ k, hx C.X C.bas C.idx x (u v k) (z k))
  let Dl : FVar D T.rank S.rank → ((Fin S.rank → Fin C.g → ℂ) → ℂ) → (Fin S.rank → Fin C.g → ℂ) → ℂ :=
    fun l Φ z => lam l z * Φ z + (1 / 2 : ℂ) * (fderiv ℝ Φ z (u l) - I * fderiv ℝ Φ z (I • u l))
  have hlam : ∀ l, (∀ a b, lam l (a + b) = lam l a + lam l b) ∧
      ∀ (t : ℂ) a, lam l (t • a) = conj t * lam l a := by
    intro l
    refine ⟨fun a b => ?_, fun t a => ?_⟩
    · simp only [lam, GlobalTheory.Dict.hx, Pi.add_apply, mulVec_add, star_add, dotProduct_add,
        Finset.sum_add_distrib]
      ring
    · simp only [lam, GlobalTheory.Dict.hx, Pi.smul_apply, mulVec_smul, star_smul, dotProduct_smul,
        smul_eq_mul, ← Finset.mul_sum, RCLike.star_def]
      ring
  have hops := GlobalTheory.Ker.CreOp.foldr_creation_zero _ _ u lam θ hlam hθ Dl (fun _ _ _ => rfl)
  let A := aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) (fun _ => 1) B
  have key : ∀ L : List (FVar D T.rank S.rank), ∀ w, IsRealPt w →
      L.foldr (fun i g => A i g) G w =
        gaussR C.X C.bas C.idx x (C.zOf x w) * ((L.map c).prod * L.foldr Dl θ (C.zOf x w)) := by
    intro L
    induction L with
    | nil => intro w hw; simpa using hG w hw
    | cons a L ih =>
      intro w hw
      have hd : Differentiable ℝ (L.foldr Dl θ) := (hops L).1.differentiable (by simp)
      have h := (GlobalTheory.T.annihilation_creation_periodCoordinates D S T C B hB _ (fun z => (L.map c).prod * L.foldr Dl θ z)
        (hd.const_mul _) ih a.1 (unitMap 1 (B a.1) a.2.1 a.2.2) (u a) (hdir a.1 a.2.1 a.2.2).symm w hw).2
      rw [List.foldr_cons]
      change ((fockScale D a.1 : ℂ)⁻¹) * crea (heisO C.ψ S T) C.θ a.1 (cplxO 1 (C.sB B a.1))
        (unitMap 1 (B a.1) a.2.1 a.2.2) (L.foldr (fun i g => A i g) G) w = _
      rw [h, fderiv_const_mul (hd _)]
      simp only [List.foldr_cons, List.map_cons, List.prod_cons, _root_.smul_apply, smul_eq_mul]
      simp only [Dl, lam, c, ← hx0]
      push_cast
      ring
  have h0 : C.zOf x 0 = 0 := by
    have h1 : C.realPt 0 = 0 := by
      have := hadd 0 0
      rw [add_zero] at this
      exact left_eq_add.mp this
    funext k i
    simp only [Ctx.zOf, h1, zR, Pi.zero_apply, mulVec_zero]
    split_ifs
    · simp [hermC]
    · rfl
  have hr0 : IsRealPt (0 : WO S T) := by
    unfold IsRealPt
    ext i j
    simp
  have hg0 : gaussR C.X C.bas C.idx x (0 : Fin S.rank → Fin C.g → ℂ) = 1 := by
    simp [gaussR, GlobalTheory.Dict.hx]
  have hsm := I2.contDiff_of_diff hθ
  induction Q using MvPolynomial.induction_on' with
  | add P P' hP hP' =>
    rw [map_add (f := _), I2.polyDeriv_add, ← hP, ← hP', Ctx.fvec, map_add (f := _)]
    rfl
  | monomial m a =>
    have e : MvPolynomial.monomial m a = a • MvPolynomial.monomial m (1 : ℂ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, I2.polyDeriv_smul, Ctx.fvec, map_smul, Pi.smul_apply, smul_eq_mul]
    congr 1
    have h2 : pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) (fun _ => 1) B G
        (MvPolynomial.monomial m (1 : ℂ)) = opPow A m G := by
      have := (MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ).constr_basis ℂ
        (fun k => opPow A k G) m
      rwa [MvPolynomial.coe_basisMonomials] at this
    rw [h2, opPow, key _ 0 hr0, h0, hg0, one_mul, (hops _).2]
    refine Eq.trans ?_ (polyDeriv_aeval_monomial c f _ hsm m 0).symm
    congr 1
    rw [I2.ct_iter_eq_itD_ofFn]
    congr 1
    exact List.ofFn_getElem_eq_map _ u

end GlobalTheory.Ker.FockOrigin
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

theorem _root_.GlobalTheory.T.harmonicConnectionValue_eq_polynomial_derivative : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (th : Fin n → (Fin g → ℂ) → ℂ), (∀ b, A.Reads ((N : ℤ) ^ 2) (F b) (th b)) → ∑ m ∈ P.support, algebraMap c.F ℂ (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) = I2.polyDeriv (MvPolynomial.map (algebraMap c.F ℂ) P) (fun ℓ => (Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1) : Fin n → Fin g → ℂ)) (fun z => ∏ b, th b (z b)) 0 := by
  first | exact @GlobalTheory.Dict.nab_harm_val_eq_polyDeriv | exact GlobalTheory.Dict.nab_harm_val_eq_polyDeriv | (intros; apply GlobalTheory.Dict.nab_harm_val_eq_polyDeriv <;> assumption)
end
