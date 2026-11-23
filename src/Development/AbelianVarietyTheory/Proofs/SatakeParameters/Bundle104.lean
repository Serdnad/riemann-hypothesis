module

public import Formalism.GaussJetBounds.Bundle003
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalRingCardinality.Bundle008
public import Formalism.LocalRingCardinality.DataDIV
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle053
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle085
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle096
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Formalism.LocalToGlobal.AlgebraicTheory.Bundle001
public import Formalism.LocalToGlobal.Columns.Bundle006
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalToGlobal.AlgebraicTheory.StatementA
import Formalism.LocalToGlobal.KernelLattices.Bundle001
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)

theorem _root_.GlobalTheory.T.expFactor_allOrbits_eq_prod_orbits : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (R : Finset (OrbitPlaces.Pl D)) {M N N' : ℕ} (eA : Fin M ≃ R × Fin N)
    (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (hbe : constantCoeff be = 0), subst (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (mvExp ((-1 : ℂ_[p]) • Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be)) =
      product_zeroth_first_parts.expS ℂ_[p] (OrbitPlaces.beAll D p (N0 := N) (N1 := N') R (fun _ => -1) (fun _ => be)) := by
  first | exact @GlobalTheory.ExpFacOrbits.expFactor_allOrbits | exact GlobalTheory.ExpFacOrbits.expFactor_allOrbits | (intros; apply GlobalTheory.ExpFacOrbits.expFactor_allOrbits <;> assumption)
end

section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.KFormCore

section Generic

variable {K : Type} [Field K] {σ σ' δ δ' : Type}

def jetL (J : (δ →₀ ℕ) → K) : MvPolynomial (σ ⊕ δ) K →ₗ[K] MvPolynomial σ K :=
  (basisMonomials (σ ⊕ δ) K).constr K fun m =>
    monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (J (m.comapDomain Sum.inr Sum.inr_injective.injOn))

theorem jetL_monomial (J : (δ →₀ ℕ) → K) (m : σ ⊕ δ →₀ ℕ) (c : K) :
    jetL J (monomial m c) = monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
      (c * J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have h1 : (monomial m c : MvPolynomial (σ ⊕ δ) K) = c • basisMonomials (σ ⊕ δ) K m := by
    simp [smul_monomial]
  rw [h1, map_smul, jetL, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

end Generic

section Main

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem applyAt0_eq (l : ℕ) [Fact l.Prime] (a b : ℕ) (Th : MvPowerSeries (ι × Fin a × Fin b) ℂ_[l])
    (Q : MvPolynomial (KM.XZ ι a b) ℤ) :
    KM.applyAt0 a b l Th Q = jetL (fun m => (m.prod fun _ k => (k.factorial : ℂ_[l])) * MvPowerSeries.coeff m Th)
      (MvPolynomial.map (Int.castRingHom ℂ_[l]) Q) := by

  conv_rhs => rw [Q.as_sum, map_sum, map_sum]
  unfold KM.applyAt0
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_monomial, jetL_monomial, mul_assoc]
  rfl

end Main

end GlobalTheory.KFormCore
end
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.FrobPeriod

theorem norm_int_le_one {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖c (x : E)‖ ≤ 1 := by
  have hx : IsIntegral ℤ (c (x : E)) := map_isIntegral_int c x.isIntegral_coe
  have h : c (x : E) ∈ (NormedField.valuation (K := PadicAlgCl l)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))).mem_of_integral
      hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem exists_comp_of_normal {E L : Type} [Field E] [Field L] [CharZero E] [CharZero L]
    [Normal ℚ E] (φ ψ : E →+* L) : ∃ g : E ≃ₐ[ℚ] E, ∀ x, ψ x = φ (g x) := by
  letI : Algebra E L := φ.toAlgebra
  haveI : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  refine ⟨AlgHom.restrictNormal' ψ.toRatAlgHom E, fun x => ?_⟩
  exact (AlgHom.restrictNormal_commutes ψ.toRatAlgHom E x).symm

theorem liesOver_of_mem {E : Type} [Field E] [NumberField E] (l : ℕ) [hl : Fact l.Prime]
    (v : HeightOneSpectrum (𝓞 E)) (h : ((l : ℕ) : 𝓞 E) ∈ v.asIdeal) :
    v.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := by
  constructor
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl.out).irreducible
  refine hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change (algebraMap ℤ (𝓞 E) (l : ℤ)) ∈ v.asIdeal
  simpa using h

theorem card_quot_under {E : Type} [Field E] [NumberField E] (l : ℕ) [hl : Fact l.Prime]
    (Q : Ideal (𝓞 E)) [h : Q.LiesOver (Ideal.span {(l : ℤ)})] :
    Nat.card (ℤ ⧸ Q.under ℤ) = l := by
  rw [← h.over, Nat.card_congr (Int.quotientSpanNatEquivZMod l).toEquiv, Nat.card_zmod]

end GlobalTheory.FrobPeriod


open GlobalTheory.FrobPeriod in
theorem GlobalTheory.FrobPeriod.periodFrob_restrict : ∀ (D : D7) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (c : D.host.E →+* ↥K.1), l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d → ∀ (x : D.host.E) (y : ↥(K0 K)), algebraMap ↥(K0 K) ↥K.1 y = c x → algebraMap ↥(K0 K) ↥K.1 ((P.PD K).σ y) = c (D.host.sigmaOf (DV.frobG D l) x) := by
  intro D l _ P K c h2 hq hd x y hy
  have hlN : ¬ l ∣ D.host.condN := fun h => by
    rcases (D.host.dvd_condN_iff_small Fact.out).1 h with h | h | h
    exacts [h2 h, hq h, hd h]
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  let c' : D.host.E →+* PadicAlgCl l := K.1.val.toRingHom.comp c
  have hK : ∀ z, c' z ∈ K0 K := fun z =>
    IntermediateField.mem_inf.2 ⟨(c z).2, GlobalTheory.T.hostField_padicEmbedding_mem_maxUnramified D.host l h2 hq hd c' z⟩
  let c0 : D.host.E →+* ↥(K0 K) := c'.codRestrict (K0 K) hK
  have hc0 : ∀ z, ((c0 z : ↥(K0 K)) : PadicAlgCl l) = c' z := fun z => rfl
  have hyx : y = c0 x := Subtype.ext (congrArg (fun t : ↥K.1 => (t : PadicAlgCl l)) hy)
  let σ0 := (P.PD K).σ
  obtain ⟨g, hg⟩ := exists_comp_of_normal c0 ((σ0 : ↥(K0 K) →+* ↥(K0 K)).comp c0)
  obtain ⟨v, hvl, hv⟩ := GlobalTheory.T.exists_place_over_prime_of_padicAlgCl_embedding l D.host.E c'
  haveI := liesOver_of_mem l v hvl
  have hgl : ∀ z : 𝓞 D.host.E, g • z - z ^ l ∈ v.asIdeal := fun z => by
    refine (hv _).2 ?_
    have h := P.PD_σ K (c0 z) (by rw [hc0]; exact norm_int_le_one c' z)
    have e : ((g • z - z ^ l : 𝓞 D.host.E) : D.host.E) = g (z : D.host.E) - (z : D.host.E) ^ l := by
      push_cast
      rfl
    rw [e, map_sub, map_pow, ← hc0, ← hc0, ← hg]
    exact h
  set F := D.host.sigmaOf (DV.frobG D l) with hFdef
  have hF : ∀ z : 𝓞 D.host.E, F • z - z ^ l ∈ v.asIdeal := fun z => by
    have h := (GlobalTheory.T.frobG_isArithFrobAt_and_sign_eq_jacobiSym D l h2 hq hd).1 v.asIdeal z
    rw [card_quot_under l v.asIdeal] at h
    exact h
  have hin := (D.host.der.frob l hlN v.asIdeal).2.2.2
  have hgF : g * F⁻¹ = 1 := by
    refine (hin _).1 fun z => ?_
    have h := v.asIdeal.sub_mem (hgl (F⁻¹ • z)) (hF (F⁻¹ • z))
    have e : (g * F⁻¹) • z - z = g • F⁻¹ • z - (F⁻¹ • z) ^ l - (F • F⁻¹ • z - (F⁻¹ • z) ^ l) := by
      rw [mul_smul, smul_inv_smul]
      ring
    rw [e]
    exact h
  have hgF' : g = F := by simpa using mul_inv_eq_one.1 hgF
  subst hyx
  apply Subtype.ext
  change (((σ0 (c0 x) : ↥(K0 K)) : PadicAlgCl l)) = c' (F x)
  have := hg x
  simp only [RingHom.comp_apply] at this
  rw [show (σ0 (c0 x)) = c0 (g x) from this, hc0, hgF']
end

section

namespace GlobalTheory

open Formalism.L2.AlgTh

theorem tensorFourthPower_smul {n : Type} [Fintype n] [DecidableEq n] (c : ℂ) (θ : (n → ℂ) → ℂ) :
    Formalism.L2.Th1.H.tens4 (c • θ) = c ^ 4 • Formalism.L2.Th1.H.tens4 θ := by
  funext z
  simp only [Formalism.L2.Th1.H.tens4, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem locNormScale : LocNormScale := by
  intro a₀ b₀ dK ha hdK lam hlam n _ _ h Λ θ p _ ι c hc hLN
  obtain ⟨g₁, ε, hiso, hp, hidx, hε, heq⟩ := hLN
  refine ⟨g₁, c ^ 4 * ε, hiso, hp, hidx, ?_, ?_⟩
  · rw [map_mul, map_pow, norm_mul, norm_pow]
    have h0 : 0 ≤ ‖ι c‖ := norm_nonneg _
    have h4 : ‖ι c‖ ^ 4 ≤ 1 := pow_le_one₀ h0 hc
    calc ‖ι c‖ ^ 4 * ‖ι ε‖ ≤ 1 * 1 := mul_le_mul h4 hε (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · rw [tensorFourthPower_smul, heq, smul_smul]

end GlobalTheory
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker MvPolynomial

namespace GlobalTheory.KerJ

theorem ufGL_val {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : UF E n) :
    ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = LinearMap.toMatrix' γ.1.toLinearMap := by
  simp [ufGL, toGLm]
  rfl

end GlobalTheory.KerJ
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

namespace GlobalTheory

theorem latSum_transport_equiv {E : Type} [Field E] [NumberField E] {H H₂ M : Type} [AddCommGroup H] [Module (𝓞 E) H]
    [AddCommGroup H₂] [Module (𝓞 E) H₂] [AddCommMonoid M] (e : H ≃ₗ[𝓞 E] H₂) (A B : Submodule (𝓞 E) H)
    (A₂ B₂ : Submodule (𝓞 E) H₂) (hA : ∀ x, e x ∈ A₂ ↔ x ∈ A) (hB : ∀ x, e x ∈ B₂ ↔ x ∈ B) (G : H → M) (F₂ : H₂ → M)
    (hG : ∀ x x', x - x' ∈ B → G x = G x') (hF : ∀ x, F₂ (e x) = G x) : latSum A₂ B₂ F₂ = latSum A B G := by
  have hAm : A.map (e : H →ₗ[𝓞 E] H₂) = A₂ := by
    ext y
    rw [Submodule.mem_map_equiv, ← hA, e.apply_symm_apply]
  let eA : ↥A ≃ₗ[𝓞 E] ↥A₂ := e.ofSubmodules A A₂ hAm
  have heA : ∀ x : A, ((eA x : A₂) : H₂) = e x := fun x => rfl
  have hBm : (B.comap A.subtype).map (eA : ↥A →ₗ[𝓞 E] ↥A₂) = B₂.comap A₂.subtype := by
    ext y
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.subtype_apply, ← hB, ← heA, eA.apply_symm_apply]
  let q := Submodule.Quotient.equiv (B.comap A.subtype) (B₂.comap A₂.subtype) eA hBm
  unfold latSum
  rw [← finsum_comp_equiv q.toEquiv]
  refine finsum_congr fun z => ?_
  set r := Function.surjInv (Submodule.Quotient.mk_surjective (B.comap A.subtype)) z with hr
  set r₂ := Function.surjInv (Submodule.Quotient.mk_surjective (B₂.comap A₂.subtype)) (q.toEquiv z) with hr₂
  have h1 : Submodule.Quotient.mk r = z := Function.surjInv_eq _ z
  have h2 : Submodule.Quotient.mk r₂ = q z := Function.surjInv_eq _ _
  have h3 : q z = Submodule.Quotient.mk (eA r) := by
    rw [← h1]; rfl
  rw [h3, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, heA] at h2
  have h4 : (r₂ : H₂) = e (e.symm r₂) := (e.apply_symm_apply _).symm
  rw [h4, hF]
  apply hG
  rw [← hB, map_sub, ← h4]
  exact h2

noncomputable def homConjEquiv {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) : HomE E a b ≃ₗ[𝓞 E] HomE E a b where
  toFun x := γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap
  invFun x := γ'.symm.toLinearMap ∘ₗ x ∘ₗ γ.toLinearMap
  map_add' x y := by simp [LinearMap.comp_add, LinearMap.add_comp]
  map_smul' r x := by
    ext y i
    simp [equiv_osmul]
  left_inv x := by ext y i; simp
  right_inv x := by ext y i; simp

theorem homConjEquiv_mem_homAt {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 E))) (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (x : HomE E a b) :
    homConjEquiv γ γ' x ∈ homAt S (gmap γ N) (gmap γ' N') ↔ x ∈ homAt S N N' := by
  show (γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) ∈ homAt S (gmap γ N) (gmap γ' N') ↔ _
  constructor
  · intro h P hP y hy
    have h1 := h P hP (γ y) ((mem_localization_gmap P γ N _).2 (by simpa using hy))
    have h2 := (mem_localization_gmap P γ' N' _).1 h1
    simpa using h2
  · intro h P hP y hy
    have h1 := h P hP (γ.symm y) ((mem_localization_gmap P γ N _).1 hy)
    exact (mem_localization_gmap P γ' N' _).2 (by simpa using h1)

theorem mem_divLat_equiv_iff {E : Type} [Field E] [NumberField E] {H H₂ : Type} [AddCommGroup H] [Module (𝓞 E) H]
    [AddCommGroup H₂] [Module (𝓞 E) H₂] (e : H ≃ₗ[𝓞 E] H₂) (A : Submodule (𝓞 E) H) (A₂ : Submodule (𝓞 E) H₂)
    (hA : ∀ x, e x ∈ A₂ ↔ x ∈ A) (c : ℕ) (x : H) : e x ∈ divLat c A₂ ↔ x ∈ divLat c A := by
  show ((c : 𝓞 E) • e x) ∈ A₂ ↔ ((c : 𝓞 E) • x) ∈ A
  rw [← map_smul, hA]

theorem mem_mulLat_equiv_iff {E : Type} [Field E] [NumberField E] {H H₂ : Type} [AddCommGroup H] [Module (𝓞 E) H]
    [AddCommGroup H₂] [Module (𝓞 E) H₂] (e : H ≃ₗ[𝓞 E] H₂) (A : Submodule (𝓞 E) H) (A₂ : Submodule (𝓞 E) H₂)
    (hA : ∀ x, e x ∈ A₂ ↔ x ∈ A) (c : ℕ) (x : H) : e x ∈ mulLat c A₂ ↔ x ∈ mulLat c A := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨e.symm y, (hA _).1 (by rw [e.apply_symm_apply]; exact hy), ?_⟩
    apply e.injective
    rw [← hxy]
    show e ((c : 𝓞 E) • e.symm y) = (c : 𝓞 E) • y
    rw [map_smul, e.apply_symm_apply]
  · rintro ⟨y, hy, hxy⟩
    refine ⟨e y, (hA _).2 hy, ?_⟩
    rw [← hxy]
    show (c : 𝓞 E) • e y = e ((c : 𝓞 E) • y)
    rw [map_smul]

theorem kerOf_gmap_frames : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))} {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] (th : ThDist E K a b SB V V') (Sa : Finset (HeightOneSpectrum (𝓞 E))) (D cA cB : ℕ) (rho : UF E a →* Module.End K V) (rho' : UF E b →* Module.End K V') (sS sT : SB → E → K), ThDist.Ok th Sa D rho rho' sS sT → ∀ (γ : UF E a) (γ' : UF E b) (N : Submodule (𝓞 E) (Sp E a)) (fr : Frs E a SB) (N' : Submodule (𝓞 E) (Sp E b)) (fr' : Frs E b SB) (κ : GLQ E a SB) (κ' : GLQ E b SB) (Ξ Ξ₂ : HomE E a b → K) (c : K), IsSdLat N → IsSdLat N' → (∀ x z, z ∈ mulLat cB (homAt Sa N N') → Ξ (x + z) = Ξ x) → (∀ x : HomE E a b, Ξ₂ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) * ∏ P : SB, (sS P ((LinearEquiv.det (κ P).1 : Eˣ) : E) * sT P ((LinearEquiv.det (κ' P).1 : Eˣ) : E)) = c * Ξ x) → kerOf th Sa cA cB (gmap γ.1 N) (fun P => γ.1 * (fr P * (κ P).1)) (gmap γ'.1 N') (fun P => γ'.1 * (fr' P * (κ' P).1)) Ξ₂ = c • ((rho' γ') ∘ₗ kerOf th Sa cA cB N fr N' fr' Ξ ∘ₗ (rho γ⁻¹)) := by
  intro E K _ _ _ _ a b SB V V' _ _ _ _ th Sa D cA cB rho rho' sS sT hok γ γ' N fr N' fr' κ κ' Ξ Ξ₂ c hN hN' hΞ hΞ₂
  have hm : ∀ (g : UF E a), rho g ∘ₗ rho g⁻¹ = LinearMap.id := fun g => by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  have hm' : ∀ (g : UF E b), rho' g ∘ₗ rho' g⁻¹ = LinearMap.id := fun g => by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  let φ : (V →ₗ[K] V') ≃+ (V →ₗ[K] V') :=
    { toFun := fun L => rho' γ' ∘ₗ L ∘ₗ rho γ⁻¹
      invFun := fun L => rho' γ'⁻¹ ∘ₗ L ∘ₗ rho γ
      left_inv := fun L => by
        have h1 := hm γ⁻¹
        have h2 := hm' γ'⁻¹
        rw [inv_inv] at h1 h2
        show rho' γ'⁻¹ ∘ₗ (rho' γ' ∘ₗ L ∘ₗ rho γ⁻¹) ∘ₗ rho γ = L
        rw [LinearMap.comp_assoc, LinearMap.comp_assoc, h1, ← LinearMap.comp_assoc, h2]; simp
      right_inv := fun L => by
        show rho' γ' ∘ₗ (rho' γ'⁻¹ ∘ₗ L ∘ₗ rho γ) ∘ₗ rho γ⁻¹ = L
        rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hm, ← LinearMap.comp_assoc, hm']; simp
      map_add' := fun L L' => by simp [LinearMap.comp_add, LinearMap.add_comp] }
  have hH := homConjEquiv_mem_homAt Sa γ.1 γ'.1 N N'
  unfold kerOf
  rw [latSum_transport_equiv (homConjEquiv γ.1 γ'.1) (divLat cA (homAt Sa N N')) (mulLat cB (homAt Sa N N')) _ _
    (mem_divLat_equiv_iff _ _ _ hH cA) (mem_mulLat_equiv_iff _ _ _ hH cB)
    (fun x => c • φ (Ξ x • th N fr N' fr' cB x))]
  · show _ = c • φ _
    unfold latSum
    rw [φ.map_finsum, smul_finsum]
  · intro x x' hx
    have h1 : Ξ x = Ξ x' := by
      have := hΞ x' (x - x') hx
      rwa [add_sub_cancel] at this
    rw [h1, hok.cong N fr N' fr' cB x x' hN hN' hx]
  · intro x
    show Ξ₂ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) • th _ _ _ _ cB (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap)
      = c • (rho' γ' ∘ₗ (Ξ x • th N fr N' fr' cB x) ∘ₗ rho γ⁻¹)
    rw [hok.equiv γ γ' N (fun P => fr P * (κ P).1) N' (fun P => fr' P * (κ' P).1) cB x hN hN',
      hok.det N fr N' fr' cB x κ κ' hN hN', LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.smul_comp,
      LinearMap.comp_smul, smul_smul, smul_smul, hΞ₂]

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

namespace GlobalTheory.SuppTop

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem intAt_nat (P : HeightOneSpectrum (𝓞 E)) (c : ℕ) : IntAt P (c : E) := by
  simpa using IntAt.coe P (c : 𝓞 E)

theorem intAt_sum {ι : Type} (P : HeightOneSpectrum (𝓞 E)) (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) :
    IntAt P (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IntAt P) (fun _ _ ha hb => ha.add hb) (by simpa using intAt_nat P 0) h

theorem smul_mem_of_inFr {a b : ℕ} (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b)
    (hf : ∀ y, f y ∈ localization₂ P.asIdeal N ↔ y ∈ stdAt E a P) (hf' : ∀ y, f' y ∈ localization₂ P.asIdeal N' ↔ y ∈ stdAt E b P)
    (c : ℕ) (x : HomE E a b) (h : ∀ s l, IntAt P ((c : E) * inFr f f' x (Pi.single s 1) l)) :
    ∀ y ∈ localization₂ P.asIdeal N, (c : E) • x y ∈ localization₂ P.asIdeal N' := by
  intro y hy
  have hv : f.symm y ∈ stdAt E a P := (hf _).1 (by simpa using hy)
  have hv' : ∀ i, IntAt P (f.symm y i) := (mem_localization_standardLattice P _).1 hv
  have e : (c : E) • x y = f' ((c : E) • inFr f f' x (f.symm y)) := by simp [inFr]
  rw [e, hf']
  refine (mem_localization_standardLattice P _).2 fun l => ?_
  have e2 : inFr f f' x (f.symm y) = ∑ s, f.symm y s • inFr f f' x (Pi.single s 1) := by
    conv_lhs => rw [pi_eq_sum_univ' (f.symm y)]

    simp only [map_sum, map_smul]
  rw [e2]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine intAt_sum P _ _ fun s _ => ?_
  rw [mul_left_comm]
  exact (hv' s).mul (h s l)

theorem entB_zero {N' N : ℕ} (q k₀ c' n' n : ℕ) (hc : c' = 0) (ex' ex : ℕ → ℕ) (x : HomE E N' N) (p p' : ℕ) (hp : p < n)
    (hp' : p' < n') :
    LocE.entB q k₀ c' n' 0 n ex' ex x p p' = Loc.atN (x (Loc.eN E N' p')) p := by
  subst hc
  have h1 : ∀ m s, LocE.fIdx k₀ 0 m s = s := by
    intro m s
    unfold LocE.fIdx
    split_ifs <;> omega
  simp [LocE.entB, h1, LocE.scE, hp, hp']

end General

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem intAt_of_phiTop (sharp : Bool) (m2 : ℕ) (hm : R.m = m2 + 2) (P : HeightOneSpectrum (𝓞 X.E))
    (z : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0)) (hz : PhiTop Ch mu sharp m2 P z ≠ 0)
    (p p' : ℕ) (hp : p < R.N R.m - 1) (hp' : p' < R.N (m2 + 1)) :
    IntAt P (Loc.atN (z (Loc.eN X.E _ p')) p) := by
  have hc : cOf R (m2 + 1) = 0 := by unfold cOf; omega
  have ha : p' < R.r + (R.m - 1) * R.t := by
    have : R.m - 1 = m2 + 1 := by omega
    unfold Ranks.N at hp'
    unfold Ranks.r
    rw [this]
    have : (m2 + 1) * (R.t + 1) = (m2 + 1) * R.t + (m2 + 1) := by ring
    omega
  unfold PhiTop at hz
  split_ifs at hz
  · unfold LocE.PhiGS at hz
    simp only at hz
    split_ifs at hz with h
    · have := h.1 p p' hp ha
      rwa [entB_zero _ _ _ _ _ hc _ _ _ _ _ hp hp'] at this
    · exact absurd rfl hz
  · unfold LocE.PhiG at hz
    simp only at hz
    split_ifs at hz with h
    · have := h.1 p p' hp ha
      rwa [entB_zero _ _ _ _ _ hc _ _ _ _ _ hp hp'] at this
    · exact absurd rfl hz
  · unfold LocE.PhiQ at hz
    split_ifs at hz with h
    · have := h.1 p p' hp (by omega)
      rwa [entB_zero _ _ _ _ _ hc _ _ _ _ _ hp hp'] at this
    · exact absurd rfl hz

theorem intAt_of_ftY {n : ℕ} (P : rowSG Pr sel mu) (η : Sp X.E n →ₗ[X.E] X.E) (y' : Sp X.E n)
    (h : ftY sel mu cst P η y' ≠ 0) (s : Fin n) : IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η (Pi.single s 1)) := by
  unfold ftY at h
  split_ifs at h with h1 h2 h3
  · have := (intAt_nat P.1 (qOf P.1 ^ cst.M)).mul (h2 s)
    simpa using this
  · exact absurd rfl h
  · exact h3 s
  · exact absurd rfl h

end Chain

end GlobalTheory.SuppTop
end
