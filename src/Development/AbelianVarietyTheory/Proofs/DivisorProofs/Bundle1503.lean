module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleTowerTrBasisAppendCoordinates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoordsLocalRingOfVarietyPointResidueC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientLastCoordinateEtaleTowerNormalLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeRaiseWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderDifferentialFormEtTower
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1415
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle240
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1420
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
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
import Mathlib.RingTheory.KrullDimension.PID
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034

@[expose] public section

section

open Filter Topology MvPolynomial GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.exists_homogeneous_int_trace_sectionTuple : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K), (∀ j, x j ≠ 0) → AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → FiniteDimensional (ratF x) K → ∀ (q : ℕ) (w : K), (∀ l, IsIntegral (ratR x l) (w / x l ^ q)) → ∃ T : MvPolynomial (Fin (D + 1)) ℤ, T.IsHomogeneous q ∧ (Algebra.trace (ratF x) K (w / x 0 ^ q) : K) = aeval (fun l => x l / x 0) T := by
  first | exact @GlobalTheory.HSAmp.TraceHom.trace_homog | exact GlobalTheory.HSAmp.TraceHom.trace_homog | (intros; apply GlobalTheory.HSAmp.TraceHom.trace_homog <;> assumption)
end

section

open Filter Topology MvPolynomial GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.norm_aeval_traceForm_le_fibreValues : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K), (∀ j, x j ≠ 0) → AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → FiniteDimensional (ratF x) K → ∀ (B : Subring K) (hB : ∀ l, x l / x 0 ∈ B), (∀ b ∈ B, IsIntegral (ratR x 0) b) → ∀ (w : B) (T : MvPolynomial (Fin (D + 1)) ℤ), (Algebra.trace (ratF x) K (w : K) : K) = aeval (fun l => x l / x 0) T → ∀ (z : Fin (D + 1) → ℂ) (M : ℝ), z 0 = 1 → (∀ φ : B →+* ℂ, (∀ l, φ ⟨x l / x 0, hB l⟩ = z l) → ‖φ w‖ ≤ M) → ‖aeval z T‖ ≤ Module.finrank (ratF x) K * M := by
  first | exact @GlobalTheory.HSAmp.norm_aeval_trace_le | exact GlobalTheory.HSAmp.norm_aeval_trace_le | (intros; apply GlobalTheory.HSAmp.norm_aeval_trace_le <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.finite_genericFibreClosure_inter_residueCharFibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ W : Set X, IsClosed W → (W ∩ fib X 0).Finite → ∀ ℓ : ℕ, (closure (W ∩ fib X 0) ∩ fib X ℓ).Finite := by
  first | exact @GlobalTheory.GenFibClosure.finite_closure_inter_fib | exact GlobalTheory.GenFibClosure.finite_closure_inter_fib | (intros; apply GlobalTheory.GenFibClosure.finite_closure_inter_fib <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.TowerTrdeg

theorem image_isAlgebraic : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
  (letI := cL.toAlgebra; ∀ a : MvPolynomial (Fin r) R,
    IsAlgebraic (Algebra.adjoin ℂ (Set.range (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))))
      ((MvPolynomial.eval₂Hom ι τ a : T) : L)) := by
  intro K L _ _ cK cL n r R T ι ψ τ x h hx
  letI := cL.toAlgebra
  intro a
  have hy : IsTranscendenceBasis ℂ (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))) :=
    trBasis_append cK cL n r R T ι ψ τ x h hx
  exact hy.isAlgebraic.isAlgebraic _

end GlobalTheory.FieldPair.TowerTrdeg
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_etaleCoords_localRingOfVarietyPoint_residueComplex : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (B : Subring κ') (hB : IsLocModel (algebraMap ℂ κ') B),
    RatRes (algebraMap ℂ κ') B → ((algebraMap ℂ κ').codRestrict B hB.const_mem).FormallySmooth →
    ∃ (r : ℕ) (τ : Fin r → B), (letI := hB.isLocalRing; IsLocalRing.maximalIdeal B = Ideal.span (Set.range τ)) ∧
      (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict B hB.const_mem) τ).FormallyEtale ∧
      TrBasis (algebraMap ℂ κ') (fun i => (τ i : κ')) := by
  first | exact @GlobalTheory.EtaleCoordLocal.exists_etaleCoords | exact GlobalTheory.EtaleCoordLocal.exists_etaleCoords | (intros; apply GlobalTheory.EtaleCoordLocal.exists_etaleCoords <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_quotient_lastCoordinate_etaleTowerNormalLocal : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin (r + 1) → T) (hT : IsEtTower cK R cL T ι ψ τ),
  ∃ (L' : Type) (_ : Field L') (cL' : ℂ →+* L') (T' : Subring L') (π : T →+* T') (ι' : R →+* T') (ψ' : T' →+* R),
    Function.Surjective π ∧ RingHom.ker π = Ideal.span {τ (Fin.last r)} ∧ τ (Fin.last r) ≠ 0 ∧
    IsEtTower cK R cL' T' ι' ψ' (fun i => π (τ (Fin.castSucc i))) ∧ ψ'.comp π = ψ ∧ π.comp ι = ι' ∧
    ∀ a, (π ⟨cL a, hT.top.const_mem a⟩ : L') = cL' a := by
  first | exact @GlobalTheory.FieldPair.IsEtTower.exists_quotient_last | exact GlobalTheory.FieldPair.IsEtTower.exists_quotient_last | (intros; apply GlobalTheory.FieldPair.IsEtTower.exists_quotient_last <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.hermLineBundleGeometricDegree_raiseWeight : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (u : SmFn p), gdeg (up L u) D = gdeg L D := by
  first | exact @GlobalTheory.GdegMetric.gdeg_up | exact GlobalTheory.GdegMetric.gdeg_up | (intros; apply GlobalTheory.GdegMetric.gdeg_up <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.order_differential_form_et_tower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) (P : Place cL),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) → P.IsPrimeOf T →
  (∀ g : R, g ≠ 0 → P.ord (ι g : L) = 0) →
  (fun ω => @dite ℤ (∃ a, P.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) = 0 := by
  first | exact @GlobalTheory.FieldPair.formOrd_dForm_append_eq_zero | exact GlobalTheory.FieldPair.formOrd_dForm_append_eq_zero | (intros; apply GlobalTheory.FieldPair.formOrd_dForm_append_eq_zero <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.DimDeg

def DimFormula (R : Type) [CommRing R] (c : ℕ) : Prop :=
  ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra R B] [FaithfulSMul R B] [Algebra.FiniteType R B] (e : ℕ),
    Algebra.trdeg R B = e → ringKrullDim B = (e + c : ℕ)

theorem dimFormula_field (F : Type) [Field F] : DimFormula F 0 := by
  intro B _ _ _ _ _ e he
  obtain ⟨d, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq F B
  have : d = e := by exact_mod_cast h₂.symm.trans he
  rw [h₁, this, add_zero]

theorem dimFormula_int : DimFormula ℤ 1 := by
  intro B _ _ _ _ _ e he
  have : CharZero B := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℤ B)
  refine le_antisymm ?_ (PrimeDivDim.succ_trdeg_le_ringKrullDim B he)
  have hZ1 : ringKrullDim ℤ ≤ 1 := by
    exact_mod_cast Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 ℤ)
  refine (IntModel.ringKrullDim_le_add (O := ℤ) ℚ).trans ?_
  rw [ringKrullDim_genericFibre_eq ℤ ℚ he]
  refine (add_le_add hZ1 (le_refl ((e : ℕ) : WithBot ℕ∞))).trans_eq ?_
  push_cast
  exact add_comm _ _

theorem exists_dim_quotient_ker {R : Type} [CommRing R] [IsDomain R] {c : ℕ} (hR : DimFormula R c)
    (hs : Function.Surjective (Int.cast : ℤ → R)) {A K : Type} [CommRing A] (hA : (Int.castRingHom A).FiniteType)
    [Field K] [Algebra R K] [FaithfulSMul R K] (φ : A →+* K) (hφ : ∀ z : K, ∃ a b : A, z = φ a / φ b) :
    ∃ e : ℕ, Algebra.trdeg R K = e ∧ ringKrullDim (A ⧸ RingHom.ker φ) = (e + c : ℕ) := by
  let B : Subalgebra R K :=
    { φ.range.toSubsemiring with
      algebraMap_mem' := fun r => by
        obtain ⟨n, rfl⟩ := hs r
        exact ⟨n, by simp⟩ }
  let ψ : A →+* B := φ.codRestrict B fun a => ⟨a, rfl⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩
  have hft : Algebra.FiniteType R B := by
    have h1 : (ψ.comp (Int.castRingHom A)).FiniteType := (RingHom.FiniteType.of_surjective ψ hψ).comp hA
    rw [Subsingleton.elim (ψ.comp (Int.castRingHom A)) ((algebraMap R B).comp (Int.castRingHom R))] at h1
    exact RingHom.finiteType_algebraMap.1 h1.of_comp_finiteType
  have : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h =>
    FaithfulSMul.algebraMap_injective R K (by
      rw [IsScalarTower.algebraMap_apply R B K, IsScalarTower.algebraMap_apply R B K, h])
  have : IsFractionRing B K := IsFractionRing.of_field B K fun z => by
    obtain ⟨a, b, h⟩ := hφ z
    exact ⟨ψ a, ψ b, h⟩
  have : Algebra.IsAlgebraic B K := IsLocalization.isAlgebraic K (nonZeroDivisors B)
  obtain ⟨e, he⟩ := exists_trdeg_eq_natCast R (A := B)
  refine ⟨e, (trdeg_eq_of_isAlgebraic_top R B K).trans he, ?_⟩
  have hk : RingHom.ker φ = RingHom.ker ψ := Ideal.ext fun a => by
    simp only [RingHom.mem_ker]
    exact (Subtype.ext_iff (a1 := ψ a) (a2 := 0)).symm
  rw [← hR B e he, hk]
  exact ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hψ)

theorem exists_dim_inter {R : Type} [CommRing R] [IsDomain R] {c : ℕ} (hR : DimFormula R c)
    (hs : Function.Surjective (Int.cast : ℤ → R)) {X : Scheme.{0}} (t : X ⟶ Sp ℤ) [LocallyOfFiniteType t] (x : X)
    [Algebra R (X.residueField x)] [FaithfulSMul R (X.residueField x)] {U : X.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) :
    ∃ e : ℕ, Algebra.trdeg R (X.residueField x) = e ∧
      topologicalKrullDim ((U : Set X) ∩ closure {x} : Set X) = (e + c : ℕ) := by
  have hA : (Int.castRingHom Γ(X, U)).FiniteType := by
    let φ := Spec.preimage (hU.fromSpec ≫ t)
    have hφ : Spec.map φ = hU.fromSpec ≫ t := Spec.map_preimage _
    have h := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
    rwa [Subsingleton.elim (Int.castRingHom Γ(X, U)) φ.hom]
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨e, h₁, h₂⟩ := exists_dim_quotient_ker hR hs hA (X.evaluation U x hx).hom (by
    intro z
    obtain ⟨w, rfl⟩ := X.residue_surjective x z
    obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (S := X.presheaf.stalk x) w
    have hu := (IsLocalization.map_units (X.presheaf.stalk x) b).map (X.residue x).hom
    refine ⟨a, b, (eq_div_iff hu.ne_zero).2 ?_⟩
    exact (map_mul (X.residue x).hom _ _).symm.trans (congrArg (X.residue x).hom h))
  refine ⟨e, h₁, ?_⟩
  have hk : RingHom.ker (X.evaluation U x hx).hom = (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    ext f
    rw [RingHom.mem_ker]
    refine (X.evaluation_eq_zero_iff_notMem_basicOpen x hx f).trans ?_
    have h := hU.fromSpec_preimage_basicOpen f
    have h' : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
      SetLike.ext_iff.1 h (hU.primeIdealOf ⟨x, hx⟩)
    rw [hU.fromSpec_primeIdealOf] at h'
    exact h'.not.trans not_not
  have h := topologicalKrullDim_range_inter_closure_eq (B := Γ(X, U)) hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩)
  rw [← h₂, hk, ← h]
  have h3 := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have h4 := hU.range_fromSpec
  exact congrArg (fun s : Set X => topologicalKrullDim s)
    (congrArg₂ (· ∩ ·) h4.symm (congrArg (fun z => closure {z}) h3.symm))

theorem exists_hasDim {R : Type} [CommRing R] [IsDomain R] {c : ℕ} (hR : DimFormula R c)
    (hs : Function.Surjective (Int.cast : ℤ → R)) {X : Scheme.{0}} (t : X ⟶ Sp ℤ) [LocallyOfFiniteType t] (x : X)
    [Algebra R (X.residueField x)] [FaithfulSMul R (X.residueField x)] :
    ∃ e : ℕ, Algebra.trdeg R (X.residueField x) = e ∧ HasDim x (e + c) := by
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top x)
  obtain ⟨e, h₁, h₂⟩ := exists_dim_inter hR hs t x hU hxU
  refine ⟨e, h₁, le_antisymm ?_ ?_⟩
  · refine topologicalKrullDim_le_of_forall_exists_isOpen fun z => ?_
    obtain ⟨V, hV, hzV, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top z.1)
    have hxV : x ∈ V := (specializes_iff_mem_closure.2 z.2).mem_open V.isOpen hzV
    obtain ⟨e', h₁', h₂'⟩ := exists_dim_inter hR hs t x hV hxV
    obtain rfl : e = e' := by exact_mod_cast h₁.symm.trans h₁'
    refine ⟨Subtype.val ⁻¹' (V : Set X), V.isOpen.preimage continuous_subtype_val, hzV, ?_⟩
    rw [← h₂']
    refine (topologicalKrullDim_eq_of_isEmbedding
      (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal) ?_).ge
    rw [Set.range_comp, Subtype.range_val, Subtype.image_preimage_val, Set.inter_comm]
  · rw [← h₂]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le

theorem locallyOfFiniteType_of_isAmb {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (h : IsAmb p) :
    LocallyOfFiniteType p := by
  obtain ⟨N, jN, _, hjN⟩ := h.isProjOver
  have := isProper_str k N
  have : IsProper p := hjN ▸ inferInstance
  infer_instance

theorem le_and_iff_of_dimFormula {R : Type} [CommRing R] [IsDomain R] {c : ℕ} (hR : DimFormula R c)
    (hs : Function.Surjective (Int.cast : ℤ → R)) {X Y : Scheme.{0}} (t : X ⟶ Sp ℤ) [LocallyOfFiniteType t]
    (π : Y ⟶ X) [LocallyOfFiniteType π] (y : Y) [Algebra R (X.residueField (π y))]
    [FaithfulSMul R (X.residueField (π y))] (d d' : ℕ) (hd : HasDim y d) (hd' : HasDim (π y) d') :
    d' ≤ d ∧ (π.residueDegree y ≠ 0 ↔ d = d') := by
  letI := (π.residueFieldMap y).hom.toAlgebra
  letI : Algebra R (Y.residueField y) := ((π.residueFieldMap y).hom.comp (algebraMap R _)).toAlgebra
  haveI : IsScalarTower R (X.residueField (π y)) (Y.residueField y) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : FaithfulSMul R (Y.residueField y) := (faithfulSMul_iff_algebraMap_injective _ _).2
    ((π.residueFieldMap y).hom.injective.comp (FaithfulSMul.algebraMap_injective R _))
  haveI : Algebra.EssFiniteType (X.residueField (π y)) (Y.residueField y) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap π y)
  obtain ⟨e, h₁, h₂⟩ := exists_hasDim hR hs (π ≫ t) y
  obtain ⟨e', h₁', h₂'⟩ := exists_hasDim hR hs t (π y)
  obtain rfl : d = e + c := by exact_mod_cast hd.symm.trans h₂
  obtain rfl : d' = e' + c := by exact_mod_cast hd'.symm.trans h₂'
  have hadd := trdeg_add_eq R (X.residueField (π y)) (A := Y.residueField y)
  rw [h₁, h₁'] at hadd
  have hle : e' ≤ e := by exact_mod_cast (self_le_add_right _ _).trans_eq hadd
  refine ⟨by omega, ?_⟩
  change Module.finrank (X.residueField (π y)) (Y.residueField y) ≠ 0 ↔ _
  constructor
  · intro h
    have : Module.Finite (X.residueField (π y)) (Y.residueField y) := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h)
    rw [trdeg_eq_zero, add_zero] at hadd
    have : e' = e := by exact_mod_cast hadd
    rw [this]
  · intro h
    obtain rfl : e = e' := by omega
    have h0 : Algebra.trdeg (X.residueField (π y)) (Y.residueField y) = 0 := by
      rcases (Cardinal.add_eq_left_iff).1 hadd with h | h
      · exact absurd (le_trans (le_max_left _ _) h) (not_le.2 Cardinal.natCast_lt_aleph0)
      · exact h
    have : Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y) := trdeg_eq_zero_iff.1 h0
    have : Module.Finite (X.residueField (π y)) (Y.residueField y) := Algebra.finite_of_essFiniteType_of_isAlgebraic
    exact Module.finrank_pos.ne'

theorem dim_le_and_residueDegree_ne_zero_iff : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (π : Y ⟶ X), π ≫ p = q → ∀ (y : Y) (d d' : ℕ), HasDim y d → HasDim (π y) d' → d' ≤ d ∧ (π.residueDegree y ≠ 0 ↔ d = d') := by
  intro k _ X Y p q hp hq π hπ y d d' hd hd'
  have := locallyOfFiniteType_of_isAmb hp
  have : LocallyOfFiniteType (π ≫ p) := hπ ▸ locallyOfFiniteType_of_isAmb hq
  have : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π p
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hp.finite)
  obtain ⟨l, hl⟩ := CharP.exists (X.residueField (π y))
  rcases CharP.char_is_prime_or_zero (X.residueField (π y)) l with h | rfl
  · haveI : Fact l.Prime := ⟨h⟩
    letI := ZMod.algebra (X.residueField (π y)) l
    exact le_and_iff_of_dimFormula (dimFormula_field (ZMod l)) (ZMod.intCast_surjective)
      (p ≫ spMap (Int.castRingHom k)) π y d d' hd hd'
  · haveI := CharP.charP_to_charZero (X.residueField (π y))
    exact le_and_iff_of_dimFormula dimFormula_int (fun n => ⟨n, rfl⟩)
      (p ≫ spMap (Int.castRingHom k)) π y d d' hd hd'

end GlobalTheory.DimDeg
end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.norm_diagonalTorusCharacter_flatLineWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (τ : Psi H) (t : Ix Dw → (CAt σ)ˣ), ‖GlobalTheory.CompHS.diagChar (exOf Dw (flatWt Dw τ) 0) t‖ = (∏ j : Fin (Dw.mult (conjEmb τ.1)), ‖toC ((t (some ⟨conjEmb τ.1, j⟩) : CAt σ))‖) / ∏ i : Fin (Dw.mult τ.1), ‖toC ((t (some ⟨τ.1, i⟩) : CAt σ))‖ := by
  first | exact @GlobalTheory.CompHS.FlatDiag.norm_diagChar_flatWt | exact GlobalTheory.CompHS.FlatDiag.norm_diagChar_flatWt | (intros; apply GlobalTheory.CompHS.FlatDiag.norm_diagChar_flatWt <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.archIntegrable_of_projArithAmbient : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ (M N : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), N.ArchIntegrable M e hr := by
  first | exact @GlobalTheory.MixHt.archIntegrable_of_isAmb | exact GlobalTheory.MixHt.archIntegrable_of_isAmb | (intros; apply GlobalTheory.MixHt.archIntegrable_of_isAmb <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.exists_tensor_sections_nonvanishing_finite_set : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ (M : HermLB q) (S : Set Y), S.Finite → ∃ (A : HermLB q) (s : (M.tens A).B.Sec) (u : A.B.Sec), S ⊆ nonzeroLocus s ∧ S ⊆ nonzeroLocus u := by
  first | exact @GlobalTheory.MixHt.exists_tens_sec_finite_subset_nonzeroLocus | exact GlobalTheory.MixHt.exists_tens_sec_finite_subset_nonzeroLocus | (intros; apply GlobalTheory.MixHt.exists_tens_sec_finite_subset_nonzeroLocus <;> assumption)
end
