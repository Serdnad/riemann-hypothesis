module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1448
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphIdealLocalizationMaximalIdealEqSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingIwasawaDecomposition
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)


theorem _root_.GlobalTheory.T.quadratic_injective_plane_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁),
    Module.finrank F E = 2 → d = d₁ + 2 → form σ W.J H'.x H'.y = 1 → (∀ u, form σ W.J (H'.ι *ᵥ u) H'.y = 0) →
    (Function.Injective fun z : Matrix (Fin n) (Fin d₁) E => z * H'.ιᵀ) →
    ∀ f : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F),
      Function.Injective f → (∀ x, hat (f x) = M.co.e (incM F x)) →
    ∀ K : Submodule F (Matrix (Fin n) (Fin d₁) E), Module.finrank F K = n * d₁ → (∀ z ∈ K, (M₁.co.e (incM F z)).1 = 0) →
      n * d ≤ Module.finrank F (lagr M M₁ H') := by
  first | exact @GlobalTheory.MixedLagr.le_finrank_lagr | exact GlobalTheory.MixedLagr.le_finrank_lagr | (intros; apply GlobalTheory.MixedLagr.le_finrank_lagr <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)


theorem _root_.GlobalTheory.T.rational_lagrangian_subspace_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W), Module.finrank F E = 2 →
    ∀ f : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F),
      Function.Injective f → (∀ x, hat (f x) = M.co.e (incM F x)) →
      ∃ K : Submodule F (Matrix (Fin n) (Fin d) E), Module.finrank F K = n * d ∧ ∀ z ∈ K, (M.co.e (incM F z)).1 = 0 := by
  first | exact @GlobalTheory.MixedLagr.rat_first_zero_dim | exact GlobalTheory.MixedLagr.rat_first_zero_dim | (intros; apply GlobalTheory.MixedLagr.rat_first_zero_dim <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)


theorem _root_.GlobalTheory.T.rational_model_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      M.co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ f : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F),
      Function.Injective f ∧ ∀ x, hat (f x) = M.co.e (incM F x) := by
  first | exact @GlobalTheory.MixedLagr.ratCoord_linear_injective | exact GlobalTheory.MixedLagr.ratCoord_linear_injective | (intros; apply GlobalTheory.MixedLagr.ratCoord_linear_injective <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.KBridge

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (F E) in
def infT : AF F ⊗[F] E →ₐ[F] Ainf F ⊗[F] E := Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)


variable (F E) in
def finT : AF F ⊗[F] E →ₐ[F] Af F ⊗[F] E := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)


variable (F E) in
def ofInfT : Ainf F ⊗[F] E →ₗ[F] AF F ⊗[F] E := (LinearMap.inl F (Ainf F) (Af F)).rTensor E


variable (F E) in
def ofFinT : Af F ⊗[F] E →ₗ[F] AF F ⊗[F] E := (LinearMap.inr F (Ainf F) (Af F)).rTensor E

theorem decomp (z : AF F ⊗[F] E) : z = ofInfT F E (infT F E z) + ofFinT F E (finT F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _)]
    conv_lhs => rw [hx, hy]
    abel
  | tmul a e =>
    change a ⊗ₜ[F] e = ((a.1, 0) : AF F) ⊗ₜ[F] e + ((0, a.2) : AF F) ⊗ₜ[F] e
    rw [← TensorProduct.add_tmul]
    congr 1
    exact Prod.ext (add_zero _).symm (zero_add _).symm

theorem tmul_eq_smul_incV {n : ℕ} (a : AF F) (x : Fin n → E) : (fun i => a ⊗ₜ[F] x i) = a • incV F x := by
  funext i
  change a ⊗ₜ[F] x i = a • ((1 : AF F) ⊗ₜ[F] x i)
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem infT_tmul (a : AF F) (e : E) : infT F E (a ⊗ₜ[F] e) = a.1 ⊗ₜ[F] e := rfl

theorem mem_latHat_iff {n : ℕ} (X : Spc F E n) (z : Fin n → AE F E) :
    z ∈ latHat X ↔ (∀ i, infT F E (z i) = 0) ∧
      (fun i => finT F E (z i)) ∈ Formalism.MainNotions.StandardLattice.latHat F E (X.L : Set (Fin n → E)) := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hv, x, hx, rfl⟩ := hz
      have h0 : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 ha
      rw [← tmul_eq_smul_incV]
      refine ⟨fun i => ?_, ?_⟩
      · rw [infT_tmul, h0, TensorProduct.zero_tmul]
      · exact AddSubgroup.subset_closure ⟨a.2, fun v => hv v, x, hx, rfl⟩
    | zero =>
      refine ⟨fun i => map_zero _, ?_⟩
      have e : (fun i => finT F E ((0 : Fin n → AE F E) i)) = 0 := funext fun i => map_zero _
      rw [e]; exact zero_mem _
    | add y z _ _ hy hz =>
      refine ⟨fun i => ?_, ?_⟩
      · rw [Pi.add_apply, map_add (f := _), hy.1 i, hz.1 i, add_zero]
      · have e : (fun i => finT F E ((y + z) i)) = (fun i => finT F E (y i)) + fun i => finT F E (z i) :=
          funext fun i => map_add _ _ _
        rw [e]; exact add_mem hy.2 hz.2
    | neg y _ hy =>
      refine ⟨fun i => ?_, ?_⟩
      · rw [Pi.neg_apply, map_neg, hy.1 i, neg_zero]
      · have e : (fun i => finT F E ((-y) i)) = -fun i => finT F E (y i) := funext fun i => map_neg _ _
        rw [e]; exact neg_mem hy.2
  · rintro ⟨hi, hf⟩
    have e : z = fun i => ofFinT F E (finT F E (z i)) := funext fun i => by
      conv_lhs => rw [decomp (z i)]
      rw [hi i, map_zero, zero_add]
    rw [e]
    suffices H : ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat F E (X.L : Set (Fin n → E)), (fun i => ofFinT F E (y i)) ∈ latHat X from H _ hf
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨show AF F from (0, a), map_zero _, fun v => ha v, x, hx, tmul_eq_smul_incV (show AF F from (0, a)) x⟩
    | zero =>
      have e : (fun i => ofFinT F E ((0 : Fin n → Af F ⊗[F] E) i)) = 0 := funext fun i => map_zero _
      rw [e]; exact zero_mem _
    | add y y' _ _ hy hy' =>
      have e : (fun i => ofFinT F E ((y + y') i)) = (fun i => ofFinT F E (y i)) + fun i => ofFinT F E (y' i) :=
        funext fun i => map_add _ _ _
      rw [e]; exact add_mem hy hy'
    | neg y _ hy =>
      have e : (fun i => ofFinT F E ((-y) i)) = -fun i => ofFinT F E (y i) := funext fun i => map_neg _ _
      rw [e]; exact neg_mem hy

theorem mulVec_mem_latHat {n : ℕ} (σ : E →ₐ[F] E) (X : Spc F E n) (hfg : X.L.FG) {k : GAd σ X.Jᵀ}
    (hk : k ∈ levelOpen σ X.Jᵀ X.L) {z : Fin n → AE F E} (hz : z ∈ latHat X) :
    (matHom (AF F) σ X.Jᵀ k).1 *ᵥ z ∈ latHat X := by
  rw [mem_latHat_iff] at hz ⊢
  obtain ⟨hi, hf⟩ := hz
  refine ⟨fun i => ?_, ?_⟩
  · have e : ((infT F E).toRingHom ∘ z) = 0 := funext fun j => hi j
    refine (RingHom.map_mulVec (infT F E).toRingHom (matHom (AF F) σ X.Jᵀ k).1 z i).trans ?_
    rw [e, Matrix.mulVec_zero]
    rfl
  · have e : (fun i => finT F E (((matHom (AF F) σ X.Jᵀ k).1 *ᵥ z) i)) =
        Formalism.MainNotions.StandardLattice.finMat σ X.Jᵀ k *ᵥ fun i => finT F E (z i) :=
      funext fun i => RingHom.map_mulVec (finT F E).toRingHom _ _ i
    rw [e]
    exact ((mem_levelOpen_iff_latHat σ X.Jᵀ hfg k).1 hk _).1 hf

theorem ofGAd_mem_stabK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n), X.L.IsLattice E → ∀ g : GAd σ X.Jᵀ,
    (∀ w, Commute ((matHom w.Completion σ X.Jᵀ (projArch σ X.Jᵀ w g)).1.map (infEmb (B.emb w))) (X.θ w)) →
    (∀ v, proj σ X.Jᵀ v g ∈ stabLoc σ X.Jᵀ X.L v) → GlobalTheory.IwLine.ofGAd σ X.J g ∈ GlobalTheory.StabHaar.stabK (σ := σ) B X := by
  intro F E _ _ _ _ _ σ B n X hL g h1 h2
  have hfg : X.L.FG := hL.fg
  have hg : g ∈ levelOpen σ X.Jᵀ X.L := mem_levelOpen.2 h2
  refine ⟨fun w => h1 w, fun z hz => ⟨?_, ?_⟩⟩
  · rw [GlobalTheory.IwLine.mat_ofGAd]
    exact mulVec_mem_latHat σ X hfg hg hz
  · rw [← map_inv, GlobalTheory.IwLine.mat_ofGAd]
    exact mulVec_mem_latHat σ X hfg (inv_mem hg) hz

end GlobalTheory.KBridge
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_isUnit_mul_zpow_uniformiser_tmul : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra (K ⊗[ℂ] κ') L]
    (E : Place (algebraMap ℂ K)) (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring),
  Function.Injective (algebraMap (K ⊗[ℂ] κ') L) → Irreducible t →
  ∀ g : K, g ≠ 0 → ∃ q : locAt (L := L) 𝔭, IsUnit q ∧
    algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) = q * (algebraMap (K ⊗[ℂ] κ') L ((t : K) ⊗ₜ 1)) ^ E.ord g := by
  first | exact @GlobalTheory.GraphLocal.exists_isUnit_mul_zpow_tmul | exact GlobalTheory.GraphLocal.exists_isUnit_mul_zpow_tmul | (intros; apply GlobalTheory.GraphLocal.exists_isUnit_mul_zpow_tmul <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isLocalRingOfVarietyPoint_localization_placeTensor : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (E : Place (algebraMap ℂ K)) (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') →
  IsLocModel (algebraMap ℂ L) (locAt (L := L) 𝔭) := by
  first | exact @GlobalTheory.GraphLocal.isLocModel_locAt | exact GlobalTheory.GraphLocal.isLocModel_locAt | (intros; apply GlobalTheory.GraphLocal.isLocModel_locAt <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

theorem _root_.GlobalTheory.T.placeGraphIdealTensor_ne_top : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K)),
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  graphIdeal (κ' := κ') E R π ρ ≠ ⊤ := by
  first | exact @GlobalTheory.GraphLocal.graphIdeal_ne_top | exact GlobalTheory.GraphLocal.graphIdeal_ne_top | (intros; apply GlobalTheory.GraphLocal.graphIdeal_ne_top <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

theorem _root_.GlobalTheory.T.sum_tmul_notMem_prime_of_graph_image_ne_zero : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  graphIdeal E R π ρ ≤ 𝔭 → E.Contains R →
  ∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ') (w : tens (κ' := κ') (placeAlg E)),
    (w : K ⊗[ℂ] κ') = ∑ i, (a i : K) ⊗ₜ b i → ∑ i, ρ (π (a i)) * b i ≠ 0 → w ∉ 𝔭 := by
  first | exact @GlobalTheory.GraphLocal.sum_notMem_of_ne_zero | exact GlobalTheory.GraphLocal.sum_notMem_of_ne_zero | (intros; apply GlobalTheory.GraphLocal.sum_notMem_of_ne_zero <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

theorem _root_.GlobalTheory.T.flat_aeval_dvrPlaceRing_uniformiser_residueLifts : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ] (k : ℕ) (R : Subring K)
    (π : R →+* κ) (E : Place (algebraMap ℂ K)) (hER : E.Contains R) (t : E.ring) (zR : Fin k → R),
    (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
    (∀ a, algebraMap ℂ K a ∈ R) →
    (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
    Irreducible t → AlgebraicIndependent ℂ (fun i => π (zR i)) →
    (MvPolynomial.aeval (Fin.cons (⟨(t : K), t.2⟩ : placeAlg E)
        (fun i => (⟨(zR i : K), hER _ (zR i).2⟩ : placeAlg E))) :
        MvPolynomial (Fin (k + 1)) ℂ →ₐ[ℂ] placeAlg E).toRingHom.Flat := by
  first | exact @GlobalTheory.GraphLocal.FlatPlace.flat_aeval_placeAlg | exact GlobalTheory.GraphLocal.FlatPlace.flat_aeval_placeAlg | (intros; apply GlobalTheory.GraphLocal.FlatPlace.flat_aeval_placeAlg <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

theorem _root_.GlobalTheory.T.graphJets_mem_pow_sup_uniformiser : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring),
  graphIdeal E R π ρ ≤ 𝔭 → Irreducible t →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ') (w : tens (κ' := κ') (placeAlg E)),
    (w : K ⊗[ℂ] κ') = ∑ i, (a i : K) ⊗ₜ b i →
    ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
    w ∈ 𝔭 ^ M ⊔ Ideal.span {⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩} := by
  first | exact @GlobalTheory.GraphLocal.jets_mem_pow_sup | exact GlobalTheory.GraphLocal.jets_mem_pow_sup | (intros; apply GlobalTheory.GraphLocal.jets_mem_pow_sup <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

theorem _root_.GlobalTheory.T.graphIdeal_localization_maximalIdeal_eq_span : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    [Algebra (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (k : ℕ) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (hER : E.Contains R) (t : E.ring) (zR : Fin k → R)
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  Irreducible t → TrBasis (algebraMap ℂ κ) (fun i => π (zR i)) →
  𝔭 ∈ (graphIdeal E R π ρ).minimalPrimes →
  letI := isLocalRing_locAt (L := L) 𝔭 (IsFractionRing.injective (K ⊗[ℂ] κ') L)
  IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) =
    Ideal.span (Set.range fun i => toQ 𝔭 (gens E R π ρ hER t zR i)) := by
  first | exact @GlobalTheory.GraphLocal.MaxGen.maximalIdeal_locAt_eq_span | exact GlobalTheory.GraphLocal.MaxGen.maximalIdeal_locAt_eq_span | (intros; apply GlobalTheory.GraphLocal.MaxGen.maximalIdeal_locAt_eq_span <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.double_scaling_iwasawa_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)) (g : GL (Fin d ⊕ Fin d) (Fv F v)),
      ∃ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v), GlobalTheory.DblScal.locMatD t c p = g := by
  first | exact @GlobalTheory.DblSurj.exists_locMatD_eq | exact GlobalTheory.DblSurj.exists_locMatD_eq | (intros; apply GlobalTheory.DblSurj.exists_locMatD_eq <;> assumption)
end
