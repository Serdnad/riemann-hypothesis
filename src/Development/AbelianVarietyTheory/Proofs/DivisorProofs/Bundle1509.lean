module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1426
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import GroundTheory.Brauer.BaseChangeCSA
import GroundTheory.Brauer.TensorSimple
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.affineArithmeticCurve_finsum_ord_log_eq_localLengths : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] [IsAffine Y] (q : Y ⟶ Sp k), IsArithVar q 0 → ∀ b : Γ(Y, ⊤), b ≠ 0 → ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField b) z : ℝ) * Real.log (Nat.card (Y.residueField z)) = ∑ᶠ m : MaximalSpectrum Γ(Y, ⊤), ((Module.length (Localization.AtPrime m.asIdeal) (LocalizedModule m.asIdeal.primeCompl (Γ(Y, ⊤) ⧸ Ideal.span {b}))).toNat : ℝ) * Real.log (Nat.card (Γ(Y, ⊤) ⧸ m.asIdeal)) := by
  first | exact @GlobalTheory.AffineCurveSum.finsum_ord_eq | exact GlobalTheory.AffineCurveSum.finsum_ord_eq | (intros; apply GlobalTheory.AffineCurveSum.finsum_ord_eq <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.arithmeticCurve_isAffine_and_finite_int : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsArithVar q 0 → IsAffine Y ∧ Module.Finite ℤ Γ(Y, ⊤) := by
  first | exact @GlobalTheory.ArithCurve.isAffine_and_finite | exact GlobalTheory.ArithCurve.isAffine_and_finite | (intros; apply GlobalTheory.ArithCurve.isAffine_and_finite <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.ResidueTrBasis

open IsLocalRing

theorem trdeg_le_of_residue {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K)
    (S : Place cL) (ψ : S.ring →+* K) (hψ : Function.Surjective ψ)
    (hc : ∀ a, ψ (S.const a) = cK a) (m : ℕ) (x : Fin (m + 2) → L) (hx : TrBasis cL x) :
    letI := cK.toAlgebra
    Algebra.trdeg ℂ K ≤ (m + 1 : ℕ) := by
  letI : Algebra ℂ S.ring := S.const.toAlgebra
  letI : Algebra ℂ L := cL.toAlgebra
  letI : Algebra ℂ K := cK.toAlgebra
  haveI : IsScalarTower ℂ S.ring L := IsScalarTower.of_algebraMap_eq' rfl
  have hcomp : ψ.comp (algebraMap ℂ S.ring) = algebraMap ℂ K := RingHom.ext hc
  haveI : Algebra.EssFiniteType ℂ S.ring := S.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ S.ring
  have hker : RingHom.ker ψ = maximalIdeal S.ring := by
    haveI := RingHom.ker_isMaximal_of_surjective ψ hψ
    exact IsLocalRing.eq_maximalIdeal this
  have hL : Algebra.trdeg ℂ L = (m + 2 : ℕ) := by
    have := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
    rw [Cardinal.mk_fin] at this
    exact this.symm
  have hR : Algebra.trdeg ℂ (ResidueField S.ring) = (m + 1 : ℕ) :=
    trdeg_residueField_of_trdeg ℂ S.ring L hL
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℂ K
  let res := IsLocalRing.residue S.ring
  let lift : s → S.ring := fun i => Function.surjInv hψ (i : K)
  have hlift : ψ ∘ lift = Subtype.val := funext fun i => Function.surjInv_eq hψ _
  have hg : AlgebraicIndependent ℂ (fun i => res (lift i)) := by
    refine algebraicIndependent_iff.2 fun P hP => ?_
    have h0 : res (MvPolynomial.eval₂ (algebraMap ℂ S.ring) lift P) = 0 := by
      rw [MvPolynomial.eval₂_comp_left]
      exact hP
    rw [IsLocalRing.residue_eq_zero_iff, ← hker, RingHom.mem_ker, MvPolynomial.hom_eval₂,
      hcomp, show (fun i => ψ (lift i)) = Subtype.val from hlift] at h0
    exact algebraicIndependent_iff.1 hs.1 P h0
  have h1 := hg.cardinalMk_le_trdeg
  rw [hs.cardinalMk_eq_trdeg, hR] at h1
  exact h1

theorem trBasis_cons : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (S : Place cL) (ψ : S.ring →+* K),
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) →
  ∀ (F : Place cK) (m : ℕ) (π : K) (y : Fin m → K), (∃ x : Fin (m + 2) → L, TrBasis cL x) →
  F.ord π = 1 → (∀ i, y i ∈ F.ring) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK y P ≠ 0 ∧ (MvPolynomial.eval₂ cK y P)⁻¹ ∈ F.ring) →
  TrBasis cK (Fin.cons π y : Fin (m + 1) → K) := by
  intro L K _ _ cL cK S ψ hψ hc F m π y ⟨x, hx⟩ hπ hy hP
  have htr := trdeg_le_of_residue cL cK S ψ hψ hc m x hx
  letI : Algebra ℂ F.ring := F.const.toAlgebra
  letI : Algebra ℂ K := cK.toAlgebra
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp [Place.ord] at hπ
  have hπm : π ∈ F.ring := (F.ord_nonneg_iff hπ0).1 (by omega)
  let f : F.ring := ⟨π, hπm⟩
  have hf0 : f ≠ 0 := fun h => hπ0 (congrArg Subtype.val h)
  have hfm : f ∈ maximalIdeal F.ring := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := F.ord_eq_zero hu
    change F.ord π = 0 at this
    omega
  let w : Fin m → F.ring := fun i => ⟨y i, hy i⟩
  have hev : ∀ P : MvPolynomial (Fin m) ℂ,
      ((MvPolynomial.eval₂ (algebraMap ℂ F.ring) w P : F.ring) : K) = MvPolynomial.eval₂ cK y P := by
    intro P
    have h := MvPolynomial.hom_eval₂ P (algebraMap ℂ F.ring) F.ring.subtype w
    rw [ValuationSubring.subtype_apply] at h
    rw [h]
    rfl
  have hwu : ∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 →
      IsUnit (MvPolynomial.eval₂ (algebraMap ℂ F.ring) w P) := by
    intro P hP0
    obtain ⟨h1, h2⟩ := hP P hP0
    refine IsUnit.of_mul_eq_one (⟨_, h2⟩ : F.ring) (Subtype.ext ?_)
    change ((MvPolynomial.eval₂ (algebraMap ℂ F.ring) w P : F.ring) : K) * _ = 1
    rw [hev]
    exact mul_inv_cancel₀ h1
  have hsplit : ∀ P : MvPolynomial (Fin (m + 1)) ℂ,
      MvPolynomial.eval₂ (algebraMap ℂ F.ring) (Fin.cons f w : Fin (m + 1) → F.ring) P =
        Polynomial.eval f (Polynomial.map (MvPolynomial.eval₂Hom (algebraMap ℂ F.ring) w)
          (MvPolynomial.finSuccEquiv ℂ m P)) := by
    intro P
    have hrh : MvPolynomial.eval₂Hom (algebraMap ℂ F.ring) (Fin.cons f w : Fin (m + 1) → F.ring) =
        (Polynomial.evalRingHom f).comp
          ((Polynomial.mapRingHom (MvPolynomial.eval₂Hom (algebraMap ℂ F.ring) w)).comp
            (MvPolynomial.finSuccEquiv ℂ m : MvPolynomial (Fin (m + 1)) ℂ →+* _)) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [MvPolynomial.finSuccEquiv_apply]
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i <;>
          simp [MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
    exact RingHom.congr_fun hrh P
  have hcoe : ∀ P : MvPolynomial (Fin (m + 1)) ℂ,
      MvPolynomial.aeval (Fin.cons π y : Fin (m + 1) → K) P =
        ((MvPolynomial.eval₂ (algebraMap ℂ F.ring) (Fin.cons f w : Fin (m + 1) → F.ring) P :
          F.ring) : K) := by
    intro P
    have h := MvPolynomial.hom_eval₂ P (algebraMap ℂ F.ring) F.ring.subtype
      (Fin.cons f w : Fin (m + 1) → F.ring)
    rw [ValuationSubring.subtype_apply] at h
    rw [h, MvPolynomial.aeval_def]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have hind : AlgebraicIndependent ℂ (Fin.cons π y : Fin (m + 1) → K) := by
    refine algebraicIndependent_iff.2 fun P hP => ?_
    rw [hcoe, ZeroMemClass.coe_eq_zero, hsplit] at hP
    set Q := MvPolynomial.finSuccEquiv ℂ m P with hQ
    have hq := eq_zero_of_eval_mem_maximalIdeal hf0 hfm _ (fun i hi => by
      rw [Polynomial.coeff_map] at hi ⊢
      refine hwu _ fun h0 => hi ?_
      rw [h0, map_zero]) hP
    have hQ0 : Q = 0 := by
      apply Polynomial.ext
      intro i
      rw [Polynomial.coeff_zero]
      by_contra h0
      apply (hwu _ h0).ne_zero
      have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) hq
      simpa [Polynomial.coeff_map] using this
    exact (MvPolynomial.finSuccEquiv ℂ m).injective (by rw [← hQ, hQ0, map_zero])
  unfold TrBasis
  refine hind.isTranscendenceBasis_of_trdeg_le_of_finite ?_
  rw [Cardinal.mk_fin]
  exact htr

end GlobalTheory.FieldPair.ResidueTrBasis
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.formOrd_kaehlerWedge_uniformiser_residueIndependent_eq_zero : ∀ {K : Type} [Field K] (cK : ℂ →+* K) (F : Place cK) (m : ℕ) (π : K) (y : Fin m → K),
  F.ord π = 1 → (∀ i, y i ∈ F.ring) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK y P ≠ 0 ∧ (MvPolynomial.eval₂ cK y P)⁻¹ ∈ F.ring) →
  TrBasis cK (Fin.cons π y : Fin (m + 1) → K) →
  (fun ω => @dite ℤ (∃ a, F.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cK (Fin.cons π y : Fin (m + 1) → K)) = 0 := by
  first | exact @GlobalTheory.formOrd_dForm_cons_of_ord_eq_one | exact GlobalTheory.formOrd_dForm_cons_of_ord_eq_one | (intros; apply GlobalTheory.formOrd_dForm_cons_of_ord_eq_one <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem count_kernel_nonzero : ∀ {κ κ' : Type} [Field κ] [Field κ'] [Algebra ℂ κ] [Algebra ℂ κ'] (k c M l : ℕ) (ρ : Fin c → (κ →ₐ[ℂ] κ'))
    (w : Fin l → κ), (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) → c * (M + k - 1).choose k < l →
  ∃ b : Fin l → κ', b ≠ 0 ∧ ∀ i, ∑ j, w j ⊗ₜ[ℂ] b j ∈
    (RingHom.ker (Algebra.TensorProduct.productMap (ρ i) (AlgHom.id ℂ κ'))) ^ M := by
  intro κ κ' _ _ _ _ k c M l ρ w hz hlt
  letI : Algebra κ' (κ ⊗[ℂ] κ') := Algebra.TensorProduct.rightAlgebra
  set J : Fin c → Ideal (κ ⊗[ℂ] κ') := fun i =>
    (RingHom.ker (Algebra.TensorProduct.productMap (ρ i) (AlgHom.id ℂ κ'))) ^ M with hJ
  have hjet := fun i => GlobalTheory.T.finrank_graphJets_le_choose k M (ρ i) hz
  haveI : ∀ i, Module.Finite κ' ((κ ⊗[ℂ] κ') ⧸ J i) := fun i => (hjet i).2
  let g : (Fin l → κ') →ₗ[κ'] (κ ⊗[ℂ] κ') := Fintype.linearCombination κ' (fun j => w j ⊗ₜ[ℂ] (1 : κ'))
  have hg : ∀ b, g b = ∑ j, w j ⊗ₜ[ℂ] b j := by
    intro b
    simp only [g, Fintype.linearCombination_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
    show (1 ⊗ₜ[ℂ] b j) * (w j ⊗ₜ[ℂ] (1 : κ')) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  let f : (Fin l → κ') →ₗ[κ'] ((i : Fin c) → (κ ⊗[ℂ] κ') ⧸ J i) :=
    LinearMap.pi fun i => (Ideal.Quotient.mkₐ κ' (J i)).toLinearMap.comp g
  have hdim : Module.finrank κ' ((i : Fin c) → (κ ⊗[ℂ] κ') ⧸ J i) < Module.finrank κ' (Fin l → κ') := by
    rw [Module.finrank_pi_fintype, Module.finrank_fin_fun]
    calc ∑ i, Module.finrank κ' ((κ ⊗[ℂ] κ') ⧸ J i) ≤ ∑ _i : Fin c, (M + k - 1).choose k :=
          Finset.sum_le_sum fun i _ => (hjet i).1
      _ = c * (M + k - 1).choose k := by simp
      _ < l := hlt
  obtain ⟨b, hbker, hb0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
  refine ⟨b, hb0, fun i => ?_⟩
  have := congr_fun (LinearMap.mem_ker.mp hbker) i
  simp only [f, LinearMap.pi_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Pi.zero_apply] at this
  rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hg] at this
  exact this

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

theorem _root_.GlobalTheory.T.exists_dvrPlace_equiv_of_ringEquiv_over_constants : ∀ {k K K' : Type} [Field k] [CharZero k] [Field K] [Field K'] (c : k →+* K) (c' : k →+* K') (e : K ≃+* K'), (∀ a, e (c a) = c' a) → ∃ Φ : Place c ≃ Place c', ∀ E : Place c, (∀ a, e a ∈ (Φ E).ring ↔ a ∈ E.ring) ∧ (∀ a, (Φ E).ord (e a) = E.ord a) ∧ (∀ φ : K →₀ ℚ, (Φ E).ordQ (Finsupp.mapDomain e φ) = E.ordQ φ) ∧ ∀ (n : ℕ) (x : Fin n → K), TrBasis c x → (Φ E).formOrd (dForm c' (e ∘ x)) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm c x) := by
  first | exact @GlobalTheory.FieldPair.placeEquiv_ringEquiv | exact GlobalTheory.FieldPair.placeEquiv_ringEquiv | (intros; apply GlobalTheory.FieldPair.placeEquiv_ringEquiv <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem roots_eig : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F) (w : ℂ),
    P.pol.eval₂ v.embedding w = 0 → ∃ x : Fin G.n → ℂ, x ≠ 0 ∧ G.psi v P.γ *ᵥ x = w • x := by
  intro p _ G P v w hw
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  have hτ : algebraMap G.F ℂ = v.embedding := rfl
  let ψF : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ :=
    { G.psi v with
      commutes' := fun x => by
        show G.psi v (algebraMap G.F G.C x) = _
        rw [G.psi_F, Matrix.algebraMap_eq_diagonal]
        rfl }
  let Ψ : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψF (fun a _ => Algebra.commute_algebraMap_left a _)
  haveI : Nontrivial (Matrix (Fin G.n) (Fin G.n) ℂ) := by
    haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
    infer_instance
  have hinj : Function.Injective Ψ := RingHom.injective (Ψ : ℂ ⊗[G.F] G.C →+* Matrix (Fin G.n) (Fin G.n) ℂ)
  set Γ := G.psi v P.γ with hΓ
  have hΨ : ∀ k : ℕ, Ψ (1 ⊗ₜ ((P.γ : G.C) ^ k)) = Γ ^ k := by
    intro k
    calc Ψ (1 ⊗ₜ ((P.γ : G.C) ^ k)) = Algebra.ofId ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) 1 * ψF ((P.γ : G.C) ^ k) :=
          Algebra.TensorProduct.lift_tmul _ _ _ _ _
      _ = Γ ^ k := by rw [map_one, one_mul, map_pow]; rfl
  have hli0 := Module.Flat.linearIndependent_one_tmul (S := ℂ) (linearIndependent_pow (K := G.F) (P.γ : G.C))
  have hli := hli0.map' Ψ.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
  have hli' : LinearIndependent ℂ (fun i : Fin (minpoly G.F (P.γ : G.C)).natDegree => Γ ^ (i : ℕ)) := by
    have e : (⇑Ψ.toLinearMap ∘ fun i : Fin (minpoly G.F (P.γ : G.C)).natDegree => (1 : ℂ) ⊗ₜ[G.F] ((P.γ : G.C) ^ (i : ℕ))) =
        fun i : Fin (minpoly G.F (P.γ : G.C)).natDegree => Γ ^ (i : ℕ) := by
      funext i
      exact hΨ i
    rw [e] at hli
    exact hli
  have hd : (minpoly G.F (P.γ : G.C)).natDegree = G.n := P.reg.1
  have hint : IsIntegral G.F (P.γ : G.C) := Algebra.IsIntegral.isIntegral _
  have hpm : P.pol.Monic := minpoly.monic hint
  set Q := P.pol.map (algebraMap G.F ℂ) with hQ
  have hQm : Q.Monic := hpm.map _
  have hQdeg : Q.natDegree = G.n := by rw [hQ, hpm.natDegree_map]; exact P.reg.1
  have hQΓ : Polynomial.aeval Γ Q = 0 := by
    rw [hQ, Polynomial.aeval_map_algebraMap]
    have h : Polynomial.aeval (ψF (P.γ : G.C)) P.pol = 0 := by
      rw [Polynomial.aeval_algHom_apply]
      simp [Pair.pol, minpoly.aeval]
    exact h
  have hroot : Q.IsRoot w := by
    rw [Polynomial.IsRoot, hQ, Polynomial.eval_map]; exact hw
  by_contra hne
  push_neg at hne
  have hdet : (Γ - algebraMap ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) w).det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hne x hx0
    rw [Matrix.sub_mulVec, sub_eq_zero] at hx
    rw [hx, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  set R := Q /ₘ (Polynomial.X - Polynomial.C w) with hRdef
  have hQR : (Polynomial.X - Polynomial.C w) * R = Q := Polynomial.mul_divByMonic_eq_iff_isRoot.2 hroot
  have hRΓ : Polynomial.aeval Γ R = 0 := by
    have h1 := hQΓ
    rw [← hQR, map_mul] at h1
    have hu : IsUnit (Polynomial.aeval Γ (Polynomial.X - Polynomial.C w)) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.2 hdet
    exact (hu.mul_right_eq_zero).1 h1
  have hRd : R.natDegree = G.n - 1 := by
    rw [hRdef, Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C w), hQdeg, Polynomial.natDegree_X_sub_C]
  have hR0 : R ≠ 0 := by
    intro h
    rw [h, mul_zero] at hQR
    exact hQm.ne_zero hQR.symm
  have hsum : ∑ i : Fin (minpoly G.F (P.γ : G.C)).natDegree, R.coeff i • Γ ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => R.coeff i • Γ ^ i), hd, ← hRΓ, Polynomial.aeval_eq_sum_range, hRd,
      Nat.sub_add_cancel G.n_pos]
  have hc := Fintype.linearIndependent_iff.1 hli' (fun i => R.coeff i) hsum ⟨G.n - 1, by rw [hd]; have := G.n_pos; omega⟩
  exact hR0 (Polynomial.leadingCoeff_eq_zero.1 (by rw [Polynomial.leadingCoeff, hRd]; exact hc))

end GlobalTheory.LKMid
end

section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount Polynomial
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

theorem charpoly_rho_eq_map_pol (G : HTGroup p) (P : Pair G) (w : Fin G.m) :
    (G.rho w (P.γ : G.C)).charpoly = P.pol.map (G.embW w) := by
  letI : Algebra G.F (G.Fw w) := (G.embW w).toAlgebra
  have hg : ∀ a, G.rho w (algebraMap G.F G.C a) = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) (G.Fw w)) a :=
    fun a => by rw [G.rho_F, Matrix.algebraMap_eq_diagonal]; rfl
  let g : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) (G.Fw w) := { G.rho w with commutes' := hg }
  let L : G.Fw w ⊗[G.F] G.C →ₐ[G.Fw w] Matrix (Fin G.n) (Fin G.n) (G.Fw w) :=
    Algebra.TensorProduct.lift (Algebra.ofId (G.Fw w) _) g (fun r _ => Algebra.commute_algebraMap_left r _)
  haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right (not_subsingleton _)
  have hL : ∀ x : G.C, L ((1 : G.Fw w) ⊗ₜ x) = G.rho w x := fun x => by
    show (Algebra.TensorProduct.lift _ g _) ((1 : G.Fw w) ⊗ₜ x) = _
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  set γ : G.C := (P.γ : G.C) with hγ
  have hdeg : (minpoly G.F γ).natDegree = G.n := P.reg.1
  have hli : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ)) := by
    have := linearIndependent_pow (K := G.F) γ
    rw [hdeg] at this
    exact this
  have hT : LinearIndependent (G.Fw w) (fun i : Fin G.n => (1 : G.Fw w) ⊗ₜ[G.F] (γ ^ (i : ℕ))) := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact Module.Flat.linearIndependent_one_tmul hli
  have hM : LinearIndependent (G.Fw w) (fun i : Fin G.n => (G.rho w γ) ^ (i : ℕ)) := by
    have := hT.map' L.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
    have e : (fun i : Fin G.n => (G.rho w γ) ^ (i : ℕ)) =
        L.toLinearMap ∘ (fun i : Fin G.n => (1 : G.Fw w) ⊗ₜ[G.F] (γ ^ (i : ℕ))) := by
      funext i
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply]
      rw [hL, map_pow]
    rw [e]
    exact this
  have hint : IsIntegral (G.Fw w) (G.rho w γ) := Algebra.IsIntegral.isIntegral _
  set q := minpoly (G.Fw w) (G.rho w γ) with hq
  have hqm : q.Monic := minpoly.monic hint
  have hqdeg : G.n ≤ q.natDegree := by
    by_contra hlt
    push_neg at hlt
    have h0 : aeval (G.rho w γ) q = 0 := minpoly.aeval _ _
    rw [Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range] at h0
    have h1 := Fintype.linearIndependent_iff.1 hM (fun i => q.coeff i) h0 ⟨q.natDegree, hlt⟩
    have h2 : q.coeff q.natDegree = 1 := hqm.coeff_natDegree
    rw [h2] at h1
    exact one_ne_zero h1
  have hpol : aeval (G.rho w γ) (P.pol.map (G.embW w)) = 0 := by
    have h : aeval (g γ) (minpoly G.F γ) = 0 := by rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    change aeval (G.rho w γ) ((minpoly G.F γ).map (algebraMap G.F (G.Fw w))) = 0
    rw [Polynomial.aeval_map_algebraMap]
    exact h
  have hFint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hm1 : (P.pol.map (G.embW w)).Monic := (minpoly.monic hFint).map _
  have hn1 : (P.pol.map (G.embW w)).natDegree = G.n := by
    rw [Polynomial.natDegree_map]; exact hdeg
  have e1 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm hm1 (minpoly.dvd _ _ hpol)
    (by rw [hn1]; exact hqdeg)
  have e2 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm (Matrix.charpoly_monic _)
    (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hqdeg)
  rw [e2, e1]

theorem atP_regular : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G),
    (∀ w, (P.atP.2 w).val.charpoly = P.pol.map (G.embW w)) ∧ regular₂ G P.atP ∧
      ∀ y : P.cent, locC G y.1 ∈ Subgroup.centralizer {P.atP} := by
  intro p _ G P
  have h1 : ∀ w, (P.atP.2 w).val.charpoly = P.pol.map (G.embW w) := fun w => charpoly_rho_eq_map_pol G P w
  refine ⟨h1, fun w => ?_, fun y => ?_⟩
  · show (P.atP.2 w).val.charpoly.Separable
    rw [h1]
    exact P.reg.2.map
  · rw [Subgroup.mem_centralizer_singleton_iff]
    show locC G y.1 * locC G (P.γ, P.c) = locC G (P.γ, P.c) * locC G y.1
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext y.2.1 (mul_comm _ _)

end GlobalTheory.LKMid
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

theorem card_roots_map_pol (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (φ : G.F →+* ℂ) :
    ((P.pol.map φ).roots.toFinset).card = G.n ∧ P.pol.Monic := by
  have hint : IsIntegral G.F (P.γ : G.C) := Algebra.IsIntegral.isIntegral _
  have hmon : P.pol.Monic := minpoly.monic hint
  refine ⟨?_, hmon⟩
  have hsep : (P.pol.map φ).Separable := P.reg.2.map
  have hdeg : (P.pol.map φ).natDegree = G.n := by
    rw [Polynomial.natDegree_map]; exact P.reg.1
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep), ← hdeg]
  exact IsAlgClosed.card_roots_eq_natDegree

end GlobalTheory.LKMid.Pair
end
