module

public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle768
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle994
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg.MinSecond

section Transport

variable {p q : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isHW_equiv (e : V ≃ₗ[ℂ] W) (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (b : Mat p q →ₗ[ℂ] Module.End ℂ W) (h : ∀ Z v, e (a Z v) = b Z (e v))
    (μ : Ix p q → ℚ) (v : V) (hv : IsHW a μ v) : IsHW b μ (e v) := by
  obtain ⟨h0, h1⟩ := hv
  refine ⟨fun h' => h0 (e.map_eq_zero_iff.mp h'), ?_⟩
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1 ⊢
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [← h, ← map_smul, ← map_sub, h1.1 i, map_zero]
  · rw [← h, h1.2 i j hij, map_zero]

theorem symm_equivariant (e : V ≃ₗ[ℂ] W) (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (b : Mat p q →ₗ[ℂ] Module.End ℂ W) (h : ∀ Z v, e (a Z v) = b Z (e v)) (Z : Mat p q) (w : W) :
    e.symm (b Z w) = a Z (e.symm w) := by
  apply e.injective
  rw [h, e.apply_symm_apply, e.apply_symm_apply]

theorem ofType_equiv (e : V ≃ₗ[ℂ] W) (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (b : Mat p q →ₗ[ℂ] Module.End ℂ W) (h : ∀ Z v, e (a Z v) = b Z (e v))
    (μ : Ix p q → ℚ) (v : V) (hv : OfType a μ v) : OfType b μ (e v) := by
  obtain ⟨U, hf, hvU, hst, hw⟩ := hv
  refine ⟨U.map (e : V →ₗ[ℂ] W), inferInstance, ⟨v, hvU, rfl⟩, ?_, ?_⟩
  · rintro X hX _ ⟨u, hu, rfl⟩
    exact ⟨a X u, hst X hX u hu, h X u⟩
  · rintro ν _ ⟨u, hu, rfl⟩ hν
    refine hw ν u hu ?_
    have := isHW_equiv e.symm b a (symm_equivariant e a b h) ν _ hν
    simpa using this

theorem genSub_map (e : V →ₗ[ℂ] W) (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (b : Mat p q →ₗ[ℂ] Module.End ℂ W) (h : ∀ Z v, e (a Z v) = b Z (e v))
    (S : Set V) (T : Set W) (hST : ∀ v ∈ S, e v ∈ T) (v : V) (hv : v ∈ genSub a S) :
    e v ∈ genSub b T := by
  simp only [genSub, Submodule.mem_sInf, Set.mem_ofPred_eq] at hv ⊢
  intro N hN
  refine hv (N.comap e) ⟨fun x hx => hN.1 (hST x hx), fun Z y hy => ?_⟩
  rw [Submodule.mem_comap, h]
  exact hN.2 Z _ hy

end Transport

noncomputable def swapPol (p q r s : ℕ) : Pol p q r s ≃ₗ[ℂ] Pol r s p q :=
  (renameEquiv ℂ (Equiv.prodComm (Ix p q) (Ix r s))).toLinearEquiv

end GlobalTheory.FockAlg.MinSecond


open GlobalTheory.FockAlg.MinSecond in
theorem GlobalTheory.FockAlg.min_second : ∀ (p q r s : ℕ) (M1 : GKMod p q) (M2 : GKMod r s) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ M1.V M2.V), IrrGK M2 → AdmGK M2 → Intw M1 M2 f → f ≠ 0 → ∀ (μ' : Ix r s → ℚ), (∃ v, IsHW M2.act μ' v) → (∀ ν w, IsHW M2.act ν w → degW (cPair p q) μ' ≤ degW (cPair p q) ν) → (∃ (μ : Ix p q → ℚ) (P : Pol p q r s), P ∈ jointHarm p q r s ∧ IsHW (fockAct1 p q r s) μ P ∧ IsHW (fockAct2 p q r s) μ' P ∧ f P ≠ 0) ∧ ∀ P, OfType (fockAct2 p q r s) μ' P → f P ∈ Submodule.map f (genSub (fockAct1 p q r s) {Q | Q ∈ jointHarm p q r s ∧ OfType (fockAct2 p q r s) μ' Q}) := by
  intro p q r s M1 M2 f hirr hadm hf hf0 μ' hμ hmin
  obtain ⟨s1, s2, s3⟩ := GlobalTheory.T.fock_dualPair_swap_symmetry r s p q
  set e := swapPol r s p q with he
  have h1 : ∀ Z v, e (fockAct1 r s p q Z v) = fockAct2 p q r s Z (e v) := s1
  have h2 : ∀ Z v, e (fockAct2 r s p q Z v) = fockAct1 p q r s Z (e v) := s2
  have hJ : ∀ P, P ∈ jointHarm r s p q → e P ∈ jointHarm p q r s := fun P hP =>
    ⟨(s3 P).1.mp hP.2, (s3 P).2.mp hP.1⟩
  set c := TensorProduct.comm ℂ M1.V M2.V with hc
  let g : Pol r s p q →ₗ[ℂ] TensorProduct ℂ M2.V M1.V :=
    (c : _ →ₗ[ℂ] _) ∘ₗ f ∘ₗ (e : _ →ₗ[ℂ] _)
  have hg : ∀ P, g P = c (f (e P)) := fun _ => rfl
  have hcm : ∀ (A : Module.End ℂ M1.V) (B : Module.End ℂ M2.V) x,
      c (TensorProduct.map A B x) = TensorProduct.map B A (c x) := by
    intro A B x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hc]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hgI : Intw M2 M1 g := by
    refine ⟨fun X => LinearMap.ext fun P => ?_, fun X => LinearMap.ext fun P => ?_⟩
    · have := LinearMap.congr_fun (hf.2 X) (e P)
      simp only [LinearMap.comp_apply] at this ⊢
      rw [hg, hg, h1, this, hcm]
    · have := LinearMap.congr_fun (hf.1 X) (e P)
      simp only [LinearMap.comp_apply] at this ⊢
      rw [hg, hg, h2, this, hcm]
  have hg0 : g ≠ 0 := by
    intro h
    apply hf0
    refine LinearMap.ext fun P => ?_
    have := LinearMap.congr_fun h (e.symm P)
    rw [hg, e.apply_symm_apply, LinearMap.zero_apply] at this
    exact c.map_eq_zero_iff.mp this
  obtain ⟨⟨μ, P, hP, hP1, hP2, hP0⟩, hB⟩ := GlobalTheory.T.exists_jointHarm_highestWeight_and_map_mem_genSub r s p q M2 M1 g hirr hadm hgI hg0 μ' hμ hmin
  refine ⟨⟨μ, e P, hJ P hP, isHW_equiv e _ _ h2 _ _ hP2, isHW_equiv e _ _ h1 _ _ hP1, ?_⟩, ?_⟩
  · intro h
    apply hP0
    rw [hg, h, map_zero]
  · intro R hR
    obtain ⟨Q, hQ, hQe⟩ := hB (e.symm R)
      (ofType_equiv e.symm _ _ (symm_equivariant e _ _ h1) _ _ hR)
    refine ⟨e Q, ?_, ?_⟩
    · exact genSub_map e.toLinearMap (fockAct2 r s p q) (fockAct1 p q r s) h2
        {Q | Q ∈ jointHarm r s p q ∧ OfType (fockAct1 r s p q) μ' Q}
        {Q | Q ∈ jointHarm p q r s ∧ OfType (fockAct2 p q r s) μ' Q}
        (fun v hv => ⟨hJ v hv.1, ofType_equiv e _ _ h1 _ _ hv.2⟩) Q hQ
    · rw [hg, hg, e.apply_symm_apply] at hQe
      exact c.injective hQe
end

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.SeenHalf

variable {D : D7}

theorem vAdd_add_star (D : D7) (w : D.what₂.places.Pl) (y : D.what₂.LL)
    (hy : y * star y = ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)) :
    vAdd (D.plEq w) y + vAdd (D.plEq w) (star y) = (D.what₂.places.ramIdx w : ℤ) := by
  have hp0 : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
  have hy0 : y ≠ 0 := fun h => hp0 (by rw [← hy, h, zero_mul])
  rw [← GlobalTheory.TypeLoss.additiveValuation_residueChar_eq_ramIndex, ← hy, GlobalTheory.TypeLoss.additiveValuation_mul_of_ne_zero _ hy0 (star_ne_zero.2 hy0)]

theorem vAdd_nonneg_of_isIntegral {K : Type} [Field K] [NumberField K]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {x : K}
    (hx : x ≠ 0) (hi : IsIntegral ℤ x) : 0 ≤ vAdd w x := by
  have h := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := K) w (⟨x, hi⟩ : 𝓞 K)
  have hx' : w.valuation K x ≠ 0 := (map_ne_zero _).2 hx
  unfold vAdd
  rw [neg_nonneg, ← WithZero.log_one, WithZero.log_le_log hx' one_ne_zero]
  exact h

theorem sigmaOf_fix {R : Ranks} (H : Host R) (g : R.Psi) {x : H.E} (hx : x ∈ H.K) : H.sigmaOf g x = x := by
  have h : H.sigmaOf g (H.sqd) = H.sqd := by
    refine (H.galE_mem_Psi_iff _).1 ?_
    have : H.galE (H.sigmaOf g) = g :=
      (H.gal).apply_symm_apply _
    rw [this]
    exact g.2
  have hle : H.K ≤ IntermediateField.fixedField (Subgroup.zpowers (H.sigmaOf g)) := by
    refine IntermediateField.adjoin_simple_le_iff.2 ?_
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have : Subgroup.zpowers (H.sigmaOf g) ≤ MulAction.stabilizer _ (H.sqd) := by
      rw [Subgroup.zpowers_le]
      exact h
    exact this hf
  exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) _ (Subgroup.mem_zpowers _)

theorem ETpi_nonneg (D : D7) (u : D.what₂.Word) : 0 ≤ Formalism.MainNotions.product_first_zeroth_parts.ETpi D u := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.ETpi
  positivity

theorem sz_ET_nonneg (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    0 ≤ SizeData₂.sz w (Formalism.MainNotions.product_first_zeroth_parts.ET D u w) := by
  have h0 := ETpi_nonneg D u
  have l0 : 0 ≤ SizeData₂.lwP w := by
    unfold SizeData₂.lwP lw
    exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  have h1 : 0 ≤ Formalism.MainNotions.product_first_zeroth_parts.ET D u w := by
    rw [Formalism.MainNotions.product_first_zeroth_parts.ET_eq]
    split_ifs
    · exact h0
    · exact le_rfl
  unfold SizeData₂.sz
  positivity

theorem sum_over_eq {X : ErrX D} (hs : SeenDef D X) (u : D.what₂.Word) (S : Finset D.what₂.places.Pl)
    (hS : ∀ w, w ∈ S ↔ D.what₂.places.resChar w = (D.mem u).A.T) :
    ∑ w ∈ S, SizeData₂.sz w (Formalism.MainNotions.product_first_zeroth_parts.ET D u w) = Formalism.MainNotions.product_first_zeroth_parts.ETpi D u * Real.log ((D.mem u).A.T : ℝ) := by
  have hT : ((D.mem u).A.T).Prime := (D.mem u).A.T_prime
  set y : D.what₂.LL := D.embE (X.piT u : D.host.E) with hy
  have hn : y * star y = ((D.mem u).A.T : D.what₂.LL) := by
    rw [hy, ← D.embE_conj, ← map_mul, X.piT_norm]
    simp
  have hy0 : y ≠ 0 := fun h => (Nat.cast_ne_zero.2 hT.ne_zero : ((D.mem u).A.T : D.what₂.LL) ≠ 0)
    (by rw [← hn, h, zero_mul])
  have hi1 : IsIntegral ℤ y := IsIntegral.map (D.embE : D.host.E →+* D.what₂.LL).toIntAlgHom (X.piT u).isIntegral_coe
  have hi2 : IsIntegral ℤ (star y) := IsIntegral.map (starRingEnd D.what₂.LL).toIntAlgHom hi1
  rw [← GlobalTheory.TypeLoss.sum_half D _ hT S hS y hn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw := (hS w).1 hw
  have a1 := vAdd_nonneg_of_isIntegral (D.plEq w) hy0 hi1
  have a2 := vAdd_nonneg_of_isIntegral (D.plEq w) (star_ne_zero.2 hy0) hi2
  have a3 := vAdd_add_star D w y (by rw [hw]; exact hn)
  have a4 := GlobalTheory.LevelCoprime.coprime_conj X u w hw
  rw [← hy] at a4
  have a5 : (D.fm u).seenP w = true ↔ 0 < vAdd (D.plEq w) y := by
    rw [hs u w hw]
    have e : ∀ τ, tauLL D τ (X.piT u : D.host.E) = y := fun τ => by
      unfold tauLL
      rw [sigmaOf_fix D.host (D.eTau τ) (X.piT_K u)]
    simp only [e, D.val_eq w y hy0]
    constructor
    · intro h
      exact_mod_cast h (D.eTau.symm 1)
    · intro h _
      exact_mod_cast h
  rw [Formalism.MainNotions.product_first_zeroth_parts.ET_eq]
  unfold SizeData₂.sz
  by_cases h : (D.fm u).seenP w = true
  · have b1 := a5.1 h
    have b2 : vAdd (D.plEq w) y = (D.what₂.places.ramIdx w : ℤ) := by
      by_contra hne
      exact a4 ⟨b1, by omega⟩
    rw [if_pos h, b2]
    push_cast
    ring
  · have b2 : vAdd (D.plEq w) y = 0 := by
      have := mt a5.2 h
      omega
    rw [if_neg h, b2]
    simp

theorem seen_half : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word) (S : Finset (Fm.D x i).what₂.places.Pl), (∀ w ∈ S, Formalism.MainNotions.product_first_zeroth_parts.OverT (Fm.D x i) u w) → 0 ≤ ∑ w ∈ S, SizeData₂.sz w (Formalism.MainNotions.product_first_zeroth_parts.ET (Fm.D x i) u w) ∧ ∑ w ∈ S, SizeData₂.sz w (Formalism.MainNotions.product_first_zeroth_parts.ET (Fm.D x i) u w) ≤ Formalism.MainNotions.product_first_zeroth_parts.ETpi (Fm.D x i) u * Real.log (((Fm.D x i).mem u).A.T : ℝ) := by
  intro eps Fm x hx i u S hS
  refine ⟨Finset.sum_nonneg fun w _ => sz_ET_nonneg _ u w, ?_⟩
  obtain ⟨S', hS'⟩ := GlobalTheory.TypeLoss.exists_over (Fm.D x i) _ ((Fm.D x i).mem u).A.T_prime
  rw [← sum_over_eq (Fm.ex x hx i).err.seen u S' hS']
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => (hS' w).2 (hS w hw)) fun w _ _ => sz_ET_nonneg _ u w

end GlobalTheory.SeenHalf
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

section LocalizationBaseChange

variable {R R' C' L ν σ : Type} [CommRing R] [CommRing R'] [CommRing C'] [CommRing L] (a : R →+* R')
  [Algebra R' C'] [Algebra C' L] (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R) (ξ : ν → C')

theorem localization_baseChange_ext (hsurj : Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C'))
    [IsLocalization.Away (MvPolynomial.aeval ξ (MvPolynomial.map a h)) L] {T : Type} [CommRing T]
    (w₁ w₂ : L →+* T)
    (h₁ : ∀ r : R', w₁ (algebraMap C' L (algebraMap R' C' r)) = w₂ (algebraMap C' L (algebraMap R' C' r)))
    (h₂ : ∀ i, w₁ (algebraMap C' L (ξ i)) = w₂ (algebraMap C' L (ξ i))) : w₁ = w₂ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (MvPolynomial.aeval ξ (MvPolynomial.map a h)))
  refine RingHom.ext fun c => ?_
  obtain ⟨P, rfl⟩ := hsurj c
  have e : w₁.comp ((algebraMap C' L).comp (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom) =
      w₂.comp ((algebraMap C' L).comp (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa using h₁ r
    · intro i
      simpa using h₂ i
  exact congr($e P)

theorem localization_baseChange_desc (hsurj : Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C'))
    (hker : ∀ G : MvPolynomial ν R', MvPolynomial.aeval ξ G = 0 →
      MvPolynomial.map a h * G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)))
    [IsLocalization.Away (MvPolynomial.aeval ξ (MvPolynomial.map a h)) L] {T : Type} [CommRing T]
    (u : Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) →+* T) (v : R' →+* T)
    (huv : ∀ r : R, u (algebraMap R _ r) = v (a r)) :
    ∃ w : L →+* T, (∀ G : MvPolynomial ν R, w (algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a G))) =
        u (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ G))) ∧
      ∀ r : R', w (algebraMap C' L (algebraMap R' C' r)) = v r := by
  let θ : MvPolynomial ν R' →+* T := MvPolynomial.eval₂Hom v (fun i ↦
    u (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ (MvPolynomial.X i))))
  have hθ : θ.comp (MvPolynomial.map a) = u.comp ((algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F))
      (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h))).comp (Ideal.Quotient.mk _)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.map_C, θ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      rw [← huv]
      rfl
    · intro i
      simp [θ]
  have hθ' : ∀ G, θ (MvPolynomial.map a G) =
      u (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ G)) :=
    fun G ↦ congr($hθ G)
  have hunit : IsUnit (θ (MvPolynomial.map a h)) := by
    rw [hθ']
    exact (IsLocalization.Away.algebraMap_isUnit _).map u
  have hspan : Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ≤ RingHom.ker θ := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, hθ', (Ideal.Quotient.eq_zero_iff_mem (a := F s) (I := Ideal.span (Set.range F))).2 (Ideal.subset_span ⟨s, rfl⟩),
      map_zero, map_zero]
  have hk : RingHom.ker (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom ≤ RingHom.ker θ := by
    intro G hG
    rw [RingHom.mem_ker] at hG
    have e := RingHom.mem_ker.1 (hspan (hker G hG))
    rw [map_mul] at e
    exact RingHom.mem_ker.2 ((hunit.mul_right_eq_zero).1 e)
  let θ' : C' →+* T := (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom.liftOfRightInverse
    (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨θ, hk⟩
  have hθ'e : ∀ P, θ' (MvPolynomial.aeval ξ P) = θ P := fun P ↦
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ P
  have hu2 : IsUnit (θ' (MvPolynomial.aeval ξ (MvPolynomial.map a h))) := by
    rw [hθ'e]
    exact hunit
  refine ⟨IsLocalization.Away.lift (MvPolynomial.aeval ξ (MvPolynomial.map a h)) hu2, fun G ↦ ?_, fun r ↦ ?_⟩
  · rw [IsLocalization.Away.lift_eq, hθ'e, hθ']
  · rw [IsLocalization.Away.lift_eq, ← MvPolynomial.aeval_C (R := R') ξ r, hθ'e]
    simp [θ]

end LocalizationBaseChange

theorem isPushout_localization_baseChange : ∀ (R R' C' L ν σ : Type) [CommRing R] [CommRing R'] [CommRing C'] [CommRing L] (a : R →+* R') [Algebra R' C'] [Algebra C' L] (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R) (ξ : ν → C'), Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') → (∀ s, MvPolynomial.aeval ξ (MvPolynomial.map a (F s)) = 0) → (∀ G : MvPolynomial ν R', MvPolynomial.aeval ξ G = 0 → MvPolynomial.map a h * G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s))) → IsLocalization.Away (MvPolynomial.aeval ξ (MvPolynomial.map a h)) L → ∃ α : Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) →+* L, IsPushout (CommRingCat.ofHom (algebraMap R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)))) (CommRingCat.ofHom a) (CommRingCat.ofHom α) (CommRingCat.ofHom ((algebraMap C' L).comp (algebraMap R' C'))) ∧ ∀ G : MvPolynomial ν R, α (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ G)) = algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a G)) := by
  intro R R' C' L ν σ _ _ _ _ a _ _ F h ξ hsurj hF hker hL
  have hI : Ideal.span (Set.range F) ≤
      RingHom.ker ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom.comp (MvPolynomial.map a)) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨s, rfl⟩
    exact RingHom.mem_ker.2 (hF s)
  let β := Ideal.Quotient.lift (Ideal.span (Set.range F))
    ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom.comp (MvPolynomial.map a))
    (fun x hx ↦ RingHom.mem_ker.1 (hI hx))
  have hβ : ∀ G, β (Ideal.Quotient.mk _ G) = MvPolynomial.aeval ξ (MvPolynomial.map a G) := fun G ↦ rfl
  have hu : IsUnit (((algebraMap C' L).comp β) (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) := by
    rw [RingHom.comp_apply, hβ]
    exact IsLocalization.Away.algebraMap_isUnit _
  let α : Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) →+* L :=
    IsLocalization.Away.lift (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) hu
  have hα : ∀ G : MvPolynomial ν R, α (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _
      (Ideal.Quotient.mk _ G)) = algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a G)) := fun G ↦ by
    simp only [α]
    rw [IsLocalization.Away.lift_eq, RingHom.comp_apply, hβ]
  have hR : ∀ r : R, algebraMap R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) r =
      algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ (MvPolynomial.C r)) :=
    fun r ↦ rfl
  refine ⟨α, IsPushout.of_isColimit' ⟨?_⟩ (PushoutCocone.IsColimit.mk _
    (fun s ↦ CommRingCat.ofHom (Classical.choose (localization_baseChange_desc (L := L) a F h ξ hsurj hker s.inl.hom s.inr.hom
      (fun r ↦ congr($(s.condition) r))))) ?_ ?_ ?_), hα⟩
  · ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [hR, hα]
    simp
  · intro s
    obtain ⟨hd1, -⟩ := Classical.choose_spec (localization_baseChange_desc (L := L) a F h ξ hsurj hker s.inl.hom s.inr.hom
      (fun r ↦ congr($(s.condition) r)))
    apply CommRingCat.hom_ext
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    apply IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range F)) h))
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun G ↦ ?_
    simp only [RingHom.comp_apply]
    rw [hα, hd1]
  · intro s
    obtain ⟨-, hd2⟩ := Classical.choose_spec (localization_baseChange_desc (L := L) a F h ξ hsurj hker s.inl.hom s.inr.hom
      (fun r ↦ congr($(s.condition) r)))
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    exact hd2 r
  · intro s m h₁ h₂
    obtain ⟨hd1, hd2⟩ := Classical.choose_spec (localization_baseChange_desc (L := L) a F h ξ hsurj hker s.inl.hom s.inr.hom
      (fun r ↦ congr($(s.condition) r)))
    apply CommRingCat.hom_ext
    simp only [CommRingCat.hom_ofHom]
    apply localization_baseChange_ext a h ξ hsurj
    · intro r
      rw [hd2]
      exact congr($h₂ r)
    · intro i
      have e : algebraMap C' L (ξ i) = algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a (MvPolynomial.X i))) := by
        simp
      rw [e, hd1, ← hα]
      exact congr($h₁ _)

end GlobalTheory.Pinch
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pinch_gens_adapted : ∀ (R R₀ R' C' D E ν : Type) [CommRing R] [CommRing R₀] [CommRing R'] [CommRing C'] [CommRing D] [CommRing E] [Algebra R' C'] [Algebra.FiniteType R' C'] [Algebra R₀ D] (a : R →+* R') (m : R →+* R₀) (π : C' →+* E) (ψ : D →+* E) (ζ : ν → D), Function.Surjective m → Function.Surjective π → Function.Surjective (MvPolynomial.aeval ζ : MvPolynomial ν R₀ →ₐ[R₀] D) → IsPushout (CommRingCat.ofHom ((algebraMap R₀ D).comp m)) (CommRingCat.ofHom a) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp (algebraMap R' C'))) → ∃ (κ : Type) (_ : Finite κ) (ξ : κ ⊕ ν → C'), (∀ s, π (ξ s) = ψ (Sum.elim (fun _ ↦ 0) ζ s)) ∧ Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial (κ ⊕ ν) R' →ₐ[R'] C') := by
  intro R R₀ R' C' D E ν _ _ _ _ _ _ _ _ _ a m π ψ ζ hm hπ hζ po
  choose ξ₀ hξ₀ using fun s => hπ (ψ (ζ s))
  have hcomm : ψ.comp ((algebraMap R₀ D).comp m) = (π.comp (algebraMap R' C')).comp a := by
    have := po.w
    exact congrArg CommRingCat.Hom.hom this
  have hsurj : Function.Surjective (π.comp (MvPolynomial.aeval ξ₀ : MvPolynomial ν R' →ₐ[R'] C').toRingHom) := by
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨r, rfl⟩)
    · obtain ⟨f, rfl⟩ := hζ d
      obtain ⟨g, rfl⟩ := MvPolynomial.map_surjective m hm f
      refine ⟨MvPolynomial.map a g, ?_⟩
      simp only [CommRingCat.hom_ofHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      induction g using MvPolynomial.induction_on with
      | C c =>
        have := congrArg (fun h => h c) hcomm
        simpa using this.symm
      | add p q hp hq => simp [hp, hq]
      | mul_X p s hp => simp [hp, hξ₀]
    · exact ⟨MvPolynomial.C r, by simp⟩
  obtain ⟨S, hS⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R' C').FG)
  choose p hp using fun t : S => hsurj (π t)
  refine ⟨S, inferInstance, Sum.elim (fun t => (t : C') - MvPolynomial.aeval ξ₀ (p t)) ξ₀, ?_, ?_⟩
  · rintro (t | s)
    · have := hp t
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
      simp [map_sub, this]
    · simp [hξ₀]
  · intro x
    have hx : x ∈ Algebra.adjoin R' (S : Set C') := by rw [hS]; trivial
    have hle : Algebra.adjoin R' (S : Set C') ≤
        (MvPolynomial.aeval (Sum.elim (fun t : S => (t : C') - MvPolynomial.aeval ξ₀ (p t)) ξ₀) :
          MvPolynomial (S ⊕ ν) R' →ₐ[R'] C').range := by
      rw [Algebra.adjoin_le_iff]
      intro t ht
      refine ⟨MvPolynomial.X (Sum.inl ⟨t, ht⟩) + MvPolynomial.rename Sum.inr (p ⟨t, ht⟩), ?_⟩
      simp [MvPolynomial.aeval_rename, Function.comp_def]
    obtain ⟨y, hy⟩ := hle hx
    exact ⟨y, hy⟩

end GlobalTheory
end
