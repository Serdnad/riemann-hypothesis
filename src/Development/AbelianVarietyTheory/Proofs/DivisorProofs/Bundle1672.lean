module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinSubstLinSubst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1629
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle533
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1631
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort

theorem exists_rightInv_of_span {F : Type} [Field F] {N n : ℕ} {w : Matrix (Fin N) (Fin n) F}
    (hw : Submodule.span F (Set.range w.col) = ⊤) : ∃ P : Matrix (Fin n) (Fin N) F, w * P = 1 := by
  refine GlobalTheory.ZeroCycleHt.exists_rightInv fun v => ?_
  have hv : v ∈ Submodule.span F (Set.range w.col) := hw ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hv
  refine ⟨c, ?_⟩
  rw [← hc]
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem htMul : HtMul := by
  intro F _ _ B N n w A Λ hL
  obtain ⟨P, hP⟩ := exists_rightInv_of_span hL.spans
  refine ⟨fun a a' G G' hG hG' ha ha' => ?_, fun c hc => ?_⟩
  · exact GlobalTheory.ZeroCycleHt.formHeight_mul 0 0 hP hL.det hG hG' ha ha'
  · have h1 : IsMultiHomogeneous (fun _ : Fin B => 0) (1 : MvPolynomial (Fin B × Fin N) F) := by
      intro t ht b
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at ht
      split_ifs at ht with h
      · subst h; simp
      · exact absurd rfl ht
    have := GlobalTheory.HeightUnique.formHeight_C_mul hL.pos 0 hL.spans hL.det one_ne_zero h1 hc
    rw [mul_one, GlobalTheory.ZeroCycleHt.formHeight_one] at this
    exact this

end GlobalTheory.HSShort
end
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.coeff_linearSubst_column_mem_integralLattice : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ κ : S.Col, κ.x ∈ S.M κ.j → ∀ m, ∑ i, AddMonoidAlgebra.coeff (linSubst S.w (coordP S.mul (c i) κ.β (κ.x : A))) m • b i ∈ S.M S.T := by
  first | exact @GlobalTheory.HSShort.colCoeff_mem | exact GlobalTheory.HSShort.colCoeff_mem | (intros; apply GlobalTheory.HSShort.colCoeff_mem <;> assumption)
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort.DetNe

theorem det_ne_zero_of_indep : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ (col : Fin d → S.Col) (u : Fin (S.D + 1) × Fin S.N → E), LinearIndependent E (fun k => word Φ.mul (fun q j => u ((col k).β q, j)) (Φ.ι (col k).x)) → S.det c col ≠ 0 := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d b c hc col u hind hdet
  obtain ⟨c', hspan, hval⟩ := GlobalTheory.T.hermitianMultiplicationFlat_columns_eval F A S hS E A' s δ Φ d b c hc
  set v : Fin d → A' := fun k => word Φ.mul (fun q j => u ((col k).β q, j)) (Φ.ι (col k).x) with hv
  set M : Matrix (Fin d) (Fin d) E := Matrix.of fun i k => c' i (v k) with hM
  have hMdet : M.det = 0 := by
    have h1 : aeval u (S.det c col) = 0 := by rw [hdet, map_zero]
    rw [Sys.det, AlgHom.map_det] at h1
    convert h1 using 2
    ext i k
    simp only [hM, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]
    exact ((hval (col k) u).2 i).symm
  obtain ⟨a, ha, hMa⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hMdet
  have hmem : ∀ k, v k ∈ Submodule.span E (Φ.ι '' S.V S.T) := fun k => (hval (col k) u).1
  set x : A' := ∑ k, a k • v k with hx
  have hxmem : x ∈ Submodule.span E (Φ.ι '' S.V S.T) :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hmem k)
  have hcx : ∀ i, c' i x = 0 := by
    intro i
    have := congrFun hMa i
    simp only [Matrix.mulVec, dotProduct, hM, Matrix.of_apply, Pi.zero_apply] at this

    rw [hx, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hx0 : x = 0 := by
    rw [← hspan x hxmem]
    simp [hcx]
  have ha0 := (Fintype.linearIndependent_iff.mp hind) a hx0
  exact ha (funext ha0)

end GlobalTheory.HSShort.DetNe
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

theorem _root_.GlobalTheory.T.hermitianSystemSlopeBound_of_determinantSlopeInequality : ∀ (T D : ℕ) (n Λ β Λ₀ ΛD ΛT δ h h' d deg : ℝ), 1 ≤ D → D + 1 ≤ T → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ δ → h - (Real.log n + 1) / 2 ≤ h' → ClaimS T D n Λ β Λ₀ ΛD ΛT δ h' d deg → Formalism.NormVectorIdentities.Items.HSClaimS 26 T D n 1 Λ β ΛD ΛT (Real.log Λ₀) δ h d deg := by
  first | exact @GlobalTheory.HSShortNum.claimS_to_hsClaimS | exact GlobalTheory.HSShortNum.claimS_to_hsClaimS | (intros; apply GlobalTheory.HSShortNum.claimS_to_hsClaimS <;> assumption)
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.hermFamComplexTensorNorm_column_unitSpheres_le : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ (κ : S.Col) (σ : F →+* ℂ) (u : Fin (S.D + 1) × Fin S.N → ℂ), (∀ i, frameNorm (S.fr σ) (fun j => u (i, j)) = 1) → cnrm (S.nm S.T) σ (fun i => eval₂ σ u (coordP S.mul (c i) κ.β (κ.x : A))) b ≤ Real.sqrt S.beta ^ κ.t * (S.nm κ.j).nrm σ κ.x := by
  first | exact @GlobalTheory.HSShort.cnrm_col_le | exact GlobalTheory.HSShort.cnrm_col_le | (intros; apply GlobalTheory.HSShort.cnrm_col_le <;> assumption)
end

section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

theorem starT_invol {p : ℕ} [Fact p.Prime] (G : HTGroup p) (K : Type) [CommRing K] [Algebra ℚ K]
    (x : K ⊗[ℚ] G.C) : (starT G.star K (starT G.star K x).unop).unop = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r c => rw [starT_tmul, starT_tmul, G.star_star]
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]

end GlobalTheory.FinClsLoc
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

open IsDedekindDomain

noncomputable section

namespace GlobalTheory.NormSign

theorem form_of_norm {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    (hrank : Module.finrank K L = 2) (σ : L →+* L) (hσK : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x)
    {t : L} {δ : K} (ht0 : t ≠ 0) (hσt : σ t = -t) (htt : t * t = algebraMap K L δ)
    (v : HeightOneSpectrum (𝓞 K)) {h : K} (h0 : h ≠ 0)
    (hz : ∃ z : v.adicCompletion K ⊗[K] L, Algebra.norm (v.adicCompletion K) z = algebraMap K (v.adicCompletion K) h) :
    ∃ x y : v.adicCompletion K, x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 =
      algebraMap K (v.adicCompletion K) h := by
  have hli : LinearIndependent K ![(1 : L), t] := by
    rw [LinearIndependent.pair_iff]
    intro s c hsc
    by_cases hc : c = 0
    · subst hc
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hsc
      exact ⟨hsc, rfl⟩
    · exfalso
      have ht : t = algebraMap K L (-s / c) := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hsc
        have hc' : algebraMap K L c ≠ 0 := (map_ne_zero _).2 hc
        rw [map_div₀, map_neg, eq_div_iff hc']
        linear_combination hsc
      have h2 : σ t = t := by rw [ht, hσK]
      rw [hσt] at h2
      have : (2 : L) * t = 0 := by linear_combination -h2
      rcases mul_eq_zero.1 this with h | h
      · have h2' : (2 : L) = algebraMap K L 2 := (map_ofNat (algebraMap K L) 2).symm
        rw [h2'] at h
        exact two_ne_zero ((map_eq_zero _).1 h)
      · exact ht0 h
  let e : Module.Basis (Fin 2) K L := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hrank])
  have e0 : e 0 = 1 := by simp [e]
  have e1 : e 1 * e 1 = algebraMap K L δ := by simp [e, htt]
  have hu : IsUnit (algebraMap K (v.adicCompletion K) h) := (map_ne_zero _).2 h0 |>.isUnit
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by omega)
  have hm : hu.unit ∈ GlobalTheory.QuadSymbol.normGroup K L (v.adicCompletion K) := by
    rw [GlobalTheory.QuadSymbol.mem_normGroup_iff]
    obtain ⟨z, hz⟩ := hz
    exact ⟨z, by rw [hz]; rfl⟩
  obtain ⟨x, y, hxy⟩ := (GlobalTheory.QuadSymbol.mem_normGroup_iff_form e e0 e1).1 hm
  exact ⟨x, y, by rw [← hxy]; rfl⟩

theorem exists_toAfP (K : Type) [Field K] [NumberField K] (p : ℕ) :
    ∃ Φ : FiniteAdeleRing (𝓞 K) K →+* AfP p ⊗[ℚ] K, ∀ k : K, Φ (algebraMap K _ k) = 1 ⊗ₜ k := by
  obtain ⟨ι, hι, -⟩ := GlobalTheory.AdeleBaseChange.exists_tensor_finiteAdele_equiv ℚ K
  obtain ⟨e, -⟩ := GlobalTheory.NormLevelCompare.exists_adele_equiv
  let g : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] AfP p :=
    ((AfP.restr p).comp (e : FiniteAdeleRing (𝓞 ℚ) ℚ →+* FiniteAdeleRing ℤ ℚ)).toRatAlgHom
  let m : FiniteAdeleRing (𝓞 ℚ) ℚ ⊗[ℚ] K →ₐ[ℚ] AfP p ⊗[ℚ] K :=
    Algebra.TensorProduct.map g (AlgHom.id ℚ K)
  refine ⟨m.toRingHom.comp ι.symm.toRingHom, fun k => ?_⟩
  have : ι.symm (algebraMap K _ k) = 1 ⊗ₜ k := by rw [← hι, RingEquiv.symm_apply_apply]
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this]
  simp [m]

theorem exists_neg_two_norm_away : ∀ (M : Type) [Field M] [NumberField M] (σ : M →+* M), σ ≠ RingHom.id M → (∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) → ∀ ε ε' : M →+* ℂ, ε ≠ ε' → ε ≠ ComplexEmbedding.conjugate ε' → ∀ (p : ℕ) [Fact p.Prime], ∃ a : M, a ≠ 0 ∧ σ a = a ∧ (ε a).re < 0 ∧ (ε' a).re < 0 ∧ (∀ φ : M →+* ℂ, φ ≠ ε → φ ≠ ComplexEmbedding.conjugate ε → φ ≠ ε' → φ ≠ ComplexEmbedding.conjugate ε' → 0 < (φ a).re) ∧ ∃ u : (AfP p ⊗[ℚ] M)ˣ, (u : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom u = 1 ⊗ₜ a := by
  intro M _ _ σ hσ hconj ε ε' hεε' hεc p _
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨φ⟩ : Nonempty (M →+* ℂ) := inferInstance
    apply φ.injective
    rw [hconj, hconj, Complex.conj_conj]
  let σe : M ≃ₐ[ℚ] M :=
    { σ.toRatAlgHom with invFun := σ, left_inv := hinv, right_inv := hinv }
  have hσe : ∀ x, σe x = σ x := fun _ => rfl
  have hσe2 : σe ^ 2 = 1 := by
    ext x; rw [pow_two, AlgEquiv.mul_apply, hσe, hσe, hinv]; rfl
  have hσe1 : σe ≠ 1 := by
    intro h; apply hσ; ext x
    have := congrArg (fun f : M ≃ₐ[ℚ] M => f x) h
    simpa [hσe] using this
  have hσinv : σe⁻¹ = σe := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hσe2])
  let K := IntermediateField.fixedField (Subgroup.zpowers σe)
  have hmem : ∀ x : M, x ∈ K ↔ σ x = x := by
    intro x
    rw [IntermediateField.mem_fixedField_iff]
    constructor
    · intro h; exact h σe (Subgroup.mem_zpowers σe)
    · intro h f hf
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
      clear hf
      induction k using Int.induction_on with
      | zero => simp
      | succ n ih => rw [_root_.zpow_add_one, AlgEquiv.mul_apply, hσe, h, ih]
      | pred n ih => rw [_root_.zpow_sub_one, AlgEquiv.mul_apply, hσinv, hσe, h, ih]
  have hrank : Module.finrank K M = 2 := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers]
    exact orderOf_eq_prime hσe2 hσe1
  have hσK : ∀ x : K, σ (algebraMap K M x) = algebraMap K M x := fun x => (hmem _).1 x.2
  obtain ⟨h, h0, hε, hε', hpos, hloc⟩ := GlobalTheory.T.exists_base_element_negative_at_two_embeddings K M hrank σ hσ hσK hconj ε ε' hεε' hεc
  obtain ⟨s, hs⟩ : ∃ s, σ s ≠ s := by
    by_contra hc; push_neg at hc; exact hσ (RingHom.ext hc)
  set t := s - σ s with ht
  have hσt : σ t = -t := by rw [ht, map_sub, hinv]; ring
  have ht0 : t ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
  have htK : t * t ∈ K := (hmem _).2 (by rw [map_mul, hσt]; ring)
  let δ : K := ⟨t * t, htK⟩
  have htt : t * t = algebraMap K M δ := rfl
  have hδ0 : δ ≠ 0 := by
    intro hd; apply ht0
    have : t * t = 0 := by rw [htt, hd, map_zero]
    exact mul_self_eq_zero.1 this
  have hform := fun v => form_of_norm hrank σ hσK ht0 hσt htt v h0 (hloc v)
  obtain ⟨x, y, hxy⟩ := GlobalTheory.T.exists_finiteAdele_sq_sub_mul_sq_eq_of_local K δ h hδ0 h0 hform
  obtain ⟨Φ, hΦ⟩ := exists_toAfP K p
  let j : AfP p ⊗[ℚ] K →ₐ[ℚ] AfP p ⊗[ℚ] M :=
    Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) (IsScalarTower.toAlgHom ℚ K M)
  let S : AfP p ⊗[ℚ] M →ₐ[ℚ] AfP p ⊗[ℚ] M :=
    Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom
  have hSj' : ∀ w, S (j w) = j w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a k =>
      show a ⊗ₜ σ (algebraMap K M k) = a ⊗ₜ algebraMap K M k
      rw [hσK]
    | add w w' hw hw' => rw [map_add (f := _), map_add (f := _), hw, hw']
  set X := j (Φ x) with hX
  set Y := j (Φ y) with hY
  set T : AfP p ⊗[ℚ] M := 1 ⊗ₜ t with hT
  have hST : S T = -T := by simp [S, T, hσt, TensorProduct.tmul_neg]
  have hTT : T * T = j (Φ (algebraMap K _ δ)) := by
    rw [hΦ, hT, Algebra.TensorProduct.tmul_mul_tmul, mul_one, htt]; simp [j]
  have hkey : (X + Y * T) * S (X + Y * T) = 1 ⊗ₜ (algebraMap K M h) := by
    rw [map_add (f := _), map_mul, hX, hY, hSj', hSj', hST]
    have : (j (Φ x) + j (Φ y) * T) * (j (Φ x) + j (Φ y) * -T) =
        j (Φ (x ^ 2 - algebraMap K _ δ * y ^ 2)) := by
      rw [map_sub, map_mul, map_pow, map_pow, map_sub, map_mul, map_pow, map_pow, ← hTT]; ring
    rw [this, hxy, hΦ]; simp [j]
  have hunit : IsUnit (X + Y * T) := by
    have ha : IsUnit ((1 : AfP p) ⊗ₜ[ℚ] (algebraMap K M h)) :=
      ((map_ne_zero (algebraMap K M)).2 h0).isUnit.map
        (Algebra.TensorProduct.includeRight : M →ₐ[ℚ] AfP p ⊗[ℚ] M)
    rw [← hkey] at ha
    exact isUnit_of_mul_isUnit_left ha
  exact ⟨algebraMap K M h, (map_ne_zero _).2 h0, hσK h, hε, hε', hpos, hunit.unit, hkey⟩

end GlobalTheory.NormSign
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.compact_finiteAdelesAwayP_bounded_denominators : ∀ (p : ℕ) [Fact p.Prime] (Q : Set (AfP p)), IsCompact Q → ∃ D : ℕ, 0 < D ∧ ∀ a ∈ Q, ∀ v : AwayP p, AfP.eval v ((D : AfP p) * a) ∈ v.1.adicCompletionIntegers ℚ := by
  first | (exact @GlobalTheory.DenAwayCpt.exists_nat_mul_integral_of_isCompact) | (exact GlobalTheory.DenAwayCpt.exists_nat_mul_integral_of_isCompact) | (intros; apply GlobalTheory.DenAwayCpt.exists_nat_mul_integral_of_isCompact  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

open IsDedekindDomain Rat.HeightOneSpectrum

theorem exists_finset_forall_prime_awayP_padic :
    ∀ (p : ℕ) [Fact p.Prime] (P : AwayP p → Prop), (∀ᶠ w in Filter.cofinite, P w) →
    ∃ S : Finset ℕ, ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ w : AwayP p, P w ∧ Nonempty (w.1.adicCompletion ℚ ≃+* ℚ_[ℓ]) := by
  intro p _ P hP
  have hfin : {w : AwayP p | ¬ P w}.Finite := hP
  refine ⟨insert p (hfin.toFinset.image fun w => ((primesEquiv (R := ℤ) w.1 : Nat.Primes) : ℕ)), ?_⟩
  intro ℓ hℓ hS
  have hℓp : ℓ ≠ p := fun h => hS (by simp [h])
  let q : Nat.Primes := ⟨ℓ, hℓ.out⟩
  let v : HeightOneSpectrum ℤ := (primesEquiv (R := ℤ)).symm q
  have hv : ((primesEquiv (R := ℤ) v : Nat.Primes) : ℕ) = ℓ := by
    show ((primesEquiv (R := ℤ) ((primesEquiv (R := ℤ)).symm q) : Nat.Primes) : ℕ) = ℓ
    rw [Equiv.apply_symm_apply]
  have hne : v.asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro h
    have h1 := span_natGenerator (R := ℤ) v
    have h2 : natGenerator v = ℓ := hv
    rw [h, h2, Ideal.map_span] at h1
    simp only [Set.image_singleton, map_natCast] at h1
    have h3 : (ℓ : ℤ) ∣ (p : ℤ) := Ideal.mem_span_singleton.1 (h1 ▸ Ideal.mem_span_singleton_self _)
    have h4 : (p : ℤ) ∣ (ℓ : ℤ) := Ideal.mem_span_singleton.1 (h1.symm ▸ Ideal.mem_span_singleton_self _)
    exact hℓp (Nat.dvd_antisymm (Int.natCast_dvd_natCast.1 h3) (Int.natCast_dvd_natCast.1 h4))
  refine ⟨⟨v, hne⟩, ?_, ?_⟩
  · by_contra hw
    apply hS
    refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨⟨v, hne⟩, hfin.mem_toFinset.2 hw, hv⟩)
  · exact ⟨((Padic.adicCompletionEquiv ℤ q).symm : _ ≃+* ℚ_[(q : ℕ)])⟩

end GlobalTheory.FinClsLoc
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_finite_primeSet_avoiding_gridPlaces : ∀ (D : D7) (T : Type) (L : LevCh D T) (sc : Consts) (G : GridData L sc) (U : Set T), U.Finite →
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧ ∀ w : Pl D.host.E, Off S w → w.under (𝓞 D.host.F) ∉ G.pl.S0 ∧
      (∀ t ∈ U, ∀ w' ∈ L.Q t, w.under (𝓞 D.host.F) ≠ w'.under (𝓞 D.host.F)) ∧
      ((D.host.QS * D.host.q * D.host.d * D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  first | exact @GlobalTheory.FunObj.exists_std_primes | exact GlobalTheory.FunObj.exists_std_primes | (intros; apply GlobalTheory.FunObj.exists_std_primes <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.character_unramified_off_finite_primes : ∀ (D : D7) (c : (AE D)ˣ →* Circle), Continuous c →
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧ ∀ w : Pl D.host.E, Off S w → ∀ e, Formalism.L2.NTheta.IsIdemAt e w → UnrIdem c e := by
  first | exact @GlobalTheory.UnrOff.unr_off | exact GlobalTheory.UnrOff.unr_off | (intros; apply GlobalTheory.UnrOff.unr_off <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalUnitary_conj_splitSupported_finiteAdelicPoint : ∀ (D : D7) (V : HSp D) (S : Finset ℕ) (γ : GL (Fin V.rank) D.host.E) (h : GA D V),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram → h ∈ GfC V →
    (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V h ∧ ∀ w ∈ P, Off S w) →
    ∃ u : GA D V, u ∈ GfC V ∧ (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V u ∧ ∀ w ∈ P, Off S w) ∧
      (Formalism.IndefR.Lev.finE V u).1 = γ.1.map (eToEAf D) * (Formalism.IndefR.Lev.finE V h).1 * (γ⁻¹).1.map (eToEAf D) := by
  first | exact @GlobalTheory.ConjSplit.conj_supp | exact GlobalTheory.ConjSplit.conj_supp | (intros; apply GlobalTheory.ConjSplit.conj_supp <;> assumption)
end
