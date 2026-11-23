module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle010
public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsResEqOfUnitInChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertTrivialOfNowhereVanishing
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle013
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SubConjTransposeOfSymm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.Blocks
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SpGenStatement
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpMove

section
open Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

theorem thetaChar_half {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (n n' : Fin g → ℤ) (z : Fin g → ℂ) :
    thetaChar τ (fun i => (n i : ℂ) / 2) (fun i => (n' i : ℂ) / 2) z = theta (halfVec n) (halfVec n') z τ := by
  refine tsum_congr fun l => ?_
  have e : ((fun i => (l i : ℂ)) + fun i => (n i : ℂ) / 2) = shiftVec (halfVec n) l := by
    funext i; simp [shiftVec, halfVec]
  have e' : (fun i => (n' i : ℂ) / 2) = ofRealVec (halfVec n') := by
    funext i; simp [ofRealVec, halfVec]
  rw [e, e', thetaTerm, eC]
  congr 1
  ring

theorem jAut_transpose_mulVec_period {g : ℕ} {δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hδ : δ ∈ Matrix.symplecticGroup (Fin g) ℤ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ SiegelH (Fin g)) (w : Fin g ⊕ Fin g → ℤ) :
    (jAut δ τ)ᵀ *ᵥ ((fun i => (w (Sum.inr i) : ℂ)) + spAct δ τ *ᵥ (fun i => (w (Sum.inl i) : ℂ))) =
      (fun i => ((δᵀ *ᵥ w) (Sum.inr i) : ℂ)) + τ *ᵥ (fun i => ((δᵀ *ᵥ w) (Sum.inl i) : ℂ)) := by
  have hj := jAut_isUnit hδ hτ
  have hs := spAct_isSymm hδ hτ.1 hj
  have h1 : (jAut δ τ)ᵀ * spAct δ τ = (nAut δ τ)ᵀ := by
    rw [← hs.eq, ← Matrix.transpose_mul, spAct_eq, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hj,
      Matrix.mul_one]
  have h2 : (fun i => ((δᵀ *ᵥ w) (Sum.inr i) : ℂ)) =
      (cMat δ).toBlocks₁₂ᵀ *ᵥ (fun i => (w (Sum.inl i) : ℂ)) +
        (cMat δ).toBlocks₂₂ᵀ *ᵥ (fun i => (w (Sum.inr i) : ℂ)) := by
    funext i
    simp [Matrix.mulVec, dotProduct, cMat, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Fintype.sum_sum_type]
  have h3 : (fun i => ((δᵀ *ᵥ w) (Sum.inl i) : ℂ)) =
      (cMat δ).toBlocks₁₁ᵀ *ᵥ (fun i => (w (Sum.inl i) : ℂ)) +
        (cMat δ).toBlocks₂₁ᵀ *ᵥ (fun i => (w (Sum.inr i) : ℂ)) := by
    funext i
    simp [Matrix.mulVec, dotProduct, cMat, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁, Fintype.sum_sum_type]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, h2, h3, jAut_eq, nAut_eq]
  simp only [Matrix.transpose_add, Matrix.transpose_mul, hτ.1.eq, Matrix.add_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_mulVec]
  abel

theorem jAut_transpose_mulVec_mem_iff {g : ℕ} {δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hδ : δ ∈ Matrix.symplecticGroup (Fin g) ℤ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ SiegelH (Fin g)) (z : Fin g → ℂ) :
    (∃ m n : Fin g → ℤ, (jAut δ τ)ᵀ *ᵥ z = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) ↔
      ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + spAct δ τ *ᵥ (fun i => (n i : ℂ)) := by
  have hj := jAut_isUnit hδ hτ
  constructor
  · rintro ⟨m, n, h⟩
    have hu : IsUnit δᵀ := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
      exact SymplecticGroup.symplectic_det hδ
    obtain ⟨w, hw⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hu (Sum.elim n m)
    have h1 := jAut_transpose_mulVec_period hδ hτ w
    rw [hw] at h1
    refine ⟨fun i => w (Sum.inr i), fun i => w (Sum.inl i), ?_⟩
    have hinj : Function.Injective (jAut δ τ)ᵀ.mulVec := by
      rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
      exact hj
    apply hinj
    rw [h, h1]
    rfl
  · rintro ⟨m, n, rfl⟩
    exact ⟨_, _, jAut_transpose_mulVec_period hδ hτ (Sum.elim n m)⟩

theorem exists_theta_law {g : ℕ} {δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hδ : δ ∈ Matrix.symplecticGroup (Fin g) ℤ) {n n' k k' : Fin g → ℤ}
    (h : KeyPow.ThetaLaw g δ n n' k k') {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) :
    ∃ r : ℂ, r ^ 8 = (jAut δ τ).det ^ 4 ∧ ∀ z,
      theta (halfVec k) (halfVec k') (zAct δ τ z) (spAct δ τ) =
        r * Complex.exp (Real.pi * Complex.I * expArg δ τ z) * theta (halfVec n) (halfVec n') z τ := by
  obtain ⟨c, hc, h⟩ := h
  have hz : Differentiable ℂ (zAct δ τ) :=
    (Matrix.mulVecLin ((jAut δ τ)⁻¹)ᵀ).toContinuousLinearMap.differentiable
  have hq : Differentiable ℂ fun z => Real.pi * Complex.I * expArg δ τ z := by
    simp only [expArg, dotProduct, mulVec]
    fun_prop
  obtain ⟨r, hr, H⟩ := entire_eq_mul_of_sq_eq_mul_sq g
    (fun z => theta (halfVec k) (halfVec k') (zAct δ τ z) (spAct δ τ))
    (fun z => theta (halfVec n) (halfVec n') z τ) _ (c * (jAut δ τ).det)
    ((differentiable_theta (spAct_mem hδ hτ) _ _).comp hz) (differentiable_theta hτ _ _) hq
    (fun z => by
      rw [h τ hτ z, eC]
      congr 3
      ring)
  refine ⟨r, ?_, H⟩
  calc r ^ 8 = (r ^ 2) ^ 4 := by ring
    _ = _ := by rw [hr, mul_pow, hc, _root_.one_mul]

end

theorem normalAt_spAct : ∀ (x : KeyIn ℂ) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c : ℂ) (sp : Matrix (Fin x.P.g ⊕ Fin x.P.g) (Fin x.P.g ⊕ Fin x.P.g) ℤ) (n n' k k' : Fin x.P.g → ℤ), sp ∈ Matrix.symplecticGroup (Fin x.P.g) ℤ → GlobalTheory.KeyPow.ThetaLaw x.P.g sp n n' k k' → c ≠ 0 → GlobalTheory.KeyPow.NormalAt x τ M (fun i => (n i : ℂ) / 2) (fun i => (n' i : ℂ) / 2) c → ∃ (M' : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c' : ℂ), c' ≠ 0 ∧ M'.det ^ 4 / c' ^ 8 = M.det ^ 4 / c ^ 8 ∧ GlobalTheory.KeyPow.NormalAt x (Key.Chi.spAct sp τ) M' (fun i => (k i : ℂ) / 2) (fun i => (k' i : ℂ) / 2) c' := by
  intro x τ M c sp n n' k k' hsp hlaw hc hN
  have hτ := hN.mem_siegelH
  obtain ⟨u, -, -, hΛ, hrig, hfn, hv⟩ := hN
  have hj := Key.Chi.jAut_isUnit hsp hτ
  have hτ' := Key.Chi.spAct_mem hsp hτ
  obtain ⟨r, hr, H⟩ := exists_theta_law hsp hlaw hτ
  set j := Key.Chi.jAut sp τ with hjdef
  have hj0 : j.det ≠ 0 := hj.ne_zero
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact pow_ne_zero 4 hj0 (by rw [← hr]; simp)
  have e1 : j.transpose * (j⁻¹).transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hj, Matrix.transpose_one]
  have e2 : (j⁻¹).transpose * j.transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hj, Matrix.transpose_one]
  let φ : (Fin x.P.g → ℂ) ≃ₗ[ℂ] (Fin x.P.g → ℂ) := Matrix.toLin'OfInv e2 e1
  have hφ : ∀ z, φ z = j.transpose.mulVec z := fun _ => rfl
  have hE : Differentiable ℂ fun z => Complex.exp (Real.pi * Complex.I * Key.Chi.expArg sp τ (φ z)) := by
    simp only [hφ, Key.Chi.expArg, dotProduct, Matrix.mulVec]
    fun_prop
  obtain ⟨u', -, hΛ', hrig', hfn', hv'⟩ := exists_holUnif_reparam x.P.A x.P.L x.P.g u φ _ hE
    (fun _ => Complex.exp_ne_zero _) (by simp [Key.Chi.expArg])
  refine ⟨M * j⁻¹, c / r, div_ne_zero hc hr0, ?_, u', hτ'.1, hτ'.2, fun z => ?_, hrig' _ hrig, ?_,
    fun i => hv' _ _ ?_⟩
  · rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', div_pow, hr]
    field_simp
  · rw [hΛ', hΛ, hφ]
    exact jAut_transpose_mulVec_mem_iff hsp hτ z
  · convert hfn' _ _ hfn using 2 with z
    have h1 := H (φ z)
    have h2 : Key.Chi.zAct sp τ (φ z) = z := by
      rw [Key.Chi.zAct, hφ, Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
    rw [h2] at h1
    rw [thetaChar_half, thetaChar_half, h1]
    field_simp
  · have h3 : φ ((M * j⁻¹) i) = M i := by
      rw [hφ, Matrix.mulVec_transpose]
      change ((M * j⁻¹) * j) i = M i
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hj, Matrix.mul_one]
    rw [map_smul, h3]
    exact hv i

end GlobalTheory.SpMove
end

section

noncomputable section
namespace GlobalTheory.HenselZero

open IsLocalRing GlobalTheory.SqZero

theorem formallySmooth_quotient {R S ι : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
    [Fintype ι] [DecidableEq ι] (f : ι → S) (τ : ι → Derivation R S S)
    (h : IsUnit (Matrix.of fun i k => τ k (f i)).det) :
    Algebra.FormallySmooth R (S ⧸ Ideal.span (Set.range f)) := by
  refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ I hI g => ?_
  obtain ⟨g', hg'⟩ := Algebra.FormallySmooth.comp_surjective R S I hI (g.comp (Ideal.Quotient.mkₐ R _))
  have hg : ∀ a, Ideal.Quotient.mk I (g' a) = g (Ideal.Quotient.mk _ a) := fun a => congr($hg' a)
  have hf : ∀ i, g' (f i) ∈ I := fun i => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hg, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self i)), map_zero]
  let M : Matrix ι ι B := Matrix.of fun i k => g' (τ k (f i))
  have hM : IsUnit M.det := by
    have := h.map g'
    rw [AlgHom.map_det] at this
    exact this
  let t : ι → B := M⁻¹.mulVec fun i => - g' (f i)
  have ht : ∀ k, t k ∈ I := fun k => Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (neg_mem (hf i))
  have hMt : M.mulVec t = fun i => - g' (f i) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]
  have h0 : ∀ i j, t i * t j = 0 := fun i j => by
    have := Ideal.mul_mem_mul (ht i) (ht j)
    rwa [← sq, hI] at this
  refine ⟨Ideal.Quotient.liftₐ _ (addDers τ g' t h0) fun a ha => ?_, ?_⟩
  · refine (Ideal.span_le (I := RingHom.ker (addDers τ g' t h0))).2 ?_ ha
    rintro _ ⟨i, rfl⟩
    have : ∑ k, g' (τ k (f i)) * t k = - g' (f i) := congrFun hMt i
    show addDers τ g' t h0 (f i) = 0
    rw [addDers_apply, this, add_neg_cancel]
  · refine Ideal.Quotient.algHom_ext _ (AlgHom.ext fun a => ?_)
    show Ideal.Quotient.mk I (addDers τ g' t h0 a) = g (Ideal.Quotient.mk _ a)
    rw [addDers_apply, map_add (f := _), hg, Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (ht k)), add_zero]

theorem exists_derivation_lift {R S K : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
    [CommRing K] [Algebra R K] (u : S →ₐ[R] K) (hu : Function.Surjective u) (D : S →ₗ[R] K)
    (hD : ∀ a b, D (a * b) = u a * D b + u b * D a) : ∃ τ : Derivation R S S, ∀ a, u (τ a) = D a := by
  let _ : Algebra S K := (u : S →+* K).toAlgebra
  have : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq fun r => (u.commutes r).symm
  let D' : Derivation R S K := Derivation.mk' D hD
  obtain ⟨l, hl⟩ := Module.projective_lifting_property (Algebra.linearMap S K) D'.liftKaehlerDifferential hu
  refine ⟨l.compDer (KaehlerDifferential.D R S), fun a => ?_⟩
  exact (congr($hl (KaehlerDifferential.D R S a))).trans (D'.liftKaehlerDifferential_comp_D a)

theorem exists_algHom_ker_eq {O S ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra O S]
    [Algebra.FormallySmooth O S] [Fintype ι] [DecidableEq ι] (f : ι → S) (u : S →+* ResidueField O)
    (hu : ∀ r, u (algebraMap O S r) = residue O r) (hf : ∀ i, u (f i) = 0)
    (χ : ι → (S →+* DualNumber (ResidueField O))) (h₁ : ∀ k a, (χ k a).fst = u a)
    (h₂ : ∀ k r, χ k (algebraMap O S r) = algebraMap (ResidueField O) _ (residue O r))
    (hd : (Matrix.of fun i k => (χ k (f i)).snd).det ≠ 0)
    (hm : maximalIdeal S ≤ Ideal.span (Set.range f) ⊔ (maximalIdeal O).map (algebraMap O S)) :
    ∃ ψ : S →ₐ[O] O, (∀ a, residue O (ψ a) = u a) ∧ RingHom.ker ψ = Ideal.span (Set.range f) := by
  let u' : S →ₐ[O] ResidueField O := ⟨u, hu⟩
  have hs : Function.Surjective u' := fun c => by
    obtain ⟨r, rfl⟩ := residue_surjective c
    exact ⟨_, hu r⟩
  have hker : RingHom.ker u = maximalIdeal S := eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective u hs)
  have hτ : ∀ k, ∃ τ : Derivation O S S, ∀ a, u (τ a) = (χ k a).snd := fun k =>
    exists_derivation_lift u' hs
      { toFun := fun a => (χ k a).snd
        map_add' := fun a b => by simp
        map_smul' := fun r a => by
          rw [Algebra.smul_def, map_mul, h₂, Algebra.smul_def]
          simp [TrivSqZeroExt.algebraMap_eq_inl] }
      fun a b => by simp [h₁, mul_comm]; rfl
  choose τ hτ using hτ
  have hunit : IsUnit (Matrix.of fun i k => τ k (f i)).det := by
    rw [← notMem_maximalIdeal, ← hker, RingHom.mem_ker, RingHom.map_det]
    refine fun h => hd (Eq.trans ?_ h)
    congr 1
    ext i k
    exact (hτ k _).symm
  have := formallySmooth_quotient f τ hunit
  have hle : Ideal.span (Set.range f) ≤ RingHom.ker u' := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hf i)
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := maximalIdeal O)
    (Ideal.Quotient.liftₐ (Ideal.span (Set.range f)) u' fun a ha => hle ha)
  let ψ : S →ₐ[O] O := g.comp (Ideal.Quotient.mkₐ O _)
  have hψ : ∀ a, residue O (ψ a) = u a := fun a => congr($hg (Ideal.Quotient.mk _ a))
  have hle' : Ideal.span (Set.range f) ≤ RingHom.ker ψ := fun a ha => by
    show g (Ideal.Quotient.mk _ a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  refine ⟨ψ, hψ, le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal S)
    (IsNoetherian.noetherian _) (maximalIdeal_le_jacobson _) fun a ha => ?_) hle'⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have ha₀ : ψ a = 0 := ha
  have ha' : a ∈ maximalIdeal S := by rw [← hker, RingHom.mem_ker, ← hψ, ha₀, map_zero]
  replace ha' := hm ha'
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at ha'
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 ha'
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hc
  refine Submodule.add_mem_sup hb (Submodule.smul_mem_smul (r := algebraMap O S π) (n := c) ?_ ?_)
  · rw [← hker, RingHom.mem_ker, hu, residue_eq_zero_iff]
    exact hπ.not_isUnit
  · have hb₀ : ψ b = 0 := hle' hb
    rw [map_add (f := _), hb₀, zero_add, map_mul, AlgHom.commutes] at ha₀
    exact (mul_eq_zero.1 ha₀).resolve_left hπ.ne_zero

end GlobalTheory.HenselZero
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory
namespace UnifCompare

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

lemma mem_iff (u u₀ : HolUnif A L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u₀.ex (F z) = u.ex z) (z : Fin g → ℂ) : F z ∈ u₀.Λ ↔ z ∈ u.Λ := by
  rw [← u₀.ker, ← u.ker, hF]

lemma injective (u u₀ : HolUnif A L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u₀.ex (F z) = u.ex z) : Function.Injective F := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  have hm : ∀ t : ℂ, t • z ∈ u.Λ := fun t => by
    rw [← mem_iff u u₀ F hF, map_smul, hz, smul_zero]
    exact u₀.Λ.zero_mem
  have := u.discrete
  have hc : Continuous fun t : ℂ => (⟨t • z, hm t⟩ : u.Λ) :=
    Continuous.subtype_mk (continuous_id.smul continuous_const) _
  have h := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℂ) hc (x := 1) (y := 0)
  simpa using congrArg Subtype.val h

lemma isDiff_iff (u u₀ : HolUnif A L g) (F : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u₀.ex (F z) = u.ex z) (w : Fin g → ℂ) (v : epsR ℂ ⟶ A) :
    u.IsDiff w v ↔ u₀.IsDiff (F w) v := by
  have key : ∀ (U : A.left.Opens) (f : Γ(A.left, U)),
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w =
        fderiv ℂ (fun z => valAt' (u₀.ex z).left U f) 0 (F w) := fun U f => by
    have e : (fun z => valAt' (u.ex z).left U f) = (fun z => valAt' (u₀.ex z).left U f) ∘ F := by
      funext z
      simp only [Function.comp, hF]
    rw [e, ContinuousLinearEquiv.comp_right_fderiv, map_zero]
    rfl
  simp only [HolUnif.IsDiff, key]


open PullHermitian in
lemma hermForm_eq (hL : L.IsLB) (u u₀ : HolUnif A L g) {Hm H₀ : Matrix (Fin g) (Fin g) ℂ}
    {χ : u.Λ → ℂ} {χ₀ : u₀.Λ → ℂ} (hu : u.IsAH Hm χ) (hu₀ : u₀.IsAH H₀ χ₀)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, u₀.ex (F z) = u.ex z) (z w : Fin g → ℂ) :
    hermForm H₀ (F z) (F w) = hermForm Hm z w := by
  have hΛ : ∀ l : u.Λ, F l ∈ u₀.Λ := fun l => (mem_iff u u₀ F hF l).2 l.2
  have hper : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  have tr : ∀ {U : A.left.Opens} {z}, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → ⊤ ≤ (u₀.ex (F z)).left ⁻¹ᵁ U :=
    fun h => by rwa [hF]
  obtain ⟨r, hr, hrφ⟩ := exists_glue
    (fun i : L.ι => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i})
    (fun i => (u.hol _ 0).1)
    (fun z => exists_chart (u.ex z).left hL)
    (fun i z => u₀.fr i (F z) / u.fr i z)
    (fun i => by
      have d2 := (u₀.fr_hol i).comp (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i})
        hFd.differentiableOn fun z hz => tr hz
      simp only [div_eq_mul_inv]
      exact d2.mul ((u.fr_hol i).inv fun z hz => u.fr_ne i z hz))
    (fun i j z hi hj => by
      have h1 := u.fr_compat i j z (inf_of _ hi hj)
      have h2 := u₀.fr_compat i j (F z) (tr (inf_of _ hi hj))
      rw [hF] at h2
      rw [div_eq_div_iff (u.fr_ne _ _ hi) (u.fr_ne _ _ hj), h1, h2]
      ring)
  set H₂ := (LinearMap.toMatrix' F).transpose * H₀ * (LinearMap.toMatrix' F).transpose.conjTranspose
    with hH₂
  have hH₂h : H₂.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose _ hu₀.1
  have hsub : ∀ z w, hermForm (Hm - H₂) z w = hermForm Hm z w - hermForm H₀ (F z) (F w) :=
    fun z w => by
      have := hermForm_sub_smul Hm H₂ 1 1 z w
      rwa [one_smul, one_smul, _root_.one_mul, _root_.one_mul, hH₂, hermForm_pull] at this
  have := u.discrete
  have key := appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full
    (Hm - H₂) (fun l => χ l / χ₀ ⟨F l, hΛ l⟩) r (hu.1.sub hH₂h)
    (fun l => by simp [hu.2.2.1, hu₀.2.2.1]) hr
    (fun z => by
      obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hL
      rw [hrφ i z hi]
      exact div_ne_zero (u₀.fr_ne _ _ (tr hi)) (u.fr_ne _ _ hi))
    (fun l z => by
      obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hL
      have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
      have h1 := hu.2.2.2 l i z hi
      have h2 := hu₀.2.2.2 ⟨F l, hΛ l⟩ i (F z) (tr hi)
      have h3 : χ l ≠ 0 := norm_ne_zero_iff.1 (by rw [hu.2.2.1]; exact one_ne_zero)
      have h4 : χ₀ ⟨F l, hΛ l⟩ ≠ 0 := norm_ne_zero_iff.1 (by rw [hu₀.2.2.1]; exact one_ne_zero)
      have h5 := u.fr_ne _ _ hi'
      rw [hrφ i z hi, hrφ i (z + l) hi']
      simp only [hsub, map_add (f := _)]
      rw [h1, h2]
      simp only [hermForm]
      generalize (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) = a
      generalize ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) = b
      generalize (F z ⬝ᵥ H₀.mulVec (star (F l))) = a'
      generalize (F l ⬝ᵥ H₀.mulVec (star (F l))) = b'
      have e : Complex.exp (Real.pi * (a - a') + Real.pi / 2 * (b - b')) =
          Complex.exp (Real.pi * a + Real.pi / 2 * b) /
            Complex.exp (Real.pi * a' + Real.pi / 2 * b') := by
        rw [← Complex.exp_sub]
        congr 1
        ring
      have h6 := Complex.exp_ne_zero (Real.pi * a + Real.pi / 2 * b)
      have h7 := Complex.exp_ne_zero (Real.pi * a' + Real.pi / 2 * b')
      rw [e]
      generalize Complex.exp (Real.pi * a + Real.pi / 2 * b) = s at h6
      generalize Complex.exp (Real.pi * a' + Real.pi / 2 * b') = s' at h7
      field_simp)
  have h := hsub z w
  rw [key.1] at h
  have h0 : hermForm (0 : Matrix (Fin g) (Fin g) ℂ) z w = 0 := by simp [hermForm]
  rw [h0] at h
  exact (sub_eq_zero.1 h.symm).symm

end UnifCompare


open UnifCompare in
theorem unimodular_and_tangent_of_isAH :
    ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen →
    ∀ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ →
    (∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef) ∧
    (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) := by
  intro hT P rig hrig u Hm χ hu
  obtain ⟨u₀, H₀, χ₀, E₀, hu₀, -, hv, hw, -, -, hE, hEb, -⟩ := hT P rig hrig
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo P.A P.isAb P.L P.g P.g u₀ hv hw u.ex u.ex_add
    (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  have hinj := injective u u₀ F hF
  let e : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ) := LinearEquiv.ofInjectiveEndo F hinj
  have he : ∀ z, e z = F z := fun z => rfl
  have hd : ∀ w v, u.IsDiff w v ↔ u₀.IsDiff (e w) v :=
    isDiff_iff u u₀ e.toContinuousLinearEquiv hF
  refine ⟨?_, fun v hv' => ?_, fun w => ?_⟩
  · let φ : u.Λ ≃ₗ[ℤ] u₀.Λ :=
      { toFun := fun a => ⟨e a, (mem_iff u u₀ F hF a).2 a.2⟩
        invFun := fun b => ⟨e.symm b, (mem_iff u u₀ F hF _).1 (by
          rw [← he, e.apply_symm_apply]; exact b.2)⟩
        map_add' := fun a b => Subtype.ext (map_add e a.1 b.1)
        map_smul' := fun n a => Subtype.ext (map_zsmul e n a.1)
        left_inv := fun a => Subtype.ext (e.symm_apply_apply a.1)
        right_inv := fun b => Subtype.ext (e.apply_symm_apply b.1) }
    refine ⟨φ.dualMap.toLinearMap ∘ₗ E₀ ∘ₗ φ.toLinearMap, fun a b => ?_,
      φ.dualMap.bijective.comp (hEb.comp φ.bijective)⟩
    rw [← hermForm_eq P.isLB u u₀ hu hu₀ F hF]
    exact hE (φ a) (φ b)
  · obtain ⟨w, h1, h2⟩ := hv v hv'
    refine ⟨e.symm w, (hd _ _).2 (by rwa [e.apply_symm_apply]), fun y hy => ?_⟩
    rw [← h2 _ ((hd _ _).1 hy), e.symm_apply_apply]
  · simp only [hd]
    exact hw (e w)

end GlobalTheory
end
