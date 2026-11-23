module

public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle310
public import Formalism.LocalToGlobal.Divisibility.Bundle002
public import Formalism.LocalToGlobal.Divisibility.FramesLemmas
public import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryGroupIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralChangeBaseFrameOrthonormal
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle004
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

@[expose] public section

section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory

namespace DecoLatticeClasses

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

noncomputable def unitEquiv (γ : Matrix (Fin n) (Fin n) E) (h : γ * γ.conjTranspose = 1) :
    Sp E n ≃ₗ[E] Sp E n :=
  LinearEquiv.ofLinearMap (Matrix.mulVecLin γ.conjTranspose) (Matrix.mulVecLin γ)
    (by rw [← Matrix.mulVecLin_mul, mul_eq_one_comm.1 h, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, h, Matrix.mulVecLin_one])

theorem unitEquiv_mem (γ : Matrix (Fin n) (Fin n) E) (h : γ * γ.conjTranspose = 1) :
    unitEquiv γ h ∈ UF E n := by
  intro x y
  change star (γ.conjTranspose.mulVec x) ⬝ᵥ (γ.conjTranspose.mulVec y) = star x ⬝ᵥ y
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem mem_one_iff [NumberField E] (a : E) :
    a ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ a := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨r, rfl⟩
    exact r.isIntegral_coe
  · intro h
    exact ⟨⟨a, h⟩, rfl⟩

end DecoLatticeClasses


open DecoLatticeClasses in
theorem exists_finset_decoSet_lattice_reps :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing E],
    (∀ x : E, star x = IsCMField.complexConj E x) → ∀ n : ℕ,
    ∃ Rs : Finset (Submodule (𝓞 E) (Sp E n)),
      (Rs.card : ℝ) ≤ (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (n : ℝ) ^ 4 *
        (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^
          (3 * Module.finrank ℚ E * n ^ 2) ∧
      ∀ (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)),
        ∃ g : UF E n,
          (((g, (1 : GLG (E := E) (n := n) (SG := SG))) • d :
            DecoSet (E := E) (n := n) (ST := ST) (SG := SG))).1.N ∈ Rs := by
  intro E _ _ _ _ hs n
  obtain ⟨R, hR, H⟩ := GlobalTheory.exists_finset_selfDual_classes_rootDiscr E n
  refine ⟨R, hR, fun ST SG d => ?_⟩
  have hu : Formalism.HermitianLatticesTheory.dual (hStd E n) d.1.N = d.1.N := d.2.uni
  have hspan : Submodule.span E (d.1.N : Set (Sp E n)) = ⊤ := by
    let W := Submodule.span E (d.1.N : Set (Sp E n))
    change W = ⊤
    by_contra hW
    let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
    let g : Sp E n →ₗ[E] Module.Dual E W :=
      (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
    have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Sp E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    -- Self-duality puts the whole line through the orthogonal vector in the lattice.
    have hsmul (a : E) : a • e x ∈ d.1.N := by
      rw [← hu, mem_dual]
      intro y hy
      have hxy : hStd E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩)
          (LinearMap.mem_ker.mp hx)
      rw [map_smul, hStd_isSymm.isRefl (e x) y hxy, smul_zero]
      exact Submodule.zero_mem _
    let i : E →ₗ[𝓞 E] d.1.N :=
      ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict d.1.N hsmul
    let : Module.Finite (𝓞 E) d.1.N := Module.Finite.iff_fg.mpr d.2.lat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  obtain ⟨L₀, hL₀, γ, hγ, hm⟩ := H d.1.N d.2.lat.fg hspan (fun y => by
    conv_lhs => rw [← hu, mem_dual]
    simp only [mem_one_iff, hStd_apply, hs])
  have hγ' : γ * γ.conjTranspose = 1 := by
    rw [← hγ]
    congr 1
    ext i j
    simp [Matrix.conjTranspose_apply, hs]
  refine ⟨⟨unitEquiv γ hγ', unitEquiv_mem γ hγ'⟩, ?_⟩
  have e : Formalism.HermitianLatticesTheory.gmap (unitEquiv γ hγ') d.1.N = L₀ := by
    ext x
    rw [mem_gmap, hm]
    rfl
  rw [← e] at hL₀
  exact hL₀

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix ComplexOrder

namespace GlobalTheory.QuotRational

theorem gram_of_quotMet {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (G : Matrix (Fin d) (Fin d) ℂ)
    (hG : IsUnit G.det) (P : Matrix (Fin d) (Fin n) ℂ) (D : Matrix (Fin n) (Fin d) ℂ) (h1 : G * P = Dᴴ * A)
    (h2 : (P * A⁻¹ * Pᴴ)⁻¹ = G) : Dᴴ * A * D = G := by
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have hM : IsUnit (P * A⁻¹ * Pᴴ).det := by
    by_contra h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h] at h2
    subst h2
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact h (by simp)
    · have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      simp at hG
  have h3 : G * (P * A⁻¹ * Pᴴ) = 1 := by rw [← h2]; exact Matrix.nonsing_inv_mul _ hM
  have h4 : Dᴴ * Pᴴ = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc Dᴴ, Matrix.mul_nonsing_inv _ hAu,
      Matrix.mul_one] at h3
    exact h3
  have h5 : P * D = 1 := by
    have := congrArg Matrix.conjTranspose h4
    simpa [Matrix.conjTranspose_mul] using this
  rw [← h1, Matrix.mul_assoc, h5, Matrix.mul_one]

theorem eq_of_gram {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (G : Matrix (Fin d) (Fin d) ℂ)
    (C D : Matrix (Fin n) (Fin d) ℂ) (h1 : Dᴴ * A * D = G) (h2 : Cᴴ * A * C = G) (h3 : Dᴴ * A * C = G) : C = D := by
  have hG : Gᴴ = G := by
    rw [← h1]; simp [Matrix.conjTranspose_mul, hA.isHermitian.eq, Matrix.mul_assoc]
  have h4 : Cᴴ * A * D = G := by
    have := congrArg Matrix.conjTranspose h3
    rw [hG] at this
    simpa [Matrix.conjTranspose_mul, hA.isHermitian.eq, Matrix.mul_assoc] using this
  have h5 : (C - D)ᴴ * A * (C - D) = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, h1, h2, h3, h4]
    simp
  have h6 : ∀ x, (C - D) *ᵥ x = 0 := by
    intro x
    by_contra hx
    have := hA.dotProduct_mulVec_pos hx
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h5] at this
    simp at this
  rw [← sub_eq_zero]
  ext i j
  simpa using congrFun (h6 (Pi.single j 1)) i

variable {K : Type} [Field K] [StarRing K]

theorem map_conjTranspose_twist (σ : K →+* ℂ) {n d : ℕ} (E : Matrix (Fin n) (Fin d) K) :
    (Eᴴ).map σ = (E.map (Formalism.DivisionValues.twist σ))ᴴ := by
  ext a i
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply, Formalism.DivisionValues.twist, RingHom.comp_apply, starRingEnd_apply, star_star]

theorem twist_twist (σ : K →+* ℂ) : Formalism.DivisionValues.twist (Formalism.DivisionValues.twist σ) = σ := by
  ext a
  simp [Formalism.DivisionValues.twist]

theorem map_twist_of_mem (σ : K →+* ℂ) {n d : ℕ} (H : Matrix (Fin n) (Fin d) K) (hH : ∀ i j, H i j ∈ cmMax K) :
    H.map (Formalism.DivisionValues.twist σ) = H.map σ := by
  ext i j
  have : σ (star (H i j)) = starRingEnd ℂ (σ (H i j)) := hH i j σ
  simp only [Matrix.map_apply, Formalism.DivisionValues.twist, RingHom.comp_apply, starRingEnd_apply (R := K), this, Complex.conj_conj]

theorem entries_mem_cmMax [NumberField K] {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (hH : ∀ i j, H i j ∈ cmMax K)
    (hpos : ∀ v : InfinitePlace K, (H.map v.embedding).PosDef) (E : Matrix (Fin n) (Fin d) K)
    (Pr : Matrix (Fin d) (Fin n) K) (hP : IsOrthProj H E Pr)
    (hR : IsRatHerm (cmMax K) (Eᴴ * H * E) (quotFrame Pr H)) : ∀ i a, E i a ∈ cmMax K := by
  have hsurj : Function.Surjective Pr.mulVec :=
    Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨E, hP.1⟩
  have hGP : Eᴴ * H * E * Pr = Eᴴ * H := by
    have h2 := hP.2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2
    rw [Matrix.mul_assoc (Eᴴ * H), ← h2]
  have hv : ∀ v : InfinitePlace K, (Eᴴ).map v.embedding * H.map v.embedding * E.map (Formalism.DivisionValues.twist v.embedding) =
      (Eᴴ * H * E).map v.embedding := by
    intro v
    have hq := (quotFrameIsQuot K n d H hpos Pr hsurj v).2
    have hr := (hR.2 v).2
    rw [map_conjTranspose_twist]
    refine gram_of_quotMet _ (hpos v) _ ?_ (Pr.map v.embedding) _ ?_ (hq.symm.trans hr)
    · rw [← hr]
      exact (Matrix.isUnit_iff_isUnit_det _).mp (metOfSpec d _ (hR.2 v).1).1.isUnit
    · rw [← Matrix.map_mul, hGP, Matrix.map_mul, map_conjTranspose_twist]
  have hall : ∀ σ : K →+* ℂ, (Eᴴ).map σ * H.map σ * E.map (Formalism.DivisionValues.twist σ) = (Eᴴ * H * E).map σ := by
    intro σ
    rcases InfinitePlace.mk_eq_iff.mp (InfinitePlace.mk_embedding (InfinitePlace.mk σ)) with h | h
    · rw [← h]; exact hv _
    · have h1 := congrArg (fun M => M.map (starRingEnd ℂ)) (hv (InfinitePlace.mk σ))
      simp only [Matrix.map_mul (f := starRingEnd ℂ), Matrix.map_map] at h1
      rw [← h]
      exact h1
  have hE : ∀ v : InfinitePlace K, E.map v.embedding = E.map (Formalism.DivisionValues.twist v.embedding) := by
    intro v
    refine eq_of_gram _ (hpos v) ((Eᴴ * H * E).map v.embedding) _ _ ?_ ?_ ?_
    · rw [← map_conjTranspose_twist]; exact hall _
    · have h1 := hall (Formalism.DivisionValues.twist v.embedding)
      rwa [map_conjTranspose_twist, twist_twist, map_twist_of_mem _ H hH, map_twist_of_mem _ _ hR.1] at h1
    · rw [Matrix.map_mul, Matrix.map_mul, map_conjTranspose_twist]
  intro i a σ
  have h1 := congrFun (congrFun (hE (InfinitePlace.mk σ)) i) a
  simp only [Matrix.map_apply, Formalism.DivisionValues.twist, RingHom.comp_apply, starRingEnd_apply] at h1
  rcases InfinitePlace.mk_eq_iff.mp (InfinitePlace.mk_embedding (InfinitePlace.mk σ)) with h | h
  · rw [h] at h1
    rw [h1, starRingEnd_apply, star_star]
  · rw [← h, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, h1]
    simp

theorem fE_mem_cmMax : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (v0 : InfinitePlace K) (s : ℕ), BlockHyp B ℓ v0 s → IsRatHerm (cmMax K) (B.HZ ℓ Z) (B.XQ ℓ Z) → ∀ a k, B.fE ℓ Z a k ∈ cmMax K := by
  intro K _ _ _ G _ _ Pl0 B ℓ Z v0 s h hR a k
  have hE := entries_mem_cmMax (B.HV ℓ) (BlockDat.HV_rat h.conj h.ok h.irr) (BlockDat.HV_pos h.conj h.ok h.irr)
    (B.zE ℓ Z) (B.Pq ℓ Z) (BlockDat.Pq_orth h.conj h.ok h.irr) hR
  rw [BlockDat.fE, Matrix.mul_apply]
  exact Subfield.sum_mem _ fun j _ => Subfield.mul_mem _ (BlockDat.vE_rat h.conj h.ok h.irr a j) (hE j k)

end GlobalTheory.QuotRational
end

section

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealOneVector

theorem isCuspIndProdChar_of_isProdCuspChar {E : Type} [Field E] [NumberField E] {K : Type} [Field K] (s : K →+* ℂ)
    (Pg : Finset (Pl E)) (r : ℕ) (χ : G0 Pg r → K) (h : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar s Pg r χ) :
    GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.IsCuspIndProdChar Pg r s χ := by
  obtain ⟨θ, hθ, hχ⟩ := h
  refine ⟨θ, fun PP => ?_, hχ⟩
  obtain ⟨d, b, σ, hσ, hx⟩ := hθ PP
  exact ⟨b, Fin d → ℂ, inferInstance, inferInstance, inferInstance, σ, hσ, hx⟩

theorem typeSum_base_eq_card : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.grp_levels F → (∀ χ ∈ A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar D.what₂.embLL R.Pg D.R.r fun g => χ (R.eG.symm g)) → ∀ [Fintype F.P0], ∀ χ ∈ A.X, ∑ h : F.P0, χ (h : G) * (((F.ψ0 h)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) = (Fintype.card F.P0 : D.what₂.LL) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hlev hind _ χ hχ
  have h := GlobalTheory.OneForm.oneVector_of_whittaker R F GlobalTheory.GenericProduct.oneWhittakerVector_holds hlev
    (fun χ hχ => isCuspIndProdChar_of_isProdCuspChar _ _ _ _ (hind χ hχ)) χ hχ
  rw [← Nat.card_eq_fintype_card, ← h, GlobalTheory.OneForm.typeSum]
  congr 1
  exact congrArg (fun i => @Finset.univ _ i) (Subsingleton.elim _ _)

end GlobalTheory.RealOneVector
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eventually_unitaryPair_keeps_completedLattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U) → (∀ᶠ p : GA D S × GA D T in 𝓝 1, ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ x : WO S T, x.map (infPart D) = 0 → ∀ N : ℕ, 0 < N → ∀ᶠ p : GA D S × GA D T in 𝓝 1, ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 x = x + N • l := by
  first | exact @GlobalTheory.LatNhds.eventually_actO | exact GlobalTheory.LatNhds.eventually_actO | (intros; apply GlobalTheory.LatNhds.eventually_actO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_heisenbergInvariant_meanSquare_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsCharAF D.host.F ψ → ∀ M : Submodule ℂ (WO S T → ℂ), (∀ f ∈ M, IsThetaFunO ψ S T f) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∃ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ (u : WO S T) (f g f' g' : M), (f' : WO S T → ℂ) = heisO ψ S T u f → (g' : WO S T → ℂ) = heisO ψ S T u g → B f' g' = B f g) ∧ ∀ f : M, ∫⁻ w in 𝓕, ‖(f : WO S T → ℂ) w‖ₑ ^ 2 ∂μ = ENNReal.ofReal (B f f).re := by
  first | exact @GlobalTheory.ThetaMeanSquareForm.exists_invariant_form | exact GlobalTheory.ThetaMeanSquareForm.exists_invariant_form | (intros; apply GlobalTheory.ThetaMeanSquareForm.exists_invariant_form <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.completedHomLattice_multiple_mem_open_level : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U) → (∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), N • u ∈ U) ∧ ∀ (g : GA D S) (h : GA D T), ∃ N : ℕ, 0 < N ∧ ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), N • actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  first | exact @GlobalTheory.LatLevel.level_of_generators | exact GlobalTheory.LatLevel.level_of_generators | (intros; apply GlobalTheory.LatLevel.level_of_generators <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilRat

theorem heisO_apply_zero {D : D7} {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w f 0 = f w := by
  have h : hO S T 0 w = 0 := by simp [hO]
  simp [heisO, symplOH, symplO, h]

theorem om_rat_actO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, IsThetaFunO ψ S T f → ∀ w, om (γ, γ') f (actO S T γ γ' w) = f w := by
  intro D ψ hψ S T χS χT om H γ hγ γ' hγ' f hf w
  have h1 := H.om_heis γ γ' w f hf
  have h2 := H.om_aut γ hγ γ' hγ' _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w)
  rw [← heisO_apply_zero ψ (actO S T γ γ' w) (om (γ, γ') f), ← h1]
  exact h2.trans (heisO_apply_zero _ _ _)

end GlobalTheory.WeilRat
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmoothCyclic

open GlobalTheory.LowTypeDetermined

theorem eq_zero_of_orbit : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
    (ℓ : M.H τ →ₗ[ℂ] ℂ), Sobolev₂ (lieAt V τ) (M.rep τ) ℓ → ∀ v ∈ M.sm τ, v ≠ 0 →
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ℓ (M.rep τ g v) = 0) → ∀ w ∈ M.sm τ, ℓ w = 0 := by
  intro D V S M τ ℓ hℓ v hv hv0 h0 w hw
  obtain ⟨_, -, hσ, hi, -⟩ := M.ds τ
  have hs : M.sm τ = smooth (gramAt D V τ) (M.rep τ) := Submodule.span_eq (smooth (gramAt D V τ) (M.rep τ))
  have hP := M.fr_unit τ
  have h := M.fr_gram τ
  refine eq_zero_of_translates hσ hi hP h hℓ (hs.le hv) hv0 (fun g hg => ?_) (hs.le hw)
  have e : M.rep τ ((M.fr τ)⁻¹ * g * M.fr τ) = M.σ τ g := congrArg (M.σ τ) (conj_conj hP g)
  rw [← e]
  exact h0 _ (conj_inv_mem hP h hg)

end GlobalTheory.SmoothCyclic
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

theorem _root_.GlobalTheory.T.exists_finiteAdelicUnitaryGroup_iso : ∀ {D : D7} (V V' : HSp D) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (j' : Matrix (Fin V.rank) (Fin V'.rank) (EAf D)), HMul.hMul j j' = 1 → HMul.hMul j' j = 1 → HMul.hMul (HMul.hMul (Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) j) (V'.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)))) j = V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) → ∃ Φ : GfC V ≃ₜ* GfC V', ∀ g : GfC V, HMul.hMul (finE V' (Φ g : GA D V')).val j = HMul.hMul j (finE V (g : GA D V)).val := by
  first | exact @GlobalTheory.FinIsoGrp.exists_finIso | exact GlobalTheory.FinIsoGrp.exists_finIso | (intros; apply GlobalTheory.FinIsoGrp.exists_finIso <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

theorem _root_.GlobalTheory.T.exists_integral_change_baseFrame_orthonormal : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∃ u : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (β * intGL D.host.F D.host.E V.rank u).val * V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * (β * intGL D.host.F D.host.E V.rank u).val = 1 := by
  first | exact @GlobalTheory.AdelicOrthFrame.exists_orthonormal_baseFrame | exact GlobalTheory.AdelicOrthFrame.exists_orthonormal_baseFrame | (intros; apply GlobalTheory.AdelicOrthFrame.exists_orthonormal_baseFrame <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

theorem _root_.GlobalTheory.T.typePlaces_not_pairwise_conjugate : ∀ {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (Pg : Finset (Pl D.host.E)), (∀ PP, PP ∈ Pg ↔ ∃ k, Pb.Div k PP) → ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP' := by
  first | exact @GlobalTheory.TypePlaces.not_isConjPl | exact GlobalTheory.TypePlaces.not_isConjPl | (intros; apply GlobalTheory.TypePlaces.not_isConjPl <;> assumption)
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps : ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S → Even S.card → ∀ z, α * z ∉ L.lattice → L.derivWeierstrassP z * ∏ t ∈ S, L.derivWeierstrassP (z + t) = (∏ t ∈ S, L.derivWeierstrassP t) * α ^ 3 * L.derivWeierstrassP (α * z) := by
  first | exact @GlobalTheory.CMModel.derivWeierstrassP_mul_prod_translate_kernel | exact GlobalTheory.CMModel.derivWeierstrassP_mul_prod_translate_kernel | (intros; apply GlobalTheory.CMModel.derivWeierstrassP_mul_prod_translate_kernel <;> assumption)
end
