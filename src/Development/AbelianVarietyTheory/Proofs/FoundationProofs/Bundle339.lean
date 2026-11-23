module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetInertPlaceLatticeLength
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle338
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle261
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle167
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.TauLatticeLatticeHolds
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle035
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.QuotientMetricDivisors.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)

theorem _root_.GlobalTheory.T.doublingNorm_det_inertPlace_lattice_length : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)), ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ (g : GLoc σ J v) (α : GL (Fin n) (Fv F v ⊗[F] E)), (∀ y : Fin n → Fv F v ⊗[F] E, (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) → ∃ l : ℕ, latLength σ J L v g = l ∧ absEv F E v (Matrix.GeneralLinearGroup.det α) = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ≥0) ^ (-(l : ℤ)) := by
  first | exact @GlobalTheory.InertLatLength.absEv_det_eq_of_inert | exact GlobalTheory.InertLatLength.absEv_det_eq_of_inert | (intros; apply GlobalTheory.InertLatLength.absEv_det_eq_of_inert <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MovedSplit

open GlobalTheory.SplitIdem GlobalTheory.IdemModTwo

theorem idem_alg {T : Type} [CommRing T] (p U R w w' : T) (hU : p * U = U)
    (hR : R * R - (w + w') * R + w * w' * p = 0) (hδ : (w + w') * U - 2 * (U * R) = p) :
    (U * w - U * R) * (U * w - U * R) = U * w - U * R ∧
      (U * w - U * R) * (U * w' - U * R) = 0 ∧
      (U * w - U * R) + (U * w' - U * R) = p := by
  have h2 : (U * w - U * R) * (U * w' - U * R) = 0 := by
    linear_combination U * U * hR - w * w' * U * hU
  refine ⟨?_, h2, by linear_combination hδ⟩
  linear_combination (U * w - U * R) * hδ - h2 + (w - R) * hU

theorem idem_tensor {F A E K : Type} [Field F] [CommRing A] [Algebra F A] [CommRing E] [Algebra F E]
    [CommRing K] [Algebra F K] (φ : K →ₙ+* A)
    (hφ : ∀ (t : F) (y : K), φ (algebraMap F K t * y) = algebraMap F A t * φ y)
    (c : A ⊗[F] E →+* A ⊗[F] E) (a b : E) (t n : F) (r u : K)
    (hc1 : ∀ x : A, c (x ⊗ₜ 1) = x ⊗ₜ 1) (hca : ∀ x : A, c (x ⊗ₜ a) = x ⊗ₜ b)
    (ht : algebraMap F E t = a + b) (hn : algebraMap F E n = a * b)
    (hr : r * r - algebraMap F K t * r + algebraMap F K n = 0) (hu : u * (algebraMap F K t - 2 * r) = 1)
    (e : A ⊗[F] E) (he : e = φ u ⊗ₜ a + φ (-(u * r)) ⊗ₜ 1) :
    e * e = e ∧ e * c e = 0 ∧ e + c e = algebraMap A (A ⊗[F] E) (φ 1) := by
  let j : A →+* A ⊗[F] E := algebraMap A _
  let k : E →+* A ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E)
  have hjk : ∀ a x, a ⊗ₜ[F] x = j a * k x := fun a x => by
    simp [j, k, Algebra.TensorProduct.tmul_mul_tmul]
  have hF : ∀ s : F, j (algebraMap F A s) = k (algebraMap F E s) := fun s => by
    have h := hjk 1 (algebraMap F E s)
    rw [tmul_algebraMap_eq, mul_one, map_one, one_mul] at h
    exact h
  have h1 : e = j (φ u) * k a - j (φ u) * j (φ r) := by
    rw [he, hjk, hjk, map_neg, map_mul, map_neg, map_mul, map_one]; ring
  have h2 : c e = j (φ u) * k b - j (φ u) * j (φ r) := by
    rw [he, map_add (f := _), hc1, hca, hjk, hjk, map_neg, map_mul, map_neg, map_mul, map_one]; ring
  rw [h2, h1]
  refine idem_alg (j (φ 1)) _ _ _ _ ?_ ?_ ?_
  · rw [← map_mul, ← map_mul, one_mul]
  · have : φ r * φ r - algebraMap F A t * φ r + algebraMap F A n * φ 1 = 0 := by
      rw [← hφ, ← hφ, ← map_mul, ← map_sub, ← map_add (f := _), mul_one, hr, map_zero]
    have h := congrArg j this
    rwa [map_add, map_sub, map_mul, map_mul, map_mul, hF, hF, ht, hn, map_add, map_mul, map_zero] at h
  · have : algebraMap F A t * φ u - 2 * (φ u * φ r) = φ 1 := by
      rw [two_mul, ← hφ, ← map_mul, ← map_add (f := _), ← map_sub, ← hu]; congr 1; ring
    have h := congrArg j this
    rwa [map_sub, map_mul, map_mul, map_mul, map_ofNat, hF, ht, map_add] at h

theorem exists_root (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t n : 𝓞 F)
    (ht : t ∉ v.asIdeal) (hn : n ∈ v.asIdeal) :
    ∃ r u : v.adicCompletionIntegers F,
      r * r - algebraMap (𝓞 F) (v.adicCompletionIntegers F) t * r +
        algebraMap (𝓞 F) (v.adicCompletionIntegers F) n = 0 ∧
      u * (algebraMap (𝓞 F) (v.adicCompletionIntegers F) t - 2 * r) = 1 := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have hm : algebraMap (𝓞 F) (v.adicCompletionIntegers F) n ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff]
    exact fun h => h hn
  have hT : IsUnit (algebraMap (𝓞 F) (v.adicCompletionIntegers F) t) :=
    (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v t).2 ht
  generalize algebraMap (𝓞 F) (v.adicCompletionIntegers F) t = T at hT
  generalize algebraMap (𝓞 F) (v.adicCompletionIntegers F) n = N at hm
  obtain ⟨r, hr, hr0⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
    (Polynomial.X ^ 2 - Polynomial.C T * Polynomial.X + Polynomial.C N) (by monicity!) 0
    (by simpa using hm) (by simpa using hT.map _)
  rw [sub_zero] at hr0
  have hunit : IsUnit (T - 2 * r) := by
    by_contra h
    have h1 : T - 2 * r ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := h
    have h2 := Ideal.add_mem _ h1 (Ideal.mul_mem_left _ 2 hr0)
    rw [sub_add_cancel] at h2
    exact h2 hT
  obtain ⟨u, hu⟩ := hunit.exists_left_inv
  refine ⟨r, u, ?_, hu⟩
  simpa [Polynomial.IsRoot, pow_two] using hr

theorem exists_int (D : D7) (x : 𝓞 D.host.E) (hx : star (x : D.host.E) = x) :
    ∃ t : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t = x ∧
      algebraMap D.host.F D.host.E (t : D.host.F) = x := by
  obtain ⟨t, ht⟩ := exists_of_star_eq D hx
  have hxint : IsIntegral ℤ (x : D.host.E) := x.2
  have hi : IsIntegral ℤ t :=
    (isIntegral_algebraMap_iff).1 (ht ▸ hxint)
  exact ⟨⟨t, hi⟩, RingOfIntegers.ext ht, ht⟩

theorem exists_splitAt : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)), GlobalTheory.UnRep.SplitPl (GlobalTheory.Member.cF D) v → ∃ e : Formalism.L2.Theta.AE D, GlobalTheory.IdemModTwo.SplitAt D v e := by
  rintro D v ⟨P, hP, hPv, a, ha, b, hb, hbP⟩
  have hb' : (b : D.host.E) = star (a : D.host.E) := hb
  obtain ⟨t, ht, ht'⟩ := exists_int D (a + b) (by
    show star ((a : D.host.E) + b) = (a : D.host.E) + b
    rw [hb', star_add, star_star, add_comm])
  obtain ⟨n, hn, hn'⟩ := exists_int D (a * b) (by
    show star ((a : D.host.E) * b) = (a : D.host.E) * b
    rw [hb', star_mul', star_star, mul_comm])
  have htv : t ∉ v.asIdeal := by
    rw [← hPv, Ideal.mem_comap, ht]
    exact fun h => hbP ((Ideal.add_mem_iff_right P ha).1 h)
  have hnv : n ∈ v.asIdeal := by
    rw [← hPv, Ideal.mem_comap, hn]
    exact Ideal.mul_mem_right _ _ ha
  obtain ⟨r, u, hr, hu⟩ := exists_root D.host.F v t n htv hnv
  have key := idem_tensor (placeHom D.host.F v) (fun s y => by
      refine Prod.ext (mul_zero _).symm ?_
      show singleV D.host.F v _ = algebraMap D.host.F (Af D.host.F) s * singleV D.host.F v y
      rw [singleV_mul, AlgHom.commutes])
    (cA D) (a : D.host.E) (b : D.host.E) (t : D.host.F) (n : D.host.F) (r : Fv D.host.F v) (u : Fv D.host.F v)
    (fun x => by rw [cA_tmul, star_one]) (fun x => by rw [cA_tmul, hb']) ht' hn'
    (congrArg Subtype.val hr) (congrArg Subtype.val hu) _ rfl
  exact ⟨_, key⟩

end GlobalTheory.MovedSplit

end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaPair_coordinates_conjugate_bound : ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), 0 < Q → ∀ (B : ℝ), 1 ≤ B → (∀ τ, (P.n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ h T, P.coord h T ∈ Qbar ∧ ‖cj Qbar ρ (P.coord h T)‖ ^ 2 ≤ (Nat.card (Cls D P.a (intG D P.a)) : ℝ) ^ 2 * (Q : ℝ) ^ (P.a * P.d) * (((P.a.factorial : ℝ) ^ (∑ τ, P.n τ)) ^ 2 * (3 * (2 * ((fF D * P.a * P.d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * P.a * P.d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * P.a * P.d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (P.a * ∑ τ, P.n τ))) := by
  first | exact @GlobalTheory.NormSum.CoordConj.coord_conj_le | exact GlobalTheory.NormSum.CoordConj.coord_conj_le | (intros; apply GlobalTheory.NormSum.CoordConj.coord_conj_le <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.definiteThetaPair_terms_norms_independent_representatives : ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), 0 < Q → (∀ γ ∈ ratG D P.a, ∀ k ∈ intG D P.a, ∀ x h T, P.term (γ * x * k) h T = P.term x h T) ∧ (∀ γ ∈ ratG D P.d, ∀ j ∈ P.J, ∀ h, P.sq (γ * h * j) = P.sq h) ∧ (∀ (s : Cls D P.a (intG D P.a) → GA D P.a), (∀ q, DoubleCoset.mk (ratG D P.a) (intG D P.a) (s q) = q) → ∀ h T, P.coord h T = ∑ᶠ q, ((gam D (intG D P.a) (s q) : ℂ))⁻¹ * P.term (s q) h T) ∧ (∀ (s : Cls D P.d P.J → GA D P.d), (∀ q, DoubleCoset.mk (ratG D P.d) P.J (s q) = q) → P.norm = ∑ᶠ q, ((gam D P.J (s q) : ℝ))⁻¹ * P.sq (s q)) ∧ ((∃ h T, P.coord h T ≠ 0) → 0 < P.norm) := by
  first | exact @GlobalTheory.NormSum.RepInv.rep_indep | exact GlobalTheory.NormSum.RepInv.rep_indep | (intros; apply GlobalTheory.NormSum.RepInv.rep_indep <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.ToricDistribution

namespace GlobalTheory.ToricDistributionObj

theorem toricSumFormula_holds : ToricSumFormula :=
  GlobalTheory.ToricSumValue.toricSum_eq exists_isHeckeL_of_hasInf

end GlobalTheory.ToricDistributionObj
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.weilRepresentation_comm_heisenbergIntertwiner : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → δ ≠ 0 → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (g h k : GA D N) (g' h' k' : GA D N') (L₁ L₂ M₁ M₂ : Lat D N) (L₁' L₂' M₁' M₂' : Lat D N'), Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((g * h : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((g' * h' : GA D N') : GL (Fin N') (AE D)) L₂' → Moves D (k : GL (Fin N) (AE D)) M₁ → Moves D (k' : GL (Fin N') (AE D)) M₁' → Moves D ((g * k : GA D N) : GL (Fin N) (AE D)) M₂ → Moves D ((g' * k' : GA D N') : GL (Fin N') (AE D)) M₂' → ∀ F ∈ Th D (tor0 D cc δ) L₁ L₁', W.Om g g' (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') (La D (tor0 D cc δ) M₁ M₁') F) = Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₂ L₂') (La D (tor0 D cc δ) M₂ M₂') (W.Om g g' F) := by
  first | exact @GlobalTheory.WeilInter.om_iop | exact GlobalTheory.WeilInter.om_iop | (intros; apply GlobalTheory.WeilInter.om_iop <;> assumption)
end

section

namespace GlobalTheory.OpenKernelLocallyConstant

theorem isOpen_ker_and_isLocallyConstant {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (C : Type) [Group C] (N : ℕ) (ψ : Formalism.ConjugateSelfDual.G ℚ Ω →* C) (hN : N ≠ 0)
    (hψ : UpperTheory.V.Af.KillsMu N ψ) :
    IsOpen (↑(MonoidHom.ker ψ) : Set (Formalism.ConjugateSelfDual.G ℚ Ω)) ∧
      IsLocallyConstant (⇑ψ : Formalism.ConjugateSelfDual.G ℚ Ω → C) := by
  classical
  have hopen : IsOpen (↑(MonoidHom.ker ψ) : Set (Formalism.ConjugateSelfDual.G ℚ Ω)) := by
    have halg : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
    let S : Set Ω := {z | z ^ N = 1}
    have hS : S.Finite := by
      refine (Polynomial.nthRoots N (1 : Ω)).toFinset.finite_toSet.subset ?_
      intro z hz
      have hz' : z ^ N = 1 := hz
      simpa [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hN)] using hz'
    have : Finite S := hS.to_subtype
    have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => (halg.isAlgebraic x).isIntegral
    refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ S).fixingSubgroup) ?_
      (IntermediateField.fixingSubgroup_isOpen _)
    intro s hs
    rw [MonoidHom.mem_ker]
    refine hψ s ?_
    intro z hz
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs z
      (IntermediateField.subset_adjoin ℚ S hz)
  refine ⟨hopen, ?_⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (MonoidHom.ker ψ : Set (Formalism.ConjugateSelfDual.G ℚ Ω)),
    hopen.preimage (continuous_const.mul continuous_id), by simp, ?_⟩
  intro y hy
  have h : ψ (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  exact h.symm

end GlobalTheory.OpenKernelLocallyConstant
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory.DecLocal

theorem exists_mulEquiv_cyc : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → IsPlaceOver A v → ∃ (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (_ : FiniteDimensional ℚ_[l] K) (e : Dec (F := F) A ≃* GK l K), Continuous e ∧ Continuous e.symm ∧ ∀ (r : ℕ) (g : Dec (F := F) A), cycK l K r (e g) = cycMod F Ω l r (g : G F Ω) := by
  intro F Ω _ _ _ _ _ l _ v A hv hA
  obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding (l := l) F Ω v A hv hA
  let K : Formalism.BasicNotions.Loc.FinExt l :=
    ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : F => j (algebraMap F Ω x)),
      GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩
  have hK := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hj K rfl
  obtain ⟨hf, hf'⟩ := GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (PadicAlgCl l) K.1
  refine ⟨K.1, hK, e.trans (IntermediateField.fixingSubgroupEquiv K.1), hf.comp he, he'.comp hf',
    fun r g => Units.ext ?_⟩
  have hl : l.Prime := Fact.out
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := j.charZero
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  have hζ' := hζ.map_of_injective j.injective
  have ha : (g : Ω ≃ₐ[F] Ω) ζ = ζ ^ ((cycMod F Ω l r (g : G F Ω) : ZMod (l ^ r))).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[F] Ω) Ω (g : Ω ≃ₐ[F] Ω)) ζ
      hζ.pow_eq_one
  set σ : GK l K.1 := (e.trans (IntermediateField.fixingSubgroupEquiv K.1)) g with hσ
  have hb : σ (j ζ) = j ζ ^ ((cycK l K.1 r σ : ZMod (l ^ r))).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GK l K.1) (PadicAlgCl l) σ) _
      hζ'.pow_eq_one
  have hc : σ (j ζ) = j ((g : Ω ≃ₐ[F] Ω) ζ) := hec g ζ
  rw [hc, ha, map_pow] at hb
  exact (ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)).symm

end GlobalTheory.DecLocal
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.DualLat

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem mem_one_iff (x : K) : x ∈ (1 : Submodule (𝓞 K) K) ↔ IsIntegral ℤ x := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

theorem star_mem_one [StarRing K] {x : K} (h : x ∈ (1 : Submodule (𝓞 K) K)) :
    star x ∈ (1 : Submodule (𝓞 K) K) := by
  rw [mem_one_iff] at h ⊢
  exact map_isIntegral_int (starRingEnd K) h

theorem exists_den_finset (s : Finset K) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ x ∈ s, d • x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨⟨d, hd⟩, hy⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) s
  exact ⟨d, nonZeroDivisors.ne_zero hd, fun x hx => Submodule.mem_one.2 (hy x hx)⟩

theorem exists_smul_mem {M : Submodule (𝓞 K) (Fin n → K)}
    {x : Fin n → K} (hx : x ∈ Submodule.span K (M : Set (Fin n → K))) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.DeterminantSimpLemma.main
  | exact _root_.GlobalTheory.DeterminantSimpLemma.main
  | (apply _root_.GlobalTheory.DeterminantSimpLemma.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DeterminantSimpLemma.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DeterminantSimpLemma.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DeterminantSimpLemma.main ..)

theorem isLattice_dualFr (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsFullLattice K M) :
    Submodule.IsFullLattice K (dualFr M) :=
  du_dualFr_lattice latticeBasisExists_holds M hM

theorem isLattice_hdualFr [StarRing K] (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hG : IsUnit G.det) (hM : Submodule.IsFullLattice K M) : Submodule.IsFullLattice K (hdualFr G M) :=
  (dualFrameLattice_holds K n G M hG hM).2

omit [NumberField K] in
theorem star_dot [StarRing K] (x y : Fin n → K) : star (x ⬝ᵥ y) = star y ⬝ᵥ star x := by
  simp [dotProduct, mul_comm]

theorem hdualFr_dualFr [StarRing K] (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hG : IsUnit G.det) : hdualFr (G⁻¹)ᵀ (dualFr M) = dualFr (hdualFr G M) := by
  have key : ∀ φ ψ : Fin n → K, star φ ⬝ᵥ ((G⁻¹)ᵀ *ᵥ ψ) = ψ ⬝ᵥ (G⁻¹ *ᵥ star φ) := by
    intro φ ψ
    rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec]
  ext ψ
  constructor
  · intro h x hx
    have hφ : star (G *ᵥ x) ∈ dualFr M := by
      intro y hy
      have := star_mem_one (hx y hy)
      rwa [star_dot, star_star] at this
    have := h _ hφ
    rwa [key, star_star, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hG, Matrix.one_mulVec] at this
  · intro h φ hφ
    rw [key]
    refine h _ fun y hy => ?_
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hG, Matrix.one_mulVec, ← star_dot]
    exact star_mem_one (hφ y hy)

theorem dualFr_lattice_and_hdual :
    (∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (G : Matrix (Fin n) (Fin n) K)
      (M : Submodule (𝓞 K) (Fin n → K)), IsUnit G.det → Submodule.IsFullLattice K M →
      Submodule.IsFullLattice K (dualFr M) ∧ Submodule.IsFullLattice K (hdualFr G M)) ∧ DualFrHdual :=
  ⟨fun _ _ _ _ _ G M hG hM => ⟨isLattice_dualFr M hM, isLattice_hdualFr G M hG hM⟩,
    fun _ _ _ _ _ G M _ hG _ => hdualFr_dualFr G M hG⟩

end GlobalTheory.DualLat
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassUnfold

theorem integral_eq_sum_of_surjective {G H : Type} [Group G] [Group H] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ]
    (π : G →* H) (hπ : Function.Surjective π) (J : Subgroup H) (𝓖 : Set G) (h𝓖 : IsFundamentalDomain Γ 𝓖 ν)
    (ho : IsOpen (J.comap π : Set G)) (h1 : ν (J.comap π) = 1) (I : Type) [Fintype I] (y : I → H)
    (hy : Bridge.IsReps (π.comp Γ.subtype) J y) (hf : ∀ c, Finite (Bridge.stab (π.comp Γ.subtype) J (y c)))
    (Φ : H → ℂ) (hΦ : ∀ (γ : Γ) h (k : J), Φ (π.comp Γ.subtype γ * h * k) = Φ h) :
    ∫ h in 𝓖, Φ (π h) ∂ν = ∑ c, (Nat.card (Bridge.stab (π.comp Γ.subtype) J (y c)) : ℂ)⁻¹ * Φ (y c) := by
  choose h hh using fun c => hπ (y c)
  have hS : ∀ c, {γ : G | γ ∈ Γ ∧ (h c)⁻¹ * γ * h c ∈ J.comap π} =
      Subtype.val '' (Bridge.stab (π.comp Γ.subtype) J (y c) : Set Γ) := by
    intro c
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, Bridge.mem_stab, Subgroup.mem_comap, map_mul,
      map_inv, hh]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨⟨γ, a⟩, b, rfl⟩
    · rintro ⟨δ, b, rfl⟩
      exact ⟨δ.2, b⟩
  have hfin : ∀ c, (Bridge.stab (π.comp Γ.subtype) J (y c) : Set Γ).Finite := fun c => hf c
  have key := GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset G ν Γ (J.comap π) 𝓖 h𝓖 ho
    (by rw [h1]; exact ENNReal.one_ne_top) I h ?_ (fun c => by rw [hS]; exact (hfin c).image _)
    (fun x => Φ (π x)) ?_ ?_
  · rw [key.2.2, h1]
    simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hS, Set.ncard_image_of_injective _ Subtype.val_injective, hh]
    rfl
  · intro x
    refine (existsUnique_congr fun i => ?_).1 (hy (π x))
    constructor
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, γ.2, (γ * h i)⁻¹ * x, ?_, by group⟩
      rw [Subgroup.mem_comap, map_mul, map_inv, map_mul, hh, e]
      change (π γ * y i)⁻¹ * (π γ * y i * k) ∈ J
      rw [inv_mul_cancel_left]
      exact k.2
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨⟨γ, hγ⟩, ⟨π k, hk⟩, by rw [map_mul, map_mul, hh]; rfl⟩
  · intro γ hγ x
    have := hΦ ⟨γ, hγ⟩ (π x) 1
    rw [OneMemClass.coe_one, mul_one] at this
    rw [map_mul]
    exact this
  · intro k hk x
    have := hΦ 1 (π x) ⟨π k, hk⟩
    rw [map_one, one_mul] at this
    rw [map_mul]
    exact this

theorem integral_eq_classSum : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), L.P.H = ⊥ → IsMeasDef V (lev D.sp.cm V.gram β L) μ 𝓕 → ∀ (I : Type) [Fintype I] (y : I → Bridge.Gf V), Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y → (∀ c, Finite (Bridge.stab (Bridge.ratF V) (levEnv V β L).J (y c))) → ∀ Φ : Bridge.Gf V → ℂ, (∀ (γ : GQ V) h (k : (levEnv V β L).J), Φ (Bridge.ratF V γ * h * k) = Φ h) → ∫ h in 𝓕, Φ (fin V h) ∂μ = ∑ c, (Nat.card (Bridge.stab (Bridge.ratF V) (levEnv V β L).J (y c)) : ℂ)⁻¹ * Φ (y c) := by
  intro D V β L μ 𝓕 hL hμ I _ y hy hf Φ hΦ
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  haveI := hμ.1.1
  have hK : (levEnv V β L).J.comap (finHom V).rangeRestrict = (lev D.sp.cm V.gram β L).comap (finE V) := by
    ext g
    change (finE V g ∈ parLev D.sp.cm V.gram β L ∧ rTup β L (finE V g) ∈ (⊥ : Subgroup _)) ↔
      (finE V g ∈ parLev D.sp.cm V.gram β L ∧ rTup β L (finE V g) ∈ L.P.H)
    rw [hL]
  refine integral_eq_sum_of_surjective μ (GQ V) (finHom V).rangeRestrict (finHom V).rangeRestrict_surjective
    (levEnv V β L).J 𝓕 hμ.2 ?_ ?_ I y hy hf Φ hΦ
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_level V β L] with κ hκ
    exact hκ.1
  · rw [hK]
    exact GlobalTheory.Mass.Levels.measure_comap_finE hμ.1

end GlobalTheory.ClassUnfold
end
