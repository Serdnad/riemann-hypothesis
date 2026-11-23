module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle842
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveTensorOfFibreProjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle861
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedBasesBlockTriangularOfReducedEtaleFiltrat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle894
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle871
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle862
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle873
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle138
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle900
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU

@[expose] public section

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

theorem _root_.GlobalTheory.T.unitaryChartSectionFrameEntries_hasStrictFDerivAt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → HasStrictFDerivAt (yF X) (dY X) 0 := by
  first | exact @GlobalTheory.SUChartSection.yF_hasStrictFDerivAt | exact GlobalTheory.SUChartSection.yF_hasStrictFDerivAt | (intros; apply GlobalTheory.SUChartSection.yF_hasStrictFDerivAt <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

theorem _root_.GlobalTheory.T.latticeIntertwiner_prod_orthogonal_blocks : ∀ (L : PeriodPair) (ω₀ : ℂ) (c : ℝ) (ι m : Type) [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)), IsSemiChar (stdH L m) Λ (alphaQ c (stdH L m)) → F0 L ω₀ m ∈ fixedBy (stdH L m) (alphaQ c (stdH L m)) (stdLat L m) → relIdx (stdLat L m) Λ ≠ 0 → IsSemiChar (stdH L (ι × m)) (blkLat Λ) (alphaQ c (stdH L (ι × m))) ∧ F0 L ω₀ (ι × m) ∈ fixedBy (stdH L (ι × m)) (alphaQ c (stdH L (ι × m))) (stdLat L (ι × m)) ∧ relIdx (stdLat L (ι × m)) (blkLat Λ) ≠ 0 ∧ ∀ w, inter (stdH L (ι × m)) (alphaQ c (stdH L (ι × m))) (stdLat L (ι × m)) (blkLat Λ) (F0 L ω₀ (ι × m)) w = ∏ k, inter (stdH L m) (alphaQ c (stdH L m)) (stdLat L m) Λ (F0 L ω₀ m) (fun v => w (k, v)) := by
  first | exact @GlobalTheory.BaseVacuum.prod_blk_inter | exact GlobalTheory.BaseVacuum.prod_blk_inter | (intros; apply GlobalTheory.BaseVacuum.prod_blk_inter <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

theorem _root_.GlobalTheory.T.exists_equivariantLift_functional_quotient_projective : ∀ {C : Type} [CommRing C] (I : Ideal C) {A : Type} [CommRing A] {H : Type u} [AddCommGroup H] [Module C H]
  (σ : A →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf σ; Module.Projective (C ⊗[ℤ] A) H) →
  ∀ (χ : A →+* C) (l₀ : H →ₗ[C] C ⧸ I), (∀ a x, l₀ (σ a x) = Ideal.Quotient.mk I (χ a) * l₀ x) →
  ∃ l : H →ₗ[C] C, (∀ a x, l (σ a x) = χ a * l x) ∧ ∀ x, Ideal.Quotient.mk I (l x) = l₀ x := by
  first | exact @GlobalTheory.eqLift_tensorModOf | exact GlobalTheory.eqLift_tensorModOf | (intros; apply GlobalTheory.eqLift_tensorModOf <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_liftSummand_lie_residueCharZero : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (I : Ideal C), I ^ 2 = ⊥ → IsUnit (p : C) → ∀ (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (ρ : D.O →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf (ρ.comp (algebraMap (𝓞 D.F) D.O)); Module.Projective (C ⊗[ℤ] 𝓞 D.F) H) → ∀ (e : Module.End C H), e * e = e → (∀ c, ρ c * e = e * ρ c) → (∀ x, ρ (algebraMap (𝓞 D.F) D.O D.ω) (e x) = tR b.ρ • e x) → ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ (c : D.O), ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, e x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → (∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F) → ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : D.O), ∀ x ∈ G, ρ c x ∈ G) ∧ G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧ ∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by
  first | exact @GlobalTheory.HTSummand.liftSummand_residueCharZero | exact GlobalTheory.HTSummand.liftSummand_residueCharZero | (intros; apply GlobalTheory.HTSummand.liftSummand_residueCharZero <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.projective_tensor_of_fibre_projective' : ∀ (C k B : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Field k] [CommRing B] (σ : C →+* k), Function.Surjective σ → ∀ (H V : Type 1) [AddCommGroup H] [Module C H] [AddCommGroup V] [Module k V] (ρ : B →+* Module.End C H) (ρ' : B →+* Module.End k V) (f : H →ₛₗ[σ] V), Module.Finite C H → Module.Projective C H → Function.Surjective f → (∀ h, f h = 0 → h ∈ RingHom.ker σ • (⊤ : Submodule C H)) → (∀ x h, f (ρ x h) = ρ' x (f h)) → (letI := GlobalTheory.HTSummand.tensorModOf ρ'; Module.Projective (k ⊗[ℤ] B) V) → letI := GlobalTheory.HTSummand.tensorModOf ρ; Module.Projective (C ⊗[ℤ] B) H := by
  first | exact @GlobalTheory.HTSummand.projective_tensor_of_fibre_projective | exact GlobalTheory.HTSummand.projective_tensor_of_fibre_projective | (intros; apply GlobalTheory.HTSummand.projective_tensor_of_fibre_projective <;> assumption)
end

section

open NumberField GlobalTheory.ExpFrame

theorem _root_.GlobalTheory.T.adaptedBases_blockTriangular_of_reducedEtaleFiltration : ∀ (ι : Type) (σ : Equiv.Perm ι) (l n t : ℕ) (F : Type) [Field F] (un : PowerSeries F) (P D : ι → Matrix (Fin n) (Fin n) (PowerSeries F)) (Pψ Dψ : Fin t → ι → PowerSeries F), 0 < l → Nonempty ι → GlobalTheory.WachBlock.RedFilt σ l un P D Pψ Dψ → ∃ (g : ι → (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) (b : Fin n → ℕ) (pos : Fin t → Fin n) (w : ι → Fin t → (PowerSeries F)ˣ) (kap : ι → Fin t → ℤ), (Function.Injective pos ∧ ∀ s j, b j = b (pos s) → j = pos s) ∧ (∀ i, (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i)).BlockTriangular b) ∧ (∀ i, (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i)).BlockTriangular b) ∧ (∀ i s, ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.frob0 l (w (σ i) s : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ ((l : ℤ) * kap (σ i) s) * ((Pψ s i : PowerSeries F) : LaurentSeries F) = ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i) (pos s) (pos s) : PowerSeries F) : LaurentSeries F) * ((w i s : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ kap i s) ∧ (∀ i s, ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.gam0 0 un (w i s : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.gamSer 0 un : PowerSeries F) : LaurentSeries F) ^ kap i s * ((1 + PowerSeries.X * Dψ s i : PowerSeries F) : LaurentSeries F) = ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i) (pos s) (pos s) : PowerSeries F) : LaurentSeries F) * ((w i s : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ kap i s) := by
  first | exact @GlobalTheory.WachBlock.adapted_bases_of_redFilt | exact GlobalTheory.WachBlock.adapted_bases_of_redFilt | (intros; apply GlobalTheory.WachBlock.adapted_bases_of_redFilt <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

namespace GlobalTheory.WachBlock

theorem integralBlock_of_blockPair : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n t : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), BlockPair E Ω l n t J bot → GlobalTheory.WachBlock.IntegralBlock E Ω l n t J bot := by
  intro E Ω _ _ _ _ _ l _ n t J bot hB
  obtain ⟨r, a, ρ, χ, hat, hr, hρ, hχ, hcong⟩ := hB
  obtain ⟨LL, hζ, hτ, hrL, hρL, hχL⟩ := GlobalTheory.T.exists_common_finiteExtension_galoisReps_characters E Ω l n a t r ρ χ hr.1 hρ (fun s => (hχ s).1)
  obtain ⟨A, hA1, hA2, hAr⟩ := GlobalTheory.T.exists_conj_integral_galoisRep E Ω l n LL r hr.1 hrL
  obtain ⟨B, hB1, hB2, hBρ⟩ := GlobalTheory.T.exists_conj_integral_galoisRep E Ω l a LL ρ hρ hρL
  have memLL : ∀ {m : ℕ} (X Y Z : Matrix (Fin m) (Fin m) (PadicAlgCl l)), (∀ i j, X i j ∈ LL.1) →
      (∀ i j, Y i j ∈ LL.1) → (∀ i j, Z i j ∈ LL.1) → ∀ i j, (X * Y * Z) i j ∈ LL.1 := by
    intro m X Y Z hX hY hZ i j
    simp only [Matrix.mul_apply]
    exact LL.1.sum_mem fun k _ => LL.1.mul_mem (LL.1.sum_mem fun k' _ => LL.1.mul_mem (hX _ _) (hY _ _)) (hZ _ _)
  have cj : ∀ {m : ℕ} (C : GL (Fin m) (PadicAlgCl l)) (x : GL (Fin m) (PadicAlgCl l)),
      (((MulAut.conj C⁻¹).toMonoidHom x : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) =
        ((C⁻¹ * x * C : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) := by
    intro m C x
    simp [MulAut.conj_apply]
  obtain ⟨r', hr'⟩ := (GlobalTheory.IntDescend.descend l LL (G E Ω)).1 n ((MulAut.conj A⁻¹).toMonoidHom.comp r) (fun g i j => by
    rw [MonoidHom.comp_apply, cj]
    refine ⟨?_, hAr g i j⟩
    simpa [Units.val_mul] using memLL _ _ _ hA2 (hrL g) hA1 i j)
  obtain ⟨ρ', hρ'⟩ := (GlobalTheory.IntDescend.descend l LL (G E Ω)).1 a ((MulAut.conj B⁻¹).toMonoidHom.comp ρ) (fun g i j => by
    rw [MonoidHom.comp_apply, cj]
    refine ⟨?_, hBρ g i j⟩
    simpa [Units.val_mul] using memLL _ _ _ hB2 (hρL g) hB1 i j)
  choose ψ hψ using fun s => (GlobalTheory.IntDescend.descend l LL (G E Ω)).2 (χ s) (fun g => ⟨hχL s g, GlobalTheory.T.norm_galoisCharacter_padicAlgClosure_eq_one E Ω l (χ s) (hχ s).1 g⟩)
  haveI : IsDiscreteValuationRing ↥(OL LL) := Examples₂.LB.OL_dvr LL
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  have hmat : ∀ g, (r' g : Matrix (Fin n) (Fin n) ↥(OL LL)).map (GlobalTheory.WachBlock.ofOL l LL) =
      ((A⁻¹ * r g * A : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) := by
    intro g
    rw [← cj]
    exact congrArg (fun f : G E Ω →* GL (Fin n) (PadicAlgCl l) => ((f g : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l))) hr'
  have hmatρ : ∀ g, (ρ' g : Matrix (Fin a) (Fin a) ↥(OL LL)).map (GlobalTheory.WachBlock.ofOL l LL) =
      ((B⁻¹ * ρ g * B : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) := by
    intro g
    rw [← cj]
    exact congrArg (fun f : G E Ω →* GL (Fin a) (PadicAlgCl l) => ((f g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) hρ'
  have hψv : ∀ s g, GlobalTheory.WachBlock.ofOL l LL ((ψ s g : (↥(OL LL))ˣ) : ↥(OL LL)) = ((χ s g : (PadicAlgCl l)ˣ) : PadicAlgCl l) := by
    intro s g
    exact congrArg (fun f : G E Ω →* (PadicAlgCl l)ˣ => ((f g : (PadicAlgCl l)ˣ) : PadicAlgCl l)) (hψ s)
  have hcp : ∀ {m : ℕ} (C : GL (Fin m) (PadicAlgCl l)) (N : Matrix (Fin m) (Fin m) (PadicAlgCl l)),
      (((C⁻¹ : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) * N * (C : Matrix (Fin m) (Fin m) (PadicAlgCl l))).charpoly = N.charpoly := by
    intro m C N
    simpa using Matrix.charpoly_units_conj C⁻¹ N
  have hc : ∀ g m, ((r' g : Matrix (Fin n) (Fin n) ↥(OL LL)).charpoly - (ρ' g : Matrix (Fin a) (Fin a) ↥(OL LL)).charpoly *
      ∏ s, (Polynomial.X - Polynomial.C ((ψ s g : (↥(OL LL))ˣ) : ↥(OL LL)))).coeff m ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    intro g m
    rw [GlobalTheory.IntMaxFinExt.mem_maximalIdeal_iff_norm_lt_one]
    have e : GlobalTheory.WachBlock.ofOL l LL (((r' g : Matrix (Fin n) (Fin n) ↥(OL LL)).charpoly - (ρ' g : Matrix (Fin a) (Fin a) ↥(OL LL)).charpoly *
      ∏ s, (Polynomial.X - Polynomial.C ((ψ s g : (↥(OL LL))ˣ) : ↥(OL LL)))).coeff m) =
        ((r g).val.charpoly - (ρ g).val.charpoly * ∏ s, (Polynomial.X - Polynomial.C ((χ s g : (PadicAlgCl l)ˣ) : PadicAlgCl l))).coeff m := by
      rw [← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map,
        ← Matrix.charpoly_map, hmat, hmatρ]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hψv, Units.val_mul]
      rw [hcp, hcp]
    have h := hcong g m
    rw [← e] at h
    exact h
  obtain ⟨R, M, rs, hM0, hML, hMm, hMs, hrs, hline⟩ := GlobalTheory.integral_flag_lift_of_residue ↥(OL LL) (G E Ω) n a t r' ρ' ψ ϖ hϖ hat hc GlobalTheory.T.exists_stable_character_flag_of_charpoly_factor
  refine ⟨LL, r', ψ, ϖ, R, M, rs, hζ, hτ, ?_, fun s => ?_, hϖ, hM0, hML, hMm, hMs, hrs, hline⟩
  · have : (Matrix.GeneralLinearGroup.map (GlobalTheory.WachBlock.ofOL l LL)).comp r' = (MulAut.conj A⁻¹).toMonoidHom.comp r := hr'
    rw [this]
    exact GlobalTheory.crysWith_conj E Ω l n r A LL _ (fun i j => ⟨hA1 i j, hA2 i j⟩) hr
  · have : (Units.map (GlobalTheory.WachBlock.ofOL l LL).toMonoidHom).comp (ψ s) = χ s := hψ s
    rw [this]
    exact hχ s

end GlobalTheory.WachBlock

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem pureLift_step : GlobalTheory.Published.GrothendieckMessing → ∀ p : ℕ, p.Prime → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), IsNilpotent (p : R) → Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (g g' : ℕ) (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (i : A₀.left ⟶ A.left) (j : B₀.left ⟶ B.left), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom → IsGrpPullback A₀ A (spMap π) i → IsGrpPullback B₀ B (spMap π) j → ∀ (U : A ⟶ A) (V : B ⟶ B) (U₀ : A₀ ⟶ A₀) (V₀ : B₀ ⟶ B₀) [IsMonHom U] [IsMonHom V] [IsMonHom U₀] [IsMonHom V₀], i ≫ U.left = U₀.left ≫ i → j ≫ V.left = V₀.left ≫ j → ∀ r s r' s' : R, IsPure A U r s → IsPure B V r' s' → IsUnit (r - s') → ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀], U₀ ≫ f₀ = f₀ ≫ V₀ → ∃ f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j ∧ U ≫ f = f ≫ V ∧ ∀ f' : A ⟶ B, IsMonHom f' → i ≫ f'.left = f₀.left ≫ j → f' = f := by
  intro GM p hp R R₀ _ _ π hR hπ h2 g g' A B _ _ A₀ B₀ _ _ i j hA hgA hB hgB hi hj U V U₀ V₀ _ _ _ _ eU eV
    r s r' s' hU hV hu f₀ _ ef₀
  have h2' : RingHom.ker π ^ 2 = 0 := by rw [Ideal.zero_eq_bot]; exact h2
  obtain ⟨Hc, -, Hl⟩ := GM p hp R hR _ (GlobalTheory.Cris.divided₂ h2') (GlobalTheory.Cris.isDPNilpotent_squareZero h2') R₀ π hπ rfl
  set κ := GlobalTheory.Cris.divided₂ h2'
  have inj := (Hc.crysToDR_bijective hi hA hgA).1
  have key : ∀ d ∈ GlobalTheory.DeRham.liftFil κ hi, GlobalTheory.DeRham.push κ (spMap π) f₀ d ∈ GlobalTheory.DeRham.liftFil κ hj := by
    intro d hd
    have hd' : GlobalTheory.DeRham.crysToDR κ hi d ∈ GlobalTheory.DeRham.Fil A := hd
    have h1 : GlobalTheory.DeRham.push κ (spMap π) U₀ d = r • d := by
      apply inj
      rw [GlobalTheory.DeRham.crysToDR_push κ hi hi U₀ U eU, map_smul]
      exact hU.1 _ hd'
    have h3 : GlobalTheory.DeRham.push κ (spMap π) V₀ (GlobalTheory.DeRham.push κ (spMap π) f₀ d)
        = r • GlobalTheory.DeRham.push κ (spMap π) f₀ d := by
      have := congrArg (fun φ => φ d) (GlobalTheory.DeRham.push_comp κ (spMap π) U₀ f₀)
      have h4 := congrArg (fun φ => φ d) (GlobalTheory.DeRham.push_comp κ (spMap π) f₀ V₀)
      simp only [LinearMap.comp_apply] at this h4
      rw [← h4, ← GlobalTheory.DeRham.push_congr κ (spMap π) ef₀, this, h1, map_smul]
    show GlobalTheory.DeRham.crysToDR κ hj _ ∈ GlobalTheory.DeRham.Fil B
    refine IsPure.mem_Fil hV hu ?_
    rw [← GlobalTheory.DeRham.crysToDR_push κ hj hj V₀ V eV, h3, map_smul]
  obtain ⟨f, ⟨hf, ef⟩, uf⟩ := Hl g A₀ A i hi hA hgA g' B₀ B j hj hB hgB f₀ key
  refine ⟨f, hf, ef, ?_, fun f' hf' ef' => uf f' ⟨hf', ef'⟩⟩
  have e1 : i ≫ (U ≫ f).left = (U₀ ≫ f₀).left ≫ j := by
    simp only [Over.comp_left, ← Category.assoc, eU]
    simp only [Category.assoc, ef]
  have e2 : i ≫ (f ≫ V).left = (U₀ ≫ f₀).left ≫ j := by
    rw [Over.comp_left, ← Category.assoc, ef, Category.assoc, eV, ← Category.assoc, ← Over.comp_left, ← ef₀]
  exact Hl.unique hi hA hgA hj hB hgB (U₀ ≫ f₀) e1 e2

end GlobalTheory
end
end

section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

theorem _root_.GlobalTheory.T.exists_labels_semisimple_parameter_GL_finiteField : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r : ℕ) (s : SSParam p ℂ r), ∃ (x : Cyc s.1 → Fbar p) (f : (ZMod p)[X]), Labels L s x f := by
  first | exact @GlobalTheory.ParamLabel.exists_labels | exact GlobalTheory.ParamLabel.exists_labels | (intros; apply GlobalTheory.ParamLabel.exists_labels <;> assumption)
end

section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

theorem _root_.GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (N : ℕ), 0 < N → (∀ (d : ℕ) (h : d ∣ N) (θ : Tor p d →* ℂˣ) (x : Fbar p) (n : ℕ), LabelsChar L θ x → LabelsChar L ((θ.comp (torNorm p h)) ^ n) (x ^ n)) ∧ ∀ (χ : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ), LabelsTame L χ a → LabelsChar L (χ.comp (baseNorm p N)) (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) ∧ LabelsTame L χ⁻¹ a⁻¹ := by
  first | exact @GlobalTheory.LabelNorm.main | exact GlobalTheory.LabelNorm.main | (intros; apply GlobalTheory.LabelNorm.main <;> assumption)
end

section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

theorem _root_.GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (b : Fin r → Fin r) (x : Cyc b → Fbar p) (f : (ZMod p)[X]), IsRootPoly x f → f.natDegree = r ∧ f.coeff 0 ≠ 0 ∧ (Squarefree f ↔ Function.Injective (rootElt x)) ∧ (Squarefree f → (∀ c, (minpoly (ZMod p) (x c)).natDegree = cycLen b c) ∧ Function.Injective (fun c => minpoly (ZMod p) (x c)) ∧ f = ∏ c, minpoly (ZMod p) (x c)) := by
  first | exact @GlobalTheory.ParamLabel.RootPolyFactor.rootPoly_factor | exact GlobalTheory.ParamLabel.RootPolyFactor.rootPoly_factor | (intros; apply GlobalTheory.ParamLabel.RootPolyFactor.rootPoly_factor <;> assumption)
end

section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

theorem _root_.GlobalTheory.T.labelled_characters_eq_and_congr_primeToPart : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (d : ℕ), 0 < d → ∀ (θ θ' : Tor p d →* ℂˣ) (x x' : Fbar p), LabelsChar L θ x → LabelsChar L θ' x' → (θ = θ' ↔ x = x') ∧ ∀ l : ℕ, l.Prime → (CongrMod l θ θ' ↔ Formalism.CyclotomicNorms.primeToPart l x = Formalism.CyclotomicNorms.primeToPart l x') := by
  first | exact @GlobalTheory.ParamLabel.Congr.eq_and_congr | exact GlobalTheory.ParamLabel.Congr.eq_and_congr | (intros; apply GlobalTheory.ParamLabel.Congr.eq_and_congr <;> assumption)
end
