module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3397
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3399
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3297
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
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Functor.grpObjObj

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HdRFibre



theorem fibre_baseChange : ∀ (C₀ : Type) [CommRing C₀] [IsLocalRing C₀] (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [CommRing O] (a : OAct O A₀), ∃ f : HdR A₀ →ₛₗ[algebraMap C₀ (IsLocalRing.ResidueField C₀)] HdR ((Over.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀)))).obj A₀), Function.Surjective f ∧ (∀ h, f h = 0 → h ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ (HdR A₀))) ∧ ∀ (x : O) (h : HdR A₀), f (act (dp0 C₀) (𝟙 _) a x h) = act (dp0 (IsLocalRing.ResidueField C₀)) (𝟙 _) (OAct.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ a) x (f h) := by
  intro C₀ _ _ A₀ _ _ hA O _ a
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C₀ A₀ hA
  obtain ⟨hFree, -, hBC, -, -⟩ := GlobalTheory.T.abelianScheme_firstDeRham_structure
  have hh := isGrpPullback_pullback A₀ (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀)))
  have hbc := (hBC C₀ A₀ g hA hg (IsLocalRing.ResidueField C₀) _ _ hh).1
  obtain ⟨hfin, hproj, -⟩ := hFree.prim hA hg
  haveI := Module.finitePresentation_of_projective C₀ (primDR A₀)
  haveI : Module.Free C₀ (primDR A₀) := Module.free_of_flat_of_isLocalRing
  refine ⟨hbc.bcMap, ?_, ?_, ?_⟩
  · intro h'
    let l : primDR A₀ →ₗ[C₀] IsLocalRing.ResidueField C₀ :=
      { toFun c := h' ((Published.AbelianDeRham.bcMor hh).pull c)
        map_add' c d := by rw [map_add (f := _), map_add (f := _)]
        map_smul' r c := by
          rw [map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
    obtain ⟨hh', hhl⟩ := Module.projective_lifting_property (Algebra.linearMap C₀ (IsLocalRing.ResidueField C₀)) l
      IsLocalRing.residue_surjective
    exact ⟨hh', hbc.corr_iff.1 fun c ↦ (LinearMap.congr_fun hhl c).symm⟩
  · intro x hx
    have hc := hbc.corr_iff.2 hx
    refine GlobalTheory.CrysFree.mem_smul_top_of_forall _ x fun c ↦ ?_
    rw [← IsLocalRing.residue_eq_zero_iff]
    exact (hc c).symm.trans (LinearMap.zero_apply _)
  · intro x h
    haveI := a.hom x
    haveI := (OAct.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ a).hom x
    refine hbc.corr_iff.1 ?_
    exact GrpMor.Corr.push (m := Published.AbelianDeRham.bcMor hh) (Published.AbelianDeRham.bcMor hh)
      (a.act x) ((OAct.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ a).act x)
      (pullback.lift_fst _ _ _).symm (hbc.corr_iff.2 rfl)

end GlobalTheory.HdRFibre
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LowChart

theorem dense_asIdeal_eq_bot_spMap (n : ℕ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [CharZero V₁]
    (b₁ : cycAway n →+* V₁) : Dense {x : Sp V₁ | (spMap b₁ x).asIdeal = ⊥} := by
  let p₀ : Sp V₁ := ⟨⊥, Ideal.isPrime_bot⟩
  let K := FractionRing V₁
  have hinj : Function.Injective (algebraMap V₁ K) := IsFractionRing.injective V₁ K
  haveI : CharZero K := charZero_of_injective_algebraMap hinj
  have hmem : p₀ ∈ {x : Sp V₁ | (spMap b₁ x).asIdeal = ⊥} := by
    let q : Sp K := ⟨⊥, Ideal.isPrime_bot⟩
    have h := GlobalTheory.AbChart.asIdeal_eq_bot_of_charZero n K (spMap ((algebraMap V₁ K).comp b₁)) q
    show Ideal.comap b₁ (⊥ : Ideal V₁) = ⊥
    have hc : Ideal.comap (algebraMap V₁ K) (⊥ : Ideal K) = ⊥ :=
      (RingHom.ker_eq_bot_iff_eq_zero _).2 fun a ha => hinj (by rw [ha, map_zero])
    rw [← hc, Ideal.comap_comap]
    exact h
  have hcl : closure ({p₀} : Set (Sp V₁)) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    exact (PrimeSpectrum.le_iff_mem_closure (R := V₁) p₀ x).1 bot_le
  refine Dense.mono (Set.singleton_subset_iff.2 hmem) ?_
  exact dense_iff_closure_eq.2 hcl

theorem exists_sFam_point : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (h : ℕ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [CharZero V₁]
    (b₁ : cycAway n →+* V₁) (s : SiegPre h n (zetaAway n) (spMap b₁)), s.Principal →
    ∃ (F : SFam h n (zetaAway n)) (x : Sp V₁ ⟶ F.X), x ≫ F.s = spMap b₁ ∧ SiegPB s F.univ x := by
  intro n hn hodd h V₁ _ _ _ b₁ s hs
  obtain ⟨F⟩ : Nonempty (SFam h n (zetaAway n)) := by
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · exact ⟨zeroFam n hn⟩
    · exact GlobalTheory.SiegelTor.exists_sFam_cycAway h n hh hn hodd
  obtain ⟨x, hx, hpb⟩ := F.rep (Sp V₁) (spMap b₁) s inferInstance (dense_asIdeal_eq_bot_spMap n V₁ b₁) hs
  exact ⟨F, x, hx, hpb⟩

end GlobalTheory.LowChart
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.abelian_locus_point_mem_range_siegelModuli_openImmersion : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) [S.IsSeparated] (j : F.X ⟶ S) [IsOpenImmersion j] (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → y ≫ j = jK R ≫ ξ → ∀ p : Sp R, p ∈ abLocus G₁ → ξ p ∈ Set.range j := by
  first | exact @GlobalTheory.AbChart.mem_range_of_mem_abLocus | exact GlobalTheory.AbChart.mem_range_of_mem_abLocus | (intros; apply GlobalTheory.AbChart.mem_range_of_mem_abLocus <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualFactor

theorem factor_of_flat {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A]
    [IsCommMonObj B] (la : A ⟶ B) [IsMonHom la] [Flat la.left] [Surjective la.left]
    [QuasiCompact la.left] (d : ℕ)
    (hk : ∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) :
    ∃ mu : B ⟶ A, IsMonHom mu ∧ la ≫ mu = 𝟙 A ^ d ∧ mu ≫ la = 𝟙 B ^ d := by
  obtain ⟨mu, hmu⟩ := GlobalTheory.AbelianQuotient.exists_desc la (𝟙 A ^ d) (by
    intro W a b h
    rw [comp_pow, comp_pow, Category.comp_id, Category.comp_id]
    have h1 : (a / b) ≫ la = 1 := by
      rw [GrpObj.div_comp, h, div_self']
    have h2 := hk W _ h1
    rwa [div_pow, div_eq_one] at h2)
  have := FlatQuotient.epi_of_flat_surjective la
  have := FlatQuotient.epi_tensorHom la la
  refine ⟨mu, ⟨?_, ?_⟩, hmu, ?_⟩
  · have e : (η[A] : 𝟙_ (Over S) ⟶ A) = 1 := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [← IsMonHom.one_hom la, Category.assoc, hmu, comp_pow, Category.comp_id, e, one_pow]
  · rw [← cancel_epi (la ⊗ₘ la), ← IsMonHom.mul_hom_assoc, hmu, tensorHom_comp_tensorHom_assoc, hmu,
      comp_pow, Category.comp_id]
    have hμ : (μ[A] : A ⊗ A ⟶ A) = fst A A * snd A A := by
      rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    rw [hμ, comp_mul, tensorHom_fst, tensorHom_snd, comp_pow, comp_pow, Category.comp_id,
      Category.comp_id, mul_pow]
  · rw [← cancel_epi la, reassoc_of% hmu, comp_pow, Category.comp_id, pow_comp, Category.id_comp]

theorem main : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → ∃ mu : B ⟶ A, IsMonHom mu ∧ la ≫ mu = 𝟙 A ^ d ∧ mu ≫ la = 𝟙 B ^ d := by
  intro S A B _ _ Q la d hA hB hAB hBA hla hd hk
  have := hA.comm
  have := hB.comm
  have := hA.proper
  have := hB.proper
  have : Surjective la.left := GlobalTheory.T.surjective_of_dual_homomorphism_kernel_killed S A B Q la d hA hB hAB hBA hla hd hk
  have : Flat la.left := GlobalTheory.T.flat_of_dual_homomorphism_kernel_killed S A B Q la d hA hB hAB hBA hla hd hk
  have : QuasiCompact la.left := by
    have : QuasiCompact (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
    exact QuasiCompact.of_comp la.left B.hom
  exact factor_of_flat A B la d hk

end GlobalTheory.DualFactor
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.potentialGoodReduction_of_divisionAlgebra_order_action : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (jj : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective jj → Submodule.span ℚ (Set.range jj) = ⊤ → g < Module.finrank ℚ B → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  first | exact @GlobalTheory.DivPotGood.potGood_of_divisionAlgebra_action | exact GlobalTheory.DivPotGood.potGood_of_divisionAlgebra_action | (intros; apply GlobalTheory.DivPotGood.potGood_of_divisionAlgebra_action <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.potentialGoodReduction_of_lieMult_zero : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (g : K →+* Ω) (σ : 𝓞 F →+* Ω), LieMult act (spMap g) σ 0 → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  first | exact @GlobalTheory.PotGoodLie.potGood_of_lieMult_zero | exact GlobalTheory.PotGoodLie.potGood_of_lieMult_zero | (intros; apply GlobalTheory.PotGoodLie.potGood_of_lieMult_zero <;> assumption)
end
