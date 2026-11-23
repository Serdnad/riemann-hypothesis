module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle010
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle021
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle022
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle087
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle006
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFinsetOfPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle043
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle105
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle164
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle163
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.UniformSpace.Uniformizable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory

theorem existsUnique_hom_extension_smConn_semiAbelian_dvr :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (H G : Over (Sp T)) [GrpObj H] [GrpObj G], SmConn H → IsSemiAbelian G → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj H ⟶ (Over.pullback (spMap (algebraMap T K))).obj G, IsMonHom f → ∃! F : H ⟶ G, IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f := by
  intro T K _ _ _ _ _ _ G G' _ _ hG hG' f hf
  obtain ⟨hcomm, hsm, hsep, hqc, hgc⟩ := hG
  have := hG'.comm
  have := hG'.smooth
  have := hG'.separated
  have := hG'.quasiCompact
  have hGflat : Flat G.hom := inferInstance
  obtain ⟨n, hn, hnT⟩ := exists_prime_isUnit_of_isLocalRing T
  let Φ := Over.pullback (spMap (algebraMap T K))
  let i : Φ.obj G ⟶ Φ.obj (G ⊗ G') := lift (𝟙 _) f ≫ Functor.LaxMonoidal.μ Φ G G'
  have hi : IsMonHom i := inferInstance
  have hi1 : i ≫ Φ.map (fst G G') = 𝟙 _ := by
    rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
  have hi2 : i ≫ Φ.map (snd G G') = f := by simp [i]
  have hs1 : IsSeparated (fst G G').left := inferInstanceAs (IsSeparated (pullback.fst G.hom G'.hom))
  have hs2 : LocallyOfFiniteType (fst G G').left :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G'.hom))
  have hs3 : QuasiCompact (fst G G').left :=
    inferInstanceAs (QuasiCompact (pullback.fst G.hom G'.hom))
  have hsP : IsSeparated (G ⊗ G').hom :=
    inferInstanceAs (IsSeparated (pullback.fst G.hom G'.hom ≫ G.hom))
  have hlP : LocallyOfFiniteType (G ⊗ G').hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G'.hom ≫ G.hom))
  have hs4 : IsSeparated (Φ.map (fst G G')).left := by
    have h1 : IsSeparated (Φ.obj (G ⊗ G')).hom :=
      inferInstanceAs (IsSeparated (pullback.snd (G ⊗ G').hom _))
    rw [← Over.w (Φ.map (fst G G'))] at h1
    exact IsSeparated.of_comp _ (Φ.obj G).hom
  have hic : IsClosedImmersion i.left := by
    have h1 : IsClosedImmersion (i.left ≫ (Φ.map (fst G G')).left) := by
      rw [← Over.comp_left, hi1, Over.id_left]; infer_instance
    exact IsClosedImmersion.of_comp i.left (Φ.map (fst G G')).left
  obtain ⟨Ga, io, e, hio, hGa, he⟩ := exists_flat_closure T K (G ⊗ G') (Φ.obj G) i hic
  obtain ⟨_, hio', -, hc⟩ := flat_closure_subgroup T K (G ⊗ G') Ga io (Φ.obj G) i e hio hGa hi he
  have := hc inferInstance
  have hp : IsMonHom (io ≫ fst G G') := inferInstance
  have hpK : Φ.map (io ≫ fst G G') = e.hom := by
    rw [Functor.map_comp, ← he, Category.assoc, hi1, Category.comp_id]
  have hpKi : IsIso (Φ.map (io ≫ fst G G')) := by rw [hpK]; infer_instance
  have hGaS : IsSeparated Ga.hom := by rw [← Over.w io]; infer_instance
  have hGaL : LocallyOfFiniteType Ga.hom := by rw [← Over.w io]; infer_instance
  have hp1 : IsSeparated (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hp2 : LocallyOfFiniteType (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hp3 : QuasiCompact (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hnt := KernelNoTorsion.eq_one_of_pow_eq_one_of_comp_eq_one T K Ga G (io ≫ fst G G') n hp hGaS
    (etale_mulN_torsion_dvr T Ga n hnT hGa hGaL).2
    (etale_mulN_torsion_dvr T G n hnT hGflat inferInstance).2 hpKi
  have hnS : IsUnit (n : Γ(Sp T, ⊤)) := by
    simpa using hnT.map (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom
  have hker := finite_geometric_kernel_of_pow_eq_one
    AbelianSubgroupFinite.finite_of_torsionFree (Sp T) G G' Ga io n hG' hio' hio hn hnS hnt
  have hqf := locallyQuasiFinite_of_finite_geometric_ker (Sp T) Ga G (io ≫ fst G G') hp hp2 hp3 hker
  have hiso := isIso_of_quasiFinite_of_isIso_genericFibre_dvr T K Ga G (io ≫ fst G G') hp hGa hp1 hp2
    hp3 hqf hsm hgc hpKi
  have hF : Φ.map (inv (io ≫ fst G G') ≫ io ≫ snd G G') = f := by
    rw [Functor.map_comp, Functor.map_inv, IsIso.inv_comp_eq, hpK, Functor.map_comp, ← he,
      Category.assoc, hi2]
  refine ⟨inv (io ≫ fst G G') ≫ io ≫ snd G G', ⟨?_, hF⟩, fun F hF' => ?_⟩
  · refine flat_dvr_generic_fibre.2.2 T K G G' _ hGflat hG'.separated ?_
    exact hF ▸ hf
  · exact flat_dvr_generic_fibre.1 T K G G' hGflat hG'.separated _ _ (hF'.2.trans hF.symm)

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem exists_isGt_specialFibre (hB : GtBaseChangeSt) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (D : DegPre V) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (g : GtCoord (IsLocalRing.maximalIdeal V) D 0 G) :
    ∃ E : SplitExt (Sp (IsLocalRing.ResidueField V)),
      E.IsGt ((Over.pullback (spMap (IsLocalRing.residue V))).obj G) := by
  obtain ⟨E₀, -, -, -, -, hE⟩ := GlobalTheory.gtCoord_isGt V (IsLocalRing.maximalIdeal V) D 0 G ⟨g⟩
  have hle : IsLocalRing.maximalIdeal V ^ (0 + 1) ≤ RingHom.ker (IsLocalRing.residue V) := by
    rw [zero_add, pow_one, IsLocalRing.ker_residue]
  let c : V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1) →+* IsLocalRing.ResidueField V :=
    Ideal.Quotient.lift _ (IsLocalRing.residue V) fun a ha => (RingHom.mem_ker).1 (hle ha)
  obtain ⟨E₁, -, -, -, -, hE₁⟩ := hB _ _ (spMap c) E₀ _ hE
  have hc : spMap c ≫ thick V (IsLocalRing.maximalIdeal V) 0 = spMap (IsLocalRing.residue V) := by
    rw [show thick V (IsLocalRing.maximalIdeal V) 0 = spMap (Ideal.Quotient.mk _) from rfl, ← spMap_comp]
    congr 1
  have gp := ((isGrpPullback_pullback (thickObj V (IsLocalRing.maximalIdeal V) 0 G) (spMap c)).comp
    (isGrpPullback_pullback G (thick V (IsLocalRing.maximalIdeal V) 0))).congr hc rfl
  obtain ⟨e, he, -⟩ := grpPullback_iso gp (isGrpPullback_pullback G (spMap (IsLocalRing.residue V)))
  exact ⟨E₁, isGt_of_iso e hE₁⟩

theorem utest_dim_and_split : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), u.A.g = S.g ∧ u.D.toPre.P.g + Module.finrank ℤ u.D.toPre.X = S.g ∧ SmoothOfRelativeDimension S.g u.G.hom ∧ 4 ≤ S.N ∧ ∃ E : SplitExt (Sp (IsLocalRing.ResidueField u.V)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue u.V))).obj u.G) := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u
  have : CharZero u.V :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  have hA : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hsm : SmoothOfRelativeDimension S.g u.A.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback u.cart.1 (ρ.g_eq ▸ ρ.P.smoothDim)
  have hg : u.A.g = S.g :=
    H1.dim_unique u.A.A.hom u.A.smoothDim hsm (eSec u.A.A (IsLocalRing.closedPoint (FractionRing u.V)))
  refine ⟨hg, ?_, ?_, ?_, exists_isGt_specialFibre hL.2.2.1.gtBaseChange _ _ (u.U.gt 0)⟩
  · have h := GlobalTheory.UT.dim_eq_rank_add_dim hL u.V _ hA u.D u.A u.G u.semi u.U
    rw [← hg, add_comm]
    exact h.symm
  · have := u.semi.smooth
    have := u.semi.geomConnected
    refine GlobalTheory.GenericDim.smoothOfRelativeDimension_of_generic u.V u.G S.g ?_
    have w : u.U.gen.hom.left ≫ u.A.A.hom = pullback.snd u.G.hom (jK u.V) := Over.w u.U.gen.hom
    have : IsIso u.U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map u.U.gen.hom))
    exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_horiz_isIso (g := 𝟙 _) ⟨w.trans (Category.comp_id _).symm⟩) hsm
  · rw [ρ.N_eq]
    have h₁ : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    exact Nat.pow_le_pow_left h₁ 2

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.SeriesConv

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.UT.CoefVal

theorem summable_coef : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 1 ≤ k → ∀ (s : Fam u.D.toPre (PadicAlgCl p) k) (g : GtPtF u.D.toPre (PadicAlgCl p)) (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b), w.IsGen → Summable (fun χ => GlobalTheory.UT.coef s g w χ) ∧ Filter.Tendsto (fun χ => GlobalTheory.UT.coef s g w χ) Filter.cofinite (nhds 0) ∧ ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ ∀ χ, GlobalTheory.UT.coef s g w χ ∈ K := by
  intro hLL o Ω _ _ _ _ S ρ p _ y₀ u _ k hk s g w hw
  have hTW : TwistBCSpanStatement := twistBCSpan_of (GlobalTheory.twistBaseChange_of_finrank_sections_one fun K _ _ P =>
    (hLL.1.globalSectionsRank K P 1 le_rfl).trans (one_pow _))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  choose Q hQ using DVR.QForm.exists_QVal hϖ u.D
  have h0 := PsiForm.norm_pos_of_irreducible (F := PadicAlgCl p) hϖ
  have h1 := PsiForm.norm_lt_one_of_irreducible u.norm_le hϖ
  obtain ⟨v, hvn⟩ := PadicVal.exists_addValuation _ h0 h1
  have hv : ValOver ϖ (PadicAlgCl p) v := fun c n hc => by
    have e := PsiForm.norm_of_hasVal u.norm_le hϖ hc
    obtain ⟨q, hq, hq'⟩ := hvn (algebraMap _ _ c) (norm_pos_iff.1 (by rw [e]; exact Real.exp_pos _))
    rw [e, Real.log_exp, neg_mul, neg_neg, mul_comm, mul_left_inj' (Real.log_neg h0 h1).ne] at hq'
    have : q = n := by exact_mod_cast hq'.symm
    rw [hq, this]
  have ht : Filter.Tendsto (fun χ => coef s g w χ) Filter.cofinite (nhds 0) := by
    refine PadicVal.tendsto_of_null h0 h1 hvn fun q => ?_
    obtain ⟨l, hl, -⟩ := exists_gtV (hϖ := hϖ) (hv := hv) g
    obtain ⟨ω, hω⟩ := exists_genV_frm (hϖ := hϖ) (hv := hv) hw
    obtain ⟨r, hr⟩ := exists_nuGe hϖ hv hTW hQ hk s
    refine (finite_sublevel hϖ hQ hk l (q - r - ω)).subset fun χ hχ => ?_
    have h : r + (Q χ : ℚ) / k + l χ + ω < q :=
      WithTop.coe_lt_coe.1 ((le_v_coef hw (hr χ) (hl χ) hω).trans_lt hχ)
    show (Q χ : ℚ) / k + l χ ≤ q - r - ω
    linarith
  obtain ⟨T, hT⟩ := CoefField.exists_finset hLL.1.globalFns hk s g hw fun α => by
    obtain ⟨r, n, a, σ, σF, hσ, -, hsum⟩ := exists_vge hϖ hv hTW hk (s.s α)
    exact ⟨n, a, σ, σF, hσ, hsum⟩
  obtain ⟨-, -, -, K₀, hK₀, hK⟩ := GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ u
  have : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (T : Set (PadicAlgCl p))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hm : ∀ χ, coef s g w χ ∈ K₀ ⊔ IntermediateField.adjoin ℚ_[p] (T : Set (PadicAlgCl p)) :=
    hT (K₀ ⊔ IntermediateField.adjoin ℚ_[p] (T : Set (PadicAlgCl p))).toSubfield
      (fun a => (le_sup_left : K₀ ≤ _) (show _ ∈ (K₀ : Set (PadicAlgCl p)) from hK ▸ ⟨a, rfl⟩))
      (fun t h => (le_sup_right : _ ≤ K₀ ⊔ _) (IntermediateField.subset_adjoin _ _ h))
  exact ⟨PadicVal.summable_of_mem _ hm ht, ht, _, inferInstance, hm⟩

end GlobalTheory.ZH.SeriesConv
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.SeriesProd

theorem hasSum_of_sumI {R F Ix : Type} [CommRing R] [NormedField F] (φ : R →+* F)
    (h1 : ∀ a, ‖φ a‖ ≤ 1) (I : Ideal R) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (ϖ : R) (hI : I = Ideal.span {ϖ})
    (hϖ : ‖φ ϖ‖ ≤ r) [Module R F] (hs : ∀ (a : R) (x : F), a • x = φ a * x) {x : Ix → F} {s : F}
    (h : GlobalTheory.UT.SumI I x s) : HasSum x s := by
  obtain ⟨N, hN, -, -, h⟩ := h
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ y ∈ N, ‖y‖ ≤ C := by
    obtain ⟨T, rfl⟩ := hN
    refine ⟨∑ t ∈ T, ‖t‖, fun y hy => ?_⟩
    obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hy
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    rw [hs, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (h1 _)
  have hb : ∀ (n : ℕ) y, y ∈ I ^ n • N → ‖y‖ ≤ r ^ n * C := by
    intro n y hy
    rw [hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [hs, norm_mul, map_pow, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hϖ n) (hC z hz) (norm_nonneg _) (pow_nonneg hr0 n)
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have ht : Filter.Tendsto (fun n : ℕ => r ^ n * C) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).mul_const C
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  obtain ⟨S, hS⟩ := h n
  refine ⟨S, fun T hT => ?_⟩
  rw [dist_comm, dist_eq_norm]
  exact (hb n _ (hS T hT)).trans_lt hn

theorem hasSum_conv {F X : Type} [NormedField F] [IsUltrametricDist F] [AddCommGroup X] {a b c : X → F} {x y : F}
    (ha : HasSum a x) (hb : HasSum b y) (hc : ∀ α, HasSum (fun χ => a χ * b (α - χ)) (c α)) :
    HasSum c (x * y) := by
  have : NonarchimedeanRing F :=
    { is_nonarchimedean := (IsUltrametricDist.nonarchimedeanAddGroup (M := F)).is_nonarchimedean }
  let e : X × X ≃ X × X :=
    { toFun := fun q => (q.2, q.1 - q.2)
      invFun := fun q => (q.1 + q.2, q.1)
      left_inv := fun q => by simp
      right_inv := fun q => by simp }
  exact ((e.hasSum_iff.2 (ha.mul_of_nonarchimedean hb))).prod_fiberwise hc

open GlobalTheory.FieldBaseChange GlobalTheory.UT

theorem mul_back {Y Y' X₁ X₂ Z₁ : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} {m : Y' ⟶ Y} {k k' : ℕ} {g₁ : Z₁ ⟶ X₁} {h₁ : Y' ⟶ Z₁}
    (hL₂ : L₂.IsLB) (n : Z₁ ⟶ Y') (hn : n ≫ h₁ = 𝟙 _) {a a' a'' b b' b''}
    (h : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a (m ≫ f₂) (𝟙 _) b)
    (h' : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k' g₁ h₁ a' (m ≫ f₂) (𝟙 _) b')
    (h'' : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m (k + k') g₁ h₁ a'' (m ≫ f₂) (𝟙 _) b'')
    (hb : ∀ j, (show Γ(Y', LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) j) from b''.f j) =
      (show Γ(Y', LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) j) from b.f j) *
        (show Γ(Y', LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) j) from b'.f j))
    (y : Z₁) (i : L₁.ι) (hi : g₁ y ∈ L₁.U i) :
    powVal a'' (𝟙 _) y i = powVal a (𝟙 _) y i * powVal a' (𝟙 _) y i := by
  have e₃ : g₁ = (n ≫ m) ≫ f₁ := by rw [Category.assoc, ← h.1, ← Category.assoc, hn, Category.id_comp]
  obtain ⟨i₂, a₂⟩ := exists_chart hL₂ (f₂ (m (n y)))
  have a₁ : f₁ (m (n y)) ∈ L₁.U i := by rw [e₃] at hi; exact hi
  have v := (isoRelM_iff w m k h₁ h.1 _ h.2.1 a b).1 h _ n y i₂ i a₂ a₁
  have v' := (isoRelM_iff w m k' h₁ h.1 _ h.2.1 a' b').1 h' _ n y i₂ i a₂ a₁
  have v'' := (isoRelM_iff w m (k + k') h₁ h.1 _ h.2.1 a'' b'').1 h'' _ n y i₂ i a₂ a₁
  have e : powVal b'' (n ≫ 𝟙 _) y i₂ = powVal b (n ≫ 𝟙 _) y i₂ * powVal b' (n ≫ 𝟙 _) y i₂ := by
    rw [Category.comp_id]
    exact (congrArg (gs n y _) (hb fun _ => i₂)).trans (gs_mul n y _ (mem_wchart.2 fun _ => a₂) _ _)
  rw [v, v', v'', hn, zpow_natCast, zpow_natCast, zpow_natCast, pow_add, _root_.mul_mul_mul_comm,
    ← Units.val_mul] at e
  exact (Units.mul_right_inj _).1 e

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_frm_mul {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k k' : ℕ}
    {b : TF (R := R) F ⟶ D.P.A} {w : Frm D F k b} {w' : Frm D F k' b} (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ w'' : Frm D F (k + k') b, w''.IsGen ∧
      ∀ z J, Good D.P.L z J → val w'' (𝟙 _) z J = val w (𝟙 _) z J * val w' (𝟙 _) z J := by
  obtain ⟨w'', h, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε (k + k'))
    (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [CoefBasic.prod_line, CoefBasic.prod_line, CoefBasic.prod_line, pow_add, pow_add, mul_inv,
        _root_.mul_mul_mul_comm])
    (LB.mulGen D.P.L _ _ _ _ w w') (DVR.mulGen_isGen _ _ _ _ _ _ _ hw hw')
  exact ⟨w'', h, fun z J hJ => (hv _ _ z J hJ).trans (val_mul hJ _ _ _)⟩

theorem exists_back {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
    (F : Type) [Field F] [Algebra (FractionRing R) F] {w : W0 U} (hw : w.IsGen) {k k' : ℕ}
    {σ : U.SecGF F k} {σ' : U.SecGF F k'} {σ'' : U.SecGF F (k + k')} {s s' s''}
    (h : U.ExpandsG F k σ s) (h' : U.ExpandsG F k' σ' s') (h'' : U.ExpandsG F (k + k') σ'' s'')
    (hb : ∀ j, (show Γ((UnifPre.GF (G := G) F).left, LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) j)
        from σ''.f j) =
      (show Γ((UnifPre.GF (G := G) F).left, LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) j) from σ.f j) *
      (show Γ((UnifPre.GF (G := G) F).left, LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) j) from σ'.f j)) :
    ∃ (t : SecA A F k) (t' : SecA A F k') (t'' : SecA A F (k + k')), U.ExpandsF F k w t s ∧ U.ExpandsF F k' w t' s' ∧
      U.ExpandsF F (k + k') w t'' s'' ∧
      ∀ z J, Good A.L z J → sA t'' (𝟙 _) z J = sA t (𝟙 _) z J * sA t' (𝟙 _) z J := by
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n ≫ U.genF F = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have hn' : U.genF F ≫ n = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have i₂ := fun k => (isoRelM_bijective (k := k) (m := (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left)
    (g₁ := (snd (TFK (R := R) F) A.A).left) (h₁ := (U.genF F).left) A.isLB U.LG.isLB hw
    (congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)) n.left
    (congrArg (fun q => q.left) hn) (congrArg (fun q => q.left) hn')).2
  obtain ⟨t, ht⟩ := (i₂ k σ).exists
  obtain ⟨t', ht'⟩ := (i₂ k' σ').exists
  obtain ⟨t'', ht''⟩ := (i₂ (k + k') σ'').exists
  exact ⟨t, t', t'', ⟨σ, ht, h⟩, ⟨σ', ht', h'⟩, ⟨σ'', ht'', h''⟩, fun z J hJ =>
    mul_back U.LG.isLB n.left (congrArg (fun q => q.left) hn) ht ht' ht'' hb z _ (hJ (𝟙 _ ≫ _))⟩

theorem main : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k k' : ℕ) (g : GtPtF u.D.toPre (PadicAlgCl p)) (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b) (w' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k' g.b) (w'' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) (k + k') g.b), 1 ≤ k → 1 ≤ k' → w.IsGen → w'.IsGen → w''.IsGen → ∃ κ : PadicAlgCl p, κ ≠ 0 ∧ ∀ (σ : u.U.toUnifPre.SecGF (PadicAlgCl p) k) (σ' : u.U.toUnifPre.SecGF (PadicAlgCl p) k') (σ'' : u.U.toUnifPre.SecGF (PadicAlgCl p) (k + k')) s s' s'', u.U.toUnifPre.ExpandsG (PadicAlgCl p) k σ s → u.U.toUnifPre.ExpandsG (PadicAlgCl p) k' σ' s' → u.U.toUnifPre.ExpandsG (PadicAlgCl p) (k + k') σ'' s'' → (∀ j, (show Γ((UnifPre.GF (G := u.G) (PadicAlgCl p)).left, (LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => ((k : ℕ) : ℤ))).U j) from σ''.f j) = σ.f j * (show Γ((UnifPre.GF (G := u.G) (PadicAlgCl p)).left, (LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => ((k : ℕ) : ℤ))).U j) from σ'.f j)) → ∀ x x', HasSum (fun χ => GlobalTheory.UT.coef s g w χ) x → HasSum (fun χ => GlobalTheory.UT.coef s' g w' χ) x' → HasSum (fun χ => GlobalTheory.UT.coef s'' g w'' χ) (κ * x * x') := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u l k k' g w w' w'' hk hk' hw hw' hw''
  obtain ⟨w₃, hw₃, hv⟩ := exists_frm_mul hw hw'
  obtain ⟨c, hc, -, hcoef⟩ :=
    ((CoefBasic.coef_basic _ u.D.toPre (PadicAlgCl p) (k + k') g).2.2 w₃ hw₃).2.2.1 w'' hw''
  refine ⟨c, hc, fun σ σ' σ'' s s' s'' h h' h'' hb x x' hx hx' => ?_⟩
  obtain ⟨w₀, hw₀⟩ := u.U.ext
  obtain ⟨t, t', t'', e, e', e'', hm⟩ := exists_back u.U.toUnifPre (PadicAlgCl p) hw₀ h h' h'' hb
  let φ : u.V →+* PadicAlgCl p :=
    (algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))
  have : CharZero u.V := φ.charZero
  have hadm : AdmBase u.V (IsLocalRing.maximalIdeal u.V) :=
    ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hS := GlobalTheory.T.product_of_sections_expands_to_convolution hL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) w₀ hw₀ k k' (k + k') hk hk' rfl
    t t' t'' s s' s'' e e' e'' hm g w w' w₃ hw hw' hw₃ hv
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  have h1 : ∀ a, ‖φ a‖ ≤ 1 := fun a => (u.norm_le _).2 ⟨a, rfl⟩
  have hlt : ‖φ ϖ‖ < 1 := lt_of_le_of_ne (h1 ϖ) fun e1 => by
    obtain ⟨z, hz⟩ := (u.norm_le (algebraMap u.V (FractionRing u.V) ϖ)⁻¹).1 (by
      rw [map_inv₀, norm_inv]
      exact (congrArg (·⁻¹) e1).le.trans inv_one.le)
    have h0 : algebraMap u.V (FractionRing u.V) ϖ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective u.V (FractionRing u.V))).2 hϖ.ne_zero
    refine hϖ.not_isUnit (IsUnit.of_mul_eq_one z (IsFractionRing.injective u.V (FractionRing u.V) ?_))
    rw [map_mul, hz, map_one, mul_inv_cancel₀ h0]
  have hsum := hasSum_conv hx hx' fun α =>
    letI : Module u.V (PadicAlgCl p) := Module.compHom _ (algebraMap u.V (FractionRing u.V))
    hasSum_of_sumI φ h1 _ (norm_nonneg _) hlt ϖ hϖ.maximalIdeal_eq le_rfl
      (fun a x => Algebra.smul_def (algebraMap u.V (FractionRing u.V) a) x) (hS α)
  simp only [hcoef, _root_.mul_assoc]
  exact hsum.mul_left c

end GlobalTheory.ZH.SeriesProd
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.crd_ne_zero_injective_surjective_of_basis : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 4 ≤ k → ∀ (J : Type) [Fintype J] (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f → (∀ (a : u.PtC) w, Crd (u.H k) σ (u.toG a) w → w ≠ 0) ∧ (∀ (a a' : u.PtC) w, Crd (u.H k) σ (u.toG a) w → Crd (u.H k) σ (u.toG a') w → a = a') ∧ ∀ a : Sp (PadicAlgCl p) ⟶ u.G.left, a ≫ u.G.hom = gPt p ≫ spMap u.j → ∃ a' : u.PtC, u.toG a' = a := by
  first | exact @GlobalTheory.ZH.AdaptedSep.basis_separates | exact GlobalTheory.ZH.AdaptedSep.basis_separates | (intros; apply GlobalTheory.ZH.AdaptedSep.basis_separates <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.polarizedAbelian_valueTable_maps_under_baseChange : LL → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CharZero R] [CommRing R'] [IsDomain R'] (gam : FractionRing R →+* FractionRing R') (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing R'))) (ψ : A'.A.left ⟶ A.A.left) (ω : LB.Iso A'.L (A.L.pull ψ)) ρ ρ', RigPull A'.A A.A (spMap gam) ψ ω ρ' ρ → ∀ (F F' : Type) [Field F] [Field F'] [IsAlgClosed F] [IsAlgClosed F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F'] (σ : F →+* F'), (∀ x, σ (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R') F' (gam x)) → ∀ (m r : ℕ) (th : SecA A F 1) (th' : SecA A' F' 1) (τ : Fin r → SecA A F (m ^ 2)) (τ' : Fin r → SecA A' F' (m ^ 2)), Thru ω 1 (T' := TFK (R := R') F') (T := TFK (R := R) F) (spMap σ) th th' → (∀ i, Thru ω (m ^ 2) (T' := TFK (R := R') F') (T := TFK (R := R) F) (spMap σ) (τ i) (τ' i)) → Tab.Map σ (tab ρ m th τ) (tab ρ' m th' τ') := by
  first | exact @GlobalTheory.OneBasis.TabMap.tab_map | exact GlobalTheory.OneBasis.TabMap.tab_map | (intros; apply GlobalTheory.OneBasis.TabMap.tab_map <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

theorem _root_.GlobalTheory.T.twistedLabels_match_of_level_ge_four : GlobalTheory.UT.LL → EVSt → BrGtSt → AllS fun {_} _ _ _ {_} {_} {_} {_} {_} _ {_} {_} _ _ {_} _ {_} _ _ A u r {o} M _ {_} ν' J => M.P.TorsionIso → Realises o A.arc A.be u r → ∀ n : ℕ, Odd n → 3 ≤ n → Labels A u r M ν' J (n ^ 2) → ∀ k, 4 ≤ k → Labels A u r M ν' J k := by
  first | exact @GlobalTheory.Ex.Trait.LevelFour.labels_of_four_le | exact GlobalTheory.Ex.Trait.LevelFour.labels_of_four_le | (intros; apply GlobalTheory.Ex.Trait.LevelFour.labels_of_four_le <;> assumption)
end
