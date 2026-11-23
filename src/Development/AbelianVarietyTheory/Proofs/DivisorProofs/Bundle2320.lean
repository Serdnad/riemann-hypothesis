module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeE
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle027
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFramesDifferByUnit
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedComplexFibreMarkedLatticeClass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralInIntegralEigenbasis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Discrepancy GlobalTheory.Cartier GlobalTheory.QCoh

set_option autoImplicit false
noncomputable section
open GlobalTheory.Adelic.LinSys
namespace GlobalTheory.BoundaryFibre

theorem eff_nsmul {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} (h : D.Eff) (n : ℕ) :
    (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

end GlobalTheory.BoundaryFibre
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

open GlobalTheory.LamT (CMPt)
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM fullB tv)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LamT.TanRel

open MonoidalCategory CartesianMonoidalCategory GlobalTheory.Frames GlobalTheory.LamT GlobalTheory.IntLie GlobalTheory.LamT.LetterInt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem tvOf_congr {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {v v' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (h : v = v') (hv : IsTanAt x v) (hv' : IsTanAt x v') :
    ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf hv = ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf hv' := by
  subst h; rfl

theorem bc_tan {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (hx : x' = spMap ψ ≫ x) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}
    (hπ : IsGrpPullback A Xo.univ.t.G x π) (w : epsR S ⟶ A) (ht : IsTangent w) :
    IsTanAt x' (spMap (dualMap ψ) ≫ w.left ≫ π) := by
  subst hx
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.tan_bc ψ ((GlobalTheory.KSExist.FrameLift.tan_iff hπ w).2 ht)

theorem bc_comb {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (hx : x' = spMap ψ ≫ x) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}
    (hπ : IsGrpPullback A Xo.univ.t.G x π) {n : ℕ} (v : Fin n → (epsR S ⟶ A))
    (hvt : ∀ k, IsTanAt x' (spMap (dualMap ψ) ≫ (v k).left ≫ π)) (cf : Fin n → S) (w : epsR S ⟶ A)
    (h : IsLieComb cf v w) (hw : IsTanAt x' (spMap (dualMap ψ) ≫ w.left ≫ π)) :
    ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf hw = ∑ k, ψ (cf k) • ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf (hvt k) :=
  (ReciprocityTheory.ChartRestriction.G.PullbackSections.combAt_iff _ hvt _ hw).1
    (GlobalTheory.Frames.ChgBC.isCombAt_pull ψ hx (fun _ => rfl) rfl (GlobalTheory.LieBasisRing.isCombAt_of_isLieComb hπ v cf w h))

end GlobalTheory.LamT.TanRel

namespace GlobalTheory.LamT.TanRel

open MonoidalCategory CartesianMonoidalCategory GlobalTheory.Frames GlobalTheory.LamT GlobalTheory.IntLie GlobalTheory.LamT.LetterInt



theorem tangent_letter_model_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : GlobalTheory.LamT.LocMod z T iK),
    (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) →
    ∀ A : Matrix (Fin z.Φ.T.g) (Fin z.Φ.T.g) z.K, GlobalTheory.LamF.IsModelAt z.B.pol z.Φ.key z.m'.φ p A →
    letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
    ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr)
      (g : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr) (a : T.Fr),
      φ.toRingHom = iK → FrMap φ z.y yT → GlobalTheory.Frames.FrChg g a yT y' → (∀ b, IsUnit (g b).det) →
      GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u →
      ∃ (nu mu : Fin z.Φ.T.g → TanM yT.x Xo.univ.t.G) (C : (Σ b : E →+* ℂ, Fin (Dw.mult b)) → Fin z.Φ.T.g → T.Fr),
        (∀ σ k, C σ k ∈ Set.range (algebraMap T.V T.Fr)) ∧
        (∀ σ, fullB yT σ = ∑ k, iK (z.U (z.e σ) k) • nu k) ∧
        (∀ k, mu k = ∑ l, iK (A k l) • nu l) ∧
        ∀ b i, ∑ j, g b i j • fullB yT ⟨b, j⟩ = ∑ k, C ⟨b, i⟩ k • mu k := by
  intro E _ _ _ H Dw l Xo c _ z f La hz p T iK M hval A hA
  letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
  intro φ yT y' g a hφ hmap hchg hg hint
  obtain ⟨-, hlet, -, hx, -, hu⟩ := hz
  obtain ⟨vV, hvV, hvw⟩ := GlobalTheory.T.exists_lieBasis_local_model E H Dw l Xo c z p T iK M hval A hA
  choose wK hwK hwV using hvw
  have hxT : yT.x = spMap iK ≫ z.x := by rw [hmap.1, hφ, hx]
  have hK := LieComb.lieComb_algebra z.K z.Φ.T.t.G _ z.Φ.v z.Φ.basis.1
  have tv0 : ∀ w : epsR z.K ⟶ z.Φ.T.t.G, IsTangent w →
      IsTanAt yT.x (spMap (dualMap iK) ≫ w.left ≫ z.Φ.m.φ) := fun w ht =>
    bc_tan iK hxT z.Φ.m.cart w ht
  have hvt : ∀ k, IsTanAt yT.x (spMap (dualMap iK) ≫ (z.Φ.v k).left ≫ z.Φ.m.φ) := fun k =>
    tv0 (z.Φ.v k) (z.Φ.basis.1 k)
  have key : ∀ (cf : Fin z.Φ.T.g → z.K) (w : epsR z.K ⟶ z.Φ.T.t.G), IsLieComb cf z.Φ.v w →
      ∀ hw : IsTanAt yT.x (spMap (dualMap iK) ≫ w.left ≫ z.Φ.m.φ),
      ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf hw = ∑ k, iK (cf k) • ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf (hvt k) :=
    fun cf w h hw => bc_comb iK hxT z.Φ.m.cart z.Φ.v hvt cf w h hw
  have hmt : ∀ k, IsTanAt yT.x (spMap (dualMap iK) ≫ (wK k).left ≫ z.Φ.m.φ) := fun k =>
    tv0 (wK k) (hK.2.1 _ _ (hwK k))

  obtain ⟨ub, hubt, -, -, hl⟩ := hint
  choose u' hu1 hu2 using hl
  let ubR : ∀ b i, epsR T.V ⟶ M.G.t.G := fun b i => Over.homMk (ub b i).left (Over.w (ub b i))
  have hubR : ∀ b i, IsTangent (ubR b i) := fun b i => by
    have h := hubt b i
    unfold IsTan at h
    unfold IsTangent
    refine h.trans ?_
    have e : (1 : ptOver T.V T.V ⟶ M.G.t.G) = toUnit _ ≫ η[M.G.t.G] := rfl
    rw [e, Over.comp_left]
    have e2 : (toUnit (ptOver T.V T.V)).left = 𝟙 (Sp T.V) := by
      have := Over.w (toUnit (ptOver T.V T.V))
      exact ((Category.comp_id _).symm.trans this).trans (Spec.map_id _)
    rw [e2]
    exact Category.id_comp _
  choose C' hC' using fun b i => (hvV.2 (ubR b i) (hubR b i)).exists

  have hsq : ∀ k, (spMap (dualMap iK) ≫ (wK k).left) ≫ z.Φ.T.t.G.hom =
      spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap iK := fun k => by
    rw [Category.assoc, Over.w (wK k)]
    exact (spMap_comp₂ _ _).trans ((congrArg spMap (IntLie.dualMap_alg iK)).trans (spMap_comp₂ _ _).symm)
  let s' : Fin z.Φ.T.g → (Sp (DualNumber T.Fr) ⟶ M.t'.t.G.left) := fun k => M.n'.cart.1.lift _ _ (hsq k)
  have hs1 : ∀ k, s' k ≫ M.n'.φ = spMap (dualMap iK) ≫ (wK k).left := fun k => M.n'.cart.1.lift_fst _ _ _
  have hs2 : ∀ k, s' k ≫ M.t'.t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := fun k =>
    M.n'.cart.1.lift_snd _ _ _
  let vV' : Fin z.Φ.T.g → (epsOver T.V T.V ⟶ M.G.t.G) := fun k => Over.homMk (vV k).left (Over.w (vV k))
  have hm2 : ∀ k, s' k ≫ M.m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (vV' k).left := fun k => by
    apply M.n.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc]
      refine Eq.trans ?_ (hwV k).symm
      exact (congrArg (s' k ≫ ·) M.h2).trans (by rw [reassoc_of% (hs1 k)])
    · rw [Category.assoc, M.m2.cart.1.w, reassoc_of% (hs2 k), Category.assoc, Over.w (vV' k)]
      exact (spMap_comp₂ _ _).trans ((congrArg spMap (IntLie.dualMap_alg _).symm).trans (spMap_comp₂ _ _).symm)
  have hm1 : ∀ k, s' k ≫ M.m1.φ = spMap (dualMap iK) ≫ (wK k).left ≫ z.Φ.m.φ := fun k => by
    rw [M.h1, reassoc_of% (hs1 k)]
  have hcomb : ∀ b i, IsComb vV' (C' b i) (ub b i) := fun b i => by
    obtain ⟨u, hu, he⟩ := hC' b i
    refine ⟨fun k => Over.homMk (u k).left (Over.w (u k)), fun k => hu k, ?_⟩
    exact he
  have hy't : ∀ b i, IsTanAt yT.x (y'.u b i) := fun b i => by
    rw [← hchg.1]; exact y'.tan b i
  have hgen : ∀ b i, IsCombAt yT.x (fun k => spMap (dualMap iK) ≫ (wK k).left ≫ z.Φ.m.φ)
      (fun k => algebraMap T.V T.Fr (C' b i k)) (y'.u b i) := fun b i => by
    have h := comb_generic M.m1 M.m2 vV' s' hm2 (ub b i) (u' b i) (hu2 b i) (C' b i) (hcomb b i)
    rw [hu1 b i] at h
    simp only [hm1] at h
    rw [hxT]
    exact h
  refine ⟨fun k => ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf (hvt k), fun k => ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf (hmt k),
    fun σ k => algebraMap T.V T.Fr (C' σ.1 σ.2 k), fun σ k => ⟨_, rfl⟩, ?_, fun k => key _ _ (hwK k) _, ?_⟩
  · rintro ⟨b, j⟩
    obtain ⟨w, hw, hwu⟩ := hu b j
    obtain ⟨w₀, hw₀, hU⟩ := hlet.2.2.1 (z.e ⟨b, j⟩)
    obtain rfl : w₀ = w := by
      refine Over.OverMorphism.ext (z.m'.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
      unfold LamF.LamLetters.IsLetter at hw hw₀
      generalize z.letters.src (z.e ⟨b, j⟩) = s at hw hw₀
      rcases s with q | q
      · exact hw₀.trans hw.symm
      · exact hw₀.trans hw.symm
    have hyu : yT.u b j = spMap (dualMap iK) ≫ w₀.left ≫ z.Φ.m.φ := by
      rw [hmap.2.1 b j, hφ, hwu]
    show ReciprocityTheory.ChartRestriction.G.PullbackSections.tvOf (yT.tan b j) = _
    rw [tvOf_congr hyu (yT.tan b j) (tv0 w₀ (hK.2.1 _ _ hU))]
    exact key _ _ hU _
  · intro b i
    have h5 := (ReciprocityTheory.ChartRestriction.G.PullbackSections.combAt_iff (yT.u b) (yT.tan b) (g b i) (hy't b i)).1 (hchg.2.1 b i)
    have h4 := (ReciprocityTheory.ChartRestriction.G.PullbackSections.combAt_iff _ hmt _ (hy't b i)).1 (hgen b i)
    exact h5.symm.trans h4

end GlobalTheory.LamT.TanRel
end
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.ShortDet

theorem le_choose {f r p q : ℕ} (hf : 8 ≤ f) (hr : 100 ≤ r) (hp : 1 ≤ p) (hq : 1 ≤ q) (h : p + q = r) :
    8 * f * r + 10 ≤ (f * p * q + 1).choose 2 := by
  have h1 : r ≤ p * q + 1 := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hp
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hq
    nlinarith [Nat.zero_le (a * b)]
  rw [Nat.choose_two_right, Nat.add_sub_cancel, mul_assoc f, mul_assoc 8, Nat.le_div_iff_mul_le two_pos]
  generalize p * q = s at h1
  have h2 : f * r ≤ 2 * (f * s) := by
    rw [mul_left_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have h3 : 8 * 99 ≤ f * s := Nat.mul_le_mul hf (by omega)
  generalize f * s = N at h2 h3
  nlinarith

section Weight

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

theorem antitone_smul_hodgeWt {s : ℤ} (hs : 0 ≤ s) (τ : Psi H) : Antitone ((s • hodgeWt Dw) τ) := fun i j h => by
  have : (i : ℕ) ≤ j := h
  simp only [hodgeWt, CompHt.barWt, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> omega

theorem gap_smul_hodgeWt (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) (s : ℤ) (τ : Psi H) : gap ((s • hodgeWt Dw) τ) (Dw.p - 1) = s := by
  have h : Dw.p - 1 + 1 < Dw.p + Dw.q := by omega
  simp only [gap, dif_pos h, hodgeWt, CompHt.barWt, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> omega

theorem size_smul_hodgeWt {s : ℤ} (hs : 0 ≤ s) :
    ∑ τ, ∑ k, |((s • hodgeWt Dw) τ k : ℝ)| ≤ Module.finrank ℚ E * ((Dw.p + Dw.q : ℕ) * s) := by
  have h0 : (0 : ℝ) ≤ s := by exact_mod_cast hs
  refine (Finset.sum_le_card_nsmul _ _ (((Dw.p + Dw.q : ℕ) : ℝ) * s) fun τ _ => ?_).trans ?_
  · refine (Finset.sum_le_card_nsmul _ _ (s : ℝ) fun k _ => ?_).trans (by simp)
    simp only [hodgeWt, CompHt.barWt, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp [h0, abs_of_nonneg h0]
  · rw [nsmul_eq_mul, ← NumberField.Embeddings.card E ℂ]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Fintype.card_subtype_le _) (by positivity)

end Weight


end GlobalTheory.ShortDet
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp

def ratField {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} (S : Set (H0 p B O))
    (y : Y) (hy : y ∈ O) : Subfield (Y.residueField y) :=
  Subfield.closure {r | ∃ (i : B.ι) (hi : y ∈ B.U i) (s s' : H0 p B O), s ∈ S ∧ s' ∈ S ∧
    r = (Y.residue y).hom (germ i y hy hi s) / (Y.residue y).hom (germ i y hy hi s')}

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def RatGen {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw) : Prop :=
  ∃ (η : Y₀ X Z) (hη : η ∈ U₀ X Z), IsGenericPoint η Set.univ ∧
    ratField (Set.range (cuspSec X Z U la)) η hη = ⊤

end GlobalTheory.HSApp
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp


namespace GlobalTheory.WtMatchArithBar

theorem exists_shift {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (f : Fin (p + q) → ℤ) (hf : Antitone f)
    (hg0 : 1 ≤ GlobalTheory.CompHS.gap f (p - 1))
    (N M k : ℕ) (hN : 0 < N) (hk : 2 * M + N ≤ k + 1) :
    ∃ w : ℤ, (∀ i : Fin (p + q), (i : ℕ) < p → 0 ≤ ((k : ℤ) + 1) * f i + N * w - M) ∧
      (∀ i : Fin (p + q), p ≤ (i : ℕ) → 0 ≤ -(((k : ℤ) + 1) * f i) - N * w - M) := by
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hk0 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
  have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
  set X : ℤ := ((k : ℤ) + 1) * f ⟨p - 1, by omega⟩ - M with hX
  refine ⟨-(X / N), fun i hi => ?_, fun i hi => ?_⟩
  · have h1 : f i ≥ f ⟨p - 1, by omega⟩ := hf (by simp [Fin.le_def]; omega)
    have h2 : ((k : ℤ) + 1) * f ⟨p - 1, by omega⟩ ≤ ((k : ℤ) + 1) * f i := mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 := Int.emod_nonneg X (by omega : (N : ℤ) ≠ 0)
    have h4 := Int.emod_add_mul_ediv X (N : ℤ)
    linarith
  · have h1 : f i ≤ f ⟨p, by omega⟩ := hf (by simp [Fin.le_def]; omega)
    have hg := hg0
    unfold GlobalTheory.CompHS.gap at hg
    rw [dite_eq_left (by omega)] at hg
    have e : (⟨p - 1 + 1, by omega⟩ : Fin (p + q)) = ⟨p, by omega⟩ := Fin.ext (by simp; omega)
    rw [e] at hg
    have h2 : ((k : ℤ) + 1) * f i ≤ ((k : ℤ) + 1) * (f ⟨p - 1, by omega⟩ - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h3 := Int.emod_lt_of_pos X (by omega : (0 : ℤ) < N)
    have h4 := Int.emod_add_mul_ediv X (N : ℤ)
    have hk' : (2 * M + N : ℤ) ≤ k + 1 := by exact_mod_cast hk
    nlinarith


open GlobalTheory.AllWt in
theorem exists_dom_exponents_bar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw), 1 ≤ Dw.p → 1 ≤ Dw.q → (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ GlobalTheory.CompHS.gap (la τ) (Dw.p - 1)) → ∀ (N M k : ℕ), 0 < N → 2 * M + N ≤ k + 1 → ∃ (w : GlobalTheory.AllWt.Psi H → ℤ) (a : (E →+* ℂ) × ℕ → ℕ), Dom a (2 * M) ∧ (fun i => (ex Dw a (2 * M) i : ℤ)) = (k + 1) • GlobalTheory.AllWt.exOf Dw la 0 + GlobalTheory.AllWt.exOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) M := by
  intro E _ _ _ H Dw la hp hq hanti hgap N M k hN hk
  have key : ∀ σ : Psi H, ∃ w : ℤ,
      (∀ i : Fin (Dw.p + Dw.q), (i : ℕ) < Dw.p → 0 ≤ ((k : ℤ) + 1) * la σ i + N * w - M) ∧
      (∀ i : Fin (Dw.p + Dw.q), Dw.p ≤ (i : ℕ) → 0 ≤ -(((k : ℤ) + 1) * la σ i) - N * w - M) :=
    fun σ => exists_shift hp hq (la σ) (hanti σ) (hgap σ) N M k hN hk
  choose w hwb hws using key
  have hantiσ : ∀ (σ : Psi H) (i j : Fin (Dw.p + Dw.q)), i ≤ j → la σ j ≤ la σ i :=
    fun σ _ _ h => hanti σ h
  set val : (E →+* ℂ) × ℕ → ℤ := fun x => ((k : ℤ) + 1) * (wtOf Dw la 0).1 x +
    (wtOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) (M : ℤ)).1 x with hval
  have vbig : ∀ (σ : Psi H) (i : ℕ) (hi : i < Dw.p),
      val (σ.1, i) = ((k : ℤ) + 1) * la σ ⟨i, by omega⟩ + (N * w σ - M) := by
    intro σ i hi
    simp only [hval]
    rw [wtOf_big _ _ σ i hi, wtOf_big _ _ σ i hi]
    simp [GlobalTheory.FlatLine.parWt]
  have vsmall : ∀ (σ : Psi H) (i : ℕ) (hi : i < Dw.q),
      val (conjEmb σ.1, i) = -(((k : ℤ) + 1) * la σ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩) - N * w σ - M := by
    intro σ i hi
    simp only [hval]
    rw [wtOf_small _ _ σ i hi, wtOf_small _ _ σ i hi]
    simp [GlobalTheory.FlatLine.parWt]
    ring
  have split : ∀ τ : E →+* ℂ, (∃ σ : Psi H, σ.1 = τ ∧ Dw.mult τ = Dw.p) ∨
      (∃ σ : Psi H, conjEmb σ.1 = τ ∧ Dw.mult τ = Dw.q) := by
    intro τ
    by_cases h : τ (H.rt : E) = H.rt0
    · exact Or.inl ⟨⟨τ, h⟩, rfl, by simp [Datum.mult, h]⟩
    · exact Or.inr ⟨⟨conjEmb τ, conj_mem h⟩, _root_.GlobalTheory.AllWt.conjEmb_conjEmb τ, by simp [Datum.mult, h]⟩
  have nonneg : ∀ (τ : E →+* ℂ) (i : ℕ), i < Dw.mult τ → 0 ≤ val (τ, i) := by
    intro τ i hi
    rcases split τ with ⟨σ, rfl, hm⟩ | ⟨σ, rfl, hm⟩
    · rw [hm] at hi; rw [vbig σ i hi]; have := hwb σ ⟨i, by omega⟩ hi; linarith
    · rw [hm] at hi; rw [vsmall σ i hi]; exact hws σ _ (by simp)
  have mono : ∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → val (τ, j) ≤ val (τ, i) := by
    intro τ i j hij hj
    have hk0 : (0 : ℤ) ≤ (k : ℤ) + 1 := by positivity
    rcases split τ with ⟨σ, rfl, hm⟩ | ⟨σ, rfl, hm⟩
    · rw [hm] at hj
      rw [vbig σ i (by omega), vbig σ j hj]
      have := hantiσ σ ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp [Fin.le_def]; omega)
      nlinarith
    · rw [hm] at hj
      rw [vsmall σ i (by omega), vsmall σ j hj]
      have := hantiσ σ ⟨Dw.p + (Dw.q - 1 - j), by omega⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩
        (by simp [Fin.le_def]; omega)
      nlinarith
  refine ⟨w, fun x => if x.2 < Dw.mult x.1 then (val x).toNat else 0, ⟨fun τ => ?_, even_two_mul M⟩, ?_⟩
  · intro i j hij
    simp only
    split_ifs with hj hi hi
    · exact Int.toNat_le_toNat (mono τ i j hij hj)
    · omega
    · exact Nat.zero_le _
    · exact le_refl _
  · funext x
    rcases x with _ | ⟨τ, i⟩
    · simp [ex, exOf, exZ, wtOf]
    · have hi : (i : ℕ) < Dw.mult τ := i.2
      show (((if (i : ℕ) < Dw.mult τ then (val (τ, (i : ℕ))).toNat else 0 : ℕ)) : ℤ) = _
      rw [if_pos hi, Int.toNat_of_nonneg (nonneg τ i hi)]
      rw [Pi.add_apply, Pi.smul_apply]
      show _ = (k + 1) • (wtOf Dw la 0).1 (τ, (i : ℕ)) +
        (wtOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) (M : ℤ)).1 (τ, (i : ℕ))
      rw [nsmul_eq_mul]
      simp only [hval]
      push_cast
      ring

end GlobalTheory.WtMatchArithBar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.uniformised_complex_fibre_marked_lattice_class : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL (D' : PLat D.O D.inv) t Q e, 0 < N → N.Coprime p → UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → ∃ t', D.Cls N D' t' ∧ ∀ a, ∃ x, t' a = t a + N • x := by
  first | exact @GlobalTheory.UPel.HT.unifAt_cls | exact GlobalTheory.UPel.HT.unifAt_cls | (intros; apply GlobalTheory.UPel.HT.unifAt_cls <;> assumption)
end
