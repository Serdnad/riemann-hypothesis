module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle934
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle686
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle919
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle613
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle943
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem exists_isCoef : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (𝔞 𝔟 : Frac F) (s : ℕ), 1 ≤ s → ∃ (Z : ℂ → ℂ) (a : F → ℂ), IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Z ∧ IsCoef (2 * s) 𝔞 𝔟 ((2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - ((2 * s : ℕ) : ℂ))) a := by
  intro hE F _ _ _ hf 𝔞 𝔟 s hs
  obtain ⟨G, hG, -, hX⟩ := hE F hf 𝔞 𝔟 s hs
  obtain ⟨Z, a, hZ, h0, hint, hsupp, hsum⟩ := GlobalTheory.T.hilbertEisenstein_fourier_expansion_support F (2 * s) 𝔞 𝔟 G hX
  refine ⟨Z, a, hZ, h0, hint, hsupp, fun w hw ↦ ?_⟩
  have hv := GlobalTheory.T.hilbertEisensteinLatticeValue_eq_of_isValue F (2 * s) _ _ _ _ (GlobalTheory.T.isHilbertEisensteinLatticeValue_of_eisensteinSeries F (2 * s) 𝔞 𝔟 G w (even_two_mul s) hG hw)
  have hne : ((2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F) ^ (2 * s) ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ Complex.two_pi_I_ne_zero)
  rw [hv, mul_pow ((2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F), mul_left_comm, mul_div_mul_left _ _ hne]
  exact hsum w hw

end GlobalTheory.HilbFam
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hilbertEisensteinLatticeJet_split_direction_add : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t v : ℂ) (κ : Emb F → ℕ), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → jet k (split 𝔞 𝔟 x) κ τ (c + v) t = ∑ μ ∈ Finset.Iic κ, ((∏ i, rco k (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i)) * jet k (split 𝔞 𝔟 x) μ τ c t := by
  first | exact @GlobalTheory.HilbFam.jet_split_add | exact GlobalTheory.HilbFam.jet_split_add | (intros; apply GlobalTheory.HilbFam.jet_split_add <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem jet_split_smul_direction : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t v : ℂ) (κ : Emb F → ℕ), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → jet k (split 𝔞 𝔟 x) κ τ (v * c) (v * t) = v ^ (∑ i, κ i) * jet k (split 𝔞 𝔟 x) κ τ c t := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t v κ hk ha hτ
  have h1 := GlobalTheory.T.hasSum_hilbertEisenstein_jet_split_lattice F k 𝔞 𝔟 a₀ a x τ (v * c) (v * t) κ hk ha hτ
  have h2 := (GlobalTheory.T.hasSum_hilbertEisenstein_jet_split_lattice F k 𝔞 𝔟 a₀ a x τ c t κ hk ha hτ).mul_left (v ^ (∑ i, κ i))
  refine h1.unique (HasSum.congr_fun h2 fun ξ ↦ ?_)
  have hp : (∏ i : Emb F, lag k (κ i) (v * c) ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * (v * t))) =
      v ^ (∑ i, κ i) * ∏ i : Emb F, lag k (κ i) c ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [show (2 * Real.pi * Complex.I) * (i ξ : ℂ) * (v * t) = v * ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t) by ring]
    exact (lag_homogeneous k (κ i) c _ v).1
  rw [hp]; ring

end GlobalTheory.HilbFam
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.tangent_value_pullback_crystalline_form_dual_numbers : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) (A' : Over (Sp R')) (φ : A'.left ⟶ A.left) (m : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R') (A'.hom ≫ 𝟙 (Sp R')) (algebraMap R R') φ) (v : epsR R' ⟶ A') (hy : (v.left ≫ φ) ≫ A.hom ≫ 𝟙 (Sp R) = spMap (algebraMap R (DualNumber R'))) (f : Form (A.hom ≫ 𝟙 (Sp R))), tanVal v (m.pullForm f) = TrivSqZeroExt.snd ((SqExt.ofModule R R' R').val (v.left ≫ φ) hy f.1) := by
  first | exact @GlobalTheory.ParPt.tanVal_pullForm_ofModule | exact GlobalTheory.ParPt.tanVal_pullForm_ofModule | (intros; apply GlobalTheory.ParPt.tanVal_pullForm_ofModule <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory

open TopForm

namespace TopForm

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ} {U : Y.Opens}

theorem dOn_eq_zero_of_eq_one (f : Fin D → Γ(Y, U)) (b : Fin D) (hb : f b = 1) : dOn p f = 0 := by
  rw [dOn, dForm_eq]
  refine AlternatingMap.map_coord_zero _ b ?_
  let := (algX p U).toAlgebra
  rw [hb]
  exact (KaehlerDifferential.D k Γ(Y, U)).map_one_eq_zero

theorem jacOn_of_eq_one (f : Fin (D + 1) → Γ(Y, U)) (i : Fin (D + 1)) (hi : f i = 1) :
    jacOn p f = (-1 : Γ(Y, U)) ^ (i : ℕ) • dOn p fun b => f (i.succAbove b) := by
  rw [jacOn_eq, Finset.sum_eq_single i, hi, mul_one]
  · intro a _ ha
    obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq (Ne.symm ha)
    rw [dOn_eq_zero_of_eq_one _ b (by rw [hb, hi]), smul_zero]
  · intro h
    exact (h (Finset.mem_univ i)).elim

theorem isUnit_of_affine {f : Γ(Y, U)}
    (h : ∀ W : Y.Opens, IsAffineOpen W → ∀ hW : W ≤ U, IsUnit (resG Y hW f)) : IsUnit f := by
  refine Y.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx => ?_
  obtain ⟨W, hW, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hx
  have := (h W hW hWU).map (Y.presheaf.germ W x hxW).hom
  rwa [show (Y.presheaf.germ W x hxW).hom (resG Y hWU f) = (Y.presheaf.germ U x hx).hom f from
    Y.presheaf.germ_res_apply (homOfLE hWU) x hxW f] at this

theorem isFreeGen_dForm_X (k : Type) [CommRing k] (D : ℕ) : IsFreeGen (MvPolynomial (Fin D) k)
    (dForm (algebraMap k (MvPolynomial (Fin D) k)) (X : Fin D → _)) := by
  have key (inst : Algebra k (MvPolynomial (Fin D) k))
      (e : inst = AddMonoidAlgebra.algebra) :
      IsFreeGen (MvPolynomial (Fin D) k) (@dWedge k _ _ _ inst D X) := by
    subst e
    have := isFreeGen_ιMulti (KaehlerDifferential.mvPolynomialBasis k (Fin D))
    rwa [funext (KaehlerDifferential.mvPolynomialBasis_apply k (Fin D))] at this
  exact key _ (Algebra.algebra_ext _ _ fun _ => rfl)

end TopForm

namespace ProjSpace

variable (R : Type) [CommRing R] (N : ℕ)

theorem isFrame_dOn_ratio (i : Fin (N + 1)) :
    IsFrame (dOn (PSpace.str R N) fun b : Fin N => ratio R N i (i.succAbove b)) := by
  refine ⟨isAffineOpen_chart R N i, ?_⟩
  let e : MvPolynomial (Fin N) R ≃ₐ[R] Γ(PSpace R N, chart R N i) :=
    (renameEquiv R (finSuccAboveEquiv i)).trans (chartAlgEquiv R N i)
  have he : (e : MvPolynomial (Fin N) R →+* _).comp (algebraMap R _) =
      algX (PSpace.str R N) (chart R N i) := RingHom.ext fun r => e.commutes r
  have := (isFreeGen_dForm_X R N).formMap (RingHom.Etale.of_bijective e.bijective) he
  rw [formMap_dForm] at this
  convert this using 3 with b
  exact ((congrArg (chartAlgEquiv R N i) (rename_X _ b)).trans
    (chartAlgEquiv_X R N i (finSuccAboveEquiv i b))).symm

theorem isUnit_jacSec_coord [SmoothOfRelativeDimension N (PSpace.str R N)]
    (K : CanonLB (PSpace.str R N) N) (c : (K.adj (O1 R N) (N + 1)).ι) :
    IsUnit ((K.jacSec (coord R N)).f c) := by
  refine isUnit_of_affine fun W hW h => ?_
  have l := h.trans (K.adj_U_le _ c)
  have h₂ : W ≤ chart R N (c.2 PUnit.unit) := l.trans inf_le_right
  rw [K.resG_jacSec_f _ c h (l.trans inf_le_left) h₂]
  change IsUnit (K.coeff _ _ (jacOn _ (ratioOn W (c.2 PUnit.unit) h₂)))
  rw [jacOn_of_eq_one _ (c.2 PUnit.unit) (ratioOn_self (hi := h₂)), map_smul, smul_eq_mul]
  refine (isUnit_one.neg.pow _).mul ((K.isUnit_jacobian_iff _ hW _ _).2 ?_)
  have := (isFrame_dOn_ratio R N (c.2 PUnit.unit)).res hW h₂
  rw [resForm_dOn] at this
  exact this

end ProjSpace

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem exists_isOb1 : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), L.IsFun → L'.IsFun → L.IsLift L' n l → ∀ w : Glob1 F, ∃ c, L.IsOb1 L' n l α w c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F C' _ F' L L' n l hL hL' hl w
  classical
  have hdiff : ∀ (T T' : C') (a : T ⟶ T') (b : L.B (n.G.obj T)),
      (L'.ρ a).comp (l T) b - (l T').comp (L.ρ (n.G.map a)) b ∈ I.map (algebraMap R (L'.B T')) := by
    intro T T' a b
    rw [← L'.ker, map_sub, sub_eq_zero]
    simp only [AlgHom.comp_apply, L'.nat]
    rw [hl, hl, L.nat]
    exact (n.naturality a _).symm
  have hκ : ∀ (T T' : C') (a : T ⟶ T'), ∃ κ : Ω[F.obj (n.G.obj T)⁄R₀] →+ L'.B T',
      IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) κ := fun T T' a ↦
    ((theta_classify R R₀ (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L'.B T') I hI π hπ (L.p _) (L.semi _)
      (L.surj _) (L.ker _) _).1 _ (hdiff T T' a)).exists
  choose κ hκ using hκ
  have hσ : ∀ T, ∃ σ : R₁ ⊗[R₀] F'.obj T →+ L'.B T, α.IsSig (L'.p T) σ := fun T ↦
    GlobalTheory.T.exists_augmentation_tensor_sigma_map R R₀ I hI π hπ hk R₁ α (L'.B T) (F'.obj T) (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T)
  choose σ hσ using hσ
  have hz : ∀ (T T' : C') (a : T ⟶ T'), ∃ y : R₁ ⊗[R₀] F'.obj T', α.KerQ y ∧ σ T' y = κ T T' a (w.1 _) :=
    fun T T' a ↦ (GlobalTheory.T.augmentation_sigma_map_basic_properties R R₀ I hI π hπ hk R₁ α (L'.B T') (F'.obj T') (L'.p T') (L'.semi T')
      (L'.surj T') (L'.ker T') (σ T') (hσ T')).2.2.2 _ ((hκ T T' a).mem _)
  choose z hzq hzs using hz

  have hcomp : ∀ (T T' T'' : C') (a : T ⟶ T') (b : T' ⟶ T'') (x : Ω[F.obj (n.G.obj T)⁄R₀]),
      κ T T'' (a ≫ b) x = L'.ρ b (κ T T' a x) + κ T' T'' b (p1 F (n.G.map a) x) := by
    intro T T' T'' a b x
    have t1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _) (L.surj _) (L.ker _)
      (L'.B T') (L'.B T'') _ _ _ (hκ T T' a)).1 (L'.ρ b)
    have t2 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj T')) (F.obj (n.G.obj T')) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _) (L.surj _) (L.ker _)
      (L'.B T'') (L'.B T'') _ _ _ (hκ T' T'' b)).2 (L.ρ (n.G.map a)) (mp F (n.G.map a)) (fun y ↦ L.nat _ y)
    have e0 : ((L'.ρ b).comp (l T')).comp (L.ρ (n.G.map a)) = (L'.ρ b).comp ((l T').comp (L.ρ (n.G.map a))) :=
      AlgHom.ext fun _ ↦ rfl
    rw [e0] at t2
    have t3 := ((GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (L'.B T'') _ _ _ _ _ t1).2.1 t2)
    have e1 : (L'.ρ b).comp ((L'.ρ a).comp (l T)) = (L'.ρ (a ≫ b)).comp (l T) :=
      AlgHom.ext fun y ↦ (hL' a b _).symm
    have e2 : ((l T'').comp (L.ρ (n.G.map b))).comp (L.ρ (n.G.map a)) = (l T'').comp (L.ρ (n.G.map (a ≫ b))) :=
      AlgHom.ext fun y ↦ by
        show l T'' (L.ρ (n.G.map b) (L.ρ (n.G.map a) y)) = l T'' (L.ρ (n.G.map (a ≫ b)) y)
        rw [Functor.map_comp, hL]
    rw [e1, e2] at t3
    have e3 := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (L'.B T'') _ _ ((l T'').comp (L.ρ (n.G.map (a ≫ b)))) _ _ (hκ T T'' (a ≫ b))).2.2.1 t3
    exact congrArg (fun f ↦ f x) e3
  let zc : Z1 (ext R₁ F') := ⟨fun T T' a ↦ z T T' a, fun T T' T'' a b ↦ by
    have sn := GlobalTheory.T.augmentation_sigma_map_natural R R₀ I hI π hπ hk R₁ α (L'.B T') (F'.obj T') (L'.p T') (L'.semi T') (L'.surj T')
      (L'.ker T') (L'.B T'') (F'.obj T'') (L'.p T'') (L'.semi T'') (L'.surj T'') (L'.ker T'') (L'.ρ b) (mp F' b)
      (fun y ↦ L'.nat b y) (σ T') (σ T'') (hσ T') (hσ T'')
    change z T T'' (a ≫ b) = extHom R₁ (mp F' b) (z T T' a) + z T' T'' b
    rw [← sub_eq_zero]
    haveI := L'.smooth T''
    refine GlobalTheory.T.augmentation_sigma_map_injective_of_flat R R₀ I hI π hπ hk R₁ α (L'.B T'') (F'.obj T'') (L'.p T'') (L'.semi T'') (L'.surj T'')
      (L'.ker T'') (σ T'') (hσ T'') _ ?_ ?_
    · have h1 := hzq T T'' (a ≫ b)
      have h2 := sn.2 _ (hzq T T' a)
      have h3 := hzq T' T'' b
      unfold Aug.KerQ at h1 h2 h3 ⊢
      rw [map_sub, map_add (f := _), h1, h2, h3]; simp
    · rw [map_sub, map_add (f := _), ← sn.1, hzs, hzs, hzs, hcomp, w.2 (n.G.map a)]
      simp⟩
  exact ⟨H1.mk _ zc, κ, σ, zc, hκ, hσ, rfl, fun T T' a ↦ ⟨hzq T T' a, hzs T T' a⟩⟩

end GlobalTheory.Obs
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

theorem exists_isOb2 : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w : Glob1 F), ∃ c, L.IsOb2 α w c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L w
  have hθ : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), ∃ θ : Ω[F.obj T⁄R₀] →+ L.B T'',
      IsTheta I (L.p T) ((L.ρ b).comp (L.ρ a)) (L.ρ (a ≫ b)) θ := by
    intro T T' T'' a b
    obtain ⟨θ, hθ, -⟩ := (theta_classify R R₀ (L.B T) (F.obj T) (L.B T'') I hI π hπ (L.p T) (L.semi T)
      (L.surj T) (L.ker T) ((L.ρ b).comp (L.ρ a))).1 (L.ρ (a ≫ b)) (fun x ↦ by
        rw [← L.ker T'', map_sub, AlgHom.comp_apply, L.nat, L.nat, L.nat, mp_comp, sub_self])
    exact ⟨θ, hθ⟩
  choose θ hθ using hθ
  have hσ : ∀ T, ∃ σ : R₁ ⊗[R₀] F.obj T →+ L.B T, α.IsSig (L.p T) σ := fun T ↦
    GlobalTheory.T.exists_augmentation_tensor_sigma_map R R₀ I hI π hπ hk R₁ α (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
  choose σ hσ using hσ
  have hz : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), ∃ y : R₁ ⊗[R₀] F.obj T'',
      α.KerQ y ∧ σ T'' y = θ T T' T'' a b (w.1 T) := fun T T' T'' a b ↦
    (GlobalTheory.T.augmentation_sigma_map_basic_properties R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'')
      (L.ker T'') (σ T'') (hσ T'')).2.2.2 _ ((hθ T T' T'' a b).mem _)
  choose z hzK hzσ using hz
  have key : ∀ (T T' T'' T''' : C) (a : T ⟶ T') (b : T' ⟶ T'') (c : T'' ⟶ T''') (x : Ω[F.obj T⁄R₀]),
      L.ρ c (θ T T' T'' a b x) + θ T T'' T''' (a ≫ b) c x =
        θ T T' T''' a (b ≫ c) x + θ T' T'' T''' b c (p1 F a x) := by
    intro T T' T'' T''' a b c x
    have h1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.B T'') (L.B T''') _ _ _
      (hθ T T' T'' a b)).1 (L.ρ c)
    have s1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T''') _ _ _ _ _ h1).2.1 (hθ T T'' T''' (a ≫ b) c)
    have h2 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T')
      (L.ker T') (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.B T''') (L.B T''') _ _ _
      (hθ T' T'' T''' b c)).2 (L.ρ a) (mp F a) (L.nat a)
    have s2 := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T''') _ _ _ _ _ h2).2.1 (hθ T T' T''' a (b ≫ c))
    rw [Category.assoc] at s1
    rw [AlgHom.comp_assoc] at s2
    have e := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
      (L.B T''') _ _ (L.ρ (a ≫ b ≫ c)) _ _ s1).2.2.1 s2
    have ex := DFunLike.congr_fun e x
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply] at ex
    exact ex.trans (add_comm _ _)
  have hZ : (fun T T' T'' a b ↦ z T T' T'' a b : C2 (ext R₁ F)) ∈ Z2 (ext R₁ F) := by
    intro T T' T'' T''' a b c
    haveI := L.smooth T'''
    haveI : Module.Flat R (L.B T''') := Algebra.Smooth.flat R _
    have nat := GlobalTheory.T.augmentation_sigma_map_natural R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'')
      (L.surj T'') (L.ker T'') (L.B T''') (F.obj T''') (L.p T''') (L.semi T''') (L.surj T''') (L.ker T''')
      (L.ρ c) (mp F c) (L.nat c) (σ T'') (σ T''') (hσ T'') (hσ T''')
    have em : ∀ y, mp (ext R₁ F) c y = extHom R₁ (mp F c) y := fun _ ↦ rfl
    rw [← sub_eq_zero]
    apply GlobalTheory.T.augmentation_sigma_map_injective_of_flat R R₀ I hI π hπ hk R₁ α (L.B T''') (F.obj T''') (L.p T''') (L.semi T''')
      (L.surj T''') (L.ker T''') (σ T''') (hσ T''')
    · have k1 := nat.2 _ (hzK T T' T'' a b)
      have k2 := hzK T T'' T''' (a ≫ b) c
      have k3 := hzK T T' T''' a (b ≫ c)
      have k4 := hzK T' T'' T''' b c
      unfold Aug.KerQ at k1 k2 k3 k4 ⊢
      rw [em]
      simp only [map_sub, map_add (f := _), k1, k2, k3, k4, sub_self, add_zero]
    · rw [em, map_sub, map_add (f := _), map_add (f := _), ← (nat.1 _), hzσ, hzσ, hzσ, hzσ, w.2 a, key, sub_self]
  exact ⟨H2.mk _ ⟨_, hZ⟩, θ, σ, ⟨_, hZ⟩, hθ, hσ, rfl, fun T T' T'' a b ↦ ⟨hzK T T' T'' a b, hzσ T T' T'' a b⟩⟩

end GlobalTheory.Obs
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem obstructionPullback_eq_zero_of_naturalLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) (C'' : Type) [Category.{0} C''] (F'' : C'' ⥤ CommAlgCat.{0} R₀) (L'' : Pre I π F'') (m : CoefMap (RingHom.id R₀) F' F'') (u : ∀ T : C'', L'.B (m.G.obj T) →ₐ[R] L''.B T) (v : ∀ T : C'', L.B (n.G.obj (m.G.obj T)) →ₐ[R] L''.B T), L.IsLift L' n l → L'.IsLift L'' m u → L'.IsNat L'' m u → (∀ T b, L''.p T (v T b) = m.α T (n.α _ (L.p _ b))) → (∀ (T T' : C'') (a : T ⟶ T') b, L''.ρ a (v T b) = v T' (L.ρ (n.G.map (m.G.map a)) b)) → ∀ (w : Glob1 F) (c : GlobalTheory.CatCoh.H1 (ext R₁ F')), L.IsOb1 L' n l α w c → (extMap R₁ m).pull1 c = 0 := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F C' _ F' L L' n l C'' _ F'' L'' m u v hl hu hun hvp hvn w c hc
  obtain ⟨κ, σ', z, hκ, hσ', rfl, hz⟩ := hc
  choose σ'' hσ'' using fun T : C'' ↦ GlobalTheory.T.exists_augmentation_tensor_sigma_map R R₀ I hI π hπ hk R₁ α (L''.B T) (F''.obj T) (L''.p T)
    (L''.semi T) (L''.surj T) (L''.ker T)

  have hdiff : ∀ (T : C'') (b : L.B (n.G.obj (m.G.obj T))),
      (u T).comp (l (m.G.obj T)) b - v T b ∈ I.map (algebraMap R (L''.B T)) := fun T b ↦ by
    refine (L''.ker T _).1 ?_
    rw [map_sub, sub_eq_zero]
    exact (hu T _).trans ((congrArg (m.α T) (hl _ b)).trans (hvp T b).symm)
  choose th hth using fun T : C'' ↦ ((theta_classify R R₀ (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T)))
    (L''.B T) I hI π hπ (L.p _) (L.semi _) (L.surj _) (L.ker _) ((u T).comp (l (m.G.obj T)))).1 (v T) (hdiff T)).exists

  have key : ∀ (T T' : C'') (a : T ⟶ T'),
      L''.ρ a (th T (w.1 (n.G.obj (m.G.obj T)))) =
        u T' (κ _ _ (m.G.map a) (w.1 (n.G.obj (m.G.obj T)))) + th T' (w.1 (n.G.obj (m.G.obj T'))) := by
    intro T T' a
    have h1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L'.B (m.G.obj T')) (L''.B T') _ _ _ (hκ _ _ (m.G.map a))).1 (u T')
    have h2 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj (m.G.obj T'))) (F.obj (n.G.obj (m.G.obj T'))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L''.B T') (L''.B T') _ _ _ (hth T')).2 (L.ρ (n.G.map (m.G.map a)))
      (mp F (n.G.map (m.G.map a))) (fun x ↦ L.nat _ x)
    rw [AlgHom.comp_assoc] at h2
    have h3 := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk _ _ (L.p (n.G.obj (m.G.obj T))) (L.semi _) (L.surj _) (L.ker _)
      (L''.B T') _ _ _ _ _ h1).2.1 h2
    have h4 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L''.B T) (L''.B T') _ _ _ (hth T)).1 (L''.ρ a)
    have e1 : (L''.ρ a).comp ((u T).comp (l (m.G.obj T))) =
        (u T').comp ((L'.ρ (m.G.map a)).comp (l (m.G.obj T))) := AlgHom.ext fun b ↦ hun a _
    have e2 : (L''.ρ a).comp (v T) = (v T').comp (L.ρ (n.G.map (m.G.map a))) := AlgHom.ext fun b ↦ hvn T T' a b
    rw [e1, e2] at h4
    have h5 := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk _ _ (L.p (n.G.obj (m.G.obj T))) (L.semi _) (L.surj _) (L.ker _)
      (L''.B T') _ _ ((v T').comp (L.ρ (n.G.map (m.G.map a)))) _ _ h4).2.2 |>.1 <| h3
    have h6 := DFunLike.congr_fun h5 (w.1 (n.G.obj (m.G.obj T)))
    rw [w.2 (n.G.map (m.G.map a))]
    exact h6
  choose g hgK hg using fun T : C'' ↦ (GlobalTheory.T.augmentation_sigma_map_basic_properties R R₀ I hI π hπ hk R₁ α (L''.B T) (F''.obj T) (L''.p T)
    (L''.semi T) (L''.surj T) (L''.ker T) (σ'' T) (hσ'' T)).2.2.2 (-(th T (w.1 (n.G.obj (m.G.obj T)))))
    (neg_mem ((hth T).mem _))
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
  refine ⟨g, ?_⟩
  funext T T' a
  have sg := GlobalTheory.T.augmentation_sigma_map_natural R R₀ I hI π hπ hk R₁ α (L''.B T) (F''.obj T) (L''.p T) (L''.semi T) (L''.surj T)
    (L''.ker T) (L''.B T') (F''.obj T') (L''.p T') (L''.semi T') (L''.surj T') (L''.ker T') (L''.ρ a) (mp F'' a)
    (fun b ↦ L''.nat a b) (σ'' T) (σ'' T') (hσ'' T) (hσ'' T')
  have su := GlobalTheory.T.augmentation_sigma_map_natural R R₀ I hI π hπ hk R₁ α (L'.B (m.G.obj T')) (F'.obj (m.G.obj T')) (L'.p _) (L'.semi _)
    (L'.surj _) (L'.ker _) (L''.B T') (F''.obj T') (L''.p T') (L''.semi T') (L''.surj T') (L''.ker T') (u T')
    (coefHom m T') (fun b ↦ hu T' b) (σ' _) (σ'' T') (hσ' _) (hσ'' T')
  haveI : Algebra.Smooth R (L''.B T') := L''.smooth T'
  change g T' - extHom R₁ (mp F'' a) (g T) = extHom R₁ (coefHom m T') (z.1 _ _ (m.G.map a))
  refine sub_eq_zero.1 (GlobalTheory.T.augmentation_sigma_map_injective_of_flat R R₀ I hI π hπ hk R₁ α (L''.B T') (F''.obj T') (L''.p T') (L''.semi T')
    (L''.surj T') (L''.ker T') (σ'' T') (hσ'' T') _ ?_ ?_)
  · have k1 := hgK T'
    have k2 := sg.2 _ (hgK T)
    have k3 := su.2 _ (hz _ _ (m.G.map a)).1
    unfold Aug.KerQ at k1 k2 k3 ⊢
    rw [map_sub, map_sub, k1, k2, k3, sub_zero, sub_zero]
  · rw [map_sub, map_sub, hg T', ← sg.1, hg T, ← su.1, (hz _ _ _).2, map_neg, key T T' a]
    abel

end GlobalTheory.Obs
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistCupProduct_assoc : ∀ (q : ℕ) [NeZero q] (E : Spc) {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l), cup q (cup q a b) c = (cup q a (cup q b c)).cast (by ring) (by ring) := by
  first
  | exact @GlobalTheory.EtC.CupAssoc.main
  | exact GlobalTheory.EtC.CupAssoc.main
  | (intros; apply GlobalTheory.EtC.CupAssoc.main <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.eqv_spMap_tw_of_isUnit : ∀ (q : ℕ) (i : ℤ) (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B), SH A → SH B → IsUnit (q : A) → Eqv _ (spMap φ) (tw q i) := by
  first | (exact @GlobalTheory.EtC.sh_eqv_tw) | (exact GlobalTheory.EtC.sh_eqv_tw) | (intros; apply GlobalTheory.EtC.sh_eqv_tw  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistCoefficientReduction_cup : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (E : Spc) {n m i j : ℤ} (a : Ht Q E n i) (b : Ht Q E m j), red Q q E _ _ (cup Q a b) = cup q (red Q q E _ _ a) (red Q q E _ _ b) := by
  exact @GlobalTheory.EtC.RedCup.reduction_cup
end
