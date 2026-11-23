module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle284
public import Formalism.LocalToGlobal.HermitianForms.PrkSmul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MeasurePreservingMulLeft
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle187
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle319
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

noncomputable section

namespace GlobalTheory.OneMapRef.Frames

open GlobalTheory.Ker.ONBasis

variable {D : D7} {T : HSp D}

theorem negM_sq (T : HSp D) (q : ℕ) : negM T q * negM T q = 1 := by
  unfold negM
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  unfold sgn
  split_ifs <;> simp

theorem negM_herm (T : HSp D) (q : ℕ) : (negM T q)ᴴ = negM T q := by
  unfold negM
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp

theorem compAt_eq (θ : InfFam D) (ρ : D.what₂.Tau) (h : GA D T) :
    compAt θ ρ (Formalism.L2.Theta.mt T h) = infMat D.sp.cm.sig T.gram (θ ρ) h := rfl

theorem compAt_unitary' {θ : InfFam D} (hθ : IsInfFam θ) (ρ : D.what₂.Tau) (g : GA D T) :
    (compAt θ ρ (Formalism.L2.Theta.mt T g))ᴴ * gramAt D T ρ * compAt θ ρ (Formalism.L2.Theta.mt T g) = gramAt D T ρ := by
  rw [GlobalTheory.FockCompare.RealAction.gramAt_eq hθ]
  exact GlobalTheory.FockCompare.RealAction.unitary_map (cA D) ((θ ρ).comp (infPart D))
    (GlobalTheory.FockCompare.comp_cA hθ ρ) _ _ (mt_rel T g)

theorem isONeg_mvZ {θ : InfFam D} (hθ : IsInfFam θ) {q : ℕ} {Z : Fam T} (hZ : IsONeg T q Z) (g : GA D T) :
    IsONeg T q (mvZ θ g Z) := by
  intro τ
  unfold mvZ
  rw [Matrix.conjTranspose_mul, ← hZ τ]
  conv_rhs => rw [← compAt_unitary' hθ τ g]
  simp only [Matrix.mul_assoc]

theorem mvZ_mul (θ : InfFam D) (Z : Fam T) (g g' : GA D T) : mvZ θ (g' * g) Z = mvZ θ g' (mvZ θ g Z) := by
  funext τ
  unfold mvZ
  have e : Formalism.L2.Theta.mt T (g' * g) = Formalism.L2.Theta.mt T g' * Formalism.L2.Theta.mt T g := by simp [Formalism.L2.Theta.mt]
  rw [e, ← Matrix.mul_assoc]
  congr 1
  exact Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem mvZ_fin (θ : InfFam D) (Z : Fam T) {g : GA D T} (hg : g ∈ GfC T) : mvZ θ g Z = Z := by
  funext τ
  have h1 : (Formalism.L2.Theta.mt T g).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  have h2 : compAt θ τ (Formalism.L2.Theta.mt T g) = ((Formalism.L2.Theta.mt T g).map (infPart D)).map (θ τ) := rfl
  unfold mvZ
  rw [h2, h1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem cartZ_mvZ {θ : InfFam D} (hθ : IsInfFam θ) {q : ℕ} {Z : Fam T} (hZ : IsONeg T q Z) (g : GA D T)
    (τ : D.what₂.Tau) :
    cartZ T q (mvZ θ g Z) τ * compAt θ τ (Formalism.L2.Theta.mt T g) = compAt θ τ (Formalism.L2.Theta.mt T g) * cartZ T q Z τ := by
  have hu' := isUnit_det (negM_sq T q) (isONeg_mvZ hθ hZ g τ)
  have e : (mvZ θ g Z τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T g) = (Z τ)⁻¹ := by
    symm
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.mul_assoc]
    exact Matrix.nonsing_inv_mul _ hu'
  unfold cartZ
  rw [Matrix.mul_assoc, e]
  unfold mvZ
  simp only [Matrix.mul_assoc]

theorem fin_of_mvZ {θ : InfFam D} (hθ : IsInfFam θ) {q : ℕ} {Z : Fam T} (hZ : IsONeg T q Z) {g : GA D T}
    (h : mvZ θ g Z = Z) : g ∈ GfC T := by
  refine (GlobalTheory.SmoothForms.RealPts.glue θ hθ T).1 g fun τ => ?_
  have hu := isUnit_det (negM_sq T q) (hZ τ)
  have h1 : compAt θ τ (Formalism.L2.Theta.mt T g) * Z τ = Z τ := congrFun h τ
  rw [← compAt_eq]
  calc _ = compAt θ τ (Formalism.L2.Theta.mt T g) * Z τ * (Z τ)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = 1 := by rw [h1, Matrix.mul_nonsing_inv _ hu]

theorem exists_move {θ : InfFam D} (hθ : IsInfFam θ) {q : ℕ} {Z Z' : Fam T} (hZ : IsONeg T q Z)
    (hZ' : IsONeg T q Z') : ∃ a ∈ GinfC T, Z' = mvZ θ a Z := by
  have hu := fun τ => isUnit_det (negM_sq T q) (hZ τ)
  obtain ⟨a, ha, h⟩ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ T).2 (fun τ => Z' τ * (Z τ)⁻¹) (fun τ => by
    show (Z' τ * (Z τ)⁻¹)ᴴ * gramAt D T τ * (Z' τ * (Z τ)⁻¹) = gramAt D T τ
    have h2 := Matrix.mul_nonsing_inv _ (hu τ)
    calc _ = (Z τ)⁻¹ᴴ * ((Z' τ)ᴴ * gramAt D T τ * Z' τ) * (Z τ)⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (Z τ * (Z τ)⁻¹)ᴴ * gramAt D T τ * (Z τ * (Z τ)⁻¹) := by
          rw [hZ' τ, ← hZ τ]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one])
  refine ⟨a, ha, funext fun τ => ?_⟩
  unfold mvZ
  rw [compAt_eq, h τ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hu τ), Matrix.mul_one]

theorem isOrtho_frOf {X : Data D.host.E T.rank} (eT : D.what₂.Tau ≃ X.Ψ) (hM : ModelW T rfl X)
    (he : ∀ ρ, (eT ρ).1 = tauE D ρ) {Z : Fam T} (hZ : IsONeg T X.p0 Z) : X.IsOrtho (frOf rfl eT Z) := by
  intro σ
  obtain ⟨τ, rfl⟩ := eT.surjective σ
  have hm : mat (frOf rfl eT Z) (eT τ) = Z τ := by
    ext a b
    simp [mat, frOf]
  have hG : ∀ a b, tauE D τ (X.Gm a b) = -gramAt D T τ b a := fun a b => by
    rw [hM.1]
    simp [gramAt]
  rw [hm, he]
  ext a b
  have h1 := congrFun (congrFun (hZ τ) b) a
  have h2 : FD.gram (tauE D τ) X.Gm (Z τ) a b = -((Z τ)ᴴ * gramAt D T τ * Z τ) b a := by
    simp only [FD.gram, hermC, FD.col, Matrix.of_apply, hG, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Finset.sum_mul, ← Finset.sum_neg_distrib, RCLike.star_def]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h2, h1, negM]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab), neg_zero]

theorem isUnitFr_of_isOrtho {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (hx : X.IsOrtho x) : IsUnitFr X x := by
  intro τ i
  unfold dmin
  have h : FD.gram τ.1 X.Gm (mat x τ) = sgnM X := hx τ
  rw [h, GlobalTheory.SW.Slab.lminor_sgnM]
  rcases GlobalTheory.SW.Slab.psgn_sq X.p0 i with h | h <;> rw [h] <;> norm_num

end GlobalTheory.OneMapRef.Frames


open GlobalTheory.OneMapRef.Frames GlobalTheory.Ker.ONBasis in
theorem GlobalTheory.OneMapRef.oneg_frames : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ Z : Fam T, IsONeg T X.p0 Z → frOf hr eT Z ∈ X.dom ∧ IsUnitFr X (frOf hr eT Z) ∧ X.IsOrtho (frOf hr eT Z) ∧ (∀ ρ, IsCartanInv (gramAt D T ρ) (cartZ T X.p0 Z ρ)) ∧ ∀ h : GA D T, IsONeg T X.p0 (mvZ θ h Z) ∧ (∀ ρ, cartZ T X.p0 (mvZ θ h Z) ρ * compAt θ ρ (Formalism.L2.Theta.mt T h) = compAt θ ρ (Formalism.L2.Theta.mt T h) * cartZ T X.p0 Z ρ) ∧ (∀ h', mvZ θ (h' * h) Z = mvZ θ h' (mvZ θ h Z)) ∧ (h ∈ GfC T → mvZ θ h Z = Z) ∧ (mvZ θ h Z = Z → h ∈ GfC T) ∧ ∀ Z', IsONeg T X.p0 Z' → ∃ a ∈ GinfC T, Z' = mvZ θ a Z := by
  intro D S T r g hr ψ θ X eT bas idx hS Z hZ
  subst hr
  obtain ⟨-, hθ, -, -, hM, -, he, -⟩ := hS
  have ho := isOrtho_frOf eT hM he hZ
  exact ⟨mem_dom X ho, isUnitFr_of_isOrtho X ho, ho,
    fun ρ => isCartanInv (negM_sq T _) (negM_herm T _) (hZ ρ),
    fun h => ⟨isONeg_mvZ hθ hZ h, cartZ_mvZ hθ hZ h, mvZ_mul θ Z h, mvZ_fin θ Z, fin_of_mvZ hθ hZ,
      fun _ hZ' => exists_move hθ hZ hZ'⟩⟩

end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.DefU.LocRet

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem under_conjSrc (v : HeightOneSpectrum (𝓞 E)) :
    (conjSrc (IsCMField.complexConj E).toRingEquiv v).under (𝓞 (maximalRealSubfield E)) =
      v.under (𝓞 (maximalRealSubfield E)) := by
  have h := conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv v
  ext y
  change algebraMap _ (𝓞 E) y ∈ (conjSrc (IsCMField.complexConj E).toRingEquiv v).asIdeal ↔ algebraMap _ (𝓞 E) y ∈ v.asIdeal
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← h]
  have : (IsCMField.complexConj E).toRingEquiv ((algebraMap _ (𝓞 E) y : 𝓞 E) : E) = ((algebraMap _ (𝓞 E) y : 𝓞 E) : E) := by
    change (IsCMField.complexConj E) (algebraMap (maximalRealSubfield E) E (y : maximalRealSubfield E)) = _
    rw [AlgEquiv.commutes]
    rfl
  rw [this]

variable (w : HeightOneSpectrum (𝓞 E))


open Classical in
def idemF : Af E :=
  ⟨fun v => if v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) then 1 else 0,
    Filter.Eventually.of_forall fun v => by
      dsimp only
      split_ifs
      · exact one_mem _
      · exact zero_mem _⟩

def idem : Ad E := sFin E (idemF w)

theorem idem_mul_idem : idem w * idem w = idem w := by
  refine Prod.ext (mul_zero _) (FiniteAdeleRing.ext E fun v => ?_)
  change (idemF w).1 v * (idemF w).1 v = (idemF w).1 v
  simp only [idemF]
  split_ifs <;> simp

def sIdem : Ad E →ₙ+* Ad E where
  toFun x := idem w * x
  map_mul' x y := by
    calc idem w * (x * y) = (idem w * idem w) * (x * y) := by rw [idem_mul_idem]
      _ = idem w * x * (idem w * y) := by ring
  map_zero' := mul_zero _
  map_add' x y := mul_add _ _ _

theorem pInf_sIdem (x : Ad E) : pInf E (sIdem w x) = 0 := by
  change pInf E (sFin E (idemF w) * x) = 0
  rw [map_mul]
  have : pInf E (sFin E (idemF w)) = 0 := map_zero (infEq E).symm
  rw [this, zero_mul]

theorem pLoc_sIdem_of_eq {v : HeightOneSpectrum (𝓞 E)}
    (hv : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) (x : Ad E) :
    ((pLoc E v).comp (pFin E)) (sIdem w x) = ((pLoc E v).comp (pFin E)) x := by
  change ((pLoc E v).comp (pFin E)) (idem w) * _ = _
  have : ((pLoc E v).comp (pFin E)) (idem w) = 1 := by
    change (idemF w).1 v = 1
    simp only [idemF, if_pos hv]
  rw [this, one_mul]
  rfl

theorem pLoc_sIdem_of_ne {v : HeightOneSpectrum (𝓞 E)}
    (hv : v.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) (x : Ad E) :
    ((pLoc E v).comp (pFin E)) (sIdem w x) = 0 := by
  change ((pLoc E v).comp (pFin E)) (idem w) * _ = _
  have : ((pLoc E v).comp (pFin E)) (idem w) = 0 := by
    change (idemF w).1 v = 0
    simp only [idemF, if_neg hv]
  rw [this, zero_mul]

theorem conjAd_idem : conjAd E (idem w) = idem w := by
  refine Prod.ext ?_ (FiniteAdeleRing.ext E fun v => ?_)
  · change (infEq E) ((starRingEnd (Cinf E)) ((infEq E).symm 0)) = 0
    simp
  change pLoc E v (conjFin (IsCMField.complexConj E).toRingEquiv (idemF w)) = (idemF w).1 v
  rw [pLoc_conjFin]
  change conjLoc _ v ((idemF w).1 _) = (idemF w).1 v
  have hc := under_conjSrc (E := E) v
  simp only [idemF]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd (hc.symm.trans h1) h2
  · exact absurd (hc.trans h2) h1
  · simp

variable {w} {n : ℕ}

theorem ga_ext' {g h : GA E n} (h1 : GeneralLinearGroup.map (pInf E) g = GeneralLinearGroup.map (pInf E) h)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 E), GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g =
      GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) h) : g = h := by
  refine ga_ext h1 (Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext E fun v => ?_))
  exact congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i j) (h2 v)

theorem cT_corner (M : Matrix (Fin n) (Fin n) (Ad E)) :
    cT (conjAd E) (corner (matN n (sIdem w)) M) = corner (matN n (sIdem w)) (cT (conjAd E) M) := by
  ext i j
  change conjAd E ((1 : Matrix (Fin n) (Fin n) (Ad E)) j i - idem w * (1 : Matrix (Fin n) (Fin n) (Ad E)) j i +
      idem w * M j i) = (1 : Matrix (Fin n) (Fin n) (Ad E)) i j - idem w * (1 : Matrix (Fin n) (Fin n) (Ad E)) i j +
      idem w * conjAd E (M j i)
  rw [map_add (f := _), map_sub, map_mul, map_mul, conjAd_idem, Matrix.one_apply, Matrix.one_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

theorem corner_mem (g : UA E n) : cornerGL n (sIdem w) g.1 ∈ UA E n := by
  have hg : cT (conjAd E) (g.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * g.1 = 1 := g.2
  change cT (conjAd E) (corner (matN n (sIdem w)) g.1.1) * 1 * corner (matN n (sIdem w)) g.1.1 = 1
  rw [cT_corner, Matrix.mul_one, ← map_mul, ← Matrix.mul_one (cT (conjAd E) _), hg, map_one]


variable (n w) in
def ret0 : UA E n →* UA E n := ((cornerGL n (sIdem w)).comp (UA E n).subtype).codRestrict (UA E n) corner_mem

theorem infiniteProj_unitaryAdelicLocalRetractionEnd_eq_one (g : UA E n) : GeneralLinearGroup.map (pInf E) (ret0 w n g).1 = 1 :=
  map_cornerGL_of_zero _ _ (pInf_sIdem w) _

theorem localProj_unitaryAdelicLocalRetractionEnd_of_under_eq {v : HeightOneSpectrum (𝓞 E)}
    (hv : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) (g : UA E n) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (ret0 w n g).1 = GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g.1 :=
  map_cornerGL_of_hom _ _ _ (pLoc_sIdem_of_eq w hv) _

theorem localProj_unitaryAdelicLocalRetractionEnd_of_under_ne {v : HeightOneSpectrum (𝓞 E)}
    (hv : v.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) (g : UA E n) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (ret0 w n g).1 = 1 :=
  map_cornerGL_of_zero _ _ (pLoc_sIdem_of_ne w hv) _

theorem unitaryAdelicLocalRetractionEnd_mem_localPoints (g : UA E n) : ret0 w n g ∈ locU n w := by
  refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 (infiniteProj_unitaryAdelicLocalRetractionEnd_eq_one g), Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_⟩
  exact MonoidHom.mem_ker.2 (localProj_unitaryAdelicLocalRetractionEnd_of_under_ne hu g)

theorem mem_locU_inf {x : UA E n} (hx : x ∈ locU n w) : GeneralLinearGroup.map (pInf E) x.1 = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hx).1

theorem mem_locU_ne {x : UA E n} (hx : x ∈ locU n w) {v : HeightOneSpectrum (𝓞 E)}
    (hv : v.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) x.1 = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 v) hv)


variable (n w) in
def ret : UA E n →* locU n w := (ret0 w n).codRestrict (locU n w) unitaryAdelicLocalRetractionEnd_mem_localPoints

theorem continuous_ret : Continuous (ret w n) := by
  have hc : Continuous (corner (matN n (sIdem w))) := by
    change Continuous fun M : Matrix (Fin n) (Fin n) (Ad E) => 1 - (1 : Matrix (Fin n) (Fin n) (Ad E)).map (idem w * ·) +
      M.map (idem w * ·)
    exact continuous_const.add (continuous_id.matrix_map (continuous_const.mul continuous_id))
  exact Continuous.subtype_mk (Continuous.subtype_mk ((Continuous.units_map _ hc).comp continuous_subtype_val) _) _

theorem ret_of_mem (x : locU n w) : ret w n x = x := by
  refine Subtype.ext (Subtype.ext (ga_ext' ?_ fun v => ?_))
  · exact (infiniteProj_unitaryAdelicLocalRetractionEnd_eq_one x.1).trans (mem_locU_inf x.2).symm
  · by_cases hv : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
    · exact localProj_unitaryAdelicLocalRetractionEnd_of_under_eq hv x.1
    · exact (localProj_unitaryAdelicLocalRetractionEnd_of_under_ne hv x.1).trans (mem_locU_ne x.2 hv).symm

theorem commute_ret (g : UA E n) (y : locU n w) : Commute ((ret w n g : UA E n)⁻¹ * g) (y : UA E n) := by
  refine Subtype.ext (ga_ext' ?_ fun v => ?_)
  · simp only [Subgroup.coe_mul, map_mul, mem_locU_inf y.2, one_mul, mul_one]
  · by_cases hv : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
    · have h : GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (((ret w n g : UA E n)⁻¹ * g : UA E n) : GA E n) = 1 := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
        change (GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (ret0 w n g).1)⁻¹ * _ = 1
        rw [localProj_unitaryAdelicLocalRetractionEnd_of_under_eq hv g, inv_mul_cancel]
      simp only [Subgroup.coe_mul, map_mul] at h ⊢
      rw [h, one_mul, mul_one]
    · simp only [Subgroup.coe_mul, map_mul, mem_locU_ne y.2 hv, one_mul, mul_one]

theorem exists_ret (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) :
    ∃ r : UA E n →* locU n w, Continuous r ∧ (∀ x : locU n w, r x = x) ∧
      ∀ (g : UA E n) (y : locU n w), Commute ((r g : UA E n)⁻¹ * g) (y : UA E n) :=
  ⟨ret w n, continuous_ret, ret_of_mem, commute_ret⟩

end GlobalTheory.DefU.LocRet

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms
attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_localPlace_asIdeal_iff_val_pos : ∀ (D : D7) (sc : Scale) (Ce : ℝ)
    (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
      (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)
    (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (iK : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w])
    (lam : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
    (hK : ∀ u w hg (z : D.what₂.LL), iK u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) =
      lamV (lam u w hg) (D.what₂.embLL z))
    (hPos : ∀ u w hg, (packC D Lc I ψ u w hg).posOK (iK u w hg) (lam u w hg))
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (v : Fin (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) (s : Fin (nFr D (D.what₂.places.resChar w)))
    (x : 𝓞 D.host.F),
    x ∈ (((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg).pl v).1.asIdeal ↔
      (0 : WithTop ℤ) < D.what₂.places.val w (tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
        (algebraMap D.host.F D.host.E (x : D.host.F))) := by
  first | exact @GlobalTheory.TiePlace.place_of_tie | exact GlobalTheory.TiePlace.place_of_tie | (intros; apply GlobalTheory.TiePlace.place_of_tie <;> assumption)
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitary_completion_maps_dualLattices : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (L Lb : Submodule (𝓞 E) (Fin n → E)) (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)), IsUnit J.det → Submodule.IsFullLattice E L → Submodule.IsFullLattice E Lb → y ∈ UPts σ J (v.adicCompletion F) → (∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔ (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb) → ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J L) ↔ (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J Lb) := by
  first | exact @GlobalTheory.DualCompletion.dual_move | exact GlobalTheory.DualCompletion.dual_move | (intros; apply GlobalTheory.DualCompletion.dual_move <;> assumption)
end

section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ.SchurMove

theorem castGA_mem_GFset {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA) :
    x ∈ I.GFset ↔ Formalism.L2.SG.RowsJoinPinned.castGA e x ∈ I'.GFset := by
  subst e; rfl

theorem schur_iotaX : ∀ (D : D7) (S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar) (M : DSModel (D.sp.Y 0) S) (E : Submodule ℂ (MMap M)) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : Formalism.IndefR.Datum.InfFam D) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)), SchurAll D → (D.sp.Y 0).SigOK → IsInfFam θ → E ≤ Mult θ M J χ → (∀ T ∈ E, ∀ T' ∈ E, ∃ c : ℂ, ∀ v v' : M.Vec, ∫ x, star (T v ((Formalism.L2.SG.RowsJoinPinned.iotaX St h).symm x * t)) * T' v' ((Formalism.L2.SG.RowsJoinPinned.iotaX St h).symm x * t) ∂(muX St) = c * ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ) := by
  intro D S M E St h θ J χ t hS hsig hθ hE T hT T' hT'
  haveI := St.B.haar
  haveI := St.B.sf
  have hι : ∀ g, g ∈ GQ (D.sp.Y 0) ↔ Formalism.L2.SG.RowsJoinPinned.iotaX St h g ∈ St.B.I.GFset := by
    intro g
    rw [Formalism.IndefR.RationalEmbedding.iota_rat]
    exact castGA_mem_GFset _ _
  exact GlobalTheory.Mem.SJ.HaarMove.schur_of_bridge M θ J χ (fun μ 𝓕 => hS _ hsig S θ M J χ μ 𝓕) hθ St.B.I St.B.μf
    St.B.fund St.B.fund_spec (Formalism.L2.SG.RowsJoinPinned.iotaX St h) hι t T (hE hT) T' (hE hT')

end GlobalTheory.Mem.SJ.SchurMove
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FixedPlaceOverType

theorem exists_splitPlace_w_plGw : ∀ (D : D7) (k : Fin 2) (v : D.nd.PlG k), ∃ s : SplitPlace D.host.E, s.w = D.naut.plGw k v :=
  fun D k v => GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D ⟨k, v⟩

end GlobalTheory.FixedPlaceOverType
end
