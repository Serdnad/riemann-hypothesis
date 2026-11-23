module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodReductionModelCmPeriodFibre
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle046
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolyDivDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle044
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle045
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle080
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle081
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementB
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle001
public import ReciprocityTheory.SemistableReduction.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle039
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle082
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle027
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle014
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.exists_goodReduction_model_cmPeriod_fibre : CMCurve → CMPoint → ThetaUnifAV → Out.Laws → Out.Laws2 → HomExtDvr → Published.KernelFiniteFlatSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (p q : ℕ) (_ : CMLat hP p q) (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k →
  ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (hk : KA l ≤ K₁) (ω : Bool → 𝓞 K₁) (C : ∀ b, Ell H (𝓞 K₁) (ω b)) (ε : Bool → ℤˣ) (h : Bool → (FU.Di i).La → (FU.Di i).La → OK H) (B : PAT H (Sp (𝓞 K₁))) (y : Sp K₁ ⟶ Xo.X) (t₀ : SAB H (Sp K₁)) (m : SABMap t₀ Xo.univ.t y) (m' : SABMap t₀ B.t (spMap (algebraMap (𝓞 K₁) K₁)))
    (ψ : ∀ b : Bool, PureType.lat hP (if b then H.rt0 else -H.rt0) → ((C b).P.A ⟶ B.t.G)) (ω' : Bool → ℂ) (C' : ∀ b, Ell H ℂ (ω' b)) (π : ∀ b, (C' b).P.A.left ⟶ (C b).P.A.left) (u₀ : ∀ b, HolUnif (C' b).P.A (C' b).P.L (C' b).P.g) (c : Bool → ℂ),
    k ≤ K₁ ∧ y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i Pe ∧
    ∀ b : Bool, 2 * ω' b - 1 = (if b then H.rt0 else -H.rt0) ∧ 0 < ((ε b : ℤ) : ℝ) * (ω' b).im ∧ IsKForm (FU.Di i) (ε b) (h b) ∧ IsFam (C b) B (h b) _ (ψ b) ∧ EllMap (C' b) (C b) ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁)) (π b) ∧ c b ≠ 0 ∧ PureType.IsQuadLattice (u₀ b).Λ H.d (c b) ∧
      ∀ a (z : ℂ) (x : Sp ℂ ⟶ t₀.G.left), x ≫ t₀.G.hom = spMap (algebraMap K₁ ℂ) → x ≫ m'.φ = ((u₀ b).ex (fun _ => c b * z)).left ≫ π b ≫ (ψ b a).left → x ≫ m.φ = (FU.ex i Pe (z • Pe a)).left := by
  first | exact @GlobalTheory.CM.PeriodModel.exists_model | exact GlobalTheory.CM.PeriodModel.exists_model | (intros; apply GlobalTheory.CM.PeriodModel.exists_model <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem evR_frChg_mul_triangular (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (F : Rul Xo c) (hF : F ∈ sec Xo c a n) (z z' : FrPt Xo c K)
    (T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K) (hT : ∀ b, (T b).BlockTriangular id)
    (hd : ∀ b, (T b).det ≠ 0) (h : FrChg (fun b => (T b).transpose) 1 z z') :
    evR Xo c F z' = (∏ b, ∏ i, T b i i ^ a (b, i)) * evR Xo c F z := by
  have hne : ∀ b i, T b i i ≠ 0 := by
    intro b i
    have h1 := hd b
    rw [Matrix.det_of_isUpperTriangular (hT b)] at h1
    exact (Finset.prod_ne_zero_iff.1 h1) i (Finset.mem_univ i)
  let t : Formalism.L2.Pj.Ix Dw → Kˣ := fun o => match o with
    | none => 1
    | some x => Units.mk0 (T x.1 x.2 x.2) (hne x.1 x.2)
  have hb : FrBor t z z' := by
    refine ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K z z' z').1 t).2
      ⟨fun b => (T b).transpose, fun τ i j hij => ?_, fun τ i => rfl, h⟩
    exact hT τ hij
  have hw := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 K inferInstance a n F hF
    t z z' hb
  rw [hw]
  congr 1
  simp only [wchar, Fintype.prod_option, Fintype.prod_sigma, t, Formalism.L2.Pj.ex, Units.val_one, one_pow, _root_.one_mul,
    Units.val_mk0]

theorem exists_isFrPoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, ∃ G : MvPolynomial (FrVar Dw.mult) K, IsFrPoly F y G := by
  classical
  intro E _ _ _ H Dw l Xo c K _ _ _ y a n F hF
  obtain ⟨P, N, hP⟩ := GlobalTheory.LamT.RatFn.exists_poly_div_det E H Dw l Xo c K y a n F hF
  have hrefl : FrMap (AlgHom.id c.F K) y y := GlobalTheory.Frames.frMapUniq_refl y
  have hPK : ∀ (z' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y z' →
      (∏ b, (Y b).det) ^ N * evR Xo c F z' = evalFr P Y := by
    intro z' Y hY h
    have h1 := hP K (AlgHom.id c.F K) y z' Y (fun b => (hY b).isUnit) hrefl h
    have h2 : MvPolynomial.map (AlgHom.id c.F K).toRingHom P = P := MvPolynomial.map_id P
    rwa [h2] at h1
  obtain ⟨G, hG⟩ := GlobalTheory.LamT.evalFr_eq_prod_det_pow_mul K (E →+* ℂ) Dw.mult P (fun b i => a (b, i)) N (by
    intro X b t hX ht htri
    let T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := Function.update (fun _ => 1) b t
    have hTb : T b = t := Function.update_self ..
    have hTo : ∀ b', b' ≠ b → T b' = 1 := fun b' h => Function.update_of_ne h ..
    have hTtri : ∀ b', (T b').BlockTriangular id := by
      intro b'
      by_cases h : b' = b
      · subst h; rw [hTb]; exact htri
      · rw [hTo b' h]; exact Matrix.blockTriangular_one
    have hTd : ∀ b', (T b').det ≠ 0 := by
      intro b'
      by_cases h : b' = b
      · subst h; rw [hTb]; exact ht
      · rw [hTo b' h]; simp
    have hup : Function.update X b (X b * t) = fun b' => X b' * T b' := by
      funext b'
      by_cases h : b' = b
      · subst h; rw [hTb, Function.update_self]
      · rw [hTo b' h, Function.update_of_ne h, _root_.mul_one]
    obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y (fun b => (X b).transpose) 1
      (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
    obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1
      (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
    rw [Units.val_one] at h₁ h₂
    have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y z₁ z₂).2 _ _ _ _ h₁ h₂
    simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
    have e₁ := hPK z₁ X hX h₁
    have e₂ := hPK z₂ (fun b' => X b' * T b')
      (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃
    have e₃ := evR_frChg_mul_triangular E H Dw l Xo c K a n F hF z₁ z₂ T hTtri hTd h₂
    have p₁ : (∏ b', ∏ i, T b' i i ^ a (b', i)) = ∏ i, t i i ^ a (b, i) := by
      rw [Finset.prod_eq_single b, hTb]
      · intro b' _ h
        rw [hTo b' h]; simp
      · intro h; exact absurd (Finset.mem_univ b) h
    have p₂ : (∏ b', (X b' * T b').det) = (∏ b', (X b').det) * ∏ i, t i i := by
      simp only [Matrix.det_mul, Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_eq_single b, hTb, Matrix.det_of_isUpperTriangular htri]
      · intro b' _ h
        rw [hTo b' h]; simp
      · intro h; exact absurd (Finset.mem_univ b) h
    rw [hup, ← e₂, ← e₁, e₃, p₁, p₂]
    simp only [pow_add, Finset.prod_mul_distrib, mul_pow, Finset.prod_pow]
    ring)
  refine ⟨G, fun S _ _ φ z z' Y hY hz hz' => ?_⟩
  have h1 := hP S φ z z' Y hY hz hz'
  rw [hG S φ.toRingHom Y] at h1
  have hu : IsUnit ((∏ b, (Y b).det) ^ N) := (IsUnit.prod_univ_iff.2 hY).pow N
  exact hu.mul_left_cancel h1

end GlobalTheory.LamT
end

section

noncomputable section

namespace GlobalTheory.MetricChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

theorem lift_comb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {G' : Over (Sp S)} [GrpObj G']
    {φ : G'.left ⟶ Xo.univ.t.G.left} (hp : IsGrpPullback G' Xo.univ.t.G x φ) :
    (∀ w : epsR S ⟶ G', IsTanAt x (w.left ≫ φ) → IsTangent w) ∧
    ∀ (n : ℕ) (c : Fin n → S) (v : Fin n → (epsR S ⟶ G')) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left),
      IsCombAt x (fun i => (v i).left ≫ φ) c w → ∃ w' : epsR S ⟶ G', w'.left ≫ φ = w ∧ IsLieComb c v w' := by
  let up : ∀ w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left,
      w ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x → (epsR S ⟶ G') :=
    fun w h => Over.homMk (hp.1.lift w _ h) (hp.1.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ φ = w := fun w h => hp.1.lift_fst _ _ _
  have one : ∀ T : Over (Sp S), (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ x) ⟶ Xo.univ.t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))
  have e : η[G'].left ≫ φ = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
    have e₁ : (1 : 𝟙_ (Over (Sp S)) ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
    rw [← e₁, one]
    exact congrArg (· ≫ (η[Xo.univ.t.G]).left) (Category.id_comp x)
  have zs : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext s; simp
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have pr : ∀ {n} (u : Fin n → (epsR S ⟶ G')), (List.ofFn u).prod.left ≫ φ =
      (List.ofFn fun i => (pushPt hp.1.w (u i) : tEps x ⟶ Xo.univ.t.G)).prod.left := fun u =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))
  refine ⟨fun w h => hp.1.hom_ext ?_ ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
  · refine (Category.assoc _ _ _).trans ?_
    rw [Over.w w, Over.w η[G']]
    exact zs
  · rintro n c v w ⟨u, hu, hw⟩
    refine ⟨(List.ofFn fun i => up (u i).left (Over.w _)).prod, (pr _).trans (Eq.trans ?_ hw),
      fun i => up (u i).left (Over.w _), fun i => hp.1.hom_ext ?_ ?_, rfl⟩
    · have : u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEps x ⟶ Xo.univ.t.G) :=
        funext fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm
      exact (congrArg (fun q : _ → (tEps x ⟶ Xo.univ.t.G) => (List.ofFn q).prod.left) this).symm
    · exact (hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)
    · refine (Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
      exact (spMap_epsScaleR_comp (c i)).symm

def scaleSec {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} (a : R) (s : LB.Sec L) : LB.Sec L where
  f i := constFn p _ a * s.f i
  compat i j := by
    have h : ∀ (U V : X.Opens) (h : U ≤ V), (X.presheaf.map (homOfLE h).op).hom (constFn p V a) = constFn p U a := by
      intro U V h
      simp only [constFn]
      exact congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
        (Scheme.Hom.appLE_map p (U := ⊤) (V := V) (fun _ _ => trivial) (homOfLE h).op)
    rw [map_mul, map_mul, h, h, s.compat]
    ring

theorem nonzeroLocus_scaleSec {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} {a : R}
    (ha : IsUnit a) (s : LB.Sec L) : Out.nonzeroLocus (scaleSec p a s) = Out.nonzeroLocus s := by
  unfold Out.nonzeroLocus
  refine iSup_congr fun k => ?_
  have hu : IsUnit (constFn p (L.U k) a) := (ha.map _).map _
  show X.basicOpen (constFn p _ a * s.f k) = _
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit hu]
  exact inf_eq_right.2 (X.basicOpen_le _)

theorem hermForm_sum {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (W : Fin n → Fin g → ℂ) (c d : Fin n → ℂ) :
    hermForm Hm (∑ l, c l • W l) (∑ j, d j • W j) = ∑ l, ∑ j, star (d j) * hermForm Hm (W l) (W j) * c l := by
  simp only [hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem metricAt_change {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} (x : Sp ℂ ⟶ Xo.X) (s s' : LB.Sec (PPx x))
    (uu uu' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (N : ℝ)
    (Gr Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ) (a : ℂ) (ha : a ≠ 0)
    (ht : ∀ b i, IsTanAt x (uu b i)) (hc : ∀ b i, IsCombAt x (uu b) (fun j => Y b j i) (uu' b i))
    (hs : SecBC (RingHom.id ℂ) a x x s s') (h : IsMetricAt x s uu N Gr) :
    IsMetricAt x s' uu' (‖a‖ ^ 2 * N) (fun b => (Y b).conjTranspose * Gr b * Y b) := by
  obtain ⟨Φ, u, Hm, χ, θ, Fd, w, W, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  obtain ⟨l1, l2⟩ := lift_comb Φ.m.cart
  have hw : ∀ b, uu b = fun i => (w b i).left ≫ Φ.m.φ := fun b => funext fun i => (h7 b i).1.symm
  have hx : ∀ b i, ∃ w' : epsR ℂ ⟶ Φ.T.t.G, w'.left ≫ Φ.m.φ = uu' b i ∧ IsLieComb (fun j => Y b j i) (w b) w' :=
    fun b i => l2 _ _ (w b) _ (hw b ▸ hc b i)
  choose w' hw1 hw2 using hx
  let Φ' : FibKey Xo ℂ x :=
    { Φ with
      th := scaleSec Φ.T.t.G.hom a Φ.th
      th_ne := fun p => by rw [nonzeroLocus_scaleSec _ ha.isUnit]; exact Φ.th_ne p }
  refine ⟨Φ', u, Hm, χ, fun z => a * θ z, Fd, w', fun b i => ∑ j, Y b j i • W b j, ?_, h2, h3, ?_, h5, ?_,
    fun b i => ⟨hw1 b i, ?_⟩, fun b i k => ?_⟩
  · exact ((GlobalTheory.LamT.TieCalc.secTie_calc E H Dw l Xo ℂ x Φ.T.t Φ.m Φ.th s h1).1 a x s' _ rfl hs).2 fun _ => rfl
  · intro i z hz
    refine (valAt'_mul _ _ _ _).trans ?_
    rw [_root_.mul_assoc]
    exact congrArg₂ (· * ·) (valAt'_constFn _ _ (Over.w (u.ex z)) _ a hz) (h4 i z hz)
  · rw [h6, ← mul_div_assoc, ← integral_const_mul]
    congr 2
    funext z
    rw [norm_mul, mul_pow, _root_.mul_assoc]
  · exact (GlobalTheory.T.tangentVector_existsUnique_uniformisingVector Φ.key u).2 _ (w b) (W b) _ (w' b i) (fun j => l1 _ ((h7 b j).1.symm ▸ ht b j))
      (fun j => (h7 b j).2) (hw2 b i)
  · rw [hermForm_sum]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, h8, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem isMetric_frChg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (y y' : FrPt Xo c (CAt σ)) (N : ℝ) (Gr Y : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)) (a : ℂ), a ≠ 0 → FrChg (S := CAt σ) (fun b => (Y b).transpose) a y y' → IsMetric y N Gr → IsMetric y' (‖a‖ ^ 2 * N) (fun b => (Y b).conjTranspose * Gr b * Y b) := by
  intro E _ _ _ H Dw l Xo c σ y y' N Gr Y a ha ⟨hx, hc, hs⟩ h
  obtain ⟨x', hx', u', t', e', b', s', g'⟩ := y'
  obtain ⟨x, hx0, u, t, e, b, s, g⟩ := y
  obtain rfl : x' = x := hx
  exact metricAt_change x' s s' u u' N Gr Y a ha t hc hs h

end GlobalTheory.MetricChange
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.exists_unit_integral_generator_principal_local_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (G : PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, y.x = x → ∃ a : T.Frˣ, ∀ (g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr)) (y' : FrPt Xo c T.Fr), FrChg g (a : T.Fr) y y' → SecInt T m1 m2 y'.s := by
  first | exact @GlobalTheory.LamT.LocSec.exists_unit_secInt | exact GlobalTheory.LamT.LocSec.exists_unit_secInt | (intros; apply GlobalTheory.LamT.LocSec.exists_unit_secInt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.framePolynomial_equivariant_and_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, ∀ G : MvPolynomial (FrVar Dw.mult) K, IsFrPoly F y G → (∀ [DecidableEq (E →+* ℂ)] (σ : K →+* ℂ), IsEquiv (fun b (i : Fin (Dw.mult b)) => a (b, i)) (MvPolynomial.map σ G)) ∧ ∀ (σ : c.F →+* ℂ) (σ₁ : K →ₐ[c.F] CAt σ) (w : FrPt Xo c (CAt σ)), spMap σ₁.toRingHom ≫ y.x = w.x → evR Xo c F w ≠ 0 → G ≠ 0 := by
  first | exact @GlobalTheory.LamT.isFrPoly_equiv_and_ne_zero | exact GlobalTheory.LamT.isFrPoly_equiv_and_ne_zero | (intros; apply GlobalTheory.LamT.isFrPoly_equiv_and_ne_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.integral_generator_baseChange_valuationRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l), ∀ (T T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∀ (x : Sp T.Fr ⟶ Xo.X) (x' : Sp T'.Fr ⟶ Xo.X) (G : PAT H (Sp T.V)) (G' : PAT H (Sp T'.V)) (t : SAB H (Sp T.Fr)) (t' : SAB H (Sp T'.Fr)) (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G.t (spMap (algebraMap T.V T.Fr))) (m1' : SABMap t' Xo.univ.t x') (m2' : SABMap t' G'.t (spMap (algebraMap T'.V T'.Fr))) (n : SABMap G'.t G.t (spMap ψ)) (n' : SABMap t' t (spMap i)), x' = spMap i ≫ x → m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')), SecBC i 1 x x' s s' → SecInt T m1 m2 s → SecInt T' m1' m2' s' := by
  first | exact @GlobalTheory.LamT.secInt_baseChange | exact GlobalTheory.LamT.secInt_baseChange | (intros; apply GlobalTheory.LamT.secInt_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.universalTripleFibreKeyData_nonempty_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → Nonempty (FibKey Xo K x) := by
  first | exact @GlobalTheory.LamT.nonempty_fibKey | exact GlobalTheory.LamT.nonempty_fibKey | (intros; apply GlobalTheory.LamT.nonempty_fibKey <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.rigidifiedSectionCorrespondence_existsUnique_nonvanishing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (t' : SAB H (Sp S)) (m : SABMap t' Xo.univ.t x), (∀ th, ∃ s : LB.Sec (PPx x), SecTie m th s) ∧ (∀ s : LB.Sec (PPx x), ∃ th, SecTie m th s) ∧ ∀ th (s : LB.Sec (PPx x)), SecTie m th s → (∀ th' (s' : LB.Sec (PPx x)), SecTie m th' s' → ((∀ i, th'.f i = th.f i) ↔ ∀ i, s'.f i = s.f i)) ∧ (SecNZ x s ↔ ∀ p : Sp S, ∃ q : t'.G.left, t'.G.hom q = p ∧ q ∈ Out.nonzeroLocus th) := by
  first | exact @GlobalTheory.SecTieEx.secTie_exists_unique | exact GlobalTheory.SecTieEx.secTie_exists_unique | (intros; apply GlobalTheory.SecTieEx.secTie_exists_unique <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory IsLocalRing Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open scoped nonZeroDivisors ComplexOrder

namespace GlobalTheory

theorem thetaDegree_and_lowerBound : (∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → T.dual.deg = (1 / 2) * abelian₂.dual.deg + (x.P.g : ℝ) / 4 * (Module.finrank ℚ K : ℝ) * Real.log (2 * Real.pi)) ∧ (∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (H : (K →+* ℂ) → Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (La logOm : ℝ) (V : Type) [Fintype V] (c : V → Fin x.P.g) (G : MvPolynomial V K) (μ : V →₀ ℕ) (n : ℕ) (S : (K →+* ℂ) → ℝ) (Rr : ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → U.det ≠ 0 → 1 ≤ La → (∀ σ, (H σ).PosDef) → (∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re) → (∀ p : HeightOneSpectrum (𝓞 K), ∃ (cd : K) (cl : Fin x.P.g → K), IsLocGen p cd abelian₂.I ∧ (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧ p.valuation K ((∏ j, cl j) * U.det) ≤ p.valuation K cd) → (∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (U j)) ≤ (La * (ℓ j).n σ) ^ 2) → (∀ j, (ℓ j).ndeg = logOm / 2) → AddMonoidAlgebra.coeff G μ ≠ 0 → AddMonoidAlgebra.coeff G μ ∈ (lineNN T.dual ℓ c μ n).I → (∀ σ, 0 < S σ) → 0 < Rr → (∀ (σ : K →+* ℂ) (z : V → ℂ), (∀ v, ‖z v‖ * (ℓ (c v)).n σ ≤ 1) → ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n ≤ S σ * Rr ^ (∑ v, μ v)) → - ((pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (x.P.g : ℝ) * n)) - (∑ v, (μ v : ℝ)) * Real.log Rr ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ)) :=
  have hdeg := GlobalTheory.T.thetaLine_dual_degree_of_keyFormulaPowerForm GlobalTheory.keyFormulaPow_and_keyDegree.1
  ⟨hdeg, GlobalTheory.T.thetaPolynomial_lower_bound_of_thetaLine_degree hdeg⟩

end GlobalTheory
end
