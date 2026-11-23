module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle070
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle103
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle077
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle100
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle075
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle098
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle083
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle101
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadraticCharProductFormulaCMHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh.PushKer

theorem unit_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

theorem one_left {S T : Scheme.{0}} (a : T ⟶ S) (G : Over S) [MonObj G] :
    (1 : Over.mk a ⟶ G).left = a ≫ (η[G]).left := by
  rw [Hom.one_def]; simp

theorem one_iff {S T : Scheme.{0}} {a : T ⟶ S} {G : Over S} [MonObj G] (x : Over.mk a ⟶ G) :
    x = 1 ↔ x.left = a ≫ (η[G]).left := by
  rw [← one_left]
  exact ⟨fun h => h ▸ rfl, fun h => Over.OverMorphism.ext h⟩

end GlobalTheory.ShFam.Hor.LogCh.PushKer

namespace GlobalTheory.ShFam.Hor.LogCh

open PushKer

theorem pushEx_eq_one_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → ∀ z, pushEx Z Fu y i P p hu hp z = 1 ↔ z ∈ P.range := by
  intro E _ _ _ H Dw l Xo c O _ β Z g ty σ₀ Fu y i P p hu hp hP z
  rw [← Fu.ex_ker i P hP z, one_iff, one_iff, pushEx_left]
  have u0 := unit_comp Z.m0.toSABMap.cart
  have u1 := unit_comp Z.m.cart
  have hs : (η[Z.oF.t.G]).left ≫ Z.oF.t.G.hom = 𝟙 (Xo.XF c) := Over.w (η[Z.oF.t.G])
  constructor
  · intro h
    have e : liftEx Z Fu y i P hu z = y ≫ (η[Z.oF.t.G]).left := by
      apply Z.m.cart.1.hom_ext
      · rw [h, Category.assoc, u1, ← hp]
        simp only [Model.j, Category.assoc]
      · rw [liftEx_snd, Category.assoc, hs, Category.comp_id]
    rw [← liftEx_fst Z Fu y i P hu z, e, Category.assoc, u0, hu, Category.assoc]
  · intro h
    have e : liftEx Z Fu y i P hu z = y ≫ (η[Z.oF.t.G]).left := by
      apply Z.m0.toSABMap.cart.1.hom_ext
      · rw [liftEx_fst, h, Category.assoc, u0, hu, Category.assoc]
      · rw [liftEx_snd, Category.assoc, hs, Category.comp_id]
    rw [e, Category.assoc, u1, ← hp]
    simp only [Category.assoc]

end GlobalTheory.ShFam.Hor.LogCh
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.BasisX

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_inclR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (e : E) :
    sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem hform_eq {A : Type} [CommRing A] (τ : A →+* A) {M : ℕ} (J : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) : Formalism.UG.hform τ J x y = (τ ∘ x) ⬝ᵥ J.mulVec y := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] (τ : A →+* A) {M : ℕ} (J P : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) :
    Formalism.UG.hform τ J (P.mulVec x) (P.mulVec y) = Formalism.UG.hform τ (Formalism.UG.cT τ P * J * P) x y := by
  rw [hform_eq, hform_eq]
  have h : (τ ∘ P.mulVec x) = (P.map τ).mulVec (τ ∘ x) := by
    funext i
    exact RingHom.map_mulVec τ P x i
  rw [h, Formalism.UG.cT, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (τ ∘ x), Matrix.vecMul_transpose]

theorem qR_mulVec (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J P : Matrix (Fin M) (Fin M) E) (z : Fin M → R ⊗[F] E) :
    qR R σ J ((P.map (inclR R)).mulVec z) = qR R σ (Formalism.UG.cT (σ : E →+* E) P * J * P) z := by
  have h : JR R (Formalism.UG.cT (σ : E →+* E) P * J * P) =
      Formalism.UG.cT (sigR R σ) (P.map (inclR R)) * JR R J * P.map (inclR R) := by
    unfold JR
    rw [Matrix.map_mul, Matrix.map_mul]
    have hc : (Formalism.UG.cT (σ : E →+* E) P).map (inclR (F := F) R) =
        Formalism.UG.cT (sigR R σ) (P.map (inclR R)) := by
      ext i j
      exact (sigR_inclR R σ _).symm
    rw [hc]
  unfold qR hR
  rw [hform_mulVec, h]

end Alg

section Proj

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem prInf_inclR (e : E) : prInf (inclR (AF F) e) = inclR (Ainf F) e := by
  simp [prInf, inclR]

theorem prV_inclR (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV v (inclR (AF F) e) = inclR (Fv F v) e := by
  simp [prV, inclR]

end Proj

theorem fibAt_basis (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (hR : Nice R) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E)
    (lam : Measure (R ⊗[F] E)) (ν : Measure R) (β : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hl : lam.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure)
    (h : FibAt R σ (Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J *
      (P : Matrix (Fin M) (Fin M) E)) (tupMeas lam 1 M) ν β m) :
    FibAt R σ J (tupMeas lam 1 M) ν β
      (modu (R ⊗[F] E) (inclR R (P : Matrix (Fin M) (Fin M) E).det) •
        m.map (lrAct ((P : Matrix (Fin M) (Fin M) E).map (inclR R)) 1)) := by
  have hdet : ((P : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R)).det =
      inclR R (P : Matrix (Fin M) (Fin M) E).det := (RingHom.map_det _ _).symm
  have hu : IsUnit ((P : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R)).det := by
    rw [hdet]
    exact ((Matrix.isUnits_det_units P)).map _
  have := GlobalTheory.T.fibreMeasures_transport_unitary_similitude F E σ R hR M _ J lam ν β 1 m _ hl hν hu isUnit_one
    (fun z => by rw [one_mul, qR_mulVec]) h
  rw [one_mul, (modu_basic R).2.2.1, inv_one, mul_one, hdet] at this
  exact this

theorem isStdX_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E) (β : F) (ν' : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), J' = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E) → IsStdX s σ J' β ν' → IsStdX s σ J β (ν'.map (lrAct ((P : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) 1)) := by
  intro F E _ _ _ _ _ σ hσ d b s M J J' P β ν' hJ ⟨mi, mv, hi, hv, hp⟩
  subst hJ
  obtain ⟨hni, hnv⟩ := nice_ainf_fv F
  have hdet : (P : Matrix (Fin M) (Fin M) E).det ≠ 0 := (Matrix.isUnits_det_units P).ne_zero
  obtain ⟨hfin, hone⟩ := GlobalTheory.T.product_formula_haarModulus_cmField_element F E σ hσ _ hdet
  refine ⟨_, _, fibAt_basis F E σ (Ainf F) hni M J P _ _ _ _ s.haar_lamI s.haar_nuI hi,
    fun v => fibAt_basis F E σ (Fv F v) (hnv v) M J P _ _ _ _ (s.haar_lamV v) (s.haar_nuV v) (hv v), ?_⟩
  have h1 := GlobalTheory.T.isRestrictedProductTupleMeasure_map_leftRightAction F E d b 1 M ν' mi mv
    (Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) P) 1 hp
  have hg : (Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) P).val =
      (P : Matrix (Fin M) (Fin M) E).map (inclR (AF F)) := rfl
  have hI : ((P : Matrix (Fin M) (Fin M) E).map (inclR (F := F) (AF F))).map prInf =
      (P : Matrix (Fin M) (Fin M) E).map (inclR (Ainf F)) := by
    ext i j
    exact prInf_inclR _
  have hV : ∀ v, ((P : Matrix (Fin M) (Fin M) E).map (inclR (F := F) (AF F))).map (prV v) =
      (P : Matrix (Fin M) (Fin M) E).map (inclR (Fv F v)) := by
    intro v
    ext i j
    exact prV_inclR v _
  have h1I : (1 : Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)).map prInf = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have h1V : ∀ v, (1 : Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)).map (prV v) = 1 := fun v =>
    Matrix.map_one _ (map_zero _) (map_one _)
  simp only [hg, Units.val_one, hI, hV, h1I, h1V] at h1
  have h2 := GlobalTheory.T.restrictedProduct_measure_smul_factors_eq_smul F E d b 1 M _ _ _
    (modu (Ainf F ⊗[F] E) (inclR (Ainf F) (P : Matrix (Fin M) (Fin M) E).det)) _ h1 hfin
  rw [hone, one_smul] at h2
  exact h2

end GlobalTheory.GaugeEx.BasisX
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.ProdBasic

theorem repr_map {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E)
    (z : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp [hx, hy]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ}

def box (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (Fin n → Fin M → AF F ⊗[F] E) :=
  {X | ∀ v ∉ S, projV v (projFin X) ∈ latV b v}

theorem isOpen_box (S : Finset (HeightOneSpectrum (𝓞 F))) : IsOpen (box (n := n) (M := M) b S) := by
  have h : box (n := n) (M := M) b S = ⋂ a, ⋂ i, ⋂ k,
      (fun X : Fin n → Fin M → AF F ⊗[F] E =>
        ((Algebra.TensorProduct.basis (AF F) b).coord k (X a i)).2) ⁻¹'
        {x : Af F | ∀ v, v ∉ S → x.1 v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))} := by
    ext X
    simp only [box, latV, projV, projFin, repr_map, Set.mem_setOf_eq, Set.mem_iInter,
      Set.mem_preimage]
    exact ⟨fun h a i k v hv => h v hv a i k, fun h v hv a i k => h a i k v hv⟩
  rw [h]
  refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun k => IsOpen.preimage ?_ ?_
  · have h1 : Continuous ((Algebra.TensorProduct.basis (AF F) b).coord k) :=
      IsModuleTopology.continuous_of_linearMap _
    exact continuous_snd.comp (h1.comp ((continuous_apply i).comp (continuous_apply a)))
  · exact RestrictedProduct.isOpen_forall_imp_mem
      (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun _ => Valued.isOpen_valuationSubring _)

theorem box_mono {S T : Finset (HeightOneSpectrum (𝓞 F))} (h : S ⊆ T) :
    box (n := n) (M := M) b S ⊆ box b T := fun _ hX v hv => hX v fun hs => hv (h hs)

theorem exists_mem_box (X : Fin n → Fin M → AF F ⊗[F] E) : ∃ S, X ∈ box b S := by
  have h := (GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding F E d b n M).2.1
  have hX : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, projV v (projFin X) ∈ latV b v := by
    have h1 := Set.mem_range_self (f := fun X : Fin n → Fin M → AF F ⊗[F] E =>
      (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) X
    rw [h, Set.mem_setOf_eq] at h1
    exact h1
  have hf := Filter.eventually_cofinite.1 hX
  refine ⟨hf.toFinset, fun v hv => ?_⟩
  by_contra h'
  exact hv (by simpa using h')

variable {b} {ν : Measure (Fin n → Fin M → AF F ⊗[F] E)}
  {mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)}
  {mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)}

theorem measure_rect (h : IsProd b ν mi mv) (S : Finset (HeightOneSpectrum (𝓞 F)))
    {Ai : Set (Fin n → Fin M → Ainf F ⊗[F] E)}
    {Av : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)}
    (hi : MeasurableSet Ai) (hv : ∀ v, MeasurableSet (Av v)) :
    ν ({X | projInf X ∈ Ai ∧ ∀ v ∈ S, projV v (projFin X) ∈ Av v} ∩ box b S) =
      mi Ai * (∏ v ∈ S, mv v (Av v)) * tailProd b mv S := by
  have hm := (GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding F E d b n M).1.measurable
  have hmi : Measurable (projInf (F := F) (E := E) (M := M) (n := n)) := measurable_fst.comp hm
  have hmv : ∀ v : HeightOneSpectrum (𝓞 F),
      Measurable fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X) := fun v =>
    (measurable_pi_apply v).comp (measurable_snd.comp hm)
  have hR : MeasurableSet {X : Fin n → Fin M → AF F ⊗[F] E |
      projInf X ∈ Ai ∧ ∀ v ∈ S, projV v (projFin X) ∈ Av v} := by
    have : {X : Fin n → Fin M → AF F ⊗[F] E |
      projInf X ∈ Ai ∧ ∀ v ∈ S, projV v (projFin X) ∈ Av v} =
        projInf ⁻¹' Ai ∩ ⋂ v ∈ S, (fun X => projV v (projFin X)) ⁻¹' Av v := by
      ext X; simp
    rw [this]
    exact (hmi hi).inter (S.measurableSet_biInter fun v _ => hmv v (hv v))
  have key := h.2 S (Ai.indicator 1) (fun v => (Av v).indicator 1)
    (measurable_const.indicator hi) (fun v => measurable_const.indicator (hv v))
  simp only [lintegral_indicator_one hi, lintegral_indicator_one (hv _)] at key
  rw [← key, ← Measure.restrict_apply hR, ← lintegral_indicator_one hR]
  refine lintegral_congr fun X => ?_
  by_cases hX : projInf X ∈ Ai ∧ ∀ v ∈ S, projV v (projFin X) ∈ Av v
  · rw [Set.indicator_of_mem (by exact hX), Set.indicator_of_mem hX.1,
      Finset.prod_eq_one fun v hv => Set.indicator_of_mem (hX.2 v hv) _]
    simp
  · rw [Set.indicator_of_notMem (by exact hX)]
    rcases not_and_or.1 hX with h1 | h1
    · rw [Set.indicator_of_notMem h1, zero_mul]
    · push Not at h1
      obtain ⟨v, hv, h1⟩ := h1
      rw [Finset.prod_eq_zero hv (Set.indicator_of_notMem h1 _), mul_zero]

theorem exists_tailProd_ne_zero (h : Conv b mi mv) : ∃ S, tailProd b mv S ≠ 0 := by
  have hs := h.2.2
  have ht := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (show (0 : ℝ) < 1 from one_pos))
  have hf := Filter.eventually_cofinite.1 ht
  refine ⟨hf.toFinset, ?_⟩
  have hpos : ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ hf.toFinset},
      0 < (mv v.1 (latV b v.1)).toReal := fun v => by
    have h1 : |(mv v.1 (latV b v.1)).toReal - 1| < 1 := by
      by_contra h'
      exact v.2 (by simpa using h')
    linarith [(abs_lt.1 h1).1]
  have hs' : Summable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ hf.toFinset} =>
      (mv v.1 (latV b v.1)).toReal - 1 := (hs.of_abs).subtype _
  have hl := Real.summable_log_one_add_of_summable hs'
  simp only [add_sub_cancel] at hl
  rw [tailProd, ← Real.rexp_tsum_eq_tprod hpos hl]
  exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'

theorem finiteOnCompacts (h : IsProd b ν mi mv) : IsFiniteMeasureOnCompacts ν := by
  classical
  refine ⟨fun K hK => ?_⟩
  obtain ⟨S, hS⟩ := hK.elim_directed_cover (box b) (isOpen_box b)
    (fun X _ => Set.mem_iUnion.2 (exists_mem_box b X))
    (fun S T => ⟨S ∪ T, box_mono b Finset.subset_union_left, box_mono b Finset.subset_union_right⟩)
  have hc := (GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding F E d b n M).2.2
  have hi := hK.image hc.1
  have hv := fun v => hK.image (hc.2 v)
  have key := measure_rect h S hi.measurableSet (fun v => (hv v).measurableSet)
  haveI := h.1.1
  haveI := h.1.2.1
  refine lt_of_le_of_lt (measure_mono fun X hX => ?_) (key.trans_lt ?_)
  · exact ⟨⟨⟨X, hX, rfl⟩, fun v _ => ⟨X, hX, rfl⟩⟩, hS hX⟩
  · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hi.measure_lt_top
      (ENNReal.prod_lt_top fun v _ => (hv v).measure_lt_top)) ENNReal.ofReal_lt_top

theorem ne_zero (h : IsProd b ν mi mv) (hi : mi ≠ 0) (hv : ∀ v, mv v ≠ 0) : ν ≠ 0 := by
  obtain ⟨S, hS⟩ := exists_tailProd_ne_zero h.1
  have := measure_rect h S (Av := fun _ => Set.univ) MeasurableSet.univ fun _ => MeasurableSet.univ
  rintro rfl
  exact mul_ne_zero (mul_ne_zero (Measure.measure_univ_ne_zero.2 hi)
    (Finset.prod_ne_zero_iff.2 fun v _ => Measure.measure_univ_ne_zero.2 (hv v))) hS this.symm

theorem null (h : IsProd b ν mi mv) (Ai : Set (Fin n → Fin M → Ainf F ⊗[F] E))
    (Av : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hi : MeasurableSet Ai) (hv : ∀ v, MeasurableSet (Av v)) (zi : mi Aiᶜ = 0)
    (zv : ∀ v, mv v (Av v)ᶜ = 0) :
    ν {X | ¬ (projInf X ∈ Ai ∧ ∀ v, projV v (projFin X) ∈ Av v)} = 0 := by
  classical
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have h1 : ∀ S, ν ({X | projInf X ∈ Aiᶜ ∧ ∀ v ∈ S, projV v (projFin X) ∈ Set.univ} ∩ box b S) = 0 :=
    fun S => by
      rw [measure_rect h S (Av := fun _ => Set.univ) hi.compl fun _ => MeasurableSet.univ, zi,
        zero_mul, zero_mul]
  have h2 : ∀ (w : HeightOneSpectrum (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))),
      ν ({X | projInf X ∈ Set.univ ∧ ∀ v ∈ insert w S,
        projV v (projFin X) ∈ (if v = w then (Av v)ᶜ else Set.univ)} ∩ box b (insert w S)) = 0 :=
    fun w S => by
      rw [measure_rect h (insert w S) (Av := fun v => if v = w then (Av v)ᶜ else Set.univ)
        MeasurableSet.univ fun v => by
          split_ifs
          exacts [(hv v).compl, MeasurableSet.univ],
        Finset.prod_eq_zero (Finset.mem_insert_self w S) (by simpa using zv w), mul_zero, zero_mul]
  refine measure_mono_null (fun X hX => ?_) (measure_union_null (measure_iUnion_null h1)
    (measure_iUnion_null fun w => measure_iUnion_null (h2 w)))
  obtain ⟨S, hS⟩ := exists_mem_box b X
  rcases not_and_or.1 hX with h3 | h3
  · exact Or.inl (Set.mem_iUnion.2 ⟨S, ⟨h3, fun _ _ => trivial⟩, hS⟩)
  · obtain ⟨w, hw⟩ := not_forall.1 h3
    refine Or.inr (Set.mem_iUnion₂.2 ⟨w, S, ⟨trivial, fun v _ => ?_⟩,
      box_mono b (Finset.subset_insert w S) hS⟩)
    split_ifs with h4
    · subst h4; exact hw
    · trivial

end GlobalTheory.GaugeEx.ProdBasic

theorem GlobalTheory.GaugeEx.isProd_basic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsProd b ν mi mv → IsFiniteMeasureOnCompacts ν ∧ (mi ≠ 0 → (∀ v, mv v ≠ 0) → ν ≠ 0) ∧ (∀ ν', IsProd b ν' mi mv → ν' = ν) ∧ ∀ (Ai : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (Av : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), MeasurableSet Ai → (∀ v, MeasurableSet (Av v)) → mi Aiᶜ = 0 → (∀ v, mv v (Av v)ᶜ = 0) → ν {X | ¬ (projInf X ∈ Ai ∧ ∀ v, projV v (projFin X) ∈ Av v)} = 0 := by
  intro F E _ _ _ _ _ d b n M ν mi mv h
  refine ⟨ProdBasic.finiteOnCompacts h, ProdBasic.ne_zero h, fun ν' h' => ?_, ProdBasic.null h⟩
  refine GlobalTheory.T.adelicTupleMeasure_ext_of_pureTensor_integrals F E d b n M ν' ν fun Φ Φi Φf Φv h1 h2 h3 h4 => ?_
  have k := GlobalTheory.T.restrictedProduct_integral_pureTensor_eq_prod F E d b n M ν mi mv h d b Φ Φi Φf Φv h1 h2 h3 h4
  have k' := GlobalTheory.T.restrictedProduct_integral_pureTensor_eq_prod F E d b n M ν' mi mv h' d b Φ Φi Φf Φv h1 h2 h3 h4
  exact ⟨k'.1, k.1, k'.2.2.trans k.2.2.symm⟩
end

section

open NumberField IsDedekindDomain Formalism.L2.Pj

namespace GlobalTheory

theorem detSpan_conj_mul_mem_range (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (M M' : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ v ∈ M, ∀ w ∈ M', ∑ j, IsCMField.complexConj E (v j) * w j ∈ (algebraMap (𝓞 E) E).range) :
    ∀ x ∈ GlobalTheory.BetaEx.detSpan M, ∀ y ∈ GlobalTheory.BetaEx.detSpan M',
      IsCMField.complexConj E x * y ∈ (algebraMap (𝓞 E) E).range := by
  have hc : ∀ a : 𝓞 E, IsCMField.complexConj E (a : E) ∈ (algebraMap (𝓞 E) E).range := fun a =>
    ⟨IsCMField.ringOfIntegersComplexConj E a, IsCMField.coe_ringOfIntegersComplexConj E a⟩
  intro x hx y hy
  unfold GlobalTheory.BetaEx.detSpan at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := (GlobalTheory.BetaEx.mem_detSet M x).1 hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := (GlobalTheory.BetaEx.mem_detSet M' y).1 hy
      choose A hA using fun i k => h (v i) (hv i) (w k) (hw k)
      refine ⟨(Matrix.of A).det, ?_⟩
      have e1 : IsCMField.complexConj E v.det
          = ((IsCMField.complexConj E : E →+* E).mapMatrix v).det := by
        rw [← RingHom.map_det]; rfl
      rw [RingHom.map_det, e1, ← Matrix.det_transpose w, ← Matrix.det_mul]
      congr 1
      ext i k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
        Matrix.transpose_apply, hA]
      rfl
    | zero => simpa using Subring.zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact Subring.add_mem _ ha hb
    | smul a b _ hb =>
      rw [Algebra.smul_def, mul_left_comm]
      exact Subring.mul_mem _ ⟨a, rfl⟩ hb
  | zero => simpa using Subring.zero_mem _
  | add a b _ _ ha hb => rw [map_add (f := _), add_mul]; exact Subring.add_mem _ ha hb
  | smul a b _ hb =>
    rw [Algebra.smul_def, map_mul, mul_assoc]
    exact Subring.mul_mem _ (hc a) hb

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.ax_sen_tate_complex_padic_fixed_closure : ∀ (l : ℕ) [Fact l.Prime], ∀ (H : Subgroup (GQ l)) (x : ℂ_[l]), (∀ g ∈ H, Per.σC g x = x) → x ∈ closure ((fun y : Om l => (y : ℂ_[l])) '' {y | ∀ g ∈ H, g y = y}) := by
  first | exact @GlobalTheory.MemLoc.ax_sen_tate | exact GlobalTheory.MemLoc.ax_sen_tate | (intros; apply GlobalTheory.MemLoc.ax_sen_tate <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.quadraticChar_product_formula_CM_host : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (a : (H.F)ˣ), (∏ᶠ v : HeightOneSpectrum (𝓞 H.F), etaFin (L := H.E) H.F v a) * ∏ w : InfinitePlace H.F, etaInf H.F w a = 1 := by
  first | exact @GlobalTheory.EtaProduct.eta_product_formula | exact GlobalTheory.EtaProduct.eta_product_formula | (intros; apply GlobalTheory.EtaProduct.eta_product_formula <;> assumption)
end
