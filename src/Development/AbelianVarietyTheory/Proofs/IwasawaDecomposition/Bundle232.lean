module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle164
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeClassMeanTraceFormDualLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeOneEqResidue
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeSiegelStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle182
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle221
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Matrix
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.OfModel

section Values

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)

theorem valAt_algebraMap (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dif_pos h]
  exact congrArg _ (IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec)

theorem valAt_mul {f g : Z.functionField} (hf : RegAt (below y) f) (hg : RegAt (below y) g) :
    valAt y (f * g) = valAt y f * valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_mul]

theorem valAt_fnOf {U : Z.Opens} (hU : below y ∈ U) (h : ⊤ ≤ y ⁻¹ᵁ U) (a : Γ(Z, U)) :
    valAt y (fnOf U (gen_mem hU) a) =
      (y.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom a := by
  have e : Z.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of K) y =
      y.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  rw [← algebraMap_germ hU, valAt_algebraMap, ← e]
  rfl

end Values

theorem eval_pull {K O : Type} [CommRing K] [CommRing O] (φ : O →+* K) {X Z : Scheme.{0}} (j : Z ⟶ X)
    (y : Sp K ⟶ Z) (yt : Sp O ⟶ X) (e : spMap φ ≫ yt = y ≫ j) {U : X.Opens} {W : Z.Opens}
    (hW : W ≤ j ⁻¹ᵁ U) (h : ⊤ ≤ y ⁻¹ᵁ W) (ht : ⊤ ≤ yt ⁻¹ᵁ U) (a : Γ(X, U)) :
    (y.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom ((j.appLE U W hW).hom a) =
      φ ((yt.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of O)).hom).hom a) := by
  have e1 : j.appLE U W hW ≫ y.appLE W ⊤ h = yt.appLE U ⊤ ht ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    refine Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    simp only [e]
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have e3 : j.appLE U W hW ≫ y.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom =
      (yt.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of O)).hom) ≫ CommRingCat.ofHom φ := by
    rw [← Category.assoc, e1, Category.assoc, e2, Category.assoc]
  exact congrArg (fun ψ => ψ.hom a) e3

variable {F : Type} [Field F] [NumberField F]

variable {Y : Var F} (M : TrueGeo.Model Y) (B : LB M.X)

end GlobalTheory.TrueGeo.OfModel
end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.HaarFinVol

open GlobalTheory.FlagMeas

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def entP (y : GL (Fin j) (Cinf E)) : InfinitePlace E → Fin j → Fin j → ℂ :=
  fun w a b => (y : Matrix (Fin j) (Fin j) (Cinf E)) a b w

def ent (y : GL (Fin j) (Cinf E)) : MatInf E j := entP E j y

def swapH : Matrix (Fin j) (Fin j) (Cinf E) ≃ₜ (InfinitePlace E → Fin j → Fin j → ℂ) where
  toFun M w a b := M a b w
  invFun x := Matrix.of fun a b w => x w a b
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun w => continuous_pi fun a => continuous_pi fun b =>
    (continuous_apply w).comp ((continuous_apply b).comp (continuous_apply a))
  continuous_invFun := continuous_pi fun a => continuous_pi fun b => continuous_pi fun w =>
    (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply w))

theorem isOpenEmbedding_val :
    IsOpenEmbedding (Units.val : GL (Fin j) (Cinf E) → Matrix (Fin j) (Fin j) (Cinf E)) := by
  let _ := Matrix.linftyOpNormedRing (n := Fin j) (α := Cinf E)
  let _ := Matrix.linftyOpNormedAlgebra (n := Fin j) (R := ℂ) (α := Cinf E)
  have : CompleteSpace (Matrix (Fin j) (Fin j) (Cinf E)) := FiniteDimensional.complete ℂ _
  exact Units.isOpenEmbedding_val

theorem isOpenEmbedding_entP : IsOpenEmbedding (entP E j) :=
  (swapH E j).isOpenEmbedding.comp (isOpenEmbedding_val E j)

theorem ent_mul (x y : GL (Fin j) (Cinf E)) : ent E j (x * y) = ent E j x * ent E j y := by
  funext w a b
  change (((x * y : GL (Fin j) (Cinf E)) : Matrix (Fin j) (Fin j) (Cinf E)) a b w) =
    (Matrix.of (ent E j x w) * Matrix.of (ent E j y w)) a b
  rw [Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_apply]
  rfl

theorem detNorm_ent_pos (y : GL (Fin j) (Cinf E)) : 0 < _root_.GlobalTheory.FlagMeas.detNorm E j (ent E j y) := by
  unfold _root_.GlobalTheory.FlagMeas.detNorm
  refine Finset.prod_pos fun w _ => ?_
  have h1 : Matrix.of (ent E j y w) =
      (y : Matrix (Fin j) (Fin j) (Cinf E)).map (Pi.evalRingHom (fun _ => ℂ) w) := by
    ext a b; rfl
  have h2 : (Matrix.of (ent E j y w)).det = (y : Matrix (Fin j) (Fin j) (Cinf E)).det w := by
    rw [h1, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  have hu : IsUnit (y : Matrix (Fin j) (Fin j) (Cinf E)).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
  have h3 : (y : Matrix (Fin j) (Fin j) (Cinf E)).det w ≠ 0 :=
    (hu.map (Pi.evalRingHom (fun _ => ℂ) w)).ne_zero
  rw [h2]
  positivity

theorem haarGL_lt_top_of_isCompact (S : Set (InfinitePlace E → Fin j → Fin j → ℂ)) (hS : IsCompact S)
    (hpos : ∀ x ∈ S, 0 < _root_.GlobalTheory.FlagMeas.detNorm E j x) : haarGL E j S < ⊤ := by
  have hd : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => _root_.GlobalTheory.FlagMeas.detNorm E j x :=
    GlobalTheory.HaarLeftInv.continuous_detNorm E j
  haveI := GlobalTheory.HaarLeftInv.isAddHaar_volume E j
  rcases S.eq_empty_or_nonempty with h | h
  · subst h; exact (measure_empty (μ := haarGL E j)).trans_lt ENNReal.zero_lt_top
  obtain ⟨x0, hx0, hmin⟩ := hS.exists_isMinOn h hd.continuousOn
  have hm := hpos x0 hx0
  show Measure.withDensity (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))
    (fun x => ENNReal.ofReal ((_root_.GlobalTheory.FlagMeas.detNorm E j x)⁻¹ ^ j)) S < ⊤
  rw [withDensity_apply _ hS.isClosed.measurableSet]
  refine (setLIntegral_mono' hS.isClosed.measurableSet
    (g := fun _ => ENNReal.ofReal ((_root_.GlobalTheory.FlagMeas.detNorm E j x0)⁻¹ ^ j)) fun x hx => ?_).trans_lt ?_
  · exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (inv_nonneg.2 (hpos x hx).le)
      (inv_anti₀ hm (hmin hx)) j)
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS.measure_lt_top

theorem haarGL_ne_zero_of_isOpen (S : Set (InfinitePlace E → Fin j → Fin j → ℂ)) (hS : IsOpen S)
    (hne : S.Nonempty) (hpos : ∀ x ∈ S, 0 < _root_.GlobalTheory.FlagMeas.detNorm E j x) : haarGL E j S ≠ 0 := by
  have hd : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => _root_.GlobalTheory.FlagMeas.detNorm E j x :=
    GlobalTheory.HaarLeftInv.continuous_detNorm E j
  haveI := GlobalTheory.HaarLeftInv.isAddHaar_volume E j
  show Measure.withDensity (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))
    (fun x => ENNReal.ofReal ((_root_.GlobalTheory.FlagMeas.detNorm E j x)⁻¹ ^ j)) S ≠ 0
  have hf : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => ENNReal.ofReal ((_root_.GlobalTheory.FlagMeas.detNorm E j x)⁻¹ ^ j) :=
    ((hd.measurable.inv).pow_const j).ennreal_ofReal
  rw [Ne, withDensity_apply_eq_zero' hf.aemeasurable]
  have : {x : InfinitePlace E → Fin j → Fin j → ℂ | ENNReal.ofReal ((_root_.GlobalTheory.FlagMeas.detNorm E j x)⁻¹ ^ j) ≠ 0} ∩ S = S :=
    Set.inter_eq_right.2 fun x hx => (ENNReal.ofReal_pos.2 (pow_pos (inv_pos.2 (hpos x hx)) j)).ne'
  rw [this]
  exact hS.measure_ne_zero volume hne

theorem haarGL_image_mul (a : MatInf E j) (ha : 0 < _root_.GlobalTheory.FlagMeas.detNorm E j a) (T : Set (MatInf E j)) :
    haarGL E j ((fun g => a * g) '' T) = haarGL E j T := by
  obtain ⟨hemb, hmp⟩ := GlobalTheory.HaarLeftInv.measurePreserving_mul_left E j a ha
  have := hemb.map_apply (haarGL E j) ((fun g => a * g) '' T)
  rw [hmp.map_eq, Set.preimage_image_eq T hemb.injective] at this
  exact this

variable [MeasurableSpace (GL (Fin j) (Cinf E))] [BorelSpace (GL (Fin j) (Cinf E))]

theorem measurableEmbedding_ent : MeasurableEmbedding (ent E j) :=
  (isOpenEmbedding_entP E j).measurableEmbedding

def nuGL : Measure (GL (Fin j) (Cinf E)) := (haarGL E j).comap (ent E j)

theorem nuGL_apply (s : Set (GL (Fin j) (Cinf E))) : nuGL E j s = haarGL E j (ent E j '' s) :=
  (measurableEmbedding_ent E j).comap_apply _ s

theorem isHaarMeasure_nuGL : (nuGL E j).IsHaarMeasure := by
  have he := isOpenEmbedding_entP E j
  refine { lt_top_of_isCompact := ?_, map_mul_left_eq_self := ?_, open_pos := ?_ }
  · intro K hK
    rw [nuGL_apply]
    refine haarGL_lt_top_of_isCompact E j (entP E j '' K) (hK.image he.continuous) ?_
    rintro _ ⟨y, -, rfl⟩
    exact detNorm_ent_pos E j y
  · intro g
    ext s hs
    rw [Measure.map_apply (measurable_const_mul g) hs, nuGL_apply, nuGL_apply]
    have e1 : (fun h => g * h) ⁻¹' s = (fun h => g⁻¹ * h) '' s := by
      ext y; simp [Set.mem_image, eq_inv_mul_iff_mul_eq]
    have e2 : ent E j '' ((fun h => g⁻¹ * h) '' s) =
        (fun x : MatInf E j => ent E j g⁻¹ * x) '' (ent E j '' s) := by
      rw [Set.image_image, Set.image_image]
      exact Set.image_congr fun y _ => ent_mul E j g⁻¹ y
    rw [e1, e2, haarGL_image_mul E j _ (detNorm_ent_pos E j g⁻¹)]
  · intro U hU hne
    rw [nuGL_apply]
    refine haarGL_ne_zero_of_isOpen E j (entP E j '' U) (he.isOpenMap U hU) (hne.image _) ?_
    rintro _ ⟨y, -, rfl⟩
    exact detNorm_ent_pos E j y

end GlobalTheory.HaarFinVol

theorem GlobalTheory.haarGL_finite_pullback : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) [MeasurableSpace (GL (Fin j) (Cinf E))] [BorelSpace (GL (Fin j) (Cinf E))] (ν : Measure (GL (Fin j) (Cinf E))) [ν.IsHaarMeasure] (D : Set (GlobalTheory.FlagMeas.MatInf E j)), MeasurableSet D → GlobalTheory.FlagMeas.haarGL E j D < ⊤ → ν {y | (fun w a b => (y : Matrix (Fin j) (Fin j) (Cinf E)) a b w : GlobalTheory.FlagMeas.MatInf E j) ∈ D} < ⊤ := by
  intro E _ _ j _ _ ν _ D _ hD
  haveI := GlobalTheory.HaarFinVol.isHaarMeasure_nuGL E j
  have he := GlobalTheory.HaarFinVol.isOpenEmbedding_entP E j
  haveI : LocallyCompactSpace (GL (Fin j) (Cinf E)) := he.locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin j) (Cinf E)) := he.isEmbedding.secondCountableTopology
  have h2 : GlobalTheory.HaarFinVol.nuGL E j {y | (fun w a b => (y : Matrix (Fin j) (Fin j) (Cinf E)) a b w :
      GlobalTheory.FlagMeas.MatInf E j) ∈ D} ≤ GlobalTheory.FlagMeas.haarGL E j D :=
    (GlobalTheory.HaarFinVol.nuGL_apply E j _).trans_le (measure_mono fun _ ⟨_, hy, e⟩ => e ▸ hy)
  rw [Measure.isMulLeftInvariant_eq_smul ν (GlobalTheory.HaarFinVol.nuGL E j), Measure.smul_apply,
    ENNReal.smul_def, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (h2.trans_lt hD)
end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.SlabFinVol

open GlobalTheory.FlagMeas GlobalTheory.MeanDual

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

theorem covol_le_of_mul_left (Γ Γ' : Set (MatInf E j)) (h : MatInf E j) (hh : 0 < _root_.GlobalTheory.FlagMeas.detNorm E j h)
    (A B : Set (MatInf E j)) (hAB : ∀ x ∈ A, h * x ∈ B)
    (hΓ : ∀ δ ∈ Γ', ∃ δ₀ ∈ Γ, ∀ x, h * (δ₀ * x) = δ * (h * x)) :
    covol Γ (haarGL E j) A ≤ covol Γ' (haarGL E j) B := by
  unfold covol
  refine le_iInf fun D' => le_iInf fun hD' => le_iInf fun hc => ?_
  have hmeas : Measurable (fun g : MatInf E j => h * g) :=
    (GlobalTheory.MeanDual.measurePreserving_mul_left E j h hh).measurable
  refine iInf_le_of_le ((fun g => h * g) ⁻¹' D') (iInf_le_of_le (hmeas hD') (iInf_le_of_le ?_ ?_))
  · intro x hx
    obtain ⟨δ, hδ, hx'⟩ := hc (h * x) (hAB x hx)
    obtain ⟨δ₀, hδ₀, H⟩ := hΓ δ hδ
    refine ⟨δ₀, hδ₀, ?_⟩
    show h * (δ₀ * x) ∈ D'
    rw [H]; exact hx'
  · rw [← Measure.map_apply hmeas hD', GlobalTheory.OrbitTerm.map_haarGL_mul_left_eq E j h hh]

def scal (r : ℝ) : MatInf E j := fun _ a b => if a = b then (r : ℂ) else 0

theorem of_scal (r : ℝ) (w : InfinitePlace E) :
    Matrix.of (scal E j r w) = (r : ℂ) • (1 : Matrix (Fin j) (Fin j) ℂ) := by
  ext a b
  simp [scal, Matrix.one_apply]

theorem scal_mul_comm (r : ℝ) (δ x : MatInf E j) : scal E j r * (δ * x) = δ * (scal E j r * x) := by
  apply matInf_ext
  intro w
  simp only [of_mul, of_scal, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]

theorem detNorm_scal (r : ℝ) (hr : 0 < r) :
    _root_.GlobalTheory.FlagMeas.detNorm E j (scal E j r) = (r ^ (2 * j)) ^ Fintype.card (InfinitePlace E) := by
  unfold _root_.GlobalTheory.FlagMeas.detNorm
  simp only [of_scal, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  rw [Finset.prod_const, Finset.card_univ]
  congr 1
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, ← pow_mul, mul_comm]

theorem exists_scal (hj : 1 ≤ j) (c : ℝ) (hc : 0 < c) : ∃ r : ℝ, 0 < r ∧ _root_.GlobalTheory.FlagMeas.detNorm E j (scal E j r) = c := by
  have hN : Fintype.card (InfinitePlace E) ≠ 0 := Fintype.card_ne_zero
  refine ⟨c ^ (((2 * j * Fintype.card (InfinitePlace E) : ℕ) : ℝ))⁻¹, Real.rpow_pos_of_pos hc _, ?_⟩
  rw [detNorm_scal E j _ (Real.rpow_pos_of_pos hc _), ← pow_mul]
  exact Real.rpow_inv_natCast_pow hc.le (by positivity)

def slab (c : ℝ) : Set (MatInf E j) := {x | c ≤ _root_.GlobalTheory.FlagMeas.detNorm E j x ∧ _root_.GlobalTheory.FlagMeas.detNorm E j x < c * Real.exp 1}

theorem covol_slab_le (hj : 1 ≤ j) (Λ : Submodule (𝓞 E) (Fin j → E)) (c : ℝ) (hc : 0 < c) :
    covol (autGL E j Λ) (haarGL E j) (slab E j c) ≤
      covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ _root_.GlobalTheory.FlagMeas.detNorm E j x ∧ _root_.GlobalTheory.FlagMeas.detNorm E j x < Real.exp 1} := by
  obtain ⟨r, hr, hd⟩ := exists_scal E j hj c⁻¹ (inv_pos.2 hc)
  refine covol_le_of_mul_left E j _ _ (scal E j r) (hd ▸ inv_pos.2 hc) _ _ ?_
    (fun δ hδ => ⟨δ, hδ, fun x => scal_mul_comm E j r δ x⟩)
  rintro x ⟨h1, h2⟩
  simp only [Set.mem_setOf_eq, detNorm_mul, hd]
  constructor
  · rw [inv_mul_eq_div, le_div_iff₀ hc, one_mul]; exact h1
  · rw [inv_mul_eq_div, div_lt_iff₀ hc, mul_comm]; exact h2

theorem covol_le_of_carries {γ : GL (Fin j) E} {Λ Λ' : Submodule (𝓞 E) (Fin j → E)} (h : Carries E j γ Λ Λ') :
    covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ _root_.GlobalTheory.FlagMeas.detNorm E j x ∧ _root_.GlobalTheory.FlagMeas.detNorm E j x < Real.exp 1} ≤
      covol (autGL E j Λ') (haarGL E j) (slab E j (_root_.GlobalTheory.FlagMeas.detNorm E j (embInf E j γ))) := by
  refine covol_le_of_mul_left E j _ _ (embInf E j γ) (detNorm_embInf E j γ) _ _ ?_ ?_
  · rintro x ⟨h1, h2⟩
    simp only [slab, Set.mem_setOf_eq, detNorm_mul]
    have hp := detNorm_embInf E j γ
    exact ⟨le_mul_of_one_le_right hp.le h1, mul_lt_mul_of_pos_left h2 hp⟩
  · intro x hx
    obtain ⟨δ, hδ, rfl⟩ := (mem_autGL E j).1 hx
    refine ⟨embInf E j (γ⁻¹ * δ * γ), (mem_autGL E j).2 ⟨_, (h.inv.mul hδ).mul h, rfl⟩, fun x => ?_⟩
    apply matInf_ext
    intro w
    simp only [of_mul, embInf_mul, ← Matrix.mul_assoc]
    have := embInf_inv_mul E j γ⁻¹ w
    rw [inv_inv] at this
    rw [this, Matrix.one_mul]

theorem glVol_lt_top (hE : IsTotallyComplex E) : ∀ j : ℕ, 1 ≤ j → glVol E j < ⊤ := by
  intro j hj
  induction j with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [GlobalTheory.NormOneVol.glVol_one E hE]; exact ENNReal.ofReal_lt_top
    · have h := ih hn
      have hs := GlobalTheory.FlagBase.SiegelStep.glVol_step E hE (n + 1) (by omega) (by simpa using h)
      rw [hs]
      simp only [Nat.add_sub_cancel] at h ⊢
      exact ENNReal.mul_lt_top h ENNReal.ofReal_lt_top

end GlobalTheory.SlabFinVol


open GlobalTheory.FlagMeas GlobalTheory.MeanDual in
theorem GlobalTheory.SlabFinVol.covol_unitSlab_lt_top : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 1 ≤ j → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsFullLattice E Λ → GlobalTheory.FlagMeas.covol (GlobalTheory.FlagMeas.autGL E j Λ) (GlobalTheory.FlagMeas.haarGL E j) {x | 1 ≤ GlobalTheory.FlagMeas.detNorm E j x ∧ GlobalTheory.FlagMeas.detNorm E j x < Real.exp 1} < ⊤ := by
  intro E _ _ hE j hj Λ hΛ
  have hfin := GlobalTheory.SlabFinVol.glVol_lt_top E hE j hj
  let R : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsFullLattice E Λ} →
      {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsFullLattice E Λ} → Prop :=
    fun Λ Λ' => ∃ γ : GL (Fin j) E, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1
  have hle : _ ≤ glVol E j := ENNReal.le_tsum (Quot.mk R ⟨Λ, hΛ⟩)
  have hrel := Quot.eqvGen_exact (Quot.out_eq (Quot.mk R ⟨Λ, hΛ⟩))
  have key : ∀ a b, Relation.EqvGen R a b →
      ∃ γ : GL (Fin j) E, Carries E j γ a.1 b.1 := by
    intro a b hab
    induction hab with
    | rel x y h => exact h
    | refl x => exact ⟨1, fun y => by simp⟩
    | symm x y _ ih => obtain ⟨γ, h⟩ := ih; exact ⟨γ⁻¹, h.inv⟩
    | trans x y z _ _ ih1 ih2 =>
      obtain ⟨γ, h⟩ := ih1; obtain ⟨δ, h'⟩ := ih2; exact ⟨δ * γ, h'.mul h⟩
  obtain ⟨γ, hγ⟩ := key _ _ hrel
  exact lt_of_le_of_lt ((covol_le_of_carries E j hγ.inv).trans
    (GlobalTheory.SlabFinVol.covol_slab_le E j hj _ _ (detNorm_embInf E j _))) (lt_of_le_of_lt hle hfin)
end
end

section

noncomputable section

open Matrix

namespace GlobalTheory.DefLift.ColComb

variable {ι : Type} {m n : ℕ}

def sw (ι : Type) (m n : ℕ) : ι × Fin m × Fin n → ι × Fin n × Fin m := fun v => (v.1, v.2.2, v.2.1)

theorem sw_sw (v : ι × Fin m × Fin n) : sw ι n m (sw ι m n v) = v := rfl

theorem sw_injective : Function.Injective (sw ι m n) := Function.LeftInverse.injective sw_sw

theorem rename_subst (a : ι → Matrix (Fin m) (Fin m) ℂ) (b : ι → Matrix (Fin n) (Fin n) ℂ) (Q : Pol ι n m) :
    MvPolynomial.rename (sw ι n m) (subst a b Q) =
      subst (fun ρ => (b ρ)ᵀ) (fun ρ => (a ρ)ᵀ) (MvPolynomial.rename (sw ι n m) Q) := by
  have : (MvPolynomial.rename (sw ι n m)).comp (subst a b) =
      (subst (fun ρ => (b ρ)ᵀ) (fun ρ => (a ρ)ᵀ)).comp (MvPolynomial.rename (sw ι n m)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨ρ, c, i⟩

    simp only [subst, AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.rename_X, map_sum, map_smul, sw,
    Matrix.transpose_apply]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  exact AlgHom.congr_fun this Q

def cj (u : Matrix.unitaryGroup (Fin n) ℂ) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨star (u : Matrix (Fin n) (Fin n) ℂ)ᵀ, by
    rw [Matrix.mem_unitaryGroup_iff', star_star]
    have h : star (u : Matrix (Fin n) (Fin n) ℂ) * u = 1 := Matrix.mem_unitaryGroup_iff'.1 u.2
    have e : star (u : Matrix (Fin n) (Fin n) ℂ)ᵀ = (star (u : Matrix (Fin n) (Fin n) ℂ))ᵀ := rfl
    rw [e, ← Matrix.transpose_mul, h, Matrix.transpose_one]⟩

theorem cj_cj (u : Matrix.unitaryGroup (Fin n) ℂ) : cj (cj u) = u := by
  apply Subtype.ext
  ext i j
  simp [cj]

theorem rename_rowSub (τ : ι) (u : Matrix.unitaryGroup (Fin n) ℂ) (Q : Pol ι n m) :
    MvPolynomial.rename (sw ι n m) (rowSub m τ u Q) = colSub m τ (cj u) (MvPolynomial.rename (sw ι n m) Q) := by
  simp only [rowSub, colSub, AlgHom.toLinearMap_apply, rename_subst]
  congr 2
  · funext ρ
    split_ifs <;> simp [cj]
  · funext ρ
    simp

theorem rename_rowLie (τ : ι) (k l : Fin n) (Q : Pol ι n m) :
    MvPolynomial.rename (sw ι n m) (rowLie m τ k l Q) = colLie m τ k l (MvPolynomial.rename (sw ι n m) Q) := by

  rw [rowLie_apply, colLie_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, MvPolynomial.rename_X, ← MvPolynomial.pderiv_rename sw_injective]
  rfl

end GlobalTheory.DefLift.ColComb

namespace GlobalTheory.DefLift


open ColComb in
theorem colLie_eq_sum_colSub : ∀ (ι : Type) [Fintype ι] (m n d : ℕ) (τ : ι) (k l : Fin n),
    ∃ (s : Finset (Matrix.unitaryGroup (Fin n) ℂ)) (c : Matrix.unitaryGroup (Fin n) ℂ → ℂ),
      ∀ P : Pol ι m n, P.totalDegree ≤ d → ∑ g ∈ s, c g • colSub m τ g P = colLie m τ k l P := by
  intro ι _ m n d τ k l
  obtain ⟨s, c, h⟩ := GlobalTheory.T.exists_sum_unitarySubstitutions_eq_rowLie ι n m d τ k l
  refine ⟨s.map ⟨cj, Function.LeftInverse.injective cj_cj⟩, fun g => c (cj g), fun P hP => ?_⟩
  have e : MvPolynomial.rename (sw ι n m) (MvPolynomial.rename (sw ι m n) P) = P := by
    rw [MvPolynomial.rename_rename]
    exact MvPolynomial.rename_id_apply P
  have h1 := congrArg (MvPolynomial.rename (sw ι n m))
    (h (MvPolynomial.rename (sw ι m n) P) ((MvPolynomial.totalDegree_rename_le _ _).trans hP))

  rw [rename_rowLie, map_sum, e] at h1
  rw [← h1, Finset.sum_map]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_smul, rename_rowSub, e]
  simp [cj_cj]

end GlobalTheory.DefLift

end
end
