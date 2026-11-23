module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1454
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjIntegralIffLatticeUnimodular
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
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1214
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ConsEta

def unitDir : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) (div_ne_zero z.ne_zero (by simp))
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    field_simp

variable (E : Type) [Field E] [NumberField E]

def infSign : Neutral.B1.Ideles E →* ℂˣ :=
  ∏ w : InfinitePlace E, unitDir.comp ((Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom).comp
    (Units.map (GlobalTheory.IdeleNormChar.infEval w)))

def conjQuot [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) : Neutral.B1.Ideles E →* (w.adicCompletion E)ˣ :=
  (Units.map (GlobalTheory.IdeleNormChar.finEval w)).comp
    (MonoidHom.id _ / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E)

theorem norm_unitDir (z : ℂˣ) : ‖((unitDir z : ℂˣ) : ℂ)‖ = 1 := by
  change ‖(z : ℂ) / (‖(z : ℂ)‖ : ℂ)‖ = 1
  rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 z.ne_zero)]

theorem norm_infSign (x : Neutral.B1.Ideles E) : ‖((infSign E x : ℂˣ) : ℂ)‖ = 1 := by
  rw [infSign, MonoidHom.finsetProd_apply, Units.coe_prod, norm_prod]
  exact Finset.prod_eq_one fun w _ => norm_unitDir _

end GlobalTheory.ConsEta

namespace GlobalTheory.ConsEta
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem nsUnits_le_unitIdl : GlobalTheory.MuExist.nsUnits E ≤ GlobalTheory.Mem.Chr.unitIdl E := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨w, u, -, hu, rfl⟩ v
  by_cases hv : v = w
  · subst hv
    rw [Neutral.B1.localIdele_snd_self]; exact hu
  · rw [((Neutral.B1.localIdele_isSupportedAt E w u).2 v hv)]; exact map_one _

theorem infSign_localIdele (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ) :
    infSign E (Neutral.B1.localIdele E w u) = 1 := by
  rw [infSign, MonoidHom.finsetProd_apply]
  refine Finset.prod_eq_one fun v _ => ?_
  have : Units.map (GlobalTheory.IdeleNormChar.infEval v) (Neutral.B1.localIdele E w u) = 1 := Units.ext rfl
  simp only [MonoidHom.comp_apply, this, map_one]

theorem infSign_nsUnits {u : Neutral.B1.Ideles E} (hu : u ∈ GlobalTheory.MuExist.nsUnits E) : infSign E u = 1 := by
  have : GlobalTheory.MuExist.nsUnits E ≤ (infSign E).ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨w, u, -, -, rfl⟩
    exact infSign_localIdele w u
  exact this hu

theorem commGroup_div_eq_mul_div_mul_inv_div {G : Type} [CommGroup G] (d dc i u cu : G) :
    d / dc = (d * i * u) / (dc * i * cu) * (u / cu)⁻¹ := by
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  rw [show d * i * u * (dc⁻¹ * i⁻¹ * cu⁻¹) * (u⁻¹ * cu) = d * dc⁻¹ * (i * i⁻¹) * (u * u⁻¹) * (cu⁻¹ * cu) by ac_rfl]
  simp

theorem continuous_unitDir : Continuous unitDir := by
  have h1 : Continuous fun z : ℂˣ => ((unitDir z : ℂˣ) : ℂ) := by
    change Continuous fun z : ℂˣ => (z : ℂ) / (‖(z : ℂ)‖ : ℂ)
    exact Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm)
      fun z => by simp
  refine Units.continuous_iff.2 ⟨h1, ?_⟩
  have h2 : (fun z : ℂˣ => (((unitDir z)⁻¹ : ℂˣ) : ℂ)) = fun z => ((unitDir z⁻¹ : ℂˣ) : ℂ) := by
    funext z; rw [map_inv]
  change Continuous fun z : ℂˣ => (((unitDir z)⁻¹ : ℂˣ) : ℂ)
  rw [h2]
  exact h1.comp continuous_inv

theorem continuous_infSign : Continuous (infSign E) := by
  rw [infSign]
  have : ⇑(∏ w : InfinitePlace E, unitDir.comp ((Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom).comp
      (Units.map (GlobalTheory.IdeleNormChar.infEval w)))) = fun x => ∏ w : InfinitePlace E, unitDir
        (Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom
          (Units.map (GlobalTheory.IdeleNormChar.infEval (K := E) w) x)) := by
    funext x; rw [MonoidHom.finsetProd_apply]; rfl
  rw [this]
  refine continuous_finsetProd _ fun w _ => continuous_unitDir.comp ?_
  refine Continuous.units_map _ ?_ |>.comp (Continuous.units_map _ ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
  · exact (continuous_apply w).comp continuous_fst

theorem continuous_conjQuot (w : HeightOneSpectrum (𝓞 E)) : Continuous (conjQuot E w) := by
  have hC : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E) :=
    @GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap E E _ _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  refine (Continuous.units_map _ ?_).comp (continuous_id.div' hC)
  exact (RestrictedProduct.continuous_eval w).comp continuous_snd

end GlobalTheory.ConsEta
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.IntegralDetModule

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def bas (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    Module.Basis (Σ _ : Fin n, Fin (Module.finrank F E)) (AF F) (Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  Pi.basis fun _ => (Module.finBasis F E).baseChange (AF F)

def big {n : ℕ} (t : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    Matrix (Σ _ : Fin n, Fin (Module.finrank F E)) (Σ _ : Fin n, Fin (Module.finrank F E)) (AF F) :=
  LinearMap.toMatrix (bas F E n) (bas F E n) ((Matrix.toLin' t).restrictScalars (AF F))

theorem big_apply {n : ℕ} (t : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (x y) :
    big t x y = (bas F E n).repr (t *ᵥ bas F E n y) x := by
  rw [big, LinearMap.toMatrix_apply]
  rfl

theorem det_big {n : ℕ} (t : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    (big t).det = Algebra.norm (AF F) t.det := by
  rw [big, LinearMap.det_toMatrix, LinearMap.det_restrictScalars, LinearMap.det_toLin']

theorem bas_eq {n : ℕ} (x) :
    bas F E n x = fun i => inclR (F := F) (AF F) ((Pi.single x.1 (Module.finBasis F E x.2) : Fin n → E) i) := by
  rw [bas, Pi.basis_apply]
  funext i
  by_cases h : i = x.1
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same, Module.Basis.baseChange_apply]
    rfl
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

theorem map_norm_det {n : ℕ} {K : Type} [CommRing K] (φ : AF F →+* K) (t : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (u : AF F) (hu : φ u = 1) (ht : u • (t - 1) = 0) : φ (Algebra.norm (AF F) t.det) = 1 := by
  rw [← det_big, RingHom.map_det]
  have : φ.mapMatrix (big t) = 1 := by
    ext x y
    have h1 : u • (t *ᵥ bas F E n y) = u • bas F E n y := by
      have h2 : (u • (t - 1)) *ᵥ bas F E n y = 0 := by rw [ht, Matrix.zero_mulVec]
      rwa [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, smul_sub, sub_eq_zero] at h2
    have h3 := congrArg (fun z => φ ((bas F E n).repr z x)) h1
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hu, one_mul, Module.Basis.repr_self] at h3
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, big_apply, h3, Matrix.one_apply, Finsupp.single_apply]
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h]
  rw [this, Matrix.det_one]

theorem exists_bound {n : ℕ} (W : Spc F E n) (hL : W.L.FG) (v : Pl (F := F)) :
    ∃ C : ℝ, ∀ z ∈ GlobalTheory.InertSph.latAt W v, ∀ x, ‖evFin F v ((bas F E n).repr z x)‖ ≤ C := by
  first
  | exact @_root_.GlobalTheory.CoordinateEmbeddingMaps.main
  | exact _root_.GlobalTheory.CoordinateEmbeddingMaps.main
  | (apply _root_.GlobalTheory.CoordinateEmbeddingMaps.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoordinateEmbeddingMaps.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoordinateEmbeddingMaps.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoordinateEmbeddingMaps.main ..)

theorem exists_mul_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E) (y : Fin n → E) :
    ∃ D : ℤ, D ≠ 0 ∧ D • y ∈ L := by
  exact _root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice L hL y

theorem exists_entry_bound {n : ℕ} (W : Spc F E n) (hL : W.L.IsFullLattice E) (v : Pl (F := F)) :
    ∃ C : ℝ, ∀ t : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      (∀ z ∈ GlobalTheory.InertSph.latAt W v, t *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) → ∀ x y, ‖evFin F v (big t x y)‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound W hL.fg v
  choose D hD0 hD using fun x : (Σ _ : Fin n, Fin (Module.finrank F E)) =>
    exists_mul_mem W.L hL (Pi.single x.1 (Module.finBasis F E x.2))
  haveI : CharZero (Fv F v) := algebraRat.charZero _
  refine ⟨∑ y, |C| / ‖(D y : Fv F v)‖, fun t ht x y => ?_⟩
  set e := GlobalTheory.EmbChart.atPlace v (1 : Fv F v) with he
  have he1 : evFin F v e = 1 := GlobalTheory.EmbChart.evFin_atPlace v 1
  have hmem : e • (D y • bas F E n y) ∈ GlobalTheory.InertSph.latAt W v := by
    refine AddSubgroup.subset_closure ⟨e, ?_, ?_, _, hD y, ?_⟩
    · intro u hu
      rw [smul_eq_mul, mul_comm, he, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]
    · rw [he1]; exact one_mem _
    · rw [bas_eq]
      congr 1
      funext i
      simp only [Pi.smul_apply, map_zsmul]
  have h1 := hC _ (ht _ hmem) x
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, map_smul, map_zsmul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul,
    map_mul, he1, one_mul, map_zsmul, zsmul_eq_mul, norm_mul, ← big_apply] at h1
  have hpos : 0 < ‖(D y : Fv F v)‖ := norm_pos_iff.2 (Int.cast_ne_zero.2 (hD0 y))
  calc ‖evFin F v (big t x y)‖ ≤ |C| / ‖(D y : Fv F v)‖ := by
        rw [le_div_iff₀ hpos, mul_comm]; exact h1.trans (le_abs_self C)
    _ ≤ _ := Finset.single_le_sum (f := fun y => |C| / ‖(D y : Fv F v)‖)
        (fun y _ => div_nonneg (abs_nonneg _) (norm_nonneg _)) (Finset.mem_univ y)

theorem norm_le_one {n : ℕ} (W : Spc F E n) (hL : W.L.IsFullLattice E) (v : Pl (F := F)) (t : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (ht : ∀ z ∈ GlobalTheory.InertSph.latAt W v, t *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    ‖evFin F v (Algebra.norm (AF F) t.det)‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := exists_entry_bound W hL v
  have hk : ∀ k : ℕ, ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t ^ k) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
    intro k
    induction k with
    | zero => intro z hz; simpa using hz
    | succ k ih => intro z hz; rw [pow_succ, ← Matrix.mulVec_mulVec]; exact ih _ (ht z hz)
  have hb : ∃ B : ℝ, ∀ k : ℕ, ‖evFin F v (Algebra.norm (AF F) t.det)‖ ^ k ≤ B := by
    refine ⟨(Fintype.card (Σ _ : Fin n, Fin (Module.finrank F E))).factorial •
      C ^ Fintype.card (Σ _ : Fin n, Fin (Module.finrank F E)), fun k => ?_⟩
    rw [← norm_pow, ← map_pow, ← map_pow, ← Matrix.det_pow, ← det_big]
    have := Matrix.det_le (abv := (NormedField.toAbsoluteValue (Fv F v))) (A := (big (t ^ k)).map (evFin F v)) (x := C)
      (fun x y => hC _ (hk k) x y)
    have e : evFin F v (big (t ^ k)).det = ((big (t ^ k)).map (evFin F v)).det :=
      RingHom.map_det (evFin F v).toRingHom _
    rw [e]
    exact this
  obtain ⟨B, hB⟩ := hb
  by_contra h
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (not_le.1 h)).eventually_gt_atTop B).exists
  exact absurd (hB k) (not_le.2 hk)

theorem modu_eq_one (a : (AF F)ˣ) (h1 : (a : AF F).1 = 1) (h2 : ∀ v, ‖evFin F v a‖ = 1) :
    (adeleClass F).modu a = 1 := by
  apply NNReal.eq
  change (MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ) = _
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have h3 : ∀ v : HeightOneSpectrum (𝓞 F), ‖(a : AF F).2 v‖ = 1 := h2
  have h4 : ∀ w : InfinitePlace F, ‖(a : AF F).1 w‖ = 1 := fun w => by
    rw [h1]; exact norm_one
  simp only [h3, h4, one_pow, Finset.prod_const_one, finprod_one, mul_one, NNReal.coe_one]

theorem modu_norm_det {n : ℕ} (W : Spc F E n) (hL : W.L.IsFullLattice E) (v : Pl (F := F)) (t : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (h1 : At (evFin F v) ((t : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1))
    (h2 : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
      ((t⁻¹ : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    (adeleClass F).modu (Units.map (Algebra.norm (AF F) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →* AF F) (Matrix.GeneralLinearGroup.det t)) = 1 := by
  have h0 := h1 (1 - GlobalTheory.EmbChart.atPlace v 1) (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  apply modu_eq_one
  · refine map_norm_det (fstA F).toRingHom _ _ ?_ h0
    rw [map_sub, map_one, sub_eq_self]
    rfl
  · intro u
    by_cases hu : u = v
    · subst hu
      have a1 := norm_le_one W hL u _ fun z hz => (h2 z hz).1
      have a2 := norm_le_one W hL u _ fun z hz => (h2 z hz).2
      have a3 : ‖evFin F u (Algebra.norm (AF F) (t : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).det)‖ *
          ‖evFin F u (Algebra.norm (AF F) ((t⁻¹ : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).det)‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one, map_one, norm_one]
      refine le_antisymm a1 ?_
      rw [← a3]
      exact mul_le_of_le_one_right (norm_nonneg _) a2
    · have := map_norm_det (evFin F u).toRingHom _ _ (by
        rw [map_sub, map_one, sub_eq_self]
        exact evalV_singleFin_ne hu 1) h0
      exact (congrArg norm this).trans norm_one

end GlobalTheory.IntegralDetModule

theorem GlobalTheory.IntegralDetModule.modu_norm_det_triple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v _ _ _ t ht
  exact GlobalTheory.IntegralDetModule.modu_norm_det G.W hT.geo.hW.lat v t ht.1 ht.2

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.CurveNbhdExcision

theorem ht_subsingleton_of_subsingleton (q : ℕ) (Z : Type) [CommRing Z] [Subsingleton Z] (n i : ℤ) :
    Subsingleton (Ht q (sp Z) n i) := by
  refine ⟨fun a b => ?_⟩
  have hfs : RingHom.fst Z Z = RingHom.snd Z Z := RingHom.ext fun _ => Subsingleton.elim _ _
  have key : ∀ z : Ht q (sp Z) n i, z = 0 := by
    intro z
    obtain ⟨y, hy⟩ := (GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q Z Z n i).2 (z, 0)
    simp only [Prod.mk.injEq] at hy
    rw [← hy.1, ← hy.2, hfs]
  rw [key a, key b]

theorem away_zero_subsingleton (B : Type) [CommRing B] : Subsingleton (Localization.Away (0 : B)) := by
  have h : IsUnit (algebraMap B (Localization.Away (0 : B)) 0) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_zero, isUnit_zero_iff] at h
  exact subsingleton_of_zero_eq_one h

theorem main : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (n i : ℤ), 0 < n → ∀ x : Ht q (sp B) n i, ∃ (A' : Type) (_ : CommRing A') (_ : Algebra B A'), IsExcisionNbhd B A' f ∧ pull _ (spMap (algebraMap B A')) _ _ x = 0 := by
  intro q _ k B _ _ _ _ _ _ hq f hf n i hn x
  by_cases hu : IsUnit f
  · haveI := away_zero_subsingleton B
    refine ⟨Localization.Away (0 : B), inferInstance, inferInstance, ⟨Algebra.Etale.of_isLocalizationAway 0, ?_, ?_⟩, ?_⟩
    · intro a'
      exact ⟨0, by rw [Subsingleton.elim (a' - _) 0]; exact Ideal.zero_mem _⟩
    · intro a _
      rw [Ideal.span_singleton_eq_top.mpr hu]
      exact Submodule.mem_top
    · haveI := ht_subsingleton_of_subsingleton q (Localization.Away (0 : B)) n i
      exact Subsingleton.elim _ _
  · obtain ⟨A', i1, i2, i3, hN, hx⟩ := GlobalTheory.T.etale_local_vanishing_cohomology q k B hq f hf hu n i (by omega) x
    exact ⟨A', i1, i2, ⟨i3, hN.1, hN.2⟩, hx⟩

end GlobalTheory.EtC.CurveNbhdExcision
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubHol

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem cubF_differentiable (ν : NumOf D ℂ N) (d : AB N.toNumB g) (geo : Geo ν d) (x y : Fin g → ℂ) :
    Differentiable ℂ (cubF d x y) := by
  intro z₀
  let j : thK → D.P.L.ι := fun I => ν.J (pt3 ν d x y z₀ ≫ thφ D.P.A (x3 D.P.A) I)
  let V : Set (Fin g → ℂ) := {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j}
  have hz₀ : z₀ ∈ V := fun w _ =>
    Good.mem (L := D.P.L) (z := w) (J := ν.J) (fun ψ => ν.good ψ trivial) (thφ D.P.A (x3 D.P.A)) (pt3 ν d x y z₀)
  obtain ⟨hV, hval⟩ := GlobalTheory.T.cubeLocalUnit_value_holomorphic_third ν d geo x y j
  have hP : ∀ z ∈ V, ∏ I : thK, geo.frG (j I) (wI x y z I) ^ thε I ≠ 0 := fun z hz =>
    Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ ((GlobalTheory.T.holomorphicFrame_partialSum_diff_ne_zero ν d geo x y j I).2 z hz)
  have hG : DifferentiableOn ℂ (fun z => valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val *
      (∏ I : thK, geo.frG (j I) (wI x y z I) ^ thε I)⁻¹) V := by
    refine hval.mul (DifferentiableOn.inv ?_ hP)
    have e : (fun z => ∏ I : thK, geo.frG (j I) (wI x y z I) ^ thε I) =
        ∏ I : thK, fun z => geo.frG (j I) (wI x y z I) ^ thε I := by
      ext z; rw [Finset.prod_apply]
    rw [e]
    refine Finset.prod_induction _ (fun f => DifferentiableOn ℂ f V) (fun f h hf hh => hf.mul hh)
      (differentiableOn_const 1) fun I _ => ?_
    exact (GlobalTheory.T.holomorphicFrame_partialSum_diff_ne_zero ν d geo x y j I).1.zpow (Or.inl fun z hz => (GlobalTheory.T.holomorphicFrame_partialSum_diff_ne_zero ν d geo x y j I).2 z hz)
  have heq : ∀ z ∈ V, cubF d x y z = valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val *
      (∏ I : thK, geo.frG (j I) (wI x y z I) ^ thε I)⁻¹ := fun z hz => by
    rw [← div_eq_mul_inv]
    exact (eq_div_iff (hP z hz)).2 (GlobalTheory.T.cubeValueTimesThetaFrames_chartGauge ν d geo x y z j hz)
  have hn : V ∈ nhds z₀ := hV.mem_nhds hz₀
  exact ((hG z₀ hz₀).differentiableAt hn).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem hn fun z hz => heq z hz)

theorem cubF_entire : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g), Nonempty (Geo ν d) → ∀ x y : Fin g → ℂ, Differentiable ℂ (cubF d x y) := by
  intro R _ _ _ _ D _ _ _ N ν g d ⟨geo⟩ x y
  exact cubF_differentiable ν d geo x y

end GlobalTheory.MBLow.Cl.CubHol

end
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

theorem _root_.GlobalTheory.T.conj_mem_principalCongruenceSubgroup_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n m : ℕ) (h k : GLw n w), k ∈ GlobalTheory.LFun.KGL w (n := n) → (k⁻¹ * h * k ∈ congSet w n m ↔ h ∈ congSet w n m) := by
  first | exact @GlobalTheory.KapOrb.conj_mem_congSet_iff | exact GlobalTheory.KapOrb.conj_mem_congSet_iff | (intros; apply GlobalTheory.KapOrb.conj_mem_congSet_iff <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_GL_latticeSpannedByGLColumns_eq_fullLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A) (L : Submodule K.O B.A), GlobalTheory.UnitLemma.IsLat K.O K.E L → ∃ q : GLw a w, GlobalTheory.TwLat.lat e b q = L := by
  first | exact @GlobalTheory.TwOrbLat.exists_lat_eq | exact GlobalTheory.TwOrbLat.exists_lat_eq | (intros; apply GlobalTheory.TwOrbLat.exists_lat_eq <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.latticeSpannedByGLColumns_eq_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A) (q q' : GLw a w), GlobalTheory.TwLat.lat e b q = GlobalTheory.TwLat.lat e b q' ↔ q⁻¹ * q' ∈ GlobalTheory.LFun.KGL w (n := a) := by
  first | exact @GlobalTheory.TwOrbLat.lat_eq_iff | exact GlobalTheory.TwOrbLat.lat_eq_iff | (intros; apply GlobalTheory.TwOrbLat.lat_eq_iff <;> assumption)
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.twistedConj_iff_mul_norm_invAlg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ u : B.A, Algebra.adjoin K.E {u} = ⊤ → ∀ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * ((-1) ^ (m - 1) * u) → (∀ x : B.Aˣ, IsUnit (GlobalTheory.TwLat.gram e b ((β₀ : B.A) * x))) → ∀ x x' : B.Aˣ, B.σ (x : B.A) = x → B.σ (x' : B.A) = x' → ((∃ g : GLw m w, GlobalTheory.TwLat.dlt e b ((β₀ : B.A) * x') = g⁻¹ * GlobalTheory.TwLat.dlt e b ((β₀ : B.A) * x) * thL m w g) ↔ ∃ a : B.Aˣ, (x' : B.A) = x * (a * B.σ a)) := by
  first | exact @GlobalTheory.TwLatInj.dlt_twConj_iff | exact GlobalTheory.TwLatInj.dlt_twConj_iff | (intros; apply GlobalTheory.TwLatInj.dlt_twConj_iff <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.twistedConj_integral_iff_lattice_unimodular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (β : B.Aˣ) (b : Module.Basis (Fin a) K.E B.A) (δ : GLw a w), (∀ i j, ((δ.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm β (b i) (b j))) → ∀ q : GLw a w, (q⁻¹ * δ * thL a w q ∈ GlobalTheory.LFun.KGL w (n := a) ↔ ∀ z, z ∈ GlobalTheory.TwLat.lat e b q ↔ ∀ y ∈ GlobalTheory.TwLat.lat e b q, B.herm β y z ∈ (algebraMap K.O K.E).range) := by
  first | exact @GlobalTheory.TwOrbUnimod.twist_integral_iff_unimodular | exact GlobalTheory.TwOrbUnimod.twist_integral_iff_unimodular | (intros; apply GlobalTheory.TwOrbUnimod.twist_integral_iff_unimodular <;> assumption)
end
