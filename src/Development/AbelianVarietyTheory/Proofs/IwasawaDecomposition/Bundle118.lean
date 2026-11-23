module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexNeZero
public import Mathlib.NumberTheory.NumberField.Basic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle200
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle011
import Formalism.LocalToGlobal.Columns.PolyFn
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle004
public import Mathlib.Algebra.MvPolynomial.Funext
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordinatesFlagVector
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle002
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle105
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Formalism.FrobeniusOrbits.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle003

@[expose] public section

section

namespace GlobalTheory.IntSmulMemLattice

open NumberField

theorem exists_int_smul_mem {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V]
    [Module (RingOfIntegers E) V] [IsScalarTower (RingOfIntegers E) E V]
    (L : Submodule (RingOfIntegers E) V) (hL : Submodule.span E (L : Set V) = ⊤) (v : V) :
    ∃ n : ℤ, n ≠ 0 ∧ n • v ∈ L := by
  apply GlobalTheory.DegCnt.Unimod.exists_mul_mem <;> assumption

end GlobalTheory.IntSmulMemLattice
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Filter Topology

namespace GlobalTheory.Mem.UnrAe

variable {L : Type} [Field L] [NumberField L]

theorem continuous_finSingle (v : HeightOneSpectrum (𝓞 L)) : Continuous (Neutral.B1.finiteSingle L v) := by
  apply GlobalTheory.CompanionTheory.InertOpen.continuous_finiteSingle <;> assumption

theorem continuous_localIdele (v : HeightOneSpectrum (𝓞 L)) : Continuous (Neutral.B1.localIdele L v) := by
  apply Continuous.units_map
  exact Continuous.prodMk continuous_const (continuous_finSingle v)

theorem tendsto_finSingle (y : ∀ v : HeightOneSpectrum (𝓞 L), v.adicCompletion L) (hy : ∀ v, Valued.v (y v) ≤ 1) :
    Tendsto (fun v => Neutral.B1.finiteSingle L v (y v)) cofinite (𝓝 1) := by
  classical
  let A : ∀ w : HeightOneSpectrum (𝓞 L), Set (w.adicCompletion L) := fun w => w.adicCompletionIntegers L
  let o : ∀ w, A w := fun w => ⟨1, one_mem (w.adicCompletionIntegers L)⟩
  let g : HeightOneSpectrum (𝓞 L) → ∀ w, A w := fun v => Function.update o v ⟨y v, hy v⟩
  have hg : Tendsto g cofinite (𝓝 o) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(Set.finite_singleton w).compl_mem_cofinite] with v hv
    have h' : w ≠ v := fun h => hv h.symm
    exact (Function.update_of_ne h' _ _).symm
  have h2 := ((RestrictedProduct.isEmbedding_structureMap (A := A) (𝓕 := cofinite)).continuous.tendsto o).comp hg
  refine Tendsto.congr (fun v => ?_) h2
  apply Subtype.ext
  funext w
  show (g v w : w.adicCompletion L) = Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) v (y v) w
  by_cases hw : w = v
  · subst hw; simp [g]
  · simp [g, o, Function.update_of_ne hw]

theorem tendsto_localIdele (x : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ) (hx : ∀ v, IsUnitAt v (x v)) :
    Tendsto (fun v => Neutral.B1.localIdele L v (x v)) cofinite (𝓝 1) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  have h1 := tendsto_finSingle (fun v => (x v : v.adicCompletion L)) fun v => (hx v).le
  have h2 := tendsto_finSingle (fun v => (((x v)⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L)) fun v => by
    have h : Valued.v (x v : v.adicCompletion L) = 1 := hx v
    rw [Units.val_inv_eq_inv_val, map_inv₀, h, inv_one]
  have h3 : Tendsto (fun v => ((Neutral.B1.localIdele L v (x v) : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L)) cofinite (𝓝 1) :=
    (tendsto_const_nhds (x := (1 : InfiniteAdeleRing L))).prodMk_nhds h1
  have h4 : Tendsto (fun v => (((Neutral.B1.localIdele L v (x v))⁻¹ : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L)) cofinite (𝓝 1) :=
    (tendsto_const_nhds (x := (1 : InfiniteAdeleRing L))).prodMk_nhds h2
  exact h3.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h4)

theorem isUnitAt_pow {v : HeightOneSpectrum (𝓞 L)} {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) (m : ℕ) :
    IsUnitAt v (x ^ m) := by
  unfold IsUnitAt at *
  rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]

theorem finite_ramified (χ : HChar L) : {v | ¬ χ.UnrAt v}.Finite := by
  have h : ∀ v, ∃ x : (v.adicCompletion L)ˣ, IsUnitAt v x ∧
      (‖((χ.loc v x : ℂˣ) : ℂ) - 1‖ < 1 / 2 → χ.UnrAt v) := fun v => by
    by_contra hc
    push Not at hc
    refine (hc 1 (map_one _)).2 fun x hx => Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
    rw [← Units.val_pow_eq_pow_val, ← map_pow]
    exact (hc _ (isUnitAt_pow hx m)).1
  choose x hx hx' using h
  have hc : Continuous fun a : Neutral.B1.Ideles L => ‖((χ.1 a : ℂˣ) : ℂ) - 1‖ :=
    ((Units.continuous_val.comp χ.2.1).sub continuous_const).norm
  have h1 := (hc.tendsto 1).comp (tendsto_localIdele x hx)
  have h2 := h1.eventually_lt_const (u := 1 / 2) (by simp)
  exact eventually_cofinite.1 (h2.mono fun v hv => hx' v hv)

theorem exists_levelLe (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : ∃ n, χ.LevelLe v n := by
  have hc : Continuous fun a : (v.adicCompletion L)ˣ => ‖((χ.loc v a : ℂˣ) : ℂ) - 1‖ :=
    ((Units.continuous_val.comp (χ.2.1.comp (continuous_localIdele v))).sub continuous_const).norm
  have h0 : {a : (v.adicCompletion L)ˣ | ‖((χ.loc v a : ℂˣ) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 1 :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨t, ht, hsub⟩ := h0
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp ht
  have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  refine ⟨(1 - WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).toNat, fun x hx hx1 => ?_⟩
  refine Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
  rw [← Units.val_pow_eq_pow_val, ← map_pow]
  apply hsub
  apply hγ
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, Units.val_pow_eq_pow_val, Units.val_one]
  have hx' : Valued.v (x : v.adicCompletion L) = 1 := hx
  have h1 : Valued.v ((x : v.adicCompletion L) ^ m - 1) ≤ Valued.v ((x : v.adicCompletion L) - 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have e : (x : v.adicCompletion L) ^ (m + 1) - 1 = x ^ m * (x - 1) + (x ^ m - 1) := by ring
      rw [e]
      refine Valuation.map_add_le _ ?_ ih
      rw [map_mul, map_pow, hx', one_pow, one_mul]
  refine (h1.trans hx1).trans_lt ?_
  conv_rhs => rw [← WithZero.exp_log hγ0]
  exact WithZero.exp_lt_exp.mpr (by omega)


open Classical in
theorem unr_ae_and_level : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L), {v | ¬ χ.UnrAt v}.Finite ∧ ∀ v, ∃ n, χ.LevelLe v n :=
  fun _ _ _ χ => ⟨finite_ramified χ, exists_levelLe χ⟩

end GlobalTheory.Mem.UnrAe
end

section

noncomputable section

namespace GlobalTheory.IntegralityCompare

open MvPolynomial Formalism.L2.Forms

theorem fnOf_apply_eq {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (A : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (y : Frames G) :
    fnOf G s A P y = (∏ τ, (A τ * y.1 τ).det ^ s τ) *
      eval (fun x : ι × Fin n × Fin n => (A x.1 * y.1 x.1) x.2.1 x.2.2) P := rfl

theorem map_mul_map_inv {E ι : Type} [Field E] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (τ : ι) :
    (M : Matrix (Fin n) (Fin n) E).map (emb τ) *
      ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (emb τ) = 1 := by
  rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem map_inv_mul_map {E ι : Type} [Field E] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (τ : ι) :
    ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (emb τ) *
      (M : Matrix (Fin n) (Fin n) E).map (emb τ) = 1 := by
  rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

theorem det_map_emb {E ι : Type} [Field E] {n : ℕ} (emb : ι → E →+* ℂ) (M : Matrix (Fin n) (Fin n) E) (τ : ι) :
    emb τ M.det = (M.map (emb τ)).det := RingHom.map_det _ _

theorem fnOf_inv_twSub {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E)
    (s : ι → ℤ) (G : ι → Matrix (Fin n) (Fin n) ℂ) (P0 : MvPolynomial (ι × Fin n × Fin n) ℂ) (y : Frames G) :
    fnOf G s (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) (twSub emb M s P0) y
      = fnOf G s 1 P0 y := by
  rw [fnOf_apply_eq, fnOf_apply_eq]
  have h := eval_twSub emb M s P0
    (fun τ => atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ)
  have hy : ∀ τ, (M : Matrix (Fin n) (Fin n) E).map (emb τ) *
      (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ) = y.1 τ := by
    intro τ; rw [← Matrix.mul_assoc, atInf, map_mul_map_inv, Matrix.one_mul]
  simp only [hy] at h
  rw [h]
  simp only [Pi.one_apply, Matrix.one_mul]
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [mul_comm, ← mul_zpow, det_map_emb, ← Matrix.det_mul, hy]

theorem exists_det_poly {ι : Type} [Fintype ι] {n : ℕ} :
    ∃ D : MvPolynomial (ι × Fin n × Fin n) ℂ, ∀ x : ι → Matrix (Fin n) (Fin n) ℂ,
      eval (fun k : ι × Fin n × Fin n => x k.1 k.2.1 k.2.2) D = ∏ τ, (x τ).det := by
  refine ⟨∏ τ, Matrix.det (Matrix.of fun a b => (X (τ, a, b) : MvPolynomial (ι × Fin n × Fin n) ℂ)), ?_⟩
  intro x
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

theorem eq_of_eval_units {ι : Type} [Fintype ι] {n : ℕ} (Q : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hQ : ∀ x : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, IsUnit (x τ).det) →
      eval (fun k : ι × Fin n × Fin n => x k.1 k.2.1 k.2.2) Q = 0) : Q = 0 := by
  apply Formalism.L2.Col.eq_zero_of_forall_isUnit <;> assumption

theorem fnOf_inv_iff_twSub_mem : ∀ {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (s : ι → ℤ)
    (G : ι → Matrix (Fin n) (Fin n) ℂ) (P0 : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (S : AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ)) {Yt : Type} (e : Yt ≃ Frames G) (f : Yt → ℂ),
    (∀ z, f z = fnOf G s 1 P0 (e z)) →
    ((∃ P ∈ S, ∀ z, f z = fnOf G s (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) P (e z)) ↔
      twSub emb M s P0 ∈ S) := by
  intro E ι _ _ n emb M s G P0 S Yt e f hf
  constructor
  · rintro ⟨P, hP, hPf⟩
    have hall : ∀ y : Frames G,
        fnOf G s (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) P y =
        fnOf G s (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) (twSub emb M s P0) y := by
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [← hPf, hf, fnOf_inv_twSub]
    suffices hPeq : P - twSub emb M s P0 = 0 by
      rw [sub_eq_zero] at hPeq
      rw [← hPeq]; exact hP
    apply eq_of_eval_units
    intro x hx
    have hMu : IsUnit (M : Matrix (Fin n) (Fin n) E).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp M.isUnit
    let y : Frames G := ⟨fun τ => (M : Matrix (Fin n) (Fin n) E).map (emb τ) * x τ, fun τ => by
      rw [Matrix.det_mul, ← det_map_emb]; exact (hMu.map (emb τ)).mul (hx τ)⟩
    have h1 := hall y
    rw [fnOf_apply_eq, fnOf_apply_eq] at h1
    have hAx : ∀ τ, atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ = x τ := by
      intro τ
      show atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ *
        ((M : Matrix (Fin n) (Fin n) E).map (emb τ) * x τ) = x τ
      rw [← Matrix.mul_assoc, atInf, map_inv_mul_map, Matrix.one_mul]
    simp only [hAx] at h1
    have hne : (∏ τ, (x τ).det ^ s τ) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hx τ).ne_zero
    rw [map_sub, sub_eq_zero]
    exact mul_left_cancel₀ hne h1
  · intro h
    exact ⟨_, h, fun z => by rw [hf, fnOf_inv_twSub]⟩

end GlobalTheory.IntegralityCompare
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep.InfType

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def diagInf (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] : E →+* Cinf E :=
  (pInf E).comp (algebraMap E (Ad E))

theorem infDiag_eq (k : Eˣ) : infDiag k = infId E (Units.map (diagInf E).toMonoidHom k) := by
  classical
  have h : ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace E, w.Completion) →* AdeleRing (𝓞 E) E :=
      MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
    change ∏ w : InfinitePlace E, ι (Pi.mulSingle w (algebraMap E w.Completion k)) =
      ι (fun w => algebraMap E w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [h]
  refine Prod.ext ?_ ?_
  · change _ = 1 - infEq E 1 + infEq E ((infEq E).symm (algebraMap E (InfiniteAdeleRing E) k))
    simp
  · change (1 : Af E) = 1 - 0 + 0
    simp

theorem denseRange_diagInf : DenseRange (diagInf E) := by
  have hc : Continuous (infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  exact (infEq E).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc

theorem denseRange_units : DenseRange (Units.map (diagInf E).toMonoidHom) := by
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ => ?_
  obtain ⟨k, v, hv, hk⟩ := denseRange_diagInf.exists_mem_open (Units.isOpenEmbedding_val.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have h0 : k ≠ 0 := by
    rintro rfl
    exact v.ne_zero (hk.trans (map_zero _))
  exact ⟨v, hv, Units.mk0 k h0, Units.ext hk.symm⟩


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_coord (τ : E →+* ℂ) : Continuous (coord τ) := by
  unfold coord
  split_ifs
  · exact continuous_apply _
  · exact Complex.continuous_conj.comp (continuous_apply _)


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem coord_expU (τ : E →+* ℂ) (x : Cinf E) : coord τ (expU x : (Cinf E)ˣ) = Complex.exp (coord τ x) := by
  unfold coord
  split_ifs
  · rfl
  · exact (Complex.exp_conj _).symm


omit [NumberField E] in
theorem conj_ne (τ : E →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
  InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
    (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h))


open Classical in
theorem coord_atEmb' (σ τ : E →+* ℂ) (z : ℂ) : coord σ (atEmb τ z) =
    (if σ = τ then z else 0) + (if σ = ComplexEmbedding.conjugate τ then starRingEnd ℂ z else 0) := by
  by_cases h1 : σ = τ
  · subst h1
    rw [if_pos rfl, if_neg (conj_ne σ).symm, add_zero, coord_atEmb]
  by_cases h2 : σ = ComplexEmbedding.conjugate τ
  · subst h2
    rw [if_neg h1, if_pos rfl, zero_add]
    have := atEmb_conj τ (starRingEnd ℂ z)
    rw [Complex.conj_conj] at this
    rw [← this, coord_atEmb]
  · have h : InfinitePlace.mk σ ≠ InfinitePlace.mk τ := fun h => by
      rcases InfinitePlace.mk_eq_iff.1 h with h | h
      · exact h1 h
      · exact h2 (by rw [← h]; ext; simp)
    rw [if_neg h1, if_neg h2, add_zero]
    unfold coord atEmb
    by_cases h3 : (InfinitePlace.mk σ).embedding = σ
    · rw [if_pos h3]; simp [h]
    · rw [if_neg h3]; simp [h]

theorem chiInf_eq (χ : HChar E) {I : Type} [Fintype I] (φ : I → E →+* ℂ) (f : I → ℂ → ℂ)
    (hf : ∀ i z, z ≠ 0 → ContinuousAt (f i) z)
    (h : ∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ i, f i (φ i k)) (u : (Cinf E)ˣ) :
    ((chiInf χ u : ℂˣ) : ℂ) = ∏ i, f i (coord (φ i) u) := by
  refine congrFun (denseRange_units.equalizer (g := fun u => ((chiInf χ u : ℂˣ) : ℂ))
    (h := fun u : (Cinf E)ˣ => ∏ i, f i (coord (φ i) u)) (Units.continuous_val.comp (continuous_chiInf χ))
    (continuous_finsetProd _ fun i _ => continuous_iff_continuousAt.2 fun v => ?_) (funext fun k => ?_)) u
  · exact ContinuousAt.comp (g := f i) (f := fun u : (Cinf E)ˣ => coord (φ i) u)
      (hf i _ (v.isUnit.map (coord (φ i))).ne_zero)
      ((continuous_coord (φ i)).comp Units.continuous_val).continuousAt
  · have e := h k
    simp only [← coord_algebraMap (φ _) (k : E)] at e
    rw [HChar.inf, MonoidHom.comp_apply, infDiag_eq] at e
    exact e


open Classical in
theorem expo_eq_sum (χ : HChar E) {I : Type} [Fintype I] (φ : I → E →+* ℂ) (f : I → ℂ → ℂ) (a b : I → ℂ)
    (hf : ∀ i z, z ≠ 0 → ContinuousAt (f i) z)
    (he : ∀ i z, f i (Complex.exp z) = Complex.exp (a i * z + b i * starRingEnd ℂ z))
    (h : ∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ i, f i (φ i k)) (τ : E →+* ℂ) :
    expo χ τ = ∑ i, ((if φ i = τ then a i else 0) + (if φ i = ComplexEmbedding.conjugate τ then b i else 0)) := by
  refine expo_eq_of_exp χ τ _
    (∑ i, ((if φ i = τ then b i else 0) + (if φ i = ComplexEmbedding.conjugate τ then a i else 0))) fun z => ?_
  rw [chiInf_eq χ φ f hf h]
  simp only [coord_expU, he, coord_atEmb']
  rw [← Complex.exp_sum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  split_ifs <;> simp <;> ring

theorem expo_of_infType : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E), (∀ n : (E →+* ℂ) → ℤ, χ.IsAlg n → ∀ τ, expo χ τ = n τ) ∧ (∀ s : ℝ, χ.IsAbsPow s → ∀ τ, expo χ τ = s) ∧ ∀ (I : Type) [Fintype I] (φ : I → E →+* ℂ) (n : I → ℤ), Function.Injective (fun i => InfinitePlace.mk (φ i)) → χ.HasInf φ n → ∀ i, expo χ (φ i) = (n i : ℂ) / 2 ∧ expo χ (ComplexEmbedding.conjugate (φ i)) = -(n i : ℂ) / 2 := by
  intro E _ _ _ χ
  classical
  refine ⟨fun n h τ => ?_, fun s h τ => ?_, fun I _ φ n hφ h i => ?_⟩
  · rw [expo_eq_sum χ (fun σ => σ) (fun σ z => z ^ n σ) (fun σ => n σ) (fun _ => 0)
      (fun σ z hz => continuousAt_zpow₀ z _ (Or.inl hz)) (fun σ z => by simp [Complex.exp_int_mul]) h τ]
    simp
  · rw [expo_eq_sum χ (fun σ => σ) (fun σ z => ((‖z‖ : ℝ) : ℂ) ^ (s : ℂ)) (fun _ => s / 2) (fun _ => s / 2)
      (fun σ z hz => ?_) (fun σ z => ?_) h.2.2 τ]
    · simp [Finset.sum_add_distrib]
    · refine ContinuousAt.cpow (Complex.continuous_ofReal.comp continuous_norm).continuousAt continuousAt_const ?_
      exact Complex.ofReal_mem_slitPlane.2 (norm_pos_iff.2 hz)
    · rw [← Complex.ofReal_cpow (norm_nonneg _), Complex.norm_exp, ← Real.exp_mul, Complex.ofReal_exp]
      congr 1
      rw [← mul_add, Complex.add_conj]
      push_cast
      ring
  · have key := expo_eq_sum χ φ (fun i z => (z / ((‖z‖ : ℝ) : ℂ)) ^ n i) (fun i => n i / 2) (fun i => -(n i : ℂ) / 2)
      (fun i z hz => ?_) (fun i z => ?_) h
    · have h1 : ∀ j, φ j = φ i ↔ j = i := fun j =>
        ⟨fun e => hφ (congrArg InfinitePlace.mk e), fun e => by rw [e]⟩
      have h2 : ∀ j, φ j ≠ ComplexEmbedding.conjugate (φ i) := fun j e => by
        have : j = i := hφ ((congrArg InfinitePlace.mk e).trans (InfinitePlace.mk_conjugate_eq _))
        subst this
        exact conj_ne _ e.symm
      have h3 : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (φ i)) = φ i := by ext; simp
      rw [key, key]
      simp [h1, h2, h3]
    · have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by simpa using hz
      exact (continuousAt_id.div (Complex.continuous_ofReal.comp continuous_norm).continuousAt hn).zpow₀ _
        (Or.inl (div_ne_zero hz hn))
    · rw [Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_sub, ← Complex.exp_int_mul]
      congr 1
      have := Complex.add_conj z
      push_cast at this
      linear_combination ((n i : ℂ) / 2) * this

end GlobalTheory.CuspRep.InfType
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IntPair GlobalTheory.IntTerm Formalism.BasicNotions
open Formalism.MainNotions.S (FlagG LieU perpS)

namespace GlobalTheory.RelFlag

section Space

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem hT_eq_form (x y : S.V) : S.hT y x = form (starRingEnd E) S.gram (co S x) (co S y) := by
  rw [hT_eq_sum, form, Matrix.dotProduct_mulVec]; rfl

variable (F : FlagG S r T)

variable {F}

end Space

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.RelFlag
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.ainf_quot_fontaineXi_pow_torsionFree_separated : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l), IsEps e → ∀ n : ℕ, (∀ a : Per.Ainf l, xi e ^ n ∣ ((l : ℕ) : Per.Ainf l) * a → xi e ^ n ∣ a) ∧ ∀ a : Per.Ainf l, (∀ k : ℕ, ∃ b : Per.Ainf l, xi e ^ n ∣ a - ((l : ℕ) : Per.Ainf l) ^ k * b) → xi e ^ n ∣ a := by
  first | exact @GlobalTheory.MemLoc.ainf_quot_xi_pow_torsionFree_sep | exact GlobalTheory.MemLoc.ainf_quot_xi_pow_torsionFree_sep | (intros; apply GlobalTheory.MemLoc.ainf_quot_xi_pow_torsionFree_sep <;> assumption)
end
