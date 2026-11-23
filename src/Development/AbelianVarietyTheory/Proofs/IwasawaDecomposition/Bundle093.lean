module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointsFinitePlaceTensorProperties
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFibreFamilyHermitianLengthInfiniteAdeles
public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedOrbitHasNearbyFixedPoint
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle087
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Filter Topology

namespace GlobalTheory.Mem.LocTriv

variable {L : Type} [Field L] [NumberField L]

theorem tendsto_finiteAdele {ι : Type} {l : Filter ι} (f : ι → FiniteAdeleRing (𝓞 L) L) (b : FiniteAdeleRing (𝓞 L) L)
    (hf : ∀ i v, f i v ∈ v.adicCompletionIntegers L) (hb : ∀ v, b v ∈ v.adicCompletionIntegers L)
    (h : ∀ v, Tendsto (fun i => f i v) l (𝓝 (b v))) : Tendsto f l (𝓝 b) := by
  first
  | exact @_root_.GlobalTheory.TendstoOfIntegrals.target_check
  | exact _root_.GlobalTheory.TendstoOfIntegrals.target_check
  | (apply _root_.GlobalTheory.TendstoOfIntegrals.target_check <;> assumption)
  | (intros; apply _root_.GlobalTheory.TendstoOfIntegrals.target_check <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TendstoOfIntegrals.target_check <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TendstoOfIntegrals.target_check ..)

def ev (v : HeightOneSpectrum (𝓞 L)) : AdeleRing (𝓞 L) L →* v.adicCompletion L where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def part (a : Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))) : Ideles L :=
  ∏ v ∈ S, localIdele L v (Units.map (ev v) a)

theorem part_inv (a : Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))) : (part a S)⁻¹ = part a⁻¹ S := by
  simp only [part, map_inv, Finset.prod_inv_distrib]

theorem ev_local_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ev v (localIdele L v x : AdeleRing (𝓞 L) L) = x := by
  classical
  have := Function.update_self (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
    (x : v.adicCompletion L) (fun _ => 1)
  convert this
  rfl

theorem ev_local_ne {v w : HeightOneSpectrum (𝓞 L)} (hw : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ev w (localIdele L v x : AdeleRing (𝓞 L) L) = 1 := by
  classical
  have := Function.update_of_ne (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) hw
    (x : v.adicCompletion L) (fun _ => 1)
  convert this
  rfl

theorem ev_part_mem (a : Ideles L) {S : Finset (HeightOneSpectrum (𝓞 L))} {w : HeightOneSpectrum (𝓞 L)} (hw : w ∈ S) :
    ev w (part a S : AdeleRing (𝓞 L) L) = ev w (a : AdeleRing (𝓞 L) L) := by
  rw [part, Units.coe_prod, map_prod, Finset.prod_eq_single_of_mem w hw (fun v _ hv => ev_local_ne hv.symm _),
    ev_local_self]
  rfl

theorem ev_part_not_mem (a : Ideles L) {S : Finset (HeightOneSpectrum (𝓞 L))} {w : HeightOneSpectrum (𝓞 L)}
    (hw : w ∉ S) : ev w (part a S : AdeleRing (𝓞 L) L) = 1 := by
  rw [part, Units.coe_prod, map_prod]
  exact Finset.prod_eq_one fun v hv => ev_local_ne (fun e : w = v => hw (e ▸ hv)) _

theorem part_fst (a : Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))) : (part a S : AdeleRing (𝓞 L) L).1 = 1 := by
  have h : finPartI L (part a S) = part a S := by
    rw [part, map_prod]
    exact Finset.prod_congr rfl fun v _ => Units.ext rfl
  rw [← h]
  rfl

theorem tendsto_part_val {a : Ideles L} (ha : a ∈ unitIdl L) (h1 : (a : AdeleRing (𝓞 L) L).1 = 1) :
    Tendsto (fun S => (part a S : AdeleRing (𝓞 L) L)) atTop (𝓝 (a : AdeleRing (𝓞 L) L)) := by
  have h2 : Tendsto (fun S => (part a S : AdeleRing (𝓞 L) L).2) atTop (𝓝 (a : AdeleRing (𝓞 L) L).2) := by
    refine tendsto_finiteAdele _ _ (fun S v => ?_) (fun v => (ha v).le) fun v => ?_
    · show ev v (part a S : AdeleRing (𝓞 L) L) ∈ _
      by_cases hv : v ∈ S
      · rw [ev_part_mem a hv]
        exact (ha v).le
      · rw [ev_part_not_mem a hv]
        exact one_mem _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ({v} : Finset _)] with S hS
      exact (ev_part_mem a (hS (Finset.mem_singleton_self v))).symm
  have h3 : Tendsto (fun S => (part a S : AdeleRing (𝓞 L) L).1) atTop (𝓝 (a : AdeleRing (𝓞 L) L).1) := by
    rw [h1]
    exact tendsto_const_nhds.congr fun S => (part_fst a S).symm
  exact h3.prodMk_nhds h2

theorem tendsto_part {a : Ideles L} (ha : a ∈ unitIdl L) (h1 : ∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) :
    Tendsto (part a) atTop (𝓝 a) := by
  have e : finPartI L a = a := finPartI_eq_self h1
  have e' : finPartI L a⁻¹ = a⁻¹ := by rw [map_inv, e]
  have t1 := tendsto_part_val ha (by rw [← e]; rfl)
  have t2 := tendsto_part_val ((unitIdl L).inv_mem ha) (by rw [← e']; rfl)
  simp only [← part_inv] at t2
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact t1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp t2)


open Classical in
theorem eq_one_of_local : ∀ (L : Type) [Field L] [NumberField L] (ψ : Ideles L →* ℂˣ), Continuous ψ → ∀ a : Ideles L, a ∈ unitIdl L → (∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) → (∀ v (x : (v.adicCompletion L)ˣ), (x : v.adicCompletion L) = (a : AdeleRing (𝓞 L) L).2 v → ψ (localIdele L v x) = 1) → ψ a = 1 := by
  intro L _ _ ψ hψ a ha h1 hl
  have t := (hψ.tendsto a).comp (tendsto_part ha h1)
  have e : ψ ∘ part a = fun _ => 1 := funext fun S => by
    show ψ (part a S) = 1
    rw [part, map_prod]
    exact Finset.prod_eq_one fun v _ => hl v _ rfl
  rw [e] at t
  exact tendsto_nhds_unique t tendsto_const_nhds

end GlobalTheory.Mem.LocTriv
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.ProdInt

theorem map_eq_smul_prod {ι Z Zi : Type} {Zv : ι → Type} [MeasurableSpace Z] [MeasurableSpace Zi]
    [∀ v, MeasurableSpace (Zv v)] (ρ : Measure Z) (mi : Measure Zi) (mv : ∀ v, Measure (Zv v))
    [SigmaFinite mi] [∀ v, SigmaFinite (mv v)] (pi : Z → Zi) (pv : ∀ v, Z → Zv v)
    (hpi : Measurable pi) (hpv : ∀ v, Measurable (pv v)) (S : Finset ι) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ (fi : Zi → ℝ≥0∞) (fv : ∀ v, Zv v → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ X, fi (pi X) * ∏ v ∈ S, fv v (pv v X) ∂ρ =
        (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * c) :
    ρ.map (fun X => (pi X, fun v : S => pv v X)) = c • mi.prod (Measure.pi fun v : S => mv v) := by
  classical
  have hT : Measurable (fun X => (pi X, fun v : S => pv v X)) :=
    hpi.prodMk (Measurable.of_eval fun v => hpv v)
  by_cases hc0 : c = 0
  · have := h (fun _ => 1) (fun _ _ => 1) measurable_const (fun _ => measurable_const)
    simp only [hc0, mul_zero, Finset.prod_const_one, mul_one, lintegral_const, one_mul,
      Measure.measure_univ_eq_zero] at this
    simp [this, hc0]
  have key : mi.prod (Measure.pi fun v : S => mv v) =
      c⁻¹ • ρ.map (fun X => (pi X, fun v : S => pv v X)) := by
    refine Measure.prod_eq_generateFrom (C := {s | MeasurableSet s})
      (D := Set.pi Set.univ '' Set.pi Set.univ fun v : S => {s : Set (Zv v) | MeasurableSet s})
      MeasurableSpace.generateFrom_measurableSet generateFrom_pi
      MeasurableSpace.isPiSystem_measurableSet isPiSystem_pi mi.toFiniteSpanningSetsIn
      (Measure.FiniteSpanningSetsIn.pi fun v : S => (mv v).toFiniteSpanningSetsIn) ?_
    rintro s hs _ ⟨t, ht, rfl⟩
    have hs' : MeasurableSet s := hs
    have ht' : ∀ v : S, MeasurableSet (t v) := fun v => ht v (Set.mem_univ _)
    let fv : ∀ v, Zv v → ℝ≥0∞ := fun v => if hv : v ∈ S then (t ⟨v, hv⟩).indicator 1 else 0
    have hfv : ∀ v, Measurable (fv v) := by
      intro v
      by_cases hv : v ∈ S
      · simp only [fv, dif_pos hv]
        exact measurable_one.indicator (ht' _)
      · simp only [fv, dif_neg hv]
        exact measurable_zero
    have hfv' : ∀ v : S, fv v = (t v).indicator 1 := fun v => by simp only [fv, dif_pos v.2]
    have h1 := h (s.indicator 1) fv (measurable_one.indicator hs') hfv
    have hm : MeasurableSet (s ×ˢ Set.pi Set.univ t) :=
      hs'.prod (MeasurableSet.univ_pi ht')
    rw [Measure.smul_apply, Measure.map_apply hT hm, ← lintegral_indicator_one (hT hm), Measure.pi_pi]
    have h2 : ∀ X, ((fun X => (pi X, fun v : S => pv v X)) ⁻¹' (s ×ˢ Set.pi Set.univ t)).indicator
        (1 : Z → ℝ≥0∞) X = s.indicator 1 (pi X) * ∏ v ∈ S, fv v (pv v X) := by
      intro X
      rw [← Finset.prod_coe_sort S]
      simp only [hfv']
      by_cases hX : pi X ∈ s
      · by_cases hY : ∀ v : S, pv v X ∈ t v
        · rw [Set.indicator_of_mem (by simpa [hX] using hY)]
          simp [hX, hY]
        · rw [Set.indicator_of_notMem (by simpa [hX] using hY)]
          push_neg at hY
          obtain ⟨v, hv⟩ := hY
          rw [Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])]
          simp
      · rw [Set.indicator_of_notMem (by simp [hX])]
        simp [hX]
    simp_rw [h2]
    rw [h1, ← Finset.prod_coe_sort S]
    simp only [hfv', lintegral_indicator_one hs', lintegral_indicator_one (ht' _), smul_eq_mul]
    rw [mul_comm c⁻¹, mul_assoc, ENNReal.mul_inv_cancel hc0 hc, mul_one]
  rw [key, smul_smul, ENNReal.mul_inv_cancel hc0 hc, one_smul]

theorem integral_tensor {ι Z Zi : Type} {Zv : ι → Type} [MeasurableSpace Z] [MeasurableSpace Zi]
    [∀ v, MeasurableSpace (Zv v)] (ρ : Measure Z) (mi : Measure Zi) (mv : ∀ v, Measure (Zv v))
    [SigmaFinite mi] [∀ v, SigmaFinite (mv v)] (pi : Z → Zi) (pv : ∀ v, Z → Zv v)
    (hpi : Measurable pi) (hpv : ∀ v, Measurable (pv v)) (S : Finset ι) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ (fi : Zi → ℝ≥0∞) (fv : ∀ v, Zv v → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ X, fi (pi X) * ∏ v ∈ S, fv v (pv v X) ∂ρ =
        (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * c)
    (Φi : Zi → ℂ) (Φv : ∀ v, Zv v → ℂ) (hi : Integrable Φi mi) (hv : ∀ v, Integrable (Φv v) (mv v)) :
    Integrable (fun X => Φi (pi X) * ∏ v ∈ S, Φv v (pv v X)) ρ ∧
      ∫ X, Φi (pi X) * ∏ v ∈ S, Φv v (pv v X) ∂ρ =
        (∫ Y, Φi Y ∂mi) * ((∏ v ∈ S, ∫ Y, Φv v Y ∂(mv v)) * (c.toReal : ℂ)) := by
  have hT : Measurable (fun X => (pi X, fun v : S => pv v X)) :=
    hpi.prodMk (Measurable.of_eval fun v => hpv v)
  have hmap := map_eq_smul_prod ρ mi mv pi pv hpi hpv S c hc h
  let G : Zi × (∀ v : S, Zv v) → ℂ := fun Y => Φi Y.1 * ∏ v : S, Φv v (Y.2 v)
  have hG : Integrable G (mi.prod (Measure.pi fun v : S => mv v)) :=
    hi.mul_prod (Integrable.fintype_prod_dep (f := fun v : S => Φv v) fun v => hv v)
  have hG' : Integrable G (ρ.map (fun X => (pi X, fun v : S => pv v X))) := by
    rw [hmap]; exact hG.smul_measure hc
  have he : (fun X => Φi (pi X) * ∏ v ∈ S, Φv v (pv v X)) =
      G ∘ (fun X => (pi X, fun v : S => pv v X)) := by
    funext X
    simp only [G, Function.comp]
    rw [← Finset.prod_coe_sort S]
  rw [he]
  refine ⟨(integrable_map_measure hG'.aestronglyMeasurable hT.aemeasurable).1 hG', ?_⟩
  have := integral_map hT.aemeasurable hG'.aestronglyMeasurable
  simp only [Function.comp_def]
  rw [← this, hmap, integral_smul_measure]
  simp only [G]
  rw [integral_prod_mul Φi (fun Y : ∀ v : S, Zv v => ∏ v : S, Φv v (Y v)),
    integral_fintype_prod_eq_prod (fun v : S => Φv v), ← Finset.prod_coe_sort S, Complex.real_smul]
  ring

theorem hasProd_of_tail {ι : Type} (f : ι → ℂ) (a : ι → ℝ) (ha : ∀ v, 0 ≤ a v)
    (hs : Summable fun v => |a v - 1|) (S : Finset ι) (hf : ∀ v ∉ S, f v = a v) :
    HasProd f ((∏ v ∈ S, f v) *
      (((ENNReal.ofReal (∏' v : {v // v ∉ S}, a v.1)).toReal : ℝ) : ℂ)) := by
  have hm : Multipliable fun v : {v // v ∉ S} => a v.1 := by
    have h1 : Summable fun v : {v // v ∉ S} => ‖a v.1 - 1‖ := hs.subtype _
    simpa using multipliable_one_add_of_summable h1
  have h0 : 0 ≤ ∏' v : {v // v ∉ S}, a v.1 :=
    ge_of_tendsto' hm.hasProd fun s => Finset.prod_nonneg fun v _ => ha _
  rw [ENNReal.toReal_ofReal h0]
  have h2 := hm.hasProd.map Complex.ofRealHom Complex.continuous_ofReal
  refine (S.hasProd f).mul_compl ?_
  have h3 : (f ∘ Subtype.val : {v // v ∉ S} → ℂ) = Complex.ofRealHom ∘ fun v : {v // v ∉ S} => a v.1 :=
    funext fun v => hf v.1 v.2
  have h4 : HasProd (f ∘ Subtype.val : {v // v ∉ S} → ℂ)
      ((∏' v : {v // v ∉ S}, a v.1 : ℝ) : ℂ) := by rw [h3]; exact h2
  exact h4

theorem integral_pure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsProd b ν mi mv → ∀ (d' : ℕ) (b' : Module.Basis (Fin d') F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), Continuous Φinf → HasCompactSupport Φinf → IsPureFin b' Φf Φv → IsProdInfFin Φ Φinf Φf → Integrable Φ ν ∧ Multipliable (fun v => ∫ X, Φv v X ∂(mv v)) ∧ ∫ X, Φ X ∂ν = (∫ X, Φinf X ∂mi) * ∏' v, ∫ X, Φv v X ∂(mv v) := by
  intro F E _ _ _ _ _ d b n M ν mi mv hP d' b' Φ Φinf Φf Φv hc hcs hpure hΦ
  obtain ⟨⟨hmi, hmv, hsum⟩, hP⟩ := hP
  obtain ⟨hsb, hae, hfin⟩ := hpure
  obtain ⟨hco, -, hint, hbb⟩ := GlobalTheory.GaugeEx.IntBasis.main F E (AlgHom.id F E) d b
  obtain ⟨-, -, hci, hcv⟩ := GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b n M
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hae' : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1 := by
    filter_upwards [hae, hbb d' b'] with v h1 h2
    rw [h1]
    congr 1
    ext Y
    rw [mem_latV_iff, mem_latV_iff, h2]
  have hfinS := Filter.eventually_cofinite.1 hae'
  set S := hfinS.toFinset with hS
  have hout : ∀ v ∉ S, Φv v = (latV b v).indicator 1 := by
    intro v hv
    by_contra hne
    exact hv (by simpa [hS] using hne)
  have hlat : ∀ v : HeightOneSpectrum (𝓞 F),
      IsClosed (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
    intro v
    have : (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) =
        ⋂ a, ⋂ i, (fun Y => Y a i) ⁻¹' intV b v := by
      ext Y; simp [mem_latV_iff]
    rw [this]
    exact isClosed_iInter fun a => isClosed_iInter fun i =>
      (hco v).1.isClosed.preimage (by fun_prop)
  set B : Set (Fin n → Fin M → AF F ⊗[F] E) := {X | ∀ v ∉ S, projV v (projFin X) ∈ latV b v} with hB
  have hBm : MeasurableSet B := by
    have : B = ⋂ v, ⋂ (_ : v ∉ S), (fun X => projV v (projFin X)) ⁻¹' latV b v := by
      ext X; simp [hB]
    rw [this]
    exact (isClosed_iInter fun v => isClosed_iInter fun _ => (hlat v).preimage (hcv v)).measurableSet
  have hΦB : Φ = B.indicator fun X => Φinf (projInf X) * ∏ v ∈ S, Φv v (projV v (projFin X)) := by
    funext X
    rw [hΦ X, hfin]
    by_cases hX : X ∈ B
    · rw [Set.indicator_of_mem hX, finprod_eq_prod_of_mulSupport_subset (s := S)]
      intro v hv
      by_contra hvS
      have hvS' : v ∉ S := hvS
      apply hv
      simp only [hout v hvS']
      exact Set.indicator_of_mem (hX v hvS') _
    · rw [Set.indicator_of_notMem hX]
      simp only [hB, Set.mem_setOf_eq, not_forall] at hX
      obtain ⟨v, hvS, hv⟩ := hX
      have hev : ∀ᶠ v in Filter.cofinite, Φv v (projV v (projFin X)) = 1 := by
        have h1 : ∀ᶠ v in Filter.cofinite, ∀ a i, prV v (X a i) ∈ intV b v :=
          Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun i => hint _
        filter_upwards [hae', h1] with w h2 h3
        rw [h2]
        exact Set.indicator_of_mem (show projV w (projFin X) ∈ latV b w from h3) _
      rw [finprod_eq_zero _ v (by rw [hout v hvS]; exact Set.indicator_of_notMem hv _)
        (Filter.eventually_cofinite.1 hev), mul_zero]
  haveI : SigmaFinite mi := inferInstance
  haveI : ∀ v, SigmaFinite (mv v) := fun v => inferInstance
  obtain ⟨h1, h2⟩ := integral_tensor (ν.restrict B) mi mv projInf (fun v X => projV v (projFin X))
    hci.measurable (fun v => (hcv v).measurable) S (tailProd b mv S) ENNReal.ofReal_ne_top (hP S)
    Φinf Φv (hc.integrable_of_hasCompactSupport hcs)
    (fun v => (hsb v).1.continuous.integrable_of_hasCompactSupport (hsb v).2)
  have h3 := hasProd_of_tail (fun v => ∫ X, Φv v X ∂(mv v)) (fun v => (mv v (latV b v)).toReal)
    (fun v => ENNReal.toReal_nonneg) hsum S (by
      intro v hv
      rw [hout v hv]
      have := integral_indicator_const (μ := mv v) (1 : ℂ) (hlat v).measurableSet
      simpa [Measure.real, Pi.one_def] using this)
  refine ⟨?_, h3.multipliable, ?_⟩
  · rw [hΦB]; exact (integrable_indicator_iff hBm).2 h1
  · rw [h3.tprod_eq, hΦB, integral_indicator hBm, h2]
    rfl

end GlobalTheory.GaugeEx.ProdInt
end

section

namespace GlobalTheory.SmulMemOfIsLattice

theorem exists_smul_mem_of_isLattice {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (B : Submodule (NumberField.RingOfIntegers E) (Formalism.L2.Col.Sp E n))
    (hB : Submodule.IsFullLattice E B) (x : Formalism.L2.Col.Sp E n) :
    ∃ r ∈ nonZeroDivisors (NumberField.RingOfIntegers E), r • x ∈ B := by
  have hx : x ∈ Submodule.span E (B : Set (Formalism.L2.Col.Sp E n)) := by
    rw [hB.span_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_mem _, by simpa using hy⟩
  | zero => exact ⟨1, one_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨r, hr, hry⟩ := hy
    obtain ⟨s, hs, hsz⟩ := hz
    refine ⟨r * s, mul_mem hr hs, ?_⟩
    rw [smul_add]
    refine B.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact B.smul_mem _ hry
    · rw [mul_smul]; exact B.smul_mem _ hsz
  | smul c y _ hy =>
    obtain ⟨r, hr, hry⟩ := hy
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) c
    refine ⟨r * b, mul_mem hr hb, ?_⟩
    have hb0 : algebraMap (NumberField.RingOfIntegers E) E b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have h : (r * b) • ((algebraMap (NumberField.RingOfIntegers E) E a / algebraMap (NumberField.RingOfIntegers E) E b) • y) = a • (r • y) := by
      rw [← algebraMap_smul E (r * b), ← algebraMap_smul E a, ← algebraMap_smul E r y, smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [h]
    exact B.smul_mem _ hry

end GlobalTheory.SmulMemOfIsLattice
end

section

set_option autoImplicit false

noncomputable section

open NumberField
open scoped Matrix ComplexOrder

namespace GlobalTheory.CentralLevelOp

open Formalism.DivisionValues Formalism.L2.DIV

theorem lvlOp_mem_lvlNab : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : NumberField.InfinitePlace K), Formalism.DivisionValues.IsConjAt v0 →
    ∀ (S : Formalism.L2.DIV.CSD K), (S.H.map v0.embedding).PosDef →
    ∀ (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms), S.ActGood r →
    ∀ (P : Subgroup G) (ψ : P →* Kˣ) (a : MonoidAlgebra K G), (∀ b, a * b = b * a) → (∀ t : G, ∃ n : ℤ, a.coeff t = n) →
    ∀ x ∈ S.lvlNab r P ψ, (S.lvlOp r P ψ a).mulVec x ∈ S.lvlNab r P ψ := by
  intro K _ _ _ v0 h0 S hH G _ _ r hr P ψ a hc hz x hx
  have hE := (level_operator_spec K v0 h0 S hH G r hr P ψ a (hc _)).1
  change (S.lvlE r P ψ).mulVec x ∈ S.nabLat at hx
  change (S.lvlE r P ψ).mulVec ((S.lvlOp r P ψ a).mulVec x) ∈ S.nabLat
  rw [Matrix.mulVec_mulVec, hE, ← Matrix.mulVec_mulVec, CSD.gaMat, Matrix.sum_mulVec]
  refine Submodule.sum_mem _ fun t _ => ?_
  obtain ⟨n, hn⟩ := hz t
  rw [Matrix.smul_mulVec, hn, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_of_tower_mem _ n ((action_preserves_lattice K S G r hr t).1 _ hx)

end GlobalTheory.CentralLevelOp
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.exists_fibreFamily_hermitianLength_infiniteAdeles : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (Ainf F)), 1 ≤ M → IsHermND σ J → μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∃ fib : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E), IsFibreFamily μ (fun X => qR (Ainf F) σ J (X 0)) id Set.univ ν {c : Ainf F | ∀ w, c w ≠ 0} fib := by
  first | exact @GlobalTheory.GaugeEx.FibExist.exists_fibreFamily_ainf | exact GlobalTheory.GaugeEx.FibExist.exists_fibreFamily_ainf | (intros; apply GlobalTheory.GaugeEx.FibExist.exists_fibreFamily_ainf <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_global_matrix_approximation_mod_integral : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (W Q : ι → Type) [∀ q, CommRing (W q)] [∀ q, IsDomain (W q)] [∀ q, IsDiscreteValuationRing (W q)] [∀ q, Field (Q q)] [∀ q, Algebra (W q) (Q q)] [∀ q, IsFractionRing (W q) (Q q)] {F : Type} [Field F] (f : ∀ q, F →+* Q q) (π : ∀ q, W q), (∀ q, Irreducible (π q)) → ∀ (t : F), (∀ q, f q t = algebraMap (W q) (Q q) (π q)) → (∀ (y : ∀ q, W q) (N : ℕ), ∃ x : F, ∀ q, ∃ z : W q, f q x = algebraMap (W q) (Q q) (y q + π q ^ N * z)) → ∀ {n : ℕ} (g : ∀ q, Matrix (Fin n) (Fin n) (Q q)), (∀ q, IsUnit (g q).det) → ∀ (q0 : ι), ∃ (B : Matrix (Fin n) (Fin n) F) (u : Matrix (Fin n) (Fin n) (W q0)), IsUnit u.det ∧ B.map (f q0) = g q0 * u.map (algebraMap (W q0) (Q q0)) ∧ ∀ q, q ≠ q0 → ∀ c, (fun i => f q (B i c)) ∈ Formalism.MainNotions.G.colSpan (W q) (g q) := by
  first | exact @GlobalTheory.GlobApx.exists_glob_approx | exact GlobalTheory.GlobApx.exists_glob_approx | (intros; apply GlobalTheory.GlobApx.exists_glob_approx <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.bounded_orbit_has_nearby_fixed_point : ∀ (l : ℕ) [Fact l.Prime], ∃ c : ℝ, 0 < c ∧ ∀ (H : Subgroup (GQ l)) (x : Om l) (r : ℝ), (∀ g ∈ H, ‖g x - x‖ ≤ r) → ∃ y : Om l, (∀ g ∈ H, g y = y) ∧ ‖x - y‖ ≤ c * r := by
  first | exact @GlobalTheory.AxLemma.ax_lemma | exact GlobalTheory.AxLemma.ax_lemma | (intros; apply GlobalTheory.AxLemma.ax_lemma <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor


theorem _root_.GlobalTheory.T.existsUnique_generator_extend_dense_proOpen : ∀ (Y U H HU X : Scheme.{0}) [IsLocallyNoetherian Y] (j : U ⟶ Y) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j], Geo.Tor.IsNormalScheme Y → ∀ (p : H ⟶ Y) (e : Y ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U) (eU : U ⟶ HU), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → IsPullback jH pU p j → eU ≫ jH = j ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => jH ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ j) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c jH = t := by
  first | exact @GlobalTheory.GenExtendDense.existsUnique_gen_extend | exact GlobalTheory.GenExtendDense.existsUnique_gen_extend | (intros; apply GlobalTheory.GenExtendDense.existsUnique_gen_extend <;> assumption)
end
