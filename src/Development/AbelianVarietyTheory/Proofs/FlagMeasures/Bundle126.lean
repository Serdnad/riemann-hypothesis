module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle098
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008

@[expose] public section

section

open MeasureTheory MeasureTheory.Measure Filter Topology
open scoped NNReal ENNReal

namespace GlobalTheory.ModularAutomorphism

section Group

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]

theorem smul_haar_cancel (ρ : Measure H) [ρ.IsHaarMeasure] {c d : ℝ≥0} (h : c • ρ = d • ρ) : c = d := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : H)
  have h0 : ρ K ≠ 0 := (measure_pos_of_mem_nhds ρ hK1).ne'
  have h1 : ρ K ≠ ∞ := hK.measure_lt_top.ne
  have h2 : (c : ℝ≥0∞) * ρ K = (d : ℝ≥0∞) * ρ K := by
    have := congrArg (fun τ : Measure H => τ K) h
    exact this
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 h1).1 h2)

theorem map_right_eq (ρ : Measure H) [ρ.IsHaarMeasure] (g : H) :
    ρ.map (· * g) = modularCharacterFun g • ρ := by
  rw [modularCharacterFun_eq_haarScalarFactor ρ g]
  exact isMulLeftInvariant_eq_smul _ ρ

theorem modular_aut (φ : H ≃ₜ* H) (g : H) : modularCharacterFun (φ g) = modularCharacterFun g := by
  let ρ : Measure H := Measure.haar
  have hφ : Measurable φ := φ.continuous.measurable
  haveI : (ρ.map φ).IsHaarMeasure := φ.toMulEquiv.isHaarMeasure_map ρ φ.continuous φ.symm.continuous
  apply smul_haar_cancel (ρ.map φ)
  rw [← map_right_eq, ← Measure.map_smul, ← map_right_eq, map_map (measurable_mul_const _) hφ,
    map_map hφ (measurable_mul_const _)]
  · congr 1
    funext x
    simp
  · exact hφ.aemeasurable

theorem continuous_modular : Continuous fun g : H => (modularCharacterFun g : ℝ) := by
  let ρ : Measure H := Measure.haar
  obtain ⟨f, hfc, hf0, hf1⟩ := exists_continuous_nonneg_pos (1 : H)
  have hI : ∫ x, f x ∂ρ ≠ 0 :=
    ne_of_gt (f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hf0 hf1)
  have hc : Continuous fun x : H => ∫ y, f (y⁻¹ * x) ∂ρ.inv :=
    continuous_integral_apply_inv_mul f.continuous hfc
  have he : ∀ g : H, (modularCharacterFun g : ℝ) = (∫ y, f (y⁻¹ * g) ∂ρ.inv) / ∫ x, f x ∂ρ := by
    intro g
    rw [modularCharacterFun_eq_haarScalarFactor ρ g,
      haarScalarFactor_eq_integral_div _ _ f.continuous hfc hI,
      integral_map (measurable_mul_const g).aemeasurable f.continuous.aestronglyMeasurable,
      Measure.inv_def, integral_map measurable_inv.aemeasurable
        (by fun_prop : Continuous fun y : H => f (y⁻¹ * g)).aestronglyMeasurable]
    simp
  simp_rw [he]
  exact hc.div_const _

theorem map_inv_eq (ρ : Measure H) [ρ.IsHaarMeasure] [ρ.IsMulRightInvariant] : ρ.inv = ρ := by
  have h : ρ.inv = haarScalarFactor ρ.inv ρ • ρ := isMulLeftInvariant_eq_smul _ ρ
  set c := haarScalarFactor ρ.inv ρ
  have h2 : (c * c) • ρ = (1 : ℝ≥0) • ρ := by
    have h3 : ρ.inv.inv = c • ρ.inv := by
      conv_lhs => rw [h]
      rw [Measure.inv_def, Measure.map_smul, ← Measure.inv_def]
      exact measurable_inv.aemeasurable
    rw [Measure.inv_inv, h, smul_smul] at h3
    rw [one_smul]
    exact h3.symm
  have h4 : c * c = 1 := smul_haar_cancel ρ h2
  have h5 : c = 1 := by
    have : (c : ℝ) * c = 1 := by exact_mod_cast h4
    have h0 : (0 : ℝ) ≤ c := c.2
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  rw [h, h5, one_smul]

end Group

def conjAut {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : Subgroup G) (b : G)
    (h1 : ∀ m ∈ N, b * m * b⁻¹ ∈ N) (h2 : ∀ m ∈ N, b⁻¹ * m * b ∈ N) : N ≃ₜ* N where
  toFun m := ⟨b * m * b⁻¹, h1 m m.2⟩
  invFun m := ⟨b⁻¹ * m * b, h2 m m.2⟩
  left_inv m := Subtype.ext (by simp [mul_assoc])
  right_inv m := Subtype.ext (by simp [mul_assoc])
  map_mul' m n := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  continuous_invFun := Continuous.subtype_mk (by fun_prop) _

theorem unimodular_of_contracted {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (N : Subgroup G) (hN : IsClosed (N : Set G)) {ν : Measure G} (hν : GlobalTheory.Dec.IsHaarSub (N : Set G) ν)
    (a : ℝ → G) (h1 : ∀ s : ℝ, ∀ m ∈ N, a s * m * (a s)⁻¹ ∈ N)
    (h2 : ∀ s : ℝ, ∀ m ∈ N, (a s)⁻¹ * m * a s ∈ N)
    (h3 : ∀ m ∈ N, Tendsto (fun s : ℝ => a s * m * (a s)⁻¹) atBot (nhds (1 : G))) :
    (∀ m ∈ N, ν.map (fun x : G => x * m) = ν) ∧ ν.map (fun x : G => x⁻¹) = ν := by
  obtain ⟨hne, hfin, hcar, hleft⟩ := hν
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hE : MeasurableEmbedding (Subtype.val : N → G) := MeasurableEmbedding.subtype_coe hN.measurableSet
  have hv : Measurable (Subtype.val : N → G) := hE.measurable
  let μ : Measure N := ν.comap Subtype.val
  have hμ : μ.map Subtype.val = ν := by
    rw [hE.map_comap, Subtype.range_coe_subtype]
    exact Measure.restrict_eq_self_of_ae_mem hcar
  haveI : μ.IsMulLeftInvariant := ⟨fun g => by
    apply hE.map_injective
    change (μ.map (g * ·)).map Subtype.val = μ.map Subtype.val
    have : (Subtype.val : N → G) ∘ (g * ·) = (fun x : G => (g : G) * x) ∘ Subtype.val := rfl
    rw [map_map hv (measurable_const_mul g), this, ← map_map (measurable_const_mul _) hv, hμ, hleft g g.2]⟩
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => by
    rw [hE.comap_apply]
    exact (hK.image continuous_subtype_val).measure_lt_top⟩
  haveI : NeZero μ := ⟨fun h => hne (by rw [← hμ, h, Measure.map_zero])⟩
  haveI : TopologicalSpace.PseudoMetrizableSpace N := inferInstance
  haveI : μ.Regular := inferInstance
  haveI : μ.IsHaarMeasure := {}
  have hmod : ∀ g : N, modularCharacterFun g = 1 := by
    intro g
    have t1 : Tendsto (fun s : ℝ => conjAut N (a s) (h1 s) (h2 s) g) atBot (nhds (1 : N)) :=
      tendsto_subtype_rng.2 (h3 g g.2)
    have t2 := ((continuous_modular (H := N)).tendsto 1).comp t1
    simp only [Function.comp_def, modular_aut, modularCharacterFun_map_one] at t2
    exact_mod_cast tendsto_const_nhds_iff.1 t2
  have hr : ∀ g : N, μ.map (· * g) = μ := fun g => by rw [map_right_eq, hmod, one_smul]
  haveI : μ.IsMulRightInvariant := ⟨hr⟩
  refine ⟨fun m hm => ?_, ?_⟩
  · have : (fun x : G => x * m) ∘ (Subtype.val : N → G) = Subtype.val ∘ (· * (⟨m, hm⟩ : N)) := rfl
    conv_lhs => rw [← hμ]
    rw [map_map (measurable_mul_const m) hv, this, ← map_map hv (measurable_mul_const _), hr, hμ]
  · have : (fun x : G => x⁻¹) ∘ (Subtype.val : N → G) = Subtype.val ∘ (Inv.inv : N → N) := rfl
    conv_lhs => rw [← hμ]
    rw [map_map measurable_inv hv, this, ← map_map hv measurable_inv, ← Measure.inv_def, map_inv_eq, hμ]

end GlobalTheory.ModularAutomorphism
end

section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

namespace GlobalTheory.Count.FrameMajorant

theorem signed_cs {n : ℕ} (ε : Fin n → Bool) (a b : Fin n → ℂ) :
    ‖star a ⬝ᵥ (Jm ε *ᵥ b)‖ ≤ Formalism.HermitianLatticesTheory.cnorm a * Formalism.HermitianLatticesTheory.cnorm b := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  have h1 : ‖star a ⬝ᵥ (Jm ε *ᵥ b)‖ ≤ ∑ i, ‖a i‖ * ‖b i‖ := by
    unfold dotProduct
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => le_of_eq ?_)
    simp only [Jm, Matrix.mulVec_diagonal, norm_mul, Pi.star_apply, norm_star]
    split_ifs <;> simp
  exact h1.trans (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)

theorem cnorm_unitary {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (a : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (u *ᵥ a) = Formalism.HermitianLatticesTheory.cnorm a := by
  have key : ∀ c : Fin n → ℂ, ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) = star c ⬝ᵥ c := by
    intro c
    unfold dotProduct
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  unfold Formalism.HermitianLatticesTheory.cnorm
  congr 1
  have : star (u *ᵥ a) ⬝ᵥ (u *ᵥ a) = star a ⬝ᵥ a := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]
  exact_mod_cast (key _).trans (this.trans (key _).symm)

theorem cnorm_inv_mul_unitary {n : ℕ} (X u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (a : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm ((X * u)⁻¹ *ᵥ a) = Formalism.HermitianLatticesTheory.cnorm (X⁻¹ *ᵥ a) := by
  rw [Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hu, ← Matrix.mulVec_mulVec]
  apply cnorm_unitary
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.1 hu

variable (I : AutInst)

theorem comap_bijective :
    Function.Bijective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) := by
  refine ⟨fun w w' h => ?_, ?_⟩
  · have hw : ∀ w : InfinitePlace I.E, w = InfinitePlace.mk (I.φ (w.comap (algebraMap I.F I.E))) := by
      intro w
      rcases Test.embedding_cases I w with h | h
      · rw [← h, InfinitePlace.mk_embedding]
      · rw [← InfinitePlace.mk_conjugate_eq, ← h, InfinitePlace.mk_embedding]
    have h' : w.comap (algebraMap I.F I.E) = w'.comap (algebraMap I.F I.E) := h
    rw [hw w, hw w', h']
  · intro v
    refine ⟨InfinitePlace.mk (I.φ v), ?_⟩
    have h2 : (I.φ v).comp (algebraMap I.F I.E) = v.embedding := RingHom.ext (I.φ_over v)
    show (InfinitePlace.mk (I.φ v)).comap _ = v
    rw [InfinitePlace.comap_mk, h2, InfinitePlace.mk_embedding]

theorem card_places : Fintype.card (InfinitePlace I.F) = I.f := by
  have hR := I.cm.totReal
  rw [AutInst.f, IsTotallyReal.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]

theorem frm_unit (x : I.GA) (w : InfinitePlace I.E) : IsUnit (frm I x w).det := by
  have h := congrArg (fun M => (Jm (I.ε (w.comap (algebraMap I.F I.E))) * M).det) (Test.frm_frame I x w)
  simp only [Jm_mul_self, Matrix.det_mul, Matrix.det_one] at h
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  simp [h0] at h

theorem hform_le (x : I.GA) (w : InfinitePlace I.E) (y z : Fin I.n → I.E) :
    ‖w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z)‖ ≤
      Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y * Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w z := by
  have hc := I.cm.cmUnram.2.1
  have hX := frm_unit I x w
  have hback : ∀ y, frm I x w *ᵥ Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = fun i => w.embedding (y i) := by
    intro y
    unfold Formalism.HermitianLatticesTheory.fcoord
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec]
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  have h1 : w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z) =
      star (fun i => w.embedding (y i)) ⬝ᵥ (I.J.map w.embedding *ᵥ fun i => w.embedding (z i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply,
      Finset.mul_sum, starRingEnd_apply, hc, mul_assoc]
  rw [h1, ← hback y, ← hback z, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Test.frm_frame I x w]
  exact signed_cs _ _ _

theorem normAt_mul (x : I.GA) (w : InfinitePlace I.E) (k : I.GA) (hk : ∀ v, uMat (k.1 v) ∈ Kset (I.ε v))
    (y : Fin I.n → I.E) :
    Formalism.HermitianLatticesTheory.normAt (bas I) (frm I (x * k)) w y = Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y := by
  set v := w.comap (algebraMap I.F I.E) with hv
  have hu : (uMat (k.1 v))ᴴ * uMat (k.1 v) = 1 := (hk v).1.1
  have hm : uMat ((x * k).1 v) = uMat (x.1 v) * uMat (k.1 v) := rfl
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord frm
  simp only [← hv]
  split_ifs with h
  · rw [hm, ← Matrix.mul_assoc]
    exact cnorm_inv_mul_unitary _ _ hu _
  · rw [hm, ← Matrix.mul_assoc, Matrix.map_mul]
    apply cnorm_inv_mul_unitary
    have hT : ∀ M : Matrix (Fin I.n) (Fin I.n) ℂ, (M.map (starRingEnd ℂ))ᴴ = Mᴴ.map (starRingEnd ℂ) := by
      intro M; ext i j; simp
    rw [hT, ← Matrix.map_mul, hu]
    simp

theorem frames_give_majorants : ∀ (I : AutInst) (x : I.GA), IsTotallyComplex I.E ∧ nPl I.E = I.f ∧ Fintype.card (InfinitePlace I.F) = I.f ∧ Function.Bijective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) ∧ ∀ w : InfinitePlace I.E, IsUnit (frm I x w).det ∧ (frm I x w)ᴴ * I.J.map w.embedding * frm I x w = Jm (I.ε (w.comap (algebraMap I.F I.E))) ∧ (∀ y z : (Fin I.n → I.E), ‖w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z)‖ ≤ Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y * Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w z) ∧ ∀ k : I.GA, (∀ v, uMat (k.1 v) ∈ Kset (I.ε v)) → ∀ y, Formalism.HermitianLatticesTheory.normAt (bas I) (frm I (x * k)) w y = Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y := by
  intro I x
  refine ⟨I.cm.cmUnram.1, ?_, card_places I, comap_bijective I, fun w =>
    ⟨frm_unit I x w, Test.frm_frame I x w, hform_le I x w, normAt_mul I x w⟩⟩
  rw [nPl, Fintype.card_of_bijective (comap_bijective I), card_places]

end GlobalTheory.Count.FrameMajorant
end

section

open NumberField Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.NearLowerCompare

open Formalism.MainNotions.S GlobalTheory.Count Formalism.HN

section General

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
  (X : InfinitePlace K → Matrix ι ι ℂ)

end General

variable (I : AutInst)

theorem lamX_isLattice (x : I.GA) : Submodule.IsLattice I.E (lamX I x) := by
  have h := Formalism.UG.P.global_lattice_isLattice_holds I.F I.E (Fin I.n) I.L (Module.Finite.iff_fg.2 I.L_fg) I.L_span
    (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
  have e1 : Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L = I.Lf := by
    unfold Formalism.UG.latS AutInst.Lf lamAf
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨z, rfl⟩; exact ⟨z, z.2, rfl⟩
  have e : lamX I x = Formalism.UG.CS.globLat (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) I.L := by
    ext y
    rw [GlobalTheory.Count.Test.mem_lamX, ← e1]
    exact Iff.rfl
  rw [e]; exact h

theorem frm_isUnit (x : I.GA) (w : InfinitePlace I.E) : IsUnit (frm I x w).det := by
  have h : ∀ v, IsUnit (I.P v * uMat (x.1 v)) := fun v => (I.P_unit v).mul (Units.isUnit _)
  rw [← Matrix.isUnit_iff_isUnit_det]
  unfold frm
  split_ifs
  · exact h _
  · exact (h _).map (starRingEnd ℂ).mapMatrix

theorem subsingleton_GA (hn : I.n = 0) : Subsingleton I.GA := by
  have : IsEmpty (Fin I.n) := by rw [hn]; infer_instance
  refine ⟨fun a b => Prod.ext (funext fun v => ?_) ?_⟩
  · exact Subtype.ext (Units.ext (Subsingleton.elim _ _))
  · exact Subtype.ext (Units.ext (Subsingleton.elim _ _))

end GlobalTheory.NearLowerCompare
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem muG_preimage_conj {n : ℕ} (ε : Fin n → Bool) (u : Formalism.REAL.UJ ε) (B : Set (Formalism.REAL.UJ ε)) :
    Formalism.REAL.muG ε ((fun g => u⁻¹ * g * u) ⁻¹' B) = Formalism.REAL.muG ε B := by
  haveI : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  haveI : (Formalism.REAL.muG ε).IsHaarMeasure := by unfold Formalism.REAL.muG; infer_instance
  have : (fun g => u⁻¹ * g * u) ⁻¹' B = (fun g => u⁻¹ * g) ⁻¹' ((fun g => g * u) ⁻¹' B) := rfl
  rw [this, measure_preimage_mul, measure_preimage_mul_right]

theorem gauge_map_of_iso : ∀ (n n' : ℕ) (ε : Fin n → Bool) (ε' : Fin n' → Bool), n = n' → ∀ (T : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε') (u : Formalism.REAL.UJ ε), (∀ g, Formalism.REAL.hs (uMat (T (u * g * u⁻¹)) - 1) = Formalism.REAL.hs (uMat g - 1)) → ∀ c c' : ℝ, IsGauge ε c → IsGauge ε' c' → (ENNReal.ofReal c • Formalism.REAL.muG ε).map T = ENNReal.ofReal c' • Formalism.REAL.muG ε' := by
  intro n n' ε ε' hn T u hT c c' hc hc'
  subst hn
  haveI : (Formalism.REAL.muG ε).IsHaarMeasure := by unfold Formalism.REAL.muG; infer_instance
  haveI : (Formalism.REAL.muG ε').IsHaarMeasure := by unfold Formalism.REAL.muG; infer_instance
  haveI : ((Formalism.REAL.muG ε).map T).IsHaarMeasure := T.isHaarMeasure_map _
  obtain ⟨a, ha⟩ : ∃ a : NNReal, (Formalism.REAL.muG ε).map T = a • Formalism.REAL.muG ε' :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have hball : ∀ r : ℝ, Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} =
      a * Formalism.REAL.muG ε' {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} := by
    intro r
    have h1 := congrArg (fun m : Measure (Formalism.REAL.UJ ε') =>
      m {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}) ha
    have h2 := MeasurableEquiv.map_apply (μ := Formalism.REAL.muG ε) T.toHomeomorph.toMeasurableEquiv
      {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}
    have h3 : (T : Formalism.REAL.UJ ε → Formalism.REAL.UJ ε') ⁻¹' {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} =
        (fun g => u⁻¹ * g * u) ⁻¹' {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} := by
      ext g
      have := hT (u⁻¹ * g * u)
      rw [show u * (u⁻¹ * g * u) * u⁻¹ = g by group] at this
      simp only [Set.mem_preimage, Set.mem_setOf_eq, this]
    change (Formalism.REAL.muG ε).map T _ = Formalism.REAL.muG ε ((T : Formalism.REAL.UJ ε → Formalism.REAL.UJ ε') ⁻¹' _) at h2
    rw [h3, muG_preimage_conj] at h2
    rw [← h2]
    simpa using h1
  have hω : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have hca : c' = c * a := by
    have h1 := Filter.Tendsto.const_mul c' hc
    have h2 := Filter.Tendsto.const_mul (c * a) hc'
    have h3 := tendsto_nhds_unique h1 (h2.congr fun r => by
      rw [hball r, ENNReal.toReal_mul, ENNReal.coe_toReal]; ring)
    exact mul_right_cancel₀ hω.ne' h3
  rw [Measure.map_smul _ (show AEMeasurable (⇑T) (Formalism.REAL.muG ε) from T.continuous.measurable.aemeasurable), ha, hca, ENNReal.ofReal_mul' a.coe_nonneg, ENNReal.ofReal_coe_nnreal, mul_smul]
  rfl

end GlobalTheory.FlagMeas
end

section

open Matrix Finset Formalism.MainNotions.S GlobalTheory.Dec

namespace GlobalTheory.PhiTriangular

theorem sum_sInt_from {n : ℕ} (lam : Fin n → ℝ) (l : Fin n) :
    ∑ i : Fin n, (if l ≤ i then sInt lam i else 0) = muInt lam l := by
  let m : ℕ → ℤ := fun k => if h : k < n then muInt lam ⟨k, h⟩ else 0
  have h1 : ∀ i : Fin n, (if l ≤ i then sInt lam i else 0) =
      m (max i.val l.val) - m (max (i.val + 1) l.val) := by
    intro i
    by_cases h : l ≤ i
    · have h' : l.val ≤ i.val := h
      rw [if_pos h, max_eq_left h', max_eq_left (by omega : l.val ≤ i.val + 1)]
      simp only [m, sInt, dif_pos i.isLt]
    · have h' : i.val < l.val := by simpa using h
      rw [if_neg h, max_eq_right h'.le, max_eq_right (by omega : i.val + 1 ≤ l.val), sub_self]
  simp only [h1]
  rw [Fin.sum_univ_eq_sum_range (fun k => m (max k l.val) - m (max (k + 1) l.val)) n,
    Finset.sum_range_sub' (fun k => m (max k l.val)) n, max_eq_right (Nat.zero_le _),
    max_eq_left l.isLt.le]
  simp [m]

theorem prod_castLE_succ {n : ℕ} (d : Fin n → ℂ) (i : Fin n) :
    ∏ j : Fin (i.val + 1), d (Fin.castLE i.isLt j) = ∏ l : Fin n, if l ≤ i then d l else 1 := by
  refine Finset.prod_of_injOn (Fin.castLE i.isLt) ((Fin.castLE_injective _).injOn) (by simp) ?_ ?_
  · intro k _ hk
    rw [if_neg]
    intro h
    exact hk ⟨⟨k.val, Nat.lt_succ_of_le h⟩, by simp, rfl⟩
  · intro j _
    rw [if_pos]
    exact Nat.le_of_lt_succ j.isLt

theorem zpow_finset_sum {ι : Type} (s : Finset ι) (f : ι → ℤ) {a : ℂ} (ha : a ≠ 0) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ ha, ih]

theorem prod_partial_zpow {n : ℕ} (lam : Fin n → ℝ) (d : Fin n → ℂ) (hd : ∀ l, d l ≠ 0) :
    ∏ i : Fin n, (∏ j : Fin (i.val + 1), d (Fin.castLE i.isLt j)) ^ (-(sInt lam i)) =
      ∏ l, d l ^ (-(muInt lam l)) := by
  simp only [prod_castLE_succ, ← Finset.prod_zpow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← sum_sInt_from, ← Finset.sum_neg_distrib, zpow_finset_sum _ _ (hd l)]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : l ≤ i <;> simp [h]

theorem phiTri : PhiTri := by
  intro n lam c z c' hc hc' hd hz
  have hd' : ∀ l, c l l * c' l l ≠ 0 := fun l => mul_ne_zero (hd l).1 (hd l).2
  refine ⟨fun i => ?_, ?_⟩
  · rw [GlobalTheory.LeadMinorTri.leadMinor_lower_mul_mul_upper n c z c' hc hc']
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => hd' _) (hz i)
  · unfold Phi
    simp only [GlobalTheory.LeadMinorTri.leadMinor_lower_mul_mul_upper n c z c' hc hc', mul_zpow _ (leadMinor z _ _)]
    rw [Finset.prod_mul_distrib, prod_partial_zpow lam (fun l => c l l * c' l l) hd']

end GlobalTheory.PhiTriangular
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem locDec_of_decGap_gapGe : DecGap → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → GapGe B h →
    (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h := by
  intro hD B d h hds hgap hh v g
  obtain ⟨h1, h2, h3, -⟩ := hds v
  have hw : B.w v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v) := h3.2
  have hn : ‖B.w v‖ = 1 := h3.1
  have := (hD _ _ _ _ _ h1 h2 h (hgap v) (hh v) (uMat g) g.2 _ hw _ hw).2
  simpa [hn] using this

end GlobalTheory.Dec
end
