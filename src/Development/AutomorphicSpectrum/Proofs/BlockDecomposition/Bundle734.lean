module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import GroundTheory.GlobalFields.Adele.Bundle003
public import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import GroundTheory.IdeleRoots.TorusPowers.HeckeTensor
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle006
public import GroundTheory.GlobalFields.TateThesis.AdeleScaling
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
public import Mathlib.GroupTheory.ArchimedeanDensely
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
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle726
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
public import GroundTheory.GlobalFields.Adele.Bundle002
public import GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
public import GroundTheory.GlobalFields.TateThesis.Bundle006

@[expose] public section

section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi.Den

variable {F : Type} [Field F] [NumberField F]

theorem valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (t : F) :
    Valued.v (algebraMap F (Fv F v) t) = v.valuation F t :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t

theorem exists_valued_bound (v : HeightOneSpectrum (𝓞 F)) {C : Set (Fv F v)} (hC : IsCompact C) :
    ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧ ∀ x ∈ C, Valued.v x ≤ γ := by
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Valued.isOpen_valuationSubring _
  obtain ⟨s, -, hs⟩ := hC.elim_nhds_subcover
    (fun x => {y : Fv F v | y - x ∈ v.adicCompletionIntegers F}) (fun x _ => by
      have hopen : IsOpen {y : Fv F v | y - x ∈ v.adicCompletionIntegers F} :=
        hO.preimage (continuous_id.sub continuous_const)
      exact hopen.mem_nhds (by simp))
  obtain ⟨M, hM⟩ := (s.image fun x => Valued.v x).exists_le
  refine ⟨max M 1, (lt_of_lt_of_le zero_lt_one (le_max_right _ _)).ne', fun y hy => ?_⟩
  obtain ⟨x, hx, hxy⟩ := Set.mem_iUnion₂.mp (hs hy)
  have h1 : Valued.v (y - x) ≤ 1 := hxy
  have h2 : Valued.v x ≤ M := hM _ (Finset.mem_image_of_mem _ hx)
  have h3 : y = (y - x) + x := by ring
  rw [h3]
  exact (Valuation.map_add _ _ _).trans
    (max_le (h1.trans (le_max_right _ _)) (h2.trans (le_max_left _ _)))

theorem exists_finset_inv_integral {D : Set (AF F)ˣ} (hD : IsCompact D) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ u ∈ D, ∀ v, v ∉ T →
      ((u⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F := by
  obtain ⟨s, -, hs⟩ := hD.elim_nhds_subcover
    (fun a : (AF F)ˣ => {u : (AF F)ˣ | a⁻¹ * u ∈ IdeleGroup.standardOpenSubgroup F}) (fun a _ => by
      have hopen : IsOpen {u : (AF F)ˣ | a⁻¹ * u ∈ IdeleGroup.standardOpenSubgroup F} :=
        (IdeleGroup.isOpen_standardOpenSubgroup F).preimage (continuous_const.mul continuous_id)
      exact hopen.mem_nhds (by simp [one_mem]))
  have hfin : ∀ a : (AF F)ˣ, {v : HeightOneSpectrum (𝓞 F) |
      ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∉ v.adicCompletionIntegers F}.Finite := fun a =>
    Filter.eventually_cofinite.mp ((a⁻¹ : (AF F)ˣ) : AF F).2.2
  refine ⟨s.biUnion fun a => (hfin a).toFinset, fun u hu v hv => ?_⟩
  obtain ⟨a, ha, hau⟩ := Set.mem_iUnion₂.mp (hs hu)
  have hav : ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F := by
    by_contra hcon
    exact hv (Finset.mem_biUnion.mpr ⟨a, ha, (hfin a).mem_toFinset.mpr hcon⟩)
  have hh := ((IdeleGroup.mem_standardOpenSubgroup F).mp hau v).2
  have hu' : u⁻¹ = (a⁻¹ * u)⁻¹ * a⁻¹ := by group
  have hmul : ((u⁻¹ : (AF F)ˣ) : AF F).2 v =
      (((a⁻¹ * u)⁻¹ : (AF F)ˣ) : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v := by
    conv_lhs => rw [hu']
    rfl
  rw [hmul]
  exact mul_mem hh hav

theorem exists_inv_bound {D : Set (AF F)ˣ} (hD : IsCompact D) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧ ∀ u ∈ D, Valued.v (((u⁻¹ : (AF F)ˣ) : AF F).2 v) ≤ γ := by
  have hc : Continuous fun u : (AF F)ˣ => ((u⁻¹ : (AF F)ˣ) : AF F).2 v :=
    Units.continuous_val.comp ((IdeleGroup.continuous_finiteProj (K := F) v).comp continuous_inv)
  obtain ⟨γ, h0, hγ⟩ := exists_valued_bound v (hD.image hc)
  exact ⟨γ, h0, fun u hu => hγ _ (Set.mem_image_of_mem _ hu)⟩

theorem exists_bound {D : Set (AF F)ˣ} (hD : IsCompact D) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hC : ∀ v ∈ S, IsCompact (C v)) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 F))) (A : HeightOneSpectrum (𝓞 F) → WithZero (Multiplicative ℤ)),
      ∀ u ∈ D, ∀ t : F, (∀ v ∈ S, algebraMap F (Fv F v) t * (u : AF F).2 v ∈ C v) →
        (∀ v, v ∉ S → algebraMap F (Fv F v) t * (u : AF F).2 v ∈ v.adicCompletionIntegers F) →
        ∀ v, v.valuation F t ≤ if v ∈ T then A v else 1 := by
  obtain ⟨T₀, hT₀⟩ := exists_finset_inv_integral hD
  choose B _ hB using fun v => exists_inv_bound hD v
  have hG : ∀ v : HeightOneSpectrum (𝓞 F), ∃ γ : WithZero (Multiplicative ℤ), v ∈ S →
      ∀ x ∈ C v, Valued.v x ≤ γ := fun v => by
    by_cases hv : v ∈ S
    · obtain ⟨γ, -, h⟩ := exists_valued_bound v (hC v hv)
      exact ⟨γ, fun _ => h⟩
    · exact ⟨1, fun h => absurd h hv⟩
  choose G hG using hG
  refine ⟨T₀ ∪ S, fun v => max (G v) 1 * B v, fun u hu t h1 h2 v => ?_⟩
  have hinv : (u : AF F).2 v * ((u⁻¹ : (AF F)ˣ) : AF F).2 v = 1 :=
    congrArg (fun a : AF F => a.2 v) (Units.mul_inv u)
  have hx : algebraMap F (Fv F v) t =
      (algebraMap F (Fv F v) t * (u : AF F).2 v) * ((u⁻¹ : (AF F)ˣ) : AF F).2 v := by
    rw [mul_assoc, hinv, mul_one]
  have hval : v.valuation F t = Valued.v (algebraMap F (Fv F v) t * (u : AF F).2 v) *
      Valued.v (((u⁻¹ : (AF F)ˣ) : AF F).2 v) := by
    rw [← valued_algebraMap, ← map_mul, ← hx]
  have hfirst : Valued.v (algebraMap F (Fv F v) t * (u : AF F).2 v) ≤ max (G v) 1 := by
    by_cases hv : v ∈ S
    · exact (hG v hv _ (h1 v hv)).trans (le_max_left _ _)
    · have a : Valued.v (algebraMap F (Fv F v) t * (u : AF F).2 v) ≤ 1 := h2 v hv
      exact a.trans (le_max_right _ _)
  by_cases hvT : v ∈ T₀ ∪ S
  · rw [if_pos hvT, hval]
    exact mul_le_mul' hfirst (hB v u hu)
  · rw [if_neg hvT, hval]
    have hvS : v ∉ S := fun h => hvT (Finset.mem_union_right _ h)
    have hvT₀ : v ∉ T₀ := fun h => hvT (Finset.mem_union_left _ h)
    have a1 : Valued.v (algebraMap F (Fv F v) t * (u : AF F).2 v) ≤ 1 := h2 v hvS
    have a2 : Valued.v (((u⁻¹ : (AF F)ˣ) : AF F).2 v) ≤ 1 := hT₀ u hu v hvT₀
    simpa using mul_le_mul' a1 a2

theorem valuation_natCast_le_one (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    v.valuation F (n : F) ≤ 1 := by
  have := HeightOneSpectrum.valuation_le_one (K := F) v (n : 𝓞 F)
  simpa using this

theorem exists_nat_mul_le_one (v : HeightOneSpectrum (𝓞 F)) (A : WithZero (Multiplicative ℤ)) :
    ∃ n : ℕ, 0 < n ∧ v.valuation F (n : F) * A ≤ 1 := by
  by_cases hA : A = 0
  · exact ⟨1, one_pos, by simp [hA]⟩
  have hlt : v.valuation F ((Ideal.absNorm v.asIdeal : ℕ) : F) < 1 := by
    have h := (v.valuation_lt_one_iff_mem (K := F) ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)).2
      (Ideal.absNorm_mem _)
    simpa using h
  obtain ⟨k, hk⟩ := exists_pow_lt₀ hlt (Units.mk0 _ (inv_ne_zero hA))
  have hpos : 0 < Ideal.absNorm v.asIdeal := by
    refine Nat.pos_of_ne_zero fun h => v.ne_bot ?_
    exact Ideal.absNorm_eq_zero_iff.mp h
  refine ⟨Ideal.absNorm v.asIdeal ^ k, pow_pos hpos k, ?_⟩
  have h3 : v.valuation F (((Ideal.absNorm v.asIdeal ^ k : ℕ)) : F) < A⁻¹ := by
    push_cast
    rw [map_pow]
    exact hk
  calc v.valuation F (((Ideal.absNorm v.asIdeal ^ k : ℕ)) : F) * A ≤ A⁻¹ * A :=
        mul_le_mul' h3.le le_rfl
    _ = 1 := inv_mul_cancel₀ hA

theorem common_denominator (F : Type) [Field F] [NumberField F] (D : Set (AF F)ˣ) (hD : IsCompact D)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (hC : ∀ v ∈ S, IsCompact (C v)) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ D, ∀ t : F, (∀ v ∈ S, algebraMap F (Fv F v) t * (u : AF F).2 v ∈ C v) →
      (∀ v, v ∉ S → algebraMap F (Fv F v) t * (u : AF F).2 v ∈ v.adicCompletionIntegers F) →
      ∃ y : 𝓞 F, (y : F) = N * t := by
  obtain ⟨T, A, hA⟩ := exists_bound hD S C hC
  choose n hn0 hn using fun v => exists_nat_mul_le_one (F := F) v (A v)
  refine ⟨∏ v ∈ T, n v, Finset.prod_pos fun v _ => hn0 v, fun u hu t h1 h2 => ?_⟩
  refine exists_eq_of_forall_mem_adicCompletionIntegers F _ fun v => ?_
  rw [coe_mem_adicCompletionIntegers_iff, map_mul]
  have ht := hA u hu t h1 h2 v
  by_cases hv : v ∈ T
  · rw [if_pos hv] at ht
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem n hv
    have hN : v.valuation F (((∏ v ∈ T, n v : ℕ)) : F) ≤ v.valuation F (n v : F) := by
      rw [hm]
      push_cast
      rw [map_mul]
      simpa using mul_le_mul' (le_refl (v.valuation F (n v : F))) (valuation_natCast_le_one v m)
    exact (mul_le_mul' hN ht).trans (hn v)
  · rw [if_neg hv] at ht
    simpa using mul_le_mul' (valuation_natCast_le_one v (∏ v ∈ T, n v)) ht

end GlobalTheory.CompanionTheory.BasePsi.Den

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open GroundTheory.Global.AdeleBaseChange
open scoped TensorProduct ENNReal NNReal Matrix Classical NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ModConj

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_involution_eq {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (e : G ≃ₜ+ G) (he2 : ∀ x, e (e x) = x) (ν : Measure G) [ν.IsAddHaarMeasure] [SecondCountableTopology G] :
    ν.map e = ν := by
  haveI : (ν.map e).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν e
  obtain ⟨b, hb⟩ : ∃ b : ℝ≥0, ν.map e = b • ν :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (ν.map e) ν⟩
  have he : Measurable e := e.continuous.measurable
  have h2 : ν.map (e ∘ e) = (b * b) • ν := by
    rw [← Measure.map_map he he, hb, Measure.map_smul _ he.aemeasurable, hb, smul_smul]
  have hid : (e ∘ e : G → G) = id := funext he2
  rw [hid, Measure.map_id] at h2
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : G)
  have hpos : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hK0).ne'
  have hfin : ν K ≠ ∞ := hK.measure_lt_top.ne
  have hbb : b * b = 1 := by
    have h3 : ((b * b : ℝ≥0) • ν) K = ((1 : ℝ≥0) • ν) K := by rw [← h2, one_smul]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).1 h3
  have hb1 : b = 1 := by
    have := (mul_self_eq_one_iff (a := (b : ℝ))).1 (by exact_mod_cast hbb)
    rcases this with h | h
    · exact_mod_cast h
    · have := b.2; simp only [NNReal.val_eq_coe] at this; linarith
  rw [hb, hb1, one_smul]

def conjA (σ : E →ₐ[F] E) : 𝔸[E] →+* 𝔸[E] :=
  (GroundTheory.BlockD.ThmBHecke.adeleEquiv F E).toRingEquiv.toRingHom.comp
    ((sigR (AF F) σ).comp (GroundTheory.BlockD.ThmBHecke.adeleEquiv F E).symm.toRingEquiv.toRingHom)

theorem conjA_apply (σ : E →ₐ[F] E) (y : 𝔸[E]) :
    conjA σ y = GroundTheory.BlockD.ThmBHecke.adeleEquiv F E
      (sigR (AF F) σ ((GroundTheory.BlockD.ThmBHecke.adeleEquiv F E).symm y)) := rfl

theorem sig_sig {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (z : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, hσ]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem continuous_sig {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) : Continuous (sigR (AF F) σ) :=
  (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)).2.2.2.2.1

theorem sigma_sigma {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2, hcm.2.2.2, star_star]

def conjE {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) : 𝔸[E] ≃ₜ+ 𝔸[E] where
  toFun := conjA σ
  invFun := conjA σ
  left_inv y := by
    simp [conjA_apply, sig_sig (sigma_sigma hcm)]
  right_inv y := by
    simp [conjA_apply, sig_sig (sigma_sigma hcm)]
  map_add' := map_add _
  continuous_toFun := GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv.comp
    ((continuous_sig hcm).comp GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv_symm)
  continuous_invFun := GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv.comp
    ((continuous_sig hcm).comp GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv_symm)

end

theorem ideleModule_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ x : (AF F ⊗[F] E)ˣ,
    (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E
        (Units.map (sigR (AF F) σ).toMonoidHom x)) : ℝ) =
      (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) := by
  intro F E _ _ _ _ _ σ hcm x
  letI : MeasurableSpace 𝔸[E] := measurableSpace_adeleRing E
  set a := GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x with ha
  set a' := GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (Units.map (sigR (AF F) σ).toMonoidHom x) with ha'
  set e := conjE hcm with he
  set ν := adeleMeasure E with hν
  have hinv : ∀ y, e (e y) = y := fun y => e.left_inv y
  have hcoe : ∀ y, e y = conjA σ y := fun _ => rfl
  have hea : e (a : 𝔸[E]) = (a' : 𝔸[E]) := by
    rw [hcoe, conjA_apply, ha, ha', GroundTheory.BlockD.ThmBHecke.coe_ideleEquiv,
      GroundTheory.BlockD.ThmBHecke.coe_ideleEquiv, AlgEquiv.symm_apply_apply]
    rfl
  have key : ∀ y : 𝔸[E], a' • y = e (a • e y) := fun y => by
    rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, hcoe (_ * _), map_mul, ← hcoe, ← hcoe,
      hinv, hea]
  have hmeas : Measurable e := e.continuous.measurable
  have hm : Measurable (fun y : 𝔸[E] => a • y) := (Homeomorph.smul a).continuous.measurable
  have hνe : ν.map e = ν := map_involution_eq e hinv ν
  have hfun : (fun y : 𝔸[E] => a' • y) = e ∘ (fun y => a • y) ∘ e := funext key
  have h1 : ν.map (fun y : 𝔸[E] => a' • y) =
      ENNReal.ofReal ((IdeleGroup.ideleModule E a : ℝ))⁻¹ • ν := by
    rw [hfun, ← Measure.map_map hmeas (hm.comp hmeas), ← Measure.map_map hm hmeas, hνe, hν,
      map_smul_adeleMeasure, Measure.map_smul _ hmeas.aemeasurable, ← hν, hνe]
  have h2 := map_smul_adeleMeasure (K := E) a'
  rw [← hν, h1] at h2
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : 𝔸[E])
  have hpos : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hK0).ne'
  have hfin : ν K ≠ ∞ := hK.measure_lt_top.ne
  have h3 := congrArg (fun m : Measure 𝔸[E] => m K) h2
  simp only [Measure.smul_apply, smul_eq_mul] at h3
  have h4 := (ENNReal.mul_left_inj hpos hfin).1 h3
  have h5 := (ENNReal.ofReal_eq_ofReal_iff (inv_nonneg.2 (IdeleGroup.ideleModule E a).2.le)
    (inv_nonneg.2 (IdeleGroup.ideleModule E a').2.le)).1 h4
  exact (inv_injective h5).symm

end GlobalTheory.CompanionTheory.SW.ModConj
end
end
