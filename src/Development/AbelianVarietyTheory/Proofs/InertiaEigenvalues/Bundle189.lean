module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle056
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle094
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle120
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle058
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle174
public import Mathlib.RingTheory.Norm.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
public import Mathlib.RingTheory.Trace.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle171
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle091
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle170
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle169
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle095
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle166
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle119
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle141
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle168
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle173
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilFOpNOpFOpGauss
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.ImgSec

theorem charpoly_companion_coeff : ∀ (k : Type) [CommRing k] (r : ℕ) (p : Fin r → k) (i : Fin r), (companion p).charpoly.coeff (i : ℕ) = p i := GlobalTheory.T.companionMatrixOfCoeffs_charpoly_coeff_eq
theorem exists_compact_open_nhd : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (U : Set (Inv r F)) (a₀ : Inv r F), IsOpen U → a₀ ∈ U → ∃ Ω : Set (Inv r F), IsCompact Ω ∧ IsOpen Ω ∧ a₀ ∈ Ω ∧ Ω ⊆ U := GlobalTheory.T.borderedMatrixInvariantSpace_exists_compact_open_subset
theorem isCompact_orbit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E) (h : Inv r F → Matrix (Fin r) (Fin r) E), IsCompact Ω → ContinuousOn s Ω → ContinuousOn h Ω → (∀ a ∈ Ω, IsUnit (h a).det ∧ Bm (s a).toGl = h a) → ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} := GlobalTheory.T.unitaryOrbit_proper_of_invertible_krylovColumns
theorem continuousOn_mkX : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (h : Inv r F → Matrix (Fin r) (Fin r) E), ContinuousOn h Ω → (∀ a ∈ Ω, IsUnit (h a).det) → ContinuousOn (fun a => GlobalTheory.JR.ImgSec.mkX a (h a)) Ω := GlobalTheory.T.continuousOn_hermitianBlockMatrixOfInvariants

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}

theorem hasInv_mkX {a : Inv r F} {h : Matrix (Fin r) (Fin r) E} (hh : hᴴ * h = (hankel a).map (algebraMap F E))
    (hd : IsUnit h.det) : HasInv (mkX a h) a := by
  unfold HasInv inv
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i
    show ((mkX a h).1.1).charpoly.coeff i = algebraMap F E (a.1 i)
    rw [mkX_fst hh hd]
    let u : (Matrix (Fin r) (Fin r) E)ˣ := Matrix.nonsingInvUnit h hd
    have e : h * (companion a.1).map (algebraMap F E) * h⁻¹ =
        (u : Matrix (Fin r) (Fin r) E) * (companion a.1).map (algebraMap F E) *
          (u : Matrix (Fin r) (Fin r) E)⁻¹ := rfl
    rw [e, Matrix.charpoly_units_conj, Matrix.charpoly_map, Polynomial.coeff_map, charpoly_companion_coeff]
  · funext i; exact mom_mkX hh hd i
  · rfl

end GlobalTheory.JR.ImgSec


open GlobalTheory.JR.ImgSec in
theorem GlobalTheory.JR.image_openClosed_section : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (a₀ : Inv r F), Delta a₀ ≠ 0 → ((¬ ∃ X : Hn r F E, HasInv X a₀) → ∀ᶠ a in 𝓝 a₀, ¬ ∃ X : Hn r F E, HasInv X a) ∧ ((∃ X : Hn r F E, HasInv X a₀) → ∃ (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E), IsCompact Ω ∧ IsOpen Ω ∧ a₀ ∈ Ω ∧ ContinuousOn s Ω ∧ (∀ a ∈ Ω, Delta a ≠ 0 ∧ HasInv (s a) a) ∧ ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C}) := by
  intro F E _ _ _ _ _ r a₀ hΔ
  haveI := continuousStar (E := E) F
  obtain ⟨-, -, -, hcrit⟩ := GlobalTheory.T.unitary_action_hermitian_invariants_transitive F E r
  obtain ⟨Ω₁, κ, hΩ₁, hH₀, hκ, -, hκeq⟩ := GlobalTheory.T.exists_continuous_congruence_near_symmetric_matrix F E r (hankel a₀) (hankel_isSymm a₀) hΔ
  set φ := algebraMap F E with hφ
  let U : Set (Inv r F) := {a | Delta a ≠ 0} ∩ (fun a => hankel a) ⁻¹' Ω₁
  have hU : IsOpen U := (isOpen_ne_fun continuous_delta continuous_const).inter (hΩ₁.preimage continuous_hankel)
  have ha₀ : a₀ ∈ U := ⟨hΔ, hH₀⟩
  have hK : ∀ a ∈ U, (κ (hankel a))ᵀ * hankel a₀ * κ (hankel a) = hankel a :=
    fun a ha => hκeq _ ha.2 (hankel_isSymm a)
  have hKd : ∀ a ∈ U, IsUnit (κ (hankel a)).det := by
    intro a ha
    refine isUnit_iff_ne_zero.2 fun h0 => ha.1 ?_
    have := congrArg Matrix.det (hK a ha)
    rw [det_mul, det_mul, h0, mul_zero] at this
    exact this.symm
  have hdm : ∀ M : Matrix (Fin r) (Fin r) F, (M.map φ).det = φ M.det := fun M => (RingHom.map_det φ M).symm
  have hKd' : ∀ a ∈ U, IsUnit ((κ (hankel a)).map φ).det := fun a ha => by
    rw [hdm]; exact (hKd a ha).map φ
  have hmapK : ∀ a ∈ U, ((κ (hankel a)).map φ)ᴴ * ((hankel a₀).map φ * (κ (hankel a)).map φ) = (hankel a).map φ := by
    intro a ha
    rw [ImgSec.conjTranspose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, hK a ha]
  have transport : ∀ a ∈ U, (∃ h : Matrix (Fin r) (Fin r) E, hᴴ * h = (hankel a).map φ) →
      ∃ h : Matrix (Fin r) (Fin r) E, hᴴ * h = (hankel a₀).map φ := by
    rintro a ha ⟨h, hh⟩
    set K' := (κ (hankel a)).map φ
    have hu' : IsUnit K'ᴴ.det := by rw [det_conjTranspose]; exact (hKd' a ha).star
    refine ⟨h * K'⁻¹, ?_⟩
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc K'ᴴ⁻¹ * hᴴ * (h * K'⁻¹) = K'ᴴ⁻¹ * (hᴴ * h) * K'⁻¹ := by simp only [Matrix.mul_assoc]
      _ = K'ᴴ⁻¹ * (K'ᴴ * ((hankel a₀).map φ * K')) * K'⁻¹ := by rw [hh, ← hmapK a ha]
      _ = (hankel a₀).map φ := by
        rw [nonsing_inv_mul_cancel_left _ _ hu', mul_nonsing_inv_cancel_right _ _ (hKd' a ha)]
  refine ⟨fun hno => ?_, fun hex => ?_⟩
  · filter_upwards [hU.mem_nhds ha₀] with a ha
    rintro ⟨X, hX⟩
    apply hno
    rw [hcrit a₀ hΔ]
    exact transport a ha ((hcrit a ha.1).1 ⟨X, hX⟩)
  · obtain ⟨h₀, hh₀⟩ := (hcrit a₀ hΔ).1 hex
    have hd₀ : IsUnit h₀.det := by
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      have := congrArg Matrix.det hh₀
      rw [det_mul, h0, mul_zero, hdm] at this
      exact hΔ ((map_eq_zero_iff φ φ.injective).1 this.symm)
    obtain ⟨Ω, hΩc, hΩo, ha₀Ω, hΩU⟩ := exists_compact_open_nhd F E r U a₀ hU ha₀
    let hf : Inv r F → Matrix (Fin r) (Fin r) E := fun a => h₀ * (κ (hankel a)).map φ
    have hhf : ∀ a ∈ U, (hf a)ᴴ * hf a = (hankel a).map φ := by
      intro a ha
      simp only [hf]
      rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc h₀ᴴ, hh₀, hmapK a ha]
    have hdf : ∀ a ∈ U, IsUnit (hf a).det := fun a ha => by
      simp only [hf]; rw [det_mul]; exact hd₀.mul (hKd' a ha)
    have hcf : ContinuousOn hf Ω := by
      have h1 : ContinuousOn (fun a => κ (hankel a)) Ω :=
        hκ.comp continuous_hankel.continuousOn fun a ha => (hΩU ha).2
      exact continuousOn_const.mul ((continuous_id.matrix_map (continuous_algebraMap F E)).comp_continuousOn h1)
    have hcs : ContinuousOn (fun a => mkX a (hf a)) Ω :=
      continuousOn_mkX F E r Ω hf hcf fun a ha => hdf a (hΩU ha)
    refine ⟨Ω, fun a => mkX a (hf a), hΩc, hΩo, ha₀Ω, hcs,
      fun a ha => ⟨(hΩU ha).1, hasInv_mkX (hhf a (hΩU ha)) (hdf a (hΩU ha))⟩, ?_⟩
    intro C hC
    exact isCompact_orbit F E r Ω (fun a => mkX a (hf a)) hf hΩc hcs hcf
      (fun a ha => ⟨hdf a (hΩU ha), bm_mkX (hhf a (hΩU ha)) (hdf a (hΩU ha))⟩) C hC
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ, IsTest f → WeilMix.negB (WeilMix.ptrB M ψ (WeilMix.rowAct (wS F) (WeilMix.ptrB M ψ f))) = fourG M ψ f := by
  intro F E _ _ _ _ hU r M ψ hψ f hf
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hψc : Continuous (fun x => ψ x) := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).1.continuous
  funext Y
  obtain ⟨A, b, c, l⟩ := Y
  have hw : ((wS F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl
  simp only [WeilMix.negB, WeilMix.ptrB, WeilMix.rowAct, WeilMix.rowMap, fourG, hw]
  simp
  set μ : Measure (Fin r → F) := Measure.pi fun _ : Fin r => M.μF with hμ
  haveI : μ.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular μ
  set G : (Fin r → F) → ℂ := fun x => (∫ b', f (A, b', x, l) * ψ (b' ⬝ᵥ c) ∂μ) * ψ (x ⬝ᵥ b) with hG
  set H : (Fin r → F) → (Fin r → F) → ℂ := fun x b' => f (A, b', x, l) * ψ (b' ⬝ᵥ c) * ψ (x ⬝ᵥ b) with hH
  have hHc : Continuous (Function.uncurry H) := by
    have h1 : Continuous (fun p : (Fin r → F) × (Fin r → F) => f (A, p.2, p.1, l)) :=
      hf.1.continuous.comp (by fun_prop)
    have h2 : Continuous (fun p : (Fin r → F) × (Fin r → F) => ψ (p.2 ⬝ᵥ c)) :=
      hψc.comp (continuous_snd.dotProduct continuous_const)
    have h3 : Continuous (fun p : (Fin r → F) × (Fin r → F) => ψ (p.1 ⬝ᵥ b)) :=
      hψc.comp (continuous_fst.dotProduct continuous_const)
    exact (h1.mul h2).mul h3
  have hHs : HasCompactSupport (Function.uncurry H) := by
    refine HasCompactSupport.intro ((hf.2.isCompact).image
      (show Continuous (fun Y : Gl r F => (Y.2.2.1, Y.2.1)) by fun_prop)) ?_
    intro p hp
    by_contra hne
    apply hp
    refine ⟨(A, p.2, p.1, l), subset_tsupport _ ?_, rfl⟩
    intro h0
    apply hne
    simp [Function.uncurry, H, h0]
  have hint : Integrable (Function.uncurry H) (μ.prod μ) := hHc.integrable_of_hasCompactSupport hHs
  calc _ = ∫ x, G (-x) ∂μ := by
        congr 1; funext x; simp only [G, neg_dotProduct, neg_neg]; rfl
    _ = ∫ x, G x ∂μ := integral_neg_eq_self G μ
    _ = ∫ x, ∫ b', H x b' ∂μ ∂μ := by
        congr 1; funext x; simp only [G, H]; rw [integral_mul_const]
    _ = ∫ b', ∫ x, H x b' ∂μ ∂μ := integral_integral_swap hint
    _ = _ := by
        congr 1; funext b'; congr 1; funext x
        simp only [H]
        rw [mul_assoc, ← AddChar.map_add_eq_mul, dotProduct_comm b' c, add_comm]
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.not_isRoot_residue_cofactor_unramifiedExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ s : K'.O, (∀ y : K'.O, ∃ f : K.O[X], ∃ z ∈ IsLocalRing.maximalIdeal K'.O, algebraMap K'.O K'.E y = f.eval₂ (φ.comp (algebraMap K.O K.E)) (algebraMap K'.O K'.E s) + algebraMap K'.O K'.E z) → ∀ (p : K.O[X]) (r c : K'.O[X]), p.Monic → r.Monic → r.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ r.natDegree → p.natDegree = d * r.natDegree → p.map (φ.comp (algebraMap K.O K.E)) = (r * c).map (algebraMap K'.O K'.E) → ¬ (c.map (IsLocalRing.residue K'.O)).IsRoot (IsLocalRing.residue K'.O s) := by
  first | exact @GlobalTheory.UnitLemma.Unr.ResMult.not_isRoot_cofactor | exact GlobalTheory.UnitLemma.Unr.ResMult.not_isRoot_cofactor | (intros; apply GlobalTheory.UnitLemma.Unr.ResMult.not_isRoot_cofactor <;> assumption)
end

section

noncomputable section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

namespace GlobalTheory.UnitLemma.Unr

theorem val_mul_of_ne {K : UQ} {a b : K.E} (ha : a ≠ 0) (hb : b ≠ 0) :
    val K.O (a * b) = val K.O a + val K.O b := by
  unfold val
  have ha' : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E a ≠ 0 := by simpa using ha
  have hb' : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E b ≠ 0 := by simpa using hb
  rw [map_mul, WithZero.log_mul ha' hb']; ring

theorem val_pow_of_ne {K : UQ} {a : K.E} (ha : a ≠ 0) (n : ℕ) : val K.O (a ^ n) = n * val K.O a := by
  induction n with
  | zero => simp [val]
  | succ n ih => rw [pow_succ, val_mul_of_ne (pow_ne_zero _ ha) ha, ih]; push_cast; ring

theorem eta_overExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → Odd d → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (x : B.Aˣ), B.σ (x : B.A) = x → K'.eta ((overExt φ B ψ hψ hσ).gramDet (x : B.A)) = K.eta (B.gramDet (x : B.A)) := by
  intro K K' d φ hU hd B ψ hψ hσ x _
  have hd0 : 0 < d := hd.pos
  obtain ⟨w, hw0, hwv⟩ := GlobalTheory.T.exists_basis_trace_involution_det_unit_unramified K K' d φ hU hd0
  letI : Algebra K.E K'.E := φ.toAlgebra
  haveI : Module.Finite K.E K'.E := Module.finite_of_finrank_pos (by rw [hU.2.2.2.2]; exact hd0)
  letI : Algebra K'.E B.A := ψ.toAlgebra
  haveI : IsScalarTower K.E K'.E B.A := IsScalarTower.of_algebraMap_eq fun e => (hψ e).symm
  haveI : Module.Finite K'.E B.A := (overExt φ B ψ hψ hσ).fd
  set u := Module.finBasis K'.E B.A with hu
  set H : Matrix (Fin (Module.finrank K'.E B.A)) (Fin (Module.finrank K'.E B.A)) K'.E :=
    Matrix.of fun i j => Algebra.trace K'.E B.A ((x : B.A) * u i * B.σ (u j)) with hH
  have h1 : (overExt φ B ψ hψ hσ).gramDet (x : B.A) = H.det := rfl
  set b0 := w.smulTower u with hb0
  set e := b0.indexEquiv (Module.finBasis K.E B.A) with he
  rw [h1, ← Orbit.eta_gram B _ (b0.reindex e)]
  have h2 : (Matrix.of fun i j => B.herm x ((b0.reindex e) i) ((b0.reindex e) j)) =
      (Matrix.of fun (p q : Fin d × Fin (Module.finrank K'.E B.A)) =>
        Algebra.trace K.E K'.E (w p.1 * H p.2 q.2 * K'.c (w q.1))).submatrix e.symm e.symm := by
    ext i j
    simp only [Module.Basis.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, hb0,
      Module.Basis.smulTower_apply, InvAlg.herm, hH]
    rw [← Algebra.trace_trace (S := K'.E)]
    refine congrArg (Algebra.trace K.E K'.E) ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul B.σ]
    have hc : ∀ y : K'.E, B.σ (algebraMap K'.E B.A y) = algebraMap K'.E B.A (K'.c y) := hσ
    rw [hc]
    have : (x : B.A) * (algebraMap K'.E B.A (w (e.symm i).1) * u (e.symm i).2) *
        (algebraMap K'.E B.A (K'.c (w (e.symm j).1)) * B.σ (u (e.symm j).2)) =
        (w (e.symm i).1 * K'.c (w (e.symm j).1)) • ((x : B.A) * u (e.symm i).2 * B.σ (u (e.symm j).2)) := by
      rw [Algebra.smul_def, map_mul]; ring
    rw [this, LinearMap.map_smul, smul_eq_mul]; ring
  rw [h2, Matrix.det_submatrix_equiv_self, GlobalTheory.T.det_trace_gram_block_eq_pow_mul_norm_det w H (fun l => K'.c (w l))]
  by_cases hH0 : H.det = 0
  · rw [hH0, Algebra.norm_zero, mul_zero]; simp [UQ.eta, val]
  have hN : Algebra.norm K.E H.det ≠ 0 := by
    rw [Ne, Algebra.norm_eq_zero_iff]; exact hH0
  unfold UQ.eta
  rw [val_mul_of_ne (pow_ne_zero _ hw0) hN, val_pow_of_ne hw0, hwv, GlobalTheory.T.addVal_norm_unramifiedInvolutionFieldExt_eq_mul K K' d φ hU hd0, mul_zero, zero_add,
    zpow_mul]
  rw [zpow_natCast, hd.neg_one_pow]

end GlobalTheory.UnitLemma.Unr
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.residue_generates_unramifiedExt_residueField : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A), (∀ e, ψ (φ e) = algebraMap K.E B.A e) → Nontrivial B.A → (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) → ∀ (s : K'.O) (Q : K'.O[X]), Q.Monic → Q.eval₂ (ψ.comp (algebraMap K'.O K'.E)) B.g = 0 → Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree → ∀ y : K'.O, ∃ f : K.O[X], ∃ z ∈ IsLocalRing.maximalIdeal K'.O, algebraMap K'.O K'.E y = f.eval₂ (φ.comp (algebraMap K.O K.E)) (algebraMap K'.O K'.E s) + algebraMap K'.O K'.E z := by
  first | exact @GlobalTheory.UnitLemma.Unr.residue_generates | exact GlobalTheory.UnitLemma.Unr.residue_generates | (intros; apply GlobalTheory.UnitLemma.Unr.residue_generates <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.dvrFractionFieldAddVal_norm_unramifiedLocalExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ y : K'.E, val K.O (@Algebra.norm K.E K'.E _ _ φ.toAlgebra y) = (d : ℤ) * val K'.O y := by
  first | exact @GlobalTheory.UnitLemma.Unr.NormValU.val_norm | exact GlobalTheory.UnitLemma.Unr.NormValU.val_norm | (intros; apply GlobalTheory.UnitLemma.Unr.NormValU.val_norm <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isLocallyConstantCompactSupport_jacquetRallisDescent : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ), IsTest f' → IsLocallyConstant α → HasCompactSupport α → IsTest (LinDesc.desc A M hG lam α f') := by
  first | exact @GlobalTheory.JR.LinDesc.desc_isTest | exact GlobalTheory.JR.LinDesc.desc_isTest | (intros; apply GlobalTheory.JR.LinDesc.desc_isTest <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LinDesc

theorem eta_inv_eq {F : Type} [NormedField F] (x : F) : eta x⁻¹ = eta x := by
  have key : (∃ y : F, ‖x⁻¹‖ = ‖y‖ ^ 2) ↔ ∃ y : F, ‖x‖ = ‖y‖ ^ 2 := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y⁻¹, ?_⟩
      rw [norm_inv] at hy
      rw [norm_inv, inv_pow, ← hy, inv_inv]
    · rintro ⟨y, hy⟩
      exact ⟨y⁻¹, by rw [norm_inv, norm_inv, inv_pow, hy]⟩
  unfold eta
  by_cases h : ∃ y : F, ‖x‖ = ‖y‖ ^ 2
  · rw [if_pos (key.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (key.mp h')), if_neg h]

theorem eta_neg_one_pow {F : Type} [NormedField F] (r : ℕ) : eta ((-1 : F) ^ r) = 1 := by
  unfold eta
  rw [if_pos]
  exact ⟨1, by simp⟩

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem row_pow (hG : A.IsGen τ p) (c : A.K) (n : ℕ) :
    (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * c)) ᵥ* (companion p) ^ n =
      fun j : Fin r => Algebra.trace F A.K (τ ^ (j : ℕ) * (τ ^ n * c)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.vecMul_vecMul, ih, ← leftMul_tau A hG, row_mul]
    funext j
    congr 2
    ring

theorem Cm_pt_one (hG : A.IsGen τ p) (lam : F) (a : A.K) :
    Cm (pt A hG lam 1 a) = Algebra.traceMatrix F (bas A hG) * Algebra.leftMulMatrix (bas A hG) a := by
  ext i j
  have h1 : Cm (pt A hG lam 1 a) i j = Algebra.trace F A.K (τ ^ (j : ℕ) * (τ ^ (i : ℕ) * a)) := by
    simp only [Cm, pt, Matrix.of_apply]
    rw [row_pow A hG]
  have h2 := congrFun (row_mul A hG a (τ ^ (i : ℕ))) j
  simp only [Matrix.vecMul, dotProduct] at h2
  rw [h1, Matrix.mul_apply]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, bas_apply]
  rw [mul_comm (τ ^ (i : ℕ)) a, ← h2]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comm (τ ^ (i : ℕ))]

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc

theorem omega_pt_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F),
    ∃ κ₀ : ℂ, ∀ a : A.K, IsUnit a → ∀ g : GL (Fin r) F,
      omega (act g (LinDesc.pt A hG lam 1 a)) = κ₀ * eta ((g : Matrix (Fin r) (Fin r) F).det) * A.etaK a := by
  intro F E _ _ _ _ _ A r τ p hG lam
  obtain ⟨hmul, -, -, -⟩ := GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms F E
  have hnd := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1
  have hT : (Algebra.traceMatrix F (bas A hG)).det ≠ 0 := by
    rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (bas A hG)] at hnd
    convert hnd using 2
    ext i j
    rw [Algebra.traceForm_toMatrix, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  refine ⟨eta (Algebra.traceMatrix F (bas A hG)).det, fun a ha g => ?_⟩
  have hL := GlobalTheory.T.jacquetRallis_transfer_factor_krylov_det F r
  have hdet : (g : Matrix (Fin r) (Fin r) F).det * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hg : (g : Matrix (Fin r) (Fin r) F).det ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hginv := eq_inv_of_mul_eq_one_right hdet
  have hna : Algebra.norm F a ≠ 0 := (ha.map (Algebra.norm F)).ne_zero
  have hr : (-1 : F) ^ r ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  unfold omega Et.etaK
  rw [hL.1, hL.2, Cm_pt_one, Matrix.det_mul, Matrix.det_mul, ← Algebra.norm_eq_matrix_det, hginv,
    hmul _ _ hr (mul_ne_zero (mul_ne_zero hT hna) (inv_ne_zero hg)),
    hmul _ _ (mul_ne_zero hT hna) (inv_ne_zero hg), hmul _ _ hT hna, eta_neg_one_pow, eta_inv_eq]
  ring

end GlobalTheory.JR.LinDesc
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

noncomputable def trxForm {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (x : A.K) : LinearMap.BilinForm F A.K :=
  LinearMap.mk₂ F (fun u b => Algebra.trace F A.K (x * u * b))
    (fun m₁ m₂ n => by simp [mul_add, add_mul])
    (fun c m n => by simp [mul_smul_comm, smul_mul_assoc])
    (fun m n₁ n₂ => by simp [mul_add])
    (fun c m n => by simp [mul_smul_comm, smul_mul_assoc])

theorem selfDual_kx_exists : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ x : A.Kˣ, ∃ ν : Measure A.K, SelfDual ν (Hyp.kx A ψ x) := by
  intro F E _ _ _ _ _ A ψ hψ x
  have hT := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1
  obtain ⟨hL, -⟩ := hT
  have hsymm : (trxForm A (x : A.K)).IsSymm := by
    refine ⟨fun u b => ?_⟩
    simp only [trxForm, LinearMap.mk₂_apply, RingHom.id_apply]
    ring_nf
  have hleft : ∀ u : A.K, (∀ b, trxForm A (x : A.K) u b = 0) → u = 0 := by
    intro u hu
    have h0 : (x : A.K) * u = 0 := hL _ (fun b => by
      have := hu b
      simpa [trxForm, Algebra.traceForm_apply, mul_assoc] using this)
    have := congrArg (fun t => ((x⁻¹ : A.Kˣ) : A.K) * t) h0
    simpa [← mul_assoc] using this
  have hnd : (trxForm A (x : A.K)).Nondegenerate := by
    refine ⟨hleft, fun b hb => hleft b (fun u => ?_)⟩
    have := hb u
    simp only [trxForm, LinearMap.mk₂_apply] at this ⊢
    rw [show (x : A.K) * b * u = x * u * b by ring]
    exact this
  obtain ⟨⟨μ, hμ, -⟩, -⟩ := GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ A.K (trxForm A (x : A.K)) hsymm hnd
  refine ⟨μ, ?_⟩
  have hk : (fun u b => ψ (trxForm A (x : A.K) u b)) = Hyp.kx A ψ x := by
    funext u b
    simp [trxForm, Hyp.kx, Et.psiK]
  rw [← hk]
  exact hμ

end GlobalTheory.JR.Hyp
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.quadraticWeilFourier_comp_smul : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (s : A.Kˣ) (φ : A.L → ℂ), IsTest φ → ∀ y, fOp A ψ x μ (fun y' => φ ((s : A.K) • y')) y = ((A.absK s : ℂ) ^ 2)⁻¹ * fOp A ψ x μ φ (((s⁻¹ : A.Kˣ) : A.K) • y) := by
  first | exact @GlobalTheory.JR.WeilQuad.fOp_comp_smul | exact GlobalTheory.JR.WeilQuad.fOp_comp_smul | (intros; apply GlobalTheory.JR.WeilQuad.fOp_comp_smul <;> assumption)
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_stable_quadraticGaussIntegral : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ u : A.Kˣ, ∃ G, IsStableGauss A ψ x μ u G := by
  first | exact @GlobalTheory.JR.WeilQuad.exists_stableGauss | exact GlobalTheory.JR.WeilQuad.exists_stableGauss | (intros; apply GlobalTheory.JR.WeilQuad.exists_stableGauss <;> assumption)
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.quadraticWeil_fOp_nOp_fOp_gauss : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (u : A.Kˣ) (G : ℂ), IsStableGauss A ψ x μ u G → ∀ φ : A.L → ℂ, IsTest φ → ∀ z, fOp A ψ x μ (nOp A ψ x u (fOp A ψ x μ φ)) z = G * A.psiK ψ (-((u⁻¹ : A.Kˣ) : A.K) * x * A.NL z) * fOp A ψ x μ (nOp A ψ x (-((u⁻¹ : A.Kˣ) : A.K)) φ) ((-((u⁻¹ : A.Kˣ) : A.K)) • z) := by
  first | exact @GlobalTheory.JR.WeilQuad.fOp_nOp_fOp | exact GlobalTheory.JR.WeilQuad.fOp_nOp_fOp | (intros; apply GlobalTheory.JR.WeilQuad.fOp_nOp_fOp <;> assumption)
end
