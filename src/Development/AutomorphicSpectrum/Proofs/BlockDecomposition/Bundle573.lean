module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.IwasawaUnitaryAdelic.IUAIwa
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaAll
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle237
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import GroundTheory.GlobalFields.Adele.Topology
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle565
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle055
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle056
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

section

open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.LeviIwa

theorem block_qr {D : ℕ} (τ : Fin D → ℕ) (hτ : Monotone τ) (h : Matrix (Fin D) (Fin D) ℂ) (hu : IsUnit h)
    (ht : h.BlockTriangular τ) : ∃ k ∈ Matrix.unitaryGroup (Fin D) ℂ, ∃ b : Matrix (Fin D) (Fin D) ℂ,
      h = k * b ∧ b.BlockTriangular id ∧ k.BlockTriangular τ ∧ kᴴ.BlockTriangular τ := by
  obtain ⟨k, hk, b, rfl, hb⟩ := GlobalTheory.T.iwasawa_unitary_upper_triangular h hu
  have hk1 : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  have hk2 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
  have hbu : IsUnit b := by
    have : kᴴ * (k * b) = b := by rw [← Matrix.mul_assoc, hk2, Matrix.one_mul]
    rw [← this]
    exact (IsUnit.of_mul_eq_one _ hk2).mul hu
  have hbτ : b.BlockTriangular τ := fun i j hij => hb (by
    by_contra hc
    exact absurd (hτ (not_lt.1 hc)) (not_le.2 hij))
  haveI : Invertible b := hbu.invertible
  have hbi : (b⁻¹).BlockTriangular τ := Matrix.blockTriangular_inv_of_blockTriangular hbτ
  have hkeq : k = (k * b) * b⁻¹ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det b).1 hbu), Matrix.mul_one]
  have hkt : k.BlockTriangular τ := hkeq ▸ ht.mul hbi
  have hkinv : kᴴ = k⁻¹ := (Matrix.inv_eq_left_inv hk2).symm
  haveI : Invertible k := (IsUnit.of_mul_eq_one _ hk1).invertible
  exact ⟨k, hk, b, rfl, hb, hkt, hkinv ▸ Matrix.blockTriangular_inv_of_blockTriangular hkt⟩

theorem blockTri_keeps {D : ℕ} {τ : Fin D → ℕ} {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.BlockTriangular τ) {i : ℕ}
    {v : Fin D → ℂ} (hv : ∀ c, i ≤ τ c → v c = 0) : ∀ c, i ≤ τ c → (M *ᵥ v) c = 0 := by
  intro c hc
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hd : i ≤ τ d
  · rw [hv d hd, mul_zero]
  · rw [hM (lt_of_lt_of_le (not_le.1 hd) hc), zero_mul]

theorem detOn_unitary {n : ℕ} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (V : Submodule ℂ (Fin n → ℂ)) (h : ∀ y ∈ V, k *ᵥ y ∈ V) (h' : ∀ y ∈ V, kᴴ *ᵥ y ∈ V) :
    GlobalTheory.FlagMeas.detOn k V = 1 := by
  have e := GlobalTheory.RealInd.detOn_mul h' h
  rw [Matrix.mem_unitaryGroup_iff'.1 hk |> fun x => (show kᴴ * k = 1 from x), GlobalTheory.RealInd.detOn_one,
    GlobalTheory.LeviPolar.detOn_conjTranspose n k V h h'] at e
  have h0 := GlobalTheory.LeviPolar.detOn_nonneg k V
  nlinarith


open GlobalTheory.RealInd in
theorem iwaOn_leviOne : ∀ {n a : ℕ} (ε : Fin n → Bool) (j : Fin a → ℕ) (W : GlobalTheory.RealInd.Flag n a),
    GlobalTheory.FlagMeas.IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
      PositivityTheory.Tls2.Iua.IwaOn (GlobalTheory.RealInd.mats (GlobalTheory.RealInd.leviOne ε W)) := by
  intro n a ε j W hW _
  obtain ⟨h0, hm, -, hiso⟩ := hW
  obtain ⟨D, C, τ, hC, hτ, hτa, hfl⟩ := GlobalTheory.T.flag_orthonormal_adapted_basis W h0 hm
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := PI.UpqRep.Jm_mul_self ε
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := PI.UpqRep.Jm_conjTranspose ε
  set J := Formalism.REAL.Jm ε with hJdef
  have hlast : ∀ v, C *ᵥ v ∈ W (Fin.last a) := fun v =>
    (hfl _ _).2 ⟨v, rfl, fun c hc => absurd (hτa c) (by simpa using hc)⟩
  have hCJ : Cᴴ * J * C = 0 := by
    ext c d
    have := hiso _ (hlast (Pi.single c 1)) _ (hlast (Pi.single d 1))
    have e : star (Pi.single c (1 : ℂ)) = (Pi.single c 1 : Fin D → ℂ) := by
      ext x
      by_cases hx : x = c
      · subst hx; simp
      · simp [hx]
    rw [star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e,
      Matrix.mulVec_single_one, single_one_dotProduct] at this
    simpa using this
  obtain ⟨m, R, ε', hR, hJR, hCR, hsum⟩ := GlobalTheory.T.isotropic_hyperbolic_complement ε C hC hCJ
  obtain ⟨U₀, hU₀, hI⟩ := CompanionTheory.D.gk.admitted.iwasawa_decomposition_unitary_group m ε'
  obtain ⟨U, hU, hTri⟩ := GlobalTheory.T.unitary_extension_of_block J (Formalism.REAL.Jm ε') C R hJ hJh hC hCJ hR hJR hCR hsum U₀ hU₀
  refine ⟨U, hU, fun g hg => ?_⟩
  obtain ⟨hgU, hgk, hgd⟩ := GlobalTheory.LeviPolar.mem_mats_leviOne.1 hg
  have hgU' : gᴴ * J * g = J := hgU
  have keep : ∀ x : Matrix (Fin n) (Fin n) ℂ, (∀ y ∈ W (Fin.last a), x *ᵥ y ∈ W (Fin.last a)) →
      x * C = C * (Cᴴ * x * C) := fun x hx => by
    refine Matrix.ext_iff_mulVec.2 fun v => ?_
    obtain ⟨w, hw, -⟩ := (hfl _ _).1 (hx _ (hlast v))
    have e : (Cᴴ * x * C) *ᵥ v = w := by
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_mulVec, hC,
        Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, hw, ← Matrix.mulVec_mulVec, e]
  set h := Cᴴ * g * C with hh
  have hgC : g * C = C * h := keep g fun y hy => (hgk _ y hy).1
  have hgC' : gᴴ * C = C * hᴴ := by
    have := keep gᴴ fun y hy => (hgk _ y hy).2
    rw [this, hh]
    simp [conjTranspose_mul, Matrix.mul_assoc]
  have htri : h.BlockTriangular τ := by
    intro c d hdc
    have hda : τ d + 1 < a + 1 := by have := hτa d; omega
    have h1 : C *ᵥ Pi.single d 1 ∈ W ⟨τ d + 1, hda⟩ := (hfl _ _).2 ⟨_, rfl, fun c' hc' => by
      have : c' ≠ d := by rintro rfl; simp at hc'
      simp [this]⟩
    obtain ⟨v, hv, hv0⟩ := (hfl _ _).1 ((hgk _ _ h1).1)
    have h2 : h *ᵥ Pi.single d 1 = v := by
      rw [hh, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_mulVec, hC,
        Matrix.one_mulVec]
    have h3 := congrFun h2 c
    rw [Matrix.mulVec_single_one] at h3
    simpa [hv0 c (by simpa using hdc)] using h3
  obtain ⟨hu, hgJC, hgR, hgRU⟩ := GlobalTheory.T.parabolic_stabilizer_block_unit J (Formalism.REAL.Jm ε') C R hJ hJh hC hR hJR hCR hsum g h hgU' hgC hgC'
  obtain ⟨k₀, hk₀, b, hb, hbT, hk₀T, hk₀T'⟩ := block_qr τ hτ h hu htri
  obtain ⟨kR, ⟨hkR, hkRJ⟩, sR, hsR, hgks, hsT⟩ := hI (Rᴴ * g * R) hgRU
  obtain ⟨k, hk, hkJ, hkC, hkC', hkR', hkJC⟩ := GlobalTheory.T.unitary_lift_commuting_involution J (Formalism.REAL.Jm ε') C R hJ hJh hC hCJ hR hJR hCR hsum
    k₀ hk₀ kR hkR hkRJ
  have hk1 : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  have hk2 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
  have hk01 : k₀ᴴ * k₀ = 1 := Matrix.mem_unitaryGroup_iff'.1 hk₀
  have hkR1 : kRᴴ * kR = 1 := Matrix.mem_unitaryGroup_iff'.1 hkR
  have kk : ∀ (i : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W i → k *ᵥ y ∈ W i := fun i y hy => by
    obtain ⟨v, rfl, hv⟩ := (hfl _ _).1 hy
    exact (hfl _ _).2 ⟨k₀ *ᵥ v, by rw [Matrix.mulVec_mulVec, hkC, ← Matrix.mulVec_mulVec], blockTri_keeps hk₀T hv⟩
  have kk' : ∀ (i : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W i → kᴴ *ᵥ y ∈ W i := fun i y hy => by
    obtain ⟨v, rfl, hv⟩ := (hfl _ _).1 hy
    exact (hfl _ _).2 ⟨k₀ᴴ *ᵥ v, by rw [Matrix.mulVec_mulVec, hkC', ← Matrix.mulVec_mulVec], blockTri_keeps hk₀T' hv⟩
  have hkG : k ∈ mats (leviOne ε W) := GlobalTheory.LeviPolar.mem_mats_leviOne.2
    ⟨by change kᴴ * J * k = J; rw [Matrix.mul_assoc, ← hkJ, ← Matrix.mul_assoc, hk2, Matrix.one_mul],
      fun i y hy => ⟨kk i y hy, kk' i y hy⟩, fun i => detOn_unitary hk _ (kk i) (kk' i)⟩
  have hkhG : kᴴ ∈ mats (leviOne ε W) := GlobalTheory.LeviPolar.mem_mats_leviOne.2
    ⟨by change (kᴴ)ᴴ * J * kᴴ = J; rw [conjTranspose_conjTranspose, hkJ, Matrix.mul_assoc, hk1, Matrix.mul_one],
      fun i y hy => ⟨kk' i y hy, by simpa using kk i y hy⟩,
      fun i => detOn_unitary (Matrix.mem_unitaryGroup_iff.2 (by simpa [star_eq_conjTranspose] using hk2)) _ (kk' i)
        (by rw [conjTranspose_conjTranspose]; exact kk i)⟩
  refine ⟨k, ⟨hkG, hk⟩, kᴴ * g, GlobalTheory.LeviPolar.mats_mul hkhG hg, by rw [← Matrix.mul_assoc, hk1, Matrix.one_mul], ?_⟩
  have hbu : IsUnit b := by
    have : k₀ᴴ * h = b := by rw [hb, ← Matrix.mul_assoc, hk01, Matrix.one_mul]
    rw [← this]
    exact (IsUnit.of_mul_eq_one _ hk01).mul hu
  haveI : Invertible b := hbu.invertible
  have hci : (b⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbT
  have hbb : b⁻¹ * b = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det b).1 hbu)
  have hhinv : (hᴴ)⁻¹ = k₀ * (b⁻¹)ᴴ := Matrix.inv_eq_right_inv (by
    rw [hb, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc k₀ᴴ, hk01, Matrix.one_mul,
      ← conjTranspose_mul, hbb, conjTranspose_one])
  refine hTri (kᴴ * g) b (b⁻¹)ᴴ (U₀ᴴ * sR * U₀) ?_ ?_ ?_ hbT hsT ?_
  · rw [Matrix.mul_assoc, hgC, ← Matrix.mul_assoc, hkC', Matrix.mul_assoc, hb, ← Matrix.mul_assoc k₀ᴴ, hk01,
      Matrix.one_mul]
  · have hU1 : U₀ * U₀ᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU₀
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc g, hgR, ← Matrix.mul_assoc kᴴ, ← Matrix.mul_assoc kᴴ, hkR',
      Matrix.mul_assoc R, hgks, ← Matrix.mul_assoc kRᴴ, hkR1, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U₀, hU1, Matrix.one_mul]
  · rw [Matrix.mul_assoc, hgJC, ← Matrix.mul_assoc, hkJC, Matrix.mul_assoc, hhinv, ← Matrix.mul_assoc k₀ᴴ, hk01,
      Matrix.one_mul]
  · intro x y hxy
    have := hci (show id x < id y from hxy)
    simp [Matrix.conjTranspose_apply, this]

end GlobalTheory.CompanionTheory.LeviIwa
end
end

section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.InterpLoc

theorem exists_finset_separating {Y : Type} (Ψ : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ Ψ] :
    ∃ t : Finset Y, ∀ ψ ∈ Ψ, (∀ y ∈ t, ψ y = 0) → ψ = 0 := by
  classical
  let K : Finset Y → Submodule ℂ (Y → ℂ) := fun t =>
    { carrier := {ψ | ψ ∈ Ψ ∧ ∀ y ∈ t, ψ y = 0}
      add_mem' := fun {a b} ha hb =>
        ⟨Ψ.add_mem ha.1 hb.1, fun y hy => by simp [ha.2 y hy, hb.2 y hy]⟩
      zero_mem' := ⟨Ψ.zero_mem, fun _ _ => rfl⟩
      smul_mem' := fun c a ha =>
        ⟨Ψ.smul_mem c ha.1, fun y hy => by simp [ha.2 y hy]⟩ }
  have hKle : ∀ t, K t ≤ Ψ := fun t _ h => h.1
  haveI : ∀ t, FiniteDimensional ℂ (K t) := fun t => Submodule.finiteDimensional_of_le (hKle t)
  let f : Finset Y → ℕ := fun t => Module.finrank ℂ (K t)
  refine ⟨Function.argmin f, fun ψ hψ h0 => ?_⟩
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (funext hall)
  set t := Function.argmin f with ht
  have hlt : K (insert y t) < K t := by
    refine lt_of_le_of_ne (fun a ha => ⟨ha.1, fun z hz => ha.2 z (Finset.mem_insert_of_mem hz)⟩) ?_
    intro heq
    have hmem : ψ ∈ K t := ⟨hψ, h0⟩
    rw [← heq] at hmem
    exact hy (hmem.2 y (Finset.mem_insert_self y t))
  have h1 : f (insert y t) < f t := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : f t ≤ f (insert y t) := Function.argmin_le f _
  omega

theorem bound_of_injective {Y : Type} [MeasurableSpace Y] (μ : Measure Y)
    (Ψ : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ Ψ]
    (hm : ∀ ψ ∈ Ψ, MemLp ψ 2 μ) (hinj : ∀ ψ ∈ Ψ, ψ =ᵐ[μ] 0 → ψ = 0) (y₀ : Y) :
    ∃ C : NNReal, ∀ ψ ∈ Ψ, ‖ψ y₀‖ₑ ^ 2 ≤ C * ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂μ := by
  let T : Ψ →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := fun ψ => (hm ψ.1 ψ.2).toLp ψ.1
      map_add' := fun a b => MemLp.toLp_add (hm a.1 a.2) (hm b.1 b.2)
      map_smul' := fun c a => MemLp.toLp_const_smul c (hm a.1 a.2) }
  have hker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro ψ hψ
    have h0 : ψ.1 =ᵐ[μ] 0 := (MemLp.toLp_eq_toLp_iff (hm ψ.1 ψ.2) MemLp.zero).1 (by
      rw [MemLp.toLp_zero]; exact hψ)
    exact Subtype.ext (hinj ψ.1 ψ.2 h0)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective T hker
  let ev : Ψ →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => ψ.1 y₀
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let ℓ : LinearMap.range T →ₗ[ℂ] ℂ := (ev ∘ₗ g).domRestrict (LinearMap.range T)
  let L : LinearMap.range T →L[ℂ] ℂ := ⟨ℓ, LinearMap.continuous_of_finiteDimensional ℓ⟩
  refine ⟨‖L‖₊ ^ 2, fun ψ hψ => ?_⟩
  let p : Ψ := ⟨ψ, hψ⟩
  have hL : L ⟨T p, LinearMap.mem_range_self T p⟩ = ψ y₀ := by
    change ev (g (T p)) = ψ y₀
    have : g (T p) = p := LinearMap.congr_fun hg p
    rw [this]; rfl
  have hb : ‖ψ y₀‖₊ ≤ ‖L‖₊ * ‖T p‖₊ := by
    rw [← hL]
    exact L.le_opNNNorm _
  have hen : ‖T p‖ₑ = eLpNorm ψ 2 μ := Lp.enorm_toLp (hm ψ hψ)
  have hb' : ‖ψ y₀‖ₑ ≤ (‖L‖₊ : ENNReal) * eLpNorm ψ 2 μ := by
    rw [← hen]
    simp only [enorm_eq_nnnorm]
    exact_mod_cast hb
  have hsq : eLpNorm ψ 2 μ ^ 2 = ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂μ := by
    have := eLpNorm_nnreal_pow_eq_lintegral (f := ψ) (μ := μ) (p := 2) (by norm_num)
      (hm ψ hψ).aestronglyMeasurable
    simpa using this
  calc ‖ψ y₀‖ₑ ^ 2 ≤ ((‖L‖₊ : ENNReal) * eLpNorm ψ 2 μ) ^ 2 := by gcongr
    _ = ((‖L‖₊ ^ 2 : NNReal) : ENNReal) * ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂μ := by
      rw [mul_pow, hsq]; push_cast; rfl

theorem interpolation_local_L2_bound : PositivityTheory.Rg.BcB.E.E3.InterpolationL2Bound := by
  intro X Y _ _ _ _ _ ν _ _ F hF hfin
  set Ψ : Submodule ℂ (Y → ℂ) := Submodule.span ℂ (Set.range F) with hΨ
  haveI : FiniteDimensional ℂ Ψ := hfin
  have hc : ∀ ψ ∈ Ψ, Continuous ψ := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x h => obtain ⟨i, rfl⟩ := h; exact hF i
    | zero => exact continuous_const
    | add a b _ _ ha hb => exact ha.add hb
    | smul c a _ ha => exact ha.const_smul c
  obtain ⟨t, ht⟩ := exists_finset_separating Ψ
  choose N hNc hNn using fun y : Y => exists_compact_mem_nhds y
  have hΩ : IsCompact (⋃ y ∈ t, N y) := t.isCompact_biUnion fun y _ => hNc y
  set Ω : Set Y := ⋃ y ∈ t, N y with hΩdef
  refine ⟨Ω, hΩ, fun y₀ => ?_⟩
  haveI : IsFiniteMeasure (ν.restrict Ω) := ⟨by simpa using hΩ.measure_lt_top⟩
  have hm : ∀ ψ ∈ Ψ, MemLp ψ 2 (ν.restrict Ω) := by
    intro ψ hψ
    obtain ⟨B, hB⟩ := hΩ.exists_bound_of_continuousOn (hc ψ hψ).continuousOn
    refine MemLp.of_bound (hc ψ hψ).aestronglyMeasurable B ?_
    have hmeas : MeasurableSet Ω := hΩ.measurableSet
    exact (ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall hB)
  have hinj : ∀ ψ ∈ Ψ, ψ =ᵐ[ν.restrict Ω] 0 → ψ = 0 := by
    intro ψ hψ h0
    refine ht ψ hψ fun y hy => ?_
    have hsub : interior (N y) ⊆ Ω := interior_subset.trans (Set.subset_biUnion_of_mem (u := N) hy)
    have h1 : ψ =ᵐ[ν.restrict (interior (N y))] 0 :=
      ae_mono (Measure.restrict_mono hsub le_rfl) h0
    have h2 := Measure.eqOn_open_of_ae_eq h1 isOpen_interior (hc ψ hψ).continuousOn
      continuousOn_const
    exact h2 (mem_interior_iff_mem_nhds.2 (hNn y))
  obtain ⟨C, hC⟩ := bound_of_injective (ν.restrict Ω) Ψ hm hinj y₀
  exact ⟨C, fun x => hC (F x) (Submodule.subset_span ⟨x, rfl⟩)⟩

end GlobalTheory.CompanionTheory.InterpLoc
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E.E3 PositivityTheory.Rg.BcB

namespace GlobalTheory.CompanionTheory.CentRe

theorem no_growth (b I K : ℝ) (M : ℕ) (hb : 0 < b) (hI : 0 < I)
    (h : ∀ s : ℝ, 0 ≤ s → I * Real.exp (b * s) ≤ K * (1 + s) ^ M) : False := by
  set K' : ℝ := K / b ^ M / I * Real.exp b with hK'
  obtain ⟨x, hx1, hx2⟩ := (((Real.tendsto_exp_div_pow_atTop M).eventually_gt_atTop K').and
    (eventually_ge_atTop b)).exists
  have hx0 : 0 < x := lt_of_lt_of_le hb hx2
  have hs : 0 ≤ x / b - 1 := by
    rw [sub_nonneg, le_div_iff₀ hb]; linarith
  have hh := h _ hs
  rw [lt_div_iff₀ (pow_pos hx0 M)] at hx1
  have h1 : I * Real.exp (-b) * (K' * x ^ M) < I * Real.exp (-b) * Real.exp x :=
    mul_lt_mul_of_pos_left hx1 (mul_pos hI (Real.exp_pos _))
  have e1 : I * Real.exp (-b) * (K' * x ^ M) = K * (1 + (x / b - 1)) ^ M := by
    have hE := Real.exp_pos b
    rw [hK', Real.exp_neg, show 1 + (x / b - 1) = x / b by ring, div_pow]
    field_simp
  have e2 : I * Real.exp (-b) * Real.exp x = I * Real.exp (b * (x / b - 1)) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  rw [e1, e2] at h1
  exact absurd hh (not_le.2 h1)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem lintegral_translate [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure]
    (φ : GA E N → ℂ) (z : ℂ) (hz : ∀ (t : ℝ) g, φ (splitCentre E N t * g) = Complex.exp (z * t) * φ g)
    (t : ℝ) (Q : Set (GA E N)) :
    ∫⁻ g in (fun q => splitCentre E N t * q) '' Q, ‖φ g‖ₑ ^ 2 ∂μ =
      ENNReal.ofReal (Real.exp (2 * z.re * t)) * ∫⁻ g in Q, ‖φ g‖ₑ ^ 2 ∂μ := by
  rw [← (measurePreserving_mul_left μ (splitCentre E N t)).setLIntegral_comp_emb
    (measurableEmbedding_mulLeft _) (fun g => ‖φ g‖ₑ ^ 2) Q,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun g => ?_
  rw [hz, enorm_mul, mul_pow]
  congr 1
  rw [← ofReal_norm_eq_enorm, Complex.norm_exp, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 2
  simp
  ring

theorem centReGlue_holds : CentReGlue := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro hS hM E _ _ _ N φ z hφ hne hL hz
  letI : MeasurableSpace (GA E N) := borel _
  haveI : BorelSpace (GA E N) := ⟨rfl⟩
  obtain ⟨C, M, hC⟩ := hL Measure.haar inferInstance
  by_contra ha
  obtain ⟨x₀, hx₀⟩ : ∃ x, φ x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (funext hcon)
  obtain ⟨Q, hQ, hQn⟩ := exists_compact_mem_nhds x₀
  obtain ⟨n, hn⟩ := hM E N Q hQ
  obtain ⟨C₁, hC₁, hsz⟩ := hS E N {1} Q isCompact_singleton hQ
  set I : ENNReal := ∫⁻ g in Q, ‖φ g‖ₑ ^ 2 ∂(Measure.haar : Measure (GA E N)) with hI
  have key : ∀ t : ℝ, ENNReal.ofReal (Real.exp (2 * z.re * t)) * I ≤
      ENNReal.ofReal (C * n * (1 + C₁ * (1 + |t|)) ^ M) := by
    intro t
    rw [hI, ← lintegral_translate _ φ z hz t Q]
    refine hC _ (hQ.image (continuous_const.mul continuous_id)) n _ (by positivity) (hn _ ?_) ?_
    · exact fun g => GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm t g
    · rintro _ ⟨q, hq, rfl⟩
      have h1 := hsz 1 rfl q hq (fun _ => t)
      rw [one_mul, PositivityTheory.Rg.Rs.JDict.tor_const] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hC₁)
      have : ‖(fun _ : Fin N => t)‖ ≤ |t| :=
        (pi_norm_le_iff_of_nonneg (abs_nonneg t)).2 fun _ => (Real.norm_eq_abs t).le
      linarith
  have hIpos : 0 < I := by
    rw [hI, setLIntegral_pos_iff (hφ.measurable.enorm.pow_const 2)]
    have hV : IsOpen (interior Q ∩ {x | φ x ≠ 0}) :=
      isOpen_interior.inter (isOpen_ne_fun hφ continuous_const)
    have hVne : (interior Q ∩ {x | φ x ≠ 0}).Nonempty :=
      ⟨x₀, mem_interior_iff_mem_nhds.2 hQn, hx₀⟩
    refine (hV.measure_pos _ hVne).trans_le (measure_mono ?_)
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, interior_subset hx1⟩
    simpa [Function.mem_support] using hx2
  have hItop : I ≠ ⊤ := by
    have h0 := key 0
    simp only [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul] at h0
    exact (h0.trans_lt ENNReal.ofReal_lt_top).ne
  have hI' : 0 < I.toReal := ENNReal.toReal_pos hIpos.ne' hItop
  have key' : ∀ t : ℝ, I.toReal * Real.exp (2 * z.re * t) ≤ C * n * (1 + C₁ * (1 + |t|)) ^ M := by
    intro t
    have h := key t
    rw [← ENNReal.ofReal_toReal hItop, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_le_ofReal_iff'] at h
    rcases h with h | h
    · rwa [mul_comm]
    · exact absurd h (not_le.2 (mul_pos (Real.exp_pos _) hI'))
  refine no_growth (2 * |z.re|) I.toReal (|C * n| * (1 + C₁) ^ M) M
    (by have := abs_pos.2 ha; positivity) hI' fun s hs => ?_
  have hsign : ∃ t : ℝ, 2 * z.re * t = 2 * |z.re| * s ∧ |t| = s := by
    rcases le_total 0 z.re with h | h
    · exact ⟨s, by rw [abs_of_nonneg h], abs_of_nonneg hs⟩
    · exact ⟨-s, by rw [abs_of_nonpos h]; ring, by rw [abs_neg, abs_of_nonneg hs]⟩
  obtain ⟨t, ht1, ht2⟩ := hsign
  have h := key' t
  rw [ht1, ht2] at h
  refine h.trans ?_
  have hb : 1 + C₁ * (1 + s) ≤ (1 + C₁) * (1 + s) := by nlinarith
  calc C * n * (1 + C₁ * (1 + s)) ^ M ≤ |C * n| * (1 + C₁ * (1 + s)) ^ M :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |C * n| * ((1 + C₁) * (1 + s)) ^ M :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb M) (abs_nonneg _)
    _ = |C * n| * (1 + C₁) ^ M * (1 + s) ^ M := by rw [mul_pow, mul_assoc]

end GlobalTheory.CompanionTheory.CentRe

end
end

section

open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace GlobalTheory.CompanionTheory.PairSpProof

theorem pairSp : PositivityTheory.Rg.BcB.E.E3.PairSp := by
  intro E _ _ _ a b F U₁ U₂ h₁ h₂ hfd
  classical
  set A : Submodule ℂ (GA E a → ℂ) := Submodule.span ℂ (Set.range fun y x => F (x, y)) with hA
  have : FiniteDimensional ℂ A := hfd
  obtain ⟨S, c, hc⟩ := PositivityTheory.Rg.Rs.SliceTensor.interp A

  let V : Submodule ℂ (GA E a → ℂ) := (U₁.map (Submodule.subtype _))
  have hAV : A ≤ V := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨φ, hφ, e⟩ := h₁ y
    exact ⟨φ, hφ, e⟩
  have hF : F = ∑ κ : S, fun x : GA E a × GA E b => (c κ : GA E a → ℂ) x.1 * F (κ.1, x.2) := by
    funext ⟨x, y⟩
    have hy : (fun x => F (x, y)) ∈ A := Submodule.subset_span ⟨y, rfl⟩
    have := congrFun (hc _ hy) x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this]
    exact Finset.sum_congr rfl fun κ _ => mul_comm _ _
  rw [hF]
  refine Submodule.sum_mem _ fun κ _ => Submodule.subset_span ?_
  obtain ⟨φ, hφ, e⟩ := hAV (c κ).2
  obtain ⟨ψ, hψ, e'⟩ := h₂ κ.1
  refine ⟨φ, hφ, ψ, hψ, ?_⟩
  funext x
  have e1 : φ.1 = (c κ : GA E a → ℂ) := e
  rw [e1, e']

end GlobalTheory.CompanionTheory.PairSpProof
end

section


theorem _root_.GlobalTheory.T.finite_mass_product_formula : PositivityTheory.Rg.BcB.G8.Fin.MassProd := by
  first | exact @GlobalTheory.CompanionTheory.MassProd.massProd | exact GlobalTheory.CompanionTheory.MassProd.massProd | (intros; apply GlobalTheory.CompanionTheory.MassProd.massProd <;> assumption)
end
