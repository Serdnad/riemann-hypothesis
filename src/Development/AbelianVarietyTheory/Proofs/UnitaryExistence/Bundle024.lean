module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermFormConjDiag
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCompatibleNormTowerProfinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SpGenStatement
import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice

@[expose] public section

section

open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FramePeriod

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


omit [NumberField E] [IsCMField E] in
lemma eq_of_hermC_eq (τ : E →+* ℂ) (Gm : Matrix (Fin r) (Fin r) E) (hG : Gm.det ≠ 0)
    (v w : Fin r → ℂ) (h : ∀ u, FD.hermC τ Gm v u = FD.hermC τ Gm w u) : v = w := by
  classical
  have hd : (τ.mapMatrix Gm).det ≠ 0 := by
    rw [← RingHom.map_det]; exact (map_ne_zero τ).2 hG
  rw [← sub_eq_zero]
  apply Matrix.eq_zero_of_vecMul_eq_zero hd
  rw [sub_vecMul, sub_eq_zero]
  funext b
  have := h (Pi.single b 1)
  simpa [FD.hermC, Pi.single_apply, apply_ite, vecMul, dotProduct] using this

lemma loc_compare (τ : E →+* ℂ) (Gm : Matrix (Fin r) (Fin r) E) (hG : Gm.det ≠ 0) (q : ℕ)
    (M M' K : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0) (hM' : M'.det ≠ 0)
    (hK : ∀ a c : Fin r, ¬ ((a : ℕ) < q ↔ (c : ℕ) < q) → K a c = 0)
    (h : ∀ u, locPer τ Gm q M' u = K *ᵥ locPer τ Gm q M u) :
    (∀ a c : Fin r, (a : ℕ) < q → K a c = (M⁻¹ * M') c a) ∧
      ∀ a c : Fin r, q ≤ (a : ℕ) → K a c = (M⁻¹ * M')⁻¹ a c := by
  classical
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.2 hM
  constructor
  · intro a c ha
    have h1 : FD.col M' a = ∑ e, K a e • FD.col M e := by
      apply eq_of_hermC_eq τ Gm hG
      intro u
      have := congrFun (h u) a
      rw [locPer_apply, if_pos ha] at this
      rw [this, FD.hermC_sum_left, mulVec, dotProduct]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [FD.hermC_smul_left, locPer_apply]
      by_cases he : (e : ℕ) < q
      · rw [if_pos he]
      · rw [hK a e (by simp [ha, he])]; simp
    rw [← FD.Data.mulVec_eq_sum_col] at h1
    have h2 : M⁻¹ *ᵥ FD.col M' a = K a := by
      rw [h1, mulVec_mulVec, Matrix.nonsing_inv_mul _ hMu, one_mulVec]
    rw [← h2]
    rfl
  · intro a c ha
    have ha' : ¬ (a : ℕ) < q := not_lt.2 ha
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hMu]
    have h1 := congrFun (h (M *ᵥ Pi.single c 1)) a
    rw [locPer_apply, if_neg ha', mulVec_mulVec] at h1
    have h2 : (K *ᵥ locPer τ Gm q M (M *ᵥ Pi.single c 1)) a = (K *ᵥ Pi.single c 1) a := by
      rw [mulVec, mulVec, dotProduct, dotProduct]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases he : (e : ℕ) < q
      · rw [hK a e (by simp [ha', he])]; simp
      · rw [locPer_apply, if_neg he, mulVec_mulVec, Matrix.nonsing_inv_mul _ hMu, one_mulVec]
    rw [h2] at h1
    simpa using h1.symm

lemma allPer_scale {Ψ : Finset (E →+* ℂ)} (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ) (x : FD.Frame Ψ r)
    {g : ℕ} (idx : Fin g ≃ Ψ × Fin r) (c : Ψ → ℂ) (y : Ψ → Fin r → ℂ) (k : Fin g) :
    allPer Gm q x idx (fun τ => c τ • y τ) k =
      (if ((idx k).2 : ℕ) < q then conj (c (idx k).1) else c (idx k).1) * allPer Gm q x idx y k := by
  rw [allPer_apply, allPer_apply, locPer_apply, locPer_apply]
  split_ifs
  · rw [FD.hermC_smul_right]
  · rw [mulVec_smul]; rfl

lemma block_of_allPer {Ψ : Finset (E →+* ℂ)} (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ)
    (x x' : FD.Frame Ψ r) {g : ℕ} (idx : Fin g ≃ Ψ × Fin r) (h : Matrix (Fin g) (Fin g) ℂ)
    (hs : Function.Surjective (allPer Gm q x idx))
    (hh : ∀ y, allPer Gm q x' idx y = h *ᵥ allPer Gm q x idx y) (k k' : Fin g)
    (hk : ¬ ((idx k).1 = (idx k').1 ∧ (((idx k).2 : ℕ) < q ↔ ((idx k').2 : ℕ) < q))) : h k k' = 0 := by
  classical
  have key : ∀ c : Ψ → ℂ, ((if ((idx k).2 : ℕ) < q then conj (c (idx k).1) else c (idx k).1) -
      (if ((idx k').2 : ℕ) < q then conj (c (idx k').1) else c (idx k').1)) * h k k' = 0 := by
    intro c
    obtain ⟨y, hy⟩ := hs (Pi.single k' 1)
    have h1 := congrFun (hh (fun τ => c τ • y τ)) k
    rw [allPer_scale, hh, hy] at h1
    have h2 : allPer Gm q x idx (fun τ => c τ • y τ) = Pi.single k'
        (if ((idx k').2 : ℕ) < q then conj (c (idx k').1) else c (idx k').1) := by
      funext l
      rw [allPer_scale, hy]
      by_cases hl : l = k'
      · subst hl; simp
      · simp [hl]
    rw [h2] at h1
    simp only [mulVec_single, Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, mul_one] at h1
    linear_combination h1
  by_cases h1 : (idx k).1 = (idx k').1
  · have h2 := key (fun _ => Complex.I)
    have hI : (2 * Complex.I) ≠ 0 := by simp
    by_cases ha : ((idx k).2 : ℕ) < q <;> by_cases hb : ((idx k').2 : ℕ) < q
    · exact absurd ⟨h1, by simp [ha, hb]⟩ hk
    · rw [if_pos ha, if_neg hb, Complex.conj_I] at h2
      apply mul_left_cancel₀ hI
      linear_combination -h2
    · rw [if_neg ha, if_pos hb, Complex.conj_I] at h2
      apply mul_left_cancel₀ hI
      linear_combination h2
    · exact absurd ⟨h1, by simp [ha, hb]⟩ hk
  · have h2 := key (Pi.single (idx k).1 1)
    simpa [Ne.symm h1] using h2

theorem frame_of_period_linear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+* ℂ)) (hty : ∀ k, ty k = if ((idx k).2 : ℕ) < D.q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1), FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → ∀ (P : D.La →+ (Fin g → ℂ)), ∀ x ∈ FD.GG Ψ Gm D.q, ∀ x' ∈ FD.GG Ψ Gm D.q, (∀ v k, P v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → ∀ (P' : D.La →+ (Fin g → ℂ)), (∀ v k, P' v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x' (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x' (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → ∀ h : Matrix (Fin g) (Fin g) ℂ, (∀ v, P' v = h *ᵥ P v) → ∃ b : FD.Frame Ψ r, x' = FD.rmul x b ∧ (∀ τ (a c : Fin r), (c : ℕ) < D.q → D.q ≤ (a : ℕ) → b τ a c = 0) ∧ (∀ k k', (idx k).1 = (idx k').1 → ((idx k).2 : ℕ) < D.q → ((idx k').2 : ℕ) < D.q → h k k' = b (idx k).1 (idx k').2 (idx k).2) ∧ (∀ k k', (idx k).1 = (idx k').1 → D.q ≤ ((idx k).2 : ℕ) → D.q ≤ ((idx k').2 : ℕ) → h k k' = (FD.mat b (idx k).1)⁻¹ (idx k).2 (idx k').2) ∧ ∀ k k', ty k ≠ ty k' → h k k' = 0 := by
  classical
  intro E _ _ _ H D r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos ⟨hφ, hspan, hG, hdet, hEF⟩ P x hx x' hx' hP P' hP' h hh
  have hcm := cmType H Ψ hΨ
  have hloc := fun τ : Ψ => (exists_loc τ.1 Gm hG D.q (FD.mat x τ) (hx τ).1 (hx τ).2).1
  have hbij := allPer_bijective Gm D.q x idx hloc
  have hQ : ∀ v, P v = allPer Gm D.q x idx (CMLattice.embAll Ψ r (φ v)) := fun v =>
    funext fun k => hP v k
  have hQ' : ∀ v, P' v = allPer Gm D.q x' idx (CMLattice.embAll Ψ r (φ v)) := fun v =>
    funext fun k => hP' v k
  have := D.fin
  obtain ⟨b, hb⟩ := CMLattice.exists_basis_of_cmType Ψ hcm r (LinearMap.range φ)
    (Module.Finite.iff_fg.1 inferInstance) (by rw [LinearMap.coe_range]; exact hspan)
  have hall : ∀ y, allPer Gm D.q x' idx y = h *ᵥ allPer Gm D.q x idx y := by
    have : allPer Gm D.q x' idx = (h.mulVecLin.restrictScalars ℝ) ∘ₗ allPer Gm D.q x idx := by
      apply b.ext
      intro i
      obtain ⟨_, ⟨v, rfl⟩, hv⟩ := (hb (b i)).1 (Submodule.subset_span ⟨i, rfl⟩)
      rw [← hv, ← hQ', hh, hQ]
      rfl
    intro y
    rw [this]; rfl
  have hblock := block_of_allPer Gm D.q x x' idx h hbij.2 hall
  let K : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ =>
    Matrix.of fun a c => h (idx.symm (τ, a)) (idx.symm (τ, c))
  have hK0 : ∀ τ (a c : Fin r), ¬ ((a : ℕ) < D.q ↔ (c : ℕ) < D.q) → K τ a c = 0 := by
    intro τ a c hac
    apply hblock
    simpa using hac
  have hK : ∀ (τ : Ψ) u, locPer τ.1 Gm D.q (FD.mat x' τ) u =
      K τ *ᵥ locPer τ.1 Gm D.q (FD.mat x τ) u := by
    intro τ u
    funext a
    have h1 := congrFun (allPer_symm Gm D.q x' idx (fun _ => u) τ) a
    rw [← h1, hall, mulVec, mulVec, dotProduct, dotProduct, ← idx.symm.sum_comp, Fintype.sum_prod_type,
      Finset.sum_eq_single τ]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [← allPer_symm Gm D.q x idx (fun _ => u) τ]
      rfl
    · intro σ _ hσ
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [hblock, zero_mul]
      simp [hσ.symm]
    · simp
  have hc := fun τ : Ψ => loc_compare τ.1 Gm hdet D.q (FD.mat x τ) (FD.mat x' τ) (K τ) (hx τ).1 (hx' τ).1
    (hK0 τ) (hK τ)
  have hhK : ∀ k k', (idx k).1 = (idx k').1 → h k k' = K (idx k).1 (idx k).2 (idx k').2 := by
    intro k k' e
    simp only [K, of_apply]
    conv_rhs => rw [Prod.mk.eta, e, Prod.mk.eta]
    simp
  refine ⟨fun τ => ((FD.mat x τ)⁻¹ * FD.mat x' τ : Matrix (Fin r) (Fin r) ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · funext τ
    exact (Matrix.mul_nonsing_inv_cancel_left (FD.mat x τ) (FD.mat x' τ)
      (isUnit_iff_ne_zero.2 (hx τ).1)).symm
  · intro τ a c hcq ha
    exact ((hc τ).1 c a hcq).symm.trans (hK0 τ c a (by simp [hcq, ha]))
  · intro k k' e h1 _
    rw [hhK k k' e]
    exact (hc _).1 _ _ h1
  · intro k k' e h1 _
    rw [hhK k k' e]
    exact (hc _).2 _ _ h1
  · intro k k' hne
    apply hblock
    rintro ⟨e1, e2⟩
    apply hne
    rw [hty, hty, e1]
    simp only [e2]

end

end GlobalTheory.FramePeriod
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)
open Formalism.L2.Pj

namespace GlobalTheory.LocalDepthCompare

section Places

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem valV_le_one (v : V) : valV V (algebraMap V K' v) ≤ 1 :=
  HeightOneSpectrum.valuation_le_one _ v

theorem valV_lt_one_iff (v : V) : valV V (algebraMap V K' v) < 1 ↔ v ∈ maximalIdeal V :=
  HeightOneSpectrum.valuation_lt_one_iff_mem _ v

theorem valV_eq_one {v : V} (h : v ∉ maximalIdeal V) : valV V (algebraMap V K' v) = 1 :=
  le_antisymm (valV_le_one v) (not_lt.1 fun h' => h ((valV_lt_one_iff v).1 h'))

theorem vV_pos {v : V} (h0 : v ≠ 0) (h : v ∈ maximalIdeal V) : 0 < vV V (algebraMap V K' v) := by
  have h1 : algebraMap V K' v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K')).2 h0
  have := (WithZero.log_lt_log (valV_ne_zero (V := V) h1) one_ne_zero).2 ((valV_lt_one_iff v).2 h)
  simp only [WithZero.log_one] at this
  simp only [vV]; omega

theorem not_charZero_iff : ¬ CharZero (ResidueField V) ↔ ∃ n : ℕ, n ≠ 0 ∧ (n : V) ∈ maximalIdeal V := by
  constructor
  · intro h
    by_contra hn
    refine h (charZero_of_inj_zero fun n h0 => ?_)
    by_contra hn0
    exact hn ⟨n, hn0, by rw [← residue_eq_zero_iff, map_natCast, h0]⟩
  · rintro ⟨n, hn, hm⟩ _
    rw [← residue_eq_zero_iff, map_natCast] at hm
    exact hn (by exact_mod_cast hm)

variable {K : Type} [Field K] [NumberField K]

theorem not_charZero_of_overLa {la : HeightOneSpectrum (𝓞 K)} {io : K →+* K'} {e : ℕ}
    (ho : OverLa la V io e) : ¬ CharZero (ResidueField V) := by
  rw [not_charZero_iff]
  have hn : Ideal.absNorm la.asIdeal ≠ 0 := fun h => la.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨_, hn, ?_⟩
  have hmem := Ideal.absNorm_mem la.asIdeal
  generalize Ideal.absNorm la.asIdeal = n at hn hmem
  by_contra hV
  have hK : ((n : ℕ) : K) ≠ 0 := by exact_mod_cast hn
  have h1 : valV V ((n : ℕ) : K') = 1 := by
    rw [← map_natCast (algebraMap V K') n]
    exact valV_eq_one hV
  have h2 : la.valuation K ((n : ℕ) : K) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 K) K) n, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hmem
  have h3 : WithZero.log (la.valuation K ((n : ℕ) : K)) < 0 := by
    have := (WithZero.log_lt_log ((la.valuation K).ne_zero_iff.2 hK) one_ne_zero).2 h2
    simpa using this
  have h4 := ho.2 ((n : ℕ) : K)
  rw [map_natCast, vV, h1, vLa, WithZero.log_one] at h4
  have he : (0 : ℤ) < e := by exact_mod_cast ho.1
  nlinarith [mul_pos he (neg_pos.2 h3)]

theorem exists_overLa_of_not_charZero (io : K →+* K') (hT : ¬ CharZero (ResidueField V)) :
    ∃ (la : HeightOneSpectrum (𝓞 K)) (e : ℕ), OverLa la V io e := by
  have hint : ∀ a : 𝓞 K, ∃ v : V, algebraMap V K' v = io a := fun a =>
    IsIntegrallyClosed.algebraMap_eq_of_integral (R := V) (K := K')
      (IsIntegral.map_of_comp_eq (Int.castRingHom V) io (RingHom.ext_int _ _) a.isIntegral_coe)
  choose g0 hg0 using hint
  have hinj := IsFractionRing.injective V K'
  let g : 𝓞 K →+* V :=
    { toFun := g0
      map_one' := hinj (by simp [hg0])
      map_mul' := fun a b => hinj (by simp [hg0])
      map_zero' := hinj (by simp [hg0])
      map_add' := fun a b => hinj (by simp [hg0]) }
  have hg : ∀ a, algebraMap V K' (g a) = io (algebraMap (𝓞 K) K a) := hg0
  have hne : (maximalIdeal V).comap g ≠ ⊥ := by
    obtain ⟨n, hn, hm⟩ := not_charZero_iff.1 hT
    intro h
    have h1 : ((n : ℕ) : 𝓞 K) ∈ (maximalIdeal V).comap g := by
      rw [Ideal.mem_comap, map_natCast]; exact hm
    rw [h, Ideal.mem_bot] at h1
    exact hn (by exact_mod_cast h1)
  let la : HeightOneSpectrum (𝓞 K) := ⟨(maximalIdeal V).comap g, Ideal.comap_isPrime _ _, hne⟩
  have hun : ∀ a : 𝓞 K, a ∉ la.asIdeal → valV V (io (algebraMap (𝓞 K) K a)) = 1 := fun a ha => by
    rw [← hg]
    exact valV_eq_one ha
  have hone : ∀ x : K, la.valuation K x = 1 → valV V (io x) = 1 := fun x hx => by
    obtain ⟨n, d, h⟩ := la.exists_primeCompl_mul_eq_of_integer x hx.le
    have hd : la.valuation K (algebraMap (𝓞 K) K d) = 1 := (la.valuation_eq_one_iff_notMem).2 d.2
    have hn : la.valuation K (algebraMap (𝓞 K) K n) = 1 := by rw [← h, map_mul, hx, hd, one_mul]
    have h2 := hun n ((la.valuation_eq_one_iff_notMem).1 hn)
    rwa [← h, map_mul, map_mul, hun d d.2, mul_one] at h2
  obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
  have hπK : la.valuation K (algebraMap (𝓞 K) K π) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, hπ]
  have hπ0 : algebraMap (𝓞 K) K π ≠ 0 := fun h => by
    simp [h] at hπK; exact WithZero.exp_ne_zero hπK.symm
  have hπm : π ∈ la.asIdeal := by
    rw [← la.valuation_lt_one_iff_mem (K := K), hπK, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hpos : 0 < vV V (io (algebraMap (𝓞 K) K π)) := by
    rw [← hg]
    refine vV_pos (fun h => ?_) hπm
    have := hg π
    rw [h, map_zero] at this
    exact (map_ne_zero io).2 hπ0 this.symm
  refine ⟨la, (vV V (io (algebraMap (𝓞 K) K π))).toNat, by omega, fun a => ?_⟩
  rw [Int.toNat_of_nonneg hpos.le]
  by_cases ha : a = 0
  · simp [ha, vV, vLa]
  have hva : la.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have h1 := hone (a * (algebraMap (𝓞 K) K π) ^ (-vLa la a)) (by
    rw [map_mul, map_zpow₀, hπK, ← WithZero.exp_zsmul, ← WithZero.exp_log hva, ← WithZero.exp_add]
    simp [vLa])
  have h2 := congrArg WithZero.log h1
  rw [map_mul, map_mul, map_zpow₀, map_zpow₀, WithZero.log_mul (valV_ne_zero ((map_ne_zero io).2 ha))
    (zpow_ne_zero _ (valV_ne_zero ((map_ne_zero io).2 hπ0))), WithZero.log_zpow,
    WithZero.log_one] at h2
  simp only [vV, smul_eq_mul] at h2 ⊢
  linarith

end Places

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

section Local

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

variable {la : HeightOneSpectrum (𝓞 c.F)} {e : ℕ}

end Local

variable (Xo c)

end GlobalTheory.LocalDepthCompare
end
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.HolSec

theorem exists_sec_pull {X X' : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (W : X.Opens) (mem : ∀ x, F x ∈ W)
    (θ₀ : ∀ j, Γ(X, W ⊓ L.U j)) (hθ₀ : θ₀ ∈ secOn L W) :
    ∃ t : LB.Sec (L.pull F), ∀ j (x : Sp ℂ ⟶ X'), ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j →
      valAt' x ((L.pull F).U (fun _ => j)) (t.f (fun _ => j)) = valAt' (x ≫ F) (W ⊓ L.U j) (θ₀ j) := by
  have le : ∀ J, (L.pull F).U J ≤ F ⁻¹ᵁ (W ⊓ L.U (J PUnit.unit)) := fun J x hx => ⟨mem x, mem_pull.1 hx⟩
  have ev : ∀ y J, y ∈ (L.pull F).U J → gs (𝟙 _) y _ ((F.appLE _ _ (le J)).hom (θ₀ _)) = gs F y _ (θ₀ (J PUnit.unit)) :=
    fun y J h => (gs_appLE F _ _ (le J) (𝟙 _) y h _).trans (by rw [Category.id_comp])
  refine ⟨⟨fun J => (F.appLE _ _ (le J)).hom (θ₀ _), fun J J' => fn_ext fun y hy => ?_⟩, fun j x hx => ?_⟩
  · have h := mem_pull.1 hy.1
    have h' := mem_pull.1 hy.2
    have hm : F y ∈ W ⊓ L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit) := ⟨⟨mem y, h⟩, h'⟩
    have e := congrArg (gs F y _) (hθ₀ (J PUnit.unit) (J' PUnit.unit))
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, gs_unit _ y (L.U _ ⊓ L.U _) ⟨h, h'⟩] at e
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy, ev y J hy.1, ev y J' hy.2,
      gm_pull_g L F (𝟙 _) y J J' hy.1 hy.2, Category.id_comp]
    exact e
  · exact valAt'_appLE x F _ _ (le _) _ (fun p hp => mem_pull.2 (hx hp))

end GlobalTheory.HolSec
end
end

section

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.exists_compatible_norm_tower_profinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (ν : ℕ → ℤ), (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) → (∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) → ∃ t : ℕ → 𝓞 E, (∀ n : ℕ, 0 < n → (n : 𝓞 E) ∣ t n * H.bar (t n) - (ν n : 𝓞 E)) ∧ (∀ n m : ℕ, 0 < n → 0 < m → (n : 𝓞 E) ∣ t (n * m) - t n) ∧ t l.M - 1 ∈ l.Mb := by
  first | exact @GlobalTheory.NormTower.exists_norm_tower | exact GlobalTheory.NormTower.exists_norm_tower | (intros; apply GlobalTheory.NormTower.exists_norm_tower <;> assumption)
end
