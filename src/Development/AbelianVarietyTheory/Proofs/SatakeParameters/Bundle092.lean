module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DerivationCoordinateChange
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle062
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Formalism.SharpRestriction.ParConsts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Formalism.GaussJetBounds.Bundle001
public import Formalism.GaussJetBounds.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

@[expose] public section

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.EntryHomComb

open Matrix

variable {p : ℕ} [Fact p.Prime]

theorem det_map_isUnit (D : D7) (ρ : D.host.E →+* ℂ_[p]) {N : ℕ} {P : Matrix (Fin N) (Fin N) D.host.E}
    (h : P.det ≠ 0) : IsUnit (P.map ρ).det := by
  have := ρ.map_det P
  rw [RingHom.mapMatrix_apply] at this
  rw [← this]
  exact Ne.isUnit ((map_ne_zero ρ).2 h)

theorem coord_le_one (D : D7) (ρ : D.host.E →+* ℂ_[p]) {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {P : Matrix (Fin N) (Fin N) D.host.E} (hP : LocBasisW D ρ L P) {x : Fin N → D.host.E} (hx : x ∈ L) (m : Fin N) :
    ‖((P.map ρ)⁻¹ *ᵥ fun i => ρ (x i)) m‖ ≤ 1 := by
  obtain ⟨s, hs, c, hc⟩ := hP.2.2 x hx
  have hs0 : ρ (s : D.host.E) ≠ 0 := by
    intro h; rw [h, norm_zero] at hs; exact zero_ne_one hs
  have e : ∀ i, (s : D.host.E) * x i = ∑ a, (c a : D.host.E) * P i a := fun i => by
    have := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply] at this
    exact this
  have h1 : (fun i => ρ (x i)) = (P.map ρ) *ᵥ fun a => (ρ (s : D.host.E))⁻¹ * ρ (c a : D.host.E) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    have h2 := congrArg ρ (e i)

    rw [map_mul, map_sum] at h2
    simp only [map_mul] at h2
    calc ρ (x i) = (ρ (s : D.host.E))⁻¹ * (ρ (s : D.host.E) * ρ (x i)) := by field_simp
      _ = _ := by
        rw [h2, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
  rw [h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (det_map_isUnit D ρ hP.1), Matrix.one_mulVec, norm_mul,
    norm_inv, hs, inv_one, one_mul]
  exact GlobalTheory.JetTieCompare.norm_int_le ρ (c m)

theorem inv_mul_le_one (D : D7) {lm : Qbar →+* ℂ_[p]} {τ : D.what₂.Tau} (ρ : D.host.E →+* ℂ_[p]) (hρ : tauEmb D lm τ = ρ)
    {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {B P : Matrix (Fin N) (Fin N) _}
    (hB : GL3Columns.BasR D lm τ L B) (hP : LocBasisW D ρ L P) (m b : Fin N) : ‖((P.map ρ)⁻¹ * B) m b‖ ≤ 1 := by
  obtain ⟨n, r, x, hr, hx, hcol⟩ := hB.2.2 b
  have : ((P.map ρ)⁻¹ * B) m b = ∑ k, r k * ((P.map ρ)⁻¹ *ᵥ fun i => ρ (x k i)) m := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hcol, hρ, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hr k) (norm_nonneg _) (coord_le_one D ρ hP (hx k) m)

theorem inv_mul_le_one' (D : D7) {lm : Qbar →+* ℂ_[p]} {τ : D.what₂.Tau} (ρ : D.host.E →+* ℂ_[p]) (hρ : tauEmb D lm τ = ρ)
    {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {B : Matrix (Fin N) (Fin N) ℂ_[p]}
    {P : Matrix (Fin N) (Fin N) D.host.E}
    (hB : GL3Columns.BasR D lm τ L B) (hP : LocBasisW D ρ L P) (a i : Fin N) : ‖(B⁻¹ * P.map ρ) a i‖ ≤ 1 := by
  obtain ⟨s, hs, hmem⟩ := hP.2.1 i
  have h := hB.2.1 _ hmem a
  rw [hρ] at h
  have e : (fun j => ρ ((s • P.transpose i) j)) = ρ (s : D.host.E) • fun j => ρ (P j i) := by
    funext j
    change ρ ((s : D.host.E) * P j i) = ρ (s : D.host.E) * ρ (P j i)
    rw [map_mul]
  rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, hs, one_mul] at h
  convert h using 2
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem entry_comb : ∀ (D : D7) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (τ : D.what₂.Tau) (B : Matrix (Fin N) (Fin N) ℂ_[p]) (B' : Matrix (Fin N') (Fin N') ℂ_[p]), GL3Columns.BasR D lm τ L B → GL3Columns.BasR D lm τ L' B' → ∀ (a : Fin N) (b : Fin N'), ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (A : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, A j ∈ homL D L L') ∧ ∀ k l, B' k b * B⁻¹ a l = ∑ j, r j * tauEmb D lm τ (A j k l) := by
  intro D N N' L L' hA p _ lm τ B B' hB hB' a b
  obtain ⟨ρ, hρ⟩ := GlobalTheory.JetTieCompare.exists_tauHom D lm τ
  obtain ⟨P, hP⟩ := GlobalTheory.JetTieCompare.exists_locBasis D ρ L hA.2.2.1.1 hA.2.2.1.2.1
  obtain ⟨P', hP'⟩ := GlobalTheory.JetTieCompare.exists_locBasis D ρ L' hA.2.2.2.1 hA.2.2.2.2.1
  have hex : ∀ q : Fin N' × Fin N, ∃ s : D.host.E, ‖ρ s‖ = 1 ∧
      (Matrix.of fun i j => s * (P' i q.1 * P⁻¹ q.2 j)) ∈ homL D L L' := fun q =>
    GlobalTheory.Proof.DirectionalDerivative.exists_smul_mem_homL D ρ hA.2.2.1.1 hP hP' q.2 q.1
  choose s hs hsA using hex
  have hs0 : ∀ q, ρ (s q) ≠ 0 := fun q h => by rw [← norm_eq_zero, hs q] at h; exact one_ne_zero h
  let e := Fintype.equivFin (Fin N' × Fin N)
  have hdet := det_map_isUnit D ρ hP.1
  have hdet' := det_map_isUnit D ρ hP'.1
  have hinv : (P.map ρ)⁻¹ = (P⁻¹).map ρ := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hP.1), Matrix.map_one _ (map_zero ρ) (map_one ρ)]
  refine ⟨Fintype.card (Fin N' × Fin N),
    fun j => ((P'.map ρ)⁻¹ * B') (e.symm j).1 b * (B⁻¹ * P.map ρ) a (e.symm j).2 * (ρ (s (e.symm j)))⁻¹,
    fun j => Matrix.of fun k l => s (e.symm j) * (P' k (e.symm j).1 * P⁻¹ (e.symm j).2 l), fun j => ?_,
    fun j => hsA _, fun k l => ?_⟩
  · rw [norm_mul, norm_mul, norm_inv, hs, inv_one, mul_one]
    exact mul_le_one₀ (inv_mul_le_one D ρ hρ hB' hP' _ b) (norm_nonneg _) (inv_mul_le_one' D ρ hρ hB hP a _)
  · have e1 : B' k b = ∑ m, ρ (P' k m) * ((P'.map ρ)⁻¹ * B') m b := by
      conv_lhs => rw [← Matrix.mul_nonsing_inv_cancel_left (P'.map ρ) B' hdet']
      rw [Matrix.mul_apply]
      simp only [Matrix.map_apply]
    have e2 : B⁻¹ a l = ∑ i, (B⁻¹ * P.map ρ) a i * ρ (P⁻¹ i l) := by
      conv_lhs => rw [← Matrix.mul_nonsing_inv_cancel_right (P.map ρ) B⁻¹ hdet, hinv]
      rw [Matrix.mul_apply]
      simp only [Matrix.map_apply]
    rw [e1, e2, Finset.sum_mul_sum, ← Fintype.sum_prod_type', hρ, ← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.of_apply, map_mul]
    field_simp [hs0 (e.symm j)]

end GlobalTheory.EntryHomComb
end
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.BlockWindow


open Formalism.MainNotions.AdmissibleParameterJ in
theorem JJ_finite_ncard {D : D7} (L : SizeData₂ D) (hb : AdmissibleParameterJ.CloudCentreDistance L) (hn : 0 < D.R.nV) (up : Bool) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (ρ : D.what₂.Tau) : (JJ D up j ρ).Finite ∧ (JJ D up j ρ).ncard = D.R.nV := by
  have hc : (Jp D j ρ).ncard = D.R.nV := (hb j h1 h2 ρ).2.2.2.2.2
  have hf : (Jp D j ρ).Finite := Set.finite_of_ncard_pos (by omega)
  cases up with
  | true => simpa [JJ] using And.intro hf hc
  | false =>
    have hinj : Function.Injective (AdmissibleParameterJ.refl D) := by
      intro a b hab
      simp only [AdmissibleParameterJ.refl] at hab
      linarith
    have hEq : Jm D j ρ = AdmissibleParameterJ.refl D '' Jp D j ρ := by
      ext q
      simp only [Jm, reflS, Set.mem_setOf_eq, Set.mem_image]
      constructor
      · intro h
        exact ⟨_, h, by simp [AdmissibleParameterJ.refl]⟩
      · rintro ⟨u, hu, rfl⟩
        have : AdmissibleParameterJ.refl D (AdmissibleParameterJ.refl D u) = u := by simp [AdmissibleParameterJ.refl]
        rwa [this]
    simp only [JJ, Bool.false_eq_true, if_false]
    rw [hEq]
    exact ⟨hf.image _, by rw [Set.ncard_image_of_injective _ hinj, hc]⟩

theorem jumpWindow_of_jumpSets : ∀ (D : D7) (large₂ : SizeData₂ D), AdmissibleParameterJ.JumpConditions large₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → D.R.t ≤ ⌊2 * large₂.sc.b⌋₊ ∧ ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ π : D.nd.X i, GlobalTheory.BlockWindow.JumpWindow D i r π ⌊2 * large₂.sc.b⌋₊ := by
  classical
  intro D large₂ hJ hP
  obtain ⟨⟨ep, hA⟩, hb, -, -, he, -, -⟩ := hJ
  have hn : 0 < D.R.nV := by
    have := D.R.rank_add_five_le
    unfold Ranks.nV; omega
  have hS := large₂.Sc_pos
  have hη := large₂.etaSz_pos
  have hP' : large₂.Sc + large₂.etaSz + (D.R.t : ℝ) + 2 ≤ large₂.sc.b := hP
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨Nat.le_floor (by linarith), ?_⟩
  intro i r hr π w hw CL h τ
  obtain ⟨g, ρ, -, hx, -⟩ := hA i r hr w hw ⟨CL, h⟩ τ
  have hj := D.nd.j_range i
  obtain ⟨hfin, hcard⟩ := JJ_finite_ncard large₂ hb hn (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) hj.1 hj.2 ρ
  have hpre : ((fun a : ℤ => (a : ℚ)) ⁻¹' AdmissibleParameterJ.JJ D (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) ρ).Finite :=
    hfin.preimage (Int.cast_injective.injOn)
  refine ⟨hpre.toFinset, ?_, ?_, ?_⟩
  · rw [← hcard, ← Set.ncard_eq_toFinset_card _ hpre,
      ← Set.ncard_image_of_injective _ (Int.cast_injective (α := ℚ))]
    exact Set.ncard_le_ncard (Set.image_preimage_subset _ _) hfin
  · intro u hu
    have hu' : (u : ℚ) ∈ AdmissibleParameterJ.JJ D (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) ρ := by
      simpa using hu
    have hbd := he.1 _ hj.1 hj.2 ρ _ _ hu'
    have hc0 : ((AdmissibleParameterJ.c0 D : ℚ) : ℝ) = ((D.R.t : ℝ) - 1) / 2 := by
      simp [AdmissibleParameterJ.c0]
    rw [hc0] at hbd
    have habs : ((u.natAbs : ℕ) : ℝ) = |((u : ℚ) : ℝ)| := by
      simp [Nat.cast_natAbs]
    have hle : u.natAbs + 1 ≤ ⌊2 * large₂.sc.b⌋₊ := by
      apply Nat.le_floor
      push_cast
      rw [habs]
      linarith
    omega
  · intro a ha
    have : (a : ℚ) ∈ AdmissibleParameterJ.JJ D (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) ρ := (hx π a).1.1 ha
    simpa using this

end GlobalTheory.BlockWindow
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.TwU

theorem two_rG_le_k_of_size {D : Formalism.BasicNotions.D7} {L : SizeData₂ D} (hS : Formalism.MainNotions.SizesAt L)
    (h : 70 < L.sc.x * L.sc.eps) : 2 * Formalism.MainNotions.G.rG L.sc ≤ D.R.k := by
  by_contra hk
  have hk : D.R.k < 2 * Formalism.MainNotions.G.rG L.sc := not_le.1 hk
  have hx := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  have he2 := L.sc.eps_lt
  have hK := hS.2.2.1.1
  have h1 : L.sc.x ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - Formalism.MainNotions.szTh L) :=
    Real.self_le_rpow_of_one_le hx.le (by unfold Formalism.MainNotions.szTh; linarith)
  have h2 : (D.R.k : ℝ) ≤ 2 * (Formalism.MainNotions.G.rG L.sc : ℝ) := by exact_mod_cast hk.le
  have h3 : (Formalism.MainNotions.G.rG L.sc : ℝ) ≤ 8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2 := by
    unfold Formalism.MainNotions.G.rG Formalism.MainNotions.G.KG
    have := Nat.ceil_lt_add_one (a := 8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps)
      (div_nonneg (by unfold Formalism.MainNotions.G.hG; linarith) he.le)
    push_cast
    linarith
  have h5 : L.sc.x ≤ 2 * (8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2) := by linarith
  have h6 := mul_le_mul_of_nonneg_right h5 he.le
  have h7 : 2 * (8 * (Formalism.MainNotions.G.hG L.sc + 2) / L.sc.eps + 2) * L.sc.eps =
      2 * (8 * (Formalism.MainNotions.G.hG L.sc + 2) + 2 * L.sc.eps) := by
    field_simp
  rw [h7] at h6
  unfold Formalism.MainNotions.G.hG at h6
  linarith

theorem two_rG_le_k_large {eps : ℝ} (Fm : FamP eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, 2 * rG (Fm.L x i).sc ≤ (Fm.D x i).R.k := by
  refine ⟨71 / eps, fun x hx hx1 i => two_rG_le_k_of_size (Fm.sizes x hx1 i) ?_⟩
  have hs : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have he : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hp : 0 < eps := he ▸ (Fm.L x i).sc.eps_pos
  rw [hs, he]
  have : 71 ≤ x * eps := (div_le_iff₀ hp).1 hx
  linarith

end GlobalTheory.TwU
end
end

section

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.ShNums

theorem pow_six_le_exp {eps : ℝ} (he : 0 < eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, 4 ≤ x ∧ x ^ 6 ≤ Real.exp (x ^ (eps / 3)) := by
  have h := (isLittleO_log_rpow_atTop (r := eps / 3) (by positivity)).bound (c := 1 / 6) (by norm_num)
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (h.and (Filter.eventually_ge_atTop (4 : ℝ)))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx0 x hx
  have hx' : 0 < x := by linarith
  refine ⟨h2, ?_⟩
  have hp : 0 < x ^ (eps / 3) := Real.rpow_pos_of_pos hx' _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp] at h1
  have h3 : Real.log x ≤ 1 / 6 * x ^ (eps / 3) := (le_abs_self _).trans h1
  calc x ^ 6 = Real.exp (Real.log (x ^ 6)) := (Real.exp_log (by positivity)).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.2
      rw [Real.log_pow]
      push_cast
      linarith

theorem size_rel_at {D : D7} (L : SizeData₂ D) (hs : SizesAt L) (h4 : 4 ≤ L.sc.x) (h6 : L.sc.x ^ 6 ≤ L.sc.X') :
    (D.R.k : ℝ) * D.R.N D.R.m ≤ L.Sc / 4 ∧ (D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n ∧
    (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' D.R.n ∧ L.etaSz ≤ L.sc.w'' D.R.n ∧
    L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x ∧ 4 ≤ L.sc.x ∧ 2 * L.sc.b' ≤ L.sc.b ∧
    (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b ∧ 1 ≤ L.sc.w'' D.R.n ∧ L.etaSz + 1 + 3 * L.Sc ≤ L.sc.b := by
  obtain ⟨-, -, hK, -, -, -, -, -, -, -, -, -, -, hEta, -, -, hDel, hW, -⟩ := hs
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hx0 : 0 < L.sc.x := by linarith
  have he := L.sc.eps_pos
  have he' := L.sc.eps_lt
  have hm : (1 : ℝ) ≤ D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := by
      unfold Ranks.n
      exact D.R.ord_pos
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    refine le_trans (Real.one_le_rpow hx1 ?_) hK.1
    unfold szTh
    linarith
  have hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ 5 := by
    refine hK.2.trans ?_
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    unfold szTh
    push_cast
    linarith
  have hb1 : 1 ≤ L.sc.b := by
    unfold Scale.b Scale.L
    exact Real.one_le_exp (by positivity)
  have hX : 0 < L.sc.X' := Real.exp_pos _
  have hb' : L.sc.b' * L.sc.X' = L.sc.x * L.sc.b := by
    unfold Scale.b' Scale.a
    field_simp
  have hb'0 : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a
    positivity
  have h5b : L.sc.x ^ 5 * L.sc.b' ≤ L.sc.b := by
    have : L.sc.x * (L.sc.x ^ 5 * L.sc.b') ≤ L.sc.x * L.sc.b := by
      rw [← hb']
      calc L.sc.x * (L.sc.x ^ 5 * L.sc.b') = L.sc.b' * L.sc.x ^ 6 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h6 hb'0.le
    exact le_of_mul_le_mul_left this hx0
  have hx5 : (4 : ℝ) ^ 5 ≤ L.sc.x ^ 5 := pow_le_pow_left₀ (by norm_num) h4 5
  have h5b' : 5 * L.sc.b' ≤ L.sc.b := by nlinarith
  have hw : L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x := by
    unfold Scale.w''
    apply div_le_div_of_nonneg_left hb'0.le hx0
    nlinarith
  have hw' : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0.le hx1
  have hw1 : 1 ≤ L.sc.w'' D.R.n := le_trans (Real.one_le_sqrt.2 hb1) hW
  have heta0 := L.etaSz_pos
  have hS0 := L.Sc_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have heta : L.etaSz ≤ L.sc.w'' D.R.n := by
    refine le_trans ?_ hEta.2.2.2.2.1
    apply le_mul_of_one_le_left heta0.le
    nlinarith
  have hS : L.Sc ≤ L.sc.w'' D.R.n := le_trans (le_mul_of_one_le_left hS0.le hk1) hDel.2.2.2.1
  have hN : (D.R.N D.R.m : ℝ) ≤ (D.s.Del : ℝ) :=
    le_trans (le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ hm)) hDel.1
  refine ⟨?_, hDel.2.2.2.1, hEta.2.2.2.2.1, heta, hw, h4, by linarith, ?_, hw1, by linarith⟩
  · rw [L.Sc_eq]
    have := mul_le_mul_of_nonneg_left hN (le_trans zero_le_one hk1)
    linarith
  · exact le_trans (mul_le_mul_of_nonneg_right hk5 hb'0.le) h5b

theorem size_rel : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ((Fm.D x i).R.k : ℝ) * (Fm.D x i).R.N (Fm.D x i).R.m ≤ (Fm.L x i).Sc / 4 ∧ ((Fm.D x i).R.k : ℝ) * (Fm.L x i).Sc ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ ((Fm.D x i).R.m : ℝ) * (((Fm.D x i).R.t : ℝ) + 1) * (Fm.L x i).etaSz ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).etaSz ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).sc.w'' (Fm.D x i).R.n ≤ (Fm.L x i).sc.b' / (Fm.L x i).sc.x ∧ 4 ≤ (Fm.L x i).sc.x ∧ 2 * (Fm.L x i).sc.b' ≤ (Fm.L x i).sc.b ∧ ((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b' ≤ (Fm.L x i).sc.b ∧ 1 ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).etaSz + 1 + 3 * (Fm.L x i).Sc ≤ (Fm.L x i).sc.b := by
  intro eps Fm
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]
    exact (Fm.L 0 i).sc.eps_pos
  obtain ⟨x0, hx0⟩ := pow_six_le_exp he
  refine ⟨x0, fun x hx hx1 i => ?_⟩
  obtain ⟨h4, h6⟩ := hx0 x hx
  apply size_rel_at (Fm.L x i) (Fm.sizes x hx1 i)
  · rw [Fm.L_x x i hx1]; exact h4
  · unfold Scale.X'
    rw [Fm.L_x x i hx1, Fm.L_eps x i]; exact h6

end GlobalTheory.ShNums
end

section

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

theorem scale_one_lt_a (s : Scale) : 1 < s.a := by
  have hx : 1 < s.x := s.one_lt_alt
  have hL : 0 ≤ s.L := by
    unfold Scale.L
    exact Real.rpow_nonneg (by linarith) _
  have hb : 1 ≤ s.b := by
    unfold Scale.b
    exact Real.one_le_exp hL
  unfold Scale.a
  nlinarith

theorem family_one_lt_scale_a : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x →
    ∀ i : Fm.Ix x, 1 < (Fm.L x i).sc.a :=
  fun Fm => ⟨0, fun x _ _ i => scale_one_lt_a (Fm.L x i).sc⟩

end GlobalTheory
end
