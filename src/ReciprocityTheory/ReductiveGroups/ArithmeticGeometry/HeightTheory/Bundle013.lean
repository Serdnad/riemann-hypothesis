module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def fDivE (hd : d.AxH 𝒜) (h : d.S1) : KTf K d.D d.N :=
  ∏ c, ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nP h c d.wF (hd.a4.choose c) p

noncomputable def omE (hd : d.AxH 𝒜) (h : d.S1) : KTf K d.D d.N := d.De hd h * d.fDivE hd h ^ 2

def IsPres (hd : d.AxH 𝒜) (h : d.S1) (a b : KTp K d.D d.N) : Prop :=
  b ≠ 0 ∧ algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a =
    d.De hd h * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b ∧
  ∃ m : Fin (d.D + 1) → ℕ, m 0 = 0 ∧ ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m a ∧
    ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m b

noncomputable def mSgP (sg : K →+* ℂ) (a b : KTp K d.D d.N) : ℝ :=
  ∫ z, (Real.log ‖d.evT sg 0 (d.tOf z) a‖ - Real.log ‖d.evT sg 0 (d.tOf z) b‖)
    ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open Matrix NumberField ComplexConjugate NumberField.ComplexEmbedding
open scoped ComplexOrder

section Real

variable {K : Type} [Field K] [NumberField K] {r k : ℕ}

abbrev hIdx (K : Type) [Field K] [NumberField K] (r : ℕ) : Type := (K →+* ℂ) × Fin r × Fin 2

noncomputable def hReF (x : (K →+* ℂ) → Fin r → ℂ) : hIdx K r → ℝ :=
  fun p => if p.2.2 = 0 then (x p.1 p.2.1).re else (x p.1 p.2.1).im

noncomputable def hRe (x : (K →+* ℂ) → Fin r → ℂ) : EuclideanSpace ℝ (hIdx K r) :=
  WithLp.toLp 2 (hReF x)

theorem realCoordsFun_add (x y : (K →+* ℂ) → Fin r → ℂ) : hReF (x + y) = hReF x + hReF y := by
  funext p
  simp only [hReF, Pi.add_apply]
  split_ifs <;> simp

theorem inner_hRe (x y : (K →+* ℂ) → Fin r → ℂ) :
    inner ℝ (hRe x) (hRe y) = (∑ σ, star (x σ) ⬝ᵥ y σ).re := by
  simp only [hRe, PiLp.inner_apply, PiLp.toLp_apply, RCLike.inner_apply, conj_trivial,
    Fintype.sum_prod_type, Fin.sum_univ_two, Complex.re_sum, dotProduct, Pi.star_apply,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, hReF]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun l _ => ?_
  simp
  ring

theorem star_dotProduct_self_re {r : ℕ} (v : Fin r → ℂ) : (star v ⬝ᵥ v).re = hns v := by
  simp only [dotProduct, Complex.re_sum, hns, Pi.star_apply, Complex.star_def]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem norm_realCoords_sq (x : (K →+* ℂ) → Fin r → ℂ) : ‖hRe x‖ ^ 2 = ∑ σ, hns (x σ) := by
  rw [← real_inner_self_eq_norm_sq, inner_hRe, Complex.re_sum]
  exact Finset.sum_congr rfl fun σ _ => star_dotProduct_self_re _

noncomputable def hpv (b : Fin k → Fin r → K) (q : Fin r → K) : EuclideanSpace ℝ (hIdx K r) :=
  hRe fun σ => hPm σ b *ᵥ fun l => σ (q l)

theorem projectedVector_add (b : Fin k → Fin r → K) (q q' : Fin r → K) :
    hpv b (q + q') = hpv b q + hpv b q' := by
  have e : (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ ((q + q') l)) =
      (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q l)) +
        (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q' l)) := by
    funext σ
    rw [Pi.add_apply, ← mulVec_add]
    congr 1
    funext l
    simp [map_add]
  simp only [hpv, hRe, e, realCoordsFun_add, WithLp.toLp_add]

theorem projectedVector_zero (b : Fin k → Fin r → K) : hpv b 0 = 0 := by
  have e : hReF (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ ((0 : Fin r → K) l)) = 0 := by
    funext p
    simp only [hReF, Pi.zero_apply, map_zero]
    rw [show (fun _ : Fin r => (0 : ℂ)) = 0 from rfl, mulVec_zero]
    split_ifs <;> simp
  simp only [hpv, hRe, e, WithLp.toLp_zero]

noncomputable def hpvHom (b : Fin k → Fin r → K) : (Fin r → K) →+ EuclideanSpace ℝ (hIdx K r) where
  toFun := hpv b
  map_zero' := projectedVector_zero b
  map_add' := projectedVector_add b

theorem normSqSum_pos {r : ℕ} {v : Fin r → ℂ} (hv : v ≠ 0) : 0 < hns v := by
  obtain ⟨l, hl⟩ := Function.ne_iff.mp hv
  have h1 : 0 < ‖v l‖ ^ 2 := by
    exact pow_pos (norm_pos_iff.mpr hl) 2
  exact lt_of_lt_of_le h1
    (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ l))

theorem projectedVector_eq_zero_iff {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (q : Fin r → K) : hpv b q = 0 ↔ q ∈ Submodule.span K (Set.range b) := by
  constructor
  · intro h0
    by_contra hq
    have hpos : Fintype.card (K →+* ℂ) ≠ 0 := by
      rw [NumberField.Embeddings.card K ℂ]; exact Module.finrank_pos.ne'
    obtain ⟨σ0⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hpos)
    have h1 := norm_realCoords_sq (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q l))
    rw [← hpv, h0, norm_zero] at h1
    have h2 : 0 < ∑ σ, hns (hPm σ b *ᵥ fun l => σ (q l)) :=
      lt_of_lt_of_le (normSqSum_pos (orthogonalProjector_mulVec_ne_zero σ0 hb hq))
        (Finset.single_le_sum (f := fun σ => hns (hPm σ b *ᵥ fun l => σ (q l)))
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ σ0))
    rw [← h1] at h2
    norm_num at h2
  · intro hq
    have e : (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q l)) = 0 := by
      funext σ
      exact orthogonalProjector_mulVec_eq_zero σ hb hq
    have e2 : hReF (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q l)) = 0 := by
      rw [e]; funext p; simp [hReF]
    simp only [hpv, hRe, e2, WithLp.toLp_zero]

theorem orthogonalProjector_mulVec_smul (σ : K →+* ℂ) (b : Fin k → Fin r → K) (a : K) (x : Fin r → K) :
    (hPm σ b *ᵥ fun l => σ ((a • x) l)) = σ a • (hPm σ b *ᵥ fun l => σ (x l)) := by
  rw [← mulVec_smul]
  congr 1
  funext l
  simp [map_smul]

theorem inner_projectedVector_smul (b : Fin k → Fin r → K) (a a' : K) (x y : Fin r → K) :
    inner ℝ (hpv b (a • x)) (hpv b (a' • y)) =
      (∑ σ : K →+* ℂ, conj (σ a) * σ a' *
        (star (hPm σ b *ᵥ fun l => σ (x l)) ⬝ᵥ (hPm σ b *ᵥ fun l => σ (y l)))).re := by
  rw [hpv, hpv, inner_hRe]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [orthogonalProjector_mulVec_smul, orthogonalProjector_mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, Complex.star_def]
  ring

end Real

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution

open MvPolynomial

variable {K : Type} [Field K] {D N : ℕ}

abbrev V (D N : ℕ) : Type := (Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)

noncomputable def ev1 : MvPolynomial (V D N) K →ₐ[K] MvPolynomial (V D N) K :=
  aeval fun v => if v = Sum.inr 0 then 1 else X v

noncomputable def thetaS (sgn : K) : MvPolynomial (V D N) K →ₐ[K] MvPolynomial (V D N) K :=
  aeval fun v => match v with
    | Sum.inl (a, j) => if a = 0 then X (Sum.inl (a, j))
        else X (Sum.inl (a, j)) + C sgn * X (Sum.inr a) * X (Sum.inl (0, j))
    | Sum.inr i => X (Sum.inr i)

private theorem thetaS_X_inr (sgn : K) (i : Fin (D + 2)) :
    thetaS (D := D) (N := N) sgn (X (Sum.inr i)) = X (Sum.inr i) := by
  simp [thetaS]

private theorem thetaS_X_inl_zero (sgn : K) (j : Fin (N + 1)) :
    thetaS (D := D) (N := N) sgn (X (Sum.inl (0, j))) = X (Sum.inl (0, j)) := by
  simp [thetaS]

private theorem thetaS_X_inl_of_ne_zero (sgn : K) {a : Fin (D + 2)} (ha : a ≠ 0) (j : Fin (N + 1)) :
    thetaS (D := D) (N := N) sgn (X (Sum.inl (a, j))) =
      X (Sum.inl (a, j)) + C sgn * X (Sum.inr a) * X (Sum.inl (0, j)) := by
  simp [thetaS, ha]

theorem thetaS_comp (s t : K) (hst : s + t = 0) :
    (thetaS (D := D) (N := N) s).comp (thetaS t) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  rintro (⟨a, j⟩ | i)
  · by_cases ha : a = 0
    · subst ha
      simp only [AlgHom.comp_apply, AlgHom.id_apply, thetaS_X_inl_zero]
    · have hC : (C s + C t : MvPolynomial (V D N) K) = 0 := by
        rw [← C_add, hst, C_0]
      simp only [AlgHom.comp_apply, AlgHom.id_apply, thetaS_X_inl_of_ne_zero _ ha, map_add (f := _), map_mul,
        thetaS_X_inr, thetaS_X_inl_zero, algHom_C, algebraMap_eq]
      linear_combination
        (X (Sum.inr a) * X (Sum.inl (0, j)) : MvPolynomial (V D N) K) * hC
  · simp only [AlgHom.comp_apply, AlgHom.id_apply, thetaS_X_inr]

noncomputable def theta : MvPolynomial (V D N) K ≃ₐ[K] MvPolynomial (V D N) K :=
  AlgEquiv.ofAlgHom (thetaS (-1)) (thetaS 1) (thetaS_comp _ _ (by ring)) (thetaS_comp _ _ (by ring))

def iota (p : TVar D N) : V D N := Sum.inl (p.1.succ, p.2)

theorem iota_injective : Function.Injective (iota (D := D) (N := N)) := by
  rintro ⟨a, j⟩ ⟨b, k⟩ h
  simp only [iota, Sum.inl.injEq, Prod.mk.injEq, Fin.succ_inj] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

private theorem ev1_X_inr_zero :
    ev1 (K := K) (D := D) (N := N) (X (Sum.inr 0)) = 1 := by
  simp [ev1]

private theorem ev1_X_of_ne_inr_zero {v : V D N} (hv : v ≠ Sum.inr 0) :
    ev1 (K := K) (X v) = X v := by
  simp [ev1, hv]

theorem evalOne_bilinearSubstitution (F : KTp K D N) : ev1 (bilinearSubstitution F) = theta (rename iota F) := by
  have key : (ev1 (K := K) (D := D) (N := N)).comp
      (aeval fun t : ReciprocityTheory.ChartRestriction.G.T0.TVar D N =>
        (X (Sum.inr 0) * X (Sum.inl (t.1.succ, t.2)) - X (Sum.inr t.1.succ) * X (Sum.inl (0, t.2)) :
          MvPolynomial (V D N) K)) =
      (thetaS (-1)).comp (rename iota) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, j⟩
    have h1 : (Sum.inl (a.succ, j) : V D N) ≠ Sum.inr 0 := Sum.inl_ne_inr
    have h2 : (Sum.inr a.succ : V D N) ≠ Sum.inr 0 :=
      fun h => Fin.succ_ne_zero a (Sum.inr_injective h)
    have h3 : (Sum.inl (0, j) : V D N) ≠ Sum.inr 0 := Sum.inl_ne_inr
    simp only [AlgHom.comp_apply, aeval_X, map_sub, map_mul, ev1_X_inr_zero, ev1_X_of_ne_inr_zero h1,
      ev1_X_of_ne_inr_zero h2, ev1_X_of_ne_inr_zero h3, rename_X, iota,
      thetaS_X_inl_of_ne_zero _ (Fin.succ_ne_zero a), map_neg, map_one]
    ring
  exact DFunLike.congr_fun key F

private theorem irreducible_rename_of_injective_height {α β : Type} [Fintype α] {f : α → β}
    (hf : Function.Injective f) {F : MvPolynomial α K} (hF : Irreducible F) :
    Irreducible (rename f F) := by
  have hP : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.mp hF
  have h1 : rename f F = rename ((↑) : Set.range f → β) (renameEquiv K (Equiv.ofInjective f hf) F) := by
    rw [renameEquiv_apply, rename_rename]
    congr 1
  have h2 : Prime (renameEquiv K (Equiv.ofInjective f hf) F) := (MulEquiv.prime_iff _).mpr hP
  rw [h1]
  exact ((prime_rename_iff (Set.range f)).mpr h2).irreducible

theorem irreducible_theta_rename (F : KTp K D N) (hF : Irreducible F) :
    Irreducible (theta (rename (iota (D := D) (N := N)) F)) :=
  (MulEquiv.irreducible_iff (theta (K := K) (D := D) (N := N))).mpr
    (irreducible_rename_of_injective_height iota_injective hF)

end ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def translatedForm (x : Fin (d.N + 1) → K) (F : KTp K d.D d.N) : KTp K d.D d.N :=
  MvPolynomial.aeval (fun v : TVar d.D d.N =>
    if v.1 = 0 then MvPolynomial.C (x v.2) else MvPolynomial.X v) F

noncomputable def localHeightAtPrime (h : d.S1) (f : ∀ c, A c) (c : ι)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
    (d.fze h c w : ℝ) * (d.ordMM c (d.Wres c w) (f c) : ℝ)

noncomputable def localHeightAtEmbedding (f : ∀ c, A c) (c : ι) (sg : K →+* ℂ) : ℝ :=
  ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
    -Real.log (d.nrm c d.wL (f c) P / d.be c P)) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))

def heightSubstitutionCondition (h : d.S1) (x : Fin (d.N + 1) → K) (c : ι) (F : KTp K d.D d.N) (κ : K) : Prop :=
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F * algebraMap K (KTf K d.D d.N) κ *
      Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)
        (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c))) =
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.translatedForm x F) *
      Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)

theorem ratio_eq_of_eq_smul_field {Ω' V : Type*} [Field Ω'] [AddCommGroup V] [Module Ω' V] {f g : V}
    (hg : g ≠ 0) {a : Ω'} (hf : f = a • g) : ratio (Ω := Ω') f g = a := by
  classical
  have h : ∃ b : Ω', f = b • g := ⟨a, hf⟩
  unfold ratio
  rw [dite_eq_left h]
  exact smul_left_injective Ω' hg (h.choose_spec.symm.trans hf)

theorem eq_ratio_base_smul (hd : d.AxH 𝒜) (c : ι) {f : A c} (hf : f ∈ 𝒜 c d.wL) :
    f = ratio (Ω := Ω c) f (d.w (d.jc c) c) • d.w (d.jc c) c := by
  have hw := hd.w_mem (d.jc c) c
  have hw0 := hd.w_base c
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨_, hw⟩ : 𝒜 c d.wL)
    (by simpa using hw0)).1 (hd.finrank_one c d.wL) ⟨f, hf⟩
  have hfa : f = a • d.w (d.jc c) c := by
    have h1 := congrArg Subtype.val ha
    simp only [SetLike.val_smul] at h1
    exact h1.symm
  rw [ratio_eq_of_eq_smul_field hw0 hfa]
  exact hfa

theorem ratio_base_ne_zero (hd : d.AxH 𝒜) (c : ι) {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    ratio (Ω := Ω c) f (d.w (d.jc c) c) ≠ 0 := by
  intro h0
  apply hf0
  rw [d.eq_ratio_base_smul hd c hf, h0, zero_smul]

theorem linearCombination_mem_section (hd : d.AxH 𝒜) (x : Fin (d.N + 1) → K) (c : ι) : d.wx x c ∈ 𝒜 c d.wL := by
  haveI := hd.tower c
  unfold wx
  rw [Finset.sum_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Pi.smul_apply, ← algebraMap_smul (Ω c) (x j)]
  exact Submodule.smul_mem _ _ (hd.w_mem j c)

theorem ord_eq_valuation_ratio_base_add (hd : d.AxH 𝒜) (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) (hv : d.admitted c v)
    {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    ((d.ord c v d.wL f : ℤ) : WithTop ℤ) =
      v (ratio (Ω := Ω c) f (d.w (d.jc c) c)) + (d.ord c v d.wL (d.w (d.jc c) c) : WithTop ℤ) := by
  have hfa := d.eq_ratio_base_smul hd c hf
  have ha := d.ratio_base_ne_zero hd c hf hf0
  conv_lhs => rw [hfa]
  exact hd.ord_smul c v hv _ (hd.w_mem _ c) (hd.w_base c) ha

theorem eq_ratio_smul_of_mem (hd : d.AxH 𝒜) (c : ι) {f g : A c} (hf : f ∈ 𝒜 c d.wL) (hg : g ∈ 𝒜 c d.wL)
    (hg0 : g ≠ 0) : f = ratio (Ω := Ω c) f g • g := by
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨_, hg⟩ : 𝒜 c d.wL)
    (by simpa using hg0)).1 (hd.finrank_one c d.wL) ⟨f, hf⟩
  have hfa : f = a • g := by
    have h1 := congrArg Subtype.val ha
    simp only [SetLike.val_smul] at h1
    exact h1.symm
  rw [ratio_eq_of_eq_smul_field hg0 hfa]
  exact hfa

theorem ratio_ne_zero_of_ne_zero (hd : d.AxH 𝒜) (c : ι) {f g : A c} (hf : f ∈ 𝒜 c d.wL) (hg : g ∈ 𝒜 c d.wL)
    (hg0 : g ≠ 0) (hf0 : f ≠ 0) : ratio (Ω := Ω c) f g ≠ 0 := by
  intro h0
  apply hf0
  rw [d.eq_ratio_smul_of_mem hd c hf hg hg0, h0, zero_smul]

theorem ord_eq_valuation_ratio_add (hd : d.AxH 𝒜) (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) (hv : d.admitted c v)
    {f g : A c} (hf : f ∈ 𝒜 c d.wL) (hg : g ∈ 𝒜 c d.wL) (hg0 : g ≠ 0) (hf0 : f ≠ 0) :
    ((d.ord c v d.wL f : ℤ) : WithTop ℤ) =
      v (ratio (Ω := Ω c) f g) + (d.ord c v d.wL g : WithTop ℤ) := by
  have hfa := d.eq_ratio_smul_of_mem hd c hf hg hg0
  have ha := d.ratio_ne_zero_of_ne_zero hd c hf hg hg0 hf0
  conv_lhs => rw [hfa]
  exact hd.ord_smul c v hv _ hg hg0 ha

theorem ratio_mul_ratio_height (hd : d.AxH 𝒜) (c : ι) {f g e : A c} (hf : f ∈ 𝒜 c d.wL)
    (hg : g ∈ 𝒜 c d.wL) (he : e ∈ 𝒜 c d.wL) (hg0 : g ≠ 0) (he0 : e ≠ 0) :
    ratio (Ω := Ω c) f e = ratio (Ω := Ω c) f g * ratio (Ω := Ω c) g e := by
  have h1 := d.eq_ratio_smul_of_mem hd c hf hg hg0
  have h2 := d.eq_ratio_smul_of_mem hd c hg he he0
  apply ratio_eq_of_eq_smul_field he0
  rw [mul_smul, ← h2, ← h1]

theorem coe_untopD_of_ne_top {v : WithTop ℤ} (hv : v ≠ ⊤) : ((v.untopD 0 : ℤ) : WithTop ℤ) = v := by
  obtain ⟨x, rfl⟩ := WithTop.ne_top_iff_exists.1 hv
  rw [WithTop.untopD_coe]

theorem ordMinMax_eq_ratio_untop_sub (hd : d.AxH 𝒜) (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) (hv : d.admitted c v)
    (j0 : Fin (d.N + 1)) (hj0 : d.w j0 c ≠ 0)
    (hint : ∀ j, 0 ≤ v (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)))
    {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.ordMM c v f = (v (ratio (Ω := Ω c) f (d.w (d.jc c) c))).untopD 0 -
      (v (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c))).untopD 0 := by
  have key : ∀ {g : A c}, g ∈ 𝒜 c d.wL → g ≠ 0 → d.ord c v d.wL g =
      (v (ratio (Ω := Ω c) g (d.w (d.jc c) c))).untopD 0 + d.ord c v d.wL (d.w (d.jc c) c) := by
    intro g hg hg0
    have h := d.ord_eq_valuation_ratio_base_add hd c v hv hg hg0
    have hne : v (ratio (Ω := Ω c) g (d.w (d.jc c) c)) ≠ ⊤ := by
      rw [Ne, AddValuation.top_iff]
      exact d.ratio_base_ne_zero hd c hg hg0
    rw [← coe_untopD_of_ne_top hne, ← WithTop.coe_add] at h
    exact WithTop.coe_inj.1 h
  have hinf : (⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c)) = d.ord c v d.wL (d.w j0 c) := by
    apply le_antisymm
    · exact ciInf_le (Set.finite_range _).bddBelow (⟨j0, hj0⟩ : {j // d.w j c ≠ 0})
    · haveI : Nonempty {j // d.w j c ≠ 0} := ⟨⟨j0, hj0⟩⟩
      refine le_ciInf fun j => ?_
      have h := d.ord_eq_valuation_ratio_add hd c v hv (hd.w_mem j.1 c) (hd.w_mem j0 c) hj0 j.2
      have hnn := hint j.1
      have hne : v (ratio (Ω := Ω c) (d.w j.1 c) (d.w j0 c)) ≠ ⊤ := by
        rw [Ne, AddValuation.top_iff]
        exact d.ratio_ne_zero_of_ne_zero hd c (hd.w_mem j.1 c) (hd.w_mem j0 c) hj0 j.2
      rw [← coe_untopD_of_ne_top hne, ← WithTop.coe_add] at h
      have h' := WithTop.coe_inj.1 h
      rw [← coe_untopD_of_ne_top hne] at hnn
      have h0 : 0 ≤ (v (ratio (Ω := Ω c) (d.w j.1 c) (d.w j0 c))).untopD 0 := by exact_mod_cast hnn
      omega
  unfold ordMM
  rw [hinf, key hf hf0, key (hd.w_mem j0 c) hj0]
  ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
