module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle006
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle083
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.Res

open IsLocalRing

theorem exists_teich {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [Fintype (ResidueField O)] (x : O) :
    ∃ t : O, t ^ Fintype.card (ResidueField O) = t ∧ t - x ∈ maximalIdeal O := by
  have hq : 1 < Fintype.card (ResidueField O) := Fintype.one_lt_card
  obtain ⟨t, h1, h2⟩ := HenselianRing.is_henselian (I := maximalIdeal O)
    (Polynomial.X ^ Fintype.card (ResidueField O) - Polynomial.X)
    (Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hq)) x
    (by
      rw [← residue_eq_zero_iff]
      simp [FiniteField.pow_card])
    (by
      change IsUnit (residue O _)
      simp [Polynomial.derivative_X_pow, FiniteField.cast_card_eq_zero])
  exact ⟨t, by simpa [sub_eq_zero] using h1, h2⟩

theorem sol_mem_range {O F : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [Fintype (ResidueField O)] [Field F] (f : O →+* F) (hf : Function.Injective f) (y : F)
    (hy : y ^ Fintype.card (ResidueField O) = y) : ∃ t, f t = y := by
  classical
  have hq : 1 < Fintype.card (ResidueField O) := Fintype.one_lt_card
  have : ∀ r : ResidueField O, ∃ t : O, t ^ Fintype.card (ResidueField O) = t ∧ residue O t = r := fun r => by
    obtain ⟨x, rfl⟩ := residue_surjective r
    obtain ⟨t, h1, h2⟩ := exists_teich x
    exact ⟨t, h1, by rwa [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]⟩
  choose t h1 h2 using this
  have hinj : Function.Injective fun r => f (t r) := fun r s h => by
    rw [← h2 r, ← h2 s, hf h]
  set P : Polynomial F := Polynomial.X ^ Fintype.card (ResidueField O) - Polynomial.X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero hq
  have hd : P.natDegree = Fintype.card (ResidueField O) := Polynomial.natDegree_X_pow_sub_X (R := F) hq
  have hm : ∀ z : F, z ^ Fintype.card (ResidueField O) = z → z ∈ P.roots.toFinset := fun z hz => by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    simp [hP, hz]
  have hs : Finset.univ.image (fun r => f (t r)) = P.roots.toFinset := by
    refine Finset.eq_of_subset_of_card_le (fun z hz => ?_) ?_
    · obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hz
      exact hm _ (by rw [← map_pow, h1])
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← hd]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P)
  obtain ⟨r, -, hr⟩ := Finset.mem_image.1 (hs ▸ hm y hy)
  exact ⟨_, hr⟩

theorem exists_witt_residue : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∃ (a : ℕ) (_ : NeZero a) (w : Wq l a →ₐ[ℤ_[l]] ↥(OL K)), Kunr l a ≤ K.1 ∧ (∀ c, intToOC K (w c) = Per.θ l (wA l a c)) ∧ ∀ x : ↥(OL K), ∃ c, ¬ IsUnit (x - w c) := by
  intro l hl K
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hfin : Module.Finite ℤ_[l] ↥(OL K) := finite_OL K
  have hfin' : Module.Finite ℤ_[l] ↥(integralClosure ℤ_[l] ↥K.1) := hfin
  have hdvr : IsDiscreteValuationRing ↥(OL K) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr ℤ_[l] ℚ_[l] ↥K.1
  have hfa := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[l] ℚ_[l] ↥K.1
  have hloc : IsLocalHom (algebraMap ℤ_[l] ↥(OL K)) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[l] ↥K.1
  have hc : IsAdicComplete (maximalIdeal ↥(OL K)) ↥(OL K) :=
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[l] _
  have hF : Finite (ResidueField ↥(OL K)) :=
    ResidueField.finite_of_finite (R := ℤ_[l]) (Finite.of_equiv _ PadicInt.residueField.symm.toEquiv)
  have := Fintype.ofFinite (ResidueField ↥(OL K))
  have hch : CharP (ResidueField ↥(OL K)) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue ↥(OL K)), residue_eq_zero_iff, ← map_natCast (algebraMap ℤ_[l] ↥(OL K)),
      mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff, ← mem_nonunits_iff]
    exact PadicInt.p_nonunit
  obtain ⟨a, -, ha⟩ := FiniteField.card (ResidueField ↥(OL K)) l
  have hne : NeZero (a : ℕ) := ⟨a.ne_zero⟩
  let f : ↥(OL K) →+* Om l := K.1.val.toRingHom.comp (OL K).val.toRingHom
  have hf : Function.Injective f := fun _ _ h => Subtype.ext (Subtype.ext h)
  have hle : Kunr l a ≤ K.1 := IntermediateField.adjoin_le_iff.2 fun y hy => by
    obtain ⟨t, rfl⟩ := sol_mem_range f hf y (by rw [ha]; exact hy)
    exact (t : ↥K.1).2
  have : HasUnr a K := ⟨hle⟩
  refine ⟨a, hne, thetaW a K, hle, intToOC_thetaW a K, fun x => ?_⟩
  obtain ⟨t, h1, h2⟩ := exists_teich x
  rw [ha] at h1
  suffices ∃ c, thetaW a K c = t by
    obtain ⟨c, rfl⟩ := this
    exact ⟨c, fun h => h2 (by simpa using h.neg)⟩
  rcases eq_or_ne t 0 with rfl | h0
  · exact ⟨0, map_zero _⟩
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  have h3 := one_lt_pow_l l a
  have : NeZero (l ^ (a : ℕ) - 1) := ⟨by omega⟩
  obtain ⟨k, -, hk⟩ := hω.eq_pow_of_pow_eq_one (ξ := f t) (by
    rw [← map_pow, ← map_one f]
    congr 1
    exact mul_right_cancel₀ h0 (by rw [← pow_succ, Nat.sub_add_cancel h3.le, one_mul, h1]))
  refine ⟨WittVector.teichmuller l z ^ k, intToOC_injective K ?_⟩
  rw [intToOC_thetaW, map_pow, map_pow, wA_teich, WittVector.fontaineTheta_teichmuller]
  refine Subtype.ext ?_
  rw [SubmonoidClass.coe_pow, GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz]
  exact (map_pow (algebraMap (Om l) ℂ_[l]) ω k).symm.trans (congrArg _ hk)

end GlobalTheory.BSP.Res
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis : ∀ (A B : Type) [CommRing A] [CommRing B] (f : A →+* B) (M : Type) [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N), SemiBC u → ∀ (ι : Type) (e : Module.Basis ι A M), ∃ b : Module.Basis ι B N, ∀ i, b i = u (e i) := by
  first | exact @GlobalTheory.Prism.semiBC_basis | exact GlobalTheory.Prism.semiBC_basis | (intros; apply GlobalTheory.Prism.semiBC_basis <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isSemilinearBaseChange_iff_isBaseChange : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (M : Type) [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N] (u : M →ₛₗ[algebraMap A B] N) (u' : M →ₗ[A] N), (∀ x, u' x = u x) → (SemiBC u ↔ IsBaseChange B u') := by
  first | exact @GlobalTheory.BSP.semiBC_iff_isBaseChange | exact GlobalTheory.BSP.semiBC_iff_isBaseChange | (intros; apply GlobalTheory.BSP.semiBC_iff_isBaseChange <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.prime_not_mem_sq_and_delta_not_mem : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (m : Ideal A), m ≠ ⊤ → (l : A) ∈ m → (l : A) ∉ m ^ 2 ∧ D.δ (l : A) ∉ m := by
  first | exact @GlobalTheory.BSP.LSq.l_not_mem_sq | exact GlobalTheory.BSP.LSq.l_not_mem_sq | (intros; apply GlobalTheory.BSP.LSq.l_not_mem_sq <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem rootT_pow_eq_untilt (e : Per.Fl l) (n : ℕ) : rootT e n ^ (l ^ n) = e.untilt := by
  induction n generalizing e with
  | zero => simp [rootT]
  | succ n ih =>
    have h : rootT e (n + 1) = rootT ((frobeniusEquiv (Per.Fl l) l).symm e) n := by
      rw [rootT, rootT, Function.iterate_succ_apply]
    rw [h, pow_succ, pow_mul, ih, ← map_pow, frobeniusEquiv_symm_pow_p]

end GlobalTheory.MemLoc

namespace GlobalTheory.BSP

theorem rootT_flat_alg_and_fix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ n : ℕ, ∃ z : Om l, ((GlobalTheory.MemLoc.rootT bk.flat n : OC l) : ℂ_[l]) = (z : ℂ_[l])) ∧ ∀ (g : GQ l) (y : OCb l), (∀ n : ℕ, Per.σO g (GlobalTheory.MemLoc.rootT bk.flat n) = GlobalTheory.MemLoc.rootT y n) → Per.σF g bk.flat = y := by
  intro l _ K bk
  refine ⟨fun n => ?_, fun g y hy => ?_⟩
  · set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ X) with hr
    have h1 : (GlobalTheory.MemLoc.rootT bk.flat n) ^ (l ^ n) = intToOC K r := by
      rw [GlobalTheory.MemLoc.rootT_pow_eq_untilt, ← WittVector.fontaineTheta_teichmuller, ← bk.ev_X]
      exact bk.θ_ev r X (by rw [hr, RingEquiv.apply_symm_apply])
    set a : Om l := ((r : ↥K.1) : Om l)
    have hf : (Polynomial.X ^ (l ^ n) - Polynomial.C a : Polynomial (Om l)) ≠ 0 :=
      Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : l.Prime).pos n) a
    have hroot : ((Polynomial.X ^ (l ^ n) - Polynomial.C a : Polynomial (Om l)).map (algebraMap (Om l) ℂ_[l])).IsRoot
        ((GlobalTheory.MemLoc.rootT bk.flat n : OC l) : ℂ_[l]) := by
      have h2 := congrArg (fun x : OC l => (x : ℂ_[l])) h1
      rw [SubmonoidClass.coe_pow] at h2
      rw [coe_intToOC] at h2
      simp only [Polynomial.IsRoot, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      rw [h2]
      exact sub_self _
    obtain ⟨z, hz⟩ := (IsAlgClosed.splits _).mem_range_of_isRoot hf hroot
    exact ⟨z, hz.symm⟩
  · refine Perfection.ext fun n => ?_
    change PreTilt.coeff n (Per.σF g bk.flat) = PreTilt.coeff n y
    have hit : ∀ k : ℕ, ((frobeniusEquiv (Per.Fl l) l).symm)^[k] (Per.σF g bk.flat) =
        Per.σF g (((frobeniusEquiv (Per.Fl l) l).symm)^[k] bk.flat) := by
      intro k
      induction k with
      | zero => exact Eq.refl (Per.σF g bk.flat)
      | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, RingHom.map_frobeniusEquiv_symm]
    have hsig : GlobalTheory.MemLoc.rootT (Per.σF g bk.flat) n = Per.σO g (GlobalTheory.MemLoc.rootT bk.flat n) := by
      rw [GlobalTheory.MemLoc.rootT, GlobalTheory.MemLoc.rootT, hit, GlobalTheory.RingBasics.untilt_σF]
    rw [GlobalTheory.MemLoc.coeff_eq_mk_rootT, GlobalTheory.MemLoc.coeff_eq_mk_rootT, hsig, hy n]

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.AcrisDiscExt

theorem isUnit_natCast_of {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R] (f : ℤ_[l] →+* R)
    (hu : IsUnit (l : R)) (n : ℕ) (hn : n ≠ 0) : IsUnit (n : R) := by
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.out.ne_one
  have h : IsUnit (m : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hm
  have h' := h.map f
  rw [map_natCast] at h'
  rw [Nat.cast_mul, Nat.cast_pow]
  exact (hu.pow v).mul h'

theorem norm_l_disc_le (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) :
    ‖((l : ℕ) : Disc l u ρ)‖ ≤ (l : ℝ)⁻¹ := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have e : ((l : ℕ) : Disc l u ρ) = ofPre l u ρ (algebraMap A (PreDisc l u ρ) ((l : A) ^ 1 * u ^ 0) *
      IsLocalization.Away.invSelf (l : A) ^ 0) := by
    simp
  rw [e, norm_ofPre]
  refine gauge_le l u ρ (inv_pos.2 hl0) (Submodule.subset_span ⟨1, 0, 0, ?_, rfl⟩)
  rw [pow_zero, pow_zero, pow_one, one_mul, inv_mul_cancel₀ hl0.ne']

theorem norm_pow_mul_le (l : ℕ) [Fact l.Prime] {K : FinExt l} (bk : BK K) (w : bk.DA bk.ρ₀) (r : ℕ) :
    ‖((l : ℕ) : bk.DA bk.ρ₀) ^ r * w‖ ≤ (l : ℝ)⁻¹ ^ r * ‖w‖ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', mul_assoc, pow_succ', mul_assoc]
    exact (norm_mul_le _ _).trans (mul_le_mul (norm_l_disc_le l _ _) ih (norm_nonneg _) (by positivity))

theorem acris_disc_ext : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (γ γ' : Per.Acris l →+* bk.DA bk.ρ₀), (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = γ' (algebraMap (Ainf l) (Per.Acris l) a)) → (∀ x, ‖γ x‖ ≤ 1) → (∀ x, ‖γ' x‖ ≤ 1) → γ = γ' := by
  intro l hl K bk γ γ' h hγ hγ'

  have h0 : ∀ s : Per.Acris0 l,
      γ (algebraMap (Per.Acris0 l) (Per.Acris l) s) = γ' (algebraMap (Per.Acris0 l) (Per.Acris l) s) := by
    intro s
    obtain ⟨n, a, hn⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) (s : Per.AinfP l)
    have e : s * ((l : ℕ) : Per.Acris0 l) ^ n = algebraMap (Per.Ainf l) (Per.Acris0 l) a :=
      Subtype.ext (by simpa using hn)
    have e' := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) e
    rw [map_mul, map_pow, map_natCast, ← GlobalTheory.RingIface.tower l] at e'
    have e1 := congrArg γ e'
    have e2 := congrArg γ' e'
    rw [map_mul, map_pow, map_natCast] at e1 e2
    refine ((isUnit_l_disc l (bk.ev X) bk.ρ₀).pow n).mul_right_cancel ?_
    exact e1.trans ((h a).trans e2.symm)
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hl1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)
  ext x
  have hb : ∀ r : ℕ, ‖γ x - γ' x‖ ≤ 2 * (l : ℝ)⁻¹ ^ r := by
    intro r
    obtain ⟨s, z, rfl⟩ := (_root_.GlobalTheory.MemLoc.acris_basic l).2.2.1 x r
    have hs := h0 s
    rw [map_add (f := _), map_add (f := _), map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, hs, add_sub_add_left_eq_sub,
      ← mul_sub]
    have hw : ‖γ z - γ' z‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [hγ z, hγ' z])
    refine (norm_pow_mul_le l bk (γ z - γ' z) r).trans ?_
    exact mul_comm ((l : ℝ)⁻¹ ^ r) _ ▸ mul_le_mul_of_nonneg_left hw (by positivity)
  have ht : Filter.Tendsto (fun r : ℕ => 2 * (l : ℝ)⁻¹ ^ r) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hl1).const_mul 2
  have hz : ‖γ x - γ' x‖ ≤ 0 := ge_of_tendsto' ht hb
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hz)

end GlobalTheory.AcrisDiscExt
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

variable {l : ℕ} [hl : Fact l.Prime]

theorem BK.X_pow_natDegree_mem {K : FinExt l} (bk : BK K) :
    (X : bk.S) ^ bk.Ep.natDegree ∈ Ideal.span {(l : bk.S)} ⊔ Ideal.span {bk.E} := by
  have h := congrArg (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) bk.monic.as_sum

  simp only [map_add (f := _), map_sum, map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
  Polynomial.coe_C, Polynomial.coe_X] at h
  have hs : ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * (X : bk.S) ^ i ∈
      Ideal.span {(l : bk.S)} := by
    refine Ideal.sum_mem _ fun i hi => ?_
    obtain ⟨c, hc⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
    rw [hc, map_mul, map_natCast, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have e : (X : bk.S) ^ bk.Ep.natDegree =
      bk.E - ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * (X : bk.S) ^ i := by
    rw [BK.E, h]; ring
  rw [e]
  exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left hs)



theorem BK.hom_eq_of_X_C {K : FinExt l} (bk : BK K) {B : Obj l ↥(OL K)} (f g : Hom bk.prism B)
    (hX : BK.hf f X = BK.hf g X) (hC : ∀ w, BK.hf f (C w) = BK.hf g (C w)) : f = g := by
  have hpoly : ∀ p : Polynomial (Wq l bk.a), BK.hf f (p : bk.S) = BK.hf g (p : bk.S) := by
    have e : (BK.hf f).comp (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) =
        (BK.hf g).comp Polynomial.coeToPowerSeries.ringHom :=
      Polynomial.ringHom_ext (fun a => by simpa using hC a) (by simpa using hX)
    exact fun p => RingHom.congr_fun e p
  have hle : Ideal.span {(l : bk.S)} ⊔ Ideal.span {bk.E} ≤
      (Ideal.span {(l : B.A)} ⊔ B.I).comap (BK.hf f) := by
    refine sup_le ?_ ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      rw [SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_sup_right (f.f_I _ (Ideal.mem_span_singleton_self _))
  have hXe : BK.hf f X ^ bk.Ep.natDegree ∈ Ideal.span {(l : B.A)} ⊔ B.I := by
    rw [← map_pow]; exact hle bk.X_pow_natDegree_mem
  refine Hom.ext' (RingHom.ext fun (s : bk.S) => ?_)
  show BK.hf f s = BK.hf g s
  haveI : IsAdicComplete (Ideal.span {(l : B.A)} ⊔ B.I) B.A := B.complete
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(l : B.A)} ⊔ B.I) B.A) _ fun n => ?_
  rw [SModEq.zero]
  obtain ⟨r, hr⟩ : (X : bk.S) ^ (bk.Ep.natDegree * n) ∣ s - (trunc (bk.Ep.natDegree * n) s : bk.S) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp [Polynomial.coeff_coe, coeff_trunc, hm]
  have e : s = (trunc (bk.Ep.natDegree * n) s : bk.S) + X ^ (bk.Ep.natDegree * n) * r := by
    rw [← hr]; ring
  have hd : BK.hf f s - BK.hf g s = BK.hf f X ^ (bk.Ep.natDegree * n) * (BK.hf f r - BK.hf g r) := by
    rw [e]
    simp only [map_add (f := _), map_mul, map_pow]
    rw [hpoly (trunc (bk.Ep.natDegree * n) s), ← hX]; ring
  have h2 : BK.hf f X ^ (bk.Ep.natDegree * n) * (BK.hf f r - BK.hf g r) ∈
      (Ideal.span {(l : B.A)} ⊔ B.I) ^ n := by
    rw [pow_mul]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hXe n)
  have h3 : BK.hf f s - BK.hf g s ∈ (Ideal.span {(l : B.A)} ⊔ B.I) ^ n := by rw [hd]; exact h2
  rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact h3

theorem BK.galHom_comp_ι_of_fixFlat {K : FinExt l} (bk : BK K) (g : ↥(GK K)) (hg : bk.FixFlat g) :
    (ainfHom K g).comp bk.ι = bk.ι := by
  refine BK.hom_eq_of_X_C bk _ _ ?_ ?_
  · change Per.σA (g : GQ l) (bk.ev X) = bk.ev X
    rw [bk.ev_X]
    exact (GlobalTheory.RingIface.sigA_teich l _ _).trans (congrArg _ hg)
  · intro w
    change Per.σA (g : GQ l) (bk.ev (C w)) = bk.ev (C w)
    rw [bk.ev_C, bk.gal_w]

theorem MReal.gal_of_fixFlat {K : FinExt l} {bk : BK K} {d : ℕ} {S : Strat bk d}
    {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} {T : Matrix (Fin d) (Fin d) (WCb l)} (h : MReal S ρ T)
    (g : ↥(GK K)) (hg : bk.FixFlat g) : zW (ρ g) * T.map (galW l (g : GQ l)) = T := by
  have e := h.gal g
  rw [BK.galHom_comp_ι_of_fixFlat bk g hg, S.ε_refl] at e
  exact e.trans ((congrArg (T * ·) (Matrix.map_one (inclW l) (map_zero _) (map_one _))).trans (Matrix.mul_one T))

theorem MReal.exists_fixed_frob : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d)
    (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l])
    (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l))
    (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' →
    ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) →
    ∃ X : Matrix (Fin d') (Fin d) (WCb l), T' * X = zW f * T ∧
      (∀ g : ↥(GK K), bk.FixFlat g → X.map (galW l (g : GQ l)) = X) ∧
      bk.evW bk.E ^ S.a • (S'.A.map bk.evW * X.map (frobW l)) = bk.evW bk.E ^ S'.a • (X * S.A.map bk.evW) := by
  intro l _ K bk d d' S S' ρ ρ' T T' hT hT' f hf
  obtain ⟨u, hu⟩ := hT'.unit
  have cancel : ∀ M N : Matrix (Fin d') (Fin d) (WCb l), T' * M = T' * N → M = N := by
    intro M N h
    have h2 := congrArg (fun Z => (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * Z) h
    simp only [← hu, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h2
    exact h2
  have hzmul : ∀ {m n o : Type} [Fintype n] (A : Matrix m n ℤ_[l]) (B : Matrix n o ℤ_[l]),
      zW (A * B) = zW A * zW B := fun A B => Matrix.map_mul
  set Xm : Matrix (Fin d') (Fin d) (WCb l) := (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * (zW f * T) with hXm
  have hX : T' * Xm = zW f * T := by
    rw [hXm, ← hu, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  refine ⟨Xm, hX, fun g hg => ?_, ?_⟩
  · let G : WCb l →+* WCb l := (galW l (g : GQ l)).toRingEquiv.toRingHom
    have hzG : ∀ {m n : Type} (M : Matrix m n ℤ_[l]), (zW M).map G = zW M :=
      fun M => Matrix.ext fun i j => (galW l (g : GQ l)).commutes _
    have a1 : zW (ρ' g) * T'.map G = T' := hT'.gal_of_fixFlat g hg
    have a2 : zW (ρ g) * T.map G = T := hT.gal_of_fixFlat g hg
    change Xm.map G = Xm
    apply cancel
    have h1 := congrArg (fun M => M.map G) hX
    simp only [Matrix.map_mul, hzG] at h1
    calc T' * Xm.map G = zW (ρ' g) * (T'.map G * Xm.map G) := by
          rw [← Matrix.mul_assoc, a1]
      _ = zW (ρ' g * f) * T.map G := by rw [h1, hzmul, Matrix.mul_assoc]
      _ = zW f * (zW (ρ g) * T.map G) := by rw [← hf g, hzmul, Matrix.mul_assoc]
      _ = T' * Xm := by rw [a2, hX]
  · let F : WCb l →+* WCb l := (frobW l).toRingHom
    have hzF : ∀ {m n : Type} (M : Matrix m n ℤ_[l]), (zW M).map F = zW M :=
      fun M => Matrix.ext fun i j => (frobW l).commutes _
    have b1 : bk.evW bk.E ^ S.a • T.map F = T * S.A.map bk.evW := hT.φ
    have b2 : bk.evW bk.E ^ S'.a • T'.map F = T' * S'.A.map bk.evW := hT'.φ
    change bk.evW bk.E ^ S.a • (S'.A.map bk.evW * Xm.map F) = bk.evW bk.E ^ S'.a • (Xm * S.A.map bk.evW)
    apply cancel
    have h1 := congrArg (fun M => M.map F) hX
    simp only [Matrix.map_mul, hzF] at h1
    rw [Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, ← b2, Matrix.smul_mul, h1, smul_smul,
      ← Matrix.mul_assoc, hX, Matrix.mul_assoc, ← b1, Matrix.mul_smul, smul_smul, mul_comm]

end GlobalTheory.BSP
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem hf_X_δ_and_str : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K)
    (C : Obj l ↥(OL K)) (g : Hom bk.prism C),
    C.D.δ (BK.hf (bk := bk) g X) = 0 ∧
      Ideal.Quotient.mk C.I (BK.hf (bk := bk) g X) = C.str (bk.str.symm (Ideal.Quotient.mk _ X)) := by
  intro l _ K bk C g
  have hδX : (deltaS l bk.a).δ (X : (Wq l bk.a)⟦X⟧) = 0 := by
    have h := (deltaS l bk.a).φ_eq (X : (Wq l bk.a)⟦X⟧)
    have h2 : (deltaS l bk.a).φ (X : (Wq l bk.a)⟦X⟧) = X ^ l := frobS_X l bk.a
    rw [h2] at h
    have h3 : (l : (Wq l bk.a)⟦X⟧) * (deltaS l bk.a).δ X = 0 := by linear_combination -h
    exact (mul_eq_zero.1 h3).resolve_left (l_ne_zero l bk.a)
  refine ⟨?_, ?_⟩
  · have h := g.f_δ (X : (Wq l bk.a)⟦X⟧)
    change C.D.δ (g.f X) = 0
    rw [← h]
    change g.f ((deltaS l bk.a).δ X) = 0
    rw [hδX]
    exact g.f.map_zero
  · refine g.f_str (bk.str.symm (Ideal.Quotient.mk _ X)) X ?_
    change Ideal.Quotient.mk (Ideal.span {bk.E}) X = bk.str (bk.str.symm (Ideal.Quotient.mk _ X))
    rw [RingEquiv.apply_symm_apply]

end GlobalTheory.BSP
end
end
