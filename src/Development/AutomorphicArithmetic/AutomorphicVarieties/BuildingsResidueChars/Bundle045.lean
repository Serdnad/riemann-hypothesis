module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfWdMkPhiDPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

theorem UpperTheory.weilDeligne_monodromy_upperTriangular :
    UpperTheory.V.Af.Wd.TriMono := by
  intro k W Γ _ _ _ n N ρ c μ hcomm hT hN
  obtain ⟨b, hb⟩ := hT
  set B := LinearMap.toMatrix b b N with hBdef
  have hAlow : ∀ σ (i j : Fin n), j < i → LinearMap.toMatrix b b (ρ σ) i j = 0 := fun σ => (hb (some σ)).1
  have hAdiag : ∀ σ (i : Fin n), LinearMap.toMatrix b b (ρ σ) i i = μ σ i := fun σ => (hb (some σ)).2
  have hB0 : B ≠ 0 := by
    intro h
    apply hN
    apply (LinearMap.toMatrix b b).injective
    rw [← hBdef, h, map_zero]
  have hex : ∃ i j, B i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hB0 (Matrix.ext h)
  classical
  have hJ : (Finset.univ.filter fun j => ∃ i, B i j ≠ 0).Nonempty := by
    obtain ⟨i, j, h⟩ := hex
    exact ⟨j, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨i, h⟩⟩
  set j := (Finset.univ.filter fun j => ∃ i, B i j ≠ 0).min' hJ with hjdef
  have hjmem := Finset.min'_mem _ hJ
  rw [← hjdef] at hjmem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjmem
  have hjmin : ∀ i l, l < j → B i l = 0 := by
    intro i l hl
    by_contra h
    have : j ≤ l := Finset.min'_le _ l (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨i, h⟩)
    exact absurd hl (not_lt.mpr this)
  have hI : (Finset.univ.filter fun i => B i j ≠ 0).Nonempty := by
    obtain ⟨i, h⟩ := hjmem
    exact ⟨i, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h⟩
  set i := (Finset.univ.filter fun i => B i j ≠ 0).max' hI with hidef
  have himem := Finset.max'_mem _ hI
  rw [← hidef] at himem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at himem
  have himax : ∀ l, i < l → B l j = 0 := by
    intro l hl
    by_contra h
    have : l ≤ i := Finset.le_max' _ l (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h)
    exact absurd hl (not_lt.mpr this)
  refine ⟨i, j, fun σ => ?_⟩
  set A := LinearMap.toMatrix b b (ρ σ) with hAdef
  have hmat : A * B = c σ • (B * A) := by
    rw [hAdef, hBdef, ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, ← map_smul, hcomm]
  have h1 : (A * B) i j = μ σ i * B i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hAdef, hAdiag]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hAdef, hAlow σ i l h, zero_mul]
      · rw [himax l h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h2 : (B * A) i j = B i j * μ σ j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j, hAdef, hAdiag]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hjmin i l h, zero_mul]
      · rw [hAdef, hAlow σ l j h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have h3 := congrFun (congrFun hmat i) j
  rw [Matrix.smul_apply, h1, h2, smul_eq_mul] at h3
  have : (μ σ i - c σ * μ σ j) * B i j = 0 := by rw [sub_mul, h3]; ring
  rcases mul_eq_zero.mp this with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h himem
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module GlobalTheory.Pst.DpstMap

private theorem tensV_eq_rT {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V']
    [IsScalarTower ℚ_[l] LL V'] (f : V →ₗ[LL] V') (x : V ⊗[ℚ_[l]] Bst P) :
    tensV P f x = (f.restrictScalars ℚ_[l]).rTensor (Bst P) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem UpperTheory.weilDeligne_dpst_leftExact :
    UpperTheory.V.Af.Wd.DLeft := by
  intro l _ P K L V' V V'' _ _ _ _ _ _ _ _ _ _ _ _ ρ' ρ ρ'' f p hf hp hfi hex0
  have hex : Function.Exact (f.restrictScalars ℚ_[l]) (p.restrictScalars ℚ_[l]) := hex0
  have hexT := Module.Flat.rTensor_exact (Bst P) hex
  have hinj : Function.Injective ((f.restrictScalars ℚ_[l]).rTensor (Bst P)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hfi
  refine ⟨fun x y hxy => Subtype.ext (hinj ?_), fun y => ⟨fun hy => ?_, ?_⟩⟩
  · rw [← tensV_eq_rT, ← tensV_eq_rT]
    exact congrArg Subtype.val hxy
  · have h0 : tensV P p (y : V ⊗[ℚ_[l]] Bst P) = 0 := congrArg Subtype.val hy
    rw [tensV_eq_rT] at h0
    obtain ⟨z, hz⟩ := (hexT _).mp h0
    have hz' : tensV P f z = y := by rw [tensV_eq_rT]; exact hz
    obtain ⟨K', hK'⟩ := (mem_Dpst P ρ).mp y.2
    have hzD : z ∈ Dpst P ρ' := by
      refine (mem_Dpst P ρ').mpr ⟨K', fun g hg => hinj ?_⟩
      rw [← tensV_eq_rT, ← tensV_eq_rT, tensV_stRep P ρ' ρ f hf, hz', hK' g hg]
    exact ⟨⟨z, hzD⟩, Subtype.ext hz'⟩
  · rintro ⟨x, rfl⟩
    refine Subtype.ext ?_
    show tensV P p (tensV P f x.1) = 0
    rw [tensV_eq_rT, tensV_eq_rT]
    exact (hexT _).mpr ⟨x.1, rfl⟩
end

section

open Module

theorem UpperTheory.weilDeligne_triangular_initial_segment :
    UpperTheory.V.Af.Wd.TriInit := by
  intro k W ι _ _ _ n T d hT
  obtain ⟨b, hb⟩ := hT
  have hp : ∀ a x, b.coord (Fin.last n) (T a x) = d a (Fin.last n) * b.coord (Fin.last n) x := by
    intro a x
    have h : (b.coord (Fin.last n)) ∘ₗ (T a) = d a (Fin.last n) • b.coord (Fin.last n) := by
      refine b.ext fun j => ?_
      have h1 := (hb a).1 (Fin.last n) j
      have h2 := (hb a).2 (Fin.last n)
      rw [LinearMap.toMatrix_apply] at h1 h2
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, smul_eq_mul]
      by_cases hj : j = Fin.last n
      · subst hj
        rw [h2]; simp
      · rw [h1 (lt_of_le_of_ne (Fin.le_last j) hj), Finsupp.single_apply, if_neg hj, mul_zero]
    simpa using LinearMap.congr_fun h x
  have hS : ∀ a, ∀ x ∈ LinearMap.ker (b.coord (Fin.last n)), T a x ∈ LinearMap.ker (b.coord (Fin.last n)) := by
    intro a x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hp, hx, mul_zero]
  refine ⟨LinearMap.ker (b.coord (Fin.last n)), hS, b.coord (Fin.last n), ?_, rfl, hp, ?_⟩
  · intro c
    exact ⟨c • b (Fin.last n), by simp⟩
  · let v : Fin n → LinearMap.ker (b.coord (Fin.last n)) := fun i =>
      ⟨b (Fin.castSucc i), by
        rw [LinearMap.mem_ker, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply,
          if_neg (Fin.castSucc_lt_last i).ne]⟩
    have hv : LinearIndependent k v := by
      apply LinearIndependent.of_comp (LinearMap.ker (b.coord (Fin.last n))).subtype
      exact b.linearIndependent.comp Fin.castSucc (Fin.castSucc_injective n)
    have key : ∀ x : LinearMap.ker (b.coord (Fin.last n)),
        x = ∑ i, b.repr (x : W) (Fin.castSucc i) • v i := by
      intro x
      apply Subtype.ext
      have hx : b.repr (x : W) (Fin.last n) = 0 := x.2
      have h := b.sum_repr (x : W)
      rw [Fin.sum_univ_castSucc, hx, zero_smul, add_zero] at h
      rw [Submodule.coe_sum]
      exact h.symm
    have hsp : ⊤ ≤ Submodule.span k (Set.range v) := by
      intro x _
      rw [key x]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    let b' := Basis.mk hv hsp
    have hb' : ∀ i, b' i = v i := fun i => Basis.mk_apply hv hsp i
    have hr : ∀ (x : LinearMap.ker (b.coord (Fin.last n))) i, b'.repr x i = b.repr (x : W) (Fin.castSucc i) := by
      intro x i
      have h := congrFun (b'.repr_sum_self fun i => b.repr (x : W) (Fin.castSucc i)) i
      simp only [hb'] at h
      rw [← key x] at h
      exact h
    have hm : ∀ a i j, LinearMap.toMatrix b' b' ((T a).restrict (hS a)) i j =
        LinearMap.toMatrix b b (T a) (Fin.castSucc i) (Fin.castSucc j) := by
      intro a i j
      rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hr, hb']
      rfl
    refine ⟨b', fun a => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
    · exact (hm a i j).trans ((hb a).1 _ _ (Fin.castSucc_lt_castSucc_iff.2 hij))
    · exact (hm a i i).trans ((hb a).2 _)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module Topology Polynomial

namespace UpperTheory.V.Af.Wd

variable {l : ℕ} [hl : Fact l.Prime]

open scoped Formalism.Per in
private theorem tf_lift (y : OCb l) {m : ℕ} (hm : 0 < m) (hy : y ^ l ^ m = y) :
    ∃ (z : OC l) (x : Om l), (z : ℂ_[l]) = (x : ℂ_[l]) ∧ x ^ l ^ m = x ∧
      PreTilt.coeff 0 y = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) z := by
  have h1 : 1 < l ^ m := Nat.one_lt_pow hm.ne' hl.out.one_lt
  have hz : y.untilt ^ l ^ m = y.untilt := by rw [← map_pow, hy]
  have hz' : ((y.untilt : OC l) : ℂ_[l]) ^ l ^ m = (y.untilt : OC l) := by
    have := congrArg (fun t : OC l => (t : ℂ_[l])) hz
    simpa using this
  have hint : IsIntegral (Om l) ((y.untilt : OC l) : ℂ_[l]) := by
    refine ⟨X ^ l ^ m - X, monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1), ?_⟩
    simp [hz']
  obtain ⟨x, hx⟩ := minpoly.mem_range_of_degree_eq_one (Om l) _
    (IsAlgClosed.degree_eq_one_of_irreducible (Om l) (minpoly.irreducible hint))
  refine ⟨y.untilt, x, hx.symm, ?_, (PreTilt.mk_untilt_eq_coeff_zero y).symm⟩
  apply (algebraMap (Om l) ℂ_[l]).injective
  have hx' : algebraMap (Om l) ℂ_[l] x = (y.untilt : OC l) := hx
  rw [map_pow, hx', hz']

private theorem tf_act {P : LocPrime l} (AI : LocAinf l P) (y : OCb l) {m : ℕ} (hm : 0 < m) (hy : y ^ l ^ m = y)
    {z : OC l} {x : Om l} (hzx : (z : ℂ_[l]) = (x : ℂ_[l]))
    (h0 : PreTilt.coeff 0 y = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) z)
    (g : GQ l) (k : ℕ) (hg : g x = x ^ k) : AI.actT g y = y ^ k := by
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g y 0 _ h0
  rw [hzx, AI.actC_ext, hg, PadicComplex.coe_eq, map_pow, ← PadicComplex.coe_eq, ← hzx] at h1
  have h3 : y' = z ^ k := Subtype.ext (by rw [h1]; simp)
  refine GlobalTheory.UnramifiedCrys.eq_of_coeff_zero hm (by rw [← map_pow, hy])
    (by rw [← pow_mul, mul_comm, pow_mul, hy]) ?_
  rw [h2, map_pow, h0, h3]
  exact map_pow _ _ _

private theorem tf_root {x : Om l} {m : ℕ} (hm : 0 < m) (hx : x ^ l ^ m = x) (h0 : x ≠ 0) :
    ∃ n, 0 < n ∧ ¬ l ∣ n ∧ x ^ n = 1 := by
  have h1 : 1 < l ^ m := Nat.one_lt_pow hm.ne' hl.out.one_lt
  refine ⟨l ^ m - 1, by omega, fun h => ?_, ?_⟩
  · have h2 := (Nat.dvd_sub_iff_right h1.le (dvd_pow_self l hm.ne')).mp h
    exact hl.out.one_lt.ne' (Nat.dvd_one.mp h2)
  · apply mul_right_cancel₀ h0
    rw [← pow_succ, one_mul, Nat.sub_add_cancel h1.le, hx]

end UpperTheory.V.Af.Wd

open UpperTheory.V.Af.Wd in
theorem UpperTheory.tilt_frobenius_teichmuller_action :
    UpperTheory.V.Af.Wd.TiltFrob := by
  intro l hl y m hm hy g k hg
  obtain ⟨z, x, hzx, hx, h0⟩ := tf_lift y hm hy
  refine tf_act _ y hm hy hzx h0 g (l ^ k) ?_
  by_cases hx0 : x = 0
  · rw [hx0, map_zero, zero_pow (pow_ne_zero _ hl.out.ne_zero)]
  obtain ⟨n, hn0, hn, hxn⟩ := tf_root hm hx hx0
  have hmem : x ∈ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨n, hn0, hn, hxn⟩
  have h1 := hg ⟨x, hmem⟩
  rw [GlobalTheory.Pst.frobUr_pow_root k ⟨x, hmem⟩ n hn0 hn (Subtype.ext hxn)] at h1
  exact h1
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.Pst.DpstMap GlobalTheory.GalOfCusp

private theorem zpow_apply_eig {F M : Type} [Field F] [AddCommGroup M] [Module F M] (u : (End F M)ˣ) (x : M) (c : F)
    (hc : c ≠ 0) (hx : (u : End F M) x = c • x) (n : ℤ) : ((u ^ n : (End F M)ˣ) : End F M) x = c ^ n • x := by
  have hi : ((u⁻¹ : (End F M)ˣ) : End F M) x = c⁻¹ • x := by
    rw [eq_inv_smul_iff₀ hc, ← map_smul, ← hx, ← End.mul_apply, Units.inv_mul, End.one_apply]
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, Units.val_mul, End.mul_apply, hx, map_smul, ih, smul_smul,
      zpow_add_one₀ hc, mul_comm]
  | pred n ih => rw [zpow_sub_one, Units.val_mul, End.mul_apply, hi, map_smul, ih, smul_smul,
      zpow_sub_one₀ hc, mul_comm]

private theorem key {F M : Type} [Field F] [AddCommGroup M] [Module F M] (u : (End F M)ˣ) (φ a : End F M)
    (hu : (u : End F M) = φ) (hcm : φ * a = a * φ) (x : M) (c s : F) (hc : c ≠ 0) (f : ℕ) (hφ : (φ ^ f) x = c • x)
    (hs : a x = s • x) (n : ℕ) (d : ℤ) :
    (a * ((u ^ (-((f : ℤ) * d)) : (End F M)ˣ) : End F M)) ((φ ^ n) x) = (c ^ (-d) * s) • (φ ^ n) x := by
  have hφ' : (φ ^ f) ((φ ^ n) x) = c • (φ ^ n) x := by
    rw [← End.mul_apply, ← pow_add, add_comm, pow_add, End.mul_apply, hφ, map_smul]
  have hs' : a ((φ ^ n) x) = s • (φ ^ n) x := by
    have hcm' : Commute φ a := hcm
    rw [← End.mul_apply, ← (hcm'.pow_left n).eq, End.mul_apply, hs, map_smul]
  have hz := zpow_apply_eig (u ^ f) _ c hc (by rw [Units.val_pow_eq_pow_val, hu]; exact hφ') (-d)
  rw [End.mul_apply, ← mul_neg, zpow_mul, zpow_natCast, hz, map_smul, hs', mul_smul]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem UpperTheory.weil_deligne_rank_one_line :
    UpperTheory.V.Af.Wd.Line := by
  intro F Ω _ _ _ _ _ l _ P ι w A h O _ _ _ Bw hj L V _ _ _ _ _ ρ h1 hV x hx0 c hc hφ σ s hs y
  have hfin := hV.finite
  have hd : finrank ℂ (WDSpace P ι ρ) = 1 := by
    rw [LetterDim.finrank_wdSpace l P ι _ L _ _ hV, h1]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, wdMk P ι ρ ((phiD P ρ ^ n) x) ≠ 0 := by
    by_contra hh
    exact hx0 (GlobalTheory.PstFaithful.eq_zero_of_wdMk_phiD_pow l P ι _ L _ _ _ fun n => by_contra fun h0 => hh ⟨n, h0⟩)
  have hw : weilD Bw h P ρ σ ((phiD P ρ ^ n) x) = (c ^ (-deg σ) * s) • (phiD P ρ ^ n) x := by
    rw [weilD_apply]
    exact key (phiU P ρ) (phiD P ρ) _ (coe_phiU P ρ) (phiD_actD P ρ _) x c s hc _ hφ hs n _
  obtain ⟨d, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (K := ℂ) _ hn).mp hd y
  rw [map_smul, wdRho_mk, hw]
  change d • wdMk P ι ρ ((Dpst P ρ).module.toSMul.smul (c ^ (-deg σ) * s) ((phiD P ρ ^ n) x)) = _
  rw [wdMk_smul, smul_comm]
end

section

theorem UpperTheory.adelic_cohomology_finite_orbit_bound :
    UpperTheory.V.Af.CohB.FinOrbAbs := by
  classical
  intro G H _ _ ι Γ U K hΓ hU ⟨T, hT⟩
  haveI : Fintype (H ⧸ Γ) := Subgroup.fintypeOfIndexNeZero hΓ.index_ne_zero
  haveI : Fintype (K ⧸ U.subgroupOf K) := Subgroup.fintypeOfIndexNeZero hU
  refine ⟨((Finset.univ : Finset (H ⧸ Γ)) ×ˢ T ×ˢ (Finset.univ : Finset (K ⧸ U.subgroupOf K))).image
    (fun x => ι (x.1.out)⁻¹ * x.2.1 * ((x.2.2.out : K) : G)), fun g => ?_⟩
  obtain ⟨h, t, ht, k, hk, rfl⟩ := hT g
  obtain ⟨γ, hγ⟩ := QuotientGroup.mk_out_eq_mul Γ h⁻¹
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf K) (⟨k, hk⟩ : K)
  have huU : (((u : K) : G))⁻¹ ∈ U := U.inv_mem (Subgroup.mem_subgroupOf.1 u.2)
  refine ⟨γ, γ.2, _, Finset.mem_image.2 ⟨(QuotientGroup.mk h⁻¹, t, QuotientGroup.mk ⟨k, hk⟩), ?_, rfl⟩,
    _, huU, ?_⟩
  · simp [ht]
  · simp only [hγ, hu, mul_inv_rev, inv_inv, map_mul, map_inv, Subgroup.coe_mul]
    group
end

section

private theorem index_closed_dyadic_subgroup {G H A : Type} [Group G] [Group H] [Group A] [Finite A] (j : G →* H) (hj : Function.Injective j)
    (f : G →* A) (K : Subgroup G) :
    (f.ker.map j).relIndex (K.map j) ≠ 0 ∧ (f.ker.map j).relIndex (K.map j) ≤ Nat.card A := by
  rw [Subgroup.relIndex_map_map_of_injective _ _ hj]
  have h1 : f.ker.relIndex ⊤ = Nat.card f.range := by rw [Subgroup.relIndex_top_right, Subgroup.index_ker]
  have h0 : f.ker.relIndex ⊤ ≠ 0 := by rw [h1]; exact Nat.card_pos.ne'
  refine ⟨fun h => h0 (Subgroup.relIndex_eq_zero_of_le_right le_top h), ?_⟩
  refine (Subgroup.relIndex_le_of_le_right le_top h0).trans ?_
  rw [h1]
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

private theorem card_GL_le (R : Type) [CommRing R] [Finite R] (n : ℕ) :
    Nat.card (GL (Fin n) R) ≤ Nat.card R ^ (n * n) := by
  have h : Nat.card (GL (Fin n) R) ≤ Nat.card (Fin n → Fin n → R) :=
    Nat.card_le_card_of_injective (fun g : GL (Fin n) R => (g.val : Fin n → Fin n → R))
      fun x y h => Units.ext h
  rw [Nat.card_fun, Nat.card_fun, ← pow_mul] at h
  simpa using h

theorem UpperTheory.level_subgroup_index_bound_of_card_ohat :
    UpperTheory.V.Af.CohB.CardOhat → UpperTheory.V.Af.CohB.KLevIdx := by
  intro hC F _ _ n N hN
  obtain ⟨hfin, hcard⟩ := hC F N hN
  have hj : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin n) (UpperTheory.V.Af.Ohat F).subtype) := fun x y h =>
    Units.ext (Matrix.ext fun a b => Subtype.ext
      (congrArg (fun z : GL (Fin n) (GlobalTheory.CuspRep.Af F) => z a b) h))
  haveI : Finite (Matrix (Fin n) (Fin n) (↥(UpperTheory.V.Af.Ohat F) ⧸ Ideal.span {(N : ↥(UpperTheory.V.Af.Ohat F))})) :=
    inferInstanceAs (Finite (Fin n → Fin n → _))
  haveI : Finite (GL (Fin n) (↥(UpperTheory.V.Af.Ohat F) ⧸ Ideal.span {(N : ↥(UpperTheory.V.Af.Ohat F))})) :=
    Finite.of_injective _ Units.val_injective
  obtain ⟨h0, h1⟩ := index_closed_dyadic_subgroup _ hj
    (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (Ideal.span {(N : ↥(UpperTheory.V.Af.Ohat F))})))
    (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (Ideal.span {((1 : ℕ) : ↥(UpperTheory.V.Af.Ohat F))}))).ker
  refine ⟨h0, h1.trans ((card_GL_le _ n).trans ?_)⟩
  rw [pow_mul (N : ℕ)]
  exact Nat.pow_le_pow_left hcard _
end

section

open UpperTheory.V.Af.CohB in
theorem UpperTheory.absolute_bound_of_partial_bound_of_orbit_bound :
    UpperTheory.V.Af.CohB.PartBound → UpperTheory.V.Af.CohB.OrbBound → UpperTheory.V.Af.CohB.AbsBound := by
  intro hP hO Γ Y _ _ hT hB
  obtain ⟨T, hT⟩ := hT
  choose cf hcf using fun t : ↥T => hO Γ Y t.1 (hB t.1)
  refine ⟨∑ t, cf t, ?_⟩
  intro X _ p hp D hD d ξ
  let r : MulAction.orbitRel.Quotient Γ Y → ↥T := fun q =>
    ⟨Classical.choose (hT q.out) • q.out, Classical.choose_spec (hT q.out)⟩
  let cl : X → ↥T := fun x => r (Quotient.mk (MulAction.orbitRel Γ Y) (p x))
  have hcl : ∀ (γ : Γ) (x : X), cl (γ • x) = cl x := by
    intro γ x
    simp only [cl, hp]
    congr 1
    exact Quotient.sound ⟨γ, rfl⟩
  refine (hP Γ X ↥T cl hcl d ξ).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul, Nat.cast_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  have hsurj : ∀ x : ↥(UpperTheory.V.Af.CohB.part cl hcl t), ∃ g : Γ, g • p x.1 = t.1 := by
    rintro ⟨x, hx⟩
    change cl x = t at hx
    obtain ⟨h, hh⟩ := Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel Γ Y) (p x)))
    refine ⟨Classical.choose (hT (Quotient.mk (MulAction.orbitRel Γ Y) (p x)).out) * h, ?_⟩
    rw [mul_smul]
    simp only at hh ⊢
    rw [hh]
    exact congrArg Subtype.val hx
  refine hcf t ↥(UpperTheory.V.Af.CohB.part cl hcl t) (fun x => p x.1) (fun γ x => hp γ x.1) hsurj D
    (le_trans (Cardinal.mk_le_of_injective
      (f := fun z : {x : ↥(UpperTheory.V.Af.CohB.part cl hcl t) // p x.1 = t.1} => (⟨z.1.1, z.2⟩ : {x // p x = t.1}))
      (fun a b hab => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab)))) (hD t.1)) d ξ
end

section

theorem UpperTheory.adelic_cohomology_fiber_card :
    UpperTheory.V.Af.CohB.FibCard := by
  intro G _ U U' h hne y
  set e := Subgroup.quotientEquivProdOfLE h with he
  have key : ∀ x : G ⧸ U, (e x).1 = Subgroup.quotientMapOfLE h x := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H g => rfl
  have e1 : {x // Subgroup.quotientMapOfLE h x = y} ≃ (U' ⧸ U.subgroupOf U') :=
    { toFun := fun x => (e x.1).2
      invFun := fun b => ⟨e.symm (y, b), by rw [← key, Equiv.apply_symm_apply]⟩
      left_inv := by
        rintro ⟨x, hx⟩
        apply Subtype.ext
        change e.symm (y, (e x).2) = x
        rw [← hx, ← key]
        exact e.symm_apply_apply x
      right_inv := by
        intro b
        change (e (e.symm (y, b))).2 = b
        rw [Equiv.apply_symm_apply] }
  rw [Cardinal.mk_congr e1]
  have : Finite (U' ⧸ U.subgroupOf U') := Subgroup.index_ne_zero_iff_finite.mp hne
  rw [← Nat.cast_card]
  rfl
end

section

open CategoryTheory

theorem UpperTheory.cohomology_rank_eq_homology_rank :
    UpperTheory.V.Af.CohB.RankHomology := by
  intro C q
  have h1 : Function.Surjective (C.homologyπ q).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have h2 : Function.Injective (C.iCycles q).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact (LinearMap.rank_le_of_surjective _ h1).trans (LinearMap.rank_le_of_injective _ h2)
end

section

open scoped Matrix

theorem UpperTheory.cohomology_to_coinvariants_injective :
    UpperTheory.V.Af.CohB.ToCoInj := by
  intro Γ X Y _ _ _ p hp y horb d ξ f f' h
  funext x
  obtain ⟨g, hg⟩ := horb x
  have hx : g • x ∈ UpperTheory.V.Af.CohB.fib p hp y := by
    change p (g • x) = y
    rw [hp, hg]
  have h1 : (UpperTheory.V.Af.CohB.toCo p hp y ξ f).1 g ⟨g • x, hx⟩
      = (UpperTheory.V.Af.CohB.toCo p hp y ξ f').1 g ⟨g • x, hx⟩ := by rw [h]
  rw [UpperTheory.V.Af.CohB.toCo_apply, UpperTheory.V.Af.CohB.toCo_apply] at h1
  simp only [inv_smul_smul] at h1
  have h2 := congrArg (fun v => ξ g⁻¹ *ᵥ v) h1
  simp only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec] at h2
  exact h2
end
