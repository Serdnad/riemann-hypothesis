module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle122
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
public import Formalism.LocalRingCardinality.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle064
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle069
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.SmoothCharNorm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finite_image_units (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (χ '' {x : kˣ | valuation k (x : k) = 1}).Finite := by
  have hS := GlobalTheory.SmGL.UnramFixed.isCompact_unitsO k
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun z : kˣ => (fun y => z⁻¹ * y) ⁻¹' (χ.ker : Set kˣ))
    (fun z => (continuous_const.mul continuous_id).isOpen_preimage _ hχ)
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
  refine (t.finite_toSet.image χ).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (ht hy)
  refine ⟨i, hi, ?_⟩
  have : χ (i⁻¹ * y) = 1 := hyi
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this

theorem norm_eq_one_of_valuation_eq_one (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (u : kˣ)
    (hu : valuation k (u : k) = 1) : ‖(χ u : ℂ)‖ = 1 := by
  by_contra hne
  have hpos : 0 < ‖(χ u : ℂ)‖ := norm_pos_iff.2 (χ u).ne_zero
  have hinj := pow_right_injective₀ hpos hne
  have hinf := Set.infinite_range_of_injective hinj
  apply hinf
  refine ((finite_image_units χ hχ).image (fun w : ℂˣ => ‖(w : ℂ)‖)).subset ?_
  rintro _ ⟨n, rfl⟩
  refine ⟨χ (u ^ n), ⟨u ^ n, ?_, rfl⟩, ?_⟩
  · simp [Units.val_pow_eq_pow_val, map_pow, hu]
  · simp [map_pow, Units.val_pow_eq_pow_val, norm_pow]

noncomputable def ordHom (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (ord k x)
  map_one' := by
    have : ord k (1 : kˣ) = 0 := ord_eq_zero_iff.2 (by simp)
    simp [this]
  map_mul' x y := by simp [ord_mul, ofAdd_add]

theorem ord_zpow (x : kˣ) (n : ℤ) : ord k (x ^ n) = n * ord k x := by
  have := congrArg Multiplicative.toAdd (map_zpow (ordHom k) x n)
  simpa [ordHom, toAdd_zpow, smul_eq_mul] using this

end GlobalTheory.SmoothCharNorm

theorem GlobalTheory.SmoothCharNorm.norm_eq_nabs_rpow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ), IsSmoothChar χ → ∃ s : ℝ, ∀ z : kˣ, ‖(χ z : ℂ)‖ = nabs k z ^ s := by
  intro k _ _ _ _ χ hχ
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  have hord : ord k ϖ = 1 := ord_eq_one hϖ
  have ha : 0 < ‖(χ ϖ : ℂ)‖ := norm_pos_iff.2 (χ ϖ).ne_zero
  have hq : (1 : ℝ) < (resCard k : ℝ) := by exact_mod_cast GlobalTheory.SplitWeil.one_lt_resCard k
  have hlq : Real.log (resCard k : ℝ) ≠ 0 := (Real.log_pos hq).ne'
  refine ⟨-Real.log ‖(χ ϖ : ℂ)‖ / Real.log (resCard k : ℝ), fun z => ?_⟩
  have hz : ‖(χ z : ℂ)‖ = ‖(χ ϖ : ℂ)‖ ^ ord k z := by
    have hw : valuation k ((ϖ ^ (-ord k z) * z : kˣ) : k) = 1 := by
      rw [← ord_eq_zero_iff, ord_mul, GlobalTheory.SmoothCharNorm.ord_zpow, hord]; ring
    have hdec : z = ϖ ^ (ord k z) * (ϖ ^ (-ord k z) * z) := by group
    conv_lhs => rw [hdec]
    rw [map_mul, Units.val_mul, norm_mul,
      GlobalTheory.SmoothCharNorm.norm_eq_one_of_valuation_eq_one χ hχ _ hw, mul_one, map_zpow,
      Units.val_zpow_eq_zpow_val, norm_zpow]
  have hϖabs : nabs k ϖ = (resCard k : ℝ)⁻¹ := by
    have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
    refine (nabs_properties k).2.2.2.2.1 ⟨ϖ, hlt.le⟩ ϖ ?_ rfl
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    ext x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one, Ideal.mem_span_singleton,
      (Valuation.integer.integers (valuation k)).dvd_iff_le, ← le_uniformizer_iff, ← hϖ]
    rfl
  have hn : nabs k z = (resCard k : ℝ) ^ (-ord k z) := by
    have hw : valuation k ((ϖ ^ (-ord k z) * z : kˣ) : k) = 1 := by
      rw [← ord_eq_zero_iff, ord_mul, GlobalTheory.SmoothCharNorm.ord_zpow, hord]; ring
    have hdec : z = ϖ ^ (ord k z) * (ϖ ^ (-ord k z) * z) := by group
    conv_lhs => rw [hdec]
    rw [nabs_mul, (nabs_eq_one_iff _).2 hw, mul_one]
    have hp : nabs k (ϖ ^ ord k z) = nabs k ϖ ^ ord k z := by
      simp [nabs, map_zpow]
    rw [hp, hϖabs, _root_.inv_zpow, _root_.zpow_neg]
  rw [hz, hn, ← Real.rpow_intCast, ← Real.rpow_intCast,
    ← Real.rpow_mul (by positivity), Real.rpow_def_of_pos ha,
    Real.rpow_def_of_pos (by positivity)]
  congr 1
  push_cast
  field_simp
end

section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory

namespace GlobalTheory.AmpleSeparateOverRing

theorem isSeparated_toSpecZ (R : Type) [CommRing R] (n : ℕ) :
    IsSeparated (specZIsTerminal.from (PSpace R n)) := by
  have : IsProper (PSpace.str R n) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R n
  rw [specZIsTerminal.hom_ext (specZIsTerminal.from (PSpace R n)) (PSpace.str R n ≫ specZIsTerminal.from _)]
  infer_instance

theorem exists_ample_model (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R)
    (ι : Type) (L : ι → LB X) (hL : ∀ i, (L i).IsLB) (M : ι → ℕ)
    (t : ∀ i, Fin (M i + 1) → (L i).Sec)
    (ht : ∀ i, ⨆ m, nonzeroLocus (t i m) = ⊤) (w : ι → ℕ) (hw : ∀ i, 1 ≤ w i)
    (T : Finset ι) :
    ∃ (Q : Scheme.{0}) (Ψ : X ⟶ Q) (r : Q ⟶ Sp R) (N : LB Q) (hN : IsAmpleLB N), IsSeparated r ∧
      Ψ ≫ r = f ∧
      CechPic.cls (N.pull Ψ) (LB.isLB_pull hN.isLB Ψ) = ∑ i ∈ T, (w i : ℤ) • CechPic.cls (L i) (hL i) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (a a' : Sp K ⟶ X), a ≫ Ψ = a' ≫ Ψ →
        a ≫ f = a' ≫ f ∧ ∀ i ∈ T,
          a ≫ ProjSpace.toProj f (t i) (ht i) = a' ≫ ProjSpace.toProj f (t i) (ht i) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨Sp R, f, 𝟙 _, LB.triv _, isAmpleLB_of_isAffine (LB.isLB_triv _), inferInstance,
      Category.comp_id _, ?_, ?_⟩
    · rw [Finset.sum_empty]
      exact map_zero (CechPic.pull f)
    · intro K _ _ a a' h
      exact ⟨h, by simp⟩
  | insert i T hi ih =>
    obtain ⟨Q, Ψ, r, N, hN, hr, hΨ, hc, hinj⟩ := ih
    have hO1 := ProjSpace.O1_isLB R (M i)
    have hO : IsAmpleLB (lbPow (ProjSpace.O1 R (M i)) (w i)) :=
      (isAmpleLB_pow_iff hO1 (hw i)).2 (isAmple_projective_O_one R (M i))
    have : IsSeparated (specZIsTerminal.from (PSpace R (M i))) := isSeparated_toSpecZ R (M i)
    have hNp := LB.isLB_pull hN.isLB (pullback.fst (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i))))
    have hOq := LB.isLB_pull hO.isLB (pullback.snd (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i))))
    have hN' := CechPic.isLB_tens hNp hOq
    have hA : IsAmpleLB (CechPic.tens
        (N.pull (pullback.fst (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i)))))
        ((lbPow (ProjSpace.O1 R (M i)) (w i)).pull
          (pullback.snd (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i)))))) := by
      refine hN.box hO hN' (IsPullback.of_hasPullback _ _) ?_
      refine (CechPic.cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hN' hNp) hOq)).1 ?_
      rw [CechPic.cls_div (LB.isLB_div hN' hNp) hOq, CechPic.cls_div hN' hNp, CechPic.cls_tens hNp hOq]
      abel
    refine ⟨_, pullback.lift Ψ (ProjSpace.toProj f (t i) (ht i)) (specZIsTerminal.hom_ext _ _),
      pullback.fst _ _ ≫ r, _, hA, inferInstance, by rw [← Category.assoc, pullback.lift_fst, hΨ], ?_, ?_⟩
    · rw [Finset.sum_insert hi, ← hc]
      have e := (CechPic.cls_eq_iff (LB.isLB_pull hO1 (ProjSpace.toProj f (t i) (ht i))) (hL i)).2
        (ProjSpace.lbIso_pullback_O1_toProj f (t i) (ht i))
      rw [← e, CechPic.cls_pull hN' _, CechPic.cls_tens hNp hOq, map_add (f := _), CechPic.cls_pull hN.isLB,
        CechPic.cls_pull hO.isLB, ← CechPic.pull_comp, ← CechPic.pull_comp, pullback.lift_fst,
        pullback.lift_snd, CechPic.cls_lbPow hO1, map_nsmul, CechPic.cls_pull hN.isLB,
        CechPic.cls_pull hO1, add_comm, natCast_zsmul]
    · intro K _ _ a a' h
      have h1 : a ≫ Ψ = a' ≫ Ψ := by
        have := congrArg (· ≫ pullback.fst (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i)))) h
        simp only [Category.assoc] at this
        rwa [pullback.lift_fst] at this
      have h2 : a ≫ ProjSpace.toProj f (t i) (ht i) = a' ≫ ProjSpace.toProj f (t i) (ht i) := by
        have := congrArg (· ≫ pullback.snd (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i)))) h
        simp only [Category.assoc] at this
        rwa [pullback.lift_snd] at this
      obtain ⟨e1, e2⟩ := hinj K a a' h1
      refine ⟨e1, fun j hj => ?_⟩
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact h2
      · exact e2 j hj

end GlobalTheory.AmpleSeparateOverRing
end

section

open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylCombInt

open Formalism.L2.DIV

theorem weyl_eq (N : ℕ) (ν : Fin N → ℕ) :
    Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν = WeylLatticeDuality.weyl ℤ N N le_rfl ν := rfl

theorem eval_ten {K Lt : Type} [Field K] [Fintype Lt] {N : ℕ} (f : Lt → MvPolynomial (Fin N × Fin N) K)
    (z : Lt × Fin N × Fin N → K) : eval z (ten f) = ∏ s, eval (fun v => z (s, v)) (f s) := by
  unfold ten
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [Formalism.GradedWeylDivisibility.blockEmb, eval_rename]
  rfl

theorem fockB_ten_dual {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {K : Type} [Field K] [CharZero K]
    (ι : Lt → Type) [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (Nc : Lt → ℚ)
    (hbg : ∀ s i k, Formalism.GradedWeylDivisibility.fockQ (b s i) (g s k) = if i = k then Nc s else 0) (κ' κ : ∀ s, ι s) :
    fockB (ten fun s => map (algebraMap ℚ K) (b s (κ' s))) (ten fun s => map (algebraMap ℚ K) (g s (κ s))) =
      if κ' = κ then ∏ s, (Nc s : K) else 0 := by
  rw [GlobalTheory.WeylMinorDual.fockB_ten]
  simp only [GlobalTheory.WeylMinorDual.fockB_map, hbg]
  split_ifs with h
  · subst h; simp
  · obtain ⟨s, hs⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])

theorem coeff_unique (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T]
    (e : Lt → T) (he : Function.Bijective e) (N : ℕ) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    [∀ s, DecidableEq (ι s)] (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (Nc : Lt → ℚ)
    (hNc : ∀ s, Nc s ≠ 0) (hbg : ∀ s i k, Formalism.GradedWeylDivisibility.fockQ (b s i) (g s k) = if i = k then Nc s else 0)
    (c : (∀ s, ι s) → ℂ_[p])
    (h : ∀ y : T → Matrix (Fin N) (Fin N) ℂ_[p], ∑ κ, c κ * ∏ s, MvPolynomial.eval
      (fun k : Fin N × Fin N => y (e s) k.1 k.2) (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) = 0) :
    c = 0 := by
  set E := Equiv.ofBijective e he with hE
  set P : (∀ s, ι s) → MvPolynomial (Lt × Fin N × Fin N) ℂ_[p] :=
    fun κ => ten fun s => map (algebraMap ℚ ℂ_[p]) (g s (κ s)) with hP
  have h0 : ∑ κ, c κ • P κ = 0 := by
    apply MvPolynomial.funext
    intro z
    have hz := h (fun τ => Matrix.of fun i j => z (E.symm τ, i, j))

    rw [map_zero, map_sum]
    rw [← hz]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [smul_eval, hP]
    simp only [eval_ten]
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    have hs : E.symm (e s) = s := by
      rw [← Equiv.ofBijective_apply e he]; exact E.symm_apply_apply s
    simp only [Matrix.of_apply, hs]
  funext κ'
  have h1 := congrArg (fockB (ten fun s => map (algebraMap ℚ ℂ_[p]) (b s (κ' s)))) h0

  rw [← fockBL_apply, ← fockBL_apply, map_sum, map_zero] at h1
  simp only [map_smul, fockBL_apply, hP, fockB_ten_dual ι b g Nc hbg, smul_eq_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  have hne : ∏ s, (Nc s : ℂ_[p]) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun s _ => by exact_mod_cast hNc s
  simpa [hne] using h1

theorem map_intQ (p : ℕ) [Fact p.Prime] (N : ℕ) (w : MvPolynomial (Fin N × Fin N) ℤ) :
    map (algebraMap ℚ ℂ_[p]) (Formalism.GradedWeylDivisibility.intQ N N w) = map (Int.castRingHom ℂ_[p]) w := by
  have : Formalism.GradedWeylDivisibility.intQ N N w = map (Int.castRingHom ℚ) w := rfl
  rw [this, map_map, show (algebraMap ℚ ℂ_[p]).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ_[p] from
    RingHom.ext_int _ _]

theorem comb_mem_iff : ∀ (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (e : Lt → T), Function.Bijective e →
    ∀ (N : ℕ) (ν : T → Fin N → ℕ) (ι : Lt → Type) [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (Nc : Lt → ℚ), (∀ s, Nc s ≠ 0) →
    (∀ s i k, Formalism.GradedWeylDivisibility.fockQ (b s i) (g s k) = if i = k then Nc s else 0) →
    (∀ s, Submodule.span ℤ (Set.range (g s)) =
      (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl (ν (e s))).map (Formalism.GradedWeylDivisibility.intQ N N)) →
    ∀ a : (∀ s, ι s) → ℂ_[p],
      ((fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => ∑ κ : (∀ s, ι s), a κ *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s)))) ∈ WeylLatticeDuality.DelW p T N ν ↔
        ∀ κ, ‖a κ‖ ≤ 1) := by
  intro p _ Lt T _ _ _ e he N ν ι _ _ b g Nc hNc hbg hspan a
  set E := Equiv.ofBijective e he with hE
  have hs : ∀ s, E.symm (e s) = s := fun s => by
    rw [← Equiv.ofBijective_apply e he]; exact E.symm_apply_apply s
  set G : (∀ s, ι s) → (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p] := fun κ y =>
    ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
      (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) with hG
  constructor
  · intro hmem
    let S : AddSubgroup ((T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) :=
      { carrier := {F | ∃ a' : (∀ s, ι s) → ℂ_[p], (∀ κ, ‖a' κ‖ ≤ 1) ∧ F = fun y => ∑ κ, a' κ * G κ y}
        zero_mem' := ⟨0, fun _ => by simp, by funext y; simp⟩
        add_mem' := by
          rintro F F' ⟨a1, h1, rfl⟩ ⟨a2, h2, rfl⟩
          refine ⟨a1 + a2, fun κ => ?_, ?_⟩
          · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1 κ) (h2 κ))
          · funext y; simp [add_mul, Finset.sum_add_distrib]
        neg_mem' := by
          rintro F ⟨a1, h1, rfl⟩
          refine ⟨-a1, fun κ => by simpa using h1 κ, ?_⟩
          funext y; simp [neg_mul, Finset.sum_neg_distrib] }
    have hle : WeylLatticeDuality.DelW p T N ν ≤ S := by
      unfold WeylLatticeDuality.DelW
      rw [AddSubgroup.closure_le]
      rintro F ⟨r, f, hr, hf, rfl⟩
      have hn : ∀ s, ∃ n : ι s → ℤ, ∑ k, n k • g s k = Formalism.GradedWeylDivisibility.intQ N N (f (e s)) := by
        intro s
        rw [← Submodule.mem_span_range_iff_exists_fun, hspan s, weyl_eq]
        exact Submodule.mem_map_of_mem (hf (e s))
      choose n hn using hn
      refine ⟨fun κ => r * ∏ s, ((n s (κ s) : ℤ) : ℂ_[p]), fun κ => ?_, ?_⟩
      · rw [norm_mul, norm_prod]
        exact mul_le_one₀ hr (by positivity)
          (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun s _ => IsUltrametricDist.norm_intCast_le_one _ _)
      · funext y
        rw [← he.prod_comp]
        have hterm : ∀ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f (e s))) =
            ∑ k, ((n s k : ℤ) : ℂ_[p]) * MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
              (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s k)) := by
          intro s

          rw [← map_intQ, ← hn s, map_sum, map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_zsmul, map_zsmul, zsmul_eq_mul]
        simp only [hterm, Fintype.prod_sum, Finset.mul_sum, hG]
        refine Finset.sum_congr rfl fun κ _ => ?_
        rw [Finset.prod_mul_distrib]; ring
    obtain ⟨a', ha', heq⟩ := hle hmem
    have hc := coeff_unique p Lt T e he N ι b g Nc hNc hbg (a - a') (fun y => by
      have := congrFun heq y
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]; exact this)
    have : a = a' := sub_eq_zero.mp hc
    subst this; exact ha'
  · intro ha
    have hw : ∀ s k, ∃ w ∈ WeylLatticeDuality.weyl ℤ N N le_rfl (ν (e s)), Formalism.GradedWeylDivisibility.intQ N N w = g s k := by
      intro s k
      have : g s k ∈ Submodule.span ℤ (Set.range (g s)) := Submodule.subset_span (Set.mem_range_self k)
      rw [hspan s, weyl_eq] at this
      exact this
    choose w hw hwg using hw
    have hfun : (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => ∑ κ : (∀ s, ι s), a κ * G κ y) =
        ∑ κ : (∀ s, ι s), fun y => a κ * G κ y := by
      funext y; simp [Finset.sum_apply]
    show (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => ∑ κ : (∀ s, ι s), a κ * G κ y) ∈ _
    rw [hfun]
    refine AddSubgroup.sum_mem _ fun κ _ => AddSubgroup.subset_closure ?_
    refine ⟨a κ, fun τ => w (E.symm τ) (κ (E.symm τ)), ha κ, fun τ => ?_, ?_⟩
    · have := hw (E.symm τ) (κ (E.symm τ))
      rwa [show e (E.symm τ) = τ from E.apply_symm_apply τ] at this
    · funext y
      congr 1
      rw [← he.prod_comp]
      refine Finset.prod_congr rfl fun s _ => ?_
      dsimp only
      rw [hs s, ← hwg s (κ s), map_intQ]

end GlobalTheory.WeylCombInt
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

namespace GlobalTheory.UnitaryScalarModT

theorem eq_one_add_of_fixes : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (_ : Module.finrank F E = 2) (_ : ∀ x, σ (σ x) = x) (_ : ∀ x, σ x = x → x ∈ (algebraMap F E).range)
    (_ : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ θ t : 𝓞 E, (t : E) = σ θ ∧ θ - t ∉ P) (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (_ : T.Prime)
    (_ : ∀ a : v.adicCompletionIntegers F, Valued.v (a : v.adicCompletion F) < 1 → ∃ b : v.adicCompletionIntegers F, a = (T : v.adicCompletionIntegers F) * b)
    (M : Type) [AddCommGroup M] [Module (intV E v) M] (_ : Nat.card M = T) (m : M) (_ : m ≠ 0) (d c : intV E v) (_ : (d - 1) • m = 0)
    (_ : sigR σ (v.adicCompletion F) (d : E ⊗[F] v.adicCompletion F) * (d : E ⊗[F] v.adicCompletion F) =
        1 + (T : E ⊗[F] v.adicCompletion F) * (c : E ⊗[F] v.adicCompletion F)),
    ∃ e : intV E v, (d : E ⊗[F] v.adicCompletion F) = 1 + (T : E ⊗[F] v.adicCompletion F) * (e : E ⊗[F] v.adicCompletion F) := by
  intro F E _ _ _ _ _ σ hdeg hσ hfix hun v T hT hunif M _ _ hM m hm d c hd hc
  obtain ⟨χ, hχ⟩ := GlobalTheory.PrimeOrderModule.exists_character (intV E v) M T hT hM
  obtain ⟨s, hs, hsχ⟩ := GlobalTheory.OverSplit.exists_splitting_of_character F E σ hdeg hσ hfix hun v T hT χ
  obtain ⟨⟨ε, hε⟩, -, -⟩ := GlobalTheory.OverResidue.residue_of_prime_card F E σ v s hs M T hT hM
    (fun a m ha => hχ a m (hsχ a ha))
  have hεm : ε m ≠ 0 := fun h => hm (ε.injective (h.trans (map_zero ε).symm))
  have key : ∀ (a : intV E v) (a' : v.adicCompletionIntegers F),
      (a' : v.adicCompletion F) = (s a).1 → a • m = 0 →
      a' ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    intro a a' h h0
    have h1 := hε a a' h m
    rw [h0, map_zero] at h1
    have h2 : IsLocalRing.residue _ a' * ε m = 0 := h1.symm
    exact (IsLocalRing.residue_eq_zero_iff _).1 ((mul_eq_zero.1 h2).resolve_right hεm)
  obtain ⟨hd1, hd2⟩ := (hs.2.2 d).1 d.2
  obtain ⟨hc1, -⟩ := (hs.2.2 c).1 c.2
  set d₁ : v.adicCompletionIntegers F := ⟨_, hd1⟩ with hd₁
  set d₂ : v.adicCompletionIntegers F := ⟨_, hd2⟩ with hd₂
  set c₁ : v.adicCompletionIntegers F := ⟨_, hc1⟩ with hc₁
  have m1 : d₁ - 1 ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) :=
    key (d - 1) _ (by simp [hd₁]) hd
  have mT : (T : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) :=
    key (T : intV E v) _ (by simp) (by rw [Nat.cast_smul_eq_nsmul, ← hM, card_nsmul_eq_zero'])
  have hrel : d₂ * d₁ = 1 + (T : v.adicCompletionIntegers F) * c₁ := by
    have h := congrArg (fun x => (s x).1) hc
    simp only [map_mul, map_add (f := _), map_one, map_natCast, hs.2.1] at h
    exact Subtype.ext (by simpa [hd₁, hd₂, hc₁, swapR] using h)
  have m2 : d₂ - 1 ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    have : d₂ - 1 = (T : v.adicCompletionIntegers F) * c₁ - d₂ * (d₁ - 1) := by
      linear_combination hrel
    rw [this]
    exact sub_mem (Ideal.mul_mem_right _ _ mT) (Ideal.mul_mem_left _ _ m1)
  obtain ⟨b₁, hb₁⟩ := hunif _ ((Valuation.mem_maximalIdeal_iff (v := Valued.v) (a := d₁ - 1)).1 m1)
  obtain ⟨b₂, hb₂⟩ := hunif _ ((Valuation.mem_maximalIdeal_iff (v := Valued.v) (a := d₂ - 1)).1 m2)
  refine ⟨⟨s.symm ((b₁ : v.adicCompletion F), (b₂ : v.adicCompletion F)), (hs.2.2 _).2 ?_⟩, s.injective ?_⟩
  · rw [s.apply_symm_apply]
    exact ⟨b₁.2, b₂.2⟩
  · have e1 : (s d).1 - 1 = (T : v.adicCompletion F) * b₁ := by
      have h := congrArg Subtype.val hb₁
      push_cast at h
      exact h
    have e2 : (s d).2 - 1 = (T : v.adicCompletion F) * b₂ := by
      have h := congrArg Subtype.val hb₂
      push_cast at h
      exact h
    rw [map_add (f := _), map_one, map_mul, map_natCast, s.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · simpa using sub_eq_iff_eq_add'.1 e1
    · simpa using sub_eq_iff_eq_add'.1 e2

end GlobalTheory.UnitaryScalarModT
end
