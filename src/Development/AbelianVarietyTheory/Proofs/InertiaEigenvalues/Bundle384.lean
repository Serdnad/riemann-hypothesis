module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle089
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle126
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle088
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle082
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle087
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle098
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle169
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle146
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle167
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle198
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle142
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeAinfSandwichInvertPi
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle362
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle263
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle221
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle197
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle166
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle314
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisNormOfNonzero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle340
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle363
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle364
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition

@[expose] public section

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem admissible_params_of_roomy {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (h : Roomy L 100) :
    (L.etaSz + D.R.t + L.Sc + 2 < L.sc.w'' D.R.n ∧ L.sc.w'' D.R.n ≤ L.sc.b' ∧ 100 * L.sc.b' ≤ L.sc.b ∧
      (∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ 3 / 2 * L.sc.b') ∧ (D.R.t : ℝ) ≤ L.etaSz) ∧
      L.Sc + L.etaSz + D.R.t + 2 ≤ L.sc.b := by
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := h
  have he := L.etaSz_pos
  have hS := L.Sc_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hL : (0 : ℝ) ≤ (D.host.Lw : ℝ) := by positivity
  have hb : (0 : ℝ) ≤ L.sc.b' := by linarith
  have hm : (0 : ℝ) ≤ (D.host.Lw : ℝ) * L.sc.b' := mul_nonneg hL hb
  have h6 : 100 * L.sc.b' ≤ L.sc.b := by nlinarith
  refine ⟨⟨by linarith, h3, h6, h4, P.t_le_eta⟩, by linarith⟩

theorem admissible_params_large : ∀ eps A : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), L.sc.eps = eps → P.CLw ≤ A → x0 ≤ L.sc.x → (L.etaSz + D.R.t + L.Sc + 2 < L.sc.w'' D.R.n ∧ L.sc.w'' D.R.n ≤ L.sc.b' ∧ 100 * L.sc.b' ≤ L.sc.b ∧ (∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ 3 / 2 * L.sc.b') ∧ (D.R.t : ℝ) ≤ L.etaSz) ∧ L.Sc + L.etaSz + D.R.t + 2 ≤ L.sc.b := by
  intro eps A heps
  obtain ⟨x0, hx0⟩ := GlobalTheory.T.roomy_of_large_scale eps 100 A heps le_rfl
  exact ⟨x0, fun D L P h1 h2 h3 => admissible_params_of_roomy L P (hx0 D L P h1 h2 h3)⟩

end GlobalTheory.HTW
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.FitsEx

theorem exists_lift {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (i : B →+* C)
    (hi : Function.Injective i) (f : A →+* C) (h : ∀ x, ∃ y, f x = i y) :
    ∃ g : A →+* B, ∀ x, i (g x) = f x := by
  choose g hg using h
  exact ⟨{ toFun := g
           map_one' := hi (by rw [← hg, map_one, map_one])
           map_mul' := fun x y => hi (by rw [map_mul, ← hg, ← hg, ← hg, map_mul])
           map_zero' := hi (by rw [← hg, map_zero, map_zero])
           map_add' := fun x y => hi (by rw [map_add (f := _), ← hg, ← hg, ← hg, map_add (f := _)]) }, fun x => (hg x).symm⟩

variable {l : ℕ} [Fact l.Prime]

theorem eps_root {P : LocPrime l} (AI : LocAinf l P) (m : ℕ) :
    (rootT (l := l) AI.ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (P.ζQ m) := by
  have : rootT (l := l) AI.ε m = AI.ζ m := by
    refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
    refine ⟨AI.ζ (m + n), ?_, by rw [zeta_pow_iter AI.ζ_succ]⟩
    have := zeta_coeff_root_iterate (p := l) (O := Per.OC l) AI.ε m n
    rw [add_comm] at this
    exact (AI.ε_coeff (m + n)).symm.trans this.symm
  rw [this]
  exact AI.ζ_eq m

theorem isLog_unique {e : Per.Fl l} (he : e.untilt = 1) {y y' : Per.BdRp l}
    (h : Per.IsLog l e y) (h' : Per.IsLog l e y') :
    y = y' :=
  GlobalTheory.CrisIncl.log_unique l e he y y' h h'

theorem exists_finExt (x : Om l) : ∃ K : FinExt l, x ∈ K.1 :=
  ⟨⟨IntermediateField.adjoin ℚ_[l] {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩,
    IntermediateField.mem_adjoin_simple_self _ x⟩

theorem iota_alg (P : LocPrime l) (c : ↥(MaximalUnramifiedExtension l)) :
    P.ιB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap (Om l) P.R.BdR (c : Om l) := by
  obtain ⟨K, hK⟩ := exists_finExt (c : Om l)
  rw [← P.PD_ι K]
  exact (P.PD K).ι.commutes (⟨c, hK, c.2⟩ : ↥(K0 K))

theorem iota_inj (P : LocPrime l) : Function.Injective P.ιB := by
  obtain ⟨K, -⟩ := exists_finExt (0 : Om l)
  intro a b h
  exact (P.PD K).ι_inj (by rw [P.PD_ι, P.PD_ι, h])

theorem phi_alg {P : LocPrime l} (AI : LocAinf l P) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l))
    (hσ : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l) (c : ↥(MaximalUnramifiedExtension l)) :
    P.φB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (σ c) := by
  have key : P.φB.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B) =
      (IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B).comp σ := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ_[l] (S := MaximalUnramifiedExtension l) rfl fun x hx => ?_
    obtain ⟨m, hm, hlm, hxm⟩ := id hx
    obtain ⟨xb, hxb⟩ := exists_isTiltOf x m hm hlm hxm
    have hx' : x ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ hx
    have h1 := AI.ιA_teich ⟨x, hx'⟩ m hm hlm hxm xb hxb
    change P.φB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨x, hx'⟩) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (σ ⟨x, hx'⟩)
    rw [hσ ⟨x, hx'⟩ m hm hlm (Subtype.ext hxm), map_pow, ← h1, ← AI.ιA_φ, ← map_pow,
      WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  exact DFunLike.congr_fun key c

theorem sigma_eq {P : LocPrime l} (AI : LocAinf l P) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l))
    (hσ : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l)
    (K : FinExt l) (x : ↥(K0 K)) (c : ↥(MaximalUnramifiedExtension l)) (h : (c : Om l) = (x : Om l)) :
    (((P.PD K).σ x : ↥(K0 K)) : Om l) = ((σ c : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  have : Nontrivial P.R.B := by
    refine ⟨⟨1, 0, fun h0 => one_ne_zero (AI.ιA_inj ?_)⟩⟩
    rw [map_one, map_zero, h0]
  have h1 := (P.PD K).φ_K₀ x
  rw [P.PD_φ] at h1
  have hc : c = ⟨x, x.2.2⟩ := Subtype.ext h
  have h2 := phi_alg AI σ hσ c
  rw [hc] at h2 ⊢
  have h3 : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨((P.PD K).σ x : ↥(K0 K)), ((P.PD K).σ x).2.2⟩ = _ := h1.symm.trans h2
  exact congrArg Subtype.val ((algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective h3)

theorem zeta_prim (P : LocPrime l) (m : ℕ) : IsPrimitiveRoot (P.ζQ (m + 1)) (l ^ (m + 1)) := by
  have h0 := zeta_pow_iter P.ζQ_succ 0 (m + 1)
  rw [zero_add, P.ζQ_zero] at h0
  have h1 := zeta_pow_iter P.ζQ_succ 1 m
  rw [add_comm] at h1
  have := orderOf_eq_prime_pow (x := P.ζQ (m + 1)) (p := l) (n := m) (by rw [h1]; exact P.ζQ_one) h0
  rw [← this]
  exact IsPrimitiveRoot.orderOf _

theorem chi_eq (P : LocPrime l) (χ : GQ l →* ℤ_[l]ˣ)
    (hχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val)
    (g : GQ l) : ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) = (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have key : ∀ m : ℕ, ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])‖ ≤
      (l : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) := by
    intro m
    have hp := zeta_prim P m
    obtain ⟨a, ha, hg⟩ := P.χQ_cyc g (m + 1) _ hp.pow_eq_one
    rw [hχ g (m + 1) _ hp.pow_eq_one] at hg
    have hmod : (PadicInt.toZModPow (m + 1) (χ g : ℤ_[l])).val ≡ a [MOD l ^ (m + 1)] := by
      have hfin : IsOfFinOrder (P.ζQ (m + 1)) :=
        isOfFinOrder_iff_pow_eq_one.2 ⟨_, pow_pos (Fact.out : l.Prime).pos _, hp.pow_eq_one⟩
      have := hfin.pow_eq_pow_iff_modEq.1 hg
      rwa [← hp.eq_orderOf] at this
    have hk : ((a : ℤ_[l]) - (χ g : ℤ_[l])) ∈ Ideal.span {(l : ℤ_[l]) ^ (m + 1)} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
        ← (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod]
      have : NeZero (l ^ (m + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
      rw [ZMod.natCast_zmod_val, sub_self]
    have hn := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).2 hk
    have hn' : ‖(a : ℚ_[l]) - (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) := by
      simpa [PadicInt.norm_def] using hn
    rw [← sub_add_sub_cancel _ (a : ℚ_[l])]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hn')
  by_contra hne
  have hpos := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl)
  have h1 := key n
  rw [zpow_neg, zpow_natCast, ← inv_pow] at h1
  have h2 : (l : ℝ)⁻¹ ^ (n + 1) ≤ (l : ℝ)⁻¹ ^ n :=
    pow_le_pow_of_le_one (by positivity) (inv_lt_one_of_one_lt₀ hl).le (Nat.le_succ n)
  linarith

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem exists_fits : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ C : Core l, Fits T C := by
  intro l _ P AI T
  have hinj := (BdRField.bdR_isField l).2.1
  obtain ⟨o, ho⟩ := exists_lift _ hinj (T.eD.toRingHom.comp (algebraMap (Om l) P.R.BdR))
    fun x => (T.om x).imp fun _ h => h.1
  have hosec : IsSec o := by
    refine ⟨fun x => ?_, fun z => hinj ?_⟩
    · obtain ⟨y, hy, hy'⟩ := T.om x
      rw [← hy', hinj ((ho x).trans hy)]
    · rw [ho]
      change T.eD (algebraMap (Om l) P.R.BdR _) = _
      rw [← IsScalarTower.algebraMap_apply, T.zD]
      exact GlobalTheory.RingIface.zD_eq_alg l z
  have hincl := T.incl
  set ι := (T.eD.toRingHom.comp (P.ιB : P.R.B →+* P.R.BdR)).comp T.eB.symm.toRingHom with hι
  have hιe : ∀ b : P.R.B, T.eD (P.ιB b) = ι (T.eB b) := fun b => by simp [hι]
  clear_value ι
  obtain ⟨j, hj', hj0, hjb⟩ := GlobalTheory.CrisIncl.exists_restrict l ι hincl
  have hj : ∀ x, algebraMap (Per.BdRp l) (Per.BdR l) (j x) =
      (ι.comp (algebraMap (Per.Acris l) (Per.Bcris l))) x := fun x => (hj' x).symm
  have hjc : IsCrisP j := ⟨hj0, hjb⟩
  have he : PreTilt.untilt (AI.ε : Per.Fl l) = 1 := Subtype.ext (by
    have := eps_root AI 0
    rw [P.ζQ_zero, map_one] at this
    exact this)
  obtain ⟨t, -, ht, -⟩ := exists_isLogA l AI.ε he
  obtain ⟨σ, hσ⟩ := exists_frobenius_Kur l
  obtain ⟨χ, hχ⟩ := exists_cyclotomicChar l
  refine ⟨{ ζ := P.ζQ, ζ_zero := P.ζQ_zero, ζ_succ := P.ζQ_succ, ζ_one := P.ζQ_one
            ε := AI.ε, ε_root := eps_root AI, o := o, o_sec := hosec, j := j, j_cris := hjc
            ι := ι, ι_j := fun x => (hj x).symm
            u := T.eB.toRingHom.comp (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)
            ι_u := fun c => ?_
            t := t, t_log := ht, σ := σ, σ_root := hσ, χ := χ, χ_cyc := hχ },
    ⟨rfl, rfl, fun x => (ho x).symm, hιe, fun _ => rfl, ?_, chi_eq P χ hχ, sigma_eq AI σ hσ⟩⟩
  · rw [ho]
    exact (hιe _).symm.trans (congrArg T.eD (iota_alg P c))
  · obtain ⟨y, hy, hy'⟩ := T.t
    have h1 := isLog_unique he hy ((LogFun.log_fun l AI.ε t he ht).2.2.2 j hjc)
    have h2 : T.eD (P.ιB P.tB) = T.eD (P.ιB (T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) t))) := by
      rw [hy', h1, hj, hιe, RingEquiv.apply_symm_apply]
      rfl
    rw [iota_inj P (T.eD.injective h2), RingEquiv.apply_symm_apply]
    rfl

end GlobalTheory.MemLoc.FitsEx
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem fourierMatchAt_of_weil (hW : WeilEt) (hR : RankOne) (hG : GammaOne) {r : ℕ} {F E : Type}
    [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (M : Meas r F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (f' : Gl r F → ℂ) (f : Hn r F E → ℂ)
    (hf' : IsTest f') (hf : IsTest f) (hm : Match M f' f) (a : Inv r F) (ha : Delta a ≠ 0)
    (hsep : (companion a.1).charpoly.Separable) :
    MatchAt M (fourG M ψ f') (fourU M ψ f) a := by
  obtain ⟨A, τ, hτ⟩ := GlobalTheory.T.exists_etaleHermitianPair_isGen_companion F E r a.1 hsep
  obtain ⟨hbij, hmom⟩ := GlobalTheory.T.jacquetRallis_invK_regular_iff_isUnit F E A r τ a.1 a.2.2 hτ
  obtain ⟨a₀, ha₀⟩ := hbij.2 a.2.1
  have ha₀' : (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * a₀)) = a.2.1 := ha₀
  have hinv : A.invK τ a.1 a.2.2 a₀ = a := by
    simp only [Et.invK, ha₀']
  have hu₀ : IsUnit a₀ := (hmom a₀).2.mp (by rw [hinv]; exact ha)
  obtain ⟨⟨m⟩, -⟩ := GlobalTheory.T.exists_selfDual_measures_and_absK_scale F E A ψ hψ
  obtain ⟨-, -, -, -, -, -, ⟨S, -, hS⟩, -⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  obtain ⟨φ', κ, hφ', hlin⟩ := GlobalTheory.T.jacquetRallis_linear_orbitalIntegral_descent F E A ψ hψ m r M τ a.1 a.2.2 hτ f' hf'
  obtain ⟨-, -, huniq, -⟩ := GlobalTheory.T.unitary_action_hermitian_invariants_transitive F E r
  obtain ⟨-, horbU, -, -⟩ := GlobalTheory.T.jacquetRallisOrbitalIntegrals_invariant_locallyConstant F E r M
  obtain ⟨hL11a, hL11b⟩ := GlobalTheory.T.hermitianBlock_invariants_iff_isometry F E A r τ a.1 a.2.2 hτ
  have key : ∀ x : A.Kˣ, ∃ φx : A.L → ℂ, IsTest φx ∧
      ((∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j) →
        ∃ (j : A.L ≃ₗ[E] (Fin r → E)) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)), A.IsIsom (x : A.K) j ∧
          (∀ y, HasInv ((Ax, j y, a.2.2) : Hn r F E) (A.invK τ a.1 a.2.2 ((x : A.K) * A.NL y))) ∧
          ∀ y : A.L, IsUnit y → orbU M f (Ax, j y, a.2.2) = A.orbL m.ν φx y ∧
            orbU M (fourU M ψ f) (Ax, j y, a.2.2) = A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) φx) y) ∧
      ((¬ ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j) → φx = 0) := by
    intro x
    by_cases hx : ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j
    · obtain ⟨j, hj⟩ := hx
      obtain ⟨Ax, hAx, hinvAx⟩ := hL11b (x : A.K) j hj
      obtain ⟨φx, hφx, hrel⟩ := GlobalTheory.T.exists_test_orbU_eq_orbL F E A ψ hψ m r M τ a.1 a.2.2 hτ x j hj Ax hAx f hf
      exact ⟨φx, hφx, fun _ => ⟨j, Ax, hj, hinvAx, hrel⟩, fun h => absurd ⟨j, hj⟩ h⟩
    · exact ⟨0, ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩, fun h => absurd h hx, fun _ => rfl⟩
  choose φ hφt hφi hφ0 using key
  choose γ Wr hWr using fun x : A.Kˣ => hW F E A ψ hψ x (m.μL x) (m.sdL x)
  have hunit : ∀ (x : A.Kˣ) (y : A.L), IsUnit y → IsUnit ((x : A.K) * A.NL y) := fun x y hy =>
    x.isUnit.mul (hy.map (Algebra.norm A.K))
  have hyp : ∀ x ∈ S, ∀ y : A.L, IsUnit y → κ * A.orbK m.μK φ' (x * A.NL y) = A.orbL m.ν (φ x) y := by
    intro x _ y hy
    have hb := hunit x y hy
    rw [← (hlin _ hb).1]
    by_cases hx : ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j
    · obtain ⟨j, Ax, -, hinvAx, hrel⟩ := hφi x hx
      rw [← (hrel y hy).1]
      exact (hm _ ((hmom _).2.mpr hb)).1 _ (hinvAx y)
    · rw [hφ0 x hx]
      have h0 : orbG M f' (sec (A.invK τ a.1 a.2.2 ((x : A.K) * A.NL y))) = 0 := by
        apply (hm _ ((hmom _).2.mpr hb)).2
        rintro ⟨X, hX⟩
        obtain ⟨j, hj, -⟩ := hL11a _ X hb hX (x : A.K) y hy rfl
        exact hx ⟨j, hj⟩
      rw [h0]
      simp [Et.orbL]
  have hRk := hR F E A ψ hψ m S hS γ Wr (fun x _ => hWr x) φ' φ κ hφ' (fun x _ => hφt x) hyp
  have hG1 : ∀ (x : A.Kˣ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom (x : A.K) j → γ x = 1 :=
    fun x j hj => hG F E A ψ hψ x (m.μL x) (m.sdL x) A.etaK (γ x) (Wr x) (hWr x) r j hj
  obtain ⟨x, ⟨hxS, y, hy, hxy⟩, -⟩ := hS hu₀.unit
  have hxy' : a₀ = x * A.NL y := by simpa using hxy
  have hb := hunit x y hy
  have hlhs : orbG M (fourG M ψ f') (sec a) =
      γ x * A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) (φ x)) y := by
    calc orbG M (fourG M ψ f') (sec a)
        = orbG M (fourG M ψ f') (sec (A.invK τ a.1 a.2.2 ((x : A.K) * A.NL y))) := by rw [← hxy', hinv]
      _ = κ * A.orbK m.μK (A.fourK m.μK ψ φ') ((x : A.K) * A.NL y) := (hlin _ hb).2
      _ = _ := hRk x hxS y hy
  constructor
  · intro X hX
    have hX' : HasInv X (A.invK τ a.1 a.2.2 a₀) := by rw [hinv]; exact hX
    obtain ⟨j₁, hj₁, -⟩ := hL11a a₀ X hu₀ hX' (x : A.K) y hy hxy'
    obtain ⟨j, Ax, hj, hinvAx, hrel⟩ := hφi x ⟨j₁, hj₁⟩
    have hXa : HasInv ((Ax, j y, a.2.2) : Hn r F E) a := by
      have := hinvAx y
      rw [← hxy', hinv] at this
      exact this
    obtain ⟨g, hg, -⟩ := huniq _ X a ha hXa hX
    rw [hlhs, hG1 x j hj, one_mul, ← (hrel y hy).2, ← hg, horbU]
  · intro hno
    have hx : ¬ ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j := by
      intro hx
      obtain ⟨j, Ax, -, hinvAx, -⟩ := hφi x hx
      have := hinvAx y
      rw [← hxy', hinv] at this
      exact hno ⟨_, this⟩
    rw [hlhs, hφ0 x hx]
    simp [fourB, Et.orbL]

theorem fourierMatch_of_weil : WeilEt → RankOne → GammaOne → ∀ r, FourierMatch r := by
  intro hW hR hG r F E _ _ _ _ _ M ψ hψ f' f hf' hf hm
  obtain ⟨h4G, h4U, -⟩ := GlobalTheory.T.partialFourier_preserves_test_fixes_unit F E r M ψ hψ
  exact (GlobalTheory.T.jacquetRallis_match_of_dense_separable F E r M _ _ (h4G f' hf') (h4U f hf)).1
    (fun a ha hsep => fourierMatchAt_of_weil hW hR hG M ψ hψ f' f hf' hf hm a ha hsep)

end GlobalTheory.JR
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.wachLattice_ainf_sandwich_invert_pi : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (E : WEt I) (Mo : NS E) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ → ∃ m : ℕ, Sand Mo T ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL) := by
  first | exact @GlobalTheory.HWL.SandProof.sandwich | exact GlobalTheory.HWL.SandProof.sandwich | (intros; apply GlobalTheory.HWL.SandProof.sandwich <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.wildJumpSum_le_of_detecting_coboundary_characters : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → AxIn K L p → Detects p r A B → jumpSum (wild K L) A B ≤ 6 * E := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_le_of_detects | exact GlobalTheory.PMon.Ram.jumpSum_le_of_detects | (intros; apply GlobalTheory.PMon.Ram.jumpSum_le_of_detects <;> assumption)
end

section

noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem log_interp (a b c : ℝ) (h : b - a ≠ 0) :
    a * ((b - c) / (b - a)) + b * (1 - (b - c) / (b - a)) = c := by
  field_simp
  ring

theorem gC_pos_of_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ →
    ρ < 1 → 0 < gC l ρ x := by
  intro l _ x hx ρ hρ0 hρ1
  have hN : ∀ r : ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → IsGauss l r (gC l r) :=
    fun r h0 h1 => isGauss_gC_target l r h0 h1
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hi0 : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hi1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  have hnn : ∀ r, (l : ℝ)⁻¹ ≤ r → r < 1 → 0 ≤ gC l r x := fun r h0 h1 => ((hN r h0 h1).1 x).1
  have h0 : gC l (l : ℝ)⁻¹ x ≠ 0 := GlobalTheory.MemLoc.gauss_ne_zero l (fun r => gC l r) hN x hx
  rcases hρ0.eq_or_lt with h | h
  · subst h
    exact lt_of_le_of_ne (hnn _ le_rfl hi1) h0.symm
  by_contra hneg
  have hz : gC l ρ x = 0 := le_antisymm (not_lt.1 hneg) (hnn ρ hρ0 hρ1)
  obtain ⟨r₁, c, k, hr₁, -, hc, hmon⟩ := GlobalTheory.MemLoc.gauss_slope l (fun r => gC l r) hN x h0
  obtain ⟨ρ', h1', h2'⟩ := exists_between (lt_min hr₁ h)
  have hρ'0 : 0 < ρ' := hi0.trans h1'
  have hρ'r : ρ' < r₁ := h2'.trans_le (min_le_left _ _)
  have hρ'ρ : ρ' < ρ := h2'.trans_le (min_le_right _ _)
  have hρpos : 0 < ρ := hi0.trans h
  have hpos : 0 < gC l ρ' x := by
    have e : gC l ρ' x = c * ρ' ^ k := hmon ρ' h1' hρ'r
    rw [e]
    exact mul_pos hc (zpow_pos hρ'0 k)
  have hL1 : Real.log (l : ℝ)⁻¹ < Real.log ρ' := Real.log_lt_log hi0 h1'
  have hL2 : Real.log ρ' < Real.log ρ := Real.log_lt_log hρ'0 hρ'ρ
  have hd : 0 < Real.log ρ - Real.log (l : ℝ)⁻¹ := by linarith
  have ht0 : 0 ≤ (Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹) :=
    div_nonneg (by linarith) hd.le
  have ht1 : (Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹) < 1 :=
    (div_lt_one hd).2 (by linarith)
  have he : (l : ℝ)⁻¹ ^ ((Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹)) *
      ρ ^ (1 - (Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹)) = ρ' := by
    rw [Real.rpow_def_of_pos hi0, Real.rpow_def_of_pos hρpos, ← Real.exp_add,
      log_interp _ _ _ hd.ne', Real.exp_log hρ'0]
  have hcv := GlobalTheory.T.gaussNormAcris_logConvex_in_radius l x (l : ℝ)⁻¹ ρ _ le_rfl h.le hρ1 ht0 ht1.le
  rw [he, hz, Real.zero_rpow (sub_pos.2 ht1).ne', mul_zero] at hcv
  linarith

theorem gC_pos_target : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 →
    0 < gC l ρ x :=
  gC_pos_of_ne_zero

end GlobalTheory.PMon.Gauss

end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual



theorem _root_.GlobalTheory.T.liftAll_subSums_of_liftFamily_matrixFamily : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (e : ℕ)
    (A A' : GRep G Qp LL O), LiftFam (O := O) PD Ms e → IsSubFam Ms A → IsSubFam Ms A' → BlochKatoDuality.LiftAll PD A A' e := by
  first | exact @GlobalTheory.Pass.LocDual.liftAll_of_liftFam | exact GlobalTheory.Pass.LocDual.liftAll_of_liftFam | (intros; apply GlobalTheory.Pass.LocDual.liftAll_of_liftFam <;> assumption)
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.groupAlgebraTrace_patternIdempotent_exchange : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ), N = k + 2 * s + 1 → ∀ χ : Gn g N → ℂ, IsClass χ → tr (eJ g N k s ψ) χ = tr (eJ' g N k ψ) χ := by
  first | exact @GlobalTheory.GLq.tr_eJ_eq_tr_eJ' | exact GlobalTheory.GLq.tr_eJ_eq_tr_eJ' | (intros; apply GlobalTheory.GLq.tr_eJ_eq_tr_eJ' <;> assumption)
end
