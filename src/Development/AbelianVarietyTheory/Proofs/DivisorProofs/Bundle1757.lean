module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1717
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle842
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_UL_of_split {n : ℕ} {w : Pl E} (hw : IsSplitAt w) (x : GLw n w) : x ∈ UL n w := by
  rw [UL, if_pos hw]; exact Subgroup.mem_top x

theorem toSub_eq {G : Type} [Group G] (H : Subgroup G) (g : G) (hg : g ∈ H) : toSub H g = ⟨g, hg⟩ := by
  simp [toSub, hg]

theorem ct_inv {a b n : ℕ} (h : a + b = n) (w : Pl E) (N : Subgroup (GLw n w)) (F : GLw n w → ℂ)
    (hNn : ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ x ∈ N, k⁻¹ * x * k ∈ N)
    (hF : ∀ y ∈ N, ∀ x, F (y * x) = F x ∧ F (x * y) = F x)
    (k : GLw a w × GLw b w) (hk1 : k.1 ∈ GlobalTheory.LFun.KGL w (n := a)) (hk2 : k.2 ∈ GlobalTheory.LFun.KGL w (n := b)) (hkN : dgM h w k ∈ N)
    (m : GLw a w × GLw b w) : ct h w F (k * m) = ct h w F m ∧ ct h w F (m * k) = ct h w F m := by
  have hab := GlobalTheory.T.absHalf_blockDet_integralGL_invariant E a b w m k hk1 hk2
  constructor
  · unfold ct
    rw [hab.1]
    congr 2
    funext X
    congr 1
    funext κ
    rw [(GlobalTheory.T.blockUpperTimesUnipotent_mul_blockDiagonal E a b n h w m k _).1]
    have e : (κ : GLw n w)⁻¹ * (dgM h w k * blk h w m (Multiplicative.toAdd X)) * κ =
        ((κ : GLw n w)⁻¹ * dgM h w k * κ) * ((κ : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * κ) := by group
    rw [e, (hF _ (hNn _ κ.2 _ hkN) _).1]
  · unfold ct
    have e : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        avg fun κ : GlobalTheory.LFun.KGL w (n := n) => F ((κ : GLw n w)⁻¹ * blk h w (m * k) (Multiplicative.toAdd X) * κ)) =
        fun X => avg fun κ : GlobalTheory.LFun.KGL w (n := n) => F ((κ : GLw n w)⁻¹ *
          blk h w m (Multiplicative.toAdd (Multiplicative.ofAdd (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val))) * κ) := by
      funext X
      congr 1
      funext κ
      rw [(GlobalTheory.T.blockUpperTimesUnipotent_mul_blockDiagonal E a b n h w m k _).2]
      have e : (κ : GLw n w)⁻¹ * (blk h w m (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val) * dgM h w k) * κ =
          ((κ : GLw n w)⁻¹ * blk h w m (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val) * κ) *
            ((κ : GLw n w)⁻¹ * dgM h w k * κ) := by group
      rw [e, (hF _ (hNn _ κ.2 _ hkN) _).2]
      rfl
    have hh := GlobalTheory.T.haarIntegralNormalized_integralMatrices_twoSidedMul E a b w (fun Y => avg fun κ : GlobalTheory.LFun.KGL w (n := n) =>
      F ((κ : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd Y) * κ)) k.1 k.2⁻¹ hk1 (inv_mem hk2)
    rw [hab.2, e, hh]

theorem ctMu_inv {a b n : ℕ} (h : a + b = n) (w : Pl E) (hw : IsSplitAt w) (N : Subgroup (GLw n w))
    (K' : Subgroup (UL n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ) (hf : IsHecke K' f)
    (hNK : N ≤ K'.map (UL n w).subtype) (hNn : ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ x ∈ N, k⁻¹ * x * k ∈ N)
    (k : GLw a w × GLw b w) (hk : k ∈ (lev₁ h w N μ).prod (lev₂ h w N μ)) (m : GLw a w × GLw b w) :
    ctMu h w μ f (k * m) = ctMu h w μ f m ∧ ctMu h w μ f (m * k) = ctMu h w μ f m := by
  obtain ⟨⟨⟨hk1, hkN1⟩, hkμ1⟩, ⟨⟨hk2, hkN2⟩, hkμ2⟩⟩ := hk
  have hkN : dgM h w k ∈ N := by
    have e : k = (k.1, 1) * (1, k.2) := by ext <;> simp
    rw [e, map_mul]
    exact N.mul_mem hkN1 hkN2
  have hF : ∀ y ∈ N, ∀ x, (fun y => f (toSub (UL n w) y)) (y * x) = (fun y => f (toSub (UL n w) y)) x ∧
      (fun y => f (toSub (UL n w) y)) (x * y) = (fun y => f (toSub (UL n w) y)) x := by
    intro y hy x
    obtain ⟨y', hy', rfl⟩ := hNK hy
    have e1 : toSub (UL n w) ((UL n w).subtype y' * x) = y' * toSub (UL n w) x := by
      rw [toSub_eq _ _ (mem_UL_of_split hw _), toSub_eq _ _ (mem_UL_of_split hw x)]; rfl
    have e2 : toSub (UL n w) (x * (UL n w).subtype y') = toSub (UL n w) x * y' := by
      rw [toSub_eq _ _ (mem_UL_of_split hw _), toSub_eq _ _ (mem_UL_of_split hw x)]; rfl
    exact ⟨by simp only; rw [e1]; exact (hf.2 y' hy' _).1, by simp only; rw [e2]; exact (hf.2 y' hy' _).2⟩
  have hc := ct_inv h w N (fun y => f (toSub (UL n w) y)) hNn hF k hk1 hk2 hkN m
  have hμ1 : μ (GeneralLinearGroup.det k.1) = 1 := hkμ1
  have hμ2 : μ (GeneralLinearGroup.det k.2) = 1 := hkμ2
  unfold ctMu
  rw [hc.1, hc.2]
  simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow, map_pow, hμ1, hμ2, one_pow, mul_one, one_mul]
  constructor <;> trivial

theorem ctMu_hecke : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E), IsSplitAt w → ∀ (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsOpen {x | μ x = 1} → ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' → ∃ (K₁ : Subgroup (GLw a w)) (K₂ : Subgroup (GLw (n - a) w)), IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) K₁ ∧ IsLevel (thL (n - a) w) (GlobalTheory.LFun.KGL w (n := (n - a))) K₂ ∧ ((K' = KL n w ∧ ∀ u ∈ (GlobalTheory.LFun.KGL w (n := 1)), μ (GeneralLinearGroup.det u) = 1) → K₁ = GlobalTheory.LFun.KGL w (n := a) ∧ K₂ = GlobalTheory.LFun.KGL w (n := (n - a))) ∧ ∀ f, IsHecke K' f → IsHecke (K₁.prod K₂) (ctMu (Nat.add_sub_cancel' ha) w μ f) ∧ ((∀ y, f y ≠ 0 → y.1.val.charpoly.Separable) → RegAt2 a (n - a) w (ctMu (Nat.add_sub_cancel' ha) w μ f)) := by
  intro E _ _ _ _ n a ha w hw μ hμ K' hK'
  obtain ⟨N, hNo, hNK, hNn, hNf⟩ := GlobalTheory.T.exists_open_conjStable_subgroup_of_splitLevel E n w K' hw hK'
  have hlev := GlobalTheory.T.isLevel_blockLevels_splitPlace E a (n - a) n (Nat.add_sub_cancel' ha) w N μ hw hNo hμ
  refine ⟨lev₁ (Nat.add_sub_cancel' ha) w N μ, lev₂ (Nat.add_sub_cancel' ha) w N μ, hlev.1, hlev.2, ?_,
    fun f hf => ⟨⟨GlobalTheory.T.hasCompactSupport_twistedConstantTermSplitPlace E a (n - a) n _ w μ f hw hf.1, fun k hk m =>
      ctMu_inv _ w hw N K' μ f hf hNK hNn k hk m⟩, GlobalTheory.T.twistedConstantTermSplitPlace_regular E a (n - a) n _ w μ f hw⟩⟩
  rintro ⟨hK'e, hμ1⟩
  rw [hNf hK'e]
  exact GlobalTheory.T.blockLevels_eq_integralGL_of_unramified E a (n - a) n _ w μ hμ1

end GlobalTheory.BCT.CtLevel
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical


open GlobalTheory.LocNormTau in
theorem GlobalTheory.LocNormTau.exists_norm_of_tau_fixed_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G (β : G.C) = β →
    ∀ (Y : G.Cˣ) (s : ℚ), (Y : G.C) * β * sh G (Y : G.C) = algebraMap ℚ G.C s * β →
    (minpoly G.F (Y : G.C)).Separable → (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∀ᶠ w : AwayP p in Filter.cofinite, ∀ m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) →
      IntC G w (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) → IntC G w ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) →
      inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) = m →
      ∃ v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) ∧
        (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = v * (inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G β hβ Y s hY hsep hdeg
  obtain ⟨f, hf0, hfc⟩ := exists_conj_neg G
  set e : G.C := algebraMap G.F G.C f with he_def
  set e' : G.C := algebraMap G.F G.C f⁻¹ with he'_def
  have hecomm : ∀ c : G.C, Commute e c := fun c => Algebra.commutes f c
  have he'comm : ∀ c : G.C, Commute e' c := fun c => Algebra.commutes f⁻¹ c
  have hee' : e * e' = 1 := by rw [he_def, he'_def, ← map_mul, mul_inv_cancel₀ hf0, map_one]
  have hsh_e : sh G e = -e := by
    simp only [sh, he_def, G.star_F, hfc, map_neg]
  have hsh_e' : sh G e' = -e' := by
    simp only [sh, he'_def, G.star_F, map_inv₀, hfc, inv_neg, map_neg]
  have hτe : (β : G.C) * sh G e * ((β⁻¹ : G.Cˣ) : G.C) = -e := by
    rw [hsh_e, mul_neg, neg_mul, (hecomm _).symm.eq, mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨L, _, _, _, _, ι, hιinj, hιrange⟩ := GlobalTheory.FixedCentraliserReg.fixed_algebra_exists p G β Y hsep hdeg
  have hee : e * e ∈ Set.range ι := by
    refine (hιrange _).2 ⟨(hecomm _).mul_left (hecomm _), ?_⟩
    rw [sh_mul, hsh_e, neg_mul_neg, ← ((hecomm (β : G.C)).mul_left (hecomm _)).eq, mul_assoc, Units.mul_inv,
      mul_one]
  have hee'' : e' * e' ∈ Set.range ι := by
    refine (hιrange _).2 ⟨(he'comm _).mul_left (he'comm _), ?_⟩
    rw [sh_mul, hsh_e', neg_mul_neg, ← ((he'comm (β : G.C)).mul_left (he'comm _)).eq, mul_assoc, Units.mul_inv,
      mul_one]
  obtain ⟨d, hd⟩ := hee
  obtain ⟨di, hdi⟩ := hee''
  have hddi : d * di = 1 := hιinj (by
    rw [map_mul, hd, hdi, map_one, mul_assoc, ← mul_assoc e e', hee', one_mul, hee'])
  have hne2 : ∀ᶠ w : AwayP p in Filter.cofinite, w.1.asIdeal ≠ Ideal.span {2} := by
    rw [Filter.eventually_cofinite]
    refine Set.Subsingleton.finite ?_
    intro w₁ h₁ w₂ h₂
    simp only [Set.mem_setOf_eq, not_not] at h₁ h₂
    exact Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext (h₁.trans h₂.symm))
  filter_upwards [hne2, GlobalTheory.T.eventually_isIntegral_of_integralCoordsLocalTensor p G, GlobalTheory.T.eventually_integralCoords_scalarTensorInclusion p G (ι d), GlobalTheory.T.eventually_integralCoords_scalarTensorInclusion p G (ι di)] with w h2 hint hId hId'
  intro m hmY hmI hmI' hmτ
  set K := w.1.adicCompletion ℚ
  obtain ⟨hΦinj, hΦrange⟩ := GlobalTheory.FinClsLoc.baseChange_fixedCentraliser_alg p G β Y L ι hιinj hιrange K
  set Φ := Algebra.TensorProduct.map (AlgHom.id K K) ι with hΦ
  have hmτ' : tauR G β K (m : K ⊗[ℚ] G.C) = m := hmτ
  have hm'τ : tauR G β K ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) = ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) := by
    have h1 : tauR G β K ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) * (m : K ⊗[ℚ] G.C) = 1 := by
      rw [← hmτ', ← tauR_mul, Units.mul_inv, tauR_one]
    calc _ = tauR G β K ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) * ((m : K ⊗[ℚ] G.C) * ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C)) := by
          rw [Units.mul_inv, mul_one]
      _ = _ := by rw [← mul_assoc, h1, one_mul]
  obtain ⟨y, hy⟩ := (hΦrange m).2 ⟨hmY, hmτ⟩
  obtain ⟨y', hy'⟩ := (hΦrange ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C)).2 ⟨hmY.units_inv_left, hm'τ⟩
  have hyy' : y * y' = 1 := hΦinj (by rw [map_mul, hy, hy', Units.mul_inv, map_one])
  set dK : K ⊗[ℚ] L := (1 : K) ⊗ₜ d
  set dK' : K ⊗[ℚ] L := (1 : K) ⊗ₜ di
  have hdd' : dK * dK' = 1 := by
    simp only [dK, dK', Algebra.TensorProduct.tmul_mul_tmul, one_mul, hddi]
    rfl
  have hΦd : Φ dK = inC G K (ι d) := by
    simp only [hΦ, dK, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  have hΦd' : Φ dK' = inC G K (ι di) := by
    simp only [hΦ, dK', Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  have pull : ∀ z : K ⊗[ℚ] L, IntC G w (Φ z) →
      ∃ g : Polynomial K, g.Monic ∧ (∀ i, g.coeff i ∈ w.1.adicCompletionIntegers ℚ) ∧ Polynomial.aeval z g = 0 := by
    intro z hz
    obtain ⟨g, hg1, hg2, hg3⟩ := hint _ hz
    refine ⟨g, hg1, hg2, hΦinj ?_⟩
    rw [← Polynomial.aeval_algHom_apply, hg3, map_zero]
  obtain ⟨a', b', hab⟩ := GlobalTheory.OddLocalNormEtale.exists_eq_sq_sub_mul_sq L w.1 h2 y y' dK dK' hyy' hdd'
    (pull y (by rw [hy]; exact hmI)) (pull y' (by rw [hy']; exact hmI'))
    (pull dK (by rw [hΦd]; exact hId)) (pull dK' (by rw [hΦd']; exact hId'))
  set a := Φ a'
  set b := Φ b'
  set E := inC G K e
  have haY := ((hΦrange a).1 ⟨a', rfl⟩).1
  have haτ : tauR G β K a = a := ((hΦrange a).1 ⟨a', rfl⟩).2
  have hbY := ((hΦrange b).1 ⟨b', rfl⟩).1
  have hbτ : tauR G β K b = b := ((hΦrange b).1 ⟨b', rfl⟩).2
  have hE : ∀ x : K ⊗[ℚ] G.C, Commute E x := commute_inC_of_forall G K e hecomm
  have hτE : tauR G β K E = -E := by
    rw [tauR_inC, hτe, map_neg]
  have habc : a * b = b * a := by
    simp only [a, b, ← map_mul, mul_comm a' b']
  have hEE : Φ dK = E * E := by rw [hΦd, hd, map_mul]
  have hm : (m : K ⊗[ℚ] G.C) = a * a - E * E * (b * b) := by
    rw [← hy, hab, map_sub, map_mul, map_mul, map_mul, hEE]
  set vv : K ⊗[ℚ] G.C := a + b * E
  have hτv : tauR G β K vv = a - E * b := by
    rw [tauR_add, tauR_mul, haτ, hbτ, hτE, neg_mul, sub_eq_add_neg]
  obtain ⟨key1, key2⟩ := norm_aux a b E (hE a) (hE b) habc
  rw [← hm] at key1 key2
  have hmv : Commute (m : K ⊗[ℚ] G.C) vv := by
    show (m : K ⊗[ℚ] G.C) * vv = vv * m
    calc (m : K ⊗[ℚ] G.C) * vv = vv * (a - E * b) * vv := by rw [key1]
      _ = vv * m := by rw [mul_assoc, key2]
  refine ⟨⟨vv, (a - E * b) * ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C), ?_, ?_⟩, ?_, ?_⟩
  · rw [← mul_assoc, key1, Units.mul_inv]
  · rw [mul_assoc, hmv.units_inv_left.eq, ← mul_assoc, key2, Units.mul_inv]
  · exact haY.add_left (hbY.mul_left (hE _))
  · change (m : K ⊗[ℚ] G.C) = vv * tauR G β K vv
    rw [hτv, key1]
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.equivariantDoubleCosetSection_mem_equivariant : ∀ (G H V : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G) (ρ : Representation ℂ H V) (K' : Subgroup G) (x : G) (v : V), secM ι ρ K' x v ∈ eqvM ι ρ K' := by
  first | exact @GlobalTheory.BCT.TraceBlocks.secM_mem_eqvM | exact GlobalTheory.BCT.TraceBlocks.secM_mem_eqvM | (intros; apply GlobalTheory.BCT.TraceBlocks.secM_mem_eqvM <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.heckeOperator_equivariantDoubleCosetSection_basePoint : ∀ (G H V : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G), Function.Injective ι → ∀ (ρ : Representation ℂ H V) (K K' : Subgroup G) (F : G → ℂ), (∀ k ∈ K', ∀ x, F (x * k) = F x) → {q : G ⧸ K' | F q.out ≠ 0}.Finite → ∀ x : G, Finite (ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G) → {h : H | F (x⁻¹ * ι h * x) ≠ 0}.Finite → ∀ v : V, levOp (rightReg ℂ G V) K K' F LinearMap.id (secM ι ρ K' x v) x = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ((stabCard ι K' x : ℂ))⁻¹ • ∑ᶠ h : H, F (x⁻¹ * ι h * x) • ρ h v := by
  first | exact @GlobalTheory.BCT.TraceBlocks.levOp_secM_apply_self | exact GlobalTheory.BCT.TraceBlocks.levOp_secM_apply_self | (intros; apply GlobalTheory.BCT.TraceBlocks.levOp_secM_apply_self <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.heckeOperator_preserves_equivariantRightInvariant : ∀ (G H V : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G) (ρ : Representation ℂ H V) (K K' : Subgroup G) (F : G → ℂ), (∀ k ∈ K', ∀ x, F (k * x) = F x ∧ F (x * k) = F x) → ∀ φ ∈ eqvM ι ρ K', levOp (rightReg ℂ G V) K K' F LinearMap.id φ ∈ eqvM ι ρ K' := by
  first | exact @GlobalTheory.BCT.TraceBlocks.levOp_rightReg_mem_eqvM | exact GlobalTheory.BCT.TraceBlocks.levOp_rightReg_mem_eqvM | (intros; apply GlobalTheory.BCT.TraceBlocks.levOp_rightReg_mem_eqvM <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker

namespace GlobalTheory.FlagPlucker

theorem det_mul_eq_sum_fun {R : Type} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det :=
  _root_.GlobalTheory.DeterminantProductExpansion.main A B

theorem exists_sum_minors_eq_one {R : Type} [CommRing R] {n k d : ℕ} (hd : d ≤ k) (A : Matrix (Fin n) (Fin k) R)
    (B : Matrix (Fin k) (Fin n) R) (hBA : B * A = 1) :
    ∃ c : (Fin d → Fin n) → R, ∑ r, c r * (A.submatrix r (Fin.castLE hd)).det = 1 := by
  have e : B.submatrix (Fin.castLE hd) id * A.submatrix id (Fin.castLE hd) = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, hBA,
      Matrix.submatrix_one _ (Fin.castLE_injective _)]
  refine ⟨fun r => ∏ a, B (Fin.castLE hd a) (r a), ?_⟩
  have := congrArg Matrix.det e
  rw [det_mul_eq_sum_fun, Matrix.det_one] at this
  exact this

end GlobalTheory.FlagPlucker

noncomputable section
namespace GlobalTheory.FlagPlucker

open GlobalTheory.FlagMod Formalism.L2.Pj MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X}

theorem exists_mul_plkU_eq_one (F : Frames Y π) (Mc : MChart Y) (k : F.J) (σ : E →+* ℂ) :
    ∃ B : Matrix (Fin (Dw.mult σ)) (Fin Mc.n) Γ(Z, F.U k ⊓ π ⁻¹ᵁ Mc.U), B * plkU F Mc k σ = 1 := by
  obtain ⟨w, hw⟩ := F.split k σ
  have hm : ∀ (M M' : MChart Y) (hle : F.U k ⊓ π ⁻¹ᵁ Mc.U ≤ π ⁻¹ᵁ (M.U ⊓ M'.U)) (S : Type) [CommRing S]
      (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ π ⁻¹ᵁ Mc.U)),
      ((chg M M').map (π.appLE _ _ hle).hom).map (ev z _ hz) =
        (chg M M').map (ev (z ≫ π) _ (le_preimage_map π hle hz)) := by
    intro M M' hle S _ z hz
    rw [Matrix.map_map]
    ext a b
    exact ev_appLE z π hle hz _ _
  have hle1 : F.U k ⊓ π ⁻¹ᵁ Mc.U ≤ π ⁻¹ᵁ ((F.M k).U ⊓ Mc.U) := fun _ hp => ⟨F.le k hp.1, hp.2⟩
  have hle2 : F.U k ⊓ π ⁻¹ᵁ Mc.U ≤ π ⁻¹ᵁ (Mc.U ⊓ (F.M k).U) := fun _ hp => ⟨hp.2, F.le k hp.1⟩
  have hC : (chg (F.M k).toMChart Mc).map (π.appLE _ _ hle1).hom *
      (chg Mc (F.M k).toMChart).map (π.appLE _ _ hle2).hom = 1 := by
    ext i j
    refine ext_ev fun S _ z hz => ?_
    have e : (((chg (F.M k).toMChart Mc).map (π.appLE _ _ hle1).hom *
        (chg Mc (F.M k).toMChart).map (π.appLE _ _ hle2).hom)).map (ev z _ hz) =
        (1 : Matrix (Fin (F.M k).n) (Fin (F.M k).n) Γ(Z, F.U k ⊓ π ⁻¹ᵁ Mc.U)).map (ev z _ hz) := by
      have hx := le_preimage_map π hle1 hz
      have hx' := le_preimage_map π hle2 hz
      rw [Matrix.map_mul, hm _ _ hle1, hm _ _ hle2,
        chg_map _ _ (z ≫ π) (le_preimage_mono inf_le_left hx) (le_preimage_mono inf_le_right hx),
        chg_map _ _ (z ≫ π) (le_preimage_mono inf_le_left hx') (le_preimage_mono inf_le_right hx'),
        Module.Basis.toMatrix_mul_toMatrix,
        Module.Basis.toMatrix_self, Matrix.map_one _ (map_zero _) (map_one _)]
    exact congrFun (congrFun e i) j
  refine ⟨(w.map (resG Z (inf_le_left : F.U k ⊓ π ⁻¹ᵁ Mc.U ≤ F.U k))) *
    (chg (F.M k).toMChart Mc).map (π.appLE _ _ hle1).hom, ?_⟩
  unfold plkU
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((chg (F.M k).toMChart Mc).map _), hC, Matrix.one_mul,
    ← Matrix.map_mul, hw, Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_mem_basicOpen_plkMinor (F : Frames Y π) (Mc : MChart Y) (k : F.J) (σ : E →+* ℂ)
    (m : Fin (Dw.mult σ)) (z : Z) (hz : z ∈ F.U k ⊓ π ⁻¹ᵁ Mc.U) :
    ∃ r, z ∈ Z.basicOpen (plkMinor F Mc k σ m r) := by
  obtain ⟨B, hB⟩ := exists_mul_plkU_eq_one F Mc k σ
  obtain ⟨cf, hc⟩ := exists_sum_minors_eq_one (d := (m : ℕ) + 1) m.2 _ B hB
  by_contra hno
  push_neg at hno
  have hmax : (Z.presheaf.germ _ z hz).hom (∑ r, cf r * plkMinor F Mc k σ m r) ∈
      IsLocalRing.maximalIdeal (Z.presheaf.stalk z) := by

    rw [map_sum]
    refine Ideal.sum_mem _ fun r _ => ?_
    rw [map_mul]
    refine Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu => hno r ?_)
    exact (Scheme.mem_basicOpen Z _ z hz).2 hu
  have h1 : ∑ r, cf r * plkMinor F Mc k σ m r = 1 := hc
  rw [h1, map_one] at hmax
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 hmax)

end GlobalTheory.FlagPlucker
end

noncomputable section
namespace GlobalTheory.FlagPlucker

open GlobalTheory.FlagMod Formalism.L2.Pj

theorem iSup_nonzeroLocus_plk : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U) (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) (t : Fin (plkNum Mc m + 1) → ((F.LL (ind σ m)).pull g).Sec), (∀ q, (t q).f = plkLoc F Mc g hg σ m q) → ⨆ q, nonzeroLocus (t q) = ⊤ := by
  intro E _ _ _ H Dw l Xo c O _ β Y Z π F Mc T g hg σ m t ht
  refine eq_top_iff.2 fun p _ => ?_
  obtain ⟨k, hk⟩ : ∃ k, g.base p ∈ F.U k := by
    have : g.base p ∈ (⨆ k, F.U k) := by rw [F.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hpM : g.base p ∈ π ⁻¹ᵁ Mc.U := by
    have := hg (show p ∈ (⊤ : T.Opens) from trivial)
    simpa using this
  obtain ⟨r, hr⟩ := exists_mem_basicOpen_plkMinor F Mc k σ m (g.base p) ⟨hk, hpM⟩
  let j : ((F.LL (ind σ m)).pull g).ι := fun _ => k
  have hpj : p ∈ ((F.LL (ind σ m)).pull g).U j := mem_pull.2 hk
  let q : Fin (plkNum Mc m + 1) := Fin.succ (Fintype.equivFin _ r)
  have hq : plkIdx Mc m q = some r := by simp [q, plkIdx]
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨q, (mem_nonzeroLocus_iff_basicOpen (t q) hpj).2 ?_⟩
  rw [congrFun (ht q) j]
  unfold plkLoc
  split
  · rename_i h; rw [hq] at h; exact absurd h (by simp)
  · rename_i r' h
    rw [hq] at h
    cases h
    rw [Scheme.basicOpen_appLE]
    exact ⟨hpj, hr⟩

end GlobalTheory.FlagPlucker
end
end

section

open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

namespace GlobalTheory.CovTop.VolUp.FrameBox

theorem boxEnt_norm_sq_eq {r : ℕ} (d : Fin r → ℝ) (hd : ∀ a, d a = 1 ∨ d a = -1) (z a b : Fin r)
    (hab : (a, b) ≠ (z, z)) :
    ∃ P Q : Fin r × Fin r, P ≠ Q ∧ ∀ p : Fin r × Fin r,
      ‖boxEnt d z a b p.1 p.2‖ ^ 2 = (if p = P then 1 else 0) + (if p = Q then 1 else 0) := by
  have hdd : ‖((d a * d b : ℝ) : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    rcases hd a with h | h <;> rcases hd b with h' | h' <;> simp [h, h']
  rcases lt_trichotomy a b with h | h | h
  · refine ⟨(a, b), (b, a), ?_, ?_⟩
    · intro e; simp only [Prod.mk.injEq] at e; exact h.ne e.1
    · rintro ⟨a', b'⟩
      simp only [boxEnt, if_pos h, Prod.mk.injEq]
      split_ifs <;> (try simp only [norm_neg, norm_mul, hdd, Complex.norm_I, norm_one, norm_zero]) <;> first | (norm_num; done) | (rename_i h1 h2; exact absurd (h1.1.symm.trans h2.1) h.ne)
  · subst h
    have haz : a ≠ z := fun e => hab (by rw [e])
    refine ⟨(a, a), (z, z), ?_, ?_⟩
    · intro e; simp only [Prod.mk.injEq] at e; exact haz e.1
    · rintro ⟨a', b'⟩
      simp only [boxEnt, lt_irrefl, if_false, Prod.mk.injEq]
      split_ifs <;> simp_all
  · refine ⟨(b, a), (a, b), ?_, ?_⟩
    · intro e; simp only [Prod.mk.injEq] at e; exact h.ne e.1
    · rintro ⟨a', b'⟩
      simp only [boxEnt, if_neg (not_lt.2 h.le), if_pos h, Prod.mk.injEq]
      split_ifs <;> (try simp only [norm_neg, norm_mul, hdd, Complex.norm_I, norm_one, norm_zero]) <;> first | (norm_num; done) | (rename_i h1 h2; exact absurd (h1.1.symm.trans h2.1) h.ne)

theorem norm_boxVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ k, ‖boxVec d z k‖ = √2 := by
  intro E _ _ _ r Ψ d z hd k
  obtain ⟨τ, ⟨⟨a, b⟩, hab⟩⟩ := k
  obtain ⟨P, Q, hPQ, hPn⟩ := boxEnt_norm_sq_eq (d τ) (hd τ) z a b hab
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · have : ∀ p : Fin r × Fin r, ‖(boxVec d z ⟨τ, ⟨(a, b), hab⟩⟩) (τ, p)‖ ^ 2 =
        (if p = P then 1 else 0) + (if p = Q then 1 else 0) := by
      intro p
      rw [← hPn p]
      simp [boxVec]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    norm_num
  · intro τ' _ hτ'
    apply Finset.sum_eq_zero
    intro p _
    simp [boxVec, hτ']
  · simp

end GlobalTheory.CovTop.VolUp.FrameBox
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

theorem _root_.GlobalTheory.T.pullback_basis_theta_eq_F0_form : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)), StandardLatticesGL3.pullB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') (GL3Theta.th0 (TaylorLogMetric.lamOf D cc δ) (B.ω₀ / 2)) z = F0 B.L B.ω₀ (Ix D n n') (phi B n n' z) := by
  first | exact @GlobalTheory.BaseVacuum.pullback_basis_theta_eq_F0 | exact GlobalTheory.BaseVacuum.pullback_basis_theta_eq_F0 | (intros; apply GlobalTheory.BaseVacuum.pullback_basis_theta_eq_F0 <;> assumption)
end
