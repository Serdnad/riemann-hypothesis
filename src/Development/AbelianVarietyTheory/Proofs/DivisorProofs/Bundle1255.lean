module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1178
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle014
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration

@[expose] public section

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

noncomputable section

namespace GlobalTheory.WeylCell.U21TorusFactor

open Formalism.UG

theorem swap_rev_comm {n : ℕ} (a i : Fin n) :
    Equiv.swap a a.rev i.rev = (Equiv.swap a a.rev i).rev := by
  rcases eq_or_ne i a with rfl | h1
  · simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rcases eq_or_ne i a.rev with rfl | h2
  · simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne]
  · exact fun h => h2 (by rw [← h, Fin.rev_rev])
  · exact fun h => h1 (Fin.rev_injective h)

theorem conj_diag_apply {R : Type} [CommRing R] {n : ℕ} (s : Equiv.Perm (Fin n))
    (Y Yi T : Matrix (Fin n) (Fin n) R) (hinv : Yi * Y = 1)
    (hY : ∀ i j, i ≠ s j → Y i j = 0) (hYi : ∀ i j, j ≠ s i → Yi i j = 0)
    (hT : ∀ i j, i ≠ j → T i j = 0) (i j : Fin n) :
    (Yi * T * Y) i j = if i = j then T (s i) (s i) else 0 := by
  have e1 : (Yi * T * Y) i j = Yi i (s j) * T (s j) (s j) * Y (s j) j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (s j)]
    · rw [Matrix.mul_apply, Finset.sum_eq_single (s j)]
      · intro p _ hp; rw [hT p (s j) hp, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro r _ hr; rw [hY r j hr, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [e1]
  split_ifs with hij
  · subst hij
    have e2 : (Yi * Y) i i = Yi i (s i) * Y (s i) i := by
      rw [Matrix.mul_apply, Finset.sum_eq_single (s i)]
      · intro p _ hp; rw [hY p i hp, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hinv, Matrix.one_apply_eq] at e2
    calc Yi i (s i) * T (s i) (s i) * Y (s i) i = T (s i) (s i) * (Yi i (s i) * Y (s i) i) := by ring
      _ = T (s i) (s i) := by rw [← e2, mul_one]
  · rw [hYi i (s j) (fun h => hij (s.injective h).symm), zero_mul, zero_mul]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_inv (z : L) : ordL z⁻¹ = -ordL z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [ordL]
  have h1 := GlobalTheory.BorelUMod.v_eq_exp (inv_ne_zero hz)
  rw [map_inv₀, GlobalTheory.BorelUMod.v_eq_exp hz, ← WithZero.exp_neg, WithZero.exp_inj] at h1
  linarith

theorem ordL_map {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (z : L) : ordL (σ z) = ordL z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hz' : σ z ≠ 0 := (map_ne_zero σ).2 hz
  have h1 := hσ z
  rw [GlobalTheory.BorelUMod.v_eq_exp hz, GlobalTheory.BorelUMod.v_eq_exp hz', WithZero.exp_inj] at h1
  linarith

end GlobalTheory.WeylCell.U21TorusFactor

namespace GlobalTheory.WeylCell.U21TorusFactor

open Formalism.UG

theorem torus_factor : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ (α : Fin (n / 2) → ℂˣ) (φ : GU σ n → ℂ), IsSphericalU q (fun i => (α i : ℂ)) φ →
    ∀ t : GU σ n, (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) → ∀ w x : GU σ n,
      φ (y⁻¹ * t * w * x) * (q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) =
        chiDeltaU q (fun i => (actU k α i : ℂ)) t * φ (y⁻¹ * w * x) := by
  intro L _ _ _ ϖ σ q hU n k hk hn y hy hw α φ hφ t ht w x
  have hσv : ∀ z, Valued.v (σ z) = Valued.v z := hU.2.1
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  have hs : simpleU k = Equiv.swap (lo k) (lo k).rev := by
    rw [simpleU, if_neg hk]
  set a : Fin n := lo k with ha
  have hkv : k.val = n / 2 - 1 := by have := k.2; omega
  have hodd : n % 2 = 1 := by
    rcases Nat.even_or_odd n with h | h
    · exact absurd h hn
    · exact Nat.odd_iff.1 h
  have hav : a.val = k.val := rfl
  have hrv : (a.rev).val = n - 1 - k.val := by rw [Fin.val_rev, hav]; omega

  set Y : Matrix (Fin n) (Fin n) L := (((y : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hYd
  set Yi : Matrix (Fin n) (Fin n) L := ((((y : GU σ n) : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hYid
  set T : Matrix (Fin n) (Fin n) L := (((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hTd
  have hinv : Yi * Y = 1 := by
    rw [hYid, hYd, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hYw : ∀ i j, i ≠ Equiv.swap a a.rev j → Y i j = 0 := by
    intro i j h; rw [← hs] at h; exact hw i j h
  have hYi : ∀ i j, j ≠ Equiv.swap a a.rev i → Yi i j = 0 := by
    intro i j h
    have hm := (GlobalTheory.LGrp.mem_GU_iff σ n _).1 (y : GU σ n).2 i j
    rw [hYid, hm]
    have : j.rev ≠ Equiv.swap a a.rev i.rev := by
      rw [swap_rev_comm]; exact fun h' => h (Fin.rev_injective h')
    exact (congrArg σ (hYw _ _ this)).trans (map_zero σ)
  set b : GU σ n := y⁻¹ * t * y with hbd
  have hb : ∀ i j, (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      if i = j then T (Equiv.swap a a.rev i) (Equiv.swap a a.rev i) else 0 := by
    intro i j
    have : (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Yi * T * Y := by
      simp [hbd, hYid, hYd, hTd, Units.val_mul]
    rw [this]
    exact conj_diag_apply _ Y Yi T hinv hYw hYi ht i j
  have hB : IsBorelU b := by
    intro i j hij
    rw [hb, if_neg (ne_of_gt hij)]
  have hsph := hφ b (y⁻¹ * w * x) 1 hB (one_mem _)
  have hprod : y⁻¹ * t * w * x = b * (y⁻¹ * w * x) * 1 := by
    rw [hbd]; group

  have hTa : T a a ≠ 0 ∧ ordL (T a.rev a.rev) = -ordL (T a a) := by
    set Ti : Matrix (Fin n) (Fin n) L := ((((t : GU σ n) : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hTid
    have h1 : T * Ti = 1 := by
      rw [hTid, hTd, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : (T * Ti) a a = T a a * Ti a a := by
      rw [Matrix.mul_apply, Finset.sum_eq_single a]
      · intro p _ hp; rw [ht a p (Ne.symm hp), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1, Matrix.one_apply_eq] at h2
    have hne : T a a ≠ 0 := by intro h0; rw [h0, zero_mul] at h2; exact one_ne_zero h2
    have hTi : Ti a a = (T a a)⁻¹ := by
      exact eq_inv_of_mul_eq_one_right h2.symm
    have hm := (GlobalTheory.LGrp.mem_GU_iff σ n _).1 (t : GU σ n).2 a a
    rw [← hTid, hTi] at hm
    refine ⟨hne, ?_⟩
    rw [← ordL_map hσv (T a.rev a.rev)]
    exact (congrArg ordL hm.symm).trans (ordL_inv _)

  have e : ∀ (β : Fin (n / 2) → ℂ) (g : GU σ n), chiDeltaU q β g =
      ∏ i : Fin (n / 2), β i ^ ordL ((((g : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i)) *
        (q : ℂ) ^ (-(ordL ((((g : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i))) *
          ((n : ℤ) - 1 - 2 * (i.val : ℤ))) := by
    intro β g
    unfold chiDeltaU
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [dite_eq_left (by have := i.2; omega)]
    rfl
  have hact : ∀ i, (actU k α i : ℂ) = if i = k then (α k : ℂ)⁻¹ else α i := by
    intro i
    unfold actU
    rw [dite_eq_right hk]
    by_cases hi : i = k
    · subst hi; simp [Function.update_self, Units.val_inv_eq_inv_val]
    · simp [Function.update_of_ne hi, hi]
  have key : chiDeltaU q (fun i => (α i : ℂ)) b * (q : ℂ) ^ (-4 * ordL (T (lo k) (lo k))) =
      chiDeltaU q (fun i => (actU k α i : ℂ)) t := by
    rw [e, e, Fintype.prod_eq_mul_prod_compl k, Fintype.prod_eq_mul_prod_compl k]
    have hrest : ∏ i ∈ ({k}ᶜ : Finset (Fin (n / 2))),
        (α i : ℂ) ^ ordL ((((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i)) *
          (q : ℂ) ^ (-(ordL ((((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i))) *
            ((n : ℤ) - 1 - 2 * (i.val : ℤ))) =
        ∏ i ∈ ({k}ᶜ : Finset (Fin (n / 2))),
        (actU k α i : ℂ) ^ ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i)) *
          (q : ℂ) ^ (-(ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i))) *
            ((n : ℤ) - 1 - 2 * (i.val : ℤ))) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hik : i ≠ k := by simpa using hi
      have hfix : Equiv.swap a a.rev (lo i) = lo i := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h; apply hik; ext; have := congrArg Fin.val h; simpa [ha] using this
        · intro h; have := congrArg Fin.val h; rw [hrv] at this
          have h3 : (lo i : Fin n).val = i.val := rfl
          have := i.2; omega
      rw [hb, if_pos rfl, hfix, hact, if_neg hik]
    rw [hrest, hb, if_pos rfl, ← ha, Equiv.swap_apply_left, hTa.2, hact, if_pos rfl]
    have hE : ((n : ℤ) - 1 - 2 * (k.val : ℤ)) = 2 := by omega
    rw [hE]
    set o := ordL (T a a)
    set R := ∏ i ∈ ({k}ᶜ : Finset (Fin (n / 2))),
        (actU k α i : ℂ) ^ ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i)) *
          (q : ℂ) ^ (-(ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i))) *
            ((n : ℤ) - 1 - 2 * (i.val : ℤ)))
    have hqq : (q : ℂ) ^ (-(-o) * 2) * (q : ℂ) ^ (-4 * o) = (q : ℂ) ^ (-o * 2) := by
      rw [← zpow_add₀ hq]; ring_nf
    have hα : (α k : ℂ) ^ (-o) = ((α k : ℂ)⁻¹) ^ o := by rw [zpow_neg, inv_zpow]
    calc (α k : ℂ) ^ (-o) * (q : ℂ) ^ (-(-o) * 2) * R * (q : ℂ) ^ (-4 * o)
        = (α k : ℂ) ^ (-o) * ((q : ℂ) ^ (-(-o) * 2) * (q : ℂ) ^ (-4 * o)) * R := by ring
      _ = ((α k : ℂ)⁻¹) ^ o * (q : ℂ) ^ (-o * 2) * R := by rw [hqq, hα]
  rw [hprod, hsph]
  calc chiDeltaU q (fun i => (α i : ℂ)) b * φ (y⁻¹ * w * x) * (q : ℂ) ^ (-4 * ordL (T (lo k) (lo k)))
      = (chiDeltaU q (fun i => (α i : ℂ)) b * (q : ℂ) ^ (-4 * ordL (T (lo k) (lo k)))) * φ (y⁻¹ * w * x) := by ring
    _ = _ := by rw [key]

end GlobalTheory.WeylCell.U21TorusFactor
end
end

section

namespace GlobalTheory.FlatPair

open NumberField ReciprocityTheory.ChartRestriction.G.FD

theorem holAlg_isDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    X.dom.Nonempty → IsDomain (GlobalTheory.FlatPair.holAlg X) := by
  intro E _ _ _ r X hne
  obtain ⟨y0, hy0⟩ := hne
  haveI : Nontrivial (holAlg X) := ⟨⟨0, 1, fun h => by
    have := congrFun (congrArg Subtype.val h) ⟨y0, hy0⟩
    simp at this⟩⟩
  haveI : NoZeroDivisors (holAlg X) := ⟨fun {a b} hab => by
    by_contra hcon
    push_neg at hcon
    obtain ⟨ha, hb⟩ := hcon
    obtain ⟨F, hF, hFa⟩ := a.2
    obtain ⟨G, hG, hGb⟩ := b.2
    have ha' : ∃ y : X.dom, (a : X.dom → ℂ) y ≠ 0 := by
      by_contra h
      push_neg at h
      exact ha (Subtype.ext (funext h))
    obtain ⟨y, hy⟩ := ha'
    have hfg : ∀ w ∈ X.dom, F w * G w = 0 := by
      intro w hw
      have := congrFun (congrArg Subtype.val hab) ⟨w, hw⟩
      rw [← hFa ⟨w, hw⟩, ← hGb ⟨w, hw⟩]
      simpa using this
    have hFy : F y.1 ≠ 0 := by rw [← hFa y]; exact hy
    have key := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero (FourierCoefficientDomain.isOpen_dom X)
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected hF hG hfg y.2 hFy
    apply hb
    apply Subtype.ext
    funext z
    rw [hGb z]
    simpa using key z.1 z.2⟩
  exact NoZeroDivisors.to_isDomain _

end GlobalTheory.FlatPair
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem GlobalTheory.WeilCont.schA_periodic_finite_cosets : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    IsCompact (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    ∀ K : Set (κ → FiniteAdeleRing (𝓞 F) F), IsCompact K →
    ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (y : Fin m → κ → FiniteAdeleRing (𝓞 F) F),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ, (∀ x ∈ L, ∀ z, Ψ (z + GlobalTheory.WeilCont.adeleJoin F 0 x) = Ψ z) →
        (∀ z, Ψ z ≠ 0 → (fun i => (z i).2) ∈ K) →
        ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Ψ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i) := by
  intro F _ _ κ _ L hLo hLc K hK
  have hcont : ∀ k : κ → FiniteAdeleRing (𝓞 F) F, Continuous fun w : κ → FiniteAdeleRing (𝓞 F) F => w - k :=
    fun k => continuous_id.sub continuous_const
  have hmk : ∀ a b : κ → FiniteAdeleRing (𝓞 F) F,
      (QuotientAddGroup.mk a : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L) = QuotientAddGroup.mk b ↔ a - b ∈ L := by
    intro a b
    rw [QuotientAddGroup.eq, ← neg_mem_iff, neg_add, neg_neg, ← sub_eq_add_neg]
  have hfin : (QuotientAddGroup.mk '' K : Set ((κ → FiniteAdeleRing (𝓞 F) F) ⧸ L)).Finite := by
    obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover (fun k => {w | w - k ∈ L})
      (fun k _ => (hLo.preimage (hcont k)).mem_nhds (by simp))
    refine (t.finite_toSet.image QuotientAddGroup.mk).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨k, hk, hwk⟩ := Set.mem_iUnion₂.mp (hcov hw)
    exact ⟨k, hk, ((hmk w k).2 hwk).symm⟩
  obtain ⟨m, e, he, hS⟩ : ∃ (m : ℕ) (e : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L), Function.Injective e ∧
      ∀ q, q ∈ (QuotientAddGroup.mk '' K : Set ((κ → FiniteAdeleRing (𝓞 F) F) ⧸ L)) ↔ ∃ i, e i = q := by
    refine ⟨hfin.toFinset.card, fun i => (hfin.toFinset.equivFin.symm i).1,
      Subtype.val_injective.comp hfin.toFinset.equivFin.symm.injective, fun q => ⟨fun hq => ?_, ?_⟩⟩
    · exact ⟨hfin.toFinset.equivFin ⟨q, hfin.mem_toFinset.2 hq⟩, by simp⟩
    · rintro ⟨i, rfl⟩
      exact hfin.mem_toFinset.1 (hfin.toFinset.equivFin.symm i).2
  choose y hy using fun i => QuotientAddGroup.mk_surjective (e i)
  refine ⟨m, fun i w => if (QuotientAddGroup.mk w : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L) = e i then 1 else 0, y,
    fun i => ?_, fun i j => ?_, ?_⟩
  · refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ⟨{w | w - x ∈ L}, hLo.preimage (hcont x), by simp,
      fun x' hx' => ?_⟩, HasCompactSupport.intro' (K := {w | w - y i ∈ L})
      ((Homeomorph.subRight (y i)).isCompact_preimage.2 hLc)
      ((AddSubgroup.isClosed_of_isOpen L hLo).preimage (hcont (y i))) fun w hw => ?_⟩
    · dsimp only
      rw [(hmk x' x).2 hx']
    · dsimp only
      rw [if_neg]
      intro h
      exact hw ((hmk w (y i)).1 (h.trans (hy i).symm))
  · dsimp only
    rw [hy j]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (fun h' => h (he h').symm), if_neg h]
  · intro Ψ hΨ hper hsupp
    choose f hf using fun i => GlobalTheory.WeilCont.exists_slice F hΨ (y i)
    refine ⟨f, funext fun z => ?_⟩
    obtain ⟨x, w, rfl⟩ : ∃ x w, z = GlobalTheory.WeilCont.adeleJoin F x w :=
      ⟨fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1, fun i => (z i).2,
        funext fun i => Prod.ext (by simp only [GlobalTheory.WeilCont.adeleJoin, RingEquiv.symm_apply_apply]) rfl⟩
    simp only [Finset.sum_apply, GlobalTheory.WeilCont.pureA_adeleJoin, ← hf]
    by_cases hw : (QuotientAddGroup.mk w : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L) ∈ QuotientAddGroup.mk '' K
    · obtain ⟨i0, hi0⟩ := (hS _).1 hw
      rw [Finset.sum_eq_single i0]
      · rw [if_pos hi0.symm, mul_one, hf]
        have hL : w - y i0 ∈ L := (hmk w (y i0)).1 (hi0.symm.trans (hy i0).symm)
        rw [← hper _ hL (GlobalTheory.WeilCont.adeleJoin F x (y i0))]
        congr 1
        funext i
        apply Prod.ext
        · change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i) =
            (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i) +
              (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0
          rw [map_zero, add_zero]
        · change w i = y i0 i + (w i - y i0 i)
          exact (add_sub_cancel _ _).symm
      · intro j _ hj
        rw [if_neg (fun h => hj (he (h.symm.trans hi0.symm))), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have h0 : Ψ (GlobalTheory.WeilCont.adeleJoin F x w) = 0 := by
        by_contra h
        exact hw ⟨w, hsupp _ h, rfl⟩
      rw [h0]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [if_neg, mul_zero]
      intro h
      exact hw (h ▸ (hS _).2 ⟨i, rfl⟩)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

private theorem ringKrullDim_le_quotient_of_algebraMap_eq_zero (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (s : R) (hs : algebraMap R S s = 0) :
    ringKrullDim S ≤ ringKrullDim (R ⧸ Ideal.span {s}) := by
  rw [ringKrullDim_quotient]
  have hmem : ∀ P : PrimeSpectrum S, (⟨P.asIdeal.comap (algebraMap R S), inferInstance⟩ : PrimeSpectrum R) ∈
      PrimeSpectrum.zeroLocus (R := R) (Ideal.span {s}) := fun P => by
    simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le,
      Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, hs, Ideal.zero_mem]
  exact Order.krullDim_le_of_strictMono (fun P => ⟨_, hmem P⟩)
    (fun P Q h => Subtype.mk_lt_mk.mpr (Ideal.IsIntegral.comap_lt_comap (R := R) h))

private theorem hInv_adjoin_of_dim_quotient_lt (q : ℕ) [NeZero q] (d : ℕ)
    (hlow : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R)
    (D : Type) [CommRing D] [Algebra.FiniteType ℤ D] (hqD : IsUnit (q : D)) (E : Type) [CommRing E]
    [Algebra D E] [Algebra.IsIntegral D E] (s : D) (hsE : algebraMap D E s = 0)
    (hlt : ringKrullDim (D ⧸ Ideal.span {s}) < d) (F : Finset E) :
    HInv q ((Algebra.adjoin D (F : Set E)).restrictScalars ℤ) := by
  set T := Algebra.adjoin D (F : Set E)
  have : Algebra.IsIntegral D T := ⟨fun x =>
    (isIntegral_algHom_iff T.val Subtype.val_injective).mp (Algebra.IsIntegral.isIntegral (x : E))⟩
  have : Algebra.FiniteType D T := (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset F)
  have : Algebra.FiniteType ℤ T := Algebra.FiniteType.trans (R := ℤ) (S := D) inferInstance inferInstance
  have hsT : algebraMap D T s = 0 := Subtype.ext (by simpa using hsE)
  have h1 : ringKrullDim T < d := (ringKrullDim_le_quotient_of_algebraMap_eq_zero D T s hsT).trans_lt hlt
  have h2 : IsUnit (q : T) := by simpa using hqD.map (algebraMap D T)
  exact hlow T h2 h1



theorem GlobalTheory.hInv_of_integral_killed_of_lower : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → ∀ (E : Type) [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (s : D), s ≠ 0 → algebraMap D E s = 0 → HInv q E := by
  intro q _ d hlow D _ _ _ hqD hdD E _ _ _ s hs0 hsE
  have hquot := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hs0)
  have hlt : ringKrullDim (D ⧸ Ideal.span {s}) < d := by
    have h := hquot.trans hdD
    generalize ringKrullDim (D ⧸ Ideal.span {s}) = a at h ⊢
    cases a using WithBot.recBotCoe with
    | bot => exact WithBot.bot_lt_coe _
    | coe a =>
      have h' : a + 1 ≤ (d : ℕ∞) := by exact_mod_cast h
      have ha : a ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) (le_trans le_self_add h')
      exact_mod_cast (ENat.add_one_le_iff ha).mp h'
  exact GlobalTheory.T.hInv_of_directed_union_subalgebras q E (Finset E) (fun F => (Algebra.adjoin D (F : Set E)).restrictScalars ℤ)
    (fun F G h x hx => Algebra.adjoin_mono (Finset.coe_subset.mpr h) hx)
    (fun a => ⟨{a}, Algebra.subset_adjoin (by simp)⟩)
    (fun F => by
      have h := hqD.map (algebraMap D (Algebra.adjoin D (F : Set E)))
      rw [map_natCast] at h
      exact h)
    (fun F => hInv_adjoin_of_dim_quotient_lt q d hlow D hqD E s hsE hlt F)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_lineBundle_descent_finiteFlat : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian Y] (L : LB X), L.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, GlobalTheory.LBDescent.chart f L i j)ˣ), GlobalTheory.LBDescent.DescCompat f L φ → GlobalTheory.LBDescent.DescCocycle f L φ → ∃ L' : LB Y, L'.IsLB ∧ LBIso L (L'.pull f) := by
  first | exact @GlobalTheory.LBDescent.exists_descent | exact GlobalTheory.LBDescent.exists_descent | (intros; apply GlobalTheory.LBDescent.exists_descent <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylorLie_spread_from_identity_point : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] (tR : R →+* C) (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A], Smooth A.hom → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), GlobalTheory.UPel.HT.LieAt b act tR (spMap (RingHom.id C)) → ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp C), x ≫ spMap tR = spMap β → GlobalTheory.UPel.HT.LieAt b act β x := by
  first | exact @GlobalTheory.HTLieSpread.lieAt_spread | exact GlobalTheory.HTLieSpread.lieAt_spread | (intros; apply GlobalTheory.HTLieSpread.lieAt_spread <;> assumption)
end
