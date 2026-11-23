module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.Skeleton
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.MapEqOfIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.MinkFix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef IsDedekindDomain

namespace PI.UnitaryGroupMassFormula.BetaModX

section Loc

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module (𝓞 E) V]

theorem le_locP (p : Ideal (𝓞 E)) [p.IsPrime] (L : Submodule (𝓞 E) V) : L ≤ Formalism.HermitianLatticesTheory.localization₂ p L := by
  intro x hx
  show ∃ s ∈ p.primeCompl, s • x ∈ L
  exact ⟨1, p.primeCompl.one_mem, by rw [one_smul]; exact hx⟩

theorem localization_mono (p : Ideal (𝓞 E)) [p.IsPrime] {L L' : Submodule (𝓞 E) V} (h : L ≤ L') :
    Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ p.primeCompl, s • x ∈ L := hx
  show ∃ s ∈ p.primeCompl, s • x ∈ L'
  exact ⟨s, hs, h hsx⟩

theorem mem_localization_of_smul_mem' (p : Ideal (𝓞 E)) [p.IsPrime] (L : Submodule (𝓞 E) V) (x : V) (s : 𝓞 E) (hs : s ∉ p)
    (h : s • x ∈ Formalism.HermitianLatticesTheory.localization₂ p L) : x ∈ Formalism.HermitianLatticesTheory.localization₂ p L := by
  obtain ⟨t, ht, htx⟩ : ∃ t ∈ p.primeCompl, t • s • x ∈ L := h
  have hs' : s ∈ p.primeCompl := hs
  show ∃ s ∈ p.primeCompl, s • x ∈ L
  exact ⟨t * s, p.primeCompl.mul_mem ht hs', by rw [mul_smul]; exact htx⟩

theorem mem_of_locP (N : Submodule (𝓞 E) V) (x : V)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N)) : x ∈ N := by

  let I : Ideal (𝓞 E) := Submodule.comap (LinearMap.toSpanSingleton (𝓞 E) V x) N
  have hmem : ∀ r : 𝓞 E, r ∈ I ↔ r • x ∈ N := fun r => by
    show (LinearMap.toSpanSingleton (𝓞 E) V x) r ∈ N ↔ r • x ∈ N
    rw [LinearMap.toSpanSingleton_apply]
  by_contra hx
  have hIt : I ≠ ⊤ := by
    intro hI
    apply hx
    have h1 : (1 : 𝓞 E) ∈ I := by rw [hI]; exact Submodule.mem_top
    have h2 := (hmem 1).1 h1
    rwa [one_smul] at h2
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hIt
  have hMb : M ≠ ⊥ := by
    intro hb
    rw [hb] at hM
    exact NumberField.RingOfIntegers.not_isField E (Ring.isField_iff_maximal_bot.mpr hM)
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ M.primeCompl, s • x ∈ N :=
    h ⟨M, hM.isPrime, hMb⟩
  exact hs (hIM ((hmem s).2 hsx))

end Loc

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lattice_sub_orthogonal_holds : XLamSub := by
  intro D u u' F0 Λ hΛ y x hx
  obtain ⟨-, ⟨-, -, -, hlc⟩, -⟩ := hΛ
  obtain ⟨-, ⟨ξ, hξl, hξd, hξm⟩, hyc, -⟩ := y.2
  have hxΛ : x ∈ Λ := (Submodule.mem_inf.1 hx).1
  refine mem_of_locP _ x (fun P => ?_)
  haveI := P.isPrime
  by_cases hgP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  swap
  · apply mem_localization_of_smul_mem' P.asIdeal _ x ((gS D : ℕ) : 𝓞 D.host.E) hgP
    apply le_locP
    exact Submodule.mem_sup_left (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hxΛ)

  have hsm : ∀ (o : 𝓞 D.host.E) (v : (VS D).V), v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) → ((o : D.host.E)) • v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) := by
    intro o v hv
    have h1 := (Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1)).smul_mem o hv
    rwa [← algebraMap_smul D.host.E o v] at h1

  have hye : ∀ b, y.1.fl.e b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) := by
    intro b
    obtain ⟨cy, -, hcy1, hcyeq⟩ := hyc.1 P
    have hmem : cy b • y.1.fl.e b ∈ Submodule.span (𝓞 D.host.E) (Set.range fun a => cy a • y.1.fl.e a) :=
      Submodule.subset_span ⟨b, rfl⟩
    rw [hcy1 hgP b, one_smul] at hmem
    have h1 : y.1.fl.e b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ y.1) := by
      rw [hcyeq]
      exact le_locP _ _ hmem
    exact localization_mono P.asIdeal le_sup_right h1

  have key : ∀ n : ℕ, ∀ b : Fin D.R.rS, (b : ℕ) = n → (lf D F0).fl.e b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih b hbn
    have hm := hξm (Fin.castSucc b)
    unfold ModG frameAct frame at hm
    have hdiff := localization_mono P.asIdeal (le_sup_left : Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ≤ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) (hm P hgP)
    have hY : y.1.fl.fvec (Fin.castSucc b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) := by
      simpa [Formalism.MainNotions.S.FlagG.fvec] using hye b
    have hS : (∑ a, ((ξ a (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec a) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) := by
      have h1 := Submodule.sub_mem _ hY hdiff
      rwa [sub_sub_cancel] at h1
    have hR : (∑ a ∈ Finset.univ.erase (Fin.castSucc b), ((ξ a (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec a) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) := by
      refine Submodule.sum_mem _ (fun a ha => ?_)
      have hab : a ≠ Fin.castSucc b := Finset.ne_of_mem_erase ha
      rcases lt_or_gt_of_ne hab with h | h
      · obtain ⟨a', rfl⟩ : ∃ a' : Fin D.R.rS, Fin.castSucc a' = a := ⟨⟨a.val, lt_trans h b.isLt⟩, Fin.ext rfl⟩
        have h' : (a' : ℕ) < (b : ℕ) := h
        simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
        exact hsm _ _ (ih a' (by omega) a' rfl)
      · rw [hξl a (Fin.castSucc b) h]
        simp
    have hsum := Finset.add_sum_erase Finset.univ (fun a => ((ξ a (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec a) (Finset.mem_univ (Fin.castSucc b))
    have h2 : ((ξ (Fin.castSucc b) (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec (Fin.castSucc b) =
        (∑ a, ((ξ a (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec a) -
          ∑ a ∈ Finset.univ.erase (Fin.castSucc b), ((ξ a (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec a :=
      eq_sub_of_add_eq hsum
    have hfb : ((ξ (Fin.castSucc b) (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec (Fin.castSucc b) =
        (lf D F0).fl.e b := by
      rw [hξd]
      simp [Formalism.MainNotions.S.FlagG.fvec]
    rw [← hfb, h2]
    exact Submodule.sub_mem _ hS hR

  obtain ⟨cl, -, hcl1, hcleq⟩ := hlc.1 P
  have hxl : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range fun a => cl a • (lf D F0).fl.e a)) := by
    rw [← hcleq]
    exact le_locP _ _ hx
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ Submodule.span (𝓞 D.host.E) (Set.range fun a => cl a • (lf D F0).fl.e a) := hxl
  apply mem_localization_of_smul_mem' P.asIdeal _ x s hs
  refine Submodule.span_le.2 ?_ hsx
  rintro _ ⟨a, rfl⟩
  simp only [hcl1 hgP a, one_smul]
  exact key _ a rfl

end D7

end PI.UnitaryGroupMassFormula.BetaModX
end
end

section

noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.BetaModX

section MX

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem xsp_le_orth {T' : E} (F' : LFlag S r T') : Xsp F' ≤ orth S (Xsp F') := by
  intro v hv
  rw [mem_orth']
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    induction hv using Submodule.span_induction with
    | mem y' hy' =>
      obtain ⟨b, rfl⟩ := hy'
      exact F'.fl.e_iso a b
    | zero => simp
    | add y y' _ _ h1 h2 => simp [h1, h2]
    | smul c y _ h1 => simp [h1]
  | zero => simp
  | add y y' _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h1 => simp [h1]

theorem mod_lattice_absolute_value : ModXAbs := by
  intro E _ _ _ S r T' g F' Λ γ hτ hT hg hΛ hpos hA hXγ hz hcong v hv
  have hX : ∀ w, γ w ∈ Xsp F' ↔ w ∈ Xsp F' := by
    intro w
    constructor
    · intro h
      rw [← hXγ] at h
      obtain ⟨w', hw', he⟩ := h
      rw [← γ.injective he]
      exact hw'
    · intro h
      rw [← hXγ]
      exact ⟨w, h, rfl⟩
  have hiso : ∀ x y, S.hT (γ x) (γ y) = S.hT x y := hA.1
  have hU := orth_iff F' γ hiso hX
  obtain ⟨n, hn, hpow⟩ := γQ_finOrd F' hT hτ hpos Λ hΛ γ hA hU hX hz
  let φ : Qt F' →ₗ[E] Qt F' := (γQ F' γ hU hX : Qt F' →ₗ[E] Qt F')
  have hφL : ∀ x ∈ Lb F' Λ, φ x ∈ Lb F' Λ := by
    intro x hx
    have h := γQ_Lb F' Λ γ hU hX hA
    rw [← h]
    exact ⟨x, hx, rfl⟩
  have hk : ∀ (k : ℕ) (x : Qt F'), φ^[k] x = (γQ F' γ hU hX ^ k) x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, pow_succ']
      rfl
  have hpow' : ∀ x, φ^[n] x = x := by
    intro x
    rw [hk, hpow]
    rfl
  have hgE : ((g : ℕ) : E) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have hcongQ : ∀ x ∈ Lb F' Λ, ∃ y ∈ Lb F' Λ, φ x - x = g • y := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (mem_Lb F' Λ).1 hx
    have hw : (a : S.V) ∈ Lrep Λ F' := ⟨ha, a.2⟩
    obtain ⟨s, hs, ξ, hξ, hsξ⟩ := Submodule.mem_sup.1 (hcong a hw)
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hs
    obtain ⟨l, hl, rfl⟩ := hs
    have hξX : ξ ∈ Xsp F' := hξ.2
    have hgl : ((g : ℕ) : E) • l = γ a - a - ξ := by
      rw [← hsξ, ← algebraMap_smul E ((g : ℕ) : 𝓞 E) l, map_natCast]
      abel
    have hlU : l ∈ Uo F' := by
      have h1 : γ a - a - ξ ∈ Uo F' :=
        sub_mem (sub_mem ((hU a).2 a.2) a.2) (xsp_le_orth F' hξX)
      have : l = ((g : ℕ) : E)⁻¹ • (γ a - a - ξ) := by
        rw [← hgl, smul_smul, inv_mul_cancel₀ hgE, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ h1
    refine ⟨Submodule.Quotient.mk ⟨l, hlU⟩, (mem_Lb F' Λ).2 ⟨⟨l, hlU⟩, hl, rfl⟩, ?_⟩
    show γQ F' γ hU hX (Submodule.Quotient.mk a) - Submodule.Quotient.mk a =
      g • (Submodule.Quotient.mk ⟨l, hlU⟩ : Qt F')
    rw [γQ_mk, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    show ((γU F' γ hU a - a - g • (⟨l, hlU⟩ : Uo F') : Uo F') : S.V) ∈ Xsp F'
    have hco : ((γU F' γ hU a - a - g • (⟨l, hlU⟩ : Uo F') : Uo F') : S.V) = ξ := by
      have e2 : ((g • (⟨l, hlU⟩ : Uo F') : Uo F') : S.V) = g • l := by simp
      rw [Submodule.coe_sub, Submodule.coe_sub, e2, γU_coe]
      have e : (g • l : S.V) = ((g : ℕ) : E) • l := (Nat.cast_smul_eq_nsmul E g l).symm
      rw [e, hgl]
      abel
    rw [hco]
    exact hξX
  have hLb := Lb_lattice F' Λ hΛ
  have hfg : (Lb F' Λ).FG := by
    first | exact hLb.toIsLattice.fg | exact hLb.fg
  have hfix := mink_fix (Lb F' Λ) hfg φ hφL n hn hpow' g hg hcongQ
  have hall : ∀ q, φ q = q := by
    have hle : Submodule.span E (Lb F' Λ : Set (Qt F')) ≤
        LinearMap.ker (φ - LinearMap.id : Qt F' →ₗ[E] Qt F') := by
      rw [Submodule.span_le]
      intro x hx
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hfix x hx, sub_self]
    intro q
    have hq : q ∈ LinearMap.ker (φ - LinearMap.id : Qt F' →ₗ[E] Qt F') :=
      hle (by
        first
        | letI : Submodule.IsFullLattice E (Lb F' Λ) := hLb
          rw [Submodule.IsFullLattice.span_eq_top]
          exact Submodule.mem_top
        | obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (Pk F') q
          obtain ⟨o, ho, hoa⟩ := Bl.general_b_fact_third''''.goal1 S Λ hΛ (a : S.V)
          have hmem : (Submodule.Quotient.mk (p := Pk F') (o • a) : Qt F') ∈ Lb F' Λ :=
            (mem_Lb F' Λ).2 ⟨o • a, by simpa using hoa, rfl⟩
          have ho' : algebraMap (𝓞 E) E o ≠ 0 :=
            (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 ho
          have ha : (Submodule.Quotient.mk (p := Pk F') a : Qt F') =
              (algebraMap (𝓞 E) E o)⁻¹ • (Submodule.Quotient.mk (p := Pk F') (o • a) : Qt F') := by
            rw [Submodule.Quotient.mk_smul, ← algebraMap_smul E o, smul_smul, inv_mul_cancel₀ ho', one_smul]
          rw [ha]
          exact Submodule.smul_mem _ _ (Submodule.subset_span hmem))
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hq
    exact hq
  have h := hall (Submodule.Quotient.mk ⟨v, hv⟩)
  change Submodule.Quotient.mk (γU F' γ hU ⟨v, hv⟩) = Submodule.Quotient.mk (p := Pk F') ⟨v, hv⟩ at h
  rw [Submodule.Quotient.eq] at h
  exact h

end MX

end PI.UnitaryGroupMassFormula.BetaModX
end
end
